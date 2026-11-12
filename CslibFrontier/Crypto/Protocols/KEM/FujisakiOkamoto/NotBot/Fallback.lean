/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Product.Split

/-!
# Decoupling the implicit-rejection seed of `FO-notbot`

The first hop of the ROM IND-CCA proof for `FO-notbot` replaces the implicit-rejection keys
`H(true, s, c)` of `Scheme.eagerIndCcaGame`, derived from the secret seed `s`, by an independent
table `Hfb c` (`Scheme.eagerFbGame`). This is the first game hop in the proof of the §3.2.2
IND-CCA theorem for `U-notbot` in [HofheinzHoevelmannsKiltz2017], with the paper's PRF-style
seed replaced by the domain-separated random-oracle query `H(true, s, c)`.

For a fixed seed `s`, a random table `H` is the same as the pair `(H, Hfb)` read through
`H(true, s, c) := Hfb c`. The two games then answer every query identically except a direct query
`H(b, s, c)` to the seed. The run of `eagerFbGame` does not use `s`, so a run making at most `qH`
queries to `H` hits the independently sampled seed with probability at most `qH * p`, where `p`
bounds the point probabilities of `Scheme.sampleMsg`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaGame_eagerFbGame_le`:
  the advantage between `eagerIndCcaGame` and `eagerFbGame` is at most `qH * p`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

namespace Scheme

/-! ### Generic helpers -/

/-- Recording a state that the replies never read does not change the result. -/
private theorem map_fst_run_interpret_log {ι σ α : Type} {spec : ι → Type}
    (h : (q : ι) → PMF (spec q)) (upd : ι → σ → σ) (prog : OracleComp spec α) (st : σ) :
    ((OracleComp.interpret (m := StateT σ PMF) (fun q st => (h q).map (·, upd q st))
      prog).run st).map Prod.fst = OracleComp.interpret h prog := by
  induction prog using OracleComp.induction generalizing st with
  | pure a => simp
  | query_bind q cont ih =>
    rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]
    exact congrArg _ (funext fun a => ih a _)

/-! ### Splitting the key-derivation table at the seed -/

/-- The table `H` with the seed row `H(true, s, ·)` replaced by `Hfb`. -/
private def fbTable [DecidableEq M] (s : M) (H : Bool × M × CT → K) (Hfb : CT → K) :
    Bool × M × CT → K :=
  fun x => if x.1 = true ∧ x.2.1 = s then Hfb x.2.2 else H x

/-- A random table is a random table with its seed row replaced by an independent random row. -/
private theorem pi_eq_bind_map_fbTable [DecidableEq M] [Fintype M] [Fintype CT] [Finite K]
    (κ : PMF K) (s : M) :
    pi (fun _ : Bool × M × CT => κ) =
      (pi fun _ : Bool × M × CT => κ).bind fun H => (pi fun _ : CT => κ).map (fbTable s H) := by
  classical
  let bad : Bool × M × CT → Prop := fun x => x.1 = true ∧ x.2.1 = s
  have hfac : (fun _ : Bool × M × CT => κ) = fun x =>
      (κ.bind fun a => κ.map (a, ·)).map (fun ab => if bad x then ab.2 else ab.1) := by
    funext x
    split_ifs
    · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
      exact (PMF.map_id κ).symm
    · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      conv_rhs => enter [2, a]; rw [show (fun _ : K => a) = Function.const K a from rfl,
        PMF.map_const]
      exact (PMF.bind_pure κ).symm
  have hpair := pi_bind_pair (fun _ : Bool × M × CT => κ) (fun _ _ => κ)
  have hinj : Function.Injective fun c : CT => ((true, s, c) : Bool × M × CT) :=
    fun c c' h => by simpa using h
  have hrow := pi_map_comp_injective (fun _ : Bool × M × CT => κ) hinj
  conv_lhs => rw [hfac, pi_map]
  calc (pi fun _ : Bool × M × CT => κ.bind fun a => κ.map (a, ·)).map
        (fun o x => if bad x then (o x).2 else (o x).1)
      = ((pi fun _ : Bool × M × CT => κ.bind fun a => κ.map (a, ·)).map
          (fun o => (fun x => (o x).1, fun x => (o x).2))).map
          (fun HH x => if bad x then HH.2 x else HH.1 x) := by
        rw [PMF.map_comp]; rfl
    _ = _ := by
        rw [hpair, PMF.map_bind]
        congr 1 with H : 1
        rw [PMF.map_comp, ← hrow, PMF.map_comp]
        congr 1 with H₂ : 1
        funext x
        obtain ⟨t, m, c⟩ := x
        by_cases hx : t = true ∧ m = s
        · obtain ⟨rfl, rfl⟩ := hx
          simp [bad, fbTable]
        · simp [bad, fbTable, hx]

/-! ### The two oracles agree until the seed is queried -/

/-- Log of the message components of the `H`-queries. -/
private def logM : ROQuery M CT → List M → List M
  | .H x, l => x.2.1 :: l
  | .G _, l => l
  | .decaps _, l => l

private theorem mem_logM {s : M} {l : List M} (q : ROQuery M CT) (h : s ∈ l) : s ∈ logM q l := by
  cases q <;> simp [logM, h]

private theorem length_logM (q : ROQuery M CT) (l : List M) :
    (logM q l).length ≤ l.length + q.hCost := by
  cases q <;> simp [logM]

private theorem snd_eq_of_mem_support_map {α σ : Type} {μ : PMF α} {t : σ} {x : α × σ}
    (hx : x ∈ (μ.map (·, t)).support) : x.2 = t := by
  obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  rfl

variable [DecidableEq CT]

section DecidableMessages

variable [DecidableEq M]

/-- Off the seed row, `eagerHandler` on `fbTable s H Hfb` is `eagerFbHandler` on `H` and `Hfb`. -/
private theorem eagerHandler_fbTable (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (Hfb : CT → K) (pk : PK) (sk : SK) (s : M) (cStar : CT)
    (q : ROQuery M CT) (hq : ∀ x, q = .H x → x.2.1 ≠ s) :
    S.eagerHandler G (fbTable s H Hfb) ⟨sk, pk, s⟩ cStar q =
      S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ cStar q := by
  cases q with
  | G m => rfl
  | H x => simp [eagerHandler, eagerFbHandler, fbTable, hq x rfl]
  | decaps c =>
    simp only [eagerHandler, eagerFbHandler, decapsNotBot]
    cases decT S.pke G pk sk c <;> simp [fbTable]

/-- The logged oracles of the two games are identical until the log contains the seed. -/
private theorem identicalUntilBad_log (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (Hfb : CT → K) (pk : PK) (sk : SK) (s : M) (cStar : CT) :
    OracleComp.IdenticalUntilBad
      (fun q st => (S.eagerHandler G (fbTable s H Hfb) ⟨sk, pk, s⟩ cStar q).map (·, logM q st))
      (fun q st => (S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ cStar q).map (·, logM q st))
      (fun st => s ∈ st) where
  agree q st _ a st' hst' := by
    by_cases hbad : ∃ x, q = .H x ∧ x.2.1 = s
    · obtain ⟨x, rfl, hx⟩ := hbad
      have hz (μ : PMF K) : (μ.map (·, logM (.H x) st)) (a, st') = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr fun hmem =>
          hst' (by rw [show st' = _ from snd_eq_of_mem_support_map hmem]; simp [logM, hx])
      exact (hz _).trans (hz _).symm
    · rw [eagerHandler_fbTable S G H Hfb pk sk s cStar q fun x hq hx => hbad ⟨x, hq, hx⟩]
  absorb_first q st hst x hx := by
    rw [snd_eq_of_mem_support_map hx]; exact mem_logM q hst
  absorb_second q st hst x hx := by
    rw [snd_eq_of_mem_support_map hx]; exact mem_logM q hst

/-! ### One run of each game -/

/-- The adversary's run in `eagerIndCcaGame` once all randomness is fixed, with the table
`H` written as `fbTable s H Hfb`. -/
private noncomputable def runReal (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) (pk : PK) (sk : SK) (s : M) (G : M → R) (H : Bool × M × CT → K) (Hfb : CT → K)
    (m : M) (kRand : K) : PMF Bool :=
  OracleComp.interpret (S.eagerHandler G (fbTable s H Hfb) ⟨sk, pk, s⟩ (encT S.pke G pk m))
    (A (pk, encT S.pke G pk m, if b then kRand else H (false, m, encT S.pke G pk m)))

/-- The adversary's run in `eagerFbGame` once all randomness is fixed. -/
private noncomputable def runFb (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) (pk : PK) (sk : SK) (s : M) (G : M → R) (H : Bool × M × CT → K) (Hfb : CT → K)
    (m : M) (kRand : K) : PMF Bool :=
  OracleComp.interpret (S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ (encT S.pke G pk m))
    (A (pk, encT S.pke G pk m, if b then kRand else H (false, m, encT S.pke G pk m)))

/-- The logged run of `eagerFbGame`; the oracle ignores the fallback seed, set here to `m`. -/
private noncomputable def logRunFb (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) (pk : PK) (sk : SK) (G : M → R) (H : Bool × M × CT → K) (Hfb : CT → K)
    (m : M) (kRand : K) : PMF (Bool × List M) :=
  (OracleComp.interpret (m := StateT (List M) PMF)
    (fun q st => (S.eagerFbHandler G H Hfb ⟨sk, pk, m⟩ (encT S.pke G pk m) q).map
      (·, logM q st))
    (A (pk, encT S.pke G pk m, if b then kRand else H (false, m, encT S.pke G pk m)))).run []

/-- Whether the logged run of `eagerFbGame` queries `H` at the seed `s`. -/
private noncomputable def hitSeed (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) (pk : PK) (sk : SK) (s : M) (G : M → R) (H : Bool × M × CT → K) (Hfb : CT → K)
    (m : M) (kRand : K) : PMF Bool :=
  (S.logRunFb A b pk sk G H Hfb m kRand).map fun x => decide (s ∈ x.2)

private theorem runReal_le_and_runFb_le (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) (pk : PK) (sk : SK) (s : M) (G : M → R)
    (H : Bool × M × CT → K) (Hfb : CT → K) (m : M) (kRand : K) :
    S.runReal A b pk sk s G H Hfb m kRand true ≤
        S.runFb A b pk sk s G H Hfb m kRand true + S.hitSeed A b pk sk s G H Hfb m kRand true ∧
      S.runFb A b pk sk s G H Hfb m kRand true ≤
        S.runReal A b pk sk s G H Hfb m kRand true +
          S.hitSeed A b pk sk s G H Hfb m kRand true := by
  set c := encT S.pke G pk m
  set prog := A (pk, c, if b then kRand else H (false, m, c))
  have h := identicalUntilBad_log S G H Hfb pk sk s c
  have e (hd : (q : ROQuery M CT) → PMF (ROResp R K q)) :
      OracleComp.interpret hd prog =
        ((OracleComp.interpret (m := StateT (List M) PMF)
          (fun q st => (hd q).map (·, logM q st)) prog).run []).bind fun x => PMF.pure x.1 := by
    rw [← map_fst_run_interpret_log hd logM prog []]
    rfl
  have hY : S.hitSeed A b pk sk s G H Hfb m kRand true =
      ((OracleComp.interpret (m := StateT (List M) PMF)
        (fun q st => (S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ c q).map (·, logM q st))
        prog).run []).toOuterMeasure {x | (fun st => s ∈ st) x.2} := by
    rw [hitSeed, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext x
    simp
  have e₁ : S.runReal A b pk sk s G H Hfb m kRand =
      OracleComp.interpret (S.eagerHandler G (fbTable s H Hfb) ⟨sk, pk, s⟩ c) prog := rfl
  have e₂ : S.runFb A b pk sk s G H Hfb m kRand =
      OracleComp.interpret (S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ c) prog := rfl
  rw [e₁, e₂, hY, e (S.eagerHandler G (fbTable s H Hfb) ⟨sk, pk, s⟩ c),
    e (S.eagerFbHandler G H Hfb ⟨sk, pk, s⟩ c)]
  refine ⟨?_, ?_⟩
  · rw [← h.bad_eq]
    exact h.bind_apply_le prog [] _ true
  · exact h.symm.bind_apply_le prog [] _ true

/-! ### Averaging over the randomness -/

/-- Average of `F` over the randomness of `eagerFbGame`: keys, seed, `G`, `H`, `Hfb`, challenge
message and random key. -/
private noncomputable def expect (S : Scheme PK SK M R CT K) [Fintype M] [Finite R] [Fintype CT]
    [Finite K]
    (F : PK → SK → M → (M → R) → (Bool × M × CT → K) → (CT → K) → M → K → PMF Bool) :
    PMF Bool :=
  (ProbComp.eval S.pke.keyGen).bind fun ks =>
  (ProbComp.eval S.sampleMsg).bind fun s =>
  (pi fun _ : M => ProbComp.eval S.pke.sampleCoins).bind fun G =>
  (pi fun _ : Bool × M × CT => ProbComp.eval S.sampleKey).bind fun H =>
  (pi fun _ : CT => ProbComp.eval S.sampleKey).bind fun Hfb =>
  (ProbComp.eval S.sampleMsg).bind fun m =>
  (ProbComp.eval S.sampleKey).bind fun kRand => F ks.1 ks.2 s G H Hfb m kRand

omit [DecidableEq M] [DecidableEq CT] in
private theorem expect_le_add [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K)
    (F₁ F₂ F₃ : PK → SK → M → (M → R) → (Bool × M × CT → K) → (CT → K) → M → K → PMF Bool)
    (h : ∀ pk sk s G H Hfb m kRand, F₁ pk sk s G H Hfb m kRand true ≤
      F₂ pk sk s G H Hfb m kRand true + F₃ pk sk s G H Hfb m kRand true) :
    S.expect F₁ true ≤ S.expect F₂ true + S.expect F₃ true := by
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun ks _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun s _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun G _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun H _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun Hfb _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun m _ => ?_
  refine Probability.PMF.bind_apply_le_add_on_support _ _ fun kRand _ => ?_
  exact h _ _ _ _ _ _ _ _

/-- The run of `eagerFbGame` queries `H` at the independent seed with probability at most
`qH * p`. -/
private theorem expect_hitSeed_le [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {p : ℝ≥0} (hp : ∀ m, ProbComp.eval S.sampleMsg m ≤ p)
    (b : Bool) : S.expect (S.hitSeed A b) true ≤ qH * p := by
  refine Probability.PMF.bind_apply_le_on_support _ fun ks _ => ?_
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun G _ => ?_
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun H _ => ?_
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun Hfb _ => ?_
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun m _ => ?_
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun kRand _ => ?_
  change ((ProbComp.eval S.sampleMsg).bind fun s =>
    (S.logRunFb A b ks.1 ks.2 G H Hfb m kRand).bind fun x =>
      PMF.pure (decide (s ∈ x.2))) true ≤ _
  rw [PMF.bind_comm (ProbComp.eval S.sampleMsg)]
  refine Probability.PMF.bind_apply_le_on_support _ fun x hx => ?_
  have hlen : x.2.length ≤ qH := by
    have hcost := (hq (ks.1, encT S.pke G ks.1 m,
      if b then kRand else H (false, m, encT S.pke G ks.1 m))).2
    simpa using hcost.measure_le _ List.length
      (fun q st res st' hmem => by
        rw [show st' = logM q st from snd_eq_of_mem_support_map hmem]
        exact length_logM q st)
      (show (x.1, x.2) ∈ _ from hx)
  have hμ : ∀ s, ((ProbComp.eval S.sampleMsg).map id) s ≤ p := fun s => by
    rw [PMF.map_id]; exact hp s
  change ((ProbComp.eval S.sampleMsg).map fun s => decide (s ∈ x.2)) true ≤ _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  calc (ProbComp.eval S.sampleMsg).toOuterMeasure ((fun s => decide (s ∈ x.2)) ⁻¹' {true})
      ≤ (ProbComp.eval S.sampleMsg).toOuterMeasure
          {a | ∃ e ∈ x.2.map (·, ()), e.1 = id a} :=
        (ProbComp.eval S.sampleMsg).toOuterMeasure.mono fun a ha => by simpa using ha
    _ ≤ (x.2.map (·, ())).length * p := RandomOracle.toOuterMeasure_exists_mem_fst_eq_le hμ _
    _ ≤ qH * p := by
        rw [List.length_map]
        gcongr

omit [DecidableEq M] in
private theorem eagerFbGame_eq_expect [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerFbGame A b = S.expect (S.runFb A b) := by
  simp only [eagerFbGame, expect, keyGenNotBot, encapsNotBot, encapsBot, ProbComp.eval_bind,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨pk, sk⟩ : 1

private theorem eagerIndCcaGame_eq_expect [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerIndCcaGame A b = S.expect (S.runReal A b) := by
  simp only [eagerIndCcaGame, expect, keyGenNotBot, encapsNotBot, encapsBot, ProbComp.eval_bind,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨pk, sk⟩ : 1
  congr 1 with s : 1
  congr 1 with G : 1
  conv_lhs => rw [pi_eq_bind_map_fbTable _ s, PMF.bind_bind]
  congr 1 with H : 1
  rw [PMF.bind_map]
  congr 1 with Hfb : 1

end DecidableMessages

/-- **Hop 1 of the ROM IND-CCA proof for `FO-notbot`** (the first game hop in the proof of the
§3.2.2 IND-CCA theorem for `U-notbot` in [HofheinzHoevelmannsKiltz2017]): replacing the
implicit-rejection keys `H(true, s, c)` by an independent table `Hfb c` changes the output
distribution by at most `qH * p`, where `qH` bounds the adversary's `H`-queries and `p` bounds the
point probabilities of the seed sampler `S.sampleMsg`. -/
theorem advantage_eagerIndCcaGame_eagerFbGame_le [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {p : ℝ≥0} (hp : ∀ m, ProbComp.eval S.sampleMsg m ≤ p)
    (b : Bool) :
    (Game.advantage (S.eagerIndCcaGame A b) (S.eagerFbGame A b) : ℝ) ≤ qH * (p : ℝ) := by
  classical
  have hbad := S.expect_hitSeed_le A hq hp b
  have hB : ((qH : ℝ≥0∞) * p) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top qH)
    ENNReal.coe_ne_top
  have h := Game.advantage_le_of_apply_le hB
    (game1 := S.eagerIndCcaGame A b) (game2 := S.eagerFbGame A b)
    (by
      rw [eagerIndCcaGame_eq_expect, eagerFbGame_eq_expect]
      exact (S.expect_le_add _ _ _ fun pk sk s G H Hfb m kRand =>
        (S.runReal_le_and_runFb_le A b pk sk s G H Hfb m kRand).1).trans (by gcongr))
    (by
      rw [eagerIndCcaGame_eq_expect, eagerFbGame_eq_expect]
      exact (S.expect_le_add _ _ _ fun pk sk s G H Hfb m kRand =>
        (S.runReal_le_and_runFb_le A b pk sk s G H Hfb m kRand).2).trans (by gcongr))
  simpa [ENNReal.toReal_mul] using h

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
