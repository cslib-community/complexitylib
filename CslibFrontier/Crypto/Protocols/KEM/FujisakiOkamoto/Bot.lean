/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.CloseTo.UntilBad
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Challenge
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Correctness
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Pushforward
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Tactic.PMFSwap

/-!
# ROM IND-CCA security of `FO^⊥`

The explicit-rejection Fujisaki–Okamoto transform `FO^⊥ = U^⊥ ∘ T` of
[HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021, §3.1
Fig. 5 and §3.2.1 Fig. 9) is IND-CCA secure in the random oracle model when the underlying
explicit-coin PKE is IND-CPA secure, `δ`-correct and `γ`-spread, and messages are uniform
(`Scheme.indCcaBotAdvantage_le`). For an adversary making at most `qG` queries to `G`, `qH` queries
to `H`, and `qD` queries to the punctured decapsulation oracle (`ROFullQueryBounds A qG qH qD`),

`Adv^{IND-CCA}_{FO^⊥}(A) ≤ 2 · Adv^{IND-CPA}(B) + 2 (qG + qH) / |M| + 2 (qG + qH + 1) δ
  + 2 (qG + qH + qD) 2^{-γ}`,

where `B = romBotCpaReduction A m₀ m₁` for some distinct messages `m₀ ≠ m₁`. Unlike the
implicit-rejection transform `FO-notbot` (module
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot`), `FO^⊥` has no secret fallback seed
and therefore no `2 qH / |M|` seed-guessing term; conversely, because `decapsBot` explicitly
outputs `none` when `decT` rejects (exposing the §3.1 ciphertext-validity oracle `CVO` of
`T[PKE, G]`), simulating decapsulation from cached `G`-queries alone incurs an additional
`2 qD 2^{-γ}` spreadness term.

The proof composes four game hops for each challenge bit `b : Bool`:

1. `eval_roIndCcaBotGame_eq_eagerIndCcaBotGame` and
   `eagerCoupledBotGame_eq_eagerIndCcaBotGame`: lazy/eager equivalence for `roIndCcaBotGame` and
   oracle re-indexing via `coupledH` (`bind_pi_coupledH`), so that valid decapsulations read the
   ciphertext key table `Hq c` while invalid ciphertexts return `none`.
2. `closeTo_cachedCoupledBotGame_eagerCoupledBotGame`: lazy-sampling simulation with `CloseTo`
   error `qD · 2^{-γ}` (the §3.1 ciphertext-validity hop for `T[PKE, G]`), replacing `decT`'s check
   on `G(m')` by a lookup in the cached `G`-queries `gCache`.
3. `advantage_cachedCoupledBotGame_simBotGame_le`: dropping the secret-key decryption test from
   both `H` and `decaps` via `NotBot.Correctness.advantage_coupledFilterGame_simFilterGame_le` costs
   `(qG + qH + 1) δ`.
4. `advantage_simBotGame_le`: in the keyless `FO^⊥` simulator `simBotGame`, the programmed
   challenge entry `(m*, r*)` never matches a punctured decapsulation query `c ≠ c*`, so
   `NotBot.Challenge.advantage_simFilterGame_le` reduces distinguishing the real and random
   challenge keys to `romBotCpaReduction`.

Steps 1–3 are applied to both challenge bits, which accounts for the factor `2` on their terms.
In `roIndCcaBotGame` and `eagerIndCcaBotGame`, both real `H` replies and the independent ideal
challenge key are drawn from the arbitrary sampler `S.sampleKey : ProbComp K` (distinct from
`S.pke.keyGen`), and the proof holds for any `S.sampleKey`; taking `S.sampleKey` uniform on `K`
recovers the standard uniform-ideal-key experiment of [HofheinzHoevelmannsKiltz2017], §2.2,
Def. 2.4 / Fig. 4.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roIndCcaBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage`: executable lazy-cached ROM
  IND-CCA game and advantage for `FO^⊥`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerIndCcaBotGame`: eager random-oracle IND-CCA
  game for `FO^⊥`, defined directly from `Scheme.encapsBot` and `Scheme.decapsBot`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotCheck`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romBotCpaReduction`: keyless ROM simulator and
  IND-CPA reduction for `FO^⊥`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_roIndCcaBotGame_eq_eagerIndCcaBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage_eq_eager`: exact eager/lazy
  equivalence for `FO^⊥`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaBotGame_simBotGame_le`: the
  eager `FO^⊥` IND-CCA game and the keyless simulator game `simBotGame` differ by at most
  `(qG + qH + 1) δ + qD · 2^{-γ}`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage_le`: ROM IND-CCA security of
  `FO^⊥` from IND-CPA security, `δ`-correctness and `γ`-spreadness.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open RandomOracle (eval_zoom_memoize_map eval_zoom_memoize_bind
  answer_bind_complete answer_bind_complete₁ answer_bind_complete₂)
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

/-! ### Generic `CloseTo` simulation and map helpers -/

/-- Two pushforwards of the same distribution `μ` that agree outside an event `B` are within
`μ.toOuterMeasure B` in statistical distance (`CloseTo`). -/
private theorem closeTo_map_of_eq_off {α β : Type} (μ : PMF α) (f g : α → β) (B : Set α)
    (heq : ∀ x, x ∉ B → f x = g x) :
    CloseTo (μ.map f) (μ.map g) (μ.toOuterMeasure B) := by
  simpa only [PMF.map, Function.comp_def] using
    Cslib.Interactive.CloseTo.bind_of_eq_on μ (fun x => PMF.pure (f x)) (fun x => PMF.pure (g x)) B
      fun x _ hx => congrArg PMF.pure (heq x hx)

/-- Approximate stateful simulation: if each query `q` commutes with `relate` up to statistical
distance `cost q * ε`, then any program `prog` with `IsCostBounded cost prog d` commutes with
`relate` up to statistical distance `d * ε`. -/
private theorem run_interpret_closeTo_simulation {ι State State' α : Type}
    {spec : OracleSpec ι} (cost : ι → ℕ) (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q)) (relate : State → PMF State')
    (ε : ℝ≥0∞)
    (step : ∀ q s, CloseTo
      ((oracle q s).bind fun x => (relate x.2).map (x.1, ·))
      ((relate s).bind (oracle' q))
      (cost q * ε))
    (prog : OracleComp spec α) {d : ℕ} (hd : OracleComp.IsCostBounded cost prog d) (s : State) :
    CloseTo
      (((OracleComp.interpret oracle prog).run s).bind fun x => (relate x.2).map (x.1, ·))
      ((relate s).bind fun t => (OracleComp.interpret oracle' prog).run t)
      (d * ε) := by
  induction hd generalizing s with
  | pure a n =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind,
      PMF.map, Function.comp_def]
    exact (CloseTo.refl _).mono zero_le
  | liftBind q cont n _ ih =>
    rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
    have h₁ : CloseTo
        ((oracle q s).bind fun x =>
          ((OracleComp.interpret oracle (cont x.1)).run x.2).bind fun y =>
            (relate y.2).map (y.1, ·))
        ((oracle q s).bind fun x =>
          (relate x.2).bind fun t => (OracleComp.interpret oracle' (cont x.1)).run t)
        ((n : ℝ≥0∞) * ε) :=
      CloseTo.bind_right _ fun x _ => ih x.1 x.2
    have h₂ : CloseTo
        (((oracle q s).bind fun x => (relate x.2).map (x.1, ·)).bind fun y =>
          (OracleComp.interpret oracle' (cont y.1)).run y.2)
        (((relate s).bind (oracle' q)).bind fun y =>
          (OracleComp.interpret oracle' (cont y.1)).run y.2)
        (cost q * ε) :=
      (step q s).bind_left _
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h₂
    refine (h₁.trans h₂).mono (le_of_eq ?_)
    rw [← add_mul, Nat.cast_add]

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-! ### Section 1: Executable and Eager ROM IND-CCA Games for `FO^⊥ = U^⊥ ∘ T` -/

/-- Stateful oracle handler for the executable ROM IND-CCA game of `FO^⊥`
([HofheinzHoevelmannsKiltz2017], §3.2.1, Fig. 9). Queries to the challenge ciphertext `cStar` are
rejected with `none`; other decapsulation queries run the scheme's decapsulation `decapsBotM`
against the lazy random oracles `G` and `H`. -/
def roBotHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) : StateT (ROCache M R CT K) ProbComp (ROResp R K q) :=
  ROQuery.dispatch (roHashG S.pke.sampleCoins) (roHashH S.sampleKey)
    (S.decapsBotM (roHashG S.pke.sampleCoins) (roHashH S.sampleKey) pk sk) cStar q

/-- The executable ROM IND-CCA security game for `FO^⊥ = U^⊥ ∘ T` with bit `b : Bool`. When
`b = false`, the adversary receives the real encapsulated key `kReal = H(false, m*, c*)`; when
`b = true`, it receives an independent key `kRand ← S.sampleKey`. -/
def roIndCcaBotGame (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, sk) ← S.pke.keyGen
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let kReal ← S.sampleKey
  let kRand ← S.sampleKey
  let kStar := if b then kRand else kReal
  let st₀ : ROCache M R CT K :=
    { gCache := [(mStar, rStar)], hCache := [((false, mStar, cStar), kReal)] }
  let (guess, _) ←
    (OracleComp.interpret (S.roBotHandler pk sk cStar) (A ⟨pk, cStar, kStar⟩)).run st₀
  return guess

/-- The ROM IND-CCA advantage of an adversary `A` against `FO^⊥`. -/
noncomputable def indCcaBotAdvantage (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) : ℝ≥0 :=
  Game.advantage
    (ProbComp.eval (S.roIndCcaBotGame A false))
    (ProbComp.eval (S.roIndCcaBotGame A true))

/-- Stateless handler for `S.eagerIndCcaBotGame`: `G` and `H` are complete functions and
decapsulation queries for `c ≠ cStar` evaluate `S.decapsBot G H pk sk c`. -/
noncomputable def eagerBotHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ H) (fun c => PMF.pure (S.decapsBot G H pk sk c))
    cStar q

/-- The eager random-oracle IND-CCA game for `FO^⊥`, defined directly from `S.pke.keyGen`,
`S.encapsBot`, and `S.decapsBot` over eagerly sampled random functions `G : M → R` and
`H : Bool × M × CT → K`. -/
noncomputable def eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, sk) ← ProbComp.eval S.pke.keyGen
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let H ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let (cStar, kReal) ← ProbComp.eval (S.encapsBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  let kStar := if b then kRand else kReal
  OracleComp.interpret (S.eagerBotHandler G H pk sk cStar) (A ⟨pk, cStar, kStar⟩)

/-- Partial-table pair `(tG, tH)` representing `ROCache`. -/
private abbrev ROTables (M R CT K : Type) : Type :=
  RandomOracle.Cache (fun _ : M => R) × RandomOracle.Cache (fun _ : Bool × M × CT => K)

private def roTablesOf (st : ROCache M R CT K) : ROTables M R CT K :=
  (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache)

/-- `roBotHandler` on represented `(tG, tH)` tables via `RandomOracle.answer`: decapsulation
queries `c ≠ cStar` run `decapsBotM` against these table oracles. -/
private noncomputable def answerBotROHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) : StateT (ROTables M R CT K) PMF (ROResp R K q) :=
  let G : M → StateT (ROTables M R CT K) PMF R := fun m t =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m t.1).map
      fun z => (z.1, (z.2, t.2))
  let H : Bool × M × CT → StateT (ROTables M R CT K) PMF K := fun x t =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) x t.2).map
      fun z => (z.1, (t.1, z.2))
  ROQuery.dispatch G H (S.decapsBotM G H pk sk) cStar q

/-- A decapsulation query `c ≠ cStar` to `answerBotROHandler` as explicit table operations. -/
private theorem answerBotROHandler_decaps (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    {cStar c : CT} (hc : c ≠ cStar) (t : ROTables M R CT K) :
    S.answerBotROHandler pk sk cStar (.decaps c) t =
      match S.pke.dec sk c with
      | none => PMF.pure (none, t)
      | some m' =>
        (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m' t.1).bind fun y =>
          if S.pke.encDet pk m' y.1 = c then
            (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m', c) t.2).map
              fun z => (some z.1, (y.2, z.2))
          else
            PMF.pure (none, (y.2, t.2)) := by
  simp only [answerBotROHandler, ROQuery.dispatch, hc, ↓reduceIte, decapsBotM_eq]
  cases S.pke.dec sk c with
  | none => rfl
  | some m' =>
    dsimp only
    simp only [bind, StateT.bind, PMF.bind_map]
    congr 1 with a : 1
    dsimp only [Function.comp_apply]
    split_ifs
    · simp only [StateT.bind, Probability.PMF.monad_bind_eq_bind, PMF.bind_map]
      rfl
    · rfl

private theorem roBotHandler_map_roTablesOf (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) (st : ROCache M R CT K) :
    (ProbComp.eval (S.roBotHandler pk sk cStar q st)).map (fun z => (z.1, roTablesOf z.2)) =
      S.answerBotROHandler pk sk cStar q (roTablesOf st) := by
  cases q with
  | G m =>
    exact eval_zoom_memoize_map ROCache.gCache (fun st g => { st with gCache := g })
      S.pke.sampleCoins m st id roTablesOf (fun g => (g, RandomOracle.ofList st.hCache))
      (fun _ => rfl)
  | H x =>
    exact eval_zoom_memoize_map ROCache.hCache (fun st h => { st with hCache := h })
      S.sampleKey x st id roTablesOf (fun h => (RandomOracle.ofList st.gCache, h))
      (fun _ => rfl)
  | decaps c =>
    by_cases hc : c = cStar
    · simp only [roBotHandler, answerBotROHandler, hc, ↓reduceIte, ROQuery.dispatch]
      exact PMF.pure_map _ _
    · rw [answerBotROHandler_decaps S pk sk hc]
      simp only [roBotHandler, hc, ↓reduceIte, ROQuery.dispatch, decapsBotM_eq]
      cases hdec : S.pke.dec sk c with
      | none =>
        exact PMF.pure_map _ _
      | some m' =>
        change (ProbComp.eval (roHashG S.pke.sampleCoins m' st >>= fun vs =>
          (if S.pke.encDet pk m' vs.1 = c then do
            let k ← roHashH S.sampleKey (false, m', c)
            return some k
          else return none) vs.2)).map _ = _
        refine eval_zoom_memoize_bind ROCache.gCache (fun st g => { st with gCache := g })
          S.pke.sampleCoins m' st
          (fun r' st' => (if S.pke.encDet pk m' r' = c then do
            let k ← roHashH S.sampleKey (false, m', c)
            return some k
          else return none) st')
          roTablesOf _ (fun r' gC => ?_)
        by_cases henc : S.pke.encDet pk m' r' = c
        · simp only [henc, ↓reduceIte]
          change (ProbComp.eval (roHashH S.sampleKey (false, m', c) { st with gCache := gC } >>=
            fun vs => pure (some vs.1, vs.2))).map _ = _
          refine Eq.trans ?_ (eval_zoom_memoize_map ROCache.hCache
            (fun st h => { st with hCache := h }) S.sampleKey (false, m', c)
            { st with gCache := gC } some roTablesOf
            (fun h => (RandomOracle.ofList gC, h)) (fun _ => rfl))
          rw [ProbComp.eval_bind, PMF.map_bind]
          simp only [ProbComp.eval_pure, PMF.pure_map]
          rfl
        · simp only [henc, ↓reduceIte]
          exact PMF.pure_map _ _

private noncomputable def completeROTables [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (t : ROTables M R CT K) :
    PMF ((M → R) × (Bool × M × CT → K)) :=
  (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins) t.1).bind fun G =>
  (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) t.2).map fun H => (G, H)

private noncomputable def eagerBotStateHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) :
    StateT ((M → R) × (Bool × M × CT → K)) PMF (ROResp R K q) :=
  fun T => (S.eagerBotHandler T.1 T.2 pk sk cStar q).map (·, T)

private theorem answerBotROHandler_sim [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT)
    (t : ROTables M R CT K) :
    (S.answerBotROHandler pk sk cStar q t).bind
        (fun x => (S.completeROTables x.2).map (x.1, ·)) =
      (S.completeROTables t).bind (S.eagerBotStateHandler pk sk cStar q) := by
  rcases t with ⟨tG, tH⟩
  cases q with
  | G m =>
    simp only [answerBotROHandler, completeROTables, eagerBotStateHandler, eagerBotHandler,
      pmf_norm, ROQuery.dispatch]
    rw [answer_bind_complete]
    · rfl
    · intros; rfl
  | H x =>
    simp only [answerBotROHandler, completeROTables, eagerBotStateHandler, eagerBotHandler,
      pmf_norm, PMF.map, ROQuery.dispatch]
    rw [answer_bind_complete₁]
    · pmf_swap
    · intros; rfl
  | decaps c =>
    change (S.answerBotROHandler pk sk cStar (.decaps c) (tG, tH)).bind
        (fun x => (S.completeROTables x.2).map (x.1, ·)) =
      (S.completeROTables (tG, tH)).bind fun T =>
        (S.eagerBotHandler T.1 T.2 pk sk cStar (.decaps c)).map (·, T)
    by_cases hc : c = cStar
    · dsimp only [answerBotROHandler, completeROTables, eagerBotHandler, ROQuery.dispatch]
      simp only [hc, ↓reduceIte, pure, StateT.pure, pmf_norm, PMF.map]
    · rw [answerBotROHandler_decaps S pk sk hc]
      dsimp only [completeROTables, eagerBotHandler, decapsBot_eq, ROQuery.dispatch]
      simp only [hc, ↓reduceIte, decT_eq, encT]
      cases hdec : S.pke.dec sk c with
      | none =>
        simp only [Option.map_none, pmf_norm, PMF.map]
      | some m' =>
        simp only [pmf_norm, PMF.map]
        refine Eq.trans ?_ (answer_bind_complete _ tG m'
          (fun x G => (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
            PMF.pure ((if S.pke.encDet pk m' x.1 = c then some m' else none).map
              fun m'' => H (false, m'', c), G, H)) (fun _ _ _ => rfl))
        congr 1 with y : 1
        by_cases henc : S.pke.encDet pk m' y.1 = c
        · simp only [henc, ↓reduceIte, Option.map_some, pmf_norm]
          rw [answer_bind_complete₁]
          · pmf_swap
          · intros; rfl
        · simp only [henc, ↓reduceIte, Option.map_none, pmf_norm]

private theorem eval_run_roBotHandler_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT) {α : Type}
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α) (st : ROCache M R CT K) :
    (ProbComp.eval ((OracleComp.interpret (S.roBotHandler pk sk cStar) prog).run st)).map
        Prod.fst =
      (S.completeROTables (roTablesOf st)).bind fun T =>
        OracleComp.interpret (S.eagerBotHandler T.1 T.2 pk sk cStar) prog := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  have hmap := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state
      (fun q s => ProbComp.eval (S.roBotHandler pk sk cStar q s))
      (S.answerBotROHandler pk sk cStar) roTablesOf
      (fun q s => S.roBotHandler_map_roTablesOf pk sk cStar q s) prog st)
  simp only [PMF.map_comp, Function.comp_def] at hmap
  rw [hmap, OracleComp.run_interpret_simulation_fst _ (S.eagerBotStateHandler pk sk cStar) _
    (fun q t => S.answerBotROHandler_sim pk sk cStar q t)]
  congr 1 with T : 1
  have hro := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_readOnly
      (fun q T' => S.eagerBotHandler T'.1 T'.2 pk sk cStar q) prog T)
  change ((OracleComp.interpret (S.eagerBotStateHandler pk sk cStar) prog).run T).map Prod.fst =
    ((OracleComp.interpret (fun q => S.eagerBotHandler T.1 T.2 pk sk cStar q) prog).map
      (fun a => (a, T))).map Prod.fst at hro
  rw [PMF.map_comp] at hro
  exact hro.trans (PMF.map_id _)

/-- **Eager/lazy equivalence for the `FO^⊥` ROM IND-CCA game**: evaluating the executable
lazy-cached game `S.roIndCcaBotGame A b` yields the exact same output distribution as the eager
random-oracle game `S.eagerIndCcaBotGame A b`. -/
theorem eval_roIndCcaBotGame_eq_eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.roIndCcaBotGame A b) = S.eagerIndCcaBotGame A b := by
  dsimp only [roIndCcaBotGame, eagerIndCcaBotGame, encapsBot]
  simp only [pmf_norm, encT]
  congr 1 with ⟨pk, sk⟩ : 1
  have hstep (mStar : M) (rStar : R) (kReal kRand : K) :
      (ProbComp.eval ((OracleComp.interpret (S.roBotHandler pk sk (S.pke.encDet pk mStar rStar))
          (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal⟩)).run
          { gCache := [(mStar, rStar)],
            hCache := [((false, mStar, S.pke.encDet pk mStar rStar), kReal)] })).bind
          (fun a => PMF.pure a.1) =
      (pi (Function.update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar
          (PMF.pure rStar))).bind fun G =>
        (pi (Function.update (fun _ : Bool × M × CT => ProbComp.eval S.sampleKey)
            (false, mStar, S.pke.encDet pk mStar rStar) (PMF.pure kReal))).bind fun H =>
          OracleComp.interpret (S.eagerBotHandler G H pk sk (S.pke.encDet pk mStar rStar))
            (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else kReal⟩) := by
    change (ProbComp.eval _).map Prod.fst = _
    rw [eval_run_roBotHandler_eq_eager]
    simp only [completeROTables, roTablesOf, RandomOracle.complete_ofList_singleton, pmf_norm]
  simp only [hstep]
  pmf_hoist (ProbComp.eval S.sampleMsg)
  congr 1 with mStar : 1
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  let dH : Bool × M × CT → PMF K := fun _ => ProbComp.eval S.sampleKey
  refine Eq.trans ?_ (bind_pi_update dG mStar (fun rStar G =>
    (pi dH).bind fun H =>
    (ProbComp.eval S.sampleKey).bind fun kRand =>
      OracleComp.interpret (S.eagerBotHandler G H pk sk (S.pke.encDet pk mStar rStar))
        (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else
          H (false, mStar, S.pke.encDet pk mStar rStar)⟩)))
  congr 1 with rStar : 1
  pmf_hoist (pi (Function.update dG mStar (PMF.pure rStar)))
  congr 1 with G : 1
  set cStar := S.pke.encDet pk mStar rStar
  refine Eq.trans ?_ (bind_pi_update dH (false, mStar, cStar) (fun kReal H =>
    (ProbComp.eval S.sampleKey).bind fun kRand =>
      OracleComp.interpret (S.eagerBotHandler G H pk sk cStar)
        (A ⟨pk, cStar, if b then kRand else kReal⟩)))
  congr 1 with kReal : 1
  exact PMF.bind_comm _ _ _

/-- The ROM IND-CCA advantage of `A` against `FO^⊥` equals the distinguishing advantage between
`S.eagerIndCcaBotGame A false` and `S.eagerIndCcaBotGame A true`. -/
theorem indCcaBotAdvantage_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) :
    S.indCcaBotAdvantage A =
      Game.advantage (S.eagerIndCcaBotGame A false) (S.eagerIndCcaBotGame A true) := by
  simp [indCcaBotAdvantage, eval_roIndCcaBotGame_eq_eagerIndCcaBotGame]

/-! ### Section 2: Oracle Re-indexing and Lazy + Spreadness CVO Hop -/

/-- Stateless oracle of `eagerCoupledBotGame`: `G` reads `G`, `H` reads `coupledH`, and
decapsulation queries `c ≠ cStar` return `some (Hq c)` when `decT` accepts `c` and `none` when
`decT` rejects `c`. -/
noncomputable def eagerCoupledBotHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (Hq : CT → K) (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ S.coupledH G Hq Hraw pk sk)
    (fun c =>
      PMF.pure
        (match decT S.pke G pk sk c with
        | some _ => some (Hq c)
        | none => none))
    cStar q

/-- The eager coupled game for `FO^⊥`: independent tables `G`, `Hq`, `Hraw`, challenge
`c* = Enc(pk, m*; G(m*))` with real key `coupledH (false, m*, c*)`, and decapsulation gated by
`decT`. -/
noncomputable def eagerCoupledBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, sk) ← ProbComp.eval S.pke.keyGen
  let G ← pi (α := fun _ : M => R) (fun _ => ProbComp.eval S.pke.sampleCoins)
  let Hq ← pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let Hraw ← pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)
  let mStar ← ProbComp.eval S.sampleMsg
  let cStar := encT S.pke G pk mStar
  let kRand ← ProbComp.eval S.sampleKey
  let kReal := S.coupledH G Hq Hraw pk sk (false, mStar, cStar)
  OracleComp.interpret (S.eagerCoupledBotHandler G Hq Hraw pk sk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)

private theorem eagerBotHandler_coupledH (S : Scheme PK SK M R CT K) (G : M → R) (Hq : CT → K)
    (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    S.eagerBotHandler G (S.coupledH G Hq Hraw pk sk) pk sk cStar q =
      S.eagerCoupledBotHandler G Hq Hraw pk sk cStar q := by
  cases q with
  | G m => rfl
  | H x => rfl
  | decaps c =>
    simp only [eagerBotHandler, eagerCoupledBotHandler, decapsBot_eq, ROQuery.dispatch]
    by_cases hc : c = cStar
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      cases hd : decT S.pke G pk sk c with
      | none => rfl
      | some m' =>
        have henc := encT_of_decT_eq_some hd
        have hdec := dec_of_decT_eq_some hd
        simp only [encT] at henc
        simp [coupledH, henc, hdec]

/-- **Re-indexing the random oracle `H` of `FO^⊥`**: `eagerCoupledBotGame` and
`eagerIndCcaBotGame` have the exact same output distribution. -/
theorem eagerCoupledBotGame_eq_eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerCoupledBotGame A b = S.eagerIndCcaBotGame A b := by
  simp only [eagerCoupledBotGame, eagerIndCcaBotGame, encapsBot,
    Probability.PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind]
  congr 1 with ⟨pk, sk⟩ : 1
  congr 1 with G : 1
  symm
  rw [S.bind_pi_coupledH G pk sk]
  congr 1 with Hq : 1
  congr 1 with Hraw : 1
  congr 1 with mStar : 1
  congr 1 with kRand : 1
  congr 1
  funext q
  exact S.eagerBotHandler_coupledH G Hq Hraw pk sk _ q

/-- Decapsulation filter of `cachedCoupledBotGame`: decrypts `c` under `sk` to `m'` and accepts
only when `m'` is already cached in `gCache` with a coin `r'` satisfying `Enc(pk, m'; r') = c`. -/
def cachedCoupledBotCheck (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK)
    (gCache : List (M × R)) (c : CT) : Bool :=
  match P.dec sk c with
  | none => false
  | some m' =>
    match gCache.lookup m' with
    | none => false
    | some r' => decide (P.encDet pk m' r' = c)

/-- Lazy coupled game for `FO^⊥` where decapsulation only checks coins already cached in `gCache`
from `mStar`, `G`, or `H` queries. -/
def cachedCoupledBotGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) : ProbComp Bool :=
  S.coupledFilterGame (cachedCoupledBotCheck S.pke) A b

/-- The three partial tables `(G, Hraw, Hq)` of the coupled game. -/
private abbrev Tables (M R CT K : Type) : Type :=
  RandomOracle.Cache (fun _ : M => R) × RandomOracle.Cache (fun _ : Bool × M × CT => K) ×
    RandomOracle.Cache (fun _ : CT => K)

/-- The represented tables of a `SimState`. -/
private def tablesOf (st : SimState M R CT K) : Tables M R CT K :=
  (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, RandomOracle.ofList st.hqCache)

/-- `coupledHashH` on represented tables, answered with `RandomOracle.answer`. -/
private noncomputable def answerHashH (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) : StateT (Tables M R CT K) PMF K := fun (tG, tH, tQ) =>
  match x with
  | (false, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m tG).bind fun y =>
      if S.pke.encDet pk m y.1 = c ∧ S.pke.dec sk c = some m then
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c tQ).map
          fun z => (z.1, (y.2, tH, z.2))
      else
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m, c) tH).map
          fun z => (z.1, (y.2, z.2, tQ))
  | (true, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, m, c) tH).map
      fun z => (z.1, (tG, z.2, tQ))

/-- Mapping `SimState` to its represented tables turns `coupledHashH` into `answerHashH`. -/
private theorem coupledHashH_map_tablesOf (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) (st : SimState M R CT K) :
    (ProbComp.eval (S.coupledHashH pk sk x st)).map (fun z => (z.1, tablesOf z.2)) =
      S.answerHashH pk sk x (tablesOf st) := by
  rcases x with ⟨_ | _, m, c⟩
  · change (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun vs =>
        (if S.pke.encDet pk m vs.1 = c ∧ S.pke.dec sk c = some m then
          simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)) vs.2)).map _ = _
    dsimp only [answerHashH, simHashG]
    refine eval_zoom_memoize_bind (fun st : SimState M R CT K => st.gCache)
      (fun st g => { st with gCache := g }) S.pke.sampleCoins m st
      (fun r st' => (if S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m then
          simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)) st')
      tablesOf _ (fun r gC => ?_)
    by_cases h : S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m
    · simp only [h, and_self, ↓reduceIte]
      exact eval_zoom_memoize_map SimState.hqCache (fun st q => { st with hqCache := q })
        S.sampleKey c _ (fun k => k) tablesOf
        (fun q => (RandomOracle.ofList gC, RandomOracle.ofList st.hCache, q)) (fun _ => rfl)
    · simp only [h, ↓reduceIte]
      exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.hCache)
        (fun st h => { st with hCache := h }) S.sampleKey (false, m, c) _ (fun k => k) tablesOf
        (fun h => (RandomOracle.ofList gC, h, RandomOracle.ofList st.hqCache)) (fun _ => rfl)
  · exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.hCache)
      (fun st h => { st with hCache := h }) S.sampleKey (true, m, c) st (fun k => k) tablesOf
      (fun h => (RandomOracle.ofList st.gCache, h, RandomOracle.ofList st.hqCache)) (fun _ => rfl)

/-- `coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk)` on represented tables
`(tG, tH, tQ)`. -/
private noncomputable def answerCachedBotHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) : StateT (Tables M R CT K) PMF (ROResp R K q) :=
  ROQuery.dispatch
    (fun m t => (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m t.1).map
      fun z => (z.1, (z.2, t.2.1, t.2.2)))
    (S.answerHashH pk sk)
    (fun c t =>
      match S.pke.dec sk c with
      | none => PMF.pure (none, t)
      | some m' =>
        match t.1 m' with
        | none => PMF.pure (none, t)
        | some r' =>
          if S.pke.encDet pk m' r' = c then
            (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c t.2.2).map
              fun z => (some z.1, (t.1, t.2.1, z.2))
          else
            PMF.pure (none, t))
    cStar q

private theorem cachedCoupledBotHandler_map_tablesOf (S : Scheme PK SK M R CT K) (pk : PK)
    (sk : SK) (cStar : CT) (q : ROQuery M CT) (st : SimState M R CT K) :
    (ProbComp.eval (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar q
        st)).map (fun z => (z.1, tablesOf z.2)) =
      S.answerCachedBotHandler pk sk cStar q (tablesOf st) := by
  cases q with
  | G m =>
    exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.gCache)
      (fun st g => { st with gCache := g }) S.pke.sampleCoins m st (fun r => r) tablesOf
      (fun g => (g, RandomOracle.ofList st.hCache, RandomOracle.ofList st.hqCache))
      (fun _ => rfl)
  | H x => exact S.coupledHashH_map_tablesOf pk sk x st
  | decaps c =>
    by_cases hc : c = cStar
    · simp only [coupledFilterHandler, simFilterDispatch, answerCachedBotHandler, hc, ↓reduceIte,
        ROQuery.dispatch]
      exact PMF.pure_map _ _
    · dsimp only [coupledFilterHandler, simFilterDispatch, answerCachedBotHandler, ROQuery.dispatch]
      simp only [hc, ↓reduceIte]
      dsimp only [filterDecaps, cachedCoupledBotCheck, tablesOf, RandomOracle.ofList]
      cases hdec : S.pke.dec sk c with
      | none => exact PMF.pure_map _ _
      | some m' =>
        dsimp only
        cases hlook : st.gCache.lookup m' with
        | none => exact PMF.pure_map _ _
        | some r' =>
          dsimp only
          by_cases henc : S.pke.encDet pk m' r' = c
          · simp only [henc, decide_true, Bool.cond_true, ↓reduceIte]
            change (ProbComp.eval (simHashHq S.sampleKey c st >>= fun vs =>
              pure (some vs.1, vs.2))).map _ = _
            refine Eq.trans ?_ (eval_zoom_memoize_map SimState.hqCache
              (fun st q => { st with hqCache := q }) S.sampleKey c st some tablesOf
              (fun q => (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, q))
              (fun _ => rfl))
            rw [ProbComp.eval_bind, PMF.map_bind]
            simp only [ProbComp.eval_pure, PMF.pure_map]
            rfl
          · simp only [henc, decide_false, Bool.cond_false, ↓reduceIte]
            exact PMF.pure_map _ _

section CompleteBot

variable [Fintype M] [Finite R] [Fintype CT] [Finite K]

/-- Full tables `(G, Hraw, Hq)` of the eager coupled game. -/
private abbrev FullTables (M R CT K : Type) : Type :=
  (M → R) × (Bool × M × CT → K) × (CT → K)

/-- Complete the three represented tables independently. -/
private noncomputable def completeTables (S : Scheme PK SK M R CT K) :
    Tables M R CT K → PMF (FullTables M R CT K)
  | (tG, tH, tQ) =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins) tG).bind fun G =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).map fun Q => (G, H, Q)

private noncomputable def eagerCoupledBotStateHandler (S : Scheme PK SK M R CT K) (pk : PK)
    (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    StateT (FullTables M R CT K) PMF (ROResp R K q) :=
  fun T => (S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 pk sk cStar q).map (·, T)

omit [DecidableEq M] [DecidableEq CT] in
/-- At an uncached message `m'` (`tG m' = none`), the `m'`-coordinate of `completeTables` has law
`sampleCoins`. -/
private theorem completeTables_map_eval_at_of_none (S : Scheme PK SK M R CT K)
    (tG : RandomOracle.Cache (fun _ : M => R))
    (tH : RandomOracle.Cache (fun _ : Bool × M × CT => K))
    (tQ : RandomOracle.Cache (fun _ : CT => K))
    (m' : M) (hnone : tG m' = none) :
    (S.completeTables (tG, tH, tQ)).map (fun T => T.1 m') = ProbComp.eval S.pke.sampleCoins := by
  classical
  let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
  have h := (answer_bind_complete dG tG m' (fun x _ => PMF.pure x.1)
    (fun _ _ _ => rfl)).symm
  rw [RandomOracle.answer_of_none dG tG m' hnone] at h
  simp only [pmf_norm, PMF.map, PMF.bind_const, dG] at h
  calc (S.completeTables (tG, tH, tQ)).map (fun T => T.1 m')
      = (RandomOracle.complete dG tG).bind (fun G => PMF.pure (G m')) := by
        simp only [completeTables, pmf_norm, PMF.map, PMF.bind_const, dG]
    _ = ProbComp.eval S.pke.sampleCoins := h

/-- Single-step `CloseTo` simulation from `answerCachedBotHandler` to
`eagerCoupledBotStateHandler`: `.G` and `.H` commute with `completeTables` exactly, while
`.decaps c` commutes up to `2^{-γ}` when `S.pke.dec sk c = some m'` and `t.1 m' = none`. -/
private theorem answerCachedBotHandler_closeTo_sim (S : Scheme PK SK M R CT K) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT)
    (q : ROQuery M CT) (t : Tables M R CT K) :
    CloseTo
      ((S.answerCachedBotHandler pk sk cStar q t).bind
        fun x => (S.completeTables x.2).map (x.1, ·))
      ((S.completeTables t).bind (S.eagerCoupledBotStateHandler pk sk cStar q))
      (q.dCost * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  rcases t with ⟨tG, tH, tQ⟩
  cases q with
  | G m =>
    suffices h : (S.answerCachedBotHandler pk sk cStar (.G m) (tG, tH, tQ)).bind
        (fun x => (S.completeTables x.2).map (x.1, ·)) =
      (S.completeTables (tG, tH, tQ)).bind (S.eagerCoupledBotStateHandler pk sk cStar (.G m)) by
      rw [h]; exact (CloseTo.refl _).mono zero_le
    simp only [answerCachedBotHandler, completeTables, eagerCoupledBotStateHandler,
      eagerCoupledBotHandler, pmf_norm, ROQuery.dispatch]
    rw [answer_bind_complete]
    · rfl
    · intros; rfl
  | H x =>
    suffices h : (S.answerCachedBotHandler pk sk cStar (.H x) (tG, tH, tQ)).bind
        (fun x => (S.completeTables x.2).map (x.1, ·)) =
      (S.completeTables (tG, tH, tQ)).bind (S.eagerCoupledBotStateHandler pk sk cStar (.H x)) by
      rw [h]; exact (CloseTo.refl _).mono zero_le
    rcases x with ⟨_ | _, m, c⟩
    · simp only [answerCachedBotHandler, answerHashH, completeTables, eagerCoupledBotStateHandler,
        eagerCoupledBotHandler, coupledH, pmf_norm, ROQuery.dispatch]
      refine Eq.trans ?_ (answer_bind_complete _ tG m
        (fun x G => (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
          (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).bind fun Q =>
            PMF.pure (if S.pke.encDet pk m x.1 = c ∧ S.pke.dec sk c = some m then Q c
              else H (false, m, c), G, H, Q)) (fun _ _ _ => rfl))
      congr 1 with y : 1
      by_cases h : S.pke.encDet pk m y.1 = c ∧ S.pke.dec sk c = some m
      · simp only [h, and_self, ↓reduceIte, pmf_norm, PMF.map]
        rw [answer_bind_complete₂]
        · pmf_swap
        · intros; rfl
      · simp only [h, ↓reduceIte, pmf_norm, PMF.map]
        rw [answer_bind_complete₁]
        · pmf_swap
        · intros; rfl
    · simp only [answerCachedBotHandler, answerHashH, completeTables, eagerCoupledBotStateHandler,
        eagerCoupledBotHandler, coupledH, pmf_norm, PMF.map, ROQuery.dispatch]
      rw [answer_bind_complete₁]
      · pmf_swap
      · intros; rfl
  | decaps c =>
    simp only [ROQuery.dCost, Nat.cast_one, one_mul]
    change CloseTo
      ((S.answerCachedBotHandler pk sk cStar (.decaps c) (tG, tH, tQ)).bind
        fun x => (S.completeTables x.2).map (x.1, ·))
      ((S.completeTables (tG, tH, tQ)).bind fun T =>
        (S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 pk sk cStar (.decaps c)).map (·, T))
      (ENNReal.ofReal ((2 : ℝ) ^ (-γ)))
    dsimp only [answerCachedBotHandler, eagerCoupledBotHandler, ROQuery.dispatch]
    simp only [decT_eq]
    have hnone_sim : CloseTo
        ((PMF.pure (none, (tG, tH, tQ))).bind
          fun x : Option K × Tables M R CT K => (S.completeTables x.2).map (x.1, ·))
        ((S.completeTables (tG, tH, tQ)).bind
          fun T => (PMF.pure (none : Option K)).map (·, T))
        (ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
      have h : (PMF.pure (none, (tG, tH, tQ))).bind
          (fun x : Option K × Tables M R CT K => (S.completeTables x.2).map (x.1, ·)) =
        (S.completeTables (tG, tH, tQ)).bind
          (fun T => (PMF.pure (none : Option K)).map (·, T)) := by
        simp only [pmf_norm, PMF.map]
      rw [h]; exact (CloseTo.refl _).mono zero_le
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte]
      exact hnone_sim
    · simp only [hc, ↓reduceIte]
      cases hdec : S.pke.dec sk c with
      | none => exact hnone_sim
      | some m' =>
        dsimp only
        cases ht : tG m' with
        | some r' =>
          dsimp only
          suffices h :
              (if S.pke.encDet pk m' r' = c then
                (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c tQ).map
                  fun z => (some z.1, tG, tH, z.2)
              else PMF.pure (none, tG, tH, tQ)).bind
                (fun x => (S.completeTables x.2).map (x.1, ·)) =
              (S.completeTables (tG, tH, tQ)).bind fun T =>
                (PMF.pure (match if encT S.pke T.1 pk m' = c then some m' else none with
                  | some _ => some (T.2.2 c)
                  | none => none)).map (·, T) by
            rw [h]; exact (CloseTo.refl _).mono zero_le
          let dG : M → PMF R := fun _ => ProbComp.eval S.pke.sampleCoins
          have hans : RandomOracle.answer dG m' tG = PMF.pure (r', tG) :=
            RandomOracle.answer_of_some dG tG m' r' ht
          have hR := (answer_bind_complete dG tG m'
            (fun x G =>
              (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
              (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).bind fun Q =>
                PMF.pure (if S.pke.encDet pk m' x.1 = c then some (Q c) else none, G, H, Q))
            (fun _ _ _ => rfl)).symm
          rw [hans, PMF.pure_bind] at hR
          have hR' : ((S.completeTables (tG, tH, tQ)).bind fun T =>
              (PMF.pure (match if encT S.pke T.1 pk m' = c then some m' else none with
                | some _ => some (T.2.2 c)
                | none => none)).map (·, T)) =
              (RandomOracle.complete dG tG).bind fun G =>
              (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
              (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).bind fun Q =>
                PMF.pure (if S.pke.encDet pk m' r' = c then some (Q c) else none, G, H, Q) := by
            refine Eq.trans ?_ hR
            simp only [completeTables, pmf_norm, PMF.map, dG]
            congr 1 with G : 1; congr 1 with H : 1; congr 1 with Q : 1
            by_cases h : S.pke.encDet pk m' (G m') = c <;> simp [encT, h]
          rw [hR']
          by_cases henc : S.pke.encDet pk m' r' = c
          · simp only [henc, ↓reduceIte, completeTables, pmf_norm, PMF.map, dG]
            rw [answer_bind_complete₂]
            · pmf_swap
            · intros; rfl
          · simp only [henc, ↓reduceIte, completeTables, pmf_norm, PMF.map, dG]
        | none =>
          dsimp only
          have hL : ((PMF.pure (none, (tG, tH, tQ))).bind
              fun x : Option K × Tables M R CT K => (S.completeTables x.2).map (x.1, ·)) =
              (S.completeTables (tG, tH, tQ)).map (fun T => ((none : Option K), T)) := by
            rw [PMF.pure_bind]
          have hR : ((S.completeTables (tG, tH, tQ)).bind fun T =>
              (PMF.pure (match if encT S.pke T.1 pk m' = c then some m' else none with
                | some _ => some (T.2.2 c)
                | none => none)).map (·, T)) =
              (S.completeTables (tG, tH, tQ)).map (fun T =>
                (if S.pke.encDet pk m' (T.1 m') = c then some (T.2.2 c) else none, T)) := by
            simp only [PMF.map, PMF.pure_bind, Function.comp_def]
            congr 1 with T : 1
            by_cases h : S.pke.encDet pk m' (T.1 m') = c <;> simp [encT, h]
          rw [hL, hR]
          refine (closeTo_map_of_eq_off (S.completeTables (tG, tH, tQ)) _ _
            {T | S.pke.encDet pk m' (T.1 m') = c} (fun T hT => ?_)).mono ?_
          · have hT' : S.pke.encDet pk m' (T.1 m') ≠ c := hT
            simp [hT']
          · have hmap := S.completeTables_map_eval_at_of_none tG tH tQ m' ht
            have hmeas : (S.completeTables (tG, tH, tQ)).toOuterMeasure
                {T | S.pke.encDet pk m' (T.1 m') = c} =
                (ProbComp.eval S.pke.sampleCoins).toOuterMeasure
                  {r | S.pke.encDet pk m' r = c} := by
              rw [← hmap, PMF.toOuterMeasure_map_apply]
              rfl
            rw [hmeas]
            exact (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _)
              (by positivity)).mpr (hγ pk sk hpk m' c)

private theorem closeTo_run_cachedCoupledBotHandler_eager (S : Scheme PK SK M R CT K) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT) {α : Type}
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α) {d : ℕ}
    (hd : OracleComp.IsCostBounded ROQuery.dCost prog d) (st : SimState M R CT K) :
    CloseTo
      ((ProbComp.eval ((OracleComp.interpret
        (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
        prog).run st)).map Prod.fst)
      ((S.completeTables (tablesOf st)).bind fun T =>
        OracleComp.interpret (S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 pk sk cStar) prog)
      (d * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  have hmap := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state
      (fun q s => ProbComp.eval
        (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar q s))
      (S.answerCachedBotHandler pk sk cStar) tablesOf
      (fun q s => S.cachedCoupledBotHandler_map_tablesOf pk sk cStar q s) prog st)
  simp only [PMF.map_comp, Function.comp_def] at hmap
  rw [hmap]
  have hsim := (run_interpret_closeTo_simulation ROQuery.dCost
    (S.answerCachedBotHandler pk sk cStar) (S.eagerCoupledBotStateHandler pk sk cStar)
    S.completeTables (ENNReal.ofReal ((2 : ℝ) ^ (-γ)))
    (fun q t => S.answerCachedBotHandler_closeTo_sim hγ hpk cStar q t) prog hd
    (tablesOf st)).map Prod.fst
  have hL : (((OracleComp.interpret (S.answerCachedBotHandler pk sk cStar) prog).run
      (tablesOf st)).bind (fun x => (S.completeTables x.2).map (x.1, ·))).map Prod.fst =
      ((OracleComp.interpret (S.answerCachedBotHandler pk sk cStar) prog).run
        (tablesOf st)).map Prod.fst := by
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, PMF.bind_const]
  have hR : ((S.completeTables (tablesOf st)).bind fun T =>
      (OracleComp.interpret (S.eagerCoupledBotStateHandler pk sk cStar) prog).run T).map
        Prod.fst =
      (S.completeTables (tablesOf st)).bind fun T =>
        OracleComp.interpret (S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 pk sk cStar) prog := by
    rw [PMF.map_bind]
    congr 1 with T : 1
    have hro := congrArg (PMF.map Prod.fst)
      (OracleComp.run_interpret_readOnly
        (fun q T' => S.eagerCoupledBotHandler T'.1 T'.2.2 T'.2.1 pk sk cStar q) prog T)
    change ((OracleComp.interpret (S.eagerCoupledBotStateHandler pk sk cStar) prog).run T).map
        Prod.fst =
      ((OracleComp.interpret (fun q => S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 pk sk cStar q)
        prog).map (fun a => (a, T))).map Prod.fst at hro
    rw [PMF.map_comp] at hro
    exact hro.trans (PMF.map_id _)
  rwa [hL, hR] at hsim

/-- **Lazy and `γ`-spreadness CVO hop for `FO^⊥`** ([HofheinzHoevelmannsKiltz2017], §3.1):
replacing `eagerCoupledBotGame` (where decapsulation evaluates `decT` on the full table `G`) by
`cachedCoupledBotGame` (where decapsulation only checks coins already cached in `gCache` from
`mStar`, `G`, or `H`) changes the output distribution by at most `qD · 2^{-γ}`. -/
theorem closeTo_cachedCoupledBotGame_eagerCoupledBotGame
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH qD : ℕ}
    (hq : ROFullQueryBounds A qG qH qD) {γ : ℝ} (hγ : S.pke.GammaSpread γ) (b : Bool) :
    CloseTo (ProbComp.eval (S.cachedCoupledBotGame A b)) (S.eagerCoupledBotGame A b)
      (qD * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  set ε := (qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))
  have hconst {α : Type} (μ : PMF α) : ∑' a, μ a * ε = ε := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hL : ProbComp.eval (S.cachedCoupledBotGame A b) =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
      (ProbComp.eval S.sampleKey).bind fun kRand =>
        let cStar := S.pke.encDet keys.1 mStar rStar
        (ProbComp.eval ((OracleComp.interpret
          (S.coupledFilterHandler (cachedCoupledBotCheck S.pke keys.1 keys.2) keys.1 keys.2 cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A ⟨keys.1, cStar, if b then kRand else k⟩)).run
          { gCache := [(mStar, rStar)] })).map Prod.fst := by
    dsimp only [cachedCoupledBotGame, coupledFilterGame]
    simp only [pmf_norm]
    congr 1 with ⟨pk, sk⟩ : 1
    congr 1 with mStar : 1
    congr 1 with rStar : 1
    set cStar := S.pke.encDet pk mStar rStar
    have hP (kRand : K) :
        (ProbComp.eval ((OracleComp.interpret
          (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A ⟨pk, cStar, if b then kRand else k⟩)).run
          { gCache := [(mStar, rStar)] })).map Prod.fst =
        (ProbComp.eval ((S.coupledHashH pk sk (false, mStar, cStar)).run
          { gCache := [(mStar, rStar)] })).bind (fun z =>
          (ProbComp.eval ((OracleComp.interpret
            (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
            (A ⟨pk, cStar, if b then kRand else z.1⟩)).run z.2)).bind fun a => PMF.pure a.1) := by
      rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      simp only [pmf_norm]
      rfl
    rw [PMF.bind_comm]
    simp only [← hP]
  have hR : S.eagerCoupledBotGame A b =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
      (ProbComp.eval S.sampleKey).bind fun kRand =>
        let cStar := S.pke.encDet keys.1 mStar rStar
        (S.completeTables (tablesOf ({ gCache := [(mStar, rStar)] } : SimState M R CT K))).bind
          fun T => OracleComp.interpret
            (S.eagerCoupledBotHandler T.1 T.2.2 T.2.1 keys.1 keys.2 cStar)
            (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
              (ROQuery.H (false, mStar, cStar)) >>= fun k =>
                A ⟨keys.1, cStar, if b then kRand else k⟩) := by
    dsimp only [eagerCoupledBotGame]
    simp only [completeTables, tablesOf, RandomOracle.complete_ofList_singleton,
      RandomOracle.ofList_nil, RandomOracle.complete_empty, OracleComp.interpret_bind,
      OracleComp.interpret_query, eagerCoupledBotHandler, pmf_norm, encT, ROQuery.dispatch]
    congr 1 with ⟨pk, sk⟩ : 1
    dsimp only
    pmf_hoist (ProbComp.eval S.sampleMsg)
    congr 1 with mStar : 1
    refine Eq.symm (Eq.trans ?_
      (bind_pi_update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar
        (fun rStar G =>
          (pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind fun Hq =>
          (pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind
            fun Hraw =>
          (ProbComp.eval S.sampleKey).bind fun kRand =>
            OracleComp.interpret
              (S.eagerCoupledBotHandler G Hq Hraw pk sk (S.pke.encDet pk mStar rStar))
              (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else
                S.coupledH G Hq Hraw pk sk (false, mStar, S.pke.encDet pk mStar rStar)⟩))))
    congr 1 with rStar : 1
    pmf_swap
  rw [hL, hR]
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun keys hkeys => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun mStar _ => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun rStar _ => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun kRand _ => ?_).mono
    (le_of_eq (hconst _))
  set cStar := S.pke.encDet keys.1 mStar rStar
  have hd : OracleComp.IsCostBounded ROQuery.dCost
      (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
        (ROQuery.H (false, mStar, cStar)) >>= fun k =>
          A ⟨keys.1, cStar, if b then kRand else k⟩) qD :=
    OracleComp.IsCostBounded.liftBind (ROQuery.H (false, mStar, cStar)) _ qD fun k =>
      hq.2 ⟨keys.1, cStar, if b then kRand else k⟩
  exact S.closeTo_run_cachedCoupledBotHandler_eager hγ hkeys cStar _ hd _

end CompleteBot

/-! ### Section 3: Keyless Simulator, Correctness Hop, Challenge Hop, and Main Theorem -/

/-- Decapsulation filter of the keyless `FO^⊥` simulator `simBotHandler`: accepts `c` when some
message `p.1` in `gCache` has active cached coin `gCache.lookup p.1 = some r` satisfying
`Enc(pk, p.1; r) = c`. -/
def simBotCheck (P : ExplicitCoinPKE PK SK M R CT) (pk : PK)
    (gCache : List (M × R)) (c : CT) : Bool :=
  gCache.any fun p =>
    match gCache.lookup p.1 with
    | none => false
    | some r => decide (P.encDet pk p.1 r = c)

/-- Stateful oracle handler for the keyless ROM simulator of the `FO^⊥` IND-CCA game: answers
`G` and `H` as in `simHandler`, and answers punctured decapsulation queries `c ≠ cStar` with
`some (H_q(c))` when `simBotCheck S.pke pk st.gCache c = true` and `none` otherwise. -/
def simBotHandler (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterHandler (simBotCheck S.pke pk) pk cStar q

/-- The lazy keyless simulator game for `FO^⊥` with challenge coin `G(m*)` programmed. -/
def simBotGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp Bool :=
  S.simFilterGame (simBotCheck S.pke) A b

/-- IND-CPA adversary built from a ROM IND-CCA adversary `A` against `FO^⊥`: runs
`A ⟨pk, cStar, kStar⟩` against `S.simBotHandler pk cStar` from empty caches and outputs whether `m1`
was queried to `G`. -/
def romBotCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (m0 m1 : M) : PK → CT → ProbComp Bool :=
  S.romFilterCpaReduction (simBotCheck S.pke) A m0 m1

private theorem simBotCheck_eq_true_iff (P : ExplicitCoinPKE PK SK M R CT) (pk : PK)
    (L : List (M × R)) (c : CT) :
    simBotCheck P pk L c = true ↔
      ∃ m r, L.lookup m = some r ∧ P.encDet pk m r = c := by
  simp only [simBotCheck, List.any_eq_true, Prod.exists]
  constructor
  · rintro ⟨m, _, -, h⟩
    cases hlook : L.lookup m with
    | none => simp [hlook] at h
    | some r => exact ⟨m, r, hlook, by simpa [hlook] using h⟩
  · rintro ⟨m, r, hlook, henc⟩
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hlook
    exact ⟨m, r, by simp [hlist], by simp [hlook, henc]⟩

/-- On any state satisfying `GoodCache`, the secret-key decapsulation check
`cachedCoupledBotCheck` agrees with the keyless check `simBotCheck`. -/
private theorem cachedCoupledBotCheck_eq_simBotCheck_of_goodCache (S : Scheme PK SK M R CT K)
    (pk : PK) (sk : SK) (st : SimState M R CT K) (c : CT)
    (hgood : GoodCache S.pke pk sk st) :
    cachedCoupledBotCheck S.pke pk sk st.gCache c = simBotCheck S.pke pk st.gCache c := by
  apply Bool.eq_iff_iff.mpr
  rw [simBotCheck_eq_true_iff]
  simp only [cachedCoupledBotCheck]
  constructor
  · intro h
    cases hdec : S.pke.dec sk c with
    | none => simp [hdec] at h
    | some m' =>
      simp only [hdec] at h
      cases hlook : st.gCache.lookup m' with
      | none => simp [hlook] at h
      | some r' => exact ⟨m', r', hlook, by simpa [hlook] using h⟩
  · rintro ⟨m', r', hlook, henc⟩
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hlook
    have hdec : S.pke.dec sk c = some m' := henc ▸ hgood (m', r') (by simp [hlist])
    simp [hdec, hlook, henc]

/-- **Correctness hop for `FO^⊥`**: for an adversary making at most `qG` queries to `G` and `qH`
queries to `H` against a `δ`-correct PKE, `cachedCoupledBotGame` and `simBotGame` have
distinguishing advantage at most `(qG + qH + 1) δ`. -/
theorem advantage_cachedCoupledBotGame_simBotGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) (b : Bool) :
    (Game.advantage (ProbComp.eval (S.cachedCoupledBotGame A b))
        (ProbComp.eval (S.simBotGame A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ :=
  S.advantage_coupledFilterGame_simFilterGame_le (cachedCoupledBotCheck S.pke) (simBotCheck S.pke)
    S.cachedCoupledBotCheck_eq_simBotCheck_of_goodCache A hq hδ b

/-- At any punctured ciphertext `c ≠ Enc(pk, mStar; rStar)`, programming `(mStar, rStar)` via `ens`
leaves `simBotCheck` unchanged whenever `LookupNoneOr mStar rStar L` holds. -/
private theorem simBotCheck_ens (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M) (rStar : R)
    (L : List (M × R)) (c : CT) (hc : c ≠ S.pke.encDet pk mStar rStar)
    (hL : LookupNoneOr mStar rStar L) :
    simBotCheck S.pke pk (ens mStar rStar L) c = simBotCheck S.pke pk L c := by
  apply Bool.eq_iff_iff.mpr
  simp only [simBotCheck_eq_true_iff, lookup_ens]
  constructor
  · rintro ⟨m, r, hlook, henc⟩
    by_cases hm : m = mStar
    · subst hm
      simp only [↓reduceIte, Option.some.injEq] at hlook
      exact absurd (hlook ▸ henc).symm hc
    · simp only [hm, ↓reduceIte] at hlook
      exact ⟨m, r, hlook, henc⟩
  · rintro ⟨m, r, hlook, henc⟩
    have hm : m ≠ mStar := by
      rintro rfl
      rcases hL with hnone | hsome
      · rw [hnone] at hlook; cases hlook
      · rw [hsome] at hlook; cases hlook; exact hc henc.symm
    exact ⟨m, r, by simp [hm, hlook], henc⟩

/-- **Challenge hop for `FO^⊥`**: if the message sampler is uniform on a message space with at
least two elements and the PKE is `γ`-spread, then for every adversary making at most `qG` queries
to `G` and `qH` queries to `H`, some distinct messages `m₀ ≠ m₁` bound the advantage between
`simBotGame A false` and `simBotGame A true` by
`2 Adv_CPA(romBotCpaReduction A m₀ m₁) + 2 (qG + qH)/|M| + 2 (qG + qH) 2^(-γ)`. -/
theorem advantage_simBotGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (Game.advantage (ProbComp.eval (S.simBotGame A false))
          (ProbComp.eval (S.simBotGame A true)) : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romBotCpaReduction A m₀ m₁) : ℝ) +
          2 * (((qG : ℝ) + qH) / Fintype.card M) +
            2 * (((qG : ℝ) + qH) * (2 : ℝ) ^ (-γ)) :=
  S.advantage_simFilterGame_le (simBotCheck S.pke) S.simBotCheck_ens A hq hM hmsg hγ

/-- **Hybrid chain for one challenge bit of `FO^⊥`**: for a `δ`-correct and `γ`-spread PKE and an
adversary satisfying `ROFullQueryBounds A qG qH qD`, the eager IND-CCA game of `FO^⊥` and the
keyless simulator game `simBotGame` differ by at most `(qG + qH + 1) δ + qD · 2^{-γ}`. -/
theorem advantage_eagerIndCcaBotGame_simBotGame_le [Fintype M] [Nonempty M] [Finite R]
    [Fintype CT] [Finite K] (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH qD : ℕ} (hq : ROFullQueryBounds A qG qH qD) {δ γ : ℝ}
    (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) (b : Bool) :
    (Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.simBotGame A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ + qD * (2 : ℝ) ^ (-γ) := by
  have hclose := (S.closeTo_cachedCoupledBotGame_eagerCoupledBotGame A hq hγ b).symm
  rw [eagerCoupledBotGame_eq_eagerIndCcaBotGame] at hclose
  have hadv₁ : (Game.advantage (S.eagerIndCcaBotGame A b)
      (ProbComp.eval (S.cachedCoupledBotGame A b)) : ℝ≥0∞) ≤
      (qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) :=
    Game.closeTo_iff_coe_advantage_le.mp hclose
  have htop : ((qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have h₁ : (Game.advantage (S.eagerIndCcaBotGame A b)
      (ProbComp.eval (S.cachedCoupledBotGame A b)) : ℝ) ≤ qD * (2 : ℝ) ^ (-γ) := by
    have hr := ENNReal.toReal_mono htop hadv₁
    rwa [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)] at hr
  have h₂ := S.advantage_cachedCoupledBotGame_simBotGame_le A hq.1 hδ b
  calc (Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.simBotGame A b)) : ℝ)
      ≤ Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.cachedCoupledBotGame A b)) +
          Game.advantage (ProbComp.eval (S.cachedCoupledBotGame A b))
            (ProbComp.eval (S.simBotGame A b)) := by
        exact_mod_cast Game.advantage_triangle _ _ _
    _ ≤ qD * (2 : ℝ) ^ (-γ) + ((qG + qH + 1 : ℕ) : ℝ) * δ := add_le_add h₁ h₂
    _ = ((qG + qH + 1 : ℕ) : ℝ) * δ + qD * (2 : ℝ) ^ (-γ) := add_comm _ _

/-- **ROM IND-CCA security of `FO^⊥ = U^⊥ ∘ T`** ([HofheinzHoevelmannsKiltz2017], §3.1 and §3.2.1,
composed directly): for uniform messages, a `δ`-correct and `γ`-spread PKE, and an adversary making
at most `qG` queries to `G`, `qH` queries to `H`, and `qD` queries to `decaps`, there are distinct
messages `m₀ ≠ m₁` with
`Adv^{IND-CCA}_{FO^⊥}(A) ≤ 2 · Adv^{IND-CPA}_{m₀, m₁}(romBotCpaReduction A m₀ m₁)
  + 2 (qG + qH) / |M| + 2 (qG + qH + 1) δ + 2 (qG + qH + qD) 2^{-γ}`.
Both real `H` replies and the independent ideal challenge key in `roIndCcaBotGame` and
`eagerIndCcaBotGame` are drawn from the arbitrary key sampler `S.sampleKey : ProbComp K`; taking
`S.sampleKey` uniform on `K` recovers the standard uniform-ideal-key experiment of
[HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 / Fig. 4. -/
theorem indCcaBotAdvantage_le [Fintype M] [Nonempty M] [Finite R] [Finite CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH qD : ℕ}
    (hq : ROFullQueryBounds A qG qH qD) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M)
    {δ γ : ℝ} (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (S.indCcaBotAdvantage A : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romBotCpaReduction A m₀ m₁) : ℝ) +
          2 * (qG + qH) / Fintype.card M + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ +
          2 * ((qG + qH + qD) * (2 : ℝ) ^ (-γ)) := by
  have : Fintype CT := Fintype.ofFinite CT
  obtain ⟨m₀, m₁, hne, hsim⟩ := S.advantage_simBotGame_le A hq.1 hM hmsg hγ
  refine ⟨m₀, m₁, hne, ?_⟩
  have hF := S.advantage_eagerIndCcaBotGame_simBotGame_le A hq hδ hγ false
  have hT := S.advantage_eagerIndCcaBotGame_simBotGame_le A hq hδ hγ true
  rw [indCcaBotAdvantage_eq_eager]
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  calc _ ≤ _ :=
        Game.advantage_four_le (S.eagerIndCcaBotGame A) (fun b => ProbComp.eval (S.simBotGame A b))
          hF hsim hT
    _ = _ := by field_simp; ring

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
