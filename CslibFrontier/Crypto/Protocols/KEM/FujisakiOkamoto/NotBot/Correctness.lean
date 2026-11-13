/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.UntilBad
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.BindFailure

/-!
# Correctness hop of the `FO-notbot` IND-CCA proof

This module bounds the distance between the lazy coupled game `Scheme.coupledGame` and the keyless
simulator game `Scheme.simGame` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids` by the decryption error of the
underlying PKE. This is the correctness step of the proof of the §3.1 theorem for `T` in
[HofheinzHoevelmannsKiltz2017], where the random oracle `G` is replaced by good coins.

The two games differ only in the decryption test `Dec(sk, c) = some m` of the key-derivation
oracle `H(false, m, c)`. For a fixed key pair, both are run on the same `SimState`, and a state is
*bad* when some coin `r` cached for a message `m` in `gCache` fails to decrypt
(`Dec(sk, Enc(pk, m; r)) ≠ some m`). Caches only grow, so bad states are absorbing, and from a good
state the two handlers agree on every transition into a good state: a cached coin `r = G(m)` with
`Enc(pk, m; r) = c` then forces `Dec(sk, c) = some m`. The difference lemma bounds the distance by
the probability of reaching a bad state. Every `G` or `H` query samples at most one fresh coin,
which fails with probability at most the worst-case message failure probability, while the
challenge coin `r*` accounts for one more term. Averaging over key generation with `δ`-correctness
gives the bound `(qG + qH + 1) δ`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_coupledGame_simGame_le`: for an
  adversary making at most `qG` queries to `G` and `qH` queries to `H` against a `δ`-correct PKE,
  the distinguishing advantage between `coupledGame` and `simGame` is at most `(qG + qH + 1) δ`.

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

variable [DecidableEq M] [DecidableEq CT]

/-- Every coin cached in `gCache` decrypts correctly for its message. -/
@[expose] def GoodCache (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK)
    (st : SimState M R CT K) : Prop :=
  ∀ e ∈ st.gCache, P.dec sk (P.encDet pk e.1 e.2) = some e.1

omit [DecidableEq M] [DecidableEq CT] in
theorem GoodCache.of_subset {P : ExplicitCoinPKE PK SK M R CT} {pk : PK} {sk : SK}
    {st st' : SimState M R CT K} (h : GoodCache P pk sk st')
    (hsub : ∀ e ∈ st.gCache, e ∈ st'.gCache) : GoodCache P pk sk st :=
  fun e he => h e (hsub e he)

omit [DecidableEq CT] in
private theorem mem_support_simHashG {sc : ProbComp R} {m : M} {st : SimState M R CT K}
    {z : R × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashG sc m st)).support) :
    (st.gCache.lookup m = some z.1 ∧ z.2 = st) ∨
    (st.gCache.lookup m = none ∧ z.1 ∈ (ProbComp.eval sc).support ∧
      z.2 = { st with gCache := (m, z.1) :: st.gCache }) := by
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, PMF.mem_support_map_iff] at hz
  obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · left; dsimp only at h1 h2 ⊢; subst h2; exact ⟨h1, rfl⟩
  · right; dsimp only at h1 h2 h3 ⊢; subst h3; exact ⟨h1, h2, rfl⟩

omit [DecidableEq CT] in
private theorem simHashG_gCache_subset {sc : ProbComp R} {m : M} {st : SimState M R CT K}
    {z : R × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashG sc m st)).support) :
    ∀ e ∈ st.gCache, e ∈ z.2.gCache := by
  intro e he
  rcases mem_support_simHashG hz with ⟨-, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact he
  · exact List.mem_cons_of_mem _ he

omit [DecidableEq CT] in
private theorem simHashG_mem_gCache {sc : ProbComp R} {m : M} {st : SimState M R CT K}
    {z : R × SimState M R CT K} (hz : z ∈ (ProbComp.eval (simHashG sc m st)).support) :
    (m, z.1) ∈ z.2.gCache := by
  rcases mem_support_simHashG hz with ⟨h1, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · obtain ⟨l₁, l₂, htable, -⟩ := List.lookup_eq_some_iff.mp h1
    rw [htable]
    simp
  · exact List.mem_cons_self

/-- Lazy `H(false, m, c)` oracle that reads `H_q(c)` exactly when the coin test `t (G m)` holds. -/
private def testHashH (S : Scheme PK SK M R CT K) (m : M) (c : CT) (t : R → Prop)
    [DecidablePred t] : StateT (SimState M R CT K) ProbComp K := do
  let r ← simHashG S.pke.sampleCoins m
  if t r then simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)

/-- Common shape of `coupledFilterHandler` and `simFilterHandler`, parametrized by the decapsulation
filter `d` and the coin test of `H`. -/
private def testHandler (S : Scheme PK SK M R CT K) (d : List (M × R) → CT → Bool)
    (cStar : CT) (t : M → CT → R → Prop)
    [∀ m c, DecidablePred (t m c)] (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterDispatch
    (fun
      | (false, m, c) => S.testHashH m c (t m c)
      | (true, m, c) => simHashHRaw S.sampleKey (true, m, c))
    d cStar q

private theorem coupledFilterHandler_eq (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (sk : SK) (cStar : CT) :
    S.coupledFilterHandler d pk sk cStar = S.testHandler d cStar
      (fun m c r => S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m) := by
  funext q
  rcases q with m | ⟨_ | _, m, c⟩ | c <;> rfl

private theorem simFilterHandler_eq (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (cStar : CT) :
    S.simFilterHandler d pk cStar =
      S.testHandler d cStar (fun m c r => S.pke.encDet pk m r = c) := by
  funext q
  rcases q with m | ⟨_ | _, m, c⟩ | c <;> rfl

private theorem eval_testHashH (S : Scheme PK SK M R CT K) (m : M) (c : CT) (t : R → Prop)
    [DecidablePred t] (st : SimState M R CT K) :
    ProbComp.eval (S.testHashH m c t st) =
      (ProbComp.eval (simHashG S.pke.sampleCoins m st)).bind fun z =>
        ProbComp.eval ((if t z.1 then simHashHq S.sampleKey c
          else simHashHRaw S.sampleKey (false, m, c)) z.2) := by
  change ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun z =>
    (if t z.1 then simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)) z.2) = _
  rw [ProbComp.eval_bind]

/-- The `H_q`/raw continuation of `testHashH` leaves `gCache` unchanged. -/
private theorem testCont_gCache_eq (S : Scheme PK SK M R CT K) (m : M) (c : CT) (p : Prop)
    [Decidable p] (st : SimState M R CT K) (x : K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval ((if p then simHashHq S.sampleKey c
      else simHashHRaw S.sampleKey (false, m, c)) st)).support) :
    x.2.gCache = st.gCache := by
  split_ifs at hx
  · exact simHashHq_gCache_eq _ _ _ _ hx
  · exact simHashHRaw_gCache_eq _ _ _ _ hx

private theorem mem_support_testHashH (S : Scheme PK SK M R CT K) (m : M) (c : CT)
    (t : R → Prop) [DecidablePred t] (st : SimState M R CT K) (x : K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.testHashH m c t st)).support) :
    ∃ z ∈ (ProbComp.eval (simHashG S.pke.sampleCoins m st)).support, x.2.gCache = z.2.gCache := by
  rw [eval_testHashH, PMF.mem_support_bind_iff] at hx
  obtain ⟨z, hz, hx⟩ := hx
  exact ⟨z, hz, testCont_gCache_eq S m c _ z.2 x hx⟩

/-- On a final state whose cache is good, `testHashH` does not depend on how the coin test treats
coins that fail to decrypt. -/
private theorem eval_testHashH_apply_congr (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (m : M) (c : CT) (t₁ t₂ : R → Prop) [DecidablePred t₁] [DecidablePred t₂]
    (ht : ∀ r, S.pke.dec sk (S.pke.encDet pk m r) = some m → (t₁ r ↔ t₂ r))
    (st : SimState M R CT K) (y : K × SimState M R CT K) (hy : GoodCache S.pke pk sk y.2) :
    ProbComp.eval (S.testHashH m c t₁ st) y = ProbComp.eval (S.testHashH m c t₂ st) y := by
  rw [eval_testHashH, eval_testHashH, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ (ProbComp.eval (simHashG S.pke.sampleCoins m st)).support
  · by_cases hgz : GoodCache S.pke pk sk z.2
    · have hiff := ht z.1 (hgz _ (simHashG_mem_gCache hz))
      by_cases h1 : t₁ z.1
      · simp only [h1, hiff.mp h1, ↓reduceIte]
      · simp only [h1, (not_congr hiff).mp h1, ↓reduceIte]
    · have h0 (p : Prop) [Decidable p] :
          ProbComp.eval ((if p then simHashHq S.sampleKey c
            else simHashHRaw S.sampleKey (false, m, c)) z.2) y = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => hgz ?_
        exact hy.of_subset fun e he => by rwa [testCont_gCache_eq S m c p z.2 y hmem]
      rw [h0, h0]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]

omit [DecidableEq M] [DecidableEq CT] in
private theorem toOuterMeasure_notGood_eq_zero {P : ExplicitCoinPKE PK SK M R CT} {pk : PK}
    {sk : SK} {α : Type} {st : SimState M R CT K} (hs : GoodCache P pk sk st)
    {μ : PMF (α × SimState M R CT K)} (h : ∀ x ∈ μ.support, ∀ e ∈ x.2.gCache, e ∈ st.gCache) :
    μ.toOuterMeasure {x | ¬GoodCache P pk sk x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hbad
  exact hbad (hs.of_subset (h x hx))

omit [DecidableEq CT] in
/-- From a good cache, one lazy `G` query reaches a bad cache with probability at most the
message failure probability. -/
private theorem simHashG_bad_le (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M)
    {st : SimState M R CT K} (hs : GoodCache P pk sk st) :
    (ProbComp.eval (simHashG P.sampleCoins m st)).toOuterMeasure
        {z | ¬GoodCache P pk sk z.2} ≤ ENNReal.ofReal (P.msgFailProb pk sk m) := by
  cases h : st.gCache.lookup m with
  | some r =>
    refine le_of_eq_of_le (toOuterMeasure_notGood_eq_zero hs fun z hz e he => ?_) zero_le
    rcases mem_support_simHashG hz with ⟨-, h2⟩ | ⟨h1, -, -⟩
    · rwa [h2] at he
    · rw [h] at h1; cases h1
  | none =>
    have hmarg : (ProbComp.eval (simHashG P.sampleCoins m st)).map Prod.fst =
        ProbComp.eval P.sampleCoins := by
      rw [simHashG, RandomOracle.eval_zoomStateT_memoize, memoize_of_none _ _ _ h]
      simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
    calc _ ≤ (ProbComp.eval (simHashG P.sampleCoins m st)).toOuterMeasure
          (Prod.fst ⁻¹' {r | P.dec sk (P.encDet pk m r) ≠ some m}) := by
          refine PMF.toOuterMeasure_mono _ ?_
          rintro z ⟨hbad, hz⟩
          rcases mem_support_simHashG hz with ⟨h1, -⟩ | ⟨-, -, h2⟩
          · rw [h] at h1; cases h1
          · intro hdec
            refine hbad fun e he => ?_
            rw [h2] at he
            rcases List.mem_cons.mp he with rfl | he
            · exact hdec
            · exact hs e he
      _ = _ := by
          rw [← PMF.toOuterMeasure_map_apply, hmarg, ExplicitCoinPKE.msgFailProb,
            ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)]

private theorem testHashH_bad_le (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (m : M) (c : CT)
    (t : R → Prop) [DecidablePred t] {st : SimState M R CT K} (hs : GoodCache S.pke pk sk st) :
    (ProbComp.eval (S.testHashH m c t st)).toOuterMeasure {x | ¬GoodCache S.pke pk sk x.2} ≤
      ENNReal.ofReal (S.pke.msgFailProb pk sk m) := by
  rw [eval_testHashH]
  refine (Probability.PMF.toOuterMeasure_bind_le_add _ _ {z | ¬GoodCache S.pke pk sk z.2} _ 0
    fun z _ hgood => ?_).trans (by rw [add_zero]; exact simHashG_bad_le _ _ _ m hs)
  refine le_of_eq (toOuterMeasure_notGood_eq_zero (of_not_not hgood) fun x hx e he => ?_)
  rwa [testCont_gCache_eq S m c _ z.2 x hx] at he

private theorem testHandler_decaps_gCache_eq (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (cStar : CT)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (c : CT) (st : SimState M R CT K)
    (x : Option K × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.testHandler d cStar t (.decaps c) st)).support) :
    x.2.gCache = st.gCache := by
  dsimp only [testHandler, simFilterDispatch, ROQuery.dispatch] at hx
  exact gCache_eq_of_mem_support_filterDecaps _ _ _ _ _ _ hx

private theorem testHandler_gCache_subset (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (cStar : CT)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)] (q : ROQuery M CT)
    (st : SimState M R CT K) (x : ROResp R K q × SimState M R CT K)
    (hx : x ∈ (ProbComp.eval (S.testHandler d cStar t q st)).support) :
    ∀ e ∈ st.gCache, e ∈ x.2.gCache := by
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · exact simHashG_gCache_subset hx
  · obtain ⟨z, hz, heq⟩ := mem_support_testHashH S m c _ st x hx
    intro e he
    rw [heq]
    exact simHashG_gCache_subset hz e he
  · intro e he
    rwa [simHashHRaw_gCache_eq _ _ _ _ hx]
  · intro e he
    rwa [testHandler_decaps_gCache_eq S d cStar t c st x hx]

private theorem testHandler_bad_le [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK)
    (sk : SK) (cStar : CT) (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    (q : ROQuery M CT) {st : SimState M R CT K} (hs : GoodCache S.pke pk sk st) :
    (ProbComp.eval (S.testHandler d cStar t q st)).toOuterMeasure
        {x | ¬GoodCache S.pke pk sk x.2} ≤
      q.ghCost * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  have hmax (m : M) : ENNReal.ofReal (S.pke.msgFailProb pk sk m) ≤
      ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) :=
    ENNReal.ofReal_le_ofReal (S.pke.msgFailProb_le_keyPairMaxFailProb pk sk m)
  rcases q with m | ⟨_ | _, m, c⟩ | c
  · simp only [ROQuery.ghCost, Nat.cast_one, one_mul]
    exact (simHashG_bad_le S.pke pk sk m hs).trans (hmax m)
  · simp only [ROQuery.ghCost, Nat.cast_one, one_mul]
    exact (testHashH_bad_le S pk sk m c _ hs).trans (hmax m)
  · refine le_of_eq_of_le (toOuterMeasure_notGood_eq_zero hs fun x hx e he => ?_) zero_le
    rwa [simHashHRaw_gCache_eq _ _ _ _ hx] at he
  · refine le_of_eq_of_le (toOuterMeasure_notGood_eq_zero hs fun x hx e he => ?_) zero_le
    rwa [testHandler_decaps_gCache_eq S d cStar t c st x hx] at he

/-- Two instances of `testHandler` whose coin tests and decapsulation filters agree on good caches
are identical until a cached coin fails to decrypt. -/
private theorem identicalUntilBad_testHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (d₁ d₂ : List (M × R) → CT → Bool)
    (t₁ t₂ : M → CT → R → Prop) [∀ m c, DecidablePred (t₁ m c)]
    [∀ m c, DecidablePred (t₂ m c)]
    (hd : ∀ (st : SimState M R CT K) c, GoodCache S.pke pk sk st →
      d₁ st.gCache c = d₂ st.gCache c)
    (ht : ∀ m c r, S.pke.dec sk (S.pke.encDet pk m r) = some m → (t₁ m c r ↔ t₂ m c r)) :
    OracleComp.IdenticalUntilBad (fun q st => ProbComp.eval (S.testHandler d₁ cStar t₁ q st))
      (fun q st => ProbComp.eval (S.testHandler d₂ cStar t₂ q st))
      (fun st => ¬GoodCache S.pke pk sk st) where
  agree q s hs a s' hs' := by
    rcases q with m | ⟨_ | _, m, c⟩ | c
    · rfl
    · exact eval_testHashH_apply_congr S pk sk m c _ _ (ht m c) s (a, s') (of_not_not hs')
    · rfl
    · by_cases hc : c = cStar <;>
        simp [testHandler, simFilterDispatch, hc, hd s c (of_not_not hs), filterDecaps]
  absorb_first q s hs x hx := fun hg =>
    hs (hg.of_subset (testHandler_gCache_subset S d₁ cStar t₁ q s x hx))
  absorb_second q s hs x hx := fun hg =>
    hs (hg.of_subset (testHandler_gCache_subset S d₂ cStar t₂ q s x hx))

private theorem testHandler_run_bad_le [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (d : List (M × R) → CT → Bool) (pk : PK) (sk : SK) (cStar : CT)
    (t : M → CT → R → Prop) [∀ m c, DecidablePred (t m c)]
    {α : Type} {prog : OracleComp (ROResp (M := M) (CT := CT) R K) α} {k : ℕ}
    (hk : OracleComp.IsCostBounded ROQuery.ghCost prog k) {st : SimState M R CT K}
    (hs : GoodCache S.pke pk sk st) :
    ((OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q st => ProbComp.eval (S.testHandler d cStar t q st)) prog).run st).toOuterMeasure
        {x | ¬GoodCache S.pke pk sk x.2} ≤
      k * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) := by
  have h := OracleComp.toOuterMeasure_bad_le_two
    (handler := fun q st => ProbComp.eval (S.testHandler d cStar t q st))
    (bad := fun st => ¬GoodCache S.pke pk sk st) ROQuery.ghCost (fun _ => 0)
    (fun _ => ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) 0 0 0
    (fun q s hs => by
      simpa only [Nat.cast_zero, zero_mul, add_zero] using
        testHandler_bad_le S d pk sk cStar t q (of_not_not hs))
    (fun _ _ _ _ _ _ => by simp) hk
    (OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) prog) (not_not.mpr hs)
  simpa only [mul_zero, add_zero, Nat.cast_zero] using h

/-- The two lazy runs from a good cache are statistically close up to the failure budget. -/
private theorem closeTo_run_coupled_sim [Fintype M] [Nonempty M] (S : Scheme PK SK M R CT K)
    (pk : PK) (sk : SK) (cStar : CT) (d₁ d₂ : List (M × R) → CT → Bool)
    (hd : ∀ (st : SimState M R CT K) c, GoodCache S.pke pk sk st →
      d₁ st.gCache c = d₂ st.gCache c)
    {α β : Type} (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α) {k : ℕ}
    (hk : OracleComp.IsCostBounded ROQuery.ghCost prog k) {st : SimState M R CT K}
    (hs : GoodCache S.pke pk sk st) (next : α × SimState M R CT K → PMF β) :
    CloseTo (((OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q state => ProbComp.eval (S.coupledFilterHandler d₁ pk sk cStar q state)) prog).run
          st).bind next)
      (((OracleComp.interpret (m := StateT (SimState M R CT K) PMF)
        (fun q state => ProbComp.eval (S.simFilterHandler d₂ pk cStar q state)) prog).run st).bind
          next)
      (k * ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk)) := by
  rw [coupledFilterHandler_eq, simFilterHandler_eq]
  refine ((identicalUntilBad_testHandler S pk sk cStar d₁ d₂ _ _ hd ?_).closeTo_bind
    prog st next).mono (testHandler_run_bad_le S d₁ pk sk cStar _ hk hs)
  intro m c r hdec
  exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hdec⟩⟩

private theorem eval_testHashH_of_lookup (S : Scheme PK SK M R CT K) (m : M) (c : CT)
    (t : R → Prop) [DecidablePred t] {st : SimState M R CT K} {r : R}
    (h : st.gCache.lookup m = some r) :
    ProbComp.eval (S.testHashH m c t st) = ProbComp.eval ((if t r then simHashHq S.sampleKey c
      else simHashHRaw S.sampleKey (false, m, c)) st) := by
  have hG : ProbComp.eval (simHashG S.pke.sampleCoins m st) = PMF.pure (r, st) := by
    rw [simHashG, RandomOracle.eval_zoomStateT_memoize, memoize_of_some _ _ _ _ h,
      PMF.monad_pure_eq_pure, PMF.pure_map]
  rw [eval_testHashH, hG, PMF.pure_bind]

private theorem eval_coupledHashH_init (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (m : M)
    (r : R) (hr : S.pke.dec sk (S.pke.encDet pk m r) = some m) :
    ProbComp.eval ((S.coupledHashH pk sk (false, m, S.pke.encDet pk m r)).run
        { gCache := [(m, r)] }) =
      ProbComp.eval ((simHashHq S.sampleKey (S.pke.encDet pk m r)).run
        ({ gCache := [(m, r)] } : SimState M R CT K)) := by
  change ProbComp.eval (S.testHashH m (S.pke.encDet pk m r) (fun r' =>
    S.pke.encDet pk m r' = S.pke.encDet pk m r ∧ S.pke.dec sk (S.pke.encDet pk m r) = some m)
      { gCache := [(m, r)] }) = _
  rw [eval_testHashH_of_lookup (r := r) _ _ _ _ (by simp),
    ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hr⟩)]
  rfl

private theorem eval_simHashH_init (S : Scheme PK SK M R CT K) (pk : PK) (m : M) (r : R) :
    ProbComp.eval ((S.simHashH pk (false, m, S.pke.encDet pk m r)).run
        { gCache := [(m, r)] }) =
      ProbComp.eval ((simHashHq S.sampleKey (S.pke.encDet pk m r)).run
        ({ gCache := [(m, r)] } : SimState M R CT K)) := by
  change ProbComp.eval (S.testHashH m (S.pke.encDet pk m r) (fun r' =>
    S.pke.encDet pk m r' = S.pke.encDet pk m r) { gCache := [(m, r)] }) = _
  rw [eval_testHashH_of_lookup (r := r) _ _ _ _ (by simp), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

/-- **Filtered correctness hop**: for an adversary making at most `qG` queries to `G` and `qH`
queries to `H` against a `δ`-correct PKE, when the decapsulation filters `d₁` and `d₂` agree on
every state satisfying `GoodCache`, `coupledFilterGame d₁` and `simFilterGame d₂` have
distinguishing advantage at most `(qG + qH + 1) δ`. -/
theorem advantage_coupledFilterGame_simFilterGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (d₁ : PK → SK → List (M × R) → CT → Bool)
    (d₂ : PK → List (M × R) → CT → Bool)
    (hd : ∀ pk sk (st : SimState M R CT K) c,
      GoodCache S.pke pk sk st → d₁ pk sk st.gCache c = d₂ pk st.gCache c)
    (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) (b : Bool) :
    (Game.advantage (ProbComp.eval (S.coupledFilterGame d₁ A b))
        (ProbComp.eval (S.simFilterGame d₂ A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ := by
  set E : ℝ≥0∞ := S.pke.keyGen.expect fun x =>
    ENNReal.ofReal (S.pke.keyPairMaxFailProb x.1 x.2) with hE
  have hclose : CloseTo (ProbComp.eval (S.coupledFilterGame d₁ A b))
      (ProbComp.eval (S.simFilterGame d₂ A b))
      (((qG + qH + 1 : ℕ) : ℝ≥0∞) * E) := by
    simp only [coupledFilterGame, simFilterGame, ProbComp.eval_bind, ProbComp.eval_pure,
      OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
    refine (CloseTo.bind_right_tsum _ (err := fun x : PK × SK =>
      ((qG + qH + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (S.pke.keyPairMaxFailProb x.1 x.2))
      fun keys _ => ?_).mono (le_of_eq ?_)
    swap
    · rw [hE, ProbComp.expect, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun x => ?_
      ring
    obtain ⟨pk, sk⟩ := keys
    set p := ENNReal.ofReal (S.pke.keyPairMaxFailProb pk sk) with hp
    have hconst {α : Type} (μ : PMF α) (c : ℝ≥0∞) : ∑' a, μ a * c = c := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    refine (CloseTo.bind_right_tsum _ (err := fun _ => ((qG + qH + 1 : ℕ) : ℝ≥0∞) * p)
      fun mStar _ => ?_).mono (le_of_eq (hconst _ _))
    refine (CloseTo.bind_right_tsum _ (err := fun r : R =>
      (if S.pke.dec sk (S.pke.encDet pk mStar r) = some mStar then 0 else 1) +
        ((qG + qH : ℕ) : ℝ≥0∞) * p) fun rStar _ => ?_).mono ?_
    swap
    · simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      have hfail : ∑' r, ProbComp.eval S.pke.sampleCoins r *
          (if S.pke.dec sk (S.pke.encDet pk mStar r) = some mStar then 0 else 1) =
          ENNReal.ofReal (S.pke.msgFailProb pk sk mStar) := by
        rw [ExplicitCoinPKE.msgFailProb,
          ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _),
          PMF.toOuterMeasure_apply]
        refine tsum_congr fun r => ?_
        by_cases h : S.pke.dec sk (S.pke.encDet pk mStar r) = some mStar <;>
          simp [h, Set.indicator]
      rw [hfail]
      calc ENNReal.ofReal (S.pke.msgFailProb pk sk mStar) + ((qG + qH : ℕ) : ℝ≥0∞) * p
          ≤ p + ((qG + qH : ℕ) : ℝ≥0∞) * p := by
            gcongr
            exact ENNReal.ofReal_le_ofReal (S.pke.msgFailProb_le_keyPairMaxFailProb pk sk mStar)
        _ = ((qG + qH + 1 : ℕ) : ℝ≥0∞) * p := by push_cast; ring
    by_cases hr : S.pke.dec sk (S.pke.encDet pk mStar rStar) = some mStar
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hr), zero_add,
        eval_coupledHashH_init S pk sk mStar rStar hr,
        eval_simHashH_init]
      refine (CloseTo.bind_right_tsum _ (err := fun _ => ((qG + qH : ℕ) : ℝ≥0∞) * p)
        fun x hx => ?_).mono (le_of_eq (hconst _ _))
      have hgood : GoodCache S.pke pk sk x.2 := by
        intro e he
        rw [simHashHq_gCache_eq _ _ _ _ hx, List.mem_singleton] at he
        subst he
        exact hr
      refine (CloseTo.bind_right_tsum _ (err := fun _ => ((qG + qH : ℕ) : ℝ≥0∞) * p)
        fun kRand _ => ?_).mono (le_of_eq (hconst _ _))
      exact closeTo_run_coupled_sim S pk sk _ (d₁ pk sk) (d₂ pk) (hd pk sk) _ (hq.ghCost _) hgood _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)]
      exact fun e => (Probability.PMF.toOuterMeasure_le_one _ e).trans
        (le_self_add.trans le_add_self)
  have hadv := Game.closeTo_iff_coe_advantage_le.mp hclose
  have hEtop : E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hE, ProbComp.expect]
    calc ∑' x, ProbComp.eval S.pke.keyGen x * ENNReal.ofReal (S.pke.keyPairMaxFailProb x.1 x.2)
        ≤ ∑' x, ProbComp.eval S.pke.keyGen x * 1 := by
          gcongr with x
          exact ENNReal.ofReal_le_one.mpr (S.pke.keyPairMaxFailProb_le_one x.1 x.2)
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc (Game.advantage (ProbComp.eval (S.coupledFilterGame d₁ A b))
        (ProbComp.eval (S.simFilterGame d₂ A b)) : ℝ)
      = ((Game.advantage (ProbComp.eval (S.coupledFilterGame d₁ A b))
          (ProbComp.eval (S.simFilterGame d₂ A b)) : ℝ≥0∞)).toReal := by rw [ENNReal.coe_toReal]
    _ ≤ (((qG + qH + 1 : ℕ) : ℝ≥0∞) * E).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hEtop) hadv
    _ = ((qG + qH + 1 : ℕ) : ℝ) * E.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ ≤ ((qG + qH + 1 : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)

/-- **Correctness hop** ([HofheinzHoevelmannsKiltz2017], proof of the §3.1 theorem for `T`): for
an adversary making at most `qG` queries to `G` and `qH` queries to `H` against a `δ`-correct PKE,
the lazy coupled game `coupledGame`, whose key-derivation oracle checks `Dec(sk, c) = some m`, and
the keyless simulator game `simGame` have distinguishing advantage at most `(qG + qH + 1) δ`. -/
theorem advantage_coupledGame_simGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) (b : Bool) :
    (Game.advantage (ProbComp.eval (S.coupledGame A b)) (ProbComp.eval (S.simGame A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ :=
  S.advantage_coupledFilterGame_simFilterGame_le (fun _ _ _ _ => true) (fun _ _ _ => true)
    (fun _ _ _ _ _ => rfl) A hq hδ b

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
