/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.SigmaProtocol.FiatShamirNIZK
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Fiat–Shamir NIZK proofs in the random-oracle model

Concrete verification over `ZMod 5` of
`CslibFrontier.Crypto.Protocols.SigmaProtocol.FiatShamirNIZK`:

1. **Completeness**: honest Schnorr Fiat–Shamir NIZK proving and verification over `ZMod 5` with
   base `2` accept with probability `1` from both empty and pre-populated caches, and evaluate to
   `(true, cache)` on concrete coins.
2. **Invalid-witness rejection**: invalid candidate pairs `(α, u)` return `none` identically in
   `nizkRealHandler`, `nizkSimHandler`, `fiatShamirNIZKRealGame`, and `fiatShamirNIZKSimGame`
   without modifying the random-oracle cache (`Game.advantage = 0`).
3. **Adaptive multi-theorem zero knowledge**: concrete `NIZKCallBounded` distinguishers querying
   multiple statements and the shared random oracle instantiate
   `schnorr_advantage_fiatShamirNIZKRealGame_simGame_le` to `2 / 5` (`Qp = 1, Qro = 1`) and
   `6 / 5` (`Qp = 2, Qro = 1`).
4. **Witness extraction and simulation-extractability**:
   * A 1-hash knowing prover for statement `u = 3` wins `fiatShamirNIZKPokGame` with probability
     `1`, forcing `fiatShamirNIZKExtract` to output the unique valid witness `some 4` with
     probability at least `9 / 50`.
   * An adaptive 1-prove, 1-hash `NIZKSimProver` that queries an honest proof on `u₁ = 2` and
     proves the fresh statement `u₂ = 3` wins `fiatShamirNIZKRealExtGame` with probability `1`,
     forcing both `fiatShamirNIZKSimExtract` and `fiatShamirNIZKSimExtractWith` (with
     `linearSimCoinSource`) to recover `(3, 4)` with probability at least `1 / 50`.
5. **Counterexample to statement-free `H(t)` Fiat–Shamir hashing**: on
   `schnorr ι5 ((1, 0) : ZMod 5 × ZMod 5)`, statements `(a, b)` with `b ≠ 0` have *no* witness, yet
   when the hash oracle is queried on `t` alone (`H(t)`), a 1-query attacker chooses a false
   statement adaptively after seeing `c = H(0, 1)` and convinces verification with probability
   `4 / 5`, strictly exceeding the statement-bound `H(y, t)` soundness cap `(1 + 1) / 5 = 2 / 5`.
-/

namespace CslibFrontierTests.Crypto.FiatShamirNIZK

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol
open OracleComp ROMSignature
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Identity challenge embedding on `ZMod 5`. -/
abbrev ι5 : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- Schnorr Sigma protocol in `ZMod 5` with generator `2`. -/
noncomputable abbrev schnorr5 : SigmaProtocol (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) :=
  schnorr ι5 (2 : ZMod 5)

/-- Boolean relation checker `α • 2 == u` in `ZMod 5`. -/
abbrev valid5 (α u : ZMod 5) : Bool :=
  decide (α • (2 : ZMod 5) = u)

/-- Standard Schnorr HVZK simulator in `ZMod 5` with generator `2`. -/
noncomputable abbrev sim5 : ZMod 5 → ZMod 5 → PMF (ZMod 5 × ZMod 5) :=
  linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 5) (ZMod 5) 2) id ι5

/-! ### 1. Completeness over `ZMod 5` -/

/-- Honest proving and verification for `(α, u) = (4, 3)` (`4 • 2 = 3` in `ZMod 5`) succeed with
probability `1` from the empty cache. -/
example :
    (do
      let coins ← schnorr5.commit (4 : ZMod 5) 3
      let (prf, cache') ←
        (interpret (oracle (ZMod 5)) (fiatShamirNIZKProve schnorr5 4 3 coins)).run []
      let (acc, _) ← (interpret (oracle (ZMod 5)) (fiatShamirNIZKVerify schnorr5 3 prf)).run cache'
      return acc) = PMF.pure true :=
  schnorr_fiatShamirNIZK_complete (by decide : (4 : ZMod 5) • (2 : ZMod 5) = 3) []

/-- Completeness also holds starting from a non-empty lazy random-oracle cache. -/
example :
    (do
      let coins ← schnorr5.commit (4 : ZMod 5) 3
      let (prf, cache') ←
        (interpret (oracle (ZMod 5)) (fiatShamirNIZKProve schnorr5 4 3 coins)).run [((1, 4), 2)]
      let (acc, _) ← (interpret (oracle (ZMod 5)) (fiatShamirNIZKVerify schnorr5 3 prf)).run cache'
      return acc) = PMF.pure true :=
  schnorr_fiatShamirNIZK_complete (by decide : (4 : ZMod 5) • (2 : ZMod 5) = 3) [((1, 4), 2)]

/-- Concrete transcript execution: with commitment randomness `r = 1` (`t = 1 • 2 = 2`) and cached
challenge `H(3, 2) = 4`, `fiatShamirNIZKProve` outputs `(2, 1 + 4 • 4) = (2, 2)` and
`fiatShamirNIZKVerify` deterministically accepts (`2 • 2 = 4 = 2 + 4 • 3` in `ZMod 5`). -/
example :
    (do
      let (prf, cache') ←
        (interpret (oracle (ZMod 5))
          (fiatShamirNIZKProve schnorr5 (4 : ZMod 5) 3 ((2 : ZMod 5), (1 : ZMod 5)))).run
          [((3, 2), 4)]
      (interpret (oracle (ZMod 5)) (fiatShamirNIZKVerify schnorr5 3 prf)).run cache') =
    PMF.pure (true, [((3, 2), 4)]) := by
  simp only [fiatShamirNIZKProve, fiatShamirNIZKVerify, interpret_map, interpret_query,
    StateT.run_map, PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  have hlookup : ([((3, 2), 4)] : List ((ZMod 5 × ZMod 5) × ZMod 5)).lookup (3, 2) = some 4 := by
    decide
  rw [show (oracle (ZMod 5) ((3 : ZMod 5), (2 : ZMod 5))).run [((3, 2), 4)] =
    memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (3, 2) [((3, 2), 4)] from rfl,
    memoize_of_some _ _ _ _ hlookup]
  simp only [PMF.monad_pure_eq_pure, PMF.pure_bind]
  rw [show (oracle (ZMod 5) ((3 : ZMod 5), (2 : ZMod 5))).run [((3, 2), 4)] =
    memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (3, 2) [((3, 2), 4)] from rfl,
    memoize_of_some _ _ _ _ hlookup]
  simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
  refine congrArg PMF.pure ?_
  decide

/-! ### 2. Invalid witness pairs return `none` identically -/

/-- `(1, 4)` is not a valid Schnorr witness-statement pair in `ZMod 5` (`1 • 2 ≠ 4`), so both
handlers return `PMF.pure (none, cache)` identically without touching `cache`. -/
example (cache : List ((ZMod 5 × ZMod 5) × ZMod 5)) :
    nizkRealHandler schnorr5 valid5 (.inl (1, 4)) cache = PMF.pure (none, cache) ∧
      nizkSimHandler sim5 valid5 (.inl (1, 4)) cache = PMF.pure (none, cache) :=
  ⟨nizkRealHandler_inl_of_false schnorr5 (by decide : valid5 1 4 = false) cache,
    nizkSimHandler_inl_of_false sim5 (by decide : valid5 1 4 = false) cache⟩

/-- Distinguisher querying an invalid witness pair `(1, 4)` and checking that `none` was returned
while a pre-existing hash query `(1, 2)` remains consistent. -/
def invalidQueryDist :
    OracleComp (NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) Bool := do
  let c₁ ← OracleComp.query
    (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inr (1, 2))
  let bad ← OracleComp.query
    (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inl (1, 4))
  let c₂ ← OracleComp.query
    (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inr (1, 2))
  return (bad.isNone && decide (c₁ = c₂))

/-- In both the real and simulated multi-theorem experiments, `invalidQueryDist` receives `none` on
the invalid `.inl (1, 4)` query without perturbing the random-oracle cache, so both games are
identically `PMF.pure true` and have advantage `0`. -/
example :
    fiatShamirNIZKRealGame schnorr5 valid5 invalidQueryDist = PMF.pure true ∧
      fiatShamirNIZKSimGame sim5 valid5 invalidQueryDist = PMF.pure true ∧
      Game.advantage
        (fiatShamirNIZKRealGame schnorr5 valid5 invalidQueryDist)
        (fiatShamirNIZKSimGame sim5 valid5 invalidQueryDist) = 0 := by
  have hreal : fiatShamirNIZKRealGame schnorr5 valid5 invalidQueryDist = PMF.pure true := by
    simp only [fiatShamirNIZKRealGame, invalidQueryDist, interpret_bind, interpret_query,
      interpret_pure, StateT.run_bind, StateT.run_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind]
    refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
      fun (c₁, cache₁) hc₁ => ?_).trans (PMF.bind_const _ _)
    change (c₁, cache₁) ∈
      (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (1, 2) []).support at hc₁
    have hlookup : cache₁.lookup (1, 2) = some c₁ := by
      rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc₁ with ⟨hl, _⟩ | ⟨_, _, hnext⟩
      · simp at hl
      · change cache₁ = [((1, 2), c₁)] at hnext
        rw [hnext, List.lookup_cons_self]
    have hfalse : valid5 1 4 = false := by decide
    change ((nizkRealHandler schnorr5 valid5 (.inl (1, 4)) cache₁).bind _) = PMF.pure true
    rw [nizkRealHandler_inl_of_false schnorr5 hfalse cache₁, PMF.pure_bind]
    change ((oracle (ZMod 5) (1, 2) cache₁).bind _) = PMF.pure true
    rw [oracle, memoize_of_some _ _ _ _ hlookup]
    simp
  have hsim : fiatShamirNIZKSimGame sim5 valid5 invalidQueryDist = PMF.pure true := by
    simp only [fiatShamirNIZKSimGame, invalidQueryDist, interpret_bind, interpret_query,
      interpret_pure, StateT.run_bind, StateT.run_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind]
    refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
      fun (c₁, cache₁) hc₁ => ?_).trans (PMF.bind_const _ _)
    change (c₁, cache₁) ∈
      (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (1, 2) []).support at hc₁
    have hlookup : cache₁.lookup (1, 2) = some c₁ := by
      rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc₁ with ⟨hl, _⟩ | ⟨_, _, hnext⟩
      · simp at hl
      · change cache₁ = [((1, 2), c₁)] at hnext
        rw [hnext, List.lookup_cons_self]
    have hfalse : valid5 1 4 = false := by decide
    change ((nizkSimHandler sim5 valid5 (.inl (1, 4)) cache₁).bind _) = PMF.pure true
    rw [nizkSimHandler_inl_of_false sim5 hfalse cache₁, PMF.pure_bind]
    change ((oracle (ZMod 5) (1, 2) cache₁).bind _) = PMF.pure true
    rw [oracle, memoize_of_some _ _ _ _ hlookup]
    simp
  refine ⟨hreal, hsim, ?_⟩
  rw [hreal, hsim, Game.advantage_self]

/-! ### 3. Concrete adaptive multi-theorem zero-knowledge bounds on `schnorr` -/

/-- Adaptive distinguisher making `Qp = 1` prove query on `(4, 3)` and `Qro = 1` direct hash query
to verify the returned proof. -/
noncomputable def singleVerifyDist :
    OracleComp (NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) Bool := do
  let opt ← OracleComp.query
    (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inl (4, 3))
  match opt with
  | none => return false
  | some (t, z) =>
    let c ← OracleComp.query
      (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inr (3, t))
    return schnorr5.verify 3 t c z

theorem singleVerifyDist_callBounded : NIZKCallBounded singleVerifyDist 1 1 := by
  refine ⟨?_, ?_⟩
  · refine .liftBind (Sum.inl ((4 : ZMod 5), (3 : ZMod 5))) _ 0 fun opt => ?_
    rcases opt with _ | ⟨t, z⟩
    · exact .pure _ 0
    · exact .liftBind (Sum.inr ((3 : ZMod 5), t)) _ 0 fun _ => .pure _ 0
  · refine .liftBind (Sum.inl ((4 : ZMod 5), (3 : ZMod 5))) _ 1 fun opt => ?_
    rcases opt with _ | ⟨t, z⟩
    · exact .pure _ 1
    · exact .liftBind (Sum.inr ((3 : ZMod 5), t)) _ 0 fun _ => .pure _ 0

/-- Non-trivial (`< 1`) concrete zero-knowledge advantage bound `2 / 5` on `singleVerifyDist`
(`Qp = 1, Qro = 1, q = 5`). -/
example :
    (Game.advantage
      (fiatShamirNIZKRealGame schnorr5 valid5 singleVerifyDist)
      (fiatShamirNIZKSimGame sim5 valid5 singleVerifyDist) : ℝ) ≤ 2 / 5 := by
  have h := schnorr_advantage_fiatShamirNIZKRealGame_simGame_le (ι := ι5) (g := (2 : ZMod 5))
    (by decide) singleVerifyDist_callBounded
  norm_num at h
  exact h

/-- Adaptive two-statement distinguisher: queries a proof for `u₁ = 3`, inspects its response to
adaptively choose between `(1, 2)` and `(2, 4)` for a second prove query, and verifies the first
proof against the shared random oracle (`Qp = 2, Qro = 1`). -/
noncomputable def adaptiveTwoStmtDist :
    OracleComp (NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) Bool := do
  let opt₁ ← OracleComp.query
    (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inl (4, 3))
  match opt₁ with
  | none => return false
  | some (t₁, z₁) =>
    let nextPair : ZMod 5 × ZMod 5 := if z₁ = 0 then (1, 2) else (2, 4)
    let opt₂ ← OracleComp.query
      (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inl nextPair)
    let c₁ ← OracleComp.query
      (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inr (3, t₁))
    return (opt₂.isSome && schnorr5.verify 3 t₁ c₁ z₁)

theorem adaptiveTwoStmtDist_callBounded : NIZKCallBounded adaptiveTwoStmtDist 2 1 := by
  refine ⟨?_, ?_⟩
  · refine .liftBind (Sum.inl ((4 : ZMod 5), (3 : ZMod 5))) _ 1 fun opt₁ => ?_
    rcases opt₁ with _ | ⟨t₁, z₁⟩
    · exact .pure _ 1
    · refine .liftBind (Sum.inl (if z₁ = 0 then (1, 2) else (2, 4))) _ 0 fun _ => ?_
      exact .liftBind (Sum.inr ((3 : ZMod 5), t₁)) _ 0 fun _ => .pure _ 0
  · refine .liftBind (Sum.inl ((4 : ZMod 5), (3 : ZMod 5))) _ 1 fun opt₁ => ?_
    rcases opt₁ with _ | ⟨t₁, z₁⟩
    · exact .pure _ 1
    · refine .liftBind (Sum.inl (if z₁ = 0 then (1, 2) else (2, 4))) _ 1 fun _ => ?_
      exact .liftBind (Sum.inr ((3 : ZMod 5), t₁)) _ 0 fun _ => .pure _ 0

/-- Concrete multi-statement zero-knowledge bound instantiation (`Qp = 2, Qro = 1, q = 5`). -/
example :
    (Game.advantage
      (fiatShamirNIZKRealGame schnorr5 valid5 adaptiveTwoStmtDist)
      (fiatShamirNIZKSimGame sim5 valid5 adaptiveTwoStmtDist) : ℝ) ≤ 6 / 5 := by
  have h := schnorr_advantage_fiatShamirNIZKRealGame_simGame_le (ι := ι5) (g := (2 : ZMod 5))
    (by decide) adaptiveTwoStmtDist_callBounded
  norm_num at h
  exact h

/-! ### 4. Concrete witness extraction (`fiatShamirNIZKExtract` and `fiatShamirNIZKSimExtract`) -/

/-- Cheating prover in `ZMod 5` that computes the discrete log `3 • u` of `u` base `2`
(`(3 • u) • 2 = 6 • u = u` mod `5`) and outputs an honest 1-hash Fiat–Shamir proof. -/
noncomputable def knowingProver : NIZKProver (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) where
  Coins := ZMod 5
  coins := PMF.uniformOfFintype (ZMod 5)
  prove u r := do
    let c ← OracleComp.query (spec := NIZKHashSpec (ZMod 5) (ZMod 5) (ZMod 5)) (u, r • 2)
    return (r • 2, r + c • (3 • u))

theorem knowingProver_queryBounded (u r : ZMod 5) : IsQueryBounded (knowingProver.prove u r) 1 :=
  .liftBind _ _ 0 fun _ => .pure _ 0

/-- `knowingProver` convinces `fiatShamirNIZKPokGame` with probability `1` on every `u : ZMod 5`. -/
theorem succProbability_knowingProver (u : ZMod 5) :
    Game.succProbability (fiatShamirNIZKPokGame schnorr5 knowingProver u) = 1 := by
  rw [Game.succProbability, ENNReal.toNNReal_eq_one_iff]
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  simp only [fiatShamirNIZKPokGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine Probability.PMF.le_bind_apply_on_support _ fun (r : ZMod 5) _ => ?_
  refine Probability.PMF.le_bind_apply_on_support _ fun proved hproved => ?_
  simp only [knowingProver, interpret_bind, interpret_query, interpret_pure, StateT.run_bind,
    StateT.run_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hproved
  obtain ⟨ans, hans, rfl⟩ := hproved
  change ans ∈ (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (u, r • (2 : ZMod 5)) []).support
    at hans
  rw [memoize_of_none _ _ _ rfl] at hans
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hans
  obtain ⟨c, -, rfl⟩ := hans
  refine Probability.PMF.le_bind_apply_on_support _ fun verified hverified => ?_
  simp only [fiatShamirNIZKVerify, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hverified
  obtain ⟨v, hv, rfl⟩ := hverified
  change v ∈ (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (u, r • (2 : ZMod 5))
    [((u, r • 2), c)]).support at hv
  rw [memoize_of_some _ _ _ _ List.lookup_cons_self, PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at hv
  subst hv
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hacc : schnorr5.Accepts u (r • 2) c (r + c • (3 • u)) := by
    rw [schnorr_accepts_iff]
    simp only [smul_eq_mul, Function.Embedding.refl_apply]
    linear_combination (c * u) * h5
  have hver : schnorr5.verify u (r • 2) c (r + c • (3 • u)) = true := hacc
  simp only [hver]
  simp

/-- Plain ROM witness extraction on `u = 3`: `1 ≤ 2 / 5 + √(2 · ε')` forces `fiatShamirNIZKExtract`
to output a valid witness with probability at least `9 / 50`, and because `4` is the unique witness
satisfying `α • 2 = 3` in `ZMod 5`, `some 4` is in the extractor's support. -/
theorem extract_knowingProver_at_3 :
    (9 / 50 : ℝ) ≤ Game.succProbability
      (fiatShamirNIZKExtractGame (fun α u => α • (2 : ZMod 5) = u)
        (fiatShamirNIZKExtract schnorr5 (linearExtract ι5) knowingProver 1 3) 3) ∧
      some (4 : ZMod 5) ∈
        (fiatShamirNIZKExtract schnorr5 (linearExtract ι5) knowingProver 1 3).support := by
  have h := schnorr_succProbability_fiatShamirNIZKPokGame_le (ι := ι5) (g := (2 : ZMod 5))
    knowingProver (3 : ZMod 5) (knowingProver_queryBounded 3)
  rw [succProbability_knowingProver 3, ZMod.card] at h
  set ext := fiatShamirNIZKExtract schnorr5 (linearExtract ι5) knowingProver 1 3
  set ε := (Game.succProbability
    (fiatShamirNIZKExtractGame (fun α u => α • (2 : ZMod 5) = u) ext 3) : ℝ)
  have hε0 : 0 ≤ ε := NNReal.coe_nonneg _
  simp only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num, NNReal.coe_one, Nat.cast_ofNat] at h
  have hsqrt : (3 / 5 : ℝ) ≤ √(2 * ε) := by linarith
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε)
  have hbound : (9 / 50 : ℝ) ≤ ε := by
    nlinarith [mul_le_mul hsqrt hsqrt (by norm_num) (Real.sqrt_nonneg _)]
  refine ⟨hbound, ?_⟩
  have hpos : (fiatShamirNIZKExtractGame (fun α u => α • (2 : ZMod 5) = u) ext 3) true ≠ 0 := by
    intro hzero
    have hεzero : ε = 0 := by
      simp only [ε, ENNReal.coe_toNNReal_eq_toReal]
      rw [hzero]
      simp
    linarith
  obtain ⟨opt, hopt, htrue⟩ := (PMF.mem_support_bind_iff _ _ _).mp
    ((PMF.mem_support_iff _ _).mpr hpos)
  rcases opt with _ | α
  · simp at htrue
  · simp only [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at htrue
    have hα : α • (2 : ZMod 5) = 3 := of_decide_eq_true htrue.symm
    have h5 : (5 : ZMod 5) = 0 := by decide
    have hα4 : α = 4 := by
      rw [smul_eq_mul] at hα
      linear_combination 3 * hα - (α - 1) * h5
    rwa [hα4] at hopt

/-- Adaptive `NIZKSimProver` (`Qp = 1, Qro = 1`): queries `.inl (1, 2)` for an honest proof on
statement `2`, then outputs an honest proof on the fresh statement `3` (`4 • 2 = 3`). -/
noncomputable def knowingSimProver :
    NIZKSimProver (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) where
  Coins := ZMod 5
  coins := PMF.uniformOfFintype (ZMod 5)
  prove r := do
    let _ ← OracleComp.query
      (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inl (1, 2))
    let c ← OracleComp.query
      (spec := NIZKDistinguisherSpec (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5) (ZMod 5)) (.inr (3, r • 2))
    return (3, (r • 2, r + c • 4))

theorem knowingSimProver_callBounded : knowingSimProver.CallBounded 1 1 := fun _ =>
  ⟨.liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0,
    .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0⟩

/-- `knowingSimProver` wins `fiatShamirNIZKRealExtGame` with probability `1`: its `.inl (1, 2)` call
only records a pair `(2, t₁)` in `proved` and `(2, t₁)` in `cache`, so `(3, r • 2)` is both fresh in
`cache` and absent from `proved`. -/
theorem succProbability_knowingSimProver :
    Game.succProbability (fiatShamirNIZKRealExtGame schnorr5 valid5 knowingSimProver) = 1 := by
  rw [Game.succProbability, ENNReal.toNNReal_eq_one_iff]
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  simp only [fiatShamirNIZKRealExtGame, fiatShamirNIZKRealExtGameOn, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  refine Probability.PMF.le_bind_apply_on_support _ fun (r : ZMod 5) _ => ?_
  refine Probability.PMF.le_bind_apply_on_support _ fun out hrun => ?_
  simp only [knowingSimProver, interpret_bind, interpret_query, interpret_pure, StateT.run_bind,
    StateT.run_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hrun
  obtain ⟨step₁, hstep₁, ans₂, hstep₂, rfl⟩ := hrun
  have hv12 : valid5 1 2 = true := by decide
  simp only [nizkRealExtHandler, StateT.run, hv12, ↓reduceIte, fiatShamirNIZKProve, interpret_map,
    interpret_query, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep₁
  obtain ⟨coins₁, -, proved₁, hc₁, rfl⟩ := hstep₁
  change proved₁ ∈
    (((fun c => (coins₁.1, schnorr5.respond 1 2 coins₁.2 c)) <$>
      oracle (ZMod 5) (2, coins₁.1)).run []).support at hc₁
  simp only [StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hc₁
  obtain ⟨r₁, hc₁', rfl⟩ := hc₁
  change r₁ ∈
    (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (2, coins₁.1) []).support at hc₁'
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc₁' with ⟨hl, _⟩ | ⟨_, _, hcache₁''⟩
  · simp at hl
  simp only [nizkRealExtHandler, StateT.run, PMF.mem_support_map_iff] at hstep₂
  obtain ⟨r₂, hc₂, rfl⟩ := hstep₂
  have h32 : (3 : ZMod 5) ≠ 2 := by decide
  have hnone : ([((2, coins₁.1), r₁.1)] : List ((ZMod 5 × ZMod 5) × ZMod 5)).lookup
      (3, r • 2) = none := by
    rw [List.lookup_cons, beq_false_of_ne (fun h => h32 (Prod.mk.inj h).1)]
    rfl
  rw [hcache₁'', oracle, memoize_of_none _ _ _ hnone] at hc₂
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hc₂
  obtain ⟨c, -, rfl⟩ := hc₂
  refine Probability.PMF.le_bind_apply_on_support _ fun verified hver => ?_
  simp only [fiatShamirNIZKVerify, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hver
  obtain ⟨v, hv, rfl⟩ := hver
  change v ∈
    (memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) (3, r • (2 : ZMod 5))
      (((3, r • 2), c) :: [((2, coins₁.1), r₁.1)])).support at hv
  rw [memoize_of_some _ _ _ _ List.lookup_cons_self, PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at hv
  subst hv
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hacc : schnorr5.Accepts 3 (r • 2) c (r + c • 4) := by
    rw [schnorr_accepts_iff]
    simp only [smul_eq_mul, Function.Embedding.refl_apply]
    linear_combination c * h5
  have hverTrue : schnorr5.verify 3 (r • 2) c (r + c • 4) = true := hacc
  have hnotProved : ([(2, coins₁.1)] : List (ZMod 5 × ZMod 5)).contains (3, r • 2) = false := by
    simp [h32]
  simp only [hverTrue, hnotProved]
  simp

/-- Adaptive simulation-extractability on `knowingSimProver` (`Qp = 1, Qro = 1, q = 5`): the bound
`1 ≤ 1 · 2 / 5 + 2 / 5 + √(2 · ε')` forces both `fiatShamirNIZKSimExtract` (using `PMF.pi`) and
`fiatShamirNIZKSimExtractWith` (using `linearSimCoinSource`) to output a valid witness with
probability at least `1 / 50`. -/
example :
    (1 / 50 : ℝ) ≤ Game.succProbability
      (fiatShamirNIZKSimExtractGame (fun α u => α • (2 : ZMod 5) = u) (fun _ => true)
        (fiatShamirNIZKSimExtract schnorr5 sim5 (linearExtract ι5) valid5 knowingSimProver 1 1)) ∧
      (1 / 50 : ℝ) ≤ Game.succProbability
        (fiatShamirNIZKSimExtractGame (fun α u => α • (2 : ZMod 5) = u) (fun _ => true)
          (fiatShamirNIZKSimExtractWith schnorr5
            (linearSimCoinSource (fun _ => LinearMap.toSpanSingleton (ZMod 5) (ZMod 5) 2) id ι5)
            (linearExtract ι5) valid5 (fun _ => true) knowingSimProver 1 1)) := by
  have h₁ := succProbability_fiatShamirNIZKRealExtGame_le
    (fun α u hv => of_decide_eq_true hv)
    schnorr_specialSoundness
    schnorr_specialHVZK
    (schnorr_unpredictableCommitments (ι := ι5) (g := (2 : ZMod 5)) (by decide))
    knowingSimProver_callBounded
  have h₂ := schnorr_succProbability_fiatShamirNIZKRealExtGame_le (ι := ι5) (g := (2 : ZMod 5))
    (by decide) (fun _ => true) knowingSimProver_callBounded
  have hwin : Game.succProbability (fiatShamirNIZKRealExtGame schnorr5 valid5 knowingSimProver) =
      1 := succProbability_knowingSimProver
  have hwin' :
      Game.succProbability
        (fiatShamirNIZKRealExtGameOn (fun _ => true) schnorr5 valid5 knowingSimProver) = 1 := hwin
  rw [hwin, ZMod.card] at h₁
  rw [hwin', ZMod.card] at h₂
  set ε₁ := (Game.succProbability
    (fiatShamirNIZKSimExtractGame (fun α u => α • (2 : ZMod 5) = u) (fun _ => true)
      (fiatShamirNIZKSimExtract schnorr5 sim5 (linearExtract ι5) valid5 knowingSimProver 1 1)) : ℝ)
  set ε₂ := (Game.succProbability
    (fiatShamirNIZKSimExtractGame (fun α u => α • (2 : ZMod 5) = u) (fun _ => true)
      (fiatShamirNIZKSimExtractWith schnorr5
        (linearSimCoinSource (fun _ => LinearMap.toSpanSingleton (ZMod 5) (ZMod 5) 2) id ι5)
        (linearExtract ι5) valid5 (fun _ => true) knowingSimProver 1 1)) : ℝ)
  have hε₁ : 0 ≤ ε₁ := NNReal.coe_nonneg _
  have hε₂ : 0 ≤ ε₂ := NNReal.coe_nonneg _
  simp only [Nat.cast_one, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one, Nat.cast_ofNat,
    show (1 : ℝ) + 1 = 2 by norm_num] at h₁
  simp only [Nat.cast_one, NNReal.coe_one, Nat.cast_ofNat,
    show (1 : ℝ) + 1 = 2 by norm_num] at h₂
  have hsqrt₁ : (1 / 5 : ℝ) ≤ √(2 * ε₁) := by linarith
  have hsqrt₂ : (1 / 5 : ℝ) ≤ √(2 * ε₂) := by linarith
  have hsq₁ := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε₁)
  have hsq₂ := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε₂)
  exact ⟨by nlinarith [mul_le_mul hsqrt₁ hsqrt₁ (by norm_num) (Real.sqrt_nonneg _)],
    by nlinarith [mul_le_mul hsqrt₂ hsqrt₂ (by norm_num) (Real.sqrt_nonneg _)]⟩

/-! ### 5. Counterexample: hashing `H(t)` without the statement `y` fails soundness -/

/-- Two-dimensional `ZMod 5`-module `ZMod 5 × ZMod 5` with generator `g₂ = (1, 0)`: every element
`(a, b)` with `b ≠ 0` lies outside the span of `g₂` and is therefore a *false* statement. -/
noncomputable abbrev schnorr2D :
    SigmaProtocol (ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5) (ZMod 5) :=
  schnorr ι5 ((1, 0) : ZMod 5 × ZMod 5)

/-- Every statement `y : ZMod 5 × ZMod 5` with `y.2 ≠ 0` has *no* Schnorr witness with respect to
`(1, 0)`. -/
theorem schnorr2D_false_of_snd_ne_zero {y : ZMod 5 × ZMod 5} (hy : y.2 ≠ 0) :
    ∀ α : ZMod 5, α • ((1, 0) : ZMod 5 × ZMod 5) ≠ y := by
  intro α hα
  apply hy
  rw [← hα]
  simp

/-- Buggy Fiat–Shamir verifier that queries the random oracle on the commitment `prf.1` *alone*,
omitting the statement `y` ([BonehShoup2023], Section 20.3.3). -/
def unstatedVerify {X Y T C Z : Type} (P : SigmaProtocol X Y T C Z) (y : Y) (prf : T × Z) :
    OracleComp (fun _ : T => C) Bool :=
  (fun c => P.verify y prf.1 c prf.2) <$> OracleComp.query (spec := fun _ : T => C) prf.1

/-- Adaptive 1-query attacker against `unstatedVerify schnorr2D`: it commits to `t = (0, 1)` and
response `z = 0` *before* querying `H`, queries `c ← H(0, 1)`, and then adaptively selects the
false statement `y = (0, -c⁻¹)` (or `(0, 1)` if `c = 0`). Whenever `c ≠ 0` (probability `4 / 5`),
`0 • (1, 0) = (0, 0) = (0, 1) + c • (0, -c⁻¹)` passes verification! -/
def unstatedFalseStmtAttacker :
    OracleComp (fun _ : ZMod 5 × ZMod 5 => ZMod 5)
      ((ZMod 5 × ZMod 5) × ((ZMod 5 × ZMod 5) × ZMod 5)) := do
  let c ← OracleComp.query (spec := fun _ : ZMod 5 × ZMod 5 => ZMod 5) (0, 1)
  let y : ZMod 5 × ZMod 5 := if c = 0 then (0, 1) else (0, -c⁻¹)
  return (y, ((0, 1), 0))

/-- Game running `unstatedFalseStmtAttacker` against a lazy uniform random oracle `H : T → C` and
checking both that `y` is a false statement (`y.2 ≠ 0`) and that `unstatedVerify` accepts. -/
noncomputable def unstatedFalseStmtGame : Game := do
  let ((y, prf), cache) ←
    (interpret (oracle (ZMod 5)) unstatedFalseStmtAttacker).run []
  let (acc, _) ← (interpret (oracle (ZMod 5)) (unstatedVerify schnorr2D y prf)).run cache
  return (decide (y.2 ≠ 0) && acc)

/-- **Soundness failure of `H(t)`**: with `Qro = 1` hash query and zero witness knowledge,
`unstatedFalseStmtAttacker` produces an accepted proof of a *false* statement (`∀ α, α • g₂ ≠ y`)
with probability `4 / 5`. -/
theorem succProbability_unstatedFalseStmtGame :
    (Game.succProbability unstatedFalseStmtGame : ℝ) = 4 / 5 := by
  have hgame :
      unstatedFalseStmtGame =
        (PMF.uniformOfFintype (ZMod 5)).map (fun c : ZMod 5 => decide (c ≠ 0)) := by
    simp only [unstatedFalseStmtGame, unstatedFalseStmtAttacker, unstatedVerify, interpret_bind,
      interpret_map, interpret_query, interpret_pure, StateT.run_bind, StateT.run_map,
      StateT.run_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
    rw [show (oracle (ZMod 5) ((0 : ZMod 5), (1 : ZMod 5))).run [] =
      memoize (fun _ => PMF.uniformOfFintype (ZMod 5)) ((0 : ZMod 5), (1 : ZMod 5)) [] from rfl,
      memoize_of_none _ _ _ rfl]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
    rw [← PMF.bind_pure_comp]
    refine congrArg (PMF.bind _) (funext fun c => ?_)
    have hlookup :
        ([(((0 : ZMod 5), (1 : ZMod 5)), c)]).lookup ((0 : ZMod 5), (1 : ZMod 5)) = some c :=
      List.lookup_cons_self
    rw [show (oracle (ZMod 5) ((0 : ZMod 5), (1 : ZMod 5))).run
        [(((0 : ZMod 5), (1 : ZMod 5)), c)] =
      oracle (ZMod 5) ((0 : ZMod 5), (1 : ZMod 5)) [(((0 : ZMod 5), (1 : ZMod 5)), c)] from rfl,
      oracle, memoize_of_some _ _ _ _ hlookup]
    simp only [PMF.monad_pure_eq_pure, PMF.pure_bind, Function.comp_apply]
    refine congrArg PMF.pure ?_
    by_cases hc : c = 0
    · subst hc
      simp [schnorr2D, schnorr, linear]
    · have hinv : -c⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
      have hacc : schnorr2D.Accepts (0, -c⁻¹) (0, 1) c 0 := by
        rw [schnorr2D, schnorr_accepts_iff]
        ext <;> simp [hc]
      have hver : schnorr2D.verify (0, -c⁻¹) (0, 1) c 0 = true := hacc
      simp [hc, hinv, hver]
  have htrue : unstatedFalseStmtGame true = (4 : ℝ≥0∞) / 5 := by
    classical
    rw [hgame, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Probability.PMF.toOuterMeasure_uniformOfFintype, ZMod.card]
    have hfilt :
        Finset.univ.filter
          (fun c : ZMod 5 => c ∈ (fun c : ZMod 5 => decide (c ≠ 0)) ⁻¹' {true}) =
        Finset.univ.filter (fun c : ZMod 5 => c ≠ 0) := by
      ext c
      simp
    have hcard : (Finset.univ.filter (fun c : ZMod 5 => c ≠ 0)).card = 4 := by decide
    rw [hfilt, hcard, div_eq_mul_inv]
    norm_num
  simp only [Game.succProbability, htrue, ENNReal.coe_toNNReal_eq_toReal]
  rw [ENNReal.toReal_div]
  norm_num

/-- **Contrast with statement-bound `H(y, t)` (`FiatShamirNIZK`)**: on the *exact same* protocol
`schnorr2D`, even when an adversary `A` may adaptively choose *any* false statement `y` (`y.2 ≠ 0`)
after `Qro = 1` hash query (`Qp = 0`), statement-bound Fiat–Shamir caps its success probability at
`2 / 5` (`< 4 / 5`), separating `H(y, t)` from `H(t)`. -/
theorem statementBound_falseStmt_soundness_cap
    (A : NIZKSimProver (ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5) (ZMod 5))
    (hA : A.CallBounded 0 1) :
    (Game.succProbability
      (fiatShamirNIZKRealExtGameOn (fun y => decide (y.2 ≠ 0))
        schnorr2D (fun α y => decide (α • ((1, 0) : ZMod 5 × ZMod 5) = y)) A) : ℝ) ≤ 2 / 5 ∧
      (2 / 5 : ℝ) < Game.succProbability unstatedFalseStmtGame := by
  refine ⟨?_, ?_⟩
  · have h := succProbability_fiatShamirNIZKRealExtGameOn_le_of_false
      (fun α y hv => of_decide_eq_true hv)
      schnorr_specialSoundness
      schnorr_specialHVZK
      (schnorr_unpredictableCommitments (ι := ι5) (g := ((1, 0) : ZMod 5 × ZMod 5)) (by decide))
      (linearSimCoinSource
        (fun _ => LinearMap.toSpanSingleton (ZMod 5) (ZMod 5 × ZMod 5) (1, 0)) id ι5)
      (admissible := fun y => decide (y.2 ≠ 0))
      (fun y hy α => schnorr2D_false_of_snd_ne_zero (of_decide_eq_true hy) α)
      hA
    rw [ZMod.card] at h
    exact h.trans (by norm_num)
  · rw [succProbability_unstatedFalseStmtGame]
    norm_num

end CslibFrontierTests.Crypto.FiatShamirNIZK
