/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Protocols.MPC.SPDZ

/-!
# Concrete Tests for SPDZ Authenticated Sharing and Batch `MACCheck`

Non-vacuous concrete evaluations, protocol executions, and soundness instantiations over `ZMod 5`
(`p = 5`, `n = 1` and `n = 2`, `T = 1` and `T = 2`) exercising
`Complexity.Crypto.Protocols.MPC.SPDZ`:

1. **SPDZ authenticated sharing & online Beaver operations (`ZMod 5`, `n = 2` and `n = 1`):**
   concrete `AuthShare` addition, negation, subtraction, scalar multiplication, constant addition,
   and `mulOnline` preserving `Valid alpha`, reconstructing `x * y = 3 * 2 = 1` via
   `secret_mulOnline_eq_mul`, and matching `Beaver.beaverMulShare` coordinatewise via
   `valShares_mulOnline_eq_beaverMulShare`.
2. **Batch `MACCheck` completeness, residual identity, and forged-opening detection (`ZMod 5`,
   `n = 2`, `T = 2`):** honest two-round `macCheckProtocol` acceptance (`n = 2, T = 2` and `n = 1,
   T = 1` edge case), commitment-mismatch rejection in `verifyResiduals`, and concrete verification
   of `sum_checkResidual_eq_neg_mul` and `sum_checkResidual_add_eq_zero_iff` on a forged opening.
3. **`2 / p` soundness games (`ZMod 5`, `T = 1` and `T = 2`):** concrete instantiations of
   `eval_linearCombZeroGame_eq`, `eval_macCheckSoundnessGame_le`,
   `succProbability_macCheckSoundnessGame_le`, and `eval_macCheckSoundness_bind_le`, together with
   exact counting of accepting `(alpha, e)` pairs (`9` out of `25` pairs on `T = 1`, strictly
   within the `2 / 5 = 10 / 25` soundness bound).
-/

namespace ComplexityTests.Crypto.SPDZ

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Beaver Cslib.Crypto.Protocols.MPC.SPDZ
open scoped ENNReal NNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. Concrete SPDZ authenticated operations over `ZMod 5` -/

/-- Authenticated share of `x = 3` (`valShares = ![1, 2]`, `delta = 1`) under global MAC key
`alpha = 4`: `macSum = 4 * (3 + 1) = 1` (`macShares = ![3, 3]`). -/
def authX : AuthShare 5 2 where
  delta := 1
  valShares := ![1, 2]
  macShares := ![3, 3]

/-- Authenticated share of `y = 2` (`valShares = ![4, 3]`, `delta = 0`) under `alpha = 4`:
`macSum = 4 * (2 + 0) = 3` (`macShares = ![2, 1]`). -/
def authY : AuthShare 5 2 where
  delta := 0
  valShares := ![4, 3]
  macShares := ![2, 1]

/-- Authenticated Beaver triple `(a = 1, b = 4, c = 4)` under `alpha = 4` (`delta = 0`). -/
def authA : AuthShare 5 2 := ⟨0, ![3, 3], ![2, 2]⟩
def authB : AuthShare 5 2 := ⟨0, ![1, 3], ![0, 1]⟩
def authC : AuthShare 5 2 := ⟨0, ![2, 2], ![3, 3]⟩

example : authX.Valid 4 ∧ authY.Valid 4 ∧ authA.Valid 4 ∧ authB.Valid 4 ∧ authC.Valid 4 := by
  decide

/-- Linear combinations (`+`, `-`, `•`, `addConst`) preserve `Valid 4` and reconstruct the
expected secrets over `ZMod 5`. -/
example :
    let lin := AuthShare.addConst 2 ((3 : ZMod 5) • authX - authY)
    lin.secret = (4 : ZMod 5) ∧ lin.Valid 4 := by
  refine ⟨by decide, ?_⟩
  exact AuthShare.Valid.addConst 2
    ((AuthShare.Valid.smul 3 (by decide : authX.Valid 4)).sub (by decide : authY.Valid 4))

/-- Online Beaver multiplication `mulOnline` on `(authA, authB, authC)` with `d = 3 - 1 = 2` and
`e = 2 - 4 = 3` reconstructs `3 * 2 = 1` in `ZMod 5`, preserves `Valid 4`, and matches
`Beaver.beaverMulShare` on each party's value share. -/
example :
    let d : ZMod 5 := (authX - authA).secret
    let e : ZMod 5 := (authY - authB).secret
    let prod := AuthShare.mulOnline authA authB authC d e
    prod.secret = authX.secret * authY.secret ∧
      prod.Valid 4 ∧
      (∀ i : Fin 2,
        prod.valShares i =
          beaverMulShare i (d, e) ⟨authA.valShares i, authB.valShares i, authC.valShares i⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · exact AuthShare.secret_mulOnline_eq_mul authX authY authA authB authC _ _
      (AuthShare.secret_sub authX authA) (AuthShare.secret_sub authY authB) (by decide)
  · exact AuthShare.Valid.mulOnline _ _ (by decide) (by decide) (by decide)
  · intro i
    exact AuthShare.valShares_mulOnline_eq_beaverMulShare authA authB authC _ _ i

/-! ### 2. Batch `MACCheck` completeness, residual identity, and forged openings -/

/-- Honest 2-party `MACCheck` batch of `T = 2` opened values `(authX, authY)` with key shares
`α = ![1, 3]` (sum `4`) and public weights `e = ![2, 3]`. -/
def honestBatch : Fin 2 → PartyCheckInput 5 2 := fun i =>
  { opened := ![⟨3, 1⟩, ⟨2, 0⟩]
    macShares := ![authX.macShares i, authY.macShares i]
    keyShare := ![1, 3] i
    weights := ![2, 3] }

theorem honestBatch_isHonest :
    PartyCheckInput.Honest 4 ![authX, authY] ![⟨3, 1⟩, ⟨2, 0⟩] ![2, 3] honestBatch := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl, by decide, by decide, by decide, by decide⟩, by decide⟩

example : (∑ i : Fin 2, checkResidual (honestBatch i)) = 0 :=
  sum_checkResidual_eq_zero honestBatch_isHonest

/-- Honest execution of the two-round `macCheckProtocol` (`n = 2`, `T = 2`) with additive
commitment `σ + r` accepts with probability `1`. -/
example :
    ((macCheckProtocol 5 2 2 (ProbComp.uniform (ZMod 5)) (· + ·)).evalWith
      noOracleWorld honestBatch).map Prod.snd = PMF.pure (fun _ => true) :=
  eval_snd_macCheckProtocol_eq_pure_true _ _ honestBatch_isHonest

/-- Edge case `n = 1`, `T = 1` for `eval_snd_macCheckProtocol_eq_pure_true`. -/
example :
    let inp : Fin 1 → PartyCheckInput 5 1 := fun _ =>
      { opened := ![⟨2, 1⟩], macShares := ![2], keyShare := 4, weights := ![3] }
    ((macCheckProtocol 5 1 1 (pure (0 : ZMod 5)) (· + ·)).evalWith
      noOracleWorld inp).map Prod.snd = PMF.pure (fun _ => true) := by
  refine eval_snd_macCheckProtocol_eq_pure_true _ _
    (alpha := 4) (shares := ![⟨1, ![2], ![2]⟩]) (opened := ![⟨2, 1⟩]) (e := ![3]) ?_
  exact ⟨⟨fun _ => rfl, fun _ => rfl, by decide, by decide, by decide, by decide⟩, by decide⟩

/-- Forged 2-party `MACCheck` batch where the first opened value is tampered from `3` to `4`
(`err = ![1, 0]`). -/
def forgedBatch : Fin 2 → PartyCheckInput 5 2 := fun i =>
  { opened := ![⟨4, 1⟩, ⟨2, 0⟩]
    macShares := ![authX.macShares i, authY.macShares i]
    keyShare := ![1, 3] i
    weights := ![2, 3] }

theorem forgedBatch_authentic :
    PartyCheckInput.AuthenticFor 4 ![authX, authY] ![⟨4, 1⟩, ⟨2, 0⟩] ![2, 3] forgedBatch := by
  exact ⟨fun _ => rfl, fun _ => rfl, by decide, by decide, by decide, by decide⟩

/-- On `forgedBatch`, `∑ i, checkResidual (forgedBatch i) = -4 * (2 * 1 + 3 * 0) = 2` in `ZMod 5`,
and `sum_checkResidual_add_eq_zero_iff` characterizes the unique compensating shift
`deltaOpen = 3`. -/
example :
    (∑ i : Fin 2, checkResidual (forgedBatch i)) = (2 : ZMod 5) ∧
      ((∑ i : Fin 2, checkResidual (forgedBatch i)) + 3 = 0 ↔
        (4 : ZMod 5) *
          errorLinearComb ![2, 3]
            (fun l => (![⟨4, 1⟩, ⟨2, 0⟩] l : OpenedValue 5).value -
              (![authX, authY] l).secret) = 3) :=
  ⟨by rw [sum_checkResidual_eq_neg_mul forgedBatch_authentic]; decide,
   sum_checkResidual_add_eq_zero_iff forgedBatch_authentic 3⟩

/-- Verification rejects if a party alters its Round-2 residual share after committing in
Round 1. -/
example :
    verifyResiduals (p := 5) (n := 2) (fun s (r : ZMod 5) => s + r)
      ![checkResidual (honestBatch 0), checkResidual (honestBatch 1)]
      ![⟨checkResidual (honestBatch 0) + 1, 0⟩, ⟨checkResidual (honestBatch 1) - 1, 0⟩] =
    false := by
  decide

/-! ### 3. Concrete `2 / p` soundness game instantiations over `ZMod 5` -/

/-- Stage 1 exact probability `1 / 5` on `ZMod 5` (`T = 2`, `err = ![1, 0]`). -/
example :
    (ProbComp.eval (linearCombZeroGame 5 2 ![1, 0])) true = (5 : ℝ≥0∞)⁻¹ :=
  eval_linearCombZeroGame_eq (by decide)

/-- Exact non-vacuity check on `ZMod 5` (`T = 1`, `err = ![1]`): the optimal `e`-adaptive shift
`deltaShift e = if e 0 = 0 then 0 else 1` wins on `5 + 4 * 1 = 9` out of `25` `(alpha, e)` pairs
(`9 / 25 < 2 / 5 = 10 / 25`), illustrating both the `1 / 5` weight-cancellation event (`e 0 = 0`)
and the `1 / 5` key-guessing event (`e 0 ≠ 0`). -/
example :
    (Finset.univ.filter fun ((alpha, e) : ZMod 5 × (Fin 1 → ZMod 5)) =>
      alpha * errorLinearComb e ![1] = (if e 0 = 0 then 0 else 1)).card = 9 := by
  decide

/-- Concrete `2 / 5` soundness bound on `ZMod 5` (`T = 1`, `err = ![1]`) in `ℝ≥0∞`, `ℝ`, and
stateful-adversary `macCheckSoundnessAdvGame` forms. -/
example :
    let deltaShift : (Fin 1 → ZMod 5) → ZMod 5 := fun e => if e 0 = 0 then 0 else 1
    (ProbComp.eval (macCheckSoundnessGame 5 1 ![1] deltaShift)) true ≤ 2 / (5 : ℝ≥0∞) ∧
      (Game.succProbability (ProbComp.eval (macCheckSoundnessGame 5 1 ![1] deltaShift)) : ℝ) ≤
        2 / (5 : ℝ) ∧
      (ProbComp.eval (macCheckSoundnessAdvGame 5 1 (ProbComp.uniform Bool)
        (fun b => if b then ![1] else ![2])
        (fun _ => deltaShift))) true ≤ 2 / (5 : ℝ≥0∞) :=
  ⟨eval_macCheckSoundnessGame_le (by decide) _,
   succProbability_macCheckSoundnessGame_le (by decide) _,
   eval_macCheckSoundness_bind_le _ _ _⟩

end ComplexityTests.Crypto.SPDZ
