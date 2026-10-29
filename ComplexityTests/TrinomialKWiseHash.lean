/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.FieldTheory.Finite.Trinomial
public import Complexity.Probability.KWiseIndependent.Trinomial
public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.WordRAM.Hashing.MultiplyShift

/-!
# Unit tests for trinomial binary fields, `k`-wise independent trinomial hashing, `Dictionary.spec`,
and Word-RAM `MultiplyShift`

Verifies non-vacuity and concrete behavior of:
1. `Cslib.trinomial`, `Cslib.irreducible_trinomial`, `Cslib.clmul`, `Cslib.reduceTrinomialCode`,
   and `Cslib.TrinomialField`;
2. `Cslib.Probability.trinomialPolyHash` and
   `Cslib.Probability.isKWiseIndependentHash_trinomialPolyHash` at `k = 5`, together with
   `Cslib.Probability.trinomialStep` degree bounds;
3. `Cslib.Algorithms.Lean.Dictionary.spec` including in-place overwrites at full capacity `n_max`;
4. `Cslib.Algorithms.WordRAM.Hashing.MultiplyShift.initCode`, `evalCode`, and
   `isUniversalHash_evalData`.
-/

public section

namespace ComplexityTests.TrinomialKWiseHash

open Cslib Cslib.Probability Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Hashing
open scoped ENNReal

/-! ## 1. Explicit trinomial binary fields and 4-limb reduction -/

/-- `trinomial 0 = X ^ 2 + X + 1` and `trinomial 1 = X ^ 6 + X ^ 3 + 1` are irreducible over
`ZMod 2`. -/
theorem trinomial_zero_and_one_irreducible :
    Irreducible (trinomial 0) ∧ Irreducible (trinomial 1) ∧
    Fintype.card (TrinomialField 0) = 4 ∧ Fintype.card (TrinomialField 1) = 64 :=
  ⟨irreducible_trinomial 0, irreducible_trinomial 1,
   TrinomialField.card 0, TrinomialField.card 1⟩

/-- Concrete check of `clmul` and `reduceTrinomialCode` at `t = 0` (`X ^ 2 + X + 1`, code `7`):
multiplying `X + 1` (code `3`) by `X + 1` (code `3`) gives `X ^ 2 + 1` (code `5`), which reduces
modulo `X ^ 2 + X + 1` to `X` (code `2`). -/
theorem clmul_and_reduce_t0 :
    clmul 3 3 = 5 ∧
    reduceTrinomialCode 0 (clmul 3 3) = 2 ∧
    AdjoinRoot.mk (trinomial 0) (polyOfCode 2) =
      AdjoinRoot.mk (trinomial 0) (polyOfCode 3 * polyOfCode 3) := by
  have hcl : clmul 3 3 = 5 := by
    rw [clmul, clmul, clmul]
    decide
  have hred : reduceTrinomialCode 0 (clmul 3 3) = 2 := by
    rw [hcl]
    decide
  refine ⟨hcl, hred, ?_⟩
  have h2 : polyOfCode 2 = polyOfCode (reduceTrinomialCode 0 (clmul 3 3)) :=
    congrArg polyOfCode hred.symm
  rw [h2, mk_polyOfCode_reduceTrinomialCode, polyOfCode_clmul]

/-- Concrete check of 4-limb reduction at `t = 1` (`r = 3`, degree `6`, modulus
`X ^ 6 + X ^ 3 + 1`): for `c = 2 ^ 11 + 2 ^ 7 + 5 = 2181 < 2 ^ 12`, `reduceTrinomialCode 1 c = 19`
(`X ^ 4 + X + 1`) and represents the same element of `TrinomialField 1`. -/
theorem reduce_t1_sound :
    let c := 2 ^ 11 + 2 ^ 7 + 5
    reduceTrinomialCode 1 c = 19 ∧
    reduceTrinomialCode 1 c < 64 ∧
    AdjoinRoot.mk (trinomial 1) (polyOfCode 19) =
      AdjoinRoot.mk (trinomial 1) (polyOfCode c) := by
  have hred : reduceTrinomialCode 1 (2 ^ 11 + 2 ^ 7 + 5) = 19 := by decide
  refine ⟨hred, reduceTrinomialCode_lt 1 (by decide), ?_⟩
  have h19 : polyOfCode 19 = polyOfCode (reduceTrinomialCode 1 (2 ^ 11 + 2 ^ 7 + 5)) :=
    congrArg polyOfCode hred.symm
  rw [h19, mk_polyOfCode_reduceTrinomialCode]

/-! ## 2. Exact `5`-wise independent trinomial polynomial hashing -/

/-- Non-vacuous `5`-wise independent hash family from `Fin 1000` onto `Fin 1024` (`M = 10`) over
`TrinomialField 2` (degree `2 * 3 ^ 2 = 18`, field size `2 ^ 18 = 262144`). -/
theorem five_wise_independent_trinomialPolyHash :
    IsKWiseIndependentHash 5 (trinomialPolyHash 2 5 1000 10) :=
  isKWiseIndependentHash_trinomialPolyHash (by decide) (by decide)

/-- Using `trinomialStep U M` automatically selects a valid trinomial field degree for any `(U, M)`
and yields an exact `5`-wise independent family onto `Fin (2 ^ M)`. -/
theorem five_wise_independent_auto_step (U M : ℕ) :
    let t := trinomialStep U M
    U ≤ 2 ^ (2 * 3 ^ t) ∧
    M ≤ 2 * 3 ^ t ∧
    2 * 3 ^ t ≤ 3 * max (Nat.clog 2 (max U 2)) (max M 1) ∧
    IsKWiseIndependentHash 5 (trinomialPolyHash t 5 U M) :=
  ⟨le_two_pow_trinomialDeg U M,
   le_trinomialDeg U M,
   trinomialDeg_le_three_mul U M,
   isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M)⟩

/-- Concrete check of `trinomialStep`: for `U = 1000, M = 10`, `trinomialStep 1000 10 = 2` and
`trinomialDeg 1000 10 = 18`. -/
theorem trinomialStep_concrete :
    trinomialStep 1000 10 = 2 ∧ trinomialDeg 1000 10 = 18 := by
  have hclog : Nat.clog 2 (max 1000 2) ≤ 10 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr (by decide)
  have ht : trinomialTargetBits 1000 10 = 10 := by
    rw [trinomialTargetBits]
    omega
  have hs : trinomialStep 1000 10 = 2 := by
    rw [trinomialStep, ht, trinomialStepAux, trinomialStepAux, trinomialStepAux]
    decide
  exact ⟨hs, by rw [trinomialDeg, hs]; decide⟩

/-! ## 3. Bounded-capacity `Dictionary.spec` -/

/-- Concrete operation history on `Dictionary.spec 8 100 2` (universe `8`, values `< 100`, capacity
`n_max = 2`):
inserts two distinct keys `(1, 42)` and `(5, 17)` reaching capacity `2`, then overwrites key `1`
in-place with `99` (which is valid even at full capacity `(dom s).card = 2` because key `1` is
already present!), and queries keys `1`, `5`, and `3`. -/
def sampleDictOps : List (Dictionary.Op 8) :=
  [.insert 1 42, .insert 5 17, .insert 1 99, .get 1, .get 5, .get 3]

theorem sampleDictOps_valid_and_run :
    (Dictionary.spec 8 100 2).ValidHistory (Dictionary.empty 8) sampleDictOps ∧
    let finalState := ((Dictionary.spec 8 100 2).run (Dictionary.empty 8) sampleDictOps).1
    (Dictionary.dom finalState).card = 2 ∧
    Dictionary.ValuesBounded 100 finalState ∧
    finalState 1 = some 99 ∧
    finalState 5 = some 17 ∧
    finalState 3 = none := by
  have hvh : (Dictionary.spec 8 100 2).ValidHistory (Dictionary.empty 8) sampleDictOps := by
    dsimp [sampleDictOps, Stateful.Spec.ValidHistory, Dictionary.spec]
    decide
  refine ⟨hvh, ?_,
    Dictionary.valuesBounded_run_of_validHistory (Dictionary.valuesBounded_empty 8 100) hvh,
    by decide, by decide, by decide⟩
  decide

/-! ## 4. Self-contained Word-RAM `MultiplyShift` -/

/-- Non-vacuous execution of `MultiplyShift.initCode` and `MultiplyShift.evalCode` at sub-word width
`w₀ = 8`, output bits `M = 4`, and machine word width `w = 16` (`2 * w₀ ≤ w`):
* `initCode 8` executes in `2` instructions and `1` `rand` call, producing a uniform seed in
  `Fin 128`;
* `evalCode 8 4` executes in `9` deterministic instructions, computing `multiplyShift 8 4 b x` in
  register `regOut`;
* the resulting hash family is `(2 / 16)`-universal. -/
theorem multiplyShift_wordram_concrete (d : Data 5) :
    ExecRand 16 (MultiplyShift.initCode 8) d (MultiplyShift.initComp 8 d) ∧
    ((MultiplyShift.initComp 8 d).eval).map (fun z => MultiplyShift.extractSeed 8 z.1) =
      PMF.uniformOfFintype (Fin 128) ∧
    (∀ b : Fin 128, ∀ x : Fin 256,
      let dIn := (d.set MultiplyShift.regB b.val).set MultiplyShift.regX x.val
      Exec 16 (MultiplyShift.evalCode 8 4) dIn (MultiplyShift.evalData 8 4 dIn) 9 ∧
      (MultiplyShift.evalData 8 4 dIn).regs MultiplyShift.regOut = multiplyShift 8 4 b x) ∧
    IsUniversalHash
      (((MultiplyShift.initComp 8 d).eval).map (fun z => MultiplyShift.extractSeed 8 z.1))
      (fun b (x : Fin 256) =>
        (MultiplyShift.evalData 8 4
          ((d.set MultiplyShift.regB b.val).set MultiplyShift.regX x.val)).regs
          MultiplyShift.regOut)
      (2 / 2 ^ 4) := by
  refine ⟨MultiplyShift.initCode_execRand (by decide) d,
    MultiplyShift.map_extractSeed_eval_initComp 8 d,
    fun b x => ⟨MultiplyShift.evalCode_exec (by decide) (by decide)
      (by simp [MultiplyShift.regB, MultiplyShift.regX])
      (by simp [MultiplyShift.regX]),
      MultiplyShift.evalData_regs_out_eq_multiplyShift 8 4 _ b x
        (by simp [MultiplyShift.regB, MultiplyShift.regX])
        (by simp [MultiplyShift.regX])⟩,
    MultiplyShift.isUniversalHash_evalData (by decide) (by decide) d⟩

end ComplexityTests.TrinomialKWiseHash

end
