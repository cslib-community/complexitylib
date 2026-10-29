import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime

open Cslib.Logic.PL.ClauseSet.Sparsification
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

-- An eleven-bit inverse budget produces the actual first successful parameter, whose entire
-- output is encoded in binary. Width is fixed separately in each certificate.
/-- info: [(131072, 18), (1048576, 21), (2, 2), (2, 2)] -/
#guard_msgs in
#eval [(2, 1024), (3, 1024), (1, 1024), (3, 0)].map fun (k, B) =>
  let M := countingThresholdBase k B
  (M, (encNat M).length)

private theorem width_two_budget_1024 : countingThresholdBase 2 1024 = 131072 :=
  countingThresholdBase_eq_two_pow (m := 17) (by decide) (by decide) (by decide) (by decide)

example : (encNat 1024).length = 11 ∧
    (encNat (countingThresholdBase 2 1024)).length = 18 := by
  rw [width_two_budget_1024]
  decide

-- The preceding dyadic value satisfies M≥Γ but fails the exact integer stopping test.
example : countingBChoiceCoeff 2 ≤ 65536 ∧
    ¬ (1024 * countingBChoiceCoeff 2 *
      Nat.clog 2 (4 * countingDepthCoeff 2 65536 * 65536) ≤ 65536) := by decide

-- A binary-input caller computes its budget by multiplication and then invokes the selector.
-- Both the original input and the computed budget retain binary encodings throughout.
example : ComputableInPolyTime (fun B : ℕ => countingThresholdBase 3 (B * B))
    encNat encNat :=
  (computableInPolyTime_countingThresholdBase 3).comp (binary_mul' id' id')

/-- info: 1048576 -/
#guard_msgs in
#eval countingThresholdBase 3 (32 * 32)

-- Output is charged as a complete binary word, not as a constant-size numeric register.
example : ¬ (encNat (countingThresholdBase 2 1024)).length ≤ 11 := by
  rw [width_two_budget_1024]
  decide
