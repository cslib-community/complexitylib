/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.NOF.ExactlyN

/-!
# Tests for leaves of number-on-forehead protocols and Exactly-N

Leaf counts and leaves of a small protocol, a leaf seen as a cylinder intersection, checked
instances of `NOF.exactlyN`, the edge case `N = 0` where Exactly-N is constant, a lower bound from
the definition at `N = 1`, the trivial upper bound, and nonvacuity of the corners-theorem
hypothesis of `NOF.ExactlyN.lt_ecomplexityFun`.
-/

open Cslib Cslib.Communication Cslib.Communication.NOF Filter

namespace CommunicationNOFExactlyNTests

/-! ### Leaves -/

/-- Player `0` announces the conjunction of the bits it sees, then player `1` announces `x 0`. -/
private def twoRounds : NOF.Protocol (fun _ : Fin 3 => Bool) Bool :=
  .speak 0 (fun v => v ⟨1, by decide⟩ && v ⟨2, by decide⟩) (.output false)
    (.speak 1 (fun v => v ⟨0, by decide⟩) (.output false) (.output true))

example : twoRounds.leafCount = 3 := by
  simp [twoRounds]

/-- The input `(1, 1, 1)` reaches the rightmost leaf. -/
example : (twoRounds.leaf ![true, true, true] : ℕ) = 2 := by
  simp [twoRounds, NOF.Protocol.leaf_speak, NOF.Protocol.leaf_output]

/-- The input `(1, 0, 1)` reaches the leftmost leaf. -/
example : (twoRounds.leaf ![true, false, true] : ℕ) = 0 := by
  simp [twoRounds, NOF.Protocol.leaf_speak, NOF.Protocol.leaf_output]

/-- The inputs reaching a leaf form a cylinder intersection. -/
example (l : Fin twoRounds.leafCount) :
    IsCylinderIntersection {x : Fin 3 → Bool | twoRounds.leaf x = l} :=
  twoRounds.isCylinderIntersection_leaf l

/-! ### Exactly-N -/

example : exactlyN 5 ![1, 2, 2] = true := exactlyN_eq_true_iff.mpr (by decide)

example : exactlyN 5 ![1, 2, 3] = false := by
  rw [Bool.eq_false_iff, ne_eq, exactlyN_eq_true_iff]
  decide

/-- With `N = 0` every input is `(0, 0, 0)`, so Exactly-0 is constant and needs no bits. -/
example : NOF.Protocol.ecomplexityFun (exactlyN 0) = 0 := by
  refine nonpos_iff_eq_zero.mp (NOF.Protocol.ecomplexityFun_le_iff (k := 0) |>.mpr
    ⟨.output true, funext fun x => ?_, le_rfl⟩)
  rw [NOF.Protocol.run_output, eq_comm, exactlyN_eq_true_iff]
  simp only [Fin.val_eq_zero, add_zero]

/-- Exactly-1 is not constant, so every protocol computing it writes a bit. -/
example : 1 ≤ NOF.Protocol.ecomplexityFun (exactlyN 1) := by
  refine NOF.Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_
  cases p with
  | output z =>
    have h0 := congrFun hp ![0, 0, 0]
    have h1 := congrFun hp ![1, 0, 0]
    simp only [NOF.Protocol.run_output] at h0 h1
    have h0' : exactlyN 1 ![0, 0, 0] = false := by
      rw [Bool.eq_false_iff, ne_eq, exactlyN_eq_true_iff]
      decide
    have h1' : exactlyN 1 ![1, 0, 0] = true := exactlyN_eq_true_iff.mpr (by decide)
    exact absurd ((h0.trans h0').symm.trans (h1.trans h1')) (by decide)
  | speak i send p₀ p₁ => simp

/-- The trivial upper bound: Exactly-N has finite communication complexity. -/
example : NOF.Protocol.ecomplexityFun (exactlyN 10) ≤ 11 := ExactlyN.ecomplexityFun_le 10

/-! ### The corners-theorem lower bound -/

/-- The hypothesis of the lower bound holds for all large `N`, so the bound is not vacuous. -/
example (c : ℕ) : ∃ N, cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9) ≤ N / 2 + 1 :=
  ⟨2 * cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9), by omega⟩

/-- For every `c`, Exactly-N needs more than `c` bits once `N` is large. -/
example (c : ℕ) : ∀ᶠ N in atTop, (c : ℕ∞) < NOF.Protocol.ecomplexityFun (exactlyN N) :=
  ENat.tendsto_nhds_top_iff_natCast_lt.mp ExactlyN.tendsto_ecomplexityFun c

/-- In particular, Exactly-N needs more than `c` bits when `N` is twice the corners bound. -/
example (c : ℕ) :
    (c : ℕ∞) <
      NOF.Protocol.ecomplexityFun (exactlyN (2 * cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9))) :=
  ExactlyN.lt_ecomplexityFun (by omega)

end CommunicationNOFExactlyNTests
