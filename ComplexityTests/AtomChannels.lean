/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Probability.PairwiseIndependentHash.AtomChannels
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for dense atoms over affine channels at two rates

* The joint retention probability at two rates over `𝔽₃`, exactly.
* Nested boxes.
* The dense atom identity at two rates for a concrete walk over `𝔽₅`.
-/

namespace ComplexityTests.AtomChannels

open Finset Cslib.Probability
open scoped BigOperators

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- Over `𝔽₃` in one coordinate, `0` lands in the box of side `2` and `1` in the box of side `1`
-- with probability `2/3 · 1/3 = 2/9`.
example : dens {s | affineRetains 3 1 2 s 0 ∧ affineRetains 3 1 1 s 1} = 2 / 9 := by
  rw [dens_affineRetains_and_affineRetains (by norm_num) (by norm_num) (by decide)]
  norm_num

-- A seed that retains `y` with side `1` retains it with side `2`.
example (s : Matrix (Fin 2) (Fin 1) (ZMod 5) × (Fin 2 → ZMod 5)) (y : ZMod 5)
    (h : affineRetains 5 2 1 s y) : affineRetains 5 2 2 s y :=
  affineRetains_of_le (by norm_num) h

/-- The `½`-walk `x → x + 1` on `ZMod 5`. -/
private noncomputable def W : Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun x w => if w = x + 1 then 1 / 2 else 0

/-- Main function zero through `1/2`. -/
private noncomputable def k : ℝ → ℝ := fun d => if d ≤ 1 / 2 then 0 else d

/-- Gate function: one below `1/1000`. -/
private noncomputable def ρ : ℝ → ℝ := fun r => if r < 1 / 1000 then 1 else 0

private theorem row_mass (x : ZMod 5) : ∑ w, W x w ≤ 1 / 2 := by
  simp [W, Finset.sum_ite_eq']

-- Rank channel of side `⌈5 · 1/2⌉ = 3` in `𝔽₅²` (rate `f = 1/4`), usage channel of side `1`:
-- the atom at `(0, 1)` has conditional mean `k (W 0 1 / f) = k 2 = 2`, for `K = 8002`.
example : 𝔼 s ∈ ({s | affineRetains 5 2 1 s (id 1)} :
      Finset (Matrix (Fin 2) (Fin 1) (ZMod 5) × (Fin 2 → ZMod 5))),
    Matrix.denseAtom (fun s v => affineRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun s v => affineRetains 5 2 1 s (id v)) k (fun _ => 1) ρ 8002 ((1 / 2 : ℝ) ^ 2) W s 0 1 =
    2 := by
  have hceil : ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  rw [expect_denseAtom_affineRetains (V := ZMod 5) (ident := id) Function.injective_id
    (by norm_num) (by norm_num) (Lt := 1) (by norm_num) (by rw [hceil]; norm_num)
    (fun _ _ => rfl) (fun r => by unfold ρ; split_ifs <;> norm_num)
    (fun r => by unfold ρ; split_ifs <;> norm_num) (by norm_num : (0 : ℝ) < 1 / 2000)
    (fun r hr => by unfold ρ; rw [ite_eq_left_iff]; exact fun h => absurd (by linarith) h)
    (fun w => by unfold W; split_ifs <;> norm_num) (row_mass 0) (by norm_num)]
  norm_num [k, W]

end ComplexityTests.AtomChannels
