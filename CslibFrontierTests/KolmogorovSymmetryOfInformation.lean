/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Kolmogorov.SymmetryOfInformation
import CslibFrontier.Computability.Kolmogorov.Uncomputability
import CslibFrontier.Foundations.Computability.DistinctValues

/-!
Regression clients for the enumeration of distinct values (`Nat.distinctValues`,
`Nat.nthDistinctValue`), the conditional universal description method `condUniversal`, and the
Kolmogorov–Levin symmetry of information.
-/

namespace ComplexityTests.KolmogorovSymmetryOfInformation

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Nat.Partrec

/-! ### Distinct values of concrete sequences -/

-- Repetitions and gaps are skipped; values are listed in order of first appearance.
example : Nat.distinctValues (fun n => some (n % 3)) 7 = [0, 1, 2] := by decide

example :
    Nat.distinctValues (fun n => if n % 2 = 0 then some (5 - n / 2) else none) 8 =
      [5, 4, 3, 2] := by
  decide

example : Nat.distinctValues (fun n => some (2 - n % 3)) 5 = [2, 1, 0] := by decide

-- The `i`-th distinct value is found by an unbounded search.
example : 2 ∈ Nat.nthDistinctValue (fun n => some (n % 3)) 2 :=
  Nat.mem_nthDistinctValue_iff.mpr ⟨3, by decide⟩

-- A sequence that never reports a value has no distinct values.
example (i b : ℕ) : b ∉ Nat.nthDistinctValue (fun _ => (none : Option ℕ)) i := fun h => by
  obtain ⟨n, hn⟩ := Nat.exists_eq_some_of_mem_nthDistinctValue h
  cases hn

-- With a range of three values there is no fourth distinct value.
example (b : ℕ) : b ∉ Nat.nthDistinctValue (fun n => some (n % 3)) 3 := fun h => by
  have hrange : {b | ∃ n, some (n % 3) = some b} = ({0, 1, 2} : Set ℕ) := by
    ext b
    simp only [Option.some.injEq, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩
      omega
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hlt := Nat.lt_ncard_of_mem_nthDistinctValue (hrange ▸ Set.toFinite _) h
  rw [hrange, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by simp)] at hlt
  omega

/-! ### The conditional universal method -/

-- The code `left` outputs the condition: the program `codeHeader left` describes `y` given `y`.
example (y : ℕ) : (condUniversal y).Produces (codeHeader Code.left) y := by
  have h := condUniversal_produces_codeHeader_append (y := y) (c := Code.left) (p := []) (x := y)
  rw [List.append_nil] at h
  exact h.mpr (by simp [Code.eval])

-- The condition matters: `C(x | x)` is bounded, `C(x)` is not.
example : ∃ x : ℕ, (condUniversal x).complexity x < universal.complexity x := by
  obtain ⟨c, hc⟩ := exists_complexity_condUniversal_self_le
  obtain ⟨x, hx⟩ := exists_le_complexity_universal (c + 1)
  exact ⟨x, by have := hc x; omega⟩

/-! ### Counting pairs of bounded complexity -/

-- At most one number `v` has `C(x, v) ≤ 0`, for every description method.
example (M : DescriptionMethod ℕ) (x : ℕ) :
    {v | M.ecomplexity (Nat.pair x v) ≤ (0 : ℕ)}.ncard ≤ 1 := by
  have h := M.ncard_setOf_ecomplexity_pair_le_lt 0 x
  omega

-- At most one number has `2 ^ k` partners of complexity at most `k`.
example (M : DescriptionMethod ℕ) (k : ℕ) :
    {u | 2 ^ k ≤ {v | M.ecomplexity (Nat.pair u v) ≤ k}.ncard}.ncard ≤ 1 := by
  have h := M.two_pow_mul_ncard_setOf_two_pow_le_ncard_lt k k
  rw [pow_succ] at h
  have h2 : 0 < 2 ^ k := pow_pos Nat.two_pos k
  by_contra hc
  have : 2 ^ k * 2 ≤ 2 ^ k * {u | 2 ^ k ≤ {v | M.ecomplexity (Nat.pair u v) ≤ k}.ncard}.ncard :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ### Symmetry of information -/

-- The pair `⟨x, x⟩` has the complexity of `x` up to a logarithmic term, since `C(x | x) = O(1)`.
example : ∃ c : ℕ, ∀ x, universal.complexity x ≤
    universal.complexity (Nat.pair x x) + 6 * (universal.complexity (Nat.pair x x)).size + c := by
  obtain ⟨c, hc⟩ := exists_abs_complexity_universal_pair_sub_le
  refine ⟨c, fun x => ?_⟩
  have h := (abs_le.mp (hc x x)).1
  omega

example : ∃ c : ℕ, ∀ x, universal.complexity (Nat.pair x x) ≤
    universal.complexity x + 6 * (universal.complexity (Nat.pair x x)).size + c := by
  obtain ⟨c, hc⟩ := exists_abs_complexity_universal_pair_sub_le
  obtain ⟨d, hd⟩ := exists_complexity_condUniversal_self_le
  refine ⟨c + d, fun x => ?_⟩
  have h := (abs_le.mp (hc x x)).2
  have := hd x
  omega

-- A number carries all its information about itself: `I(x : x) ≥ C(x) - O(1)`.
example : ∃ c : ℕ, ∀ x, (universal.complexity x : ℤ) - c ≤ algorithmicInformation x x := by
  obtain ⟨c, hc⟩ := exists_complexity_condUniversal_self_le
  refine ⟨c, fun x => ?_⟩
  have := hc x
  rw [algorithmicInformation]
  omega

-- Information is symmetric for the pair `(x, x)` trivially, and up to `12 log C(x, y)` in general.
example : ∃ c : ℕ, ∀ x y, algorithmicInformation x y ≤
    algorithmicInformation y x + 12 * (universal.complexity (Nat.pair x y)).size + c := by
  obtain ⟨c, hc⟩ := exists_abs_algorithmicInformation_sub_algorithmicInformation_le
  exact ⟨c, fun x y => by have := (abs_le.mp (hc x y)).2; omega⟩

end ComplexityTests.KolmogorovSymmetryOfInformation
