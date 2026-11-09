/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.ModP.PrimePower
import Complexity.Computability.Complexity.Classes.SharpP.Choose
import Complexity.Foundations.Data.Nat.Choose.PrimePowerDvd
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Prime-power moduli, binomial #P counts and base-`p` digits. -/

namespace ComplexityTests.ModPPrimePower

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Base-`p` digits as binomial coefficients -/

/-- `10 = 1010₂`: `C(10, 2 ^ i)` is odd exactly at the binary digits `1` of `10`. -/
example : (10 : ℕ).choose 1 % 2 = 0 ∧ (10 : ℕ).choose 2 % 2 = 1 ∧ (10 : ℕ).choose 4 % 2 = 0 ∧
    (10 : ℕ).choose 8 % 2 = 1 := by decide

/-- `21 = 210₃`: `C(21, 3) = 1330 ≡ 1` and `C(21, 9) = 293930 ≡ 2` modulo `3`. -/
example : (21 : ℕ).choose 3 % 3 = 1 ∧ (21 : ℕ).choose 9 % 3 = 2 := by decide

/-- `9 ∣ 18` and `27 ∤ 18`, read from the binomial coefficients at `3 ^ 0, 3 ^ 1, 3 ^ 2`. -/
example : 3 ^ 2 ∣ 18 ∧ ¬3 ^ 3 ∣ 18 := by
  refine ⟨(Nat.pow_dvd_iff_forall_dvd_choose Nat.prime_three 2 18).mpr fun i hi => ?_,
    fun h => ?_⟩
  · interval_cases i <;> decide
  · have := (Nat.pow_dvd_iff_forall_dvd_choose Nat.prime_three 3 18).mp h 2 (by decide)
    revert this
    decide

/-! ### Binomial coefficients of #P counts -/

/-- The number of `2`-element sets of length-`|w|` words is in #P. -/
example : (fun w : List Bool => (2 ^ w.length).choose 2) ∈ SharpP encBits := by
  have h := SharpP.choose_mem (SharpP.two_pow_mem (enc := encBits) Polynomial.X)
    (ComputableInPolyTime.const 2)
  simpa [encBits_apply] using h

/-- With five accepted rows of width three, the subset test accepts `C(5, 2) = 10` words using
three rows, the last of which must be zero. -/
example : (Finset.univ.filter fun zs : Fin (3 * 3) → Bool =>
    SharpP.subsetTest (fun w => decide (w ≠ [true, true, true] ∧ w ≠ [true, true, false] ∧
      w ≠ [true, false, true])) 3 3 2 (List.ofFn zs) = true).card = 10 := by
  rw [SharpP.card_filter_subsetTest _ 3 (by decide)]
  decide

/-! ### The prime-power collapse -/

example : ModP 4 encBits = ModP 2 encBits := ModP_prime_pow (e := 2) Nat.prime_two two_ne_zero

example : ModP 4 encBits = ParityP encBits := ModP_two_pow (e := 2) two_ne_zero

example : ModP 9 encBits = ModP 3 encBits := ModP_prime_pow (e := 2) Nat.prime_three two_ne_zero

example : ModP 8 encBits = ModP (Nat.minFac 8) encBits :=
  ModP_eq_ModP_minFac ⟨2, 3, Nat.prime_two.prime, by decide, by decide⟩

private theorem isPrimePow_nine : IsPrimePow 9 :=
  ⟨3, 2, Nat.prime_three.prime, by decide, by decide⟩

/-- The odd-head language: one witness exactly when the first bit is `true`. -/
private theorem head_mem_ModP_nine : {w : List Bool | w.headD false = true} ∈ ModP 9 encBits :=
  P_subset_ModP (by decide) ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- Prime-power complement closure, on a language with a single-witness count. -/
example : {w : List Bool | w.headD false = true}ᶜ ∈ ModP 9 encBits :=
  compl_mem_ModP_of_isPrimePow isPrimePow_nine head_mem_ModP_nine

example : {w : List Bool | w.headD false = true}ᶜ ∈ coModP 9 encBits := by
  rw [coModP_eq_ModP_of_isPrimePow isPrimePow_nine]
  exact compl_mem_ModP_of_isPrimePow isPrimePow_nine head_mem_ModP_nine

example : (Set.univ : Set (List Bool)) ∈ ModP 9 encBits := by
  simpa using union_mem_ModP_of_isPrimePow isPrimePow_nine head_mem_ModP_nine
    (compl_mem_ModP_of_isPrimePow isPrimePow_nine head_mem_ModP_nine)

/-- The divisor inclusion at a composite modulus that is not a prime power. -/
example : ModP 3 encBits ⊆ ModP 6 encBits := ModP_subset_ModP_of_dvd (by decide) (by decide)

end ComplexityTests.ModPPrimePower
