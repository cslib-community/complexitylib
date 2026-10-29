/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Boolean.ACC0

/-!
# Tests for `ACC⁰`

Concrete evaluations of `modGate` and non-vacuity witnesses for `ACC0` and `SIZEMod` from
`Complexity.Computability.Circuit.Boolean.ACC0`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Boolean.ACC0

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Concrete gate evaluations -/

example : modGate 0 3 ![false, true, false] = true := by decide
example : modGate 0 3 ![false, false, false] = false := by decide
example : modGate 1 3 ![true, true, true] = false := by decide
example : modGate 2 3 ![true, false, true] = false := by decide
example : modGate 2 3 ![true, true, true] = true := by decide
example : modGate 6 4 ![true, true, true, false] = true := by decide

-- Non-vacuity of `SIZEMod`: for every modulus `q`, every `c ≥ 1`, and every degree `k`,
-- `Language.ofSlices (modGate q)` belongs to `SIZEMod q (fun n => c * (n + 1) ^ k)`.
theorem modGate_mem_SIZEMod (q : ℕ) {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    Language.ofSlices (modGate q) ∈ SIZEMod q fun n => c * (n + 1) ^ k := by
  intro n
  refine ⟨Circuit.oneGate (σ := Unbounded.extSignature) (.gate n) id, ?_, ?_⟩
  · intro x
    funext j
    rw [Language.slice_ofSlices]
    rfl
  · rw [Circuit.size_oneGate]
    exact Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Nat.succ_ne_zero n)))

/-! ### Concrete class inclusions and strict separations -/

example : AC0 ⊂ AC0Mod 6 :=
  AC0_ssubset_AC0Mod_two.trans_subset (AC0Mod_subset_AC0Mod_of_dvd (by decide) ⟨3, rfl⟩)

example : AC0Mod 3 ⊆ AC0Mod 6 :=
  AC0Mod_subset_AC0Mod_of_dvd (by decide) ⟨2, rfl⟩

example : AC0 ⊂ TC0 :=
  AC0_ssubset_ACC0.trans_subset ACC0_subset_TC0

example : AC0Mod 3 ⊂ TC0 :=
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  (AC0Mod_ssubset_ACC0 (by decide)).trans_subset ACC0_subset_TC0

example : AC0Mod 5 ⊂ NC 2 :=
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  (AC0Mod_ssubset_ACC0 (by decide)).trans_subset ACC0_subset_NC_two

example : Language.ofSlices (modGate 2) ⊓ Language.ofSlices (modGate 3) ∈ ACC0 :=
  ACC0.inf (modGate_mem_ACC0 2) (modGate_mem_ACC0 3)

example : Language.ofSlices (modGate 6) ∈ TC0 ∧
    Language.ofSlices (modGate 6) ∈ AC 1 ∧
    Language.ofSlices (modGate 6) ∈ NC 2 ∧
    Language.ofSlices (modGate 6) ∈ PPoly :=
  ⟨ACC0_subset_TC0 (modGate_mem_ACC0 6),
    ACC0_subset_AC_one (modGate_mem_ACC0 6),
    ACC0_subset_NC_two (modGate_mem_ACC0 6),
    ACC0_subset_PPoly (modGate_mem_ACC0 6)⟩

example : ∃ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∧
    (∀ c, L ∉ SIZEMod 6 fun n => c * (n + 1) ^ 3) ∧
    L ≠ Language.ofSlices (modGate 6) := by
  obtain ⟨L, hL₂, hnot⟩ := exists_mem_SigmaP_two_notMem_SIZEMod 6 3
  refine ⟨L, hL₂, hnot, ?_⟩
  rintro rfl
  exact hnot 1 (modGate_mem_SIZEMod 6 (by decide) 3)

example : ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧
    L ∉ AC0Mod 3 ∧ L ∉ AC0 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨L, hP, hnot3⟩ := exists_mem_P_notMem_AC0Mod (p := 3) (by decide)
  exact ⟨L, hP, hnot3, fun hAC0 => hnot3 (AC0_subset_AC0Mod 3 hAC0)⟩

end ComplexityTests.Computability.Circuit.Boolean.ACC0
