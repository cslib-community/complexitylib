/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Separation of `NP` from `NEXP`

This module proves that `NP` is strictly contained in `NEXP` on bitstrings
(`Cslib.Complexity.not_NEXP_subset_NP`, `Cslib.Complexity.NP_ssubset_NEXP`). This is a special case
of the nondeterministic time hierarchy theorem [Arora and Barak, Theorem 3.2][AroraBarak09], proved
here by translation from the deterministic time hierarchy (`setOf_timeDiagonal_notMem_DTIME`) via
double-exponential padding (`preimage_append_two_pow_mem_NEXP`), without formalizing the general
nondeterministic time hierarchy.

## Main results

* `Cslib.Complexity.not_NEXP_subset_NP`: `NEXP encBits` is not contained in `NP encBits`.
* `Cslib.Complexity.NP_ssubset_NEXP`: `NP encBits` is strictly contained in `NEXP encBits`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

private theorem timeDiagonal_two_pow_two_pow_bound (n : ℕ) :
    (n + 1) ^ 5 * (2 ^ (2 ^ n) + 1) ^ 3 ≤ 2 ^ (2 ^ (n + 4)) := by
  have h₁ : n + 1 ≤ 2 ^ (2 ^ n) := by
    calc n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
  have h₂ : (n + 1) ^ 5 ≤ 2 ^ (5 * 2 ^ n) := by
    calc (n + 1) ^ 5 ≤ (2 ^ (2 ^ n)) ^ 5 := Nat.pow_le_pow_left h₁ 5
      _ = 2 ^ (5 * 2 ^ n) := by rw [← Nat.pow_mul, mul_comm]
  have h₃ : 2 ^ (2 ^ n) + 1 ≤ 2 ^ (2 * 2 ^ n) := by
    have hp₁ : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_two_pow
    have hp₂ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc 2 ^ (2 ^ n) + 1 ≤ 2 * 2 ^ (2 ^ n) := by omega
      _ = 2 ^ (2 ^ n + 1) := (pow_succ' 2 (2 ^ n)).symm
      _ ≤ 2 ^ (2 * 2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₄ : (2 ^ (2 ^ n) + 1) ^ 3 ≤ 2 ^ (6 * 2 ^ n) := by
    calc (2 ^ (2 ^ n) + 1) ^ 3 ≤ (2 ^ (2 * 2 ^ n)) ^ 3 := Nat.pow_le_pow_left h₃ 3
      _ = 2 ^ (6 * 2 ^ n) := by rw [← Nat.pow_mul]; ring_nf
  calc (n + 1) ^ 5 * (2 ^ (2 ^ n) + 1) ^ 3
      ≤ 2 ^ (5 * 2 ^ n) * 2 ^ (6 * 2 ^ n) := Nat.mul_le_mul h₂ h₄
    _ = 2 ^ (11 * 2 ^ n) := by rw [← Nat.pow_add]; ring_nf
    _ ≤ 2 ^ (16 * 2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (2 ^ (n + 4)) := by rw [Nat.pow_add, mul_comm (2 ^ n) (2 ^ 4)]

private theorem timeDiagonal_two_pow_two_pow_mem_NTIME :
    {x | timeDiagonal (fun n => 2 ^ (2 ^ n)) x = true} ∈ NTIME encBits fun n => 2 ^ (2 ^ (n + 4)) :=
  DTIME_subset_NTIME (DTIME_mono timeDiagonal_two_pow_two_pow_bound
    (setOf_timeDiagonal_mem_DTIME timeConstructible_two_pow_two_pow))

/-- **`NEXP` is not contained in `NP`** on bitstrings: a special case of the nondeterministic time
hierarchy theorem [Arora and Barak, Theorem 3.2][AroraBarak09], proved here by translation from the
deterministic time hierarchy (`setOf_timeDiagonal_notMem_DTIME`) via double-exponential padding
(`preimage_append_two_pow_mem_NEXP`), without formalizing the general nondeterministic time
hierarchy. If `NEXP ⊆ NP`, then the doubly-exponential clocked diagonal language, which lies in
`NTIME (2 ^ (2 ^ (n + 4)))`, reduces in two exponential-padding stages through `NEXP ⊆ NP` to a
language in `NP ⊆ EXP`, contradicting `setOf_timeDiagonal_notMem_DTIME` against `EXP`. -/
theorem not_NEXP_subset_NP : ¬ (NEXP encBits ⊆ NP encBits) := by
  intro hSub
  let J (n : ℕ) : ℕ := 2 ^ (2 ^ n)
  let L : Set (List Bool) := {x | timeDiagonal J x = true}
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := timeDiagonal_two_pow_two_pow_mem_NTIME
  set c := Nat.card (Turing.Action k Bool State) * (c₁ + c₂)
  let h₁ (y : List Bool) : List Bool := y ++ List.replicate (2 ^ y.length) true
  let g₂ (x : List Bool) : List Bool := frame x ++ List.replicate (2 ^ (x.length + 4)) true
  have hB₁ : h₁ ⁻¹' ntm.padded c ∈ NP encBits :=
    hSub (preimage_append_two_pow_mem_NEXP (ntm.padded_mem_NP c))
  have hf_add : ComputableInPolyTime (fun n : ℕ => n + 4) encUnary encUnary :=
    (ComputableInPolyTime.unary_add.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 4)))
  have hB₂ : g₂ ⁻¹' (h₁ ⁻¹' ntm.padded c) ∈ NEXP encBits :=
    preimage_pad_mem_NEXP hB₁ hf_add fun n => Nat.le_add_right n 4
  have hL_eq : L = g₂ ⁻¹' (h₁ ⁻¹' ntm.padded c) := by
    ext x
    change x ∈ L ↔ h₁ (g₂ x) ∈ ntm.padded c
    have hpad_eq : h₁ (g₂ x) =
        frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true) := by
      simp [h₁, g₂, List.append_assoc]
    rw [hpad_eq]
    refine (hdec.frame_append_mem_padded_iff (a := x) ?_).symm
    change Nat.card (Turing.Action k Bool State) * (c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂) ≤
      c * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
        List.replicate (2 ^ (g₂ x).length) true)).length
    have hM : 2 ^ (x.length + 4) ≤ (g₂ x).length := by
      simp only [g₂, List.length_append, length_frame, List.length_replicate]
      omega
    have hpow_le : 2 ^ (2 ^ (x.length + 4)) ≤ 2 ^ (g₂ x).length :=
      Nat.pow_le_pow_right (by norm_num) hM
    have hlen_ge : 2 ^ (2 ^ (x.length + 4)) + 1 ≤
        (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true)).length := by
      simp only [List.length_append, length_frame, List.length_replicate]
      calc 2 ^ (2 ^ (x.length + 4)) + 1
          ≤ 2 ^ (g₂ x).length + 1 := Nat.add_le_add_right hpow_le 1
        _ ≤ 2 * x.length + 1 + (2 ^ (x.length + 4) + 2 ^ (g₂ x).length) := by
            have := Nat.zero_le (2 ^ (x.length + 4))
            omega
    have hmul : c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂ ≤
        (c₁ + c₂) * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true)).length := by
      calc c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂
          ≤ c₁ * (2 ^ (2 ^ (x.length + 4)) + 1) + c₂ * (2 ^ (2 ^ (x.length + 4)) + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left c₁ (Nat.le_succ _))
              (Nat.le_mul_of_pos_right c₂ (Nat.succ_pos _))
        _ = (c₁ + c₂) * (2 ^ (2 ^ (x.length + 4)) + 1) := (Nat.add_mul _ _ _).symm
        _ ≤ (c₁ + c₂) * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
            List.replicate (2 ^ (g₂ x).length) true)).length :=
            Nat.mul_le_mul_left _ hlen_ge
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hmul
  have hL_EXP : L ∈ EXP encBits := hL_eq ▸ NP_subset_EXP (hSub hB₂)
  obtain ⟨d, hd⟩ := mem_EXP_iff.mp hL_EXP
  refine setOf_timeDiagonal_notMem_DTIME (f := fun n => 2 ^ n ^ d) (J := J) (fun C => ?_) hd
  have hpoly : PolynomiallyBounded fun n => n ^ d + n + 1 := by fun_prop
  filter_upwards [hpoly.eventually_lt_two_pow, eventually_ge_atTop (C + 1)] with n hn hC
  have h₁ : 2 * C ≤ 2 ^ (n + 1) := by
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    rw [pow_succ']
    omega
  have h₂ : 1 ≤ 2 ^ n ^ d := Nat.one_le_two_pow
  calc C * 2 ^ n ^ d + C
      ≤ 2 * C * 2 ^ n ^ d := by nlinarith
    _ ≤ 2 ^ (n + 1) * 2 ^ n ^ d := Nat.mul_le_mul_right _ h₁
    _ = 2 ^ (n ^ d + n + 1) := by rw [← Nat.pow_add]; ring_nf
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) hn.le

/-- **`NP` is strictly contained in `NEXP`** on bitstrings: a special case of the nondeterministic
time hierarchy theorem [Arora and Barak, Theorem 3.2][AroraBarak09], proved via
`not_NEXP_subset_NP`. -/
theorem NP_ssubset_NEXP : NP encBits ⊂ NEXP encBits :=
  NP_subset_NEXP.ssubset_of_ne fun h => not_NEXP_subset_NP h.ge

end Cslib.Complexity
