/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.Rademacher.Basic
public import Complexity.MachineLearning.PACLearning.GrowthFunction

/-!
# Rademacher complexity of binary classes

A binary concept class `C` becomes a class of `{-1, +1}`-valued functions `signClass C` through
`Cslib.BitString.signVal`. On a sample `S` of `m` points its functions realize at most
`growthFunction C m` restriction patterns, so Massart's lemma bounds its empirical Rademacher
complexity by `√(2 log Π_C(m) / m)` [MohriRostamizadehTalwalkar2018, Corollary 3.8]. Sauer's lemma
(`Cslib.MachineLearning.PACLearning.growthFunction_le_exp_one_mul_div_pow`) turns this into
`√(2 d log (e m / d) / m)` for a class whose shattered sets have at most `d ≤ m` points
[MohriRostamizadehTalwalkar2018, Corollary 3.18 and the proof of Corollary 3.19], and into
`√(2 d log (m + 1) / m)` for every `m`.

## Main definitions

* `Cslib.MachineLearning.signClass`: the `{-1, +1}`-valued functions `signVal ∘ c` for `c ∈ C`.

## Main results

* `Cslib.MachineLearning.mem_signClass`, `Cslib.MachineLearning.signClass_singleton`:
  membership, and the sign class of a single concept.
* `Cslib.MachineLearning.empiricalRademacherComplexity_signClass_le`,
  `Cslib.MachineLearning.rademacherComplexity_signClass_le`: the growth-function bound.
* `Cslib.MachineLearning.empiricalRademacherComplexity_signClass_le_vc`,
  `Cslib.MachineLearning.rademacherComplexity_signClass_le_vc`: the bound
  `√(2 d log (e m / d) / m)` for `d ≤ m`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_signClass_le_add_one`: the bound
  `√(2 d log (m + 1) / m)`.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Corollaries 3.8 and 3.18
-/

public section

namespace Cslib.MachineLearning

open Cslib.BitString Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- The `{-1, +1}`-valued functions `x ↦ signVal (c x)` of a binary concept class `C`. -/
def signClass (C : ConceptClass α Bool) : Set (α → ℝ) :=
  (fun c x => signVal (c x)) '' C

theorem mem_signClass {C : ConceptClass α Bool} {f : α → ℝ} :
    f ∈ signClass C ↔ ∃ c ∈ C, (fun x => signVal (c x)) = f := by
  rw [signClass, Set.mem_image]

/-- A single concept gives a single sign function. -/
theorem signClass_singleton (c : α → Bool) :
    signClass ({c} : ConceptClass α Bool) = {fun x => signVal (c x)} := by
  rw [signClass, Set.image_singleton]

/-- Functions of `signClass C` take values in `[-1, 1]`. -/
theorem abs_le_one_of_mem_signClass {C : ConceptClass α Bool} {f : α → ℝ}
    (hf : f ∈ signClass C) (x : α) : |f x| ≤ 1 := by
  obtain ⟨c, -, rfl⟩ := mem_signClass.1 hf
  exact (abs_signVal _).le

/-- The restriction patterns of `signClass C` to a sample are the sign images of the labelings
realized by `C`. -/
private theorem image_signClass_subset (C : ConceptClass α Bool) {m : ℕ} (S : Fin m → α) :
    (fun f : α → ℝ => fun i => f (S i)) '' signClass C ⊆
      (fun v : Fin m → Bool => fun i => signVal (v i)) '' restriction C S := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, hc, rfl⟩ := mem_signClass.1 hf
  exact ⟨fun i => c (S i), mem_restriction.2 ⟨c, hc, fun _ => rfl⟩, rfl⟩

/-- `log n ≤ log x` for a natural number `n ≤ x`, including `n = 0`, when `x ≥ 1`. -/
private theorem log_natCast_le_log {n : ℕ} {x : ℝ} (hnx : (n : ℝ) ≤ x) (hx : 1 ≤ x) :
    Real.log n ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg hx
  · exact Real.log_le_log (Nat.cast_pos.2 hn) hnx

/-- **The growth-function bound** [MohriRostamizadehTalwalkar2018, Corollary 3.8]: the empirical
Rademacher complexity of `signClass C` on `m` points is at most `√(2 log Π_C(m) / m)`. -/
theorem empiricalRademacherComplexity_signClass_le (C : ConceptClass α Bool) {m : ℕ}
    (S : Fin m → α) :
    empiricalRademacherComplexity (signClass C) S ≤
      √(2 * Real.log (growthFunction C m) / m) := by
  rcases (signClass C).eq_empty_or_nonempty with hC | hC
  · rw [hC, empiricalRademacherComplexity_empty]
    positivity
  have hfin : ((fun f : α → ℝ => fun i => f (S i)) '' signClass C).Finite :=
    ((Set.toFinite _).image _).subset (image_signClass_subset C S)
  refine (empiricalRademacherComplexity_le_of_finite zero_le_one
    (fun f hf => abs_le_one_of_mem_signClass hf) S hfin).trans_eq (one_mul _) |>.trans ?_
  have hpos : 0 < ((fun f : α → ℝ => fun i => f (S i)) '' signClass C).ncard :=
    (Set.ncard_pos hfin).2 (hC.image _)
  have hle : ((fun f : α → ℝ => fun i => f (S i)) '' signClass C).ncard ≤ growthFunction C m :=
    (Set.ncard_le_ncard (image_signClass_subset C S) ((Set.toFinite _).image _)).trans
      ((Set.ncard_image_le (Set.toFinite _)).trans (ncard_restriction_le_growthFunction C S))
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m))
  gcongr

/-- **The VC bound** [MohriRostamizadehTalwalkar2018, Corollaries 3.8 and 3.18]: if every finite
set shattered by `C` has at most `d ≤ m` points, the empirical Rademacher complexity of
`signClass C` on `m` points is at most `√(2 d log (e m / d) / m)`. -/
theorem empiricalRademacherComplexity_signClass_le_vc {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (hdm : d ≤ m)
    (S : Fin m → α) :
    empiricalRademacherComplexity (signClass C) S ≤
      √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) := by
  refine (empiricalRademacherComplexity_signClass_le C S).trans ?_
  have hx : 1 ≤ (Real.exp 1 * m / d) ^ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    refine one_le_pow₀ ?_
    rw [le_div_iff₀ (Nat.cast_pos.2 hd), one_mul]
    calc (d : ℝ) ≤ m := by exact_mod_cast hdm
      _ ≤ Real.exp 1 * m := le_mul_of_one_le_left (Nat.cast_nonneg m)
          (by linarith [Real.add_one_le_exp (1 : ℝ)])
  rw [← Real.log_pow]
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m))
  exact mul_le_mul_of_nonneg_left
    (log_natCast_le_log (growthFunction_le_exp_one_mul_div_pow hC hdm) hx) zero_le_two

/-- **The polynomial VC bound**: if every finite set shattered by `C` has at most `d` points, the
empirical Rademacher complexity of `signClass C` on `m` points is at most
`√(2 d log (m + 1) / m)`. -/
theorem empiricalRademacherComplexity_signClass_le_add_one {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (S : Fin m → α) :
    empiricalRademacherComplexity (signClass C) S ≤ √(2 * (d * Real.log (m + 1)) / m) := by
  refine (empiricalRademacherComplexity_signClass_le C S).trans ?_
  have hle : (growthFunction C m : ℝ) ≤ ((m : ℝ) + 1) ^ d := by
    exact_mod_cast growthFunction_le_add_one_pow hC m
  have hx : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ d :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [← Real.log_pow]
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m))
  exact mul_le_mul_of_nonneg_left (log_natCast_le_log hle hx) zero_le_two

variable [Fintype α]

/-- **The growth-function bound** for the Rademacher complexity
[MohriRostamizadehTalwalkar2018, Corollary 3.8]. -/
theorem rademacherComplexity_signClass_le (D : PMF α) (C : ConceptClass α Bool) (m : ℕ) :
    rademacherComplexity D (signClass C) m ≤ √(2 * Real.log (growthFunction C m) / m) :=
  rademacherComplexity_le D fun S => empiricalRademacherComplexity_signClass_le C S

/-- **The VC bound** for the Rademacher complexity [MohriRostamizadehTalwalkar2018, Corollaries
3.8 and 3.18]. -/
theorem rademacherComplexity_signClass_le_vc (D : PMF α) {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (hdm : d ≤ m) :
    rademacherComplexity D (signClass C) m ≤ √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) :=
  rademacherComplexity_le D fun S => empiricalRademacherComplexity_signClass_le_vc hC hdm S

end Cslib.MachineLearning
