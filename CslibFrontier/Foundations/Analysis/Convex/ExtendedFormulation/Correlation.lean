/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Nondeterministic.ExtensionComplexity
public import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Reduction
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential extension-complexity lower bound for the correlation polytope

The **correlation polytope** `corrPolytope K α` (`CORR(n)` for `|α| = n`) is the convex hull of
all rank-1 binary matrices `b bᵀ : (α × α) → K` indexed by subsets `b : Finset α`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]; [KaibelWeltge2015, Section 1].

Using the valid inequalities `(2 diag(a) - a aᵀ) ⬝ᵥ x ≤ 1` (`corrValidMatrix`), whose slack at
vertex `corrVertex K b` equals `(1 - |a ∩ b|)²` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 6],
[KaibelWeltge2015, Lemma 1], the support of the resulting valid-inequality slack matrix is the
non-unique-intersection predicate `nonUniqueInter α`. Combining Yannakakis's rectangle covering
bound (`coverNumberFun_ne_zero_le_nonnegRank`) with Kaibel–Weltge's `(3 / 2) ^ n` bound for
unique disjointness (`three_pow_le_two_pow_mul_coverNumberFun_nonUniqueInter`), we obtain
`xc(CORR(n)) ≥ (3 / 2) ^ n` whenever `α` is nonempty [KaibelWeltge2015, Theorem 1]. When `α` is
empty, `CORR(0)` is a singleton `{0}` so `xc = 0`.

## Main definitions

* `corrVertex`: the rank-1 `0/1` matrix `b bᵀ` associated with `b : Finset α`.
* `corrPolytope`: `CORR(α) = conv {corrVertex K b | b : Finset α}`.
* `corrValidVec`, `corrValidMatrix`: the valid inequality `(2 diag(a) - a aᵀ) ⬝ᵥ x ≤ 1`.

## Main results

* `corrValidMatrix_slackMatrix_apply`: the slack of `corrValidVec K a` at `corrVertex K b` is
  `((|a ∩ b| : K) - 1) ^ 2`.
* `corrPolytope_nontrivial`: `corrPolytope K α` is nontrivial whenever `α` is nonempty.
* `three_pow_le_two_pow_mul_extensionComplexity_corrPolytope`:
  `(3 : ℕ) ^ |α| ≤ 2 ^ |α| * extensionComplexity (corrPolytope K α)` for `[Nonempty α]`.
* `HasExtendedFormulation.three_div_two_pow_le_of_corrPolytope`:
  `(3 / 2 : F) ^ |α| ≤ r` whenever `HasExtendedFormulation (corrPolytope K α) r`.

## References

* [KaibelWeltge2015], Sections 1–2 (Lemma 1 and Theorem 1).
* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.2 (Lemma 6 and Theorem 7).
-/

public section

open Matrix
open Cslib.Communication.Nondeterministic

section Defs

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- The vertex `b bᵀ` of the correlation polytope associated with `b : Finset α`
[KaibelWeltge2015, Section 2]; [FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]. -/
@[expose] def corrVertex {α : Type*} [DecidableEq α] (b : Finset α) : (α × α) → K :=
  fun p => if p.1 ∈ b ∧ p.2 ∈ b then 1 else 0

/-- The **correlation polytope** `CORR(α) = conv {b bᵀ | b ⊆ α}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.2]. -/
@[expose] def corrPolytope (α : Type*) [DecidableEq α] : Set ((α × α) → K) :=
  convexHull K (Set.range (corrVertex K))

end Defs

section Slack

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The valid inequality vector `2 diag(a) - a aᵀ` on `(α × α) → K`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 6]; [KaibelWeltge2015, Lemma 1]. -/
def corrValidVec (a : Finset α) : (α × α) → K :=
  fun p => if p.1 ∈ a ∧ p.2 ∈ a then (if p.1 = p.2 then 1 else -1) else 0

/-- Matrix of Kaibel–Weltge / FMPTW valid inequalities `⟨2 diag(a) - a aᵀ, x⟩ ≤ 1` indexed by
`a : Finset α`. -/
def corrValidMatrix (α : Type*) [DecidableEq α] : Matrix (Finset α) (α × α) K :=
  Matrix.of (corrValidVec K)

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype α] in
@[simp] theorem corrVertex_apply (b : Finset α) (i j : α) :
    corrVertex K b (i, j) = if i ∈ b ∧ j ∈ b then 1 else 0 := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Evaluating `2 diag(a) - a aᵀ` on `corrVertex K b` gives `2 |a ∩ b| - |a ∩ b| ^ 2`. -/
theorem corrValidVec_dotProduct_corrVertex (a b : Finset α) :
    corrValidVec K a ⬝ᵥ corrVertex K b =
      2 * ((a ∩ b).card : K) - ((a ∩ b).card : K) ^ 2 := by
  have hterm : ∀ i j : α,
      corrValidVec K a (i, j) * corrVertex K b (i, j) =
        if i ∈ a ∩ b ∧ j ∈ a ∩ b then (if i = j then (2 : K) else 0) - 1 else 0 := fun i j => by
    dsimp only [corrValidVec, corrVertex_apply]
    by_cases ha : i ∈ a ∧ j ∈ a <;> by_cases hb : i ∈ b ∧ j ∈ b
    · have hab : i ∈ a ∩ b ∧ j ∈ a ∩ b :=
        ⟨Finset.mem_inter.2 ⟨ha.1, hb.1⟩, Finset.mem_inter.2 ⟨ha.2, hb.2⟩⟩
      rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left hab, mul_one]
      split_ifs <;> norm_num
    · have nhab : ¬ (i ∈ a ∩ b ∧ j ∈ a ∩ b) := fun h =>
        hb ⟨(Finset.mem_inter.1 h.1).2, (Finset.mem_inter.1 h.2).2⟩
      rw [ite_eq_right hb, ite_eq_right nhab, mul_zero]
    · have nhab : ¬ (i ∈ a ∩ b ∧ j ∈ a ∩ b) := fun h =>
        ha ⟨(Finset.mem_inter.1 h.1).1, (Finset.mem_inter.1 h.2).1⟩
      rw [ite_eq_right ha, ite_eq_right nhab, zero_mul]
    · have nhab : ¬ (i ∈ a ∩ b ∧ j ∈ a ∩ b) := fun h =>
        ha ⟨(Finset.mem_inter.1 h.1).1, (Finset.mem_inter.1 h.2).1⟩
      rw [ite_eq_right hb, ite_eq_right nhab, mul_zero]
  calc
    corrValidVec K a ⬝ᵥ corrVertex K b
        = ∑ i : α, ∑ j : α, corrValidVec K a (i, j) * corrVertex K b (i, j) := by
      simp only [dotProduct, Fintype.sum_prod_type]
    _ = ∑ i ∈ a ∩ b, ∑ j ∈ a ∩ b, ((if i = j then (2 : K) else 0) - 1) := by
      simp only [hterm]
      rw [← Finset.sum_subset (Finset.subset_univ (a ∩ b))]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_subset (Finset.subset_univ (a ∩ b))]
        · refine Finset.sum_congr rfl fun j hj => ?_
          simp only [hi, hj, and_self, ↓reduceIte]
        · intro j _ hj
          simp only [hj, and_false, ↓reduceIte]
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [hi, false_and, ↓reduceIte]
    _ = (∑ i ∈ a ∩ b, ∑ j ∈ a ∩ b, (if i = j then (2 : K) else 0)) -
          (∑ _i ∈ a ∩ b, ∑ _j ∈ a ∩ b, (1 : K)) := by
      simp only [Finset.sum_sub_distrib]
    _ = 2 * ((a ∩ b).card : K) - ((a ∩ b).card : K) ^ 2 := by
      congr 1
      · have hdiag : ∀ i ∈ a ∩ b, (∑ j ∈ a ∩ b, if i = j then (2 : K) else 0) = 2 :=
          fun i hi => by rw [Finset.sum_ite_eq (a ∩ b) i (fun _ => (2 : K)), ite_eq_left hi]
        rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_comm]
      · simp only [Finset.sum_const, nsmul_eq_mul, mul_one, sq]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The slack of `corrValidVec K a` at vertex `corrVertex K b` is `(|a ∩ b| - 1) ^ 2`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 6]; [KaibelWeltge2015, Lemma 1]. -/
theorem corrValidMatrix_slackMatrix_apply (a b : Finset α) :
    (corrValidMatrix K α).slackMatrix (fun _ => 1) (corrVertex K) a b =
      (((a ∩ b).card : K) - 1) ^ 2 := by
  rw [Matrix.slackMatrix_apply]
  change 1 - corrValidVec K a ⬝ᵥ corrVertex K b = _
  rw [corrValidVec_dotProduct_corrVertex]
  ring

/-- The inequality `corrValidMatrix K α *ᵥ x ≤ 1` is valid on `corrPolytope K α`. -/
theorem corrValidMatrix_mulVec_le {x : (α × α) → K} (hx : x ∈ corrPolytope K α) :
    corrValidMatrix K α *ᵥ x ≤ fun _ => 1 := fun a => by
  dsimp only [mulVec]
  change corrValidVec K a ⬝ᵥ x ≤ 1
  refine dotProduct_le_of_mem_convexHull (fun b => ?_) hx
  rw [corrValidVec_dotProduct_corrVertex]
  have hsq : (0 : K) ≤ (((a ∩ b).card : K) - 1) ^ 2 := sq_nonneg _
  linarith

omit [Fintype α] in
/-- For nonempty `α`, `corrPolytope K α` is nontrivial (`dim ≥ 1`). -/
theorem corrPolytope_nontrivial [Nonempty α] : (corrPolytope K α).Nontrivial := by
  refine nontrivial_convexHull_range_iff.2 ⟨∅, {Classical.arbitrary α}, fun h => ?_⟩
  have hval := congrFun h (Classical.arbitrary α, Classical.arbitrary α)
  simp only [corrVertex_apply, Finset.notMem_empty, false_and, ↓reduceIte,
    Finset.mem_singleton] at hval
  exact zero_ne_one hval

end Slack

section LowerBound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every extended formulation of `corrPolytope K α` (`|α| ≥ 1`) satisfies
`3 ^ |α| ≤ 2 ^ |α| * xc (corrPolytope K α)` in `ℕ∞`
[KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_corrPolytope [Nonempty α] :
    ((3 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      (2 ^ Fintype.card α : ℕ∞) * extensionComplexity (corrPolytope K α) := by
  have hsupp :
      (fun a b : Finset α =>
        decide ((corrValidMatrix K α).slackMatrix (fun _ => 1) (corrVertex K) a b ≠ 0)) =
      nonUniqueInter α := by
    ext a b
    simp only [corrValidMatrix_slackMatrix_apply, ne_eq, sq_eq_zero_iff, sub_eq_zero,
      Nat.cast_eq_one, nonUniqueInter]
  have hcov : coverNumberFun true (nonUniqueInter α) Set.univ Set.univ ≤
      ((corrValidMatrix K α).slackMatrix (fun _ => 1) (corrVertex K)).nonnegRank := by
    rw [← hsupp]
    exact coverNumberFun_ne_zero_le_nonnegRank _
  have hnn : ((corrValidMatrix K α).slackMatrix (fun _ => 1) (corrVertex K)).nonnegRank ≤
      extensionComplexity (corrPolytope K α) :=
    nonnegRank_slackMatrix_le_extensionComplexity_of_forall_le
      (fun _ hx => corrValidMatrix_mulVec_le K hx) rfl (corrPolytope_nontrivial K)
  exact three_pow_le_two_pow_mul_coverNumberFun_nonUniqueInter.trans
    (mul_le_mul_right (hcov.trans hnn) _)

/-- Every extended formulation of `corrPolytope K α` (`|α| ≥ 1`) has at least
`⌈(3 / 2) ^ |α|⌉` inequalities in `ℕ∞` [KaibelWeltge2015, Theorem 1]. -/
theorem ceil_three_div_two_pow_le_extensionComplexity_corrPolytope [Nonempty α] :
    (((3 ^ Fintype.card α + 2 ^ Fintype.card α - 1) / 2 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      extensionComplexity (corrPolytope K α) :=
  ceil_three_div_two_pow_le_of_mul_le_extensionComplexity
    three_pow_le_two_pow_mul_extensionComplexity_corrPolytope

/-- Field-valued Kaibel–Weltge lower bound: any extended formulation of `corrPolytope K α`
(`|α| ≥ 1`) with `r` inequalities satisfies `(3 / 2 : F) ^ |α| ≤ r`
[KaibelWeltge2015, Theorem 1]. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_corrPolytope [Nonempty α]
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {r : ℕ} (hr : HasExtendedFormulation (corrPolytope K α) r) :
    (3 / 2 : F) ^ Fintype.card α ≤ r :=
  hr.three_div_two_pow_le_of_mul_le three_pow_le_two_pow_mul_extensionComplexity_corrPolytope

end LowerBound
