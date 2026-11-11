/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
public import CslibFrontier.Probability.Extractor.TwoSource
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.PMF.Map
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Raz's Extractor

Raz's two-source extractor for one source with min-entropy > n/2 and a second source with
logarithmic min-entropy.

## Main definitions

* `Cslib.Probability.razExtractor`: The Raz extractor function.
* `Cslib.Probability.IsRazMatrixFamily`: The rank condition on the matrix family.

## Main theorem statement

* `Cslib.Probability.RazExtractorTheorem`: The correctness statement of Raz's extractor,
  formulated as a `Prop` to avoid `sorry` while the proof is being developed.
-/

public section

namespace Cslib.Probability

open Finset Cslib.Probability Cslib.Probability.PMF Matrix Fintype Classical
attribute [local instance] Classical.propDecidable

variable {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι]

/-- The condition on the matrix family for Raz's extractor: any non-trivial XOR sum
of up to `2 * t` matrices has rank at least `(1 - δ) * n`. -/
def IsRazMatrixFamily (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) : Prop :=
  ∀ s : Finset Y, 0 < s.card → s.card ≤ 2 * t →
    (1 - δ) * Fintype.card ι ≤ (∑ y ∈ s, M y).rank

/-- The Raz extractor function. -/
def razExtractor (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2))
    (y : Y) : ZMod 2 :=
  x.1 ⬝ᵥ (M y *ᵥ x.2)

/-- The statement that Raz's extractor is a two-source extractor.
Defined as a `Prop` to avoid `sorry` before the proof is complete. -/
theorem dist_bind_map_eq_abs_bias (p : PMF ((ι → ZMod 2) × (ι → ZMod 2))) (q : PMF Y)
    (M : Y → Matrix ι ι (ZMod 2)) :
    dist (p.bind (fun x => q.map (fun y => decide (razExtractor M x y = 1))))
      (PMF.uniformOfFintype Bool) =
    |∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val| / 2 := by
  rw [dist_uniformOfFintype_bool]
  have h1 : (p.bind (fun x => q.map (fun y => decide (razExtractor M x y = 1))) true).toReal =
      ∑ x, (p x).toReal * ∑ y, if decide (razExtractor M x y = 1) = true
          then (q y).toReal else 0 := by
    rw [PMF.bind_apply_toReal]
    refine sum_congr rfl fun x _ => ?_
    rw [PMF.map_apply_toReal]
    simp_rw [eq_comm (a := true)]
  rw [h1]
  have hB : ∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val =
      1 - 2 * ∑ x, (p x).toReal * ∑ y, if decide (razExtractor M x y = 1) = true
        then (q y).toReal else 0 := by
    calc ∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val
      _ = ∑ x, (p x).toReal * ∑ y,
          ((q y).toReal - 2 *
            (if decide (razExtractor M x y = 1) = true then (q y).toReal else 0)) := by
        refine sum_congr rfl fun x _ => ?_
        congr 1
        refine sum_congr rfl fun y _ => ?_
        by_cases h : razExtractor M x y = 1
        · have hv : (razExtractor M x y).val = 1 := by rw [h]; rfl
          rw [hv]
          have hd : decide (razExtractor M x y = 1) = true := decide_eq_true h
          simp [hd]
          ring
        · have hv : (razExtractor M x y).val = 0 := by
            revert h
            generalize razExtractor M x y = z
            intro hz
            revert hz
            generalize eq : z.val = v
            intro hz
            have h_bound := ZMod.val_lt z
            rw [eq] at h_bound
            have h_cases : v = 0 ∨ v = 1 := by omega
            rcases h_cases with rfl | rfl
            · rfl
            · exfalso
              apply hz
              apply ZMod.val_injective
              rw [eq]
              rfl
          rw [hv]
          have hd : decide (razExtractor M x y = 1) = false := decide_eq_false h
          simp [hd]
      _ = ∑ x, ( (p x).toReal * (∑ y, (q y).toReal) - (2 * (p x).toReal) *
          (∑ y, if decide (razExtractor M x y = 1) = true then (q y).toReal else 0) ) := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_sub_distrib, mul_sub, ← mul_sum]
        congr 1
        ring
      _ = (∑ x, (p x).toReal * (∑ y, (q y).toReal)) - ∑ x, (2 * (p x).toReal) *
          (∑ y, if decide (razExtractor M x y = 1) = true then (q y).toReal else 0) := by
        rw [sum_sub_distrib]
      _ = (∑ x, (p x).toReal * (∑ y, (q y).toReal)) - 2 * ∑ x, (p x).toReal *
          (∑ y, if decide (razExtractor M x y = 1) = true then (q y).toReal else 0) := by
        congr 1
        have hs : ∑ x, (2 * (p x).toReal) *
            (∑ y, if decide (razExtractor M x y = 1) = true then (q y).toReal else 0) =
            ∑ x, 2 * ((p x).toReal *
            (∑ y, if decide (razExtractor M x y = 1) = true then (q y).toReal else 0)) := by
          refine sum_congr rfl fun x _ => ?_
          ring
        rw [hs, ← mul_sum]
      _ = 1 - 2 * ∑ x, (p x).toReal * ∑ y, if decide (razExtractor M x y = 1) = true
          then (q y).toReal else 0 := by
        have hq : ∀ x, (p x).toReal * ∑ y, (q y).toReal = (p x).toReal * 1 := by
          intro x
          congr 1
          exact sum_toReal q
        simp_rw [hq, mul_one, sum_toReal p]
  have hS : (∑ x, (p x).toReal * ∑ y, if decide (razExtractor M x y = 1) = true
      then (q y).toReal else 0) - 1 / 2 =
      -(∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) / 2 := by
    linarith
  rw [hS, abs_div, abs_neg]
  congr 1
  norm_num

def HasEvenFrequencies {α Y : Type*} [Fintype α] [DecidableEq Y] (f : α → Y) : Prop :=
  ∀ v : Y, Even (Finset.univ.filter (fun i => f i = v)).card

def reconstruct {α Y : Type*} [DecidableEq α] (a0 j : α) (y : Y) (g : {x : α // x ≠ a0 ∧ x ≠ j} → Y) : α → Y :=
  fun x =>
    if h1 : x = a0 then y
    else if h2 : x = j then y
    else g ⟨x, ⟨h1, h2⟩⟩

lemma card_subtype_eq {α Y : Type*} [Fintype α] [DecidableEq α] [DecidableEq Y] (f : α → Y) (v : Y) (a0 j : α) (hj1 : j ≠ a0) (hv_a0 : f a0 = v) (hv_j : f j = v) :
    (Finset.univ.filter (fun i : α => f i = v)).card =
    (Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).card + 2 := by
  have h_disj : Disjoint ((Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).image (fun x => x.val)) {a0, j} := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_image, mem_filter, mem_univ, true_and] at ha
    simp only [mem_insert, mem_singleton] at hb
    rcases ha with ⟨y, _, rfl⟩
    rcases hb with rfl | rfl
    · exact y.2.1
    · exact y.2.2
  have h_union : (Finset.univ.filter (fun i : α => f i = v)) =
      ((Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).image (fun x => x.val)) ∪ {a0, j} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases h1 : x = a0
      · right; left; exact h1
      · by_cases h2 : x = j
        · right; right; exact h2
        · left; exact ⟨⟨x, ⟨h1, h2⟩⟩, hx, rfl⟩
    · rintro (⟨y, hy, rfl⟩ | rfl | rfl)
      · exact hy
      · exact hv_a0
      · exact hv_j
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [← h_union] at h_card
  rw [h_card]
  have h_card_img : ((Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).image (fun x => x.val)).card =
      (Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact Subtype.ext hxy
  rw [h_card_img]
  rw [Finset.card_pair hj1.symm]

lemma card_subtype_eq_not {α Y : Type*} [Fintype α] [DecidableEq α] [DecidableEq Y] (f : α → Y) (v : Y) (a0 j : α) (hv_a0 : f a0 ≠ v) (hv_j : f j ≠ v) :
    (Finset.univ.filter (fun i : α => f i = v)).card =
    (Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).card := by
  have h_eq : (Finset.univ.filter (fun i : α => f i = v)) =
      ((Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).image (fun x => x.val)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      have h1 : x ≠ a0 := by rintro rfl; exact hv_a0 hx
      have h2 : x ≠ j := by rintro rfl; exact hv_j hx
      exact ⟨⟨x, ⟨h1, h2⟩⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [h_eq]
  apply Finset.card_image_of_injective
  intro x y hxy
  exact Subtype.ext hxy

lemma reconstruct_image_subset {α Y : Type*} [Fintype α] [Fintype Y] [DecidableEq α] [DecidableEq Y] (a0 : α) :
    (Finset.univ.filter (fun f : α → Y => HasEvenFrequencies f)) ⊆
    (Finset.univ.filter (fun j => j ≠ a0)).biUnion (fun j =>
      (Finset.univ : Finset Y).biUnion (fun y =>
        (Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).image
          (reconstruct a0 j y))) := by
  intro f hf
  rw [mem_filter] at hf
  have h1 : a0 ∈ Finset.univ.filter (fun i => f i = f a0) := by simp
  have h3 : (Finset.univ.filter (fun i => f i = f a0)).card ≥ 2 := by
    have even_card := hf.2 (f a0)
    have pos_card : (Finset.univ.filter (fun i => f i = f a0)).card > 0 := Finset.card_pos.mpr ⟨a0, h1⟩
    have hdvd : 2 ∣ (Finset.univ.filter (fun i => f i = f a0)).card := even_iff_two_dvd.mp even_card
    omega
  have exists_j : ∃ j : α, j ≠ a0 ∧ f j = f a0 := by
    by_contra h_contra
    simp only [not_exists, not_and] at h_contra
    have : Finset.univ.filter (fun i => f i = f a0) = {a0} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hx; by_contra hneq; exact (h_contra x hneq) hx
      · rintro rfl; rfl
    rw [this, Finset.card_singleton] at h3
    revert h3; omega
  rcases exists_j with ⟨j, hj1, hj2⟩
  rw [Finset.mem_biUnion]
  refine ⟨j, ?_, ?_⟩
  · rw [mem_filter]; exact ⟨mem_univ _, hj1⟩
  · rw [Finset.mem_biUnion]
    refine ⟨f a0, mem_univ _, ?_⟩
    rw [Finset.mem_image]
    refine ⟨fun x => f x.val, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      intro v
      have h_even := hf.2 v
      by_cases hv : f a0 = v
      · have h_eq := card_subtype_eq f v a0 j hj1 hv (hj2.trans hv)
        have hdvd : 2 ∣ (Finset.univ.filter (fun i => f i = v)).card := even_iff_two_dvd.mp h_even
        rw [h_eq] at hdvd
        have hdvd2 : 2 ∣ (Finset.univ.filter (fun i : {x : α // x ≠ a0 ∧ x ≠ j} => f i.val = v)).card := by omega
        exact even_iff_two_dvd.mpr hdvd2
      · have h_eq := card_subtype_eq_not f v a0 j hv (by rw [hj2]; exact hv)
        rw [h_eq] at h_even
        exact h_even
    · ext x
      unfold reconstruct
      by_cases h_a0 : x = a0
      · simp [h_a0]
      · by_cases h_j : x = j
        · have hj2_symm : f a0 = f j := hj2.symm
          simp [h_j, hj2_symm]
        · simp [h_a0, h_j]

lemma card_hasEvenFrequencies_le (t : ℕ) : ∀ {α Y : Type*} [Fintype α] [Fintype Y] [DecidableEq α] [DecidableEq Y]
    (h_card : Fintype.card α = 2 * t),
    (Finset.univ.filter (fun f : α → Y => HasEvenFrequencies f)).card ≤ (2 * t) ^ t * (Fintype.card Y) ^ t := by
  induction t with
  | zero =>
    intro α Y _ _ _ _ h_card
    have h_emp : Fintype.card (α → Y) = 1 := by
      rw [Fintype.card_fun, h_card, pow_zero]
    calc (Finset.univ.filter (fun f : α → Y => HasEvenFrequencies f)).card
      _ ≤ (Finset.univ : Finset (α → Y)).card := Finset.card_filter_le _ _
      _ = Fintype.card (α → Y) := Finset.card_univ
      _ = 1 := h_emp
      _ = (2 * 0) ^ 0 * Fintype.card Y ^ 0 := by norm_num
  | succ t ih =>
    intro α Y hFα hFY hDα hDY h_card
    have h_nonempty : Nonempty α := by
      by_contra h
      have h_empty : IsEmpty α := ⟨fun x => h ⟨x⟩⟩
      have h_card0 : Fintype.card α = 0 := Fintype.card_of_isEmpty (α := α)
      omega
    have a0 : α := h_nonempty.some
    have h_sub := reconstruct_image_subset (Y := Y) a0
    calc (Finset.univ.filter (fun f : α → Y => HasEvenFrequencies f)).card
      _ ≤ ((Finset.univ.filter (fun j => j ≠ a0)).biUnion (fun j =>
            (Finset.univ : Finset Y).biUnion (fun y =>
              (Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).image
                (reconstruct a0 j y)))).card := Finset.card_le_card h_sub
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ a0), ((Finset.univ : Finset Y).biUnion (fun y =>
              (Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).image
                (reconstruct a0 j y))).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ a0), ∑ y ∈ (Finset.univ : Finset Y),
              ((Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).image
                (reconstruct a0 j y)).card := by
        apply sum_le_sum
        intro j _
        exact Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ a0), ∑ y ∈ (Finset.univ : Finset Y),
              (Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).card := by
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro y hy
        have h_img_le : ((Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).image (reconstruct a0 j y)).card ≤
              (Finset.univ.filter (fun g : {x : α // x ≠ a0 ∧ x ≠ j} → Y => HasEvenFrequencies g)).card := Finset.card_image_le
        exact h_img_le
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≠ a0), ∑ y ∈ (Finset.univ : Finset Y),
              (2 * t) ^ t * (Fintype.card Y) ^ t := by
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro y hy
        have h_neq : j ≠ a0 := by
          rw [mem_filter] at hj
          exact hj.2
        have h_sub_card : Fintype.card {x : α // x ≠ a0 ∧ x ≠ j} = 2 * t := by
          rw [Fintype.card_subtype]
          have h_eq : ((Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)).card = 2 := by
            have h_eq2 : ((Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)) = {a0, j} := by
              ext x; simp <;> tauto
            rw [h_eq2, Finset.card_pair h_neq.symm]
          have h_sub_union : (Finset.univ : Finset α) = ((Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)) ∪ ((Finset.univ : Finset α).filter (fun x : α => ¬(x = a0 ∨ x = j))) := by
            ext x; simp <;> tauto
          have h_disj : Disjoint ((Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)) ((Finset.univ : Finset α).filter (fun x : α => ¬(x = a0 ∨ x = j))) := by
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            simp only [mem_filter, mem_univ, true_and] at ha hb
            rintro rfl; exact hb ha
          have h_card_univ_eq : (Finset.univ : Finset α).card = ((Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)).card + ((Finset.univ : Finset α).filter (fun x : α => ¬(x = a0 ∨ x = j))).card := by
            have h_union' := Finset.card_union_of_disjoint (s := (Finset.univ : Finset α).filter (fun x : α => x = a0 ∨ x = j)) (t := (Finset.univ : Finset α).filter (fun x : α => ¬(x = a0 ∨ x = j))) h_disj
            rw [← h_union', ← h_sub_union]
          rw [Finset.card_univ] at h_card_univ_eq
          have h_equiv : ((Finset.univ : Finset α).filter (fun x : α => ¬(x = a0 ∨ x = j))) = ((Finset.univ : Finset α).filter (fun x : α => x ≠ a0 ∧ x ≠ j)) := by
            ext x; simp <;> tauto
          rw [h_equiv] at h_card_univ_eq
          omega
        exact @ih {x : α // x ≠ a0 ∧ x ≠ j} Y (Subtype.fintype _) hFY _ hDY h_sub_card
      _ = (Fintype.card α - 1) * Fintype.card Y * ((2 * t) ^ t * Fintype.card Y ^ t) := by
        simp only [sum_const, nsmul_eq_mul, card_univ]
        have h_card_j : ((Finset.univ : Finset α).filter (fun j : α => j ≠ a0)).card = Fintype.card α - 1 := by
          have h_univ : (Finset.univ : Finset α) = ((Finset.univ : Finset α).filter (fun j : α => j = a0)) ∪ ((Finset.univ : Finset α).filter (fun j : α => j ≠ a0)) := by
            ext x; simp <;> tauto
          have h_disj : Disjoint ((Finset.univ : Finset α).filter (fun j : α => j = a0)) ((Finset.univ : Finset α).filter (fun j : α => j ≠ a0)) := by
            rw [Finset.disjoint_iff_ne]; intro a ha b hb; simp only [mem_filter, mem_univ, true_and] at ha hb; rintro rfl; exact hb ha
          have h_card_univ_eq : (Finset.univ : Finset α).card = ((Finset.univ : Finset α).filter (fun j : α => j = a0)).card + ((Finset.univ : Finset α).filter (fun j : α => j ≠ a0)).card := by
            have h_union' := Finset.card_union_of_disjoint (s := (Finset.univ : Finset α).filter (fun j : α => j = a0)) (t := (Finset.univ : Finset α).filter (fun j : α => j ≠ a0)) h_disj
            rw [← h_union', ← h_univ]
          have h_sing : ((Finset.univ : Finset α).filter (fun j : α => j = a0)) = {a0} := by
            ext x; simp <;> tauto
          rw [Finset.card_univ, h_sing, Finset.card_singleton] at h_card_univ_eq
          omega
        rw [h_card_j]
        push_cast
        ring
      _ ≤ (2 * (t + 1)) ^ (t + 1) * Fintype.card Y ^ (t + 1) := by
        have ht1 : Fintype.card α - 1 = 2 * t + 1 := by omega
        rw [ht1]
        have h_ineq : (2 * t + 1) * (2 * t) ^ t ≤ (2 * (t + 1)) ^ (t + 1) := by
          calc (2 * t + 1) * (2 * t) ^ t
            _ ≤ (2 * t + 2) * (2 * t + 2) ^ t := by
              apply Nat.mul_le_mul
              · omega
              · apply Nat.pow_le_pow_left (by omega)
            _ = (2 * t + 2) ^ (t + 1) := by rw [pow_succ]; ring
        calc (2 * t + 1) * Fintype.card Y * ((2 * t) ^ t * Fintype.card Y ^ t)
          _ = ((2 * t + 1) * (2 * t) ^ t) * (Fintype.card Y * Fintype.card Y ^ t) := by ring
          _ ≤ (2 * (t + 1)) ^ (t + 1) * (Fintype.card Y * Fintype.card Y ^ t) := by
            apply Nat.mul_le_mul_right; exact h_ineq
          _ = (2 * (t + 1)) ^ (t + 1) * Fintype.card Y ^ (t + 1) := by
            rw [pow_succ]
            ring


lemma sum_mul_le_of_le {I : Type*} [Fintype I] (P S : I → ℝ) {c : ℝ} (hP : ∀ x, P x ≤ c) (hS : ∀ x, 0 ≤ S x) :
    ∑ x, P x * S x ≤ c * ∑ x, S x := by
  have : ∀ x, P x * S x ≤ c * S x := by
    intro x
    exact mul_le_mul_of_nonneg_right (hP x) (hS x)
  calc ∑ x, P x * S x
    _ ≤ ∑ x, c * S x := sum_le_sum fun x _ => this x
    _ = c * ∑ x, S x := by rw [← mul_sum]

lemma S_pow_ge_0 {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι] [DecidableEq Y]
    (q : PMF Y) (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2)) (t : ℕ) :
    0 ≤ (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) := by
  have h_pow : (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) = ((∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ t) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [h_pow]
  exact sq_nonneg _

lemma E_S_pow_bound {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι] [DecidableEq Y]
    (p : PMF ((ι → ZMod 2) × (ι → ZMod 2))) (q : PMF Y) (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (k₁ : ℝ)
    (hp : ∀ x, (p x).toReal ≤ (2 : ℝ) ^ (-k₁)) :
    (∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) ≤
    (2 : ℝ) ^ (-k₁) * ∑ x, (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) := by
  have h1 : (∑ x, (p x).toReal * ∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) ≤
      ∑ x, (p x).toReal * (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) := by
    apply pow_sum_mul_le
    · intro x; exact ENNReal.toReal_nonneg
    · exact sum_toReal p
  have h2 : ∑ x, (p x).toReal * (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) ≤
      (2 : ℝ) ^ (-k₁) * ∑ x, (∑ y, (q y).toReal * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) := by
    apply sum_mul_le_of_le
    · exact hp
    · intro x; exact S_pow_ge_0 q M x t
  exact le_trans h1 h2

variable {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι] [DecidableEq Y]

theorem RazExtractorTheorem (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) (C : ℝ) (ε : ℝ)
    (hM : IsRazMatrixFamily M t δ) (k₁ k₂ : ℝ)
    (hk₁ : (1 / 2 + δ) * (Fintype.card ι : ℝ) ≤ k₁)
    (hk₂ : C * Real.log (Fintype.card ι) ≤ k₂)
    (hε : ((2 : ℝ) ^ (-k₁) * (((2 * t : ℝ) ^ t * (Fintype.card Y : ℝ) ^ t) * (2 : ℝ) ^ (-2 * t * k₂) * (2 : ℝ) ^ (2 * Fintype.card ι) + (2 : ℝ) ^ (2 * Fintype.card ι - (1 - δ) * Fintype.card ι))) ^ (1 / (2 * t : ℝ)) / 2 ≤ ε) :
    IsTwoSourceExtractor (fun x y => decide ((razExtractor M x y) = 1)) k₁ k₂ ε := by
  intro p q hp hq
  rw [dist_bind_map_eq_abs_bias]
  sorry

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_add_left (M : Y → Matrix ι ι (ZMod 2)) (x₁ x₁' x₂ : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁ + x₁', x₂) y = razExtractor M (x₁, x₂) y + razExtractor M (x₁', x₂) y := by
  simp [razExtractor, ]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_add_right (M : Y → Matrix ι ι (ZMod 2)) (x₁ x₂ x₂' : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁, x₂ + x₂') y = razExtractor M (x₁, x₂) y + razExtractor M (x₁, x₂') y := by
  simp [razExtractor, mulVec_add]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_zero_left (M : Y → Matrix ι ι (ZMod 2)) (x₂ : ι → ZMod 2) (y : Y) :
    razExtractor M (0, x₂) y = 0 := by
  simp [razExtractor, zero_dotProduct]

omit [Fintype Y] [DecidableEq ι] in
theorem razExtractor_zero_right (M : Y → Matrix ι ι (ZMod 2)) (x₁ : ι → ZMod 2) (y : Y) :
    razExtractor M (x₁, 0) y = 0 := by
  simp [razExtractor, mulVec_zero, dotProduct_zero]

omit [Fintype Y] [DecidableEq ι] in
theorem ZMod.neg_one_pow_val_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

omit [Fintype Y] [DecidableEq ι] in
theorem ZMod.neg_one_pow_val_sum {R : Type*} [CommRing R] {I : Type*} (s : Finset I)
    (f : I → ZMod 2) :
    (-1 : R) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1) ^ (f i).val := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_cons, prod_cons, ZMod.neg_one_pow_val_add, ih]

omit [Fintype Y] [DecidableEq ι] in
theorem sum_razExtractor (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2))
    {I : Type*} (s : Finset I) (y : I → Y) :
    ∑ i ∈ s, razExtractor M x (y i) = x.1 ⬝ᵥ ((∑ i ∈ s, M (y i)) *ᵥ x.2) := by
  induction s using Finset.cons_induction with
  | empty => simp [razExtractor]
  | cons a s ha ih =>
    rw [sum_cons, sum_cons, add_mulVec, dotProduct_add, ← ih]
    rfl

omit [DecidableEq ι] in
theorem razExtractor_sum_pow_bias (q : Y → ℝ)
    (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2)) (t : ℕ) :
    (∑ y, q y * (-1 : ℝ) ^ (razExtractor M x y).val) ^ (2 * t) =
      ∑ y : Fin (2 * t) → Y, (∏ i, q (y i)) * (-1 : ℝ) ^ (∑ i, razExtractor M x (y i)).val := by
  have := Fintype.sum_pow (fun y => q y * (-1 : ℝ) ^ (razExtractor M x y).val) (2 * t)
  rw [this]
  refine sum_congr rfl fun y _ => ?_
  rw [prod_mul_distrib]
  congr 1
  rw [← ZMod.neg_one_pow_val_sum]

omit [Fintype Y] [DecidableEq ι] in
theorem pow_sum_mul_le {I : Type*} [Fintype I] (P S : I → ℝ) (hP_nonneg : ∀ x, 0 ≤ P x)
    (hP_sum : ∑ x, P x = 1) (t : ℕ) :
    (∑ x, P x * S x) ^ (2 * t) ≤ ∑ x, P x * S x ^ (2 * t) := by
  have heven : Even (2 * t) := even_two_mul t
  have h_conv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * t)) := Even.convexOn_pow heven
  have h_jensen := ConvexOn.map_sum_le h_conv (fun i _ => hP_nonneg i) hP_sum
    (fun i _ => Set.mem_univ (S i))
  simp_rw [smul_eq_mul] at h_jensen
  exact h_jensen

omit [Fintype Y] in
theorem sum_x1_x2_eq_two_pow_corank (M : Matrix ι ι (ZMod 2)) :
    ∑ x : (ι → ZMod 2) × (ι → ZMod 2), (-1 : ℝ) ^ (x.1 ⬝ᵥ (M *ᵥ x.2)).val =
    (2 : ℝ) ^ (2 * Fintype.card ι) / (2 : ℝ) ^ M.rank := by
  have h1 : ∑ x : (ι → ZMod 2) × (ι → ZMod 2), (-1 : ℝ) ^ (x.1 ⬝ᵥ (M *ᵥ x.2)).val =
      ∑ x1 : ι → ZMod 2, ∑ x2 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val := by
    rw [Fintype.sum_prod_type]
  have h1' : ∑ x1 : ι → ZMod 2, ∑ x2 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val =
      ∑ x2 : ι → ZMod 2, ∑ x1 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val := by
    rw [sum_comm]
  rw [h1, h1']
  have h2 : ∀ x2, ∑ x1 : ι → ZMod 2, (-1 : ℝ) ^ (x1 ⬝ᵥ (M *ᵥ x2)).val =
      if M *ᵥ x2 = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
    intro x2
    exact sum_neg_one_pow_val_dotProduct (M *ᵥ x2)
  simp_rw [h2]
  have h3 : ∑ x2 : ι → ZMod 2, (if M *ᵥ x2 = 0 then (2 : ℝ) ^ Fintype.card ι else 0) =
      (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * (2 : ℝ) ^ Fintype.card ι := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rw [h3]
  have h4 : (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * 2 ^ M.rank = (2 : ℝ) ^ Fintype.card ι := by
    exact_mod_cast card_ker_mul_two_pow_rank M
  have h5 : (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) = (2 : ℝ) ^ Fintype.card ι / 2 ^ M.rank := by
    calc (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) =
        (#{z : ι → ZMod 2 | M *ᵥ z = 0} : ℝ) * 2 ^ M.rank / 2 ^ M.rank := by
          rw [mul_div_cancel_right₀]
          positivity
      _ = (2 : ℝ) ^ Fintype.card ι / 2 ^ M.rank := by rw [h4]
  rw [h5, mul_comm, mul_div, ← pow_add, ← two_mul]

end Cslib.Probability
