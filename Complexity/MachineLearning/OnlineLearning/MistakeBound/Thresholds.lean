/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MistakeBound.SOA
public import Complexity.MachineLearning.OnlineLearning.MistakeBound.VCDimension
public import Mathlib.Order.Interval.Finset.Nat
import Complexity.MachineLearning.PACLearning.VCDimension

/-!
# Thresholds: VC dimension one, unbounded Littlestone dimension

The threshold concept `thresholdConcept θ : ℕ → Bool` labels `x` with `true` iff `x < θ`. The
thresholds `θ ≤ N` (`thresholdClassUpTo N`) separate the VC dimension from the Littlestone
dimension [Littlestone1988, §3, Example 3]:

* no two points are shattered, since a threshold labelling the larger point `true` labels the
  smaller one `true` too, so the VC dimension is `1` (`vcDim_thresholdClassUpTo`);
* a learner can be forced to err once per step of a binary search, and halving matches this, so
  the Littlestone dimension is `⌊log₂ (N + 1)⌋` (`littlestoneDim_thresholdClassUpTo`).

So the chain `vcDim C ≤ littlestoneDim C ≤ ⌊log₂ |C|⌋` can be strict in its first inequality by an
arbitrary amount. For `N = 2 ^ n - 1` this is Littlestone's example: `2 ^ n` thresholds, VC
dimension `1` and optimal mistake bound `n`. The class of all thresholds (`thresholdClass`) has VC
dimension `1` and infinite Littlestone dimension. It is learnable in the PAC model but not with
finitely many mistakes.

Littlestone's Example 3 uses the instance space `{1, …, 2 ^ n - 1}` and the thresholds
`f_j(x) = 1` iff `x < j` for `j ∈ {1, …, 2 ^ n}`. Here the instance space is all of `ℕ` and
`θ ∈ {0, …, 2 ^ n - 1}`. The two classes have the same number of thresholds and the same dimensions;
the instances `x ≥ N` add nothing, since every threshold labels them `false`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdConcept`: the threshold `x < θ`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdClass`: all thresholds.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdClassUpTo`: the thresholds `θ ≤ N`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_thresholdClassUpTo`:
  `littlestoneDim (thresholdClassUpTo N) = ⌊log₂ (N + 1)⌋`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_thresholdClassUpTo_pow`:
  [Littlestone1988, §3, Example 3], `2 ^ n` thresholds have optimal mistake bound `n`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.vcDim_thresholdClassUpTo`: VC dimension `1`
  for `N ≥ 1`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_thresholdClass`,
  `Cslib.MachineLearning.OnlineLearning.MistakeBound.vcDim_thresholdClass`: all thresholds have
  infinite Littlestone dimension and VC dimension `1`.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass SetShatters vcDim)

/-- The threshold concept: `x` is labelled `true` iff `x < θ`. -/
def thresholdConcept (θ : ℕ) : ℕ → Bool := fun x => decide (x < θ)

/-- The class of all threshold concepts on `ℕ`. -/
def thresholdClass : ConceptClass ℕ Bool := Set.range thresholdConcept

/-- The threshold concepts with `θ ≤ N`. -/
def thresholdClassUpTo (N : ℕ) : ConceptClass ℕ Bool := thresholdConcept '' Set.Iic N

@[simp] theorem thresholdConcept_apply (θ x : ℕ) : thresholdConcept θ x = decide (x < θ) := by
  rw [thresholdConcept]

theorem mem_thresholdClass {c : ℕ → Bool} : c ∈ thresholdClass ↔ ∃ θ, thresholdConcept θ = c :=
  Iff.rfl

theorem mem_thresholdClassUpTo {N : ℕ} {c : ℕ → Bool} :
    c ∈ thresholdClassUpTo N ↔ ∃ θ ≤ N, thresholdConcept θ = c :=
  Iff.rfl

theorem thresholdConcept_injective : Function.Injective thresholdConcept := by
  intro a b hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := congrFun hab a; simp [h] at this
  · have := congrFun hab b; simp [h] at this

theorem thresholdClassUpTo_subset_thresholdClass (N : ℕ) : thresholdClassUpTo N ⊆ thresholdClass :=
  Set.image_subset_range _ _

/-- Binary search: the thresholds `θ ∈ [lo, lo + 2 ^ k - 1]` have a complete `k`-mistake tree, whose
root is labelled with the midpoint `lo + 2 ^ (k - 1) - 1`. -/
theorem hasMistakeTree_thresholdConcept_Icc (k lo : ℕ) :
    HasMistakeTree k (thresholdConcept '' Set.Icc lo (lo + 2 ^ k - 1)) := by
  induction k generalizing lo with
  | zero => exact ⟨thresholdConcept lo, lo, ⟨le_rfl, by simp⟩, rfl⟩
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨lo + 2 ^ k - 1, fun y => ?_⟩
    cases y
    · refine (ih lo).mono ?_
      rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      refine mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨h1, ?_⟩, rfl⟩, ?_⟩
      · rw [pow_succ]; omega
      · simp only [thresholdConcept, decide_eq_false_iff_not, not_lt]; omega
    · refine (ih (lo + 2 ^ k)).mono ?_
      rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      refine mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨by omega, ?_⟩, rfl⟩, ?_⟩
      · rw [pow_succ]; omega
      · simp only [thresholdConcept, decide_eq_true_eq]; omega

/-- The thresholds `θ ≤ N` have Littlestone dimension `⌊log₂ (N + 1)⌋`. -/
theorem littlestoneDim_thresholdClassUpTo (N : ℕ) :
    littlestoneDim (thresholdClassUpTo N) = Nat.log 2 (N + 1) := by
  classical
  apply le_antisymm
  · have hC : thresholdClassUpTo N =
        ((Finset.Iic N).image thresholdConcept : Set (ℕ → Bool)) := by
      simp [thresholdClassUpTo]
    rw [hC]
    refine (littlestoneDim_le_log_card _).trans ?_
    exact_mod_cast Nat.log_mono_right ((Finset.card_image_le).trans (by simp))
  · refine le_littlestoneDim_of_hasMistakeTree ((hasMistakeTree_thresholdConcept_Icc _ 0).mono ?_)
    rintro _ ⟨θ, ⟨-, h2⟩, rfl⟩
    refine ⟨θ, ?_, rfl⟩
    have := Nat.pow_log_le_self 2 (show N + 1 ≠ 0 by omega)
    simp only [Set.mem_Iic]
    omega

/-- [Littlestone1988, §3, Example 3]: the `2 ^ n` thresholds `θ < 2 ^ n` have optimal mistake
bound `n`. -/
theorem optimalMistakeBound_thresholdClassUpTo_pow (n : ℕ) :
    optimalMistakeBound (thresholdClassUpTo (2 ^ n - 1)) = n := by
  rw [optimalMistakeBound_eq_littlestoneDim, littlestoneDim_thresholdClassUpTo,
    Nat.sub_add_cancel Nat.one_le_two_pow, Nat.log_pow (by norm_num)]

/-- All thresholds together have infinite Littlestone dimension: no learner has a finite mistake
bound. -/
theorem littlestoneDim_thresholdClass : littlestoneDim thresholdClass = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  refine le_littlestoneDim_of_hasMistakeTree ((hasMistakeTree_thresholdConcept_Icc n 0).mono ?_)
  rintro _ ⟨θ, -, rfl⟩
  exact ⟨θ, rfl⟩

/-- No two points are shattered by thresholds. -/
theorem not_setShatters_thresholdClass {W : Finset ℕ} (hW : 1 < W.card) :
    ¬ SetShatters thresholdClass (W : Set ℕ) := by
  intro hsh
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hW
  wlog hlt : a < b generalizing a b
  · exact this b hb a ha (Ne.symm hab) (by omega)
  obtain ⟨c, ⟨θ, rfl⟩, hc⟩ := hsh {b} (by simpa using hb)
  have hb' : b ∈ thresholdConcept θ ⁻¹' {true} ∩ (W : Set ℕ) := hc ▸ rfl
  have ha' : a ∉ thresholdConcept θ ⁻¹' {true} ∩ (W : Set ℕ) := by
    rw [hc]; simpa using hab
  have hbθ : b < θ := by simpa using hb'.1
  exact ha' ⟨by simp only [Set.mem_preimage, Set.mem_singleton_iff, thresholdConcept_apply,
    decide_eq_true_eq]; omega, ha⟩

theorem setShatters_singleton_thresholdClassUpTo {N x : ℕ} (hx : x < N) :
    SetShatters (thresholdClassUpTo N) ({x} : Set ℕ) := by
  intro W' hW'
  rcases Set.subset_singleton_iff_eq.mp hW' with rfl | rfl
  · refine ⟨thresholdConcept 0, ⟨0, by simp, rfl⟩, ?_⟩
    ext z; simp
  · refine ⟨thresholdConcept (x + 1), ⟨x + 1, by simp only [Set.mem_Iic]; omega, rfl⟩, ?_⟩
    ext z; simp

/-- A class of thresholds that shatters a point has VC dimension `1`. -/
theorem vcDim_eq_one_of_subset_thresholdClass {C : ConceptClass ℕ Bool} (hC : C ⊆ thresholdClass)
    (x : ℕ) (hx : SetShatters C ({x} : Set ℕ)) : vcDim C = 1 := by
  have hub : ∀ n ∈ {n : ℕ | ∃ W : Finset ℕ, W.card = n ∧ SetShatters C (W : Set ℕ)}, n ≤ 1 := by
    rintro n ⟨W, rfl, hW⟩
    exact not_lt.mp fun h => not_setShatters_thresholdClass h (hW.superset hC)
  refine le_antisymm (csSup_le' hub) ?_
  simpa using (show SetShatters C (({x} : Finset ℕ) : Set ℕ) by simpa using hx).card_le_vcDim
    ⟨1, hub⟩

/-- For `N ≥ 1`, the thresholds `θ ≤ N` have VC dimension `1`. -/
theorem vcDim_thresholdClassUpTo {N : ℕ} (hN : 1 ≤ N) : vcDim (thresholdClassUpTo N) = 1 :=
  vcDim_eq_one_of_subset_thresholdClass (thresholdClassUpTo_subset_thresholdClass N) 0
    (setShatters_singleton_thresholdClassUpTo hN)

/-- All thresholds together have VC dimension `1`. -/
theorem vcDim_thresholdClass : vcDim thresholdClass = 1 :=
  vcDim_eq_one_of_subset_thresholdClass subset_rfl 0
    ((setShatters_singleton_thresholdClassUpTo (N := 1) one_pos).superset
      (thresholdClassUpTo_subset_thresholdClass 1))

end Cslib.MachineLearning.OnlineLearning.MistakeBound
