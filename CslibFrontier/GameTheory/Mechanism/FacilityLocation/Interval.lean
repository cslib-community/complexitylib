/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import Mathlib.Data.Finset.Fold

/-!
# Strategyproof facility location on closed real intervals

This module formalizes Moulin's characterization ([Moulin1980]) of deterministic, surjective,
strategyproof facility-location mechanisms on a closed interval `[a, b] ⊆ ℝ` (`Set.Icc a b`), along
with transfer lemmas for isometric intervals in an arbitrary metric space.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.MoulinScheme`: a generalized median voter scheme on
  `Set.Icc a b` for a finite nonempty agent set `ι`, determined by an antitone family of phantom
  parameters `alpha : Finset ι → ℝ` valued in `Set.Icc a b` with `alpha ∅ = b` and
  `alpha Finset.univ = a`.
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.eval`: evaluates the generalized median rule
  `min_{S} max(alpha S, max(a, sup_{i ∈ S} x i))`.

## Main results

* `Cslib.GameTheory.FacilityLocation.unanimous_of_surjective_isStrategyProof`: every deterministic,
  surjective, strategyproof mechanism on a metric space is unanimous.
* `Cslib.GameTheory.FacilityLocation.MoulinScheme.eval_isGroupStrategyProof`: every Moulin scheme
  defines a group-strategyproof deterministic mechanism.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme`:
  a deterministic rule on `Set.Icc a b` is surjective and strategyproof if and only if it is the
  evaluation map of a `MoulinScheme`.
* `Cslib.GameTheory.FacilityLocation.moulinScheme_of_isometry`: transfers any strategyproof
  mechanism preserving and surjecting onto an isometric copy of `[0, d]` in a metric space to a
  `MoulinScheme ι 0 d`.
* `Cslib.GameTheory.FacilityLocation.moulinScheme_finTwo_eq`: explicit two-agent formula
  `min (max α₀ x₀) (min (max α₁ x₁) (max x₀ x₁))`.

## References

* [Moulin1980] H. Moulin, "On strategy-proofness and single peakedness", Public Choice 35 (1980).
-/

public section

namespace Cslib.GameTheory.FacilityLocation

section Unanimity

/-- Every surjective, strategyproof deterministic facility-location mechanism on a metric space is
unanimous: when all agents report the same location `y`, the mechanism places the facility at
`y`. -/
theorem unanimous_of_surjective_isStrategyProof {ι G : Type*} [Finite ι] [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) (y : G) :
    f (fun _ => y) = y := by
  classical
  let _ := Fintype.ofFinite ι
  have hsp : ∀ (x : ι → G) (i : ι) (z : G),
      dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i) := fun x i z => by
    simpa only [dist_comm] using (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp x i z
  suffices h : ∀ (n : ℕ) (x : ι → G),
      (Finset.univ.filter fun i => x i ≠ y).card = n → f x = y → f (fun _ => y) = y by
    obtain ⟨x₀, hx₀⟩ := hf_onto y
    exact h _ x₀ rfl hx₀
  intro n
  induction n with
  | zero =>
    intro x hcard hfx
    have hemp : (Finset.univ.filter fun i => x i ≠ y) = ∅ := Finset.card_eq_zero.mp hcard
    have heq : x = fun _ => y := by
      funext i
      by_contra hne
      have hi : i ∈ Finset.univ.filter fun i => x i ≠ y := by simp [hne]
      rw [hemp] at hi
      exact Finset.notMem_empty i hi
    simpa [heq] using hfx
  | succ k ih =>
    intro x hcard hfx
    have hne : (Finset.univ.filter fun i => x i ≠ y).Nonempty :=
      Finset.card_pos.mp (hcard ▸ Nat.succ_pos k)
    obtain ⟨i₀, hi₀⟩ := hne
    have hi₀_ne : x i₀ ≠ y := (Finset.mem_filter.mp hi₀).2
    let x' := Function.update x i₀ y
    have hfx' : f x' = y := by
      have h1 : dist (f x') y ≤ dist (f x) y := by
        have hupd := hsp x' i₀ (x i₀)
        have hxx : Function.update x' i₀ (x i₀) = x := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [x']
          · simp [x', hj]
        simpa [x', hxx] using hupd
      rw [hfx, dist_self] at h1
      exact dist_le_zero.mp h1
    have hsub : Finset.univ.filter (fun i => x' i ≠ y) =
        (Finset.univ.filter fun i => x i ≠ y).erase i₀ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, x']
      by_cases hj : j = i₀
      · subst hj; simp
      · simp [hj]
    have hcard' : (Finset.univ.filter fun i => x' i ≠ y).card = k := by
      rw [hsub, Finset.card_erase_of_mem hi₀, hcard]
      simp
    exact ih x' hcard' hfx'

end Unanimity

section Moulin

private noncomputable def finMax {ι : Type*} (a : ℝ) (S : Finset ι) (g : ι → ℝ) : ℝ :=
  S.fold max a g

private noncomputable def finMin {ι : Type*} (b : ℝ) (T : Finset (Finset ι))
    (g : Finset ι → ℝ) : ℝ :=
  T.fold min b g

private lemma le_finMax {ι : Type*} (a : ℝ) (S : Finset ι) (g : ι → ℝ) : a ≤ finMax a S g :=
  (Finset.le_fold_max a).mpr (Or.inl le_rfl)

private lemma mem_le_finMax {ι : Type*} (a : ℝ) {S : Finset ι} (g : ι → ℝ) {i : ι}
    (hi : i ∈ S) : g i ≤ finMax a S g :=
  (Finset.le_fold_max (g i)).mpr (Or.inr ⟨i, hi, le_rfl⟩)

private lemma finMax_le {ι : Type*} {a c : ℝ} {S : Finset ι} {g : ι → ℝ}
    (ha : a ≤ c) (hg : ∀ i ∈ S, g i ≤ c) : finMax a S g ≤ c :=
  (Finset.fold_max_le c).mpr ⟨ha, hg⟩

private lemma finMax_lt {ι : Type*} {a c : ℝ} {S : Finset ι} {g : ι → ℝ}
    (ha : a < c) (hg : ∀ i ∈ S, g i < c) : finMax a S g < c :=
  (Finset.fold_max_lt c).mpr ⟨ha, hg⟩

private lemma finMax_mono_fun {ι : Type*} (a : ℝ) (S : Finset ι) {g₁ g₂ : ι → ℝ}
    (hg : ∀ i ∈ S, g₁ i ≤ g₂ i) : finMax a S g₁ ≤ finMax a S g₂ :=
  finMax_le (le_finMax a S g₂) fun i hi => (hg i hi).trans (mem_le_finMax a g₂ hi)

private lemma finMax_eq_of_eqOn {ι : Type*} (a : ℝ) (S : Finset ι) {g₁ g₂ : ι → ℝ}
    (hg : ∀ i ∈ S, g₁ i = g₂ i) : finMax a S g₁ = finMax a S g₂ :=
  Finset.fold_congr hg

private lemma finMin_le {ι : Type*} (b : ℝ) {T : Finset (Finset ι)} (g : Finset ι → ℝ)
    {S : Finset ι} (hS : S ∈ T) : finMin b T g ≤ g S :=
  (Finset.fold_min_le (g S)).mpr (Or.inr ⟨S, hS, le_rfl⟩)

private lemma le_finMin {ι : Type*} {b c : ℝ} {T : Finset (Finset ι)} {g : Finset ι → ℝ}
    (hb : c ≤ b) (hg : ∀ S ∈ T, c ≤ g S) : c ≤ finMin b T g :=
  (Finset.le_fold_min c).mpr ⟨hb, hg⟩

private lemma finMin_le_base {ι : Type*} (b : ℝ) (T : Finset (Finset ι)) (g : Finset ι → ℝ) :
    finMin b T g ≤ b :=
  (Finset.fold_min_le b).mpr (Or.inl le_rfl)

private lemma exists_finMin_eq {ι : Type*} {b : ℝ} {T : Finset (Finset ι)} {g : Finset ι → ℝ}
    (hT : T.Nonempty) (hbd : ∃ S ∈ T, g S ≤ b) :
    ∃ S ∈ T, g S = finMin b T g := by
  classical
  obtain ⟨S₀, hS₀_mem, hS₀_le⟩ := T.exists_min_image g hT
  refine ⟨S₀, hS₀_mem, le_antisymm ?_ (finMin_le b g hS₀_mem)⟩
  obtain ⟨S₁, hS₁_mem, hS₁_le⟩ := hbd
  exact le_finMin ((hS₀_le S₁ hS₁_mem).trans hS₁_le) fun S hS => hS₀_le S hS

private lemma finMin_eq_of_eqOn {ι : Type*} (b : ℝ) {T : Finset (Finset ι)}
    {g₁ g₂ : Finset ι → ℝ} (hg : ∀ S ∈ T, g₁ S = g₂ S) : finMin b T g₁ = finMin b T g₂ :=
  Finset.fold_congr hg

private lemma finMin_union {ι : Type*} [DecidableEq ι] (b : ℝ) (T₁ T₂ : Finset (Finset ι))
    (g : Finset ι → ℝ) :
    finMin b (T₁ ∪ T₂) g = min (finMin b T₁ g) (finMin b T₂ g) := by
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · refine le_finMin (finMin_le_base b _ _) fun S hS =>
        finMin_le b g (Finset.mem_union_left T₂ hS)
    · refine le_finMin (finMin_le_base b _ _) fun S hS =>
        finMin_le b g (Finset.mem_union_right T₁ hS)
  · refine le_finMin (min_le_of_left_le (finMin_le_base b T₁ g)) fun S hS => ?_
    rcases Finset.mem_union.mp hS with h1 | h2
    · exact min_le_of_left_le (finMin_le b g h1)
    · exact min_le_of_right_le (finMin_le b g h2)

private lemma finMin_max_right {ι : Type*} (b : ℝ) (T : Finset (Finset ι)) (g : Finset ι → ℝ)
    {t : ℝ} (ht : t ≤ b) :
    finMin b T (fun S => max (g S) t) = max (finMin b T g) t := by
  classical
  dsimp only [finMin]
  induction T using Finset.induction with
  | empty => simp [ht]
  | insert U T hU ih =>
    rw [Finset.fold_insert hU, Finset.fold_insert hU, ih, max_min_distrib_right]

private lemma finMax_eq_max_sdiff {ι : Type*} [DecidableEq ι] (a : ℝ) (S T : Finset ι)
    (g : ι → ℝ) :
    finMax a (S ∪ T) g = max (finMax a S g) (finMax a T g) := by
  refine le_antisymm ?_ ?_
  · refine finMax_le (le_max_of_le_left (le_finMax a S g)) fun i hi => ?_
    rcases Finset.mem_union.mp hi with hiS | hiT
    · exact le_max_of_le_left (mem_le_finMax a g hiS)
    · exact le_max_of_le_right (mem_le_finMax a g hiT)
  · exact max_le
      (finMax_le (le_finMax a _ g) fun i hi => mem_le_finMax a g (Finset.mem_union_left T hi))
      (finMax_le (le_finMax a _ g) fun i hi => mem_le_finMax a g (Finset.mem_union_right S hi))

/-- A **Moulin generalized median voter scheme** on `Set.Icc a b` for a finite nonempty agent
type `ι`: an antitone family of phantom thresholds `alpha : Finset ι → ℝ` taking values in
`Set.Icc a b` with boundary conditions `alpha ∅ = b` and `alpha Finset.univ = a`. -/
structure MoulinScheme (ι : Type*) [Fintype ι] (a b : ℝ) where
  /-- Coalition phantom parameters `α_S ∈ [a, b]`. -/
  alpha : Finset ι → ℝ
  /-- Every phantom parameter lies in `[a, b]`. -/
  mem_Icc : ∀ S : Finset ι, alpha S ∈ Set.Icc a b
  /-- Larger coalitions receive weakly smaller phantom thresholds. -/
  antitone : Antitone alpha
  /-- Empty coalition takes the upper endpoint `b`. -/
  boundary_empty : alpha ∅ = b
  /-- Grand coalition takes the lower endpoint `a`. -/
  boundary_univ : alpha Finset.univ = a

namespace MoulinScheme

section Eval

variable {ι : Type*} [Fintype ι] {a b : ℝ} (E : MoulinScheme ι a b)

private noncomputable def evalVal (x : ι → Set.Icc a b) : ℝ :=
  finMin b Finset.univ fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ))

private lemma evalVal_mem_Icc (x : ι → Set.Icc a b) : E.evalVal x ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · refine le_finMin ?_ fun S _ => ?_
    · exact (E.mem_Icc Finset.univ).1.trans (E.mem_Icc Finset.univ).2
    · exact le_max_of_le_left (E.mem_Icc S).1
  · exact finMin_le_base b Finset.univ _

/-- Evaluates a `MoulinScheme` on an agent profile `x : ι → Set.Icc a b`, returning
`min_{S} max(α_S, max(a, sup_{i ∈ S} x_i)) ∈ Set.Icc a b`. -/
noncomputable def eval (x : ι → Set.Icc a b) : Set.Icc a b :=
  ⟨E.evalVal x, E.evalVal_mem_Icc x⟩

@[simp]
private theorem eval_coe (x : ι → Set.Icc a b) : (E.eval x : ℝ) = E.evalVal x := rfl

private lemma exists_eval_witness (x : ι → Set.Icc a b) :
    ∃ S : Finset ι, max (E.alpha S) (finMax a S fun i => (x i : ℝ)) = (E.eval x : ℝ) := by
  obtain ⟨S, _, hS⟩ := exists_finMin_eq (b := b) (T := Finset.univ)
    (g := fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ)))
    (Finset.univ_nonempty (α := Finset ι))
    ⟨∅, Finset.mem_univ _, by
      have ha : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
      rw [E.boundary_empty]
      simp [finMax, ha]⟩
  exact ⟨S, hS⟩

theorem eval_const [Nonempty ι] (y : Set.Icc a b) : E.eval (fun _ => y) = y := by
  ext
  refine le_antisymm ?_ ?_
  · have hle := finMin_le b (T := Finset.univ)
      (fun S => max (E.alpha S) (finMax a S fun _ : ι => (y : ℝ))) (Finset.mem_univ Finset.univ)
    have hmax : finMax a Finset.univ (fun _ : ι => (y : ℝ)) = y := by
      refine le_antisymm (finMax_le y.2.1 fun _ _ => le_rfl) ?_
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      exact mem_le_finMax a (fun _ => (y : ℝ)) (Finset.mem_univ i₀)
    rw [eval_coe]
    dsimp only [evalVal]
    rw [E.boundary_univ, hmax, max_eq_right y.2.1] at hle
    exact hle
  · refine le_finMin y.2.2 fun S _ => ?_
    by_cases hS : S = ∅
    · subst hS
      rw [E.boundary_empty]
      exact le_max_of_le_left y.2.2
    · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      exact le_max_of_le_right (mem_le_finMax a (fun _ => (y : ℝ)) hi₀)

theorem eval_surjective [Nonempty ι] : Function.Surjective E.eval :=
  fun y => ⟨fun _ => y, E.eval_const y⟩

theorem eval_mono {x z : ι → Set.Icc a b} (hxz : ∀ i, (x i : ℝ) ≤ (z i : ℝ)) :
    (E.eval x : ℝ) ≤ E.eval z := by
  obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness z
  rw [← hS₀, eval_coe]
  refine (finMin_le b (T := Finset.univ)
    (fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ)))
    (Finset.mem_univ S₀)).trans ?_
  exact max_le (le_max_left _ _) (le_max_of_le_right (finMax_mono_fun a S₀ fun i _ => hxz i))

theorem lt_eval_iff (x : ι → Set.Icc a b) (y : Set.Icc a b) :
    (y : ℝ) < E.eval x ↔ (y : ℝ) < E.alpha (Finset.univ.filter fun i => (x i : ℝ) ≤ y) := by
  classical
  let Sle : Finset ι := Finset.univ.filter fun i => (x i : ℝ) ≤ y
  constructor
  · intro hy
    have hle : (E.eval x : ℝ) ≤ max (E.alpha Sle) (finMax a Sle fun i => (x i : ℝ)) := by
      rw [eval_coe]
      exact finMin_le b (T := Finset.univ)
        (fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ))) (Finset.mem_univ Sle)
    have hmax : (finMax a Sle fun i => (x i : ℝ)) ≤ y :=
      finMax_le y.2.1 fun i hi => (Finset.mem_filter.mp hi).2
    have hlt_max : (y : ℝ) < max (E.alpha Sle) (finMax a Sle fun i => (x i : ℝ)) :=
      hy.trans_le hle
    exact (lt_max_iff.mp hlt_max).resolve_right (not_lt.mpr hmax)
  · intro hy
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    rw [← hS₀]
    by_cases hsub : S₀ ⊆ Sle
    · exact lt_of_lt_of_le hy ((E.antitone hsub).trans (le_max_left _ _))
    · obtain ⟨i, hiS₀, hi_not⟩ := Finset.not_subset.mp hsub
      have hi_gt : (y : ℝ) < x i := by
        by_contra hle
        exact hi_not (Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_lt.mp hle⟩)
      exact lt_max_of_lt_right (hi_gt.trans_le (mem_le_finMax a (fun j => (x j : ℝ)) hiS₀))

theorem eval_lt_iff (x : ι → Set.Icc a b) (y : Set.Icc a b) :
    (E.eval x : ℝ) < y ↔ E.alpha (Finset.univ.filter fun i => (x i : ℝ) < y) < y := by
  classical
  let Slt : Finset ι := Finset.univ.filter fun i => (x i : ℝ) < y
  constructor
  · intro hy
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    rw [← hS₀] at hy
    have hα : E.alpha S₀ < y := (le_max_left _ _).trans_lt hy
    have hsub : S₀ ⊆ Slt := fun i hi => by
      have hm : (x i : ℝ) ≤ finMax a S₀ fun j => (x j : ℝ) :=
        mem_le_finMax a (fun j => (x j : ℝ)) hi
      have hmax : (finMax a S₀ fun j => (x j : ℝ)) < y := (le_max_right _ _).trans_lt hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm.trans_lt hmax⟩
    exact (E.antitone hsub).trans_lt hα
  · intro hy
    have ha : a < y := (E.mem_Icc Slt).1.trans_lt hy
    have hle : (E.eval x : ℝ) ≤ max (E.alpha Slt) (finMax a Slt fun i => (x i : ℝ)) := by
      rw [eval_coe]
      exact finMin_le b (T := Finset.univ)
        (fun S => max (E.alpha S) (finMax a S fun i => (x i : ℝ))) (Finset.mem_univ Slt)
    exact hle.trans_lt (max_lt hy (finMax_lt ha fun i hi => (Finset.mem_filter.mp hi).2))

theorem eval_isGroupStrategyProof [DecidableEq ι] [MeasurableSpace (Set.Icc a b)]
    [OpensMeasurableSpace (Set.Icc a b)] :
    (Mechanism.deterministic E.eval).IsGroupStrategyProof := by
  rw [Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, i₀, hi₀, hlt⟩
  let y : ℝ := (E.eval x : ℝ)
  let y' : ℝ := (E.eval (A.piecewise z x) : ℝ)
  have hne : y ≠ y' := by
    intro heq
    have hd : dist (x i₀) (E.eval (A.piecewise z x)) = dist (x i₀) (E.eval x) := by
      rw [Subtype.dist_eq, Subtype.dist_eq]
      change dist (x i₀ : ℝ) y' = dist (x i₀ : ℝ) y
      rw [heq]
    exact hlt.ne hd
  have hdist_le : ∀ i ∈ A, |y' - (x i : ℝ)| ≤ |y - (x i : ℝ)| := by
    intro i hi
    simpa [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, y, y'] using hle i hi
  rcases lt_or_gt_of_ne hne with hy_lt | hy'_lt
  · have hA_gt : ∀ i ∈ A, y < (x i : ℝ) := by
      intro i hi
      have hsq : (y' - (x i : ℝ)) ^ 2 ≤ (y - (x i : ℝ)) ^ 2 := by
        simpa [sq_le_sq] using hdist_le i hi
      nlinarith
    obtain ⟨S₀, hS₀⟩ := E.exists_eval_witness x
    have hdisj : ∀ j ∈ S₀, j ∉ A := by
      intro j hjS hjA
      have h1 : y < (x j : ℝ) := hA_gt j hjA
      have h2 : (x j : ℝ) ≤ max (E.alpha S₀) (finMax a S₀ fun k => (x k : ℝ)) :=
        le_max_of_le_right (mem_le_finMax a (fun k => (x k : ℝ)) hjS)
      linarith [hS₀]
    have hfin_eq : (finMax a S₀ fun j => ((A.piecewise z x j : Set.Icc a b) : ℝ)) =
        finMax a S₀ fun j => (x j : ℝ) :=
      finMax_eq_of_eqOn a S₀ fun j hj => by simp [Finset.piecewise_eq_of_notMem _ _ _ (hdisj j hj)]
    have hy' : y' ≤ y := by
      have := finMin_le b (T := Finset.univ)
        (fun S => max (E.alpha S) (finMax a S fun j => ((A.piecewise z x j : Set.Icc a b) : ℝ)))
        (Finset.mem_univ S₀)
      dsimp only [y', y, eval_coe, evalVal] at this ⊢
      rw [hfin_eq, hS₀] at this
      exact this
    linarith
  · have hA_lt : ∀ i ∈ A, (x i : ℝ) < y := by
      intro i hi
      have hsq : (y' - (x i : ℝ)) ^ 2 ≤ (y - (x i : ℝ)) ^ 2 := by
        simpa [sq_le_sq] using hdist_le i hi
      nlinarith
    obtain ⟨S₁, hS₁⟩ := E.exists_eval_witness (A.piecewise z x)
    have hα : E.alpha (S₁ ∪ A) < y := by
      have h1 : E.alpha (S₁ ∪ A) ≤ E.alpha S₁ := E.antitone Finset.subset_union_left
      have h2 : E.alpha S₁ ≤ y' := (le_max_left _ _).trans_eq hS₁
      linarith
    have ha_lt : a < y := lt_of_le_of_lt (E.mem_Icc _).1 (hα.trans_le le_rfl)
    have hmem_lt : ∀ j ∈ S₁ ∪ A, (x j : ℝ) < y := by
      intro j hj
      by_cases hjA : j ∈ A
      · exact hA_lt j hjA
      · have hjS : j ∈ S₁ := (Finset.mem_union.mp hj).resolve_right hjA
        have heq : (x j : ℝ) = ((A.piecewise z x j : Set.Icc a b) : ℝ) := by
          simp [Finset.piecewise_eq_of_notMem _ _ _ hjA]
        have hle' : ((A.piecewise z x j : Set.Icc a b) : ℝ) ≤ y' :=
          (le_max_of_le_right (mem_le_finMax a _ hjS)).trans_eq hS₁
        linarith
    have hle_y := finMin_le b (T := Finset.univ)
      (fun S => max (E.alpha S) (finMax a S fun j => (x j : ℝ)))
      (Finset.mem_univ (S₁ ∪ A))
    have hlt_y : max (E.alpha (S₁ ∪ A)) (finMax a (S₁ ∪ A) fun j => (x j : ℝ)) < y :=
      max_lt hα (finMax_lt ha_lt hmem_lt)
    dsimp only [y, eval_coe, evalVal] at hle_y hlt_y
    linarith

theorem eval_isStrategyProof [DecidableEq ι] [MeasurableSpace (Set.Icc a b)]
    [OpensMeasurableSpace (Set.Icc a b)] :
    (Mechanism.deterministic E.eval).IsStrategyProof :=
  E.eval_isGroupStrategyProof.isStrategyProof

private lemma evalVal_update_eq [DecidableEq ι] (x : ι → Set.Icc a b) (i₀ : ι) (t : Set.Icc a b) :
    E.evalVal (Function.update x i₀ t) =
      min (E.evalVal (Function.update x i₀ ⟨b, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2, le_rfl⟩))
        (max (E.evalVal (Function.update x i₀ ⟨a, le_rfl, (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2⟩))
          (t : ℝ)) := by
  classical
  let hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
  let g : Finset ι → ℝ := fun S => max (E.alpha S) (finMax a (S.erase i₀) fun j => (x j : ℝ))
  let T₀ := Finset.univ.filter fun S : Finset ι => i₀ ∉ S
  let T₁ := Finset.univ.filter fun S : Finset ι => i₀ ∈ S
  have huniv : (Finset.univ : Finset (Finset ι)) = T₀ ∪ T₁ := by
    ext S
    simp only [T₀, T₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hxz : ∀ (z : Set.Icc a b) (S : Finset ι),
      max (E.alpha S) (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ)) =
        if i₀ ∈ S then max (g S) (z : ℝ) else g S := by
    intro z S
    let xz := Function.update x i₀ z
    split_ifs with hi
    · have hS_eq : S = {i₀} ∪ S.erase i₀ := by
        ext k
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
        by_cases hk : k = i₀ <;> simp [hk, hi]
      have hfin : (finMax a S fun j => (xz j : ℝ)) =
          max (z : ℝ) (finMax a (S.erase i₀) fun j => (x j : ℝ)) := by
        calc
          (finMax a S fun j => (xz j : ℝ)) =
              finMax a ({i₀} ∪ S.erase i₀) fun j => (xz j : ℝ) := by conv_lhs => rw [hS_eq]
          _ = max (finMax a ({i₀} : Finset ι) fun j => (xz j : ℝ))
                (finMax a (S.erase i₀) fun j => (xz j : ℝ)) := finMax_eq_max_sdiff a _ _ _
          _ = max (max a (z : ℝ)) (finMax a (S.erase i₀) fun j => (x j : ℝ)) := by
            have h1 : (finMax a ({i₀} : Finset ι) fun j => (xz j : ℝ)) = max a (z : ℝ) := by
              simp [finMax, xz, max_comm]
            have h2 : (finMax a (S.erase i₀) fun j => (xz j : ℝ)) =
                finMax a (S.erase i₀) fun j => (x j : ℝ) :=
              finMax_eq_of_eqOn a _ fun j hj => by
                simp [xz, Finset.ne_of_mem_erase hj]
            rw [h1, h2]
          _ = max (z : ℝ) (finMax a (S.erase i₀) fun j => (x j : ℝ)) := by
            rw [max_eq_right z.2.1]
      rw [hfin]
      dsimp only [g]
      rw [max_left_comm, max_comm]
    · dsimp only [g]
      rw [Finset.erase_eq_of_notMem hi]
      congr 1
      exact finMax_eq_of_eqOn a S fun j hj => by
        have hne : j ≠ i₀ := fun h => hi (h ▸ hj)
        simp [hne]
  have hmin_eq : ∀ z : Set.Icc a b,
      E.evalVal (Function.update x i₀ z) =
        min (finMin b T₀ g) (max (finMin b T₁ g) (z : ℝ)) := by
    intro z
    dsimp only [evalVal]
    rw [huniv, finMin_union]
    have hT0 : (finMin b T₀ fun S =>
          max (E.alpha S) (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ))) =
        finMin b T₀ g :=
      finMin_eq_of_eqOn b fun S hS => by
        have hi : i₀ ∉ S := (Finset.mem_filter.mp hS).2
        rw [hxz z S]
        split_ifs
        rfl
    have hT1 : (finMin b T₁ fun S =>
          max (E.alpha S) (finMax a S fun j => ((Function.update x i₀ z j : Set.Icc a b) : ℝ))) =
        max (finMin b T₁ g) (z : ℝ) := by
      rw [← finMin_max_right b T₁ g z.2.2]
      exact finMin_eq_of_eqOn b fun S hS => by
        have hi : i₀ ∈ S := (Finset.mem_filter.mp hS).2
        rw [hxz z S]
        split_ifs
        rfl
    rw [hT0, hT1]
  have hb_eq : E.evalVal (Function.update x i₀ ⟨b, hab, le_rfl⟩) = finMin b T₀ g := by
    rw [hmin_eq ⟨b, hab, le_rfl⟩]
    have hM1 : finMin b T₁ g ≤ b := finMin_le_base b T₁ g
    have hM0 : finMin b T₀ g ≤ b := finMin_le_base b T₀ g
    dsimp only
    rw [max_eq_right hM1, min_eq_left hM0]
  have ha_eq : E.evalVal (Function.update x i₀ ⟨a, le_rfl, hab⟩) =
      min (finMin b T₀ g) (finMin b T₁ g) := by
    rw [hmin_eq ⟨a, le_rfl, hab⟩]
    have ha_M1 : a ≤ finMin b T₁ g := le_finMin hab fun S _ =>
      le_max_of_le_left (E.mem_Icc S).1
    dsimp only
    rw [max_eq_left ha_M1]
  rw [hmin_eq t, hb_eq, ha_eq]
  rcases le_total (finMin b T₀ g) (finMin b T₁ g) with h01 | h10
  · rw [min_eq_left h01, min_eq_left (h01.trans (le_max_left _ _)),
      min_eq_left (le_max_left _ _)]
  · rw [min_eq_right h10]

end Eval

end MoulinScheme

section Characterization

variable {ι : Type*} [Finite ι] [Nonempty ι] {a b : ℝ}

omit [Finite ι] [Nonempty ι] in
private lemma sp_le_of_deterministic {ι G : Type*} [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (x : ι → G) (i : ι) (z : G) :
    dist (f x) (x i) ≤ dist (f (Function.update x i z)) (x i) := by
  simpa only [dist_comm] using (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp x i z

omit [Finite ι] [Nonempty ι] in
private lemma coord_mono_of_sp [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (x : ι → Set.Icc a b) (i : ι) {z₁ z₂ : Set.Icc a b} (hz : (z₁ : ℝ) ≤ (z₂ : ℝ)) :
    (f (Function.update x i z₁) : ℝ) ≤ (f (Function.update x i z₂) : ℝ) := by
  rcases hz.eq_or_lt with hzeq | hzlt
  · rw [Subtype.ext hzeq]
  have hsp := sp_le_of_deterministic hf_sp
  let x₁ := Function.update x i z₁
  let x₂ := Function.update x i z₂
  have h1 : |(f x₁ : ℝ) - (z₁ : ℝ)| ≤ |(f x₂ : ℝ) - (z₁ : ℝ)| := by
    have := hsp x₁ i z₂
    have hx2 : Function.update x₁ i z₂ = x₂ := by simp [x₁, x₂]
    simpa [x₁, x₂, hx2, Subtype.dist_eq, Real.dist_eq] using this
  have h2 : |(f x₂ : ℝ) - (z₂ : ℝ)| ≤ |(f x₁ : ℝ) - (z₂ : ℝ)| := by
    have := hsp x₂ i z₁
    have hx1 : Function.update x₂ i z₁ = x₁ := by simp [x₁, x₂]
    simpa [x₁, x₂, hx1, Subtype.dist_eq, Real.dist_eq] using this
  have hsq1 : ((f x₁ : ℝ) - (z₁ : ℝ)) ^ 2 ≤ ((f x₂ : ℝ) - (z₁ : ℝ)) ^ 2 := by
    simpa [sq_le_sq] using h1
  have hsq2 : ((f x₂ : ℝ) - (z₂ : ℝ)) ^ 2 ≤ ((f x₁ : ℝ) - (z₂ : ℝ)) ^ 2 := by
    simpa [sq_le_sq] using h2
  dsimp only [x₁, x₂] at hsq1 hsq2
  nlinarith

omit [Nonempty ι] in
private lemma profile_mono_of_sp [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {x y : ι → Set.Icc a b} (hxy : ∀ i, (x i : ℝ) ≤ (y i : ℝ)) :
    (f x : ℝ) ≤ (f y : ℝ) := by
  classical
  let _ := Fintype.ofFinite ι
  let m : Finset ι → ι → Set.Icc a b := fun S i => if i ∈ S then y i else x i
  have hm_mono : ∀ S : Finset ι, (f (m ∅) : ℝ) ≤ (f (m S) : ℝ) := by
    intro S
    induction S using Finset.induction with
    | empty => exact le_rfl
    | insert i S hi ih =>
      refine ih.trans ?_
      have hupd1 : m S = Function.update (m S) i (x i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [m, hi]
        · simp [m, hj]
      have hupd2 : m (insert i S) = Function.update (m S) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [m]
        · simp [m, hj]
      rw [hupd1, hupd2]
      exact coord_mono_of_sp hf_sp (m S) i (hxy i)
  have hx_eq : m ∅ = x := by funext i; simp [m]
  have hy_eq : m Finset.univ = y := by funext i; simp [m]
  simpa [hx_eq, hy_eq] using hm_mono Finset.univ

omit [Nonempty ι] in
private lemma pareto_bounds_of_sp [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) {c d : Set.Icc a b}
    (hc : ∀ i, (c : ℝ) ≤ (x i : ℝ)) (hd : ∀ i, (x i : ℝ) ≤ (d : ℝ)) :
    (c : ℝ) ≤ (f x : ℝ) ∧ (f x : ℝ) ≤ (d : ℝ) := by
  refine ⟨?_, ?_⟩
  · have := profile_mono_of_sp hf_sp hc
    simpa [hf_unan c] using this
  · have := profile_mono_of_sp hf_sp hd
    simpa [hf_unan d] using this

omit [Nonempty ι] in
private lemma no_jump_at_midpoint [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) {c η w t : ℝ} (hη : 0 < η)
    (hw_mem : w ∈ Set.Icc a b) (ht_mem : t ∈ Set.Icc a b)
    (hm1_mem : c - η ∈ Set.Icc a b) (hm2_mem : c + η ∈ Set.Icc a b)
    (hw_lo : c - η / 2 < w) (_hw_c : w ≤ c) (_hc_t : c ≤ t) (ht_hi : t < c + η / 2)
    (hfw_lo : c - 9 * η < (f (Function.update x i₀ ⟨w, hw_mem⟩) : ℝ))
    (hfw_hi : (f (Function.update x i₀ ⟨w, hw_mem⟩) : ℝ) ≤ c - 7 * η)
    (hft_lo : c + 8 * η ≤ (f (Function.update x i₀ ⟨t, ht_mem⟩) : ℝ)) :
    False := by
  classical
  let _ := Fintype.ofFinite ι
  have hsp := sp_le_of_deterministic hf_sp
  let wPt : Set.Icc a b := ⟨w, hw_mem⟩
  let tPt : Set.Icc a b := ⟨t, ht_mem⟩
  let m₁ : Set.Icc a b := ⟨c - η, hm1_mem⟩
  let m₂ : Set.Icc a b := ⟨c + η, hm2_mem⟩
  let repLow : Finset ι → ι → Set.Icc a b :=
    fun S k => if k ∈ S ∧ (x k : ℝ) < c - η then m₁ else x k
  have hphase1 : ∀ S : Finset ι, i₀ ∉ S →
      c - 9 * η < (f (Function.update (repLow S) i₀ wPt) : ℝ) ∧
      (f (Function.update (repLow S) i₀ wPt) : ℝ) ≤ c - 7 * η ∧
      c + 8 * η ≤ (f (Function.update (repLow S) i₀ tPt) : ℝ) := by
    intro S hiS
    induction S using Finset.induction with
    | empty =>
      have h0 : repLow ∅ = x := by funext k; simp [repLow]
      simpa [h0] using ⟨hfw_lo, hfw_hi, hft_lo⟩
    | insert j S hj ih =>
      have hji₀ : j ≠ i₀ := fun h => hiS (h ▸ Finset.mem_insert_self _ _)
      have hiS' : i₀ ∉ S := fun h => hiS (Finset.mem_insert_of_mem h)
      obtain ⟨ih_lo, ih_hi, ih_t⟩ := ih hiS'
      by_cases hj_low : (x j : ℝ) < c - η
      · have hupd_w : Function.update (repLow (insert j S)) i₀ wPt =
            Function.update (Function.update (repLow S) i₀ wPt) j m₁ := by
          funext k
          by_cases hki : k = i₀
          · subst hki; simp [Function.update, hji₀.symm]
          · by_cases hkj : k = j
            · subst hkj; simp [repLow, Function.update, hki, hj_low]
            · simp [repLow, Function.update, hki, hkj]
        have hupd_t : Function.update (repLow (insert j S)) i₀ tPt =
            Function.update (Function.update (repLow S) i₀ tPt) j m₁ := by
          funext k
          by_cases hki : k = i₀
          · subst hki; simp [Function.update, hji₀.symm]
          · by_cases hkj : k = j
            · subst hkj; simp [repLow, Function.update, hki, hj_low]
            · simp [repLow, Function.update, hki, hkj]
        have hbase_w : Function.update (repLow S) i₀ wPt =
            Function.update (Function.update (repLow S) i₀ wPt) j (x j) := by
          funext k
          by_cases hki : k = i₀
          · subst hki; simp [Function.update, hji₀.symm]
          · by_cases hkj : k = j
            · subst hkj; simp [repLow, Function.update, hki, hj]
            · simp [Function.update, hkj]
        have hbase_t : Function.update (repLow S) i₀ tPt =
            Function.update (Function.update (repLow S) i₀ tPt) j (x j) := by
          funext k
          by_cases hki : k = i₀
          · subst hki; simp [Function.update, hji₀.symm]
          · by_cases hkj : k = j
            · subst hkj; simp [repLow, Function.update, hki, hj]
            · simp [Function.update, hkj]
        have ht_new : c + 8 * η ≤ (f (Function.update (repLow (insert j S)) i₀ tPt) : ℝ) := by
          refine ih_t.trans ?_
          rw [hupd_t]
          conv_lhs => rw [hbase_t]
          exact coord_mono_of_sp hf_sp _ j
            (show ((x j : Set.Icc a b) : ℝ) ≤ (m₁ : ℝ) from hj_low.le)
        have hw_new_lo : c - 9 * η < (f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) := by
          refine lt_of_lt_of_le ih_lo ?_
          rw [hupd_w]
          conv_lhs => rw [hbase_w]
          exact coord_mono_of_sp hf_sp _ j
            (show ((x j : Set.Icc a b) : ℝ) ≤ (m₁ : ℝ) from hj_low.le)
        have hj_sp : |(f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) - (m₁ : ℝ)| ≤
            |(f (Function.update (repLow S) i₀ wPt) : ℝ) - (m₁ : ℝ)| := by
          have h1 := hsp (Function.update (repLow (insert j S)) i₀ wPt) j (x j)
          have hrev : Function.update (Function.update (repLow (insert j S)) i₀ wPt) j (x j) =
              Function.update (repLow S) i₀ wPt := by
            funext k
            by_cases hkj : k = j
            · subst hkj; simp [repLow, Function.update, hji₀, hj]
            · by_cases hki : k = i₀
              · subst hki; simp [Function.update, hji₀.symm]
              · simp [repLow, Function.update, hki, hkj]
          rw [hrev] at h1
          have hj_val : Function.update (repLow (insert j S)) i₀ wPt j = m₁ := by
            simp [repLow, Function.update, hji₀, hj_low]
          simpa [hj_val, Subtype.dist_eq, Real.dist_eq] using h1
        have hw_new_cap : (f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) < c + 7 * η := by
          have hdist : |(f (Function.update (repLow S) i₀ wPt) : ℝ) - (m₁ : ℝ)| < 8 * η := by
            dsimp only [m₁]
            rw [abs_of_nonpos (by linarith)]
            linarith
          have hlt' : |(f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) - (m₁ : ℝ)| < 8 * η :=
            hj_sp.trans_lt hdist
          dsimp only [m₁] at hlt'
          linarith [(abs_lt.mp hlt').2]
        have hi0_sp : |(f (Function.update (repLow (insert j S)) i₀ tPt) : ℝ) - t| ≤
            |(f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) - t| := by
          have := hsp (Function.update (repLow (insert j S)) i₀ tPt) i₀ wPt
          have hupd_wt : Function.update (Function.update (repLow (insert j S)) i₀ tPt) i₀ wPt =
              Function.update (repLow (insert j S)) i₀ wPt := by simp
          simpa [tPt, hupd_wt, Subtype.dist_eq, Real.dist_eq] using this
        have hw_lt_t : (f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) < t := by
          by_contra hge
          have h1 : (f (Function.update (repLow (insert j S)) i₀ tPt) : ℝ) - t ≤
              (f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) - t := by
            rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hi0_sp
          linarith
        have hw_new_hi : (f (Function.update (repLow (insert j S)) i₀ wPt) : ℝ) ≤ c - 7 * η := by
          rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at hi0_sp
          linarith
        exact ⟨hw_new_lo, hw_new_hi, ht_new⟩
      · have heq : repLow (insert j S) = repLow S := by
          funext k
          by_cases hkj : k = j
          · subst hkj; simp [repLow, hj_low]
          · simp [repLow, hkj]
        rw [heq]
        exact ⟨ih_lo, ih_hi, ih_t⟩
  have hf_x1 : (f (Function.update (repLow (Finset.univ.erase i₀)) i₀ wPt) : ℝ) ≤ c - 7 * η :=
    (hphase1 (Finset.univ.erase i₀) (Finset.notMem_erase _ _)).2.1
  let x₁ := Function.update (repLow (Finset.univ.erase i₀)) i₀ wPt
  let x₂ : ι → Set.Icc a b := fun k => if c + η < (x₁ k : ℝ) then m₂ else x₁ k
  have hx21 : ∀ k, (x₂ k : ℝ) ≤ (x₁ k : ℝ) := fun k => by
    dsimp only [x₂]
    split_ifs with h
    · exact h.le
    · exact le_rfl
  have hf_x2 : (f x₂ : ℝ) ≤ c - 7 * η := (profile_mono_of_sp hf_sp hx21).trans hf_x1
  have hx2_lo : ∀ k, (m₁ : ℝ) ≤ (x₂ k : ℝ) := by
    intro k
    dsimp only [x₂, m₁]
    split_ifs with h
    · dsimp only [m₂]; linarith
    · dsimp only [x₁]
      by_cases hki : k = i₀
      · subst hki; simp only [Function.update_self, wPt]; linarith
      · simp only [Function.update_of_ne hki, repLow, Finset.mem_erase, Ne.eq_def, hki,
          not_false_eq_true, Finset.mem_univ, and_self, true_and]
        split_ifs with hlt
        · exact le_rfl
        · exact not_lt.mp hlt
  have hx2_hi : ∀ k, (x₂ k : ℝ) ≤ (m₂ : ℝ) := fun k => by
    dsimp only [x₂, m₂]
    split_ifs with h
    · exact le_rfl
    · exact not_lt.mp h
  have hpareto := (pareto_bounds_of_sp hf_sp hf_unan x₂ hx2_lo hx2_hi).1
  dsimp only [m₁] at hpareto
  linarith

omit [Nonempty ι] in
private lemma coord_continuous_of_sp [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) :
    Continuous fun t : Set.Icc a b => (f (Function.update x i₀ t) : ℝ) := by
  let g : Set.Icc a b → ℝ := fun t => (f (Function.update x i₀ t) : ℝ)
  have hg_mono : Monotone g := fun s t hst => coord_mono_of_sp hf_sp x i₀ hst
  have hsp := sp_le_of_deterministic hf_sp
  have hg_sp : ∀ s t : Set.Icc a b, |g s - (s : ℝ)| ≤ |g t - (s : ℝ)| := by
    intro s t
    have := hsp (Function.update x i₀ s) i₀ t
    have hupd : Function.update (Function.update x i₀ s) i₀ t = Function.update x i₀ t := by simp
    simpa [g, hupd, Subtype.dist_eq, Real.dist_eq] using this
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  by_contra hnc
  push Not at hnc
  obtain ⟨ε, hε, hδ_all⟩ := hnc
  have hcases : (∀ δ > 0, ∃ t : Set.Icc a b, (t₀ : ℝ) < t ∧ (t : ℝ) < t₀ + δ ∧ g t₀ + ε ≤ g t) ∨
      (∀ δ > 0, ∃ t : Set.Icc a b, (t₀ : ℝ) - δ < t ∧ (t : ℝ) < t₀ ∧ g t + ε ≤ g t₀) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨δ₁, hδ₁, hnoR⟩, ⟨δ₂, hδ₂, hnoL⟩⟩ := hboth
    obtain ⟨t, ht_dist, ht_g⟩ := hδ_all (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
    rw [Subtype.dist_eq, Real.dist_eq] at ht_dist
    rw [Real.dist_eq] at ht_g
    rcases lt_trichotomy (t : ℝ) t₀ with hlt | heq | hgt
    · have ht2 : (t₀ : ℝ) - δ₂ < t := by linarith [(abs_lt.mp ht_dist).1, min_le_right δ₁ δ₂]
      have hgle : g t ≤ g t₀ := hg_mono hlt.le
      have hge : g t + ε ≤ g t₀ := by
        rw [abs_of_nonpos (by linarith)] at ht_g
        linarith
      exact (hnoL t ht2 hlt).not_ge hge
    · have hteq : t = t₀ := Subtype.ext heq
      rw [hteq, sub_self, abs_zero] at ht_g
      linarith
    · have ht1 : (t : ℝ) < t₀ + δ₁ := by linarith [(abs_lt.mp ht_dist).2, min_le_left δ₁ δ₂]
      have hgle : g t₀ ≤ g t := hg_mono hgt.le
      have hge : g t₀ + ε ≤ g t := by
        rw [abs_of_nonneg (by linarith)] at ht_g
        linarith
      exact (hnoR t hgt ht1).not_ge hge
  rcases hcases with hR | hL
  · set u₀ := g t₀ with hu₀_def
    let S := g '' { t : Set.Icc a b | (t₀ : ℝ) < t }
    have hS_ne : S.Nonempty := by
      obtain ⟨t₁, ht₁, _, _⟩ := hR 1 one_pos
      exact ⟨g t₁, t₁, ht₁, rfl⟩
    have hS_lo : ∀ y ∈ S, u₀ + ε ≤ y := by
      rintro y ⟨t, ht, rfl⟩
      obtain ⟨t', ht', ht'lt, ht'g⟩ := hR ((t : ℝ) - t₀) (sub_pos.mpr ht)
      exact ht'g.trans (hg_mono (show (t' : ℝ) ≤ t by linarith))
    set v₀ := sInf S with hv₀_def
    have hu₀_le_v₀ : u₀ + ε ≤ v₀ := le_csInf hS_ne hS_lo
    have hv₀_le_b : v₀ ≤ b := by
      obtain ⟨y, ⟨t, ht, rfl⟩⟩ := hS_ne
      exact (csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨t, ht, rfl⟩).trans (f (Function.update x i₀ t)).2.2
    have hu₀_ge_a : a ≤ u₀ := (f (Function.update x i₀ t₀)).2.1
    have ht₀_eq : (t₀ : ℝ) = (u₀ + v₀) / 2 := by
      rcases lt_trichotomy (t₀ : ℝ) ((u₀ + v₀) / 2) with hlt | heq | hgt
      · obtain ⟨t₁, ht₁, _, _⟩ := hR 1 one_pos
        set t' := ((t₀ : ℝ) + min ((u₀ + v₀) / 2) (t₁ : ℝ)) / 2 with ht'_def
        have hmin_gt : (t₀ : ℝ) < min ((u₀ + v₀) / 2) (t₁ : ℝ) := lt_min hlt ht₁
        have hmin_le_half : min ((u₀ + v₀) / 2) (t₁ : ℝ) ≤ (u₀ + v₀) / 2 := min_le_left _ _
        have hmin_le_t1 : min ((u₀ + v₀) / 2) (t₁ : ℝ) ≤ (t₁ : ℝ) := min_le_right _ _
        have ht'_gt : (t₀ : ℝ) < t' := by linarith
        have ht'_le_t1 : t' ≤ (t₁ : ℝ) := by linarith
        have ht'_lt : t' < (u₀ + v₀) / 2 := by linarith
        have ht'_mem : t' ∈ Set.Icc a b := ⟨t₀.2.1.trans ht'_gt.le, ht'_le_t1.trans t₁.2.2⟩
        have hv_le : v₀ ≤ g ⟨t', ht'_mem⟩ :=
          csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨⟨t', ht'_mem⟩, ht'_gt, rfl⟩
        have hsp' := hg_sp ⟨t', ht'_mem⟩ t₀
        have h1 : v₀ - t' ≤ |g ⟨t', ht'_mem⟩ - t'| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have h2 : |u₀ - t'| < v₀ - t' := abs_lt.mpr ⟨by linarith, by linarith⟩
        linarith
      · exact heq
      · set r := 2 * (t₀ : ℝ) - u₀ - v₀ with hr_def
        have hr : 0 < r := by linarith
        obtain ⟨y, ⟨t, ht_gt, rfl⟩, hy_lt⟩ :=
          (csInf_lt_iff ⟨u₀ + ε, hS_lo⟩ hS_ne).mp (show sInf S < v₀ + r by rw [← hv₀_def]; linarith)
        have hv_le : v₀ ≤ g t := csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨t, ht_gt, rfl⟩
        have h1 : |g t - (t₀ : ℝ)| < (t₀ : ℝ) - u₀ :=
          abs_lt.mpr ⟨by linarith, by linarith⟩
        have h2 : |u₀ - (t₀ : ℝ)| = (t₀ : ℝ) - u₀ := by
          rw [abs_of_neg (show u₀ - (t₀ : ℝ) < 0 by linarith)]
          ring
        have hsp' := hg_sp t₀ t
        linarith
    set η := (v₀ - u₀) / 16 with hη_def
    have hη : 0 < η := by linarith
    have htplus_mem : (t₀ : ℝ) + η / 4 ∈ Set.Icc a b :=
      ⟨(t₀.2.1).trans (by linarith), (by linarith : (t₀ : ℝ) + η / 4 ≤ v₀).trans hv₀_le_b⟩
    have hm1_mem : (t₀ : ℝ) - η ∈ Set.Icc a b :=
      ⟨hu₀_ge_a.trans (by linarith), (by linarith : (t₀ : ℝ) - η ≤ t₀).trans t₀.2.2⟩
    have hm2_mem : (t₀ : ℝ) + η ∈ Set.Icc a b :=
      ⟨(t₀.2.1).trans (by linarith), (by linarith : (t₀ : ℝ) + η ≤ v₀).trans hv₀_le_b⟩
    have hft_lo : (t₀ : ℝ) + 8 * η ≤ g ⟨(t₀ : ℝ) + η / 4, htplus_mem⟩ := by
      have hv_eq : v₀ = (t₀ : ℝ) + 8 * η := by linarith
      rw [← hv_eq]
      have htplus_gt : (t₀ : ℝ) < (⟨(t₀ : ℝ) + η / 4, htplus_mem⟩ : Set.Icc a b) := by
        dsimp only
        linarith
      exact csInf_le ⟨u₀ + ε, hS_lo⟩ ⟨⟨(t₀ : ℝ) + η / 4, htplus_mem⟩, htplus_gt, rfl⟩
    exact no_jump_at_midpoint hf_sp hf_unan x i₀ hη t₀.2 htplus_mem hm1_mem hm2_mem
      (by linarith) le_rfl (by linarith) (by linarith)
      (by
        change (t₀ : ℝ) - 9 * η < g t₀
        linarith [hu₀_def])
      (by
        change g t₀ ≤ (t₀ : ℝ) - 7 * η
        linarith [hu₀_def])
      hft_lo
  · set v₀ := g t₀ with hv₀_def
    let S := g '' { t : Set.Icc a b | (t : ℝ) < t₀ }
    have hS_ne : S.Nonempty := by
      obtain ⟨t₁, _, ht₁, _⟩ := hL 1 one_pos
      exact ⟨g t₁, t₁, ht₁, rfl⟩
    have hS_hi : ∀ y ∈ S, y ≤ v₀ - ε := by
      rintro y ⟨t, ht, rfl⟩
      obtain ⟨t', _, ht'lt, ht'g⟩ := hL ((t₀ : ℝ) - t) (sub_pos.mpr ht)
      exact (hg_mono (show (t : ℝ) ≤ t' by linarith)).trans (by linarith)
    set u₀ := sSup S with hu₀_def
    have hu₀_le_v₀ : u₀ ≤ v₀ - ε := csSup_le hS_ne hS_hi
    have hu₀_ge_a : a ≤ u₀ := by
      obtain ⟨y, ⟨t, ht, rfl⟩⟩ := hS_ne
      exact (f (Function.update x i₀ t)).2.1.trans (le_csSup ⟨v₀ - ε, hS_hi⟩ ⟨t, ht, rfl⟩)
    have hv₀_le_b : v₀ ≤ b := (f (Function.update x i₀ t₀)).2.2
    have ht₀_eq : (t₀ : ℝ) = (u₀ + v₀) / 2 := by
      rcases lt_trichotomy (t₀ : ℝ) ((u₀ + v₀) / 2) with hlt | heq | hgt
      · set r := u₀ + v₀ - 2 * (t₀ : ℝ) with hr_def
        have hr : 0 < r := by linarith
        obtain ⟨y, ⟨t, ht_lt, rfl⟩, hy_gt⟩ :=
          (lt_csSup_iff ⟨v₀ - ε, hS_hi⟩ hS_ne).mp (show u₀ - r < sSup S by rw [← hu₀_def]; linarith)
        have hle_u : g t ≤ u₀ := le_csSup ⟨v₀ - ε, hS_hi⟩ ⟨t, ht_lt, rfl⟩
        have h1 : |g t - (t₀ : ℝ)| < v₀ - (t₀ : ℝ) := abs_lt.mpr ⟨by linarith, by linarith⟩
        have h2 : |v₀ - (t₀ : ℝ)| = v₀ - (t₀ : ℝ) := abs_of_pos (by linarith)
        have hsp' := hg_sp t₀ t
        linarith
      · exact heq
      · obtain ⟨t₁, _, ht₁, _⟩ := hL 1 one_pos
        set t' := (max ((u₀ + v₀) / 2) (t₁ : ℝ) + (t₀ : ℝ)) / 2 with ht'_def
        have hmax_lt : max ((u₀ + v₀) / 2) (t₁ : ℝ) < (t₀ : ℝ) := max_lt hgt ht₁
        have hmax_ge_half : (u₀ + v₀) / 2 ≤ max ((u₀ + v₀) / 2) (t₁ : ℝ) := le_max_left _ _
        have hmax_ge_t1 : (t₁ : ℝ) ≤ max ((u₀ + v₀) / 2) (t₁ : ℝ) := le_max_right _ _
        have ht'_lt : t' < (t₀ : ℝ) := by linarith
        have ht'_ge_t1 : (t₁ : ℝ) ≤ t' := by linarith
        have ht'_gt : (u₀ + v₀) / 2 < t' := by linarith
        have ht'_mem : t' ∈ Set.Icc a b := ⟨t₁.2.1.trans ht'_ge_t1, ht'_lt.le.trans t₀.2.2⟩
        have hle_u : g ⟨t', ht'_mem⟩ ≤ u₀ :=
          le_csSup ⟨v₀ - ε, hS_hi⟩ ⟨⟨t', ht'_mem⟩, ht'_lt, rfl⟩
        have hsp' := hg_sp ⟨t', ht'_mem⟩ t₀
        have h1 : t' - u₀ ≤ |g ⟨t', ht'_mem⟩ - t'| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        have h2 : |v₀ - t'| < t' - u₀ := abs_lt.mpr ⟨by linarith, by linarith⟩
        linarith
    set η := (v₀ - u₀) / 16 with hη_def
    have hη : 0 < η := by linarith
    have hm1_mem : (t₀ : ℝ) - η ∈ Set.Icc a b :=
      ⟨hu₀_ge_a.trans (by linarith), (by linarith : (t₀ : ℝ) - η ≤ t₀).trans t₀.2.2⟩
    have hm2_mem : (t₀ : ℝ) + η ∈ Set.Icc a b :=
      ⟨(t₀.2.1).trans (by linarith), (by linarith : (t₀ : ℝ) + η ≤ v₀).trans hv₀_le_b⟩
    obtain ⟨y, ⟨t₁, ht₁_lt, rfl⟩, hy_gt⟩ :=
      (lt_csSup_iff ⟨v₀ - ε, hS_hi⟩ hS_ne).mp (show u₀ - η / 2 < sSup S by rw [← hu₀_def]; linarith)
    set w := max (t₁ : ℝ) ((t₀ : ℝ) - η / 4) with hw_def
    have hw_mem : w ∈ Set.Icc a b :=
      ⟨t₁.2.1.trans (le_max_left _ _), (max_le ht₁_lt.le (by linarith)).trans t₀.2.2⟩
    have hfw_lo : (t₀ : ℝ) - 9 * η < g ⟨w, hw_mem⟩ :=
      (by linarith : (t₀ : ℝ) - 9 * η < g t₁).trans_le
        (hg_mono (show (t₁ : ℝ) ≤ w from le_max_left _ _))
    have hfw_hi : g ⟨w, hw_mem⟩ ≤ (t₀ : ℝ) - 7 * η := by
      have hw_lt : ((⟨w, hw_mem⟩ : Set.Icc a b) : ℝ) < t₀ := by
        dsimp only
        rw [hw_def]
        exact max_lt ht₁_lt (by linarith)
      exact (le_csSup ⟨v₀ - ε, hS_hi⟩ ⟨⟨w, hw_mem⟩, hw_lt, rfl⟩).trans (by linarith)
    exact no_jump_at_midpoint hf_sp hf_unan x i₀ hη hw_mem t₀.2 hm1_mem hm2_mem
      (lt_of_lt_of_le (by linarith) (le_max_right _ _))
      (max_le ht₁_lt.le (by linarith)) le_rfl (by linarith) hfw_lo hfw_hi
      (by
        change (t₀ : ℝ) + 8 * η ≤ g t₀
        linarith [hv₀_def])

omit [Nonempty ι] in
private lemma coord_clamp_eq [DecidableEq ι]
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (hab : a ≤ b) {f : (ι → Set.Icc a b) → Set.Icc a b}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unan : ∀ c : Set.Icc a b, f (fun _ => c) = c)
    (x : ι → Set.Icc a b) (i₀ : ι) (t : Set.Icc a b) :
    (f (Function.update x i₀ t) : ℝ) =
      min (f (Function.update x i₀ ⟨b, hab, le_rfl⟩) : ℝ)
        (max (f (Function.update x i₀ ⟨a, le_rfl, hab⟩) : ℝ) (t : ℝ)) := by
  have hsp := sp_le_of_deterministic hf_sp
  let aPt : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let bPt : Set.Icc a b := ⟨b, hab, le_rfl⟩
  let u : ℝ := (f (Function.update x i₀ aPt) : ℝ)
  let v : ℝ := (f (Function.update x i₀ bPt) : ℝ)
  have huv : u ≤ v := coord_mono_of_sp hf_sp x i₀ hab
  have hgt_a : u ≤ (f (Function.update x i₀ t) : ℝ) := coord_mono_of_sp hf_sp x i₀ t.2.1
  have hlt_b : (f (Function.update x i₀ t) : ℝ) ≤ v := coord_mono_of_sp hf_sp x i₀ t.2.2
  have hg_sp : ∀ s : Set.Icc a b,
      |(f (Function.update x i₀ t) : ℝ) - (t : ℝ)| ≤
        |(f (Function.update x i₀ s) : ℝ) - (t : ℝ)| := by
    intro s
    have := hsp (Function.update x i₀ t) i₀ s
    have hupd : Function.update (Function.update x i₀ t) i₀ s = Function.update x i₀ s := by simp
    simpa [hupd, Subtype.dist_eq, Real.dist_eq] using this
  rcases le_or_gt (t : ℝ) u with htu | hut
  · rw [max_eq_left htu, min_eq_right huv]
    have hsp' := hg_sp aPt
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hsp'
    linarith
  · rcases le_or_gt v (t : ℝ) with hvt | htv
    · rw [max_eq_right (huv.trans hvt), min_eq_left hvt]
      have hsp' := hg_sp bPt
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hsp'
      linarith
    · rw [max_eq_right hut.le, min_eq_right htv.le]
      let g' : ℝ → ℝ := fun r => (f (Function.update x i₀ (Set.projIcc a b hab r)) : ℝ)
      have hg'_cont : Continuous g' :=
        (coord_continuous_of_sp hf_sp hf_unan x i₀).comp continuous_projIcc
      have hg'a : g' a = u := by
        simp only [g', u, Set.projIcc_left, aPt]
      have hg'b : g' b = v := by
        simp only [g', v, Set.projIcc_right, bPt]
      have ht_mem : (t : ℝ) ∈ Set.Icc (g' a) (g' b) := by
        rw [hg'a, hg'b]
        exact ⟨hut.le, htv.le⟩
      obtain ⟨s, hs_mem, hgs⟩ := intermediate_value_Icc hab hg'_cont.continuousOn ht_mem
      have hs_eq : Set.projIcc a b hab s = ⟨s, hs_mem⟩ := Set.projIcc_of_mem hab hs_mem
      have hf_eq : (f (Function.update x i₀ ⟨s, hs_mem⟩) : ℝ) = (t : ℝ) := by
        simpa [g', hs_eq] using hgs
      have hsp' := hg_sp ⟨s, hs_mem⟩
      rw [hf_eq, sub_self, abs_zero] at hsp'
      linarith [abs_nonneg ((f (Function.update x i₀ t) : ℝ) - (t : ℝ)),
        abs_eq_zero.mp (le_antisymm hsp' (abs_nonneg _))]

/-- A deterministic facility-location mechanism on a nonempty closed interval `Set.Icc a b` is
strategyproof and surjective if and only if it is the evaluation map of a `MoulinScheme`. -/
theorem isStrategyProof_and_surjective_iff_exists_moulinScheme
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {a b : ℝ} (hab : a ≤ b)
    [MeasurableSpace (Set.Icc a b)] [OpensMeasurableSpace (Set.Icc a b)]
    (f : (ι → Set.Icc a b) → Set.Icc a b) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f) ↔
      ∃ E : MoulinScheme ι a b, f = E.eval := by
  classical
  constructor
  · rintro ⟨hf_sp, hf_onto⟩
    have hf_unan : ∀ y : Set.Icc a b, f (fun _ => y) = y :=
      unanimous_of_surjective_isStrategyProof hf_sp hf_onto
    let aPt : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let bPt : Set.Icc a b := ⟨b, hab, le_rfl⟩
    let indProf : Finset ι → ι → Set.Icc a b := fun S i => if i ∈ S then aPt else bPt
    let E : MoulinScheme ι a b :=
      { alpha := fun S => (f (indProf S) : ℝ)
        mem_Icc := fun S => (f (indProf S)).2
        antitone := fun S T hST => profile_mono_of_sp hf_sp fun i => by
          by_cases hT : i ∈ T <;> by_cases hS : i ∈ S
          · simp [indProf, hT, hS]
          · simpa [indProf, hT, hS, aPt, bPt] using hab
          · exact absurd (hST hS) hT
          · simp [indProf, hT, hS]
        boundary_empty := by
          have hemp : indProf ∅ = fun _ => bPt := by funext i; simp [indProf]
          rw [hemp, hf_unan]
        boundary_univ := by
          have hun : indProf Finset.univ = fun _ => aPt := by funext i; simp [indProf]
          rw [hun, hf_unan] }
    refine ⟨E, funext fun x => Subtype.ext ?_⟩
    suffices h : ∀ (n : ℕ) (y : ι → Set.Icc a b),
        (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).card = n →
        (f y : ℝ) = E.evalVal y from h _ x rfl
    intro n
    induction n with
    | zero =>
      intro y hcard
      have hemp : (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt) = ∅ :=
        Finset.card_eq_zero.mp hcard
      let S := Finset.univ.filter fun i => y i = aPt
      have hy_eq : y = indProf S := by
        funext i
        by_cases hia : y i = aPt
        · simp [indProf, S, hia]
        · have hib : y i = bPt := by
            by_contra hne
            have hi : i ∈ Finset.univ.filter fun j => y j ≠ aPt ∧ y j ≠ bPt := by
              simp [hia, hne]
            rw [hemp] at hi
            exact Finset.notMem_empty i hi
          simp [indProf, S, hib]
      rw [hy_eq]
      dsimp only [MoulinScheme.evalVal, E]
      refine le_antisymm ?_ ?_
      · refine le_finMin (f (indProf S)).2.2 fun T _ => ?_
        by_cases hTS : T ⊆ S
        · exact le_max_of_le_left (E.antitone hTS)
        · obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hTS
          have hjb : indProf S j = bPt := by
            have hjnot : j ∉ Finset.univ.filter (fun i => y i = aPt) := hjS
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjnot
            simp [indProf, S, hjnot]
          have hle : b ≤ finMax a T fun k => (indProf S k : ℝ) := by
            have := mem_le_finMax a (fun k => (indProf S k : ℝ)) hjT
            simpa [hjb, bPt] using this
          exact le_max_of_le_right ((f (indProf S)).2.2.trans hle)
      · refine (finMin_le b (T := Finset.univ)
          (fun T => max (E.alpha T) (finMax a T fun k => (indProf S k : ℝ)))
          (Finset.mem_univ S)).trans_eq ?_
        have hmax : (finMax a S fun k => (indProf S k : ℝ)) = a := by
          refine le_antisymm (finMax_le le_rfl fun k hk => ?_) (le_finMax a S _)
          simp [indProf, hk, aPt]
        simp [E, hmax, max_eq_left (f (indProf S)).2.1]
    | succ k ih =>
      intro y hcard
      have hne : (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).Nonempty :=
        Finset.card_pos.mp (hcard ▸ Nat.succ_pos k)
      obtain ⟨i₀, hi₀⟩ := hne
      have hi₀_ne := (Finset.mem_filter.mp hi₀).2
      let ya := Function.update y i₀ aPt
      let yb := Function.update y i₀ bPt
      have hsub_a : Finset.univ.filter (fun i => ya i ≠ aPt ∧ ya i ≠ bPt) =
          (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).erase i₀ := by
        ext j
        simp only [ya, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hj : j = i₀
        · subst hj; simp
        · simp [hj]
      have hsub_b : Finset.univ.filter (fun i => yb i ≠ aPt ∧ yb i ≠ bPt) =
          (Finset.univ.filter fun i => y i ≠ aPt ∧ y i ≠ bPt).erase i₀ := by
        ext j
        simp only [yb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hj : j = i₀
        · subst hj; simp
        · simp [hj]
      have hcard_a : (Finset.univ.filter fun i => ya i ≠ aPt ∧ ya i ≠ bPt).card = k := by
        rw [hsub_a, Finset.card_erase_of_mem hi₀, hcard]; simp
      have hcard_b : (Finset.univ.filter fun i => yb i ≠ aPt ∧ yb i ≠ bPt).card = k := by
        rw [hsub_b, Finset.card_erase_of_mem hi₀, hcard]; simp
      have hy_upd : Function.update y i₀ (y i₀) = y := Function.update_eq_self i₀ y
      calc
        (f y : ℝ) = (f (Function.update y i₀ (y i₀)) : ℝ) := by rw [hy_upd]
        _ = min (f yb : ℝ) (max (f ya : ℝ) (y i₀ : ℝ)) :=
          coord_clamp_eq hab hf_sp hf_unan y i₀ (y i₀)
        _ = min (E.evalVal yb) (max (E.evalVal ya) (y i₀ : ℝ)) := by
          rw [ih ya hcard_a, ih yb hcard_b]
        _ = E.evalVal (Function.update y i₀ (y i₀)) := (E.evalVal_update_eq y i₀ (y i₀)).symm
        _ = E.evalVal y := by rw [hy_upd]
  · rintro ⟨E, rfl⟩
    exact ⟨E.eval_isStrategyProof, E.eval_surjective⟩

/-- Transfers a strategyproof mechanism on any metric space `G` that preserves and surjects onto
the image of an isometric embedding `φ : Set.Icc 0 d → G` to a `MoulinScheme ι 0 d`. -/
theorem moulinScheme_of_isometry {ι G : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {d : ℝ} (hd : 0 ≤ d) (φ : Set.Icc (0 : ℝ) d → G) (hφ : Isometry φ)
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_range : ∀ x : ι → G, (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ)
    (hf_onto : ∀ y ∈ Set.range φ, ∃ x : ι → G, (∀ i, x i ∈ Set.range φ) ∧ f x = y) :
    ∃ E : MoulinScheme ι 0 d, ∀ x : ι → Set.Icc (0 : ℝ) d,
      f (fun i => φ (x i)) = φ (E.eval x) := by
  classical
  have hf'_mem : ∀ x : ι → Set.Icc (0 : ℝ) d, f (fun i => φ (x i)) ∈ Set.range φ :=
    fun x => hf_range (fun i => φ (x i)) fun i => ⟨x i, rfl⟩
  let f' : (ι → Set.Icc (0 : ℝ) d) → Set.Icc (0 : ℝ) d :=
    fun x => Classical.choose (hf'_mem x)
  have hf'_spec : ∀ x, φ (f' x) = f (fun i => φ (x i)) :=
    fun x => Classical.choose_spec (hf'_mem x)
  have hf'_sp : (Mechanism.deterministic f').IsStrategyProof := by
    rw [Mechanism.isStrategyProof_deterministic_iff]
    intro x i z
    have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp (fun j => φ (x j)) i (φ z)
    have hupd : Function.update (fun j => φ (x j)) i (φ z) =
        fun j => φ (Function.update x i z j) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hupd, ← hf'_spec x, ← hf'_spec (Function.update x i z)] at hsp
    simpa only [hφ.dist_eq] using hsp
  have hf'_onto : Function.Surjective f' := by
    intro y
    obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := hf_onto (φ y) ⟨y, rfl⟩
    let x : ι → Set.Icc (0 : ℝ) d := fun i => Classical.choose (hx₀_mem i)
    have hx_eq : (fun i => φ (x i)) = x₀ := funext fun i => Classical.choose_spec (hx₀_mem i)
    refine ⟨x, hφ.injective ?_⟩
    rw [hf'_spec x, hx_eq, hx₀_eq]
  obtain ⟨E, hE⟩ :=
    (isStrategyProof_and_surjective_iff_exists_moulinScheme hd f').mp ⟨hf'_sp, hf'_onto⟩
  refine ⟨E, fun x => ?_⟩
  rw [← hf'_spec x, hE]

/-- Explicit two-agent formula for a `MoulinScheme (Fin 2) a b`: `(E.eval x : ℝ)` equals
`min (max (E.alpha {0}) (x 0 : ℝ))` paired with
`min (max (E.alpha {1}) (x 1 : ℝ)) (max (x 0 : ℝ) (x 1 : ℝ))`. -/
theorem moulinScheme_finTwo_eq {a b : ℝ} (E : MoulinScheme (Fin 2) a b)
    (x : Fin 2 → Set.Icc a b) :
    (E.eval x : ℝ) =
      min (max (E.alpha {0}) (x 0 : ℝ))
        (min (max (E.alpha {1}) (x 1 : ℝ)) (max (x 0 : ℝ) (x 1 : ℝ))) := by
  classical
  have huniv_sets : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, Finset.univ} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · right; right; right
      ext i
      fin_cases i <;> simp [h0, h1]
    · right; left
      ext i
      fin_cases i <;> simp [h0, h1]
    · right; right; left
      ext i
      fin_cases i <;> simp [h0, h1]
    · left
      ext i
      fin_cases i <;> simp [h0, h1]
  have hf_emp : max (E.alpha ∅) (finMax a ∅ fun i => (x i : ℝ)) = b := by
    have hab : a ≤ b := (E.mem_Icc ∅).1.trans (E.mem_Icc ∅).2
    simp [E.boundary_empty, finMax, hab]
  have hf_0 : max (E.alpha {0}) (finMax a {0} fun i => (x i : ℝ)) =
      max (E.alpha {0}) (x 0 : ℝ) := by
    have h0 : (finMax a {0} fun i => (x i : ℝ)) = (x 0 : ℝ) := by
      simp [finMax, max_eq_left (x 0).2.1]
    rw [h0]
  have hf_1 : max (E.alpha {1}) (finMax a {1} fun i => (x i : ℝ)) =
      max (E.alpha {1}) (x 1 : ℝ) := by
    have h1 : (finMax a {1} fun i => (x i : ℝ)) = (x 1 : ℝ) := by
      simp [finMax, max_eq_left (x 1).2.1]
    rw [h1]
  have hf_u : max (E.alpha Finset.univ) (finMax a Finset.univ fun i => (x i : ℝ)) =
      max (x 0 : ℝ) (x 1 : ℝ) := by
    have hu : (finMax a Finset.univ fun i => (x i : ℝ)) = max (x 0 : ℝ) (x 1 : ℝ) := by
      refine le_antisymm ?_ ?_
      · refine finMax_le (le_max_of_le_left (x 0).2.1) fun i _ => ?_
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      · exact max_le
          (mem_le_finMax a (fun i => (x i : ℝ)) (Finset.mem_univ 0))
          (mem_le_finMax a (fun i => (x i : ℝ)) (Finset.mem_univ 1))
    rw [E.boundary_univ, hu, max_eq_right (le_max_of_le_left (x 0).2.1)]
  rw [MoulinScheme.eval_coe]
  dsimp only [MoulinScheme.evalVal, finMin]
  rw [huniv_sets]
  have hmem0 : ({0} : Finset (Fin 2)) ∉ ({({1} : Finset (Fin 2)), Finset.univ} : Finset _) := by
    decide
  have hmem1 : ({1} : Finset (Fin 2)) ∉ ({Finset.univ} : Finset _) := by decide
  have hmemE : (∅ : Finset (Fin 2)) ∉ ({({0} : Finset (Fin 2)), {1}, Finset.univ} : Finset _) := by
    decide
  rw [Finset.fold_insert hmemE, Finset.fold_insert hmem0, Finset.fold_insert hmem1,
    Finset.fold_singleton, hf_emp, hf_0, hf_1, hf_u]
  have hmax_b : max (x 0 : ℝ) (x 1 : ℝ) ≤ b := max_le (x 0).2.2 (x 1).2.2
  rw [min_eq_left hmax_b, min_eq_right]
  exact min_le_of_left_le (max_le (E.mem_Icc {0}).2 (x 0).2.2)

end Characterization

end Moulin

end Cslib.GameTheory.FacilityLocation
