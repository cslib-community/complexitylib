/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Optimization.FiniteMinPlus
public import Mathlib.Data.List.Sublists
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-!
# Exact finite fixed-effects sign audits

Rational observations, actual retained sublists and within-group centering for
[XuGaoHu2027], equation (2) and Theorem 4.1 (PDF p. 9). Empty and singleton
groups contribute zero. `audit` computes a first nonpositive crossing and retains
the observations chosen in each group. Among equal cross-scatters it maximizes
regressor scatter, so a nonsingular minimizer is recovered when one exists.

The slope here is the within-group ratio in equation (2). `dummy_normal_equation` and
`pooled_normal_equation` verify the refitted group-dummy and regressor normal
equations. A full matrix-design uniqueness bridge is not asserted. The implementation
uses shared arrays but does not trim the group curves or double the search cap;
no resource bound is claimed for this implementation.
-/

public section

namespace Cslib.LeastSquares.FixedEffects

open FiniteMinPlus

/-- One rational regressor and one rational response. -/
abbrev Point := ℚ × ℚ

/-- Recomputed group mean, with value zero for an empty group. -/
@[expose] def mean (f : Point → ℚ) (g : List Point) : ℚ :=
  (g.map f).sum / g.length

/-- Centered cross-scatter, including the empty and singleton cases. -/
@[expose] def cross (g : List Point) : ℚ :=
  (g.map fun p => (p.1 - mean Prod.fst g) * (p.2 - mean Prod.snd g)).sum

/-- Centered regressor scatter. -/
@[expose] def variance (g : List Point) : ℚ :=
  (g.map fun p => (p.1 - mean Prod.fst g) ^ 2).sum

/-- Empty groups disappear and contribute no scatter. -/
theorem empty_scatter : cross [] = 0 ∧ variance [] = 0 := by
  simp [cross, variance]

/-- A singleton has no within-group variation. -/
theorem singleton_scatter (p : Point) : cross [p] = 0 ∧ variance [p] = 0 := by
  simp [cross, variance, mean]

/-- Within-group scatter is always nonnegative. -/
theorem variance_nonneg (g : List Point) : 0 ≤ variance g := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hz
  exact sq_nonneg _

/-- A singular group has zero cross-scatter, as used in Theorem 4.1. -/
theorem cross_eq_zero_of_variance_eq_zero (g : List Point) (hv : variance g = 0) :
    cross g = 0 := by
  have hz : ∀ p ∈ g, p.1 - mean Prod.fst g = 0 := by
    intro p hp
    have hsq : (p.1 - mean Prod.fst g) ^ 2 = 0 :=
      List.all_zero_of_le_zero_le_of_sum_eq_zero
        (fun z hz => by obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz; exact sq_nonneg _)
        hv (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact (sq_eq_zero_iff).mp hsq
  apply List.sum_eq_zero
  intro z hz'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
  rw [hz p hp, zero_mul]


/-- Recentring makes each within-group regressor or response sum zero. -/
theorem centered_sum (f : Point → ℚ) (g : List Point) :
    (g.map fun p => f p - mean f g).sum = 0 := by
  simp only [sub_eq_add_neg, List.sum_map_add, List.map_const', List.sum_replicate,
    nsmul_eq_mul, mean]
  by_cases h : (g.length : ℚ) = 0
  · have hg : g = [] := List.length_eq_zero_iff.mp (by exact_mod_cast h)
    subst g
    simp
  · field_simp
    ring

/-- The centered scatter equals the running-sum formula used by the enumerator. -/
theorem cross_running_sums (g : List Point) :
    cross g = (g.map fun p => p.1 * p.2).sum -
      (g.map Prod.fst).sum * (g.map Prod.snd).sum / g.length := by
  have he : (fun p : Point => (p.1 - mean Prod.fst g) * (p.2 - mean Prod.snd g)) =
      (fun p => p.1 * p.2 + (-mean Prod.fst g) * p.2 +
        (-mean Prod.snd g) * p.1 + mean Prod.fst g * mean Prod.snd g) := by
    funext p
    ring
  rw [cross, he]
  simp only [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate,
    nsmul_eq_mul, mean]
  by_cases h : (g.length : ℚ) = 0
  · have hg : g = [] := List.length_eq_zero_iff.mp (by exact_mod_cast h)
    subst g
    simp
  · field_simp
    ring

/-- The regressor scatter also has a running-sum formula. -/
theorem variance_running_sums (g : List Point) :
    variance g = (g.map fun p => p.1 ^ 2).sum - (g.map Prod.fst).sum ^ 2 / g.length := by
  have he : (fun p : Point => (p.1 - mean Prod.fst g) ^ 2) =
      (fun p => p.1 ^ 2 + (-2 * mean Prod.fst g) * p.1 + mean Prod.fst g ^ 2) := by
    funext p
    ring
  rw [variance, he]
  simp only [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate,
    nsmul_eq_mul, mean]
  by_cases h : (g.length : ℚ) = 0
  · have hg : g = [] := List.length_eq_zero_iff.mp (by exact_mod_cast h)
    subst g
    simp
  · field_simp
    ring

/-- Refit the dummy coefficient separately for each retained group. -/
@[expose] def intercept (b : ℚ) (g : List Point) : ℚ :=
  mean Prod.snd g - b * mean Prod.fst g

/-- Every retained group's refitted residuals satisfy its dummy normal equation. -/
theorem dummy_normal_equation (b : ℚ) (g : List Point) :
    (g.map fun p => p.2 - intercept b g - b * p.1).sum = 0 := by
  have he : (fun p : Point => p.2 - intercept b g - b * p.1) =
      (fun p => (p.2 - mean Prod.snd g) + (-b) * (p.1 - mean Prod.fst g)) := by
    funext p
    dsimp only [intercept]
    ring
  rw [he, List.sum_map_add, List.sum_map_mul_left, centered_sum, centered_sum]
  ring

/-- The regressor normal-equation residual splits additively over groups. -/
theorem group_regressor_residual (b : ℚ) (g : List Point) :
    (g.map fun p => p.1 * (p.2 - intercept b g - b * p.1)).sum =
      cross g - b * variance g := by
  have he : (fun p : Point => p.1 * (p.2 - intercept b g - b * p.1)) =
      (fun p => p.1 * p.2 + (-intercept b g) * p.1 + (-b) * p.1 ^ 2) := by
    funext p
    ring
  rw [he, List.sum_map_add, List.sum_map_add, List.sum_map_mul_left,
    List.sum_map_mul_left, cross_running_sums, variance_running_sums]
  dsimp only [intercept, mean]
  ring

/-- A retained group and the number of its removed observations. -/
structure Choice where
  /-- Exact natural deletion count. -/
  deleted : ℕ
  /-- Actual retained observations in their original order. -/
  kept : List Point
  deriving DecidableEq, Repr

/-- Enumerate all actual subsets, retaining multiplicities of repeated observations. -/
@[expose] def choices (g : List Point) : List Choice :=
  g.sublists.map fun s => ⟨g.length - s.length, s⟩

/-- Membership means actual sample removal, with the exact deletion count. -/
theorem mem_choices (g : List Point) (a : Choice) :
    a ∈ choices g ↔ List.Sublist a.kept g ∧ a.deleted = g.length - a.kept.length := by
  simp only [choices, List.mem_map, List.mem_sublists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hs, rfl⟩
  · rintro ⟨h, he⟩
    exact ⟨a.kept, h, by cases a; simp_all⟩

/-- Actual groupwise removal plans for this input. -/
@[expose] def Valid (groups : List (List Point)) (p : List Choice) : Prop :=
  Admissible (groups.map choices) p

/-- Total removed observations. -/
@[expose] def deletions (p : List Choice) : ℕ := total Choice.deleted p

/-- Additive fixed-effects numerator. -/
@[expose] def numerator (p : List Choice) : ℚ := total (cross ∘ Choice.kept) p

/-- Additive fixed-effects denominator. -/
@[expose] def denominator (p : List Choice) : ℚ := total (variance ∘ Choice.kept) p

/-- Equation (2); a slope target is used only with a positive denominator. -/
@[expose] def slope (p : List Choice) : ℚ := numerator p / denominator p

/-- Nonsingular, sign-reversing retained data. -/
@[expose] def Feasible (groups : List (List Point)) (p : List Choice) : Prop :=
  Valid groups p ∧ 0 < denominator p ∧ slope p ≤ 0

/-- Sign reversal is exactly a nonpositive numerator for nonsingular retained data. -/
theorem slope_nonpos_iff (p : List Choice) (hv : 0 < denominator p) :
    slope p ≤ 0 ↔ numerator p ≤ 0 := by
  exact (div_le_iff₀ hv).trans (by simp)


/-- Equation (2) solves the pooled regressor normal equation, with every
nonempty retained group's dummy refitted by `intercept`. Empty groups contribute zero. -/
theorem pooled_normal_equation (p : List Choice) (hv : 0 < denominator p) :
    (p.map fun a =>
      (a.kept.map fun z => z.1 *
        (z.2 - intercept (slope p) a.kept - slope p * z.1)).sum).sum = 0 := by
  simp_rw [group_regressor_residual]
  have he : (fun a : Choice => cross a.kept - slope p * variance a.kept) =
      (fun a => cross a.kept + (-slope p) * variance a.kept) := by
    funext a
    ring
  rw [he, List.sum_map_add, List.sum_map_mul_left]
  change numerator p + (-slope p) * denominator p = 0
  dsimp only [slope]
  field_simp
  ring

/-- Lexicographic objective: minimize cross-scatter, then maximize x-scatter.
The tie-break prevents returning a singular plan when a nonsingular minimizer exists. -/
@[expose] def key (a : Choice) : ℚ ×ₗ ℚ :=
  toLex (cross a.kept, -variance a.kept)

/-- The additive lexicographic score has the claimed components. -/
theorem total_key (p : List Choice) :
    total key p = toLex (numerator p, -denominator p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change key a + total key p = _
    rw [ih]
    change toLex (_, _) = toLex (_, _)
    simp only [numerator, denominator, total, List.map_cons, List.sum_cons,
      Function.comp_apply, key, neg_add]
    rfl

/-- Nonnegativity of the total regressor scatter, including an empty panel. -/
theorem denominator_nonneg (p : List Choice) : 0 ≤ denominator p := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  exact variance_nonneg _

/-- Zero total scatter forces a zero total numerator. -/
theorem numerator_eq_zero_of_denominator_eq_zero (p : List Choice)
    (hv : denominator p = 0) : numerator p = 0 := by
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  apply cross_eq_zero_of_variance_eq_zero
  exact List.all_zero_of_le_zero_le_of_sum_eq_zero
    (fun z hz => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
      exact variance_nonneg _) hv (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- The lexicographic tie-break does not change which costs cross zero. -/
theorem key_nonpos_iff (p : List Choice) : total key p ≤ 0 ↔ numerator p ≤ 0 := by
  rw [total_key, Prod.Lex.le_iff]
  change numerator p < 0 ∨ numerator p = 0 ∧ -denominator p ≤ 0 ↔ _
  have := denominator_nonneg p
  constructor
  · rintro (h | ⟨h, _⟩) <;> linarith
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, neg_nonpos.mpr this⟩

/-- Number of input observations, including empty groups. -/
@[expose] def sampleSize (groups : List (List Point)) : ℕ := total List.length groups

/-- Actual retained sample counts partition the input count into kept and removed data. -/
theorem deletion_accounting (groups : List (List Point)) (p : List Choice)
    (hp : Valid groups p) :
    deletions p + total (List.length ∘ Choice.kept) p = sampleSize groups := by
  induction groups generalizing p with
  | nil =>
    cases p with
    | nil => rfl
    | cons => cases hp
  | cons g groups ih =>
    cases p with
    | nil => cases hp
    | cons a p =>
      obtain ⟨ha, htail⟩ := List.forall₂_cons.mp hp
      obtain ⟨hsub, hdel⟩ := (mem_choices g a).mp ha
      have hlen := hsub.length_le
      have ht := ih p htail
      change a.deleted + deletions p +
        (a.kept.length + total (List.length ∘ Choice.kept) p) = g.length + sampleSize groups
      omega

/-- Compute the exact first crossing and its actual retained data. -/
@[expose] def audit (groups : List (List Point)) : Option (List Choice) :=
  memoFirstCrossing Choice.deleted key (groups.map choices) (sampleSize groups)

/-- The executable table has exactly the reference recurrence's witnesses. -/
theorem audit_eq (groups : List (List Point)) :
    audit groups = firstCrossing Choice.deleted key (groups.map choices) (sampleSize groups) :=
  memoFirstCrossing_eq _ _ _ _

/-- The first crossing is a lower bound for every nonsingular successful removal plan. -/
theorem audit_lower_bound (groups : List (List Point)) (p : List Choice)
    (hp : audit groups = some p) :
    Valid groups p ∧ numerator p ≤ 0 ∧
      ∀ q, Feasible groups q → deletions p ≤ deletions q := by
  rw [audit_eq] at hp
  obtain ⟨hv, _, hs, hmin⟩ := firstCrossing_spec _ _ _ _ _ hp
  refine ⟨hv, (key_nonpos_iff p).mp hs, ?_⟩
  intro q hq
  exact hmin q hq.1 ((key_nonpos_iff q).mpr ((slope_nonpos_iff q hq.2.1).mp hq.2.2))

/-- Under nondegeneracy the computed first crossing is an optimal deletion plan. -/
theorem audit_optimal_of_positive_denominator (groups : List (List Point)) (p : List Choice)
    (hp : audit groups = some p) (hv : 0 < denominator p) :
    Feasible groups p ∧ ∀ q, Feasible groups q → deletions p ≤ deletions q := by
  obtain ⟨hvalid, hs, hmin⟩ := audit_lower_bound groups p hp
  exact ⟨⟨hvalid, hv, (slope_nonpos_iff p hv).mpr hs⟩, hmin⟩

/-- All deletions is always an admissible zero-scatter crossing, even for empty groups. -/
theorem all_deleted (groups : List (List Point)) :
    ∃ p, Valid groups p ∧ deletions p = sampleSize groups ∧ numerator p = 0 := by
  induction groups with
  | nil => exact ⟨[], List.Forall₂.nil, rfl, rfl⟩
  | cons g groups ih =>
    obtain ⟨p, hp, hc, hs⟩ := ih
    refine ⟨⟨g.length, []⟩ :: p, List.Forall₂.cons ?_ hp, ?_, ?_⟩
    · exact (mem_choices ..).mpr ⟨List.nil_sublist _, by simp⟩
    · change g.length + deletions p = g.length + sampleSize groups
      rw [hc]
    · change cross [] + numerator p = 0
      rw [empty_scatter.1, hs, zero_add]

/-- The search always terminates with a crossing; this need not be nonsingular. -/
theorem audit_exists (groups : List (List Point)) : ∃ p, audit groups = some p := by
  cases hp : audit groups with
  | some p => exact ⟨p, rfl⟩
  | none =>
    obtain ⟨p, hv, hc, hs⟩ := all_deleted groups
    rw [audit_eq] at hp
    have hn := (firstCrossing_eq_none Choice.deleted key (groups.map choices)
      (sampleSize groups)).mp hp
    exact False.elim (hn ⟨p, hv, hc.le, (key_nonpos_iff p).mpr hs.le⟩)

/-- The paper's nondegeneracy condition suffices for the computed witness:
if any numerator minimizer at the first crossing is nonsingular, so is the
returned lexicographic minimizer. No nondegeneracy hypothesis is used for the lower bound. -/
theorem audit_optimal_of_nondegenerate (groups : List (List Point)) (p : List Choice)
    (hp : audit groups = some p)
    (hnd : ∃ q, Valid groups q ∧ deletions q = deletions p ∧
      numerator q = numerator p ∧ 0 < denominator q) :
    Feasible groups p ∧ ∀ q, Feasible groups q → deletions p ≤ deletions q := by
  obtain ⟨q, hq, hc, hn, hv⟩ := hnd
  have hmin := firstCrossing_score_minimal Choice.deleted key (groups.map choices)
    (sampleSize groups) p (by simpa only [audit_eq] using hp) q hq hc
  rw [total_key, total_key, Prod.Lex.le_iff] at hmin
  rcases hmin with hlt | ⟨_, hle⟩
  · change numerator p < numerator q at hlt
    rw [hn] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · change -denominator p ≤ -denominator q at hle
    apply audit_optimal_of_positive_denominator groups p hp
    linarith

/-- A strict negative first crossing is automatically nondegenerate. -/
theorem audit_optimal_of_negative_numerator (groups : List (List Point)) (p : List Choice)
    (hp : audit groups = some p) (hs : numerator p < 0) :
    Feasible groups p ∧ ∀ q, Feasible groups q → deletions p ≤ deletions q := by
  apply audit_optimal_of_positive_denominator groups p hp
  have hv := denominator_nonneg p
  have hn : denominator p ≠ 0 := by
    intro hzero
    rw [numerator_eq_zero_of_denominator_eq_zero p hzero] at hs
    exact lt_irrefl _ hs
  exact lt_of_le_of_ne hv (Ne.symm hn)

end Cslib.LeastSquares.FixedEffects
