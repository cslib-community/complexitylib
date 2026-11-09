/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Valiant's depth reduction

A *grading* of a set `E` of edges with `D` levels is a labelling of the vertices by numbers below
`D` that increases along every edge (`IsGrading`). The levels increase along every path, so a path
of edges of `E` has at most `D` vertices; labelling every vertex of a directed acyclic graph by the
number of vertices on a longest path ending at it is a grading, so this is a way of bounding the
depth of the graph. **Valiant's depth reduction** [Valiant1977],
[Jukna, Lemma 1.4][Jukna2012]: if `E` has a grading with `2 ^ k` levels, then for every `r ≤ k`,
removing some `r / k` of the edges leaves edges with a grading with `2 ^ (k - r)` levels
(`IsGrading.exists_sdiff`).

An edge `(u, v)` is in *class* `b` when the levels of `u` and `v` first differ, from the top, at
bit `b` (`InClass`). Each edge is in at most one class, so among `k` classes one has at most `1 / k`
of the edges; deleting bit `b` from every level grades all edges outside class `b` with half the
levels. Repeating `r` times removes at most `r / k` of the edges.

## Main definitions

* `Cslib.IsGrading`: a labelling of the vertices that increases along the edges.

## Main results

* `Cslib.IsGrading.exists_sdiff`: Valiant's depth reduction.

## References

* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open Finset

variable {V : Type*}

/-- `g` grades the edges `E` with `D` levels: its values are below `D`, and it increases along
every edge. -/
def IsGrading (E : Finset (V × V)) (D : ℕ) (g : V → ℕ) : Prop :=
  (∀ v, g v < D) ∧ ∀ e ∈ E, g e.1 < g e.2

namespace IsGrading

variable {E F : Finset (V × V)} {D : ℕ} {g : V → ℕ}

/-- A grading of the edges `E` grades every subset `F ⊆ E`. -/
theorem mono (hg : IsGrading E D g) (hF : F ⊆ E) : IsGrading F D g :=
  ⟨hg.1, fun e he => hg.2 e (hF he)⟩

/-- The levels `a` and `c` first differ, from the top, at bit `b`. -/
private def InClass (b a c : ℕ) : Prop :=
  a / 2 ^ (b + 1) = c / 2 ^ (b + 1) ∧ a / 2 ^ b ≠ c / 2 ^ b

private instance (b a c : ℕ) : Decidable (InClass b a c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two levels first differ at one bit at most. -/
private theorem not_inClass_of_inClass {b b' a c : ℕ} (hb : InClass b a c) (hbb' : b < b') :
    ¬ InClass b' a c := fun hb' => hb'.2 (by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hbb'
  rw [show b + t + 1 = (b + 1) + t by omega, pow_add, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, hb.1])

/-- The level `a` with bit `b` deleted. -/
private def deleteBit (b a : ℕ) : ℕ :=
  a / 2 ^ (b + 1) * 2 ^ b + a % 2 ^ b

/-- Deleting a bit keeps the order of levels that do not first differ at that bit. -/
private theorem deleteBit_lt_deleteBit {b a c : ℕ} (hac : a < c) (hb : ¬ InClass b a c) :
    deleteBit b a < deleteBit b c := by
  have h2 : 0 < 2 ^ b := Nat.pow_pos (by omega)
  have hmod (m : ℕ) : m % 2 ^ b < 2 ^ b := Nat.mod_lt _ h2
  have hdiv (m : ℕ) : m / 2 ^ (b + 1) * 2 = m / 2 ^ b / 2 * 2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rcases Nat.lt_or_ge (a / 2 ^ (b + 1)) (c / 2 ^ (b + 1)) with hlt | hge
  · -- the levels differ above bit `b`
    have := hmod a
    calc deleteBit b a < (a / 2 ^ (b + 1) + 1) * 2 ^ b := by unfold deleteBit; nlinarith
      _ ≤ c / 2 ^ (b + 1) * 2 ^ b := Nat.mul_le_mul_right _ hlt
      _ ≤ deleteBit b c := Nat.le_add_right _ _
  · -- the levels agree down to bit `b`, so they differ below it
    have heq : a / 2 ^ (b + 1) = c / 2 ^ (b + 1) :=
      le_antisymm (Nat.div_le_div_right hac.le) hge
    have hb' : a / 2 ^ b = c / 2 ^ b := by
      by_contra h
      exact hb ⟨heq, h⟩
    have hmodlt : a % 2 ^ b < c % 2 ^ b := by
      have ha := Nat.div_add_mod a (2 ^ b)
      have hc := Nat.div_add_mod c (2 ^ b)
      rw [hb'] at ha
      omega
    unfold deleteBit
    rw [heq]
    omega

/-- Deleting a bit below `k + 1` halves the levels. -/
private theorem deleteBit_lt {b k a : ℕ} (hb : b ≤ k) (ha : a < 2 ^ (k + 1)) :
    deleteBit b a < 2 ^ k := by
  have h2 : 0 < 2 ^ b := Nat.pow_pos (by omega)
  have hq : a / 2 ^ (b + 1) < 2 ^ (k - b) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← pow_add]
    rwa [show k - b + (b + 1) = k + 1 by omega]
  have := Nat.mod_lt a h2
  calc deleteBit b a < (a / 2 ^ (b + 1) + 1) * 2 ^ b := by unfold deleteBit; nlinarith
    _ ≤ 2 ^ (k - b) * 2 ^ b := Nat.mul_le_mul_right _ hq
    _ = 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hb]

/-- **One round of depth reduction**: removing at most `1 / (k + 1)` of the edges halves the
levels. -/
private theorem exists_sdiff_one [DecidableEq V] {k : ℕ} (hg : IsGrading E (2 ^ (k + 1)) g) :
    ∃ F ⊆ E, (k + 1) * #F ≤ #E ∧ ∃ g' : V → ℕ, IsGrading (E \ F) (2 ^ k) g' := by
  -- the classes of edges, one for each bit
  set C : ℕ → Finset (V × V) := fun b => {e ∈ E | InClass b (g e.1) (g e.2)}
  have hdisj : (range (k + 1) : Set ℕ).PairwiseDisjoint C := by
    intro b _ b' _ hbb'
    refine disjoint_left.2 fun e he he' => ?_
    rcases Nat.lt_or_gt_of_ne hbb' with h | h
    · exact not_inClass_of_inClass (mem_filter.1 he).2 h (mem_filter.1 he').2
    · exact not_inClass_of_inClass (mem_filter.1 he').2 h (mem_filter.1 he).2
  have hsum : ∑ b ∈ range (k + 1), #(C b) ≤ #E := by
    rw [← card_biUnion hdisj]
    exact card_le_card (biUnion_subset.2 fun b _ => filter_subset _ _)
  -- the smallest class has at most `1 / (k + 1)` of the edges
  obtain ⟨b, hb, hmin⟩ := exists_min_image (range (k + 1)) (fun b => #(C b))
    (nonempty_range_iff.2 (Nat.succ_ne_zero k))
  have hcard : (k + 1) * #(C b) ≤ #E := by
    refine le_trans ?_ hsum
    simpa using card_nsmul_le_sum (range (k + 1)) (fun b => #(C b)) _ hmin
  refine ⟨C b, filter_subset _ _, hcard, deleteBit b ∘ g, fun v => ?_, fun e he => ?_⟩
  · exact deleteBit_lt (Nat.lt_succ_iff.1 (mem_range.1 hb)) (hg.1 v)
  · obtain ⟨he, hnot⟩ := mem_sdiff.1 he
    exact deleteBit_lt_deleteBit (hg.2 e he) fun h => hnot (mem_filter.2 ⟨he, h⟩)

/-- **Valiant's depth reduction.** If `E` has a grading with `2 ^ k` levels and `r ≤ k`, then
removing at most `r / k` of the edges leaves edges with a grading with `2 ^ (k - r)` levels. -/
theorem exists_sdiff [DecidableEq V] {k r : ℕ} (hg : IsGrading E (2 ^ k) g) (hr : r ≤ k) :
    ∃ F ⊆ E, k * #F ≤ r * #E ∧ ∃ g' : V → ℕ, IsGrading (E \ F) (2 ^ (k - r)) g' := by
  induction r generalizing E g k with
  | zero => exact ⟨∅, empty_subset _, by simp, g, by simpa using hg⟩
  | succ r ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨F₁, hF₁, hcard₁, g₁, hg₁⟩ := exists_sdiff_one hg
    obtain ⟨F₂, hF₂, hcard₂, g₂, hg₂⟩ := ih hg₁ (by omega)
    refine ⟨F₁ ∪ F₂, union_subset hF₁ (hF₂.trans sdiff_subset), ?_, g₂, ?_⟩
    · -- the bound for the union
      have hdisj : Disjoint F₁ F₂ := disjoint_of_subset_right hF₂ disjoint_sdiff
      have hE : #(E \ F₁) + #F₁ = #E := card_sdiff_add_card_eq_card hF₁
      have hy : #F₂ ≤ #(E \ F₁) := card_le_card hF₂
      rw [card_union_of_disjoint hdisj]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · obtain rfl : r = 0 := by omega
        omega
      · -- multiply by `k`; the slack is `(k - r) (#(E \ F₁) - k #F₁) ≥ 0`
        refine Nat.le_of_mul_le_mul_left ?_ hk
        have h₁ : k * #F₁ ≤ #(E \ F₁) := by linarith
        have h₃ : r ≤ k := by omega
        have key : (k + 1) * (k * #F₂) ≤ (k + 1) * (r * #(E \ F₁)) :=
          Nat.mul_le_mul_left _ hcard₂
        have slack : (k - r) * (k * #F₁) ≤ (k - r) * #(E \ F₁) := Nat.mul_le_mul_left _ h₁
        zify [h₃] at slack ⊢
        rw [← hE]
        push_cast
        nlinarith [key, slack]
    · rw [show k + 1 - (r + 1) = k - r by omega,
        show E \ (F₁ ∪ F₂) = (E \ F₁) \ F₂ by ext; simp [and_assoc]]
      exact hg₂

end IsGrading

end Cslib
