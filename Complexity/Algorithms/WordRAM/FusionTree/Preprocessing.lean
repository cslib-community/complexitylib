/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Model
public import Complexity.Algorithms.WordRAM.FusionTree.Parameters

/-!
# Static preprocessing of a whole fusion tree

Every eligible large-width internal node stores the words of its actual classically chosen
`NodeParameters`. All other parameter words are zero. Child minima inherit strict ordering
and full-key bounds from the leaves. Consequently the concrete contiguous encoding needs no
assumed preprocessing header or node-search oracle.

This is a classical static construction. It asserts no RAM preprocessing time, and does not
compose the node query with whole-tree traversal or the small-width binary fallback.

## Main definitions

* `childMinima`: the full keys used by an internal fusion-node query.
* `ParameterEligible`: the actual hypotheses needed to choose fitting node parameters.
* `parameterWords`: one total parameter assignment for the whole tree at each word width.

## Main results

* `childMinima_strictMono`, `childMinima_fit`: leaf invariants imply node-key invariants.
* `parameterWords_node`: the exact chosen witness used in each eligible node header.
* `parameterWords_fit`: every parameter word fits, even for invalid trees and zero width.
* `preprocessed_contentFits`: valid trees with bounded leaves have fitting contents.
* `preprocessed_encoding_exists`: concrete memory, decoding and at most `126n + 18` words.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- A nonempty valid tree's cached minimum is one of its actual leaf keys. -/
private theorem minimum_mem {B : ℕ} {t : Tree} (ht : Tree.Valid B t)
    (hne : t.keys ≠ []) : t.minimum ∈ t.keys := by
  rw [Tree.minimum_eq_headD ht]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  simp [hx]

private theorem minimum_fit {B w : ℕ} {t : Tree} (ht : Tree.Valid B t)
    (hb : ∀ x ∈ t.keys, Fits w x) : Fits w t.minimum := by
  by_cases hn : t.keys = []
  · rw [Tree.minimum_eq_headD ht, hn, List.headD_nil]
    exact fits_zero w
  · exact hb _ (minimum_mem ht hn)

/-- Full cached child minima, in the same order as the interleaved child table. -/
def childMinima (cs : List Tree) : Fin cs.length → ℕ := fun i => cs[i].minimum

/-- Each valid nonempty child supplies an actual leaf key to the node's query table. -/
private theorem childMinima_mem {B m : ℕ} {cs : List Tree}
    (ht : Tree.Valid B (.node m cs)) (i : Fin cs.length) :
    childMinima cs i ∈ cs[i].keys := by
  simp only [Tree.Valid] at ht
  exact minimum_mem (ht.2.2.2 _ (List.getElem_mem i.isLt)).1
    (ht.2.2.2 _ (List.getElem_mem i.isLt)).2

/-- Sorted distinct leaves imply strictly increasing full child minima. -/
theorem childMinima_strictMono {B m : ℕ} {cs : List Tree}
    (ht : Tree.Valid B (.node m cs))
    (hs : (Lean.FusionTree.Tree.node m cs).keys.Pairwise (· < ·)) :
    StrictMono (childMinima cs) := by
  simp only [Tree.keys] at hs
  have hcross := (List.pairwise_flatMap.mp hs).2
  intro i j hij
  exact (List.pairwise_iff_getElem.mp hcross) i j i.isLt j.isLt hij _
    (childMinima_mem ht i) _ (childMinima_mem ht j)

/-- Every child minimum obeys the full-key bound on the leaves. -/
theorem childMinima_fit {B w m : ℕ} {cs : List Tree}
    (ht : Tree.Valid B (.node m cs))
    (hb : ∀ x ∈ (Lean.FusionTree.Tree.node m cs).keys, Fits w x)
    (i : Fin cs.length) : Fits w (childMinima cs i) := by
  simp only [Tree.keys] at hb
  exact hb _ (List.mem_flatMap.mpr ⟨cs[i], List.getElem_mem i.isLt, childMinima_mem ht i⟩)

/-- Eligibility checks real width, occupancy, ordering and full-key bounds. Small-width
binary nodes need no fusion parameters. -/
def ParameterEligible (w : ℕ) (cs : List Tree) : Prop :=
  9 ≤ Nat.log 2 w ∧ 2 ≤ cs.length ∧ cs.length ≤ branching w ∧
    StrictMono (childMinima cs) ∧ ∀ i, Fits w (childMinima cs i)

/-- One uniform static assignment for all trees. Leaves and ineligible nodes have fifteen
zero parameter words. The remaining three header words are supplied by `encode`. -/
noncomputable def parameterWords (w : ℕ) : Parameters := by
  classical
  exact fun t => match t with
    | .leaf _ => fun _ => 0
    | .node _ cs =>
      if h : ParameterEligible w cs then
        (NodeParameters.choose h.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1 h.1).words
      else fun _ => 0

/-- Exact agreement with the chosen node witness, with no header-correctness hypothesis. -/
theorem parameterWords_node {w m : ℕ} {cs : List Tree} (h : ParameterEligible w cs) :
    parameterWords w (.node m cs) =
      (NodeParameters.choose h.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1 h.1).words := by
  simp [parameterWords, h]

/-- Leaves use no fusion parameters, including empty and singleton leaves. -/
theorem parameterWords_leaf (w : ℕ) (xs : List ℕ) :
    parameterWords w (.leaf xs) = fun _ => 0 := rfl

/-- Small-width internal nodes use no fusion parameters. -/
theorem parameterWords_small {w : ℕ} (hw : ¬9 ≤ Nat.log 2 w) (m : ℕ) (cs : List Tree) :
    parameterWords w (.node m cs) = fun _ => 0 := by
  simp [parameterWords, ParameterEligible, hw]

/-- All parameter words fit for every tree and width, independently of validity. -/
theorem parameterWords_fit (w : ℕ) (t : Tree) (j : Fin 15) :
    Fits w (parameterWords w t j) := by
  cases t with
  | leaf xs => exact fits_zero w
  | node m cs =>
    by_cases h : ParameterEligible w cs
    · rw [parameterWords_node h]
      exact NodeParameters.words_fit _ h.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1 h.1 j
    · simpa only [parameterWords, dite_eq_right h] using fits_zero w

/-- Every large-width valid ordered bounded node is eligible for actual preprocessing. -/
theorem parameterEligible_of_valid {w m : ℕ} {cs : List Tree}
    (hw : 9 ≤ Nat.log 2 w) (ht : Tree.Valid (branching w) (.node m cs))
    (hs : (Lean.FusionTree.Tree.node m cs).keys.Pairwise (· < ·))
    (hb : ∀ x ∈ (Lean.FusionTree.Tree.node m cs).keys, Fits w x) :
    ParameterEligible w cs := by
  have ht' := ht
  simp only [Tree.Valid] at ht'
  exact ⟨hw, ht'.1, ht'.2.1, childMinima_strictMono ht hs, childMinima_fit ht hb⟩

/-- Valid trees with bounded leaves have fitting cached minima and actual parameters.
Ordering is unnecessary for this fit statement because eligibility checks it itself. -/
theorem preprocessed_contentFits {B w : ℕ} {t : Tree} (ht : Tree.Valid B t)
    (hb : ∀ x ∈ t.keys, Fits w x) : ContentFits w (parameterWords w) t := by
  cases t with
  | leaf xs => simpa only [ContentFits, Tree.keys] using hb
  | node m cs =>
    have hm := minimum_fit ht hb
    simp only [Tree.Valid] at ht
    simp only [Tree.keys] at hb
    simp only [ContentFits]
    refine ⟨hm, parameterWords_fit w (.node m cs), ?_⟩
    intro u hu
    exact preprocessed_contentFits (ht.2.2.2 u hu).1
      (fun x hx => hb x (List.mem_flatMap.mpr ⟨u, hu, hx⟩))
termination_by sizeOf t
decreasing_by
  have hlt := List.sizeOf_lt_of_mem hu
  subst t
  simp_wf
  omega

/-- The built tree has fitting actual preprocessing contents from full-key bounds alone. -/
theorem preprocessed_contentFits_build (w : ℕ) (xs : List ℕ)
    (hb : ∀ x ∈ xs, Fits w x) :
    ContentFits w (parameterWords w) (Tree.build (branching w) xs) :=
  preprocessed_contentFits (Tree.valid_build (two_le_branching w) xs)
    (by simpa only [Tree.keys_build (two_le_branching w)] using hb)

/-- A concrete whole-tree memory with actual chosen preprocessing, exact decoding and
linear allocated words. The arena frontier is explicit; fitting keys alone do not bound it.
For unsorted inputs ineligible nodes receive zeros; ordered inputs additionally satisfy
`parameterEligible_of_valid` at every large-width internal node. No query or RAM
preprocessing-time certificate is asserted. -/
theorem preprocessed_encoding_exists {w base : ℕ} (xs : List ℕ)
    (hb : ∀ x ∈ xs, Fits w x)
    (ha : ArenaFits w base (Tree.build (branching w) xs)) :
    ∃ mem : ℕ → ℕ, Rep (parameterWords w) (Tree.build (branching w) xs) base mem ∧
      (∀ a, Fits w (mem a)) ∧
      decode ((Tree.build (branching w) xs).height + 1) mem base =
        Tree.build (branching w) xs ∧
      (encode (parameterWords w) base (Tree.build (branching w) xs)).length ≤
        126 * xs.length + 18 :=
  encoding_exists (two_le_branching w) xs (parameterWords w) ha
    (preprocessed_contentFits_build w xs hb)

end Cslib.Algorithms.WordRAM.FusionTree
