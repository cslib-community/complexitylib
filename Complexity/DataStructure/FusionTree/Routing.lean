/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.DataStructure.FusionTree.Tree
public import Complexity.DataStructure.FusionTree.Correction

/-!
# Routing by child-minimum ranks

A constant-time node rank replaces the outer tree's semantic linear scan: a zero rank
stops the search, and a positive rank selects the preceding child pointer.

## Main results

* `Tree.selectChild_eq_rank`: inclusive rank selects the same child as the semantic search.

## References

See [FredmanWillard1993] for multiway fusion-tree descent.
-/

@[expose] public section

namespace Cslib.DataStructure.FusionTree.Tree

private theorem selectChild_eq_cut (q : ℕ) (cs : List Tree) (t : ℕ) (ht : t ≤ cs.length)
    (hcut : ∀ i (hi : i < cs.length), cs[i].minimum ≤ q ↔ i < t) :
    selectChild q cs = if t = 0 then none else cs[t - 1]? := by
  induction cs generalizing t with
  | nil =>
    have he : t = 0 := by simpa using ht
    simp [selectChild, he]
  | cons c cs ih =>
    cases t with
    | zero =>
      have hc : ¬c.minimum ≤ q := by
        have hh := hcut 0 (by simp)
        change c.minimum ≤ q ↔ 0 < 0 at hh
        exact fun hc => Nat.not_lt_zero 0 (hh.mp hc)
      have htail : ∀ i (hi : i < cs.length), cs[i].minimum ≤ q ↔ i < 0 := by
        intro i hi
        have hh := hcut (i + 1) (by simp; omega)
        change cs[i].minimum ≤ q ↔ i + 1 < 0 at hh
        simpa only [Nat.not_lt_zero] using hh
      rw [selectChild, ih 0 (by omega) htail]
      simp [hc]
    | succ t =>
      have hc : c.minimum ≤ q := (hcut 0 (by simp)).mpr (by omega)
      have htail : ∀ i (hi : i < cs.length), cs[i].minimum ≤ q ↔ i < t := by
        intro i hi
        have hh := hcut (i + 1) (by simp; omega)
        change cs[i].minimum ≤ q ↔ i + 1 < t + 1 at hh
        simpa only [Nat.add_lt_add_iff_right] using hh
      rw [selectChild, ih t (by simp only [List.length_cons] at ht; omega) htail]
      cases t with
      | zero => simp [hc]
      | succ t =>
        have hi : t < cs.length := by simp only [List.length_cons] at ht; omega
        simp [List.getElem?_eq_getElem hi, hc]

/-- For strictly increasing child minima, the inclusive full-key rank routes to exactly the
same child as the semantic linear scan. A positive cut uses child index `rank-1`. -/
theorem selectChild_eq_rank (q : ℕ) (cs : List Tree)
    (hsorted : StrictMono (fun i : Fin cs.length => cs[i.val].minimum)) :
    selectChild q cs =
      if upperRank (fun i : Fin cs.length => cs[i.val].minimum) q = 0 then none
      else cs[upperRank (fun i : Fin cs.length => cs[i.val].minimum) q - 1]? := by
  apply selectChild_eq_cut q cs _ (upperRank_le _ _)
  intro i hi
  exact (lt_upperRank_iff hsorted ⟨i, hi⟩).symm

end Cslib.DataStructure.FusionTree.Tree
