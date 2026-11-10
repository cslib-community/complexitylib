/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Blocking
public import Mathlib.Data.List.Infix

/-!
# Black pebbling of complete binary trees

The complete binary tree `T_h` of height `h` has a vertex for each root-first path of length at
most `h`. Edges point from children to parents, so the leaves are the sources and the root is the
sink. A vertex at depth `d < h` has black pebbling price `h - d + 2`, so the root has price `h + 2`.

The upper bound pebbles the two children one after the other. The lower bound uses the
path-blocking engine of `Complexity.Computability.Pebbling.Blocking`, with the leftmost path into
each child as the witness path.

## Main definitions

* `Cslib.Pebbling.BinaryTreeVertex h`, `Cslib.Pebbling.completeBinaryTree h`: the tree.
* `Cslib.Pebbling.BinaryTreeVertex.root h`: its root.
* `Cslib.Pebbling.BinaryTreeVertex.below v`: the subtree rooted at `v`.

## Main results

* `Cslib.Pebbling.blackPebblingPrice_completeBinaryTree`: a vertex at depth `d < h` has price
  `h - d + 2`.
* `Cslib.Pebbling.blackPebblingPrice_completeBinaryTree_root`: for `h ≥ 1` the root has price
  `h + 2`.

## References

* [J. Nordström, *New wine into old wineskins*][Nordstrom2015Survey], Theorem 4.1.
* [J. E. Savage, *Models of Computation*][Savage1998], Lemma 10.2.1 (with sliding, so its bound
  is one lower).
-/

public section

namespace Cslib.Pebbling

/-! ## Complete binary trees -/

/-- A vertex of the complete binary tree of height `h`: a root-first path of length at most `h`,
where `false` is the left child. -/
@[ext]
structure BinaryTreeVertex (h : ℕ) where
  /-- The root-first path, with `false` for the left child. -/
  path : List Bool
  /-- The depth is at most `h`. -/
  length_le : path.length ≤ h
  deriving DecidableEq

/-- The complete binary tree `T_h`, with edges directed from children to parents. -/
def completeBinaryTree (h : ℕ) : Digraph (BinaryTreeVertex h) where
  Adj u v := ∃ b, u.path = v.path ++ [b]

@[simp] theorem completeBinaryTree_adj {h : ℕ} {u v : BinaryTreeVertex h} :
    (completeBinaryTree h).Adj u v ↔ ∃ b, u.path = v.path ++ [b] :=
  Iff.rfl

/-- The root of `T_h`. -/
@[expose] def BinaryTreeVertex.root (h : ℕ) : BinaryTreeVertex h := ⟨[], Nat.zero_le h⟩

@[simp] theorem BinaryTreeVertex.root_path (h : ℕ) : (BinaryTreeVertex.root h).path = [] := rfl

/-- The vertices of the subtree rooted at `v`. -/
def BinaryTreeVertex.below {h : ℕ} (v : BinaryTreeVertex h) : Set (BinaryTreeVertex h) :=
  {u | v.path <+: u.path}

@[simp] theorem BinaryTreeVertex.mem_below {h : ℕ} {u v : BinaryTreeVertex h} :
    u ∈ v.below ↔ v.path <+: u.path :=
  Iff.rfl

private theorem blackPebblable_completeBinaryTree_aux {h : ℕ} (k : ℕ) (v : BinaryTreeVertex h)
    (hk : v.path.length + k = h) : BlackPebblable (completeBinaryTree h) (k + 2) v := by
  induction k generalizing v with
  | zero =>
    refine BlackPebblable.of_forall_adj (s := 1) ∅ (fun u hu => ?_) (by simp) (by simp)
      (by simp)
    obtain ⟨b, hb⟩ := hu
    have h₁ := congrArg List.length hb
    have h₂ := u.length_le
    simp only [List.length_append, List.length_singleton] at h₁
    omega
  | succ k ih =>
    let y : BinaryTreeVertex h := ⟨v.path ++ [false], by simp; omega⟩
    let z : BinaryTreeVertex h := ⟨v.path ++ [true], by simp; omega⟩
    have hyz := Finset.card_le_two (a := y) (b := z)
    refine BlackPebblable.of_forall_adj (s := k + 2) {y, z} (fun u hu => ?_) ?_ (by omega)
      (by omega)
    · obtain ⟨b, hb⟩ := hu
      cases b
      · exact Finset.mem_insert.2 (.inl (BinaryTreeVertex.ext hb))
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.2 (BinaryTreeVertex.ext hb))
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact ih _ (by simp [y]; omega)
      · exact ih _ (by simp [z]; omega)

/-- A vertex at depth `d` of `T_h` can be pebbled with `h - d + 2` pebbles. -/
theorem blackPebblable_completeBinaryTree {h : ℕ} (v : BinaryTreeVertex h) :
    BlackPebblable (completeBinaryTree h) (h - v.path.length + 2) v :=
  blackPebblable_completeBinaryTree_aux _ v (by have := v.length_le; omega)

/-- The leftmost path into `v` is open when `P` has no pebble on it. -/
private theorem completeBinaryTree_unblocked_left {h : ℕ} {P : Finset (BinaryTreeVertex h)}
    (k : ℕ) (v : BinaryTreeVertex h) (hk : v.path.length + k = h)
    (hP : ∀ w ∈ P, ∀ i, w.path ≠ v.path ++ List.replicate i false) :
    Unblocked (completeBinaryTree h) P v := by
  induction k generalizing v with
  | zero =>
    refine .source (fun u hu => ?_) (fun hv => hP v hv 0 (by simp))
    obtain ⟨b, hb⟩ := hu
    have h₁ := congrArg List.length hb
    have h₂ := u.length_le
    simp only [List.length_append, List.length_singleton] at h₁
    omega
  | succ k ih =>
    let y : BinaryTreeVertex h := ⟨v.path ++ [false], by simp; omega⟩
    refine .step (u := y) (ih y (by simp [y]; omega) fun w hw i hwi => hP w hw (i + 1) ?_)
      ⟨false, rfl⟩ (fun hv => hP v hv 0 (by simp))
    simp [hwi, y, List.replicate_succ]

private theorem completeBinaryTree_exists_left {h : ℕ} {P : Finset (BinaryTreeVertex h)}
    (v : BinaryTreeVertex h) (hv : ¬ Unblocked (completeBinaryTree h) P v) :
    ∃ w ∈ P, ∃ i, w.path = v.path ++ List.replicate i false := by
  by_contra hcon
  push Not at hcon
  exact hv (completeBinaryTree_unblocked_left (h - v.path.length) v
    (by have := v.length_le; omega) hcon)

private theorem forcesPebbles_completeBinaryTree_aux {h : ℕ} (k : ℕ) (v : BinaryTreeVertex h)
    (hk : v.path.length + (k + 1) = h) :
    ForcesPebbles (completeBinaryTree h) v.below v (k + 3) := by
  induction k generalizing v with
  | zero =>
    exact forcesPebbles_three (y := ⟨v.path ++ [false], by simp; omega⟩)
      (z := ⟨v.path ++ [true], by simp; omega⟩) ⟨false, rfl⟩ ⟨true, rfl⟩
      (fun h => by simpa using congrArg BinaryTreeVertex.path h)
      (BinaryTreeVertex.mem_below.2 (List.prefix_refl _))
      (BinaryTreeVertex.mem_below.2 (List.prefix_append _ _))
      (BinaryTreeVertex.mem_below.2 (List.prefix_append _ _))
  | succ k ih =>
    let y : BinaryTreeVertex h := ⟨v.path ++ [false], by simp; omega⟩
    let z : BinaryTreeVertex h := ⟨v.path ++ [true], by simp; omega⟩
    rw [show k + 1 + 3 = k + 3 + 1 by omega]
    refine ForcesPebbles.step (y := y) (z := z) (Ry := y.below) (Rz := z.below) ⟨false, rfl⟩
      ⟨true, rfl⟩ (fun u hu => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun P hP => ?_)
      (fun P hP => ?_) (ih y (by simp [y]; omega)) (ih z (by simp [z]; omega))
    · obtain ⟨b, hb⟩ := hu
      cases b
      · exact .inl (BinaryTreeVertex.ext hb)
      · exact .inr (BinaryTreeVertex.ext hb)
    · exact BinaryTreeVertex.mem_below.2 ((List.prefix_append _ _).trans hw)
    · exact BinaryTreeVertex.mem_below.2 ((List.prefix_append _ _).trans hw)
    · obtain ⟨w, hw, i, hwi⟩ := completeBinaryTree_exists_left y hP
      refine ⟨w, hw, BinaryTreeVertex.mem_below.2 ?_, fun hwz => ?_⟩
      · rw [hwi]
        exact (List.prefix_append _ _).trans (List.prefix_append _ _)
      · rw [BinaryTreeVertex.mem_below, hwi] at hwz
        simp [y, z, List.prefix_append_right_inj] at hwz
    · obtain ⟨w, hw, i, hwi⟩ := completeBinaryTree_exists_left z hP
      refine ⟨w, hw, BinaryTreeVertex.mem_below.2 ?_, fun hwy => ?_⟩
      · rw [hwi]
        exact (List.prefix_append _ _).trans (List.prefix_append _ _)
      · rw [BinaryTreeVertex.mem_below, hwi] at hwy
        simp [y, z, List.prefix_append_right_inj] at hwy

/-- Every non-leaf vertex `v` of `T_h` forces `h - depth + 2` pebbles on its subtree. -/
theorem forcesPebbles_completeBinaryTree {h : ℕ} (v : BinaryTreeVertex h)
    (hv : v.path.length < h) :
    ForcesPebbles (completeBinaryTree h) v.below v (h - v.path.length + 2) := by
  have := forcesPebbles_completeBinaryTree_aux (h - v.path.length - 1) v (by omega)
  rwa [show h - v.path.length - 1 + 3 = h - v.path.length + 2 by omega] at this

theorem unblocked_completeBinaryTree_empty {h : ℕ} (v : BinaryTreeVertex h) :
    Unblocked (completeBinaryTree h) ∅ v :=
  completeBinaryTree_unblocked_left (h - v.path.length) v (by have := v.length_le; omega)
    fun w hw => absurd hw (Finset.notMem_empty w)

/-- The black pebbling price of a non-leaf vertex at depth `d` of `T_h` is `h - d + 2`. -/
theorem blackPebblingPrice_completeBinaryTree {h : ℕ} (v : BinaryTreeVertex h)
    (hv : v.path.length < h) :
    blackPebblingPrice (completeBinaryTree h) v = h - v.path.length + 2 :=
  blackPebblingPrice_eq (blackPebblable_completeBinaryTree v) fun _ hs =>
    (forcesPebbles_completeBinaryTree v hv).le_of_blackPebblable
      (unblocked_completeBinaryTree_empty v) hs

/-- The complete binary tree of height `h ≥ 1` has black pebbling price `h + 2`. -/
theorem blackPebblingPrice_completeBinaryTree_root {h : ℕ} (hh : h ≠ 0) :
    blackPebblingPrice (completeBinaryTree h) (BinaryTreeVertex.root h) = h + 2 := by
  rw [blackPebblingPrice_completeBinaryTree _ (by simp; omega), BinaryTreeVertex.root_path,
    List.length_nil, Nat.sub_zero]

end Cslib.Pebbling
