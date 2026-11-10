/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log

/-!
# Balanced folds of lists

`List.balancedFold op e f l` combines the images under `f` of the elements of `l` by the binary
operation `op` along a balanced binary tree: the empty list gives `e`, a singleton `[b]` gives
`f b`, and a list of length `k ≥ 2` gives `op` of the folds of its first `⌊k / 2⌋` elements and of
the others. The tree has depth `⌈log₂ k⌉`, so a measure that grows by at most `c` with every
application of `op` grows by at most `c ⌈log₂ k⌉` along the fold (`List.apply_balancedFold_le`).
For an associative operation with identity `e`, the fold is `foldr` (`List.balancedFold_eq_foldr`),
whatever the shape of the tree.

Balanced folds give formulas of logarithmic depth: the disjunction of `k` formulas, and the
formula saying that a branching program of length `k` maps one state to another.

## Main definitions

* `List.balancedFold`: the fold of a list along a balanced binary tree.

## Main results

* `List.balancedFold_induction`: a property preserved by concatenation holds for balanced folds.
* `List.balancedFold_hom`: maps commuting with the operations commute with balanced folds.
* `List.balancedFold_eq_foldr`: for an associative operation with an identity, the balanced fold
  is `foldr`.
* `List.apply_balancedFold_le`: a measure growing by at most `c` with each operation grows by at
  most `c ⌈log₂ k⌉` along a balanced fold of `k` elements.
-/

@[expose] public section

namespace List

variable {α β γ : Type*}

/-- The fold of `l` along a balanced binary tree: `e` for the empty list, `f b` for `[b]`, and for
a list of length `k ≥ 2`, `op` applied to the folds of its first `⌊k / 2⌋` elements and of the
others. -/
def balancedFold (op : α → α → α) (e : α) (f : β → α) (l : List β) : α :=
  match h : l with
  | [] => e
  | [b] => f b
  | _ :: _ :: _ =>
    op ((l.take (l.length / 2)).balancedFold op e f) ((l.drop (l.length / 2)).balancedFold op e f)
termination_by l.length
decreasing_by
  all_goals subst h; simp only [List.length_take, List.length_drop, List.length_cons]; omega

variable {op : α → α → α} {e : α} {f : β → α}

/-- The balanced fold of the empty list is `e`. -/
@[simp] theorem balancedFold_nil : ([] : List β).balancedFold op e f = e := by
  rw [balancedFold]

/-- The balanced fold of a singleton `[b]` is `f b`. -/
@[simp] theorem balancedFold_singleton (b : β) : [b].balancedFold op e f = f b := by
  rw [balancedFold]

/-- A list of length at least two folds into `op` of the folds of its two halves. -/
theorem balancedFold_of_two_le {l : List β} (hl : 2 ≤ l.length) :
    l.balancedFold op e f =
      op ((l.take (l.length / 2)).balancedFold op e f)
        ((l.drop (l.length / 2)).balancedFold op e f) := by
  match l, hl with
  | _ :: _ :: _, _ => rw [balancedFold]

/-- **Induction for balanced folds.** A property of lists and values that holds for the empty list
and `e`, for every singleton `[b]` and `f b`, and for `l₁ ++ l₂` and `op x y` whenever it holds for
nonempty `l₁` and `x` and for nonempty `l₂` and `y`, holds for every list and its balanced fold. -/
theorem balancedFold_induction {p : List β → α → Prop} (nil : p [] e)
    (singleton : ∀ b, p [b] (f b))
    (append : ∀ l₁ l₂ x y, l₁ ≠ [] → l₂ ≠ [] → p l₁ x → p l₂ y → p (l₁ ++ l₂) (op x y))
    (l : List β) : p l (l.balancedFold op e f) := by
  induction l using balancedFold.induct with
  | case1 => simpa using nil
  | case2 b => simpa using singleton b
  | case3 b b' l ih₁ ih₂ =>
    have := append _ _ _ _ (by simp [List.take_eq_nil_iff])
      (by simp only [ne_eq, List.drop_eq_nil_iff, length_cons]; omega) ih₁ ih₂
    rwa [List.take_append_drop,
      ← balancedFold_of_two_le (op := op) (e := e) (f := f) (l := b :: b' :: l) (by simp)] at this

/-- A map commuting with the operations commutes with balanced folds. -/
theorem balancedFold_hom (g : α → γ) {op' : γ → γ → γ} (hg : ∀ x y, g (op x y) = op' (g x) (g y))
    (l : List β) : g (l.balancedFold op e f) = l.balancedFold op' (g e) (g ∘ f) := by
  induction l using balancedFold.induct with
  | case1 => simp
  | case2 b => simp
  | case3 b b' l ih₁ ih₂ =>
    rw [balancedFold_of_two_le (l := b :: b' :: l) (by simp),
      balancedFold_of_two_le (l := b :: b' :: l) (by simp), hg, ih₁, ih₂]

/-- For an associative operation with identity `e`, the balanced fold is `foldr`. -/
theorem balancedFold_eq_foldr [Std.Associative op] [Std.LawfulIdentity op e] (l : List β) :
    l.balancedFold op e f = (l.map f).foldr op e := by
  refine balancedFold_induction (p := fun l x => x = (l.map f).foldr op e) (by simp)
    (fun b => by simp [Std.LawfulRightIdentity.right_id]) (fun l₁ l₂ x y _ _ hx hy => ?_) l
  have h := foldr_assoc (op := op) (l := l₁.map f) (a₁ := e) (a₂ := (l₂.map f).foldr op e)
  rw [Std.LawfulLeftIdentity.left_id (op := op) (o := e)] at h
  rw [hx, hy, map_append, foldr_append, h]

/-- **Depth of a balanced fold.** If applying `op` raises a measure `d` by at most `c` above its
values on the arguments, and `d` is at most `D` on the leaves, then `d` is at most
`D + c ⌈log₂ k⌉` on the balanced fold of a list of `k` elements; `e` only matters for the empty
list. -/
theorem apply_balancedFold_le (d : α → ℕ) {c D : ℕ}
    (hop : ∀ x y, d (op x y) ≤ max (d x) (d y) + c) {l : List β} (hf : ∀ b ∈ l, d (f b) ≤ D)
    (he : l = [] → d e ≤ D) : d (l.balancedFold op e f) ≤ D + c * Nat.clog 2 l.length := by
  induction l using balancedFold.induct with
  | case1 => simpa using he rfl
  | case2 b => simpa using hf b (mem_singleton_self b)
  | case3 b b' l ih₁ ih₂ =>
    set L := b :: b' :: l
    have hk : 2 ≤ L.length := by simp [L]
    have hlen₁ : (L.take (L.length / 2)).length ≤ (L.length + 2 - 1) / 2 := by
      simp only [length_take]
      omega
    have hlen₂ : (L.drop (L.length / 2)).length ≤ (L.length + 2 - 1) / 2 := by
      simp only [length_drop]
      omega
    have h₁ := ih₁ (fun b hb => hf b (mem_of_mem_take hb))
      (fun h => absurd h (by simp [L, List.take_eq_nil_iff]))
    have h₂ := ih₂ (fun b hb => hf b (mem_of_mem_drop hb))
      (fun h => absurd h (by simp only [L, List.drop_eq_nil_iff, length_cons]; omega))
    have hm₁ := Nat.mul_le_mul_left c (Nat.clog_mono_right 2 hlen₁)
    have hm₂ := Nat.mul_le_mul_left c (Nat.clog_mono_right 2 hlen₂)
    have := hop ((L.take (L.length / 2)).balancedFold op e f)
      ((L.drop (L.length / 2)).balancedFold op e f)
    rw [balancedFold_of_two_le hk, Nat.clog_of_two_le (by decide) hk, Nat.mul_succ]
    omega

end List
