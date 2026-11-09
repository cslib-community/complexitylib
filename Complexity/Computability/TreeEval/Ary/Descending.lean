/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Basic

/-!
# Unfolding computations with decreasing natural-number indices

A computation has a source value at index zero, a gate at each positive index, and `d` strictly
earlier dependencies. Unfolding those dependencies gives the existing `Ary.Tree`. Constant gates
pad the source to obtain a uniform height. Paths can be resolved by following indices, without
materializing the tree.

## Main results

* `Cslib.TreeEval.Ary.Descending.eval_tree`: unfolding preserves the well-founded value.
* `Cslib.TreeEval.Ary.Descending.nodeAt_tree`: path lookup agrees with the implicit lookup.

These are pure semantic constructions, with no native resource certificate.
-/

public section

namespace Cslib.TreeEval.Ary.Descending

variable {d ℓ : ℕ}

/-- A source has only source dependencies; positive indices follow the supplied dependencies. -/
@[expose] def next (child : ℕ → Fin d → ℕ) (i : ℕ) (j : Fin d) : ℕ :=
  if i = 0 then 0 else child i j

/-- A constant gate pads the source; every positive index uses its supplied gate. -/
@[expose] def paddedGate (source : Fin ℓ → Bool) (gates : ℕ → Gate d ℓ)
    (i : ℕ) : Gate d ℓ :=
  if i = 0 then fun _ => source else gates i

/-- Evaluate a computation whose positive dependencies have strictly smaller indices. -/
@[expose] def value (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) (hchild : ∀ i, 0 < i → ∀ j, child i j < i) :
    ℕ → Fin ℓ → Bool
  | 0 => source
  | i + 1 => gates (i + 1) fun j => value source child gates hchild (child (i + 1) j)
termination_by i => i
decreasing_by exact hchild _ (by omega) _

/-- Unfold dependencies to height `h`, padding source nodes with constant gates. -/
@[expose] def tree (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) : (h : ℕ) → ℕ → Tree d ℓ h
  | 0, _ => .leaf source
  | h + 1, i => .node (paddedGate source gates i)
      (fun j => tree source child gates h (next child i j))

/-- A height at least the starting index suffices to reach every source dependency. -/
theorem eval_tree (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) (hchild : ∀ i, 0 < i → ∀ j, child i j < i)
    {h i : ℕ} (hi : i ≤ h) :
    (tree source child gates h i).eval = value source child gates hchild i := by
  induction h generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp only [tree, Tree.eval_leaf, value]
  | succ h ih =>
    cases i with
    | zero => simp [tree, paddedGate, value]
    | succ i =>
      simp only [tree, Tree.eval_node, paddedGate, Nat.succ_ne_zero, ite_false, value,
        next]
      congr 1
      funext j
      have hj := hchild (i + 1) (by omega) j
      exact ih (by omega)

/-- Resolve an implicit node index by following the path from the root. -/
@[expose] def resolve (child : ℕ → Fin d → ℕ) (i : ℕ) (P : List (Fin d)) : ℕ :=
  P.foldl (next child) i

@[simp] theorem resolve_nil (child : ℕ → Fin d → ℕ) (i : ℕ) :
    resolve child i [] = i := rfl

theorem resolve_cons (child : ℕ → Fin d → ℕ) (i : ℕ) (j : Fin d) (P : List (Fin d)) :
    resolve child i (j :: P) = resolve child (next child i j) P := rfl

/-- The label at an implicit path, including the uniform source padding and invalid paths. -/
@[expose] def lookup (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) (h i : ℕ) (P : List (Fin d)) : Tree.Node d ℓ :=
  if P.length < h then .gate (paddedGate source gates (resolve child i P))
  else if P.length = h then .leaf source else .none

private theorem lookup_cons (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) (h i : ℕ) (j : Fin d) (P : List (Fin d)) :
    lookup source child gates (h + 1) i (j :: P) =
      lookup source child gates h (next child i j) P := by
  simp only [lookup, List.length_cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
    resolve_cons]

/-- The unfolded tree is read by resolving just one decreasing index along the path. -/
theorem nodeAt_tree (source : Fin ℓ → Bool) (child : ℕ → Fin d → ℕ)
    (gates : ℕ → Gate d ℓ) (h i : ℕ) (P : List (Fin d)) :
    (tree source child gates h i).nodeAt P = lookup source child gates h i P := by
  induction h generalizing i P with
  | zero =>
    cases P with
    | nil => simp [tree, lookup]
    | cons j P => simp [tree, Tree.nodeAt, lookup]
  | succ h ih =>
    cases P with
    | nil => simp [tree, lookup]
    | cons j P =>
      rw [tree, Tree.nodeAt_node_cons, lookup_cons]
      exact ih _ _

end Cslib.TreeEval.Ary.Descending
