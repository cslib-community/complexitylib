/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Heap

/-!
# List-valued block assertions

These are specializations of `Block.Realizes`, not an additional memory model.

## Main definitions

* `Block.HoldsList`: a contiguous block realizes a list.

## Main results

* `Block.HoldsList.append_one`: a store immediately after a list appends one element.
* `Block.HoldsList.frame`: writes outside the block preserve its list.
-/

@[expose] public section

namespace Cslib.WordRAM.Block

/-- The block starting at `base` realizes exactly the entries of `xs`. -/
abbrev HoldsList (base : ℕ) (xs : List ℕ) (mem : ℕ → ℕ) : Prop :=
  (Block.mk base xs.length).Realizes mem (fun i => xs[i])

/-- Read an entry of a represented list. -/
theorem HoldsList.get {base : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    (h : HoldsList base xs mem) (i : ℕ) (hi : i < xs.length) :
    mem (base + i) = xs[i] := h ⟨i, hi⟩

/-- An empty list imposes no memory constraints. -/
theorem holdsList_nil (base : ℕ) (mem : ℕ → ℕ) : HoldsList base [] mem := by
  intro i
  exact Fin.elim0 i

/-- The prefix of a represented list is represented in the same memory. -/
theorem HoldsList.take {base : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    (h : HoldsList base xs mem) (k : ℕ) : HoldsList base (xs.take k) mem := by
  intro i
  have hi : i.val < xs.length := lt_of_lt_of_le i.isLt (List.take_sublist k xs).length_le
  change mem (base + i.val) = (xs.take k)[i.val]
  rw [List.getElem_take]
  exact h.get i.val hi

/-- A store immediately following a represented list appends an element. -/
theorem HoldsList.append_one {base : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    (h : HoldsList base xs mem) (v : ℕ) :
    HoldsList base (xs ++ [v]) (Function.update mem (base + xs.length) v) := by
  intro i
  change Function.update mem (base + xs.length) v (base + i.val) = (xs ++ [v])[i.val]
  by_cases hi : i.val < xs.length
  · rw [Function.update_of_ne (by omega), List.getElem_append_left hi]
    exact h.get i.val hi
  · have hil := i.isLt
    simp only [List.length_append, List.length_singleton] at hil
    have he : i.val = xs.length := by omega
    simp [he]

/-- Writes outside the represented block preserve the list. -/
theorem HoldsList.frame {base : ℕ} {xs : List ℕ} {mem mem' : ℕ → ℕ}
    (h : HoldsList base xs mem)
    (heq : ∀ a, base ≤ a → a < base + xs.length → mem' a = mem a) :
    HoldsList base xs mem' := by
  intro i
  have hi : i.val < xs.length := i.isLt
  change mem' (base + i.val) = xs[i.val]
  rw [heq _ (by omega) (by omega)]
  exact h.get i.val i.isLt

/-- Append two adjacent represented blocks. -/
theorem HoldsList.append {base : ℕ} {xs ys : List ℕ} {mem : ℕ → ℕ}
    (h : HoldsList base xs mem) (h' : HoldsList (base + xs.length) ys mem) :
    HoldsList base (xs ++ ys) mem := by
  intro i
  change mem (base + i.val) = (xs ++ ys)[i.val]
  by_cases hi : i.val < xs.length
  · rw [List.getElem_append_left hi]
    exact h.get i.val hi
  · rw [List.getElem_append_right (by omega)]
    have hil := i.isLt
    simp only [List.length_append] at hil
    have he : base + xs.length + (i.val - xs.length) = base + i.val := by omega
    simpa only [he] using h'.get (i.val - xs.length) (by omega)

end Cslib.WordRAM.Block
