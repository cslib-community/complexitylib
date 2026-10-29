/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.FromNumbers
public import Complexity.Computability.WordRAM.ListArray
public import Complexity.Computability.WordRAM.Signed.Encoding

/-!
# Exact memory output of native Chan–He traversal

The pointer table is an unsigned word list. Each pointed-to block contains the existing
`Node.oneArray`, encoded with the signed integer encoding, at the common finite length `4N`.
This reuses the generic block/list realization API and introduces no alternative convolution
predicate or execution model.

## Main definitions

* `StoredNodes`: exact pointer-table and packed-array readback for the emitted preorder.

## Main results

* `StoredNodes.congr`: transfer exact readback along a frame on its live cells.
* `StoredNodes.append`: one actual pointer-table store appends a represented native node.

The concrete output invariant and proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe

/-- The exact finite output table and its signed-encoded packed node arrays. -/
structure StoredNodes (U N table : ℕ) (ns : List (ℕ × Node)) (mem : ℕ → ℕ) : Prop where
  /-- The table contains exactly the native base pointers in emitted order. -/
  pointers : Block.HoldsList table (ns.map Prod.fst) mem
  /-- Every pointed-to word equals the existing mathematical packed array cell. -/
  cells : ∀ i : Fin ns.length, (Block.mk ns[i.val].1 (4 * N)).Realizes mem
    (fun u => Signed.encode (ns[i.val].2.oneArray U u.val))

/-- Empty traversal output imposes no pointed-to array obligations. -/
theorem storedNodes_nil (U N table : ℕ) (mem : ℕ → ℕ) : StoredNodes U N table [] mem :=
  ⟨Block.holdsList_nil table mem, fun i => Fin.elim0 i⟩

/-- Pointer-table and packed-array readback survive a frame on all their live cells. -/
theorem StoredNodes.congr {U N table : ℕ} {ns : List (ℕ × Node)} {before after : ℕ → ℕ}
    (h : StoredNodes U N table ns before)
    (ht : ∀ a, table ≤ a → a < table + ns.length → after a = before a)
    (hc : ∀ i : Fin ns.length, ∀ u < 4 * N,
      after (ns[i.val].1 + u) = before (ns[i.val].1 + u)) :
    StoredNodes U N table ns after := by
  refine ⟨h.pointers.frame (by simpa only [List.length_map] using ht), ?_⟩
  intro i u
  exact (hc i u.val u.isLt).trans (h.cells i u)

/-- Appending one native pointer preserves all packed readback. The stored pointer lies below
both the old arrays and the fresh array, so the actual store cannot overwrite array data. -/
theorem StoredNodes.append {U N table p : ℕ} {ν : Node} {ns : List (ℕ × Node)}
    {mem : ℕ → ℕ} (h : StoredNodes U N table ns mem)
    (hnew : (Block.mk p (4 * N)).Realizes mem (fun u => Signed.encode (ν.oneArray U u.val)))
    (hold : ∀ i : Fin ns.length, table + ns.length < ns[i.val].1)
    (hp : table + ns.length < p) :
    StoredNodes U N table (ns ++ [(p, ν)]) (Function.update mem (table + ns.length) p) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.map_append, List.map_singleton, List.length_map] using
      h.pointers.append_one p
  · intro i
    by_cases hi : i.val < ns.length
    · rw [List.getElem_append_left hi]
      apply (h.cells ⟨i.val, hi⟩).update_of_not_owns
      intro ha
      have hb := hold ⟨i.val, hi⟩
      exact (not_le_of_gt hb) ha.1
    · have hil := i.isLt
      simp only [List.length_append, List.length_singleton] at hil
      have he : i.val = ns.length := by omega
      have hg : (ns ++ [(p, ν)])[ns.length] = (p, ν) := by simp
      intro u
      change Function.update mem (table + ns.length) p
          ((ns ++ [(p, ν)])[i.val].1 + u.val) =
        Signed.encode ((ns ++ [(p, ν)])[i.val].2.oneArray U u.val)
      simp only [he, hg]
      rw [Function.update_of_ne (show p + u.val ≠ table + ns.length by omega)]
      exact hnew u

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
