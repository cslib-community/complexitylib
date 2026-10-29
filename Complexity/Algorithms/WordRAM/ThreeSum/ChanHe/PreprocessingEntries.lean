/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Layout
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalFrames
public import Complexity.Algorithms.ThreeSum.ChanHe.FromNumbers

/-!
# Exact native frontend entries for Chan–He traversal

The semantic entries use the actual frontend payload bases and decoded compact lists. Native
readback follows from the frontend's canonical encoding theorem. Their output is exactly the
existing finite Chan–He node list; no new 3SUM predicate or padded input is introduced.

## Main definitions

* `entry`, `entries`: semantic records of the actual six-word frontend descriptors.

## Main results

* `entry_stored`: exact signed-encoded payload readback.
* `entry_valid`, `entry_ends`: admissibility and containment in the concrete frontend allocation.
* `entries_output`: exact equality with the existing finite node list, in order.

These native representation bridges are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- One actual frontend descriptor, with the shared runtime fuel and concrete payload bases. -/
def entry (l : Frontend.Layout) (U f : ℕ) (rs : List (ℕ × ℕ)) (t : ℕ) : Traversal.Entry :=
  ⟨f, fun j => l.pointer (3 * t + j.val),
    fun j => (Frontend.Math.array U l.digits rs (3 * t + j.val)).map Signed.decode⟩

/-- All actual frontend roots in their existing enumeration order. -/
def entries (l : Frontend.Layout) (U : ℕ) (rs : List (ℕ × ℕ)) : List Traversal.Entry :=
  (List.range l.count).map (entry l U (Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n) rs)

/-- Each concrete root column is a valid physical frontend slot. -/
theorem entry_slot {l : Frontend.Layout} {t : ℕ} (ht : t < l.count) (j : Fin 3) :
    3 * t + j.val < l.arrays := by
  have := j.isLt
  dsimp only [Frontend.Layout.arrays]
  omega

/-- A root column occupies at most its actual `n+1`-word payload capacity. -/
theorem entry_length_le (l : Frontend.Layout) (U f : ℕ) (rs : List (ℕ × ℕ))
    (hcard : rs.length ≤ l.n) (t : ℕ) (j : Fin 3) :
    ((entry l U f rs t).data j).length ≤ l.n + 1 := by
  simpa only [entry, List.length_map] using
    (Frontend.Math.length_array_le U l.digits rs (3 * t + j.val)).trans (by omega)

/-- The actual native frontend payload is exactly the signed encoding expected by traversal. -/
theorem entry_stored {input : List ℤ} {rs : List (ℕ × ℕ)} {l : Frontend.Layout}
    {U f t : ℕ} {mem : ℕ → ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (h : Frontend.Output l U rs mem) (ht : t < l.count) :
    (entry l U f rs t).Stored mem := by
  intro j i
  have hj := entry_slot ht j
  have hi : i.val < (Frontend.Math.array U l.digits rs (3 * t + j.val)).length := by
    simpa only [entry, List.length_map] using i.isLt
  have hm := (h _ hj).2.2.get i.val hi
  change mem (l.pointer (3 * t + j.val) + i.val) =
    Signed.encode (((Frontend.Math.array U l.digits rs (3 * t + j.val)).map Signed.decode)[i.val])
  simp only [List.getElem_map]
  exact hm.trans (Frontend.Math.array_canonical hkeys U l.digits _ _
    (List.getElem_mem hi)).symm

/-- Frontend roots satisfy the existing admissibility notion, including singleton zero at n=0. -/
theorem entry_valid {input : List ℤ} {rs : List (ℕ × ℕ)} (l : Frontend.Layout) (U f t : ℕ)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    (entry l U f rs t).Valid (l.n + 1) (2 * U) := by
  have hn (j : Fin 3) : ((entry l U f rs t).data j).Nodup :=
    Frontend.Math.array_decoded_nodup hkeys hnd U l.digits (3 * t + j.val)
  have hc (j : Fin 3) : ((entry l U f rs t).data j).toFinset.card ≤ l.n + 1 := by
    rw [List.toFinset_card_of_nodup (hn j)]
    exact entry_length_le l U f rs hcard t j
  have hb (j : Fin 3) : Cslib.Algorithms.ThreeSum.Bdd (2 * U)
      ((entry l U f rs t).data j).toFinset := by
    intro z hz
    change z ∈ ((Frontend.Math.array U l.digits rs (3 * t + j.val)).map Signed.decode).toFinset
      at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    exact Frontend.Math.array_magnitude hkeys hvalues l.digits _ u hu
  exact ⟨hn, hc 0, hc 1, hc 2, hb 0, hb 1, hb 2⟩

/-- Every actual root payload ends inside the frontend's concrete allocation. -/
theorem entry_ends (l : Frontend.Layout) (U f : ℕ) (rs : List (ℕ × ℕ))
    (hcard : rs.length ≤ l.n) {t : ℕ} (ht : t < l.count) (j : Fin 3) :
    (entry l U f rs t).source j + ((entry l U f rs t).data j).length ≤ l.endpoint := by
  have hj := entry_slot ht j
  have hn := entry_length_le l U f rs hcard t j
  calc (entry l U f rs t).source j + ((entry l U f rs t).data j).length
      ≤ l.pointer (3 * t + j.val) + l.capacity := Nat.add_le_add_left hn _
    _ = l.pointer (3 * t + j.val + 1) := (l.pointer_succ _).symm
    _ ≤ l.pointer l.arrays := l.pointer_mono (by omega)

/-- Traversing these exact entries produces precisely the unchanged finite Chan–He node list. -/
theorem entries_output {input : List ℤ} {rs : List (ℕ × ℕ)} {U : ℕ}
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hcounts : ∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    let l : Frontend.Layout := ⟨input.length, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩
    Traversal.Math.output
      (Nat.primesLE (Cslib.Algorithms.ThreeSum.ChanHe.mPar input.length (2 * U))) l.digits
      ((entries l U rs).map Traversal.Entry.task) =
        Cslib.Algorithms.ThreeSum.ChanHe.allNodes input.length U
          (fun i : Fin input.length => input[i]) := by
  let l : Frontend.Layout := ⟨input.length, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩
  have hr := Frontend.Math.roots_indexed U rs
  have hd := Frontend.Math.roots_decoded hkeys hcounts hvalues
  change ((List.range l.count).map (Frontend.Math.root U l.digits rs)) =
    Frontend.Math.roots U rs at hr
  calc Traversal.Math.output _ _ ((entries l U rs).map Traversal.Entry.task)
      = (((List.range l.count).map (Frontend.Math.root U l.digits rs)).map
          Frontend.Math.decodeRoot).flatMap (fun T =>
            Cslib.Algorithms.ThreeSum.ChanHe.reduction input.length (2 * U) T.1 T.2.1 T.2.2) := by
          simp only [Traversal.Math.output, entries, List.flatMap_map, List.map_map,
            Function.comp_def]
          rfl
    _ = _ := by rw [hr, hd]; rfl

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
