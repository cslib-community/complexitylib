/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.BackendFrame
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Read
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Update
public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Extract

/-!
# A native backend for the existing memory heap

The five operation certificates share one register bank and exchange factor, chosen before the
heap's dimension, key bound, runtime layout, width or contents. The existing memory refinement
provides correctness and admissibility; extraction observes its encoded natural handle through
the original checked entry constructor. This preserves the complete source state and history.

## Main definitions

* `certificates`: the fixed finite family of original-source operation certificates.
* `backend`: the existing Backend specialized to the indexed priority queue.

## Main results

* `implements`: the backend implements the existing heap-to-memory refinement.
* `bound`: constant read-operation and logarithmic update/extraction native body bounds.
* `modifies`: every actual operation preserves cells outside the source heap footprint.

Calling-convention argument installation is external to these body-only contracts. Raw native
argument delivery, initialization and complete-client clocks require their separate proofs.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue.BinaryHeap

/-- The five fixed original-source certificates, independent of every runtime heap parameter. -/
@[expose] noncomputable def certificates : Fin 5 → Certificate .exact :=
  ![Certificate.ofRealizes realizes_isEmpty, Certificate.ofRealizes realizes_getKeyWord,
    Certificate.ofRealizes realizes_insert,
    Certificate.ofRealizes realizes_decreaseKey, Certificate.ofRealizes realizes_extractMin]

/-- Constructor selection, runtime arguments and typed observation for the indexed-PQ methods. -/
@[expose] def backend (n K : ℕ) (L : Memory.Layout n) :
    Backend (indexedMinPQSpec n K) certificates where
  tag
    | .isEmpty => 0
    | .getKey _ => 1
    | .insert _ _ => 2
    | .decreaseKey _ _ => 3
    | .extractMin => 4
  arg
    | .isEmpty => ⟨n, L⟩
    | .getKey v => (⟨n, L⟩, v.val)
    | .insert v k => ((⟨n, L⟩, v.val), k)
    | .decreaseKey v k => ((⟨n, L⟩, v.val), k)
    | .extractMin => ⟨n, L⟩
  answer
    | .isEmpty => id
    | .getKey _ => id
    | .insert _ _ => id
    | .decreaseKey _ _ => id
    | .extractMin => fun a => a.bind fun p => Memory.entry n p.1 p.2

private theorem layout_fits {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K)
    {s : Memory.State} (hs : Memory.Inv L s) (hw : Memory.WellFormed w s) :
    ∀ i, Fits w (layoutWords ⟨n, L⟩ i) := by
  intro i
  fin_cases i
  · exact hL.n_fits
  · exact hw.fits_of_lt_frontier (hs.size_lt hL)
  · change Fits w L.size.length
    rw [hL.size_length]
    apply hw.frontier_fits.of_le
    have ha := hs.size_allocated
    change L.size.base + L.size.length ≤ s.frontier at ha
    rw [hL.size_length] at ha
    omega
  · change Fits w L.base
    apply hw.frontier_fits.of_le
    have ha := hs.arrays_allocated
    change L.base + (3 * n + 1) ≤ s.frontier at ha
    omega

/-- Each method preserves its exact source run and meets the native certificate entry domain. -/
theorem implements {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K) :
    (backend n K L).Implements (Memory.refinement hL) where
  run o s := by
    cases o
    · rfl
    · rfl
    · rfl
    · rfl
    · exact extractMin_run w ⟨n, L⟩ s
  entry o hw hs hv := by
    have hl := layout_fits L hL hs hw
    have hvfit (v : Fin n) : ∀ i : Fin 1,
        Fits w ((Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding v.val i) :=
      fun _ => hL.n_fits.of_le v.isLt.le
    cases o with
    | isEmpty =>
      dsimp only [backend, certificates, Matrix.cons_val_zero]
      exact ⟨hl, hL.size_length, hs.size_allocated⟩
    | getKey v =>
      dsimp only [backend, certificates, Matrix.cons_val_one]
      exact ⟨fits_appendWords layoutWords _ hl (hvfit v), v.isLt,
        hs.arrays_allocated⟩
    | insert v k =>
      dsimp only [backend, certificates, Matrix.cons_val_two]
      exact ⟨fits_appendWords indexWords _
        (fits_appendWords layoutWords _ hl (hvfit v)) (fun _ => hL.key_fits.of_le hv.2),
        v.isLt, K, hL, hs, hv⟩
    | decreaseKey v k =>
      dsimp only [backend, certificates, Matrix.cons_val_three]
      exact ⟨fits_appendWords indexWords _
        (fits_appendWords layoutWords _ hl (hvfit v)) (fun _ => hL.key_fits.of_le hv.2),
        v.isLt, K, hL, hs, hv⟩
    | extractMin =>
      dsimp only [backend, certificates, Matrix.cons_val_four]
      exact ⟨hl, K, hL, hs⟩

/-- The original source bounds, keeping the read-only operations constant. -/
def memoryBound {n : ℕ} : IndexedMinPQ.Op n → ℕ
  | .isEmpty => 1
  | .getKey _ => 2
  | .insert _ _ => 8 * Nat.log 2 n + 9
  | .decreaseKey _ _ => 8 * Nat.log 2 n + 6
  | .extractMin => Memory.opCost n

private theorem source_amortized {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K) :
    (Memory.refinement hL).Amortized Memory.charge (fun _ o => memoryBound o)
      (fun _ => 0) := by
  apply Refinement.Amortized.ofFn
  intro s o hs hv
  cases o with
  | isEmpty => exact (triple_iff.mp (Memory.isEmpty_triple hL hs)).2.1
  | getKey v => exact (triple_iff.mp (Memory.getKey_triple hs v)).2.1
  | insert v k => exact (triple_iff.mp (Memory.insert_triple hL hs hv)).2.1
  | decreaseKey v k => exact (triple_iff.mp (Memory.decreaseKey_triple hL hs hv)).2.1
  | extractMin => exact (triple_iff.mp (Memory.extractMin_triple hL hs)).2.1

/-- The generic execution implementation; argument installation remains a calling convention. -/
noncomputable def implementation {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K) :=
  Backend.implementation (implements L hL)

/-- Every actual operation body has the source's constant or logarithmic bound, multiplied by
one factor fixed before all runtime heap parameters. This excludes argument installation/halt. -/
theorem bound {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K) :
    Bound (implementation L hL) id
      (fun _ o => Backend.factor certificates * (memoryBound o + 1)) := by
  have hw : ∀ {s} o, (Memory.refinement hL).inv s →
      (indexedMinPQSpec n K).valid ((Memory.refinement hL).abs s) o →
      (certificates ((backend n K L).tag o)).work ((backend n K L).arg o) s ≤ 0 := by
    intro s o _ _
    cases o <;> exact Nat.le_refl 0
  intro s x o a y steps hr hv he
  have h := Backend.bound (implements L hL) (source_amortized L hL) 0 hw hr hv he
  simpa only [Nat.add_zero] using h

/-- The same operation bounds after adding fixed initialization certificates to the bank.
Only the selected method body is charged; extra tags do not install or execute arguments. -/
theorem bound_extend {ι : Type} [Fintype ι] (extra : ι → Certificate .exact)
    {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K) :
    Bound (Backend.implementation ((implements L hL).extend extra)) id
      (fun _ o => Backend.factor (Sum.elim certificates extra) * (memoryBound o + 1)) := by
  have hw : ∀ {s} o, (Memory.refinement hL).inv s →
      (indexedMinPQSpec n K).valid ((Memory.refinement hL).abs s) o →
      ((Sum.elim certificates extra) (((backend n K L).extend extra).tag o)).work
        (((backend n K L).extend extra).arg o) s ≤ 0 := by
    intro s o _ _
    cases o <;> exact Nat.le_refl 0
  intro s x o a y steps hr hv he
  have h := Backend.bound ((implements L hL).extend extra) (source_amortized L hL) 0 hw hr hv he
  simpa only [Nat.add_zero] using h

/-- Every operation preserves all cells outside the existing heap layout, including inaccessible
cells. The proof is the shared BackendFrame theorem specialized to a zero-room heap. -/
theorem modifies {w n K : ℕ} (L : Memory.Layout n) (hL : L.Valid w K)
    {s : (indexedMinPQSpec n K).State}
    {x y : Data (Backend.registers certificates)} {o : IndexedMinPQ.Op n}
    {a : o.Result} {steps : ℕ} (hr : (implementation L hL).rep s x)
    (hv : IndexedMinPQ.valid K s o) (he : (backend n K L).exec w x o a y steps) :
    Modifies L.footprint x.mem y.mem := by
  have h := Backend.modifies (M := Memory.framed hL) (implements L hL) hr hv he
  simpa only [Memory.Framed.region_eq_footprint (Memory.framed hL) rfl,
    Memory.framed_footprint] using h

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
