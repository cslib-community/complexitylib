/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.BackendFrame
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Read
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Decrease
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Extract

/-!
# A uniform native method family for the original indexed Fibonacci heap

Five fixed certificates choose the bank, body emitters and one exchange factor before every
runtime capacity, key bound, layout base, width and heap. The original memory refinement supplies
full source correctness, histories and the nonzero amortized potential. Typed observation uses
the existing generic partial inverse of handle erasure; it executes no decoder instructions.

These are method-body contracts. Calling-convention installation is external and uncharged;
initialization, paid argument delivery, complete callers and abstract space bounds remain
separate obligations. In particular, the amortized result is not a per-operation worst-case
logarithmic bound for extraction or decrease-key.

## Main definitions

* `certificates`: the fixed five original-source native certificates.
* `backend`: specialization of the existing `Backend` to the indexed queue.

## Main results

* `implements`: complete method-source and typed-answer transport.
* `amortized`: native body charges with the original heap potential.
* `modifies`: preservation of memory outside the original heap footprint.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

/-- The bank and factor are fixed before all runtime heap arguments. -/
@[expose] noncomputable def certificates : Fin 5 → Certificate .exact :=
  ![Certificate.ofRealizes realizes_isEmpty, Certificate.ofRealizes realizes_getKey,
    Certificate.ofRealizes realizes_insert,
    Certificate.ofRealizes realizes_decreaseKey, Certificate.ofRealizes realizes_extractRaw]

/-- Constructor selection and runtime arguments for the existing indexed queue. Typed result
observation is proof-only: the partial inverse is applied only to actual erased source results. -/
@[expose] noncomputable def backend (n K base : ℕ) :
    Backend (indexedMinPQSpec n K) certificates where
  tag
    | .isEmpty => 0
    | .getKey _ => 1
    | .insert _ _ => 2
    | .decreaseKey _ _ => 3
    | .extractMin => 4
  arg
    | .isEmpty => (n, base)
    | .getKey v => ![n, base, v.val]
    | .insert v key => ![n, base, v.val, key]
    | .decreaseKey v key => ![n, base, v.val, key]
    | .extractMin => ![n, base]
  answer
    | .isEmpty => id
    | .getKey _ => id
    | .insert _ _ => id
    | .decreaseKey _ _ => id
    | .extractMin => fun a => a.bind
        (Function.partialInv (fun p : Fin n × ℕ => (p.1.val, p.2)))

private theorem observe_erasure {n : ℕ} (a : Option (Fin n × ℕ)) :
    (Option.map (fun p : Fin n × ℕ => (p.1.val, p.2)) a).bind
      (Function.partialInv (fun p : Fin n × ℕ => (p.1.val, p.2))) = a := by
  have hi : Function.Injective (fun p : Fin n × ℕ => (p.1.val, p.2)) := by
    intro a b h
    exact Prod.ext (Fin.ext (congrArg (fun p : ℕ × ℕ => p.1) h))
      (congrArg (fun p : ℕ × ℕ => p.2) h)
  cases a with
  | none => rfl
  | some a => exact Function.partialInv_left hi a

/-- Full method runs agree with the original refinement, including every memory cell, frontier
and source-history entry. The original queue validity supplies each native entry domain. -/
theorem implements {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (hfit : Fits w (base + (9 * n + 5))) :
    (backend n K base).Implements (memRefinement hn hK base) where
  run o s := by
    cases o with
    | isEmpty => rfl
    | getKey v =>
      change (Memory.spec w).runClient s (DataStructure.link ((layout n base).methods w)
        (getKey v.val)) = (Memory.spec w).runClient s
          (DataStructure.link ((layout n base).methods 0) (getKey v.val))
      rw [link_width (w := w)]
      rfl
    | insert v key =>
      change (Memory.spec w).runClient s (DataStructure.link ((layout n base).methods w)
        (insert v.val key)) = (Memory.spec w).runClient s
          (DataStructure.link ((layout n base).methods 0) (insert v.val key))
      rw [link_width (w := w)]
      rfl
    | decreaseKey v key =>
      change (Memory.spec w).runClient s (DataStructure.link ((layout n base).methods w)
        (decreaseKey n v.val key)) = (Memory.spec w).runClient s
          (DataStructure.link ((layout n base).methods 0) (decreaseKey n v.val key))
      rw [link_width (w := w)]
      rfl
    | extractMin =>
      change (Memory.spec w).runClient s (DataStructure.link ((layout n base).methods w)
        (extractMin n)) = Prod.map _ id ((Memory.spec w).runClient s
          (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (extractRaw n)))
      rw [runClient_extractRaw, link_width (w := w)]
      simp only [Prod.map, id_eq, backend, observe_erasure]
  entry o hw hs hv := by
    have hnf : Fits w n := hfit.of_le (by omega)
    have hbf : Fits w base := hfit.of_le (by omega)
    have hvf (v : Fin n) : Fits w v.val := hn.of_le v.isLt.le
    cases o with
    | isEmpty =>
      dsimp only [backend, certificates, Matrix.cons_val_zero]
      exact ⟨by intro i; fin_cases i <;> assumption, hfit⟩
    | getKey v =>
      dsimp only [backend, certificates, Matrix.cons_val_one]
      exact ⟨by intro i; fin_cases i <;> first | exact hnf | exact hbf | exact hvf v,
        hfit, v.isLt⟩
    | insert v key =>
      dsimp only [backend, certificates, Matrix.cons_val_two]
      exact ⟨by intro i; fin_cases i <;>
        first | exact hnf | exact hbf | exact hvf v | exact hK.of_le hv.2,
        hfit, v.isLt⟩
    | decreaseKey v key =>
      dsimp only [backend, certificates, Matrix.cons_val_three]
      obtain ⟨⟨k₀, hOld, hle⟩, hk⟩ := hv
      refine ⟨?_, hfit, hs.1, v, K, k₀, rfl, hK, hs.2, hOld, hle, hk⟩
      intro i
      fin_cases i <;> first | exact hnf | exact hbf | exact hvf v | exact hK.of_le hk
    | extractMin =>
      dsimp only [backend, certificates, Matrix.cons_val_four]
      exact ⟨by intro i; fin_cases i <;> assumption, hfit, hs.1, K, hK, hs.2⟩

/-- The shared native execution adapter, with argument installation external to its clock. -/
@[expose] noncomputable def implementation {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (hfit : Fits w (base + (9 * n + 5))) := Backend.implementation (implements hn hK hfit)

/-- The native family retains the original potential, scaled by one factor fixed before all
runtime parameters. Its charges are the existing constant read/update and logarithmic extract
amortized charges, plus the shared body-entry/exit unit. -/
theorem amortized {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (hfit : Fits w (base + (9 * n + 5))) :
    DataStructure.Amortized (implementation hn hK hfit) id
      (fun _ x => Backend.factor certificates *
        (potential n ((layout n base).abs (memoryState (Backend.frontier certificates) x)) + 0))
      (fun s o => Backend.factor certificates * (charge n s o + 1)) := by
  have hw : ∀ {s} o, (memRefinement hn hK base).inv s →
      (indexedMinPQSpec n K).valid ((memRefinement hn hK base).abs s) o →
      (certificates ((backend n K base).tag o)).work ((backend n K base).arg o) s ≤ 0 := by
    intro s o _ _
    cases o <;> exact le_rfl
  have h := Backend.amortized (implements hn hK hfit) (mem_amortized hn hK base) 0 hw
  simpa only [implementation, Nat.add_zero] using h

/-- Every native method body preserves every cell outside the old source footprint. -/
theorem modifies {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (hfit : Fits w (base + (9 * n + 5))) {s : (indexedMinPQSpec n K).State}
    {x y : Data (Backend.registers certificates)} {o : IndexedMinPQ.Op n}
    {a : o.Result} {steps : ℕ} (hr : (implementation hn hK hfit).rep s x)
    (hv : IndexedMinPQ.valid K s o) (he : (backend n K base).exec w x o a y steps) :
    Modifies (footprint n base) x.mem y.mem := by
  have h := Backend.modifies (M := framed hn hK base) (implements hn hK hfit) hr hv he
  simpa only [Memory.Framed.region, framed, Memory.Framed.ofStatic, Nat.add_zero,
    Finset.Ico_self, Finset.union_empty] using h

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
