/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingSetup
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingReserve

/-!
# Completing the native forest reservations

The actual power loop computes the per-root tree reservation. Three further instructions multiply
by the root count and place the initial heap above the complete pointer table.

## Main results

* `finish_exec`: execute reservation and layout completion with exact native heap/table metadata.

The native composition and memory-frame proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Compute all root reservations and the actual first fresh heap address by native code. -/
theorem finish_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hc : (arena κ n x.mem).Controls x) (hcount : x.regs Traversal.outputCount = 0)
    (hp : x.regs power = 1)
    (hr : x.regs remaining = Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1)
    (hscalar : x.regs scalar = 3)
    (hpow : Fits w (3 ^ (Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1)))
    (hfloor : Fits w (arena κ n x.mem).floor) :
    ∃ y, ExecWithin w (.seq reserve finishLayout) x y
        (4 * (Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1) + 5) ∧
      Saved κ n y ∧ (arena κ n x.mem).Controls y ∧
      y.regs Traversal.outputCount = 0 ∧ y.regs Traversal.heap = (arena κ n x.mem).floor ∧
      y.regs outputCapacity = (arena κ n x.mem).outputCapacity ∧
      y.regs heapFloor = (arena κ n x.mem).floor ∧ y.mem = x.mem := by
  let a := arena κ n x.mem
  obtain ⟨p, he, hpower, _, hmem, hregs⟩ := reserve_exec x hp hr hs.zero hs.one hscalar hpow
  have ps : Saved κ n p := hs.congr (fun i hi hj => hregs i
    (by intro hh; subst i; norm_num [power] at hj)
    (by intro hh; subst i; norm_num [remaining] at hj))
  have pc : a.Controls p := hc.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hregs i (by intro hh; subst i; norm_num [power] at hi)
      (by intro hh; subst i; norm_num [remaining] at hi))
  have pcount : p.regs Traversal.outputCount = 0 :=
    (hregs _ (by decide) (by decide)).trans hcount
  let y := p |>.set outputCapacity a.outputCapacity |>.set Traversal.heap a.floor
    |>.set heapFloor a.floor
  have hcap : Fits w a.outputCapacity := hfloor.of_le (by dsimp only [a, arena]; omega)
  have hout := pc.2.2.2.2.2.2.1
  dsimp only [a, arena] at hcap hfloor hout
  have hz : Exec w finishLayout p y 3 := by
    ram_eval [finishLayout, y, a, arena, ps.count, hpower, hout, hcap, hfloor,
      outputCapacity, roots, power, Traversal.outputs, Traversal.heap, heapFloor]
  have ys : Saved κ n y := ps.congr (fun i hi hj => hz.within.regs_eq (by
    have hh : ∀ i : Fin 128, 109 ≤ i.val → (i.val ≤ 120 ∨ i.val = 126) →
        finishLayout.Preserves i := by decide
    exact hh i hi hj))
  have yc : a.Controls y := pc.congr (by
    intro i hi
    apply hz.within.regs_eq
    have hh : ∀ i : Fin 128, i.val ∈ [71, 72, 73, 74, 75, 76, 78, 80, 81, 82, 83] →
        finishLayout.Preserves i := by decide
    exact hh i hi)
  refine ⟨y, (he.seq hz.within).mono (by omega), ys, yc, ?_, ?_, ?_, ?_, hmem⟩
  · simpa +decide [y, outputCapacity, Traversal.heap, heapFloor,
      Traversal.outputCount] using pcount
  all_goals simp +decide [y, a, outputCapacity, Traversal.heap, heapFloor]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
