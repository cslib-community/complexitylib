/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Memory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Exec
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Input

/-!
# Actual routing in the product caller's register bank

## Main results

* `QueriedProduct.exec_wanted`: invoke the existing router on real coordinates while retaining
  the caller's protected addresses, including its untouched original-input snapshot.

No routing or permutation certificate is an input. The computed memory equations in this
internal interface are conclusions of the actual finite native program.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The existing actual router runs in the low bank and preserves every caller scalar.
Its stable permutation retains separate occurrences of duplicate requests. -/
public theorem exec_wanted {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (x : Data 160) (hp : Parameters L m N qs.length x)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N)
    (hQ : x.mem 4 = qs.length)
    (hinput : ∀ i < qs.length,
      x.mem (5 + 2 * i) = (Wanted.inputPairs qs i).1 ∧
        x.mem (5 + 2 * i + 1) = (Wanted.inputPairs qs i).2)
    (hfit : Fits w (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin w (Wanted.program.rename bank) x y (Wanted.timeBound L m N qs.length) ∧
      Parameters L m N qs.length y ∧ Wanted.Parameters L m N qs.length (y.comap bank) ∧
      (∀ i : Fin qs.length,
        y.mem (Wanted.codeAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
          y.mem (Wanted.originalAddress L m N qs.length +
            CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
              i.val) ∧
      (∀ t ≤ numBands L m N ^ 2,
        y.mem (Wanted.offsetAddress L m N qs.length + t) =
          Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length) ∧
      y.mem (Wanted.offsetAddress L m N qs.length + numBands L m N ^ 2) = qs.length ∧
      (∀ a, a < Wanted.inputLimit qs.length ∨ Wanted.memoryLimit L m N qs.length ≤ a →
        y.mem a = x.mem a) := by
  obtain ⟨z, he, zp, zv, zo, zlast, zframe⟩ := Wanted.exec_program hm (Wanted.inputPairs qs)
    (Wanted.inputPairs_lt qs) (x.comap bank) hL hmemory hN hQ hinput (producer_fits hfit).2
  let y := z.extend bank x
  have hf (i : Fin 160) (hi : 96 ≤ i.val) : y.regs i = x.regs i := by
    have hnot : ¬∃ j, bank j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun r : Fin 160 => r.val) hj
      change j.val = i.val at hv
      omega
    exact Function.extend_apply' _ _ _ hnot
  refine ⟨y, he.rename bank_injective, hp.reframe hf, ?_, ?_, zo, zlast, zframe⟩
  · simpa only [y, Data.comap_extend bank_injective] using zp
  · intro i
    change z.mem _ = _ ∧ z.mem _ = _
    simpa only [Wanted.inputPairs_get] using zv i.val i.isLt

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
