/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Program
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLocalEmission
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Reusing the consumed node's packed tail

After the actual Convolution consumer returns, one native copy moves the committed frontier to
the packed pointer. Every live heavy child and pending ancestor column ends before this pointer.
The packed, residue and histogram tail can therefore be overwritten by the next native node.
Heavy arrays and their capacity/count cells remain allocated; the shared reserved gap remains.

The emission witness stays anchored before consumption and release. Its heap equation describes
the complete node endpoint, whereas the released state has the smaller committed frontier.
No total-space or touched-high-water bound for arbitrary callee scratch is asserted here.

## Main definitions

* `releaseState`: the actual one-copy result in the full caller register bank.

## Main results

* `exec_releasePacked`: the exact one-instruction native execution.
* `release_frontier`: exact committed allocation advance, retaining only heavy-array capacities.
* `release_children_ends`: all actual heavy children remain below the released frontier.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open ChanHe.Traversal

/-- Exact full-bank state after copying the consumed packed pointer to the heap register. -/
@[expose] def releaseState {r : ℕ} (v : Data (registerCount r)) : Data (registerCount r) :=
  v.set (preprocessingRegisters r heap) (v.regs (preprocessingRegisters r packed))

/-- The released pointer is already actual metadata; copying it costs one native instruction. -/
theorem exec_releasePacked {r w : ℕ} (v : Data (registerCount r)) :
    Exec w releasePacked v (releaseState v) 1 := Exec.copy

/-- The instruction changes no memory cell. -/
theorem releaseState_mem {r : ℕ} (v : Data (registerCount r)) : (releaseState v).mem = v.mem := rfl

/-- Every register except the actual preprocessing heap is preserved. -/
theorem releaseState_regs {r : ℕ} (v : Data (registerCount r)) (i : Fin (registerCount r))
    (hi : i ≠ preprocessingRegisters r heap) : (releaseState v).regs i = v.regs i := by
  simp only [releaseState, Data.set_regs, Function.update_of_ne hi]

/-- The actual preprocessing view receives exactly the corresponding single register update. -/
theorem releaseState_pre {r : ℕ} (v : Data (registerCount r)) :
    (releaseState v).comap (preprocessingRegisters r) =
      (v.comap (preprocessingRegisters r)).set heap (v.regs (preprocessingRegisters r packed)) :=
  Data.comap_set (preprocessing_injective r) v heap _

/-- The committed allocation advances by exactly the heavy capacities and three count cells. -/
theorem release_frontier {r : ℕ} {Q : Finset ℕ} {Λ : ℕ} {e : Entry}
    {x q : Data 128} {v : Data (registerCount r)}
    (em : Emission Q Λ e x q false)
    (hr : ∀ i, v.regs (preprocessingRegisters r i) = q.regs i) :
    (releaseState v).regs (preprocessingRegisters r heap) = x.regs heap + 3 +
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) := by
  have hp : v.regs (preprocessingRegisters r packed) = (recordLayout x em.M).packed :=
    (hr packed).trans em.packedPointer
  change v.regs (preprocessingRegisters r packed) = _
  rw [hp]
  rfl

/-- Releasing a dead tail retains a monotonically advancing persistent heavy-array frontier. -/
theorem release_heap_mono {r : ℕ} {Q : Finset ℕ} {Λ : ℕ} {e : Entry}
    {x q : Data 128} {v : Data (registerCount r)}
    (em : Emission Q Λ e x q false)
    (hr : ∀ i, v.regs (preprocessingRegisters r i) = q.regs i) :
    x.regs heap ≤ (releaseState v).regs (preprocessingRegisters r heap) := by
  rw [release_frontier em hr]
  omega

/-- The exact discarded tail consists of the packed block, residue workspace and histogram. -/
theorem release_dead_tail {r : ℕ} {Q : Finset ℕ} {Λ : ℕ} {e : Entry}
    {x q : Data 128} {v : Data (registerCount r)}
    (em : Emission Q Λ e x q false)
    (hr : ∀ i, v.regs (preprocessingRegisters r i) = q.regs i) :
    v.regs (preprocessingRegisters r heap) =
      (releaseState v).regs (preprocessingRegisters r heap) +
        (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) + 4 * x.regs groups + em.M := by
  have hh : v.regs (preprocessingRegisters r heap) = (recordLayout x em.M).endpoint :=
    (hr heap).trans em.heap_eq
  rw [hh, release_frontier em hr, recordLayout_endpoint]
  omega

/-- The released frontier stays below the completed node's original allocation endpoint. -/
theorem release_heap_le {r : ℕ} {Q : Finset ℕ} {Λ : ℕ} {e : Entry}
    {x q : Data 128} {v : Data (registerCount r)}
    (em : Emission Q Λ e x q false)
    (hr : ∀ i, v.regs (preprocessingRegisters r i) = q.regs i) :
    (releaseState v).regs (preprocessingRegisters r heap) ≤
      v.regs (preprocessingRegisters r heap) := by
  have h := release_dead_tail em hr
  omega

/-- Every child, including unchanged parent columns, remains live below the new frontier. -/
theorem release_children_ends {r : ℕ} {Q : Finset ℕ} {Λ : ℕ} {e : Entry}
    {x q : Data 128} {v : Data (registerCount r)}
    (em : Emission Q Λ e x q false)
    (hr : ∀ i, v.regs (preprocessingRegisters r i) = q.regs i) (hl : e.Loaded x)
    (hend : ∀ j, e.source j + (e.data j).length ≤ x.regs heap) :
    ∀ d ∈ em.children, ∀ j, d.source j + (d.data j).length ≤
      (releaseState v).regs (preprocessingRegisters r heap) := by
  have hp : v.regs (preprocessingRegisters r packed) = (recordLayout x em.M).packed :=
    (hr packed).trans em.packedPointer
  change ∀ d ∈ em.children, ∀ j, d.source j + (d.data j).length ≤
    v.regs (preprocessingRegisters r packed)
  rw [hp]
  exact em.children_ends_packed hl hend

/-- All persistent traversal controls survive; the heap is not one of those fixed parameters. -/
theorem release_controls {r : ℕ} {a : Arena} {v : Data (registerCount r)}
    (hc : a.Controls (v.comap (preprocessingRegisters r))) :
    a.Controls ((releaseState v).comap (preprocessingRegisters r)) := by
  apply hc.congr
  intro i hi
  apply releaseState_regs
  intro he
  have hei := (preprocessing_injective r) he
  subst i
  norm_num [List.mem_cons, heap] at hi

/-- All child descriptor words survive the copy, including zero-length column pointers. -/
theorem release_childWords {r : ℕ} (v : Data (registerCount r)) (j : Fin 3) :
    childWords ((releaseState v).comap (preprocessingRegisters r)) j =
      childWords (v.comap (preprocessingRegisters r)) j := by
  rw [releaseState_pre]
  fin_cases j <;> rfl

/-- The entire actual stack view is unchanged, including its boundedness and concrete contents. -/
theorem release_stack {r w base capacity : ℕ} {vs : List ℕ} {v : Data (registerCount r)}
    (hs : WordStack.Rep w base capacity vs
      ((v.comap (preprocessingRegisters r)).comap registers)) :
    WordStack.Rep w base capacity vs
      (((releaseState v).comap (preprocessingRegisters r)).comap registers) := by
  have hne : ∀ i : Fin 9, registers i ≠ heap := by decide
  rw [releaseState_pre, Data.comap_set_of_forall_ne _ _ _ hne]
  exact hs

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
