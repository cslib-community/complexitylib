/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorInvariant

/-!
# Direct solver envelopes for an interleaved Chan–He visitor

The fixed arena's existing admission envelope bounds allocations, common packed length and
packed values before any standalone catalogue run is completed. These bounds therefore apply
to actual nodes reached while native solver calls are interleaved with traversal.

## Main results

* `arena_resources`: endpoints, packed length and signed values fit the caller's value envelope.
* `packed_values`: direct bounds on every value supplied by an admitted pending entry.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM

/-- Pure layout and admission bounds, independent of any completed preprocessing execution. -/
theorem arena_resources (κ n : ℕ) (retained : ℕ → ℕ) :
    let a := ChanHe.Preprocessing.arena κ n retained
    a.ceiling < (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ := by
  let a := ChanHe.Preprocessing.arena κ n retained
  let S := a.ceiling + a.n + a.m ^ 2 + a.Λ + a.m + a.U + a.N + 100
  have hS : S ≤ S ^ 4 := Nat.le_self_pow (by decide) S
  have hready := ChanHe.Preprocessing.arena_ready (κ := κ) (n := n) le_rfl retained
  have hfit := Signed.unsigned_fits_of_signed hready.2.2
  have hw := ChanHe.Preprocessing.three_le_width κ n
  rw [show ChanHe.Preprocessing.width κ n - 2 + 2 =
    ChanHe.Preprocessing.width κ n by omega] at hfit
  have henv : ChanHe.Traversal.envelope a.ceiling a.n a.m a.Λ a.U a.N <
      (n + 2) ^ envelopeExponent κ :=
    hfit.trans_le (ChanHe.Preprocessing.two_pow_width_le κ n)
  change 65536 * S ^ 4 < (n + 2) ^ envelopeExponent κ at henv
  dsimp only [S] at hS
  change a.ceiling < _ ∧ 4 * a.N < _ ∧ 60 * a.U + 40 ≤ _
  dsimp only [S] at henv
  omega

/-- Every actual packed value follows from the pending entry's finite input promises. -/
theorem packed_values {κ n : ℕ} {retained : ℕ → ℕ} {e : ChanHe.Traversal.Entry}
    (h : e.Valid (ChanHe.Preprocessing.arena κ n retained).n
      (ChanHe.Preprocessing.arena κ n retained).U) (i : ℕ) :
    |(e.task.node (Nat.primesLE (ChanHe.Preprocessing.arena κ n retained).m)
      (ChanHe.Preprocessing.arena κ n retained).Λ).oneArray
        (ChanHe.Preprocessing.arena κ n retained).U i| ≤
      (((n + 2) ^ envelopeExponent κ : ℕ) : ℤ) := by
  have hb := (arena_resources κ n retained).2.2
  exact (h.abs_oneArray_le _ _ i).trans (by exact_mod_cast hb)

/-- The concrete emitted pointer, readback and arena bounds discharge the actual host contract. -/
theorem exec_consume_emission {r κ n w : ℕ} {a : ChanHe.Traversal.Arena}
    (c : Host.Callee r) (e : ChanHe.Traversal.Entry) (x : Data 128)
    (v : Data (registerCount r))
    (em : ChanHe.Traversal.Emission
      (Nat.primesLE a.m)
      a.Λ e x
      (v.comap (preprocessingRegisters r)) false)
    (hc : a.Controls x)
    (hv : e.Valid a.n
      a.U)
    (hw : width κ c.widthCoefficient n ≤ w)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hheap : v.regs (preprocessingRegisters r ChanHe.Traversal.heap) ≤
      a.ceiling)
    (hlen : v.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) =
      4 * a.N)
    (hbound : v.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ)
    (hone : v.regs (controllerRegisters r one) = 1)
    (hb : v.regs (controllerRegisters r answer) ≤ 1) :
    ∃ y, ExecWithin w (consume c.code) v y
        (Host.callerTime (4 * a.N)
          (c.time (Host.sideLength (4 * a.N))
            (2 * (n + 2) ^ envelopeExponent κ + 1)) + 7) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        v.regs (controllerRegisters r answer) = 1 ∨
          Cslib.Algorithms.ThreeSum.Convolution
            (4 * a.N)
            ((e.task.node (Nat.primesLE a.m)
              a.Λ).oneArray
                a.U)) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = v.regs (preprocessingRegisters r i)) ∧
      (∀ i, i ≠ answer →
        y.regs (controllerRegisters r i) = v.regs (controllerRegisters r i)) ∧
      ∀ p < v.regs (preprocessingRegisters r ChanHe.Traversal.heap), y.mem p = v.mem p := by
  have hN : x.regs ChanHe.Traversal.groups = a.N := hc.2.2.2.1
  have hU : x.regs ChanHe.Traversal.magnitude = a.U := hc.2.2.1
  have hp : v.regs (preprocessingRegisters r ChanHe.Traversal.packed) =
      (ChanHe.Traversal.recordLayout x em.M).packed := em.packedPointer
  have he : v.regs (preprocessingRegisters r ChanHe.Traversal.heap) =
      (ChanHe.Traversal.recordLayout x em.M).endpoint := em.heap_eq
  apply exec_consume c v _ hw hresources.2.1
    (hheap.trans hresources.1) hlen hbound rfl hone rfl hb
  · rw [hp, he]
    dsimp only [ChanHe.NodePacking.Layout.endpoint, ChanHe.NodePacking.Layout.hist,
      ChanHe.NodePacking.Layout.scratch, ChanHe.Traversal.recordLayout]
    omega
  · intro i _
    exact (hv.abs_oneArray_le _ _ i).trans (by exact_mod_cast hresources.2.2)
  · intro i hi
    have hi' : i < 4 * x.regs ChanHe.Traversal.groups := by simpa only [hN] using hi
    have hm := em.packed ⟨i, hi'⟩
    rw [hp]
    simpa only [Block.read, Data.comap_mem, hU] using hm

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
