/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalEmissionFrame

/-!
# Actual Chan–He emissions for an in-place consumer

The complete native modulus and node kernels enter the local delivery block without writing
an output-pointer table. Semantic readback and all three child descriptors reuse the same
emission API as catalogue production, with publication explicitly disabled.

## Main results

* `emit_local_entry`: actual charged construction and exact local heavy/packed readback.

This local theorem does not supply a solver execution or a complete initialized decision result.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Execute the complete kernels and local delivery, with no table or counter premise. -/
theorem emit_local_entry {w n : ℕ} (x : Data 128) (e : Entry) (hl : e.Loaded x)
    (hv : e.Valid n (x.regs magnitude)) (hs : e.Stored x.mem)
    (hm : 2 ≤ x.regs limit)
    (hmod : GenericRAM.Signed.Fits w ((x.regs limit ^ 2 : ℕ) : ℤ))
    (hbudget : Fits (w + 2) (Modulus.budget ((modulusState x).comap kernel)))
    (hnode : ∀ M, 1 ≤ M → M ≤ x.regs limit ^ 2 →
      GenericRAM.Signed.Fits w ((recordLayout x M).budget : ℤ))
    (hN : 2 * x.regs limit ^ 2 ≤ x.regs groups)
    (hcard : x.regs primeCount = (Nat.primesLE (x.regs limit)).card)
    (hbefore : x.regs bitmap + x.regs limit < x.regs heap)
    (hbitmap : ∀ q ≤ x.regs limit,
      x.mem (x.regs bitmap + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < (e.data j).length → GenericRAM.Signed.Fits w (e.read j i))
    (hsrc : ∀ j, e.source j + (e.data j).length ≤ x.regs heap)
    (hone : x.regs one = 1) :
    ∃ y, ExecWithin (w + 2) localVisit x y
      (visitTime n (x.regs limit) (x.regs groups)) ∧
      Nonempty (Emission (Nat.primesLE (x.regs limit)) (x.regs digits) e x y false) := by
  classical
  obtain ⟨M, u, b, he, hu, hus, hprefix, hout, hb, hMpos, hMle, hM⟩ :=
    construct_exec x e.read hm hmod hbudget hnode hN hcard hbefore hbitmap
      (by simpa only [hl.2.2] using hvalues)
      (by intro j i hi; exact hv.natAbs_le j i ((hl.2.2 j) ▸ hi))
      (by simpa only [hl.2.1, hl.2.2] using hsrc)
      (by simpa only [hl.2.1, hl.2.2] using hs.input)
      (by intro j; simpa only [hl.2.2] using e.read_injOn j (hv.1 j))
  have hbp (i : Fin 128) (hi : 64 ≤ i.val) (hne : i ≠ selected) :
      b.regs i = x.regs i := (hb i hi).trans (hu i hi hne)
  have hL : NodePacking.layout ((nodeState b).comap kernel) = recordLayout x M := by
    rw [nodeState_layout, hb selected (by decide), hus]
    exact recordLayout_congr x b M hbp
  have hEnd : Fits (w + 2) ((recordLayout x M).endpoint) :=
    (Signed.unsigned_fits_of_signed (hnode M hMpos hMle)).of_le
      (recordLayout x M).bounds.1
  have hEndEq : (recordLayout x M).endpoint = b.regs heap + 3 + 2 *
      (b.regs (slot 2) + b.regs (slot 4) + b.regs (slot 6)) +
      4 * b.regs groups + b.regs selected := by
    rw [← hL, nodeState_layout, recordLayout_endpoint]
  rw [hEndEq] at hEnd
  have hd := deliverLocal_exec b ((hbp _ (by decide) (by decide)).trans hone) hEnd
  refine ⟨localDeliveryState b, (he.seq hd.within).mono ?_, ?_⟩
  · have ht := visit_cost_le x n (x.regs limit) (x.regs groups) M
      (by intro j; rw [hl.2.2]; exact hv.length_le j) le_rfl le_rfl hMle
    omega
  · exact emission_readback false x e hl hv M u b hu hus hprefix hout hb hMpos hMle hM
      (by intro h; cases h)

/-- One admission interface for the fixed catalogue and local-consumer programs. Only the
catalogue specialization needs a table-address fit. The flag selects fixed code before input. -/
theorem emit_with_publication {w n : ℕ} (published : Bool) (x : Data 128) (e : Entry)
    (hl : e.Loaded x)
    (hv : e.Valid n (x.regs magnitude)) (hs : e.Stored x.mem)
    (hm : 2 ≤ x.regs limit)
    (hmod : GenericRAM.Signed.Fits w ((x.regs limit ^ 2 : ℕ) : ℤ))
    (hbudget : Fits (w + 2) (Modulus.budget ((modulusState x).comap kernel)))
    (hnode : ∀ M, 1 ≤ M → M ≤ x.regs limit ^ 2 →
      GenericRAM.Signed.Fits w ((recordLayout x M).budget : ℤ))
    (hN : 2 * x.regs limit ^ 2 ≤ x.regs groups)
    (hcard : x.regs primeCount = (Nat.primesLE (x.regs limit)).card)
    (hbefore : x.regs bitmap + x.regs limit < x.regs heap)
    (hbitmap : ∀ q ≤ x.regs limit,
      x.mem (x.regs bitmap + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < (e.data j).length → GenericRAM.Signed.Fits w (e.read j i))
    (hsrc : ∀ j, e.source j + (e.data j).length ≤ x.regs heap)
    (hone : x.regs one = 1)
    (htable : published = true → x.regs outputs + x.regs outputCount < x.regs heap) :
    ∃ y, ExecWithin (w + 2) (if published then visit else localVisit) x y
      (visitTime n (x.regs limit) (x.regs groups)) ∧
      Nonempty (Emission (Nat.primesLE (x.regs limit)) (x.regs digits) e x y published) := by
  cases published with
  | false =>
    simpa using emit_local_entry x e hl hv hs hm hmod hbudget hnode hN hcard hbefore
      hbitmap hvalues hsrc hone
  | true =>
    simpa using emit_entry x e hl hv hs hm hmod hbudget hnode hN hcard hbefore
      hbitmap hvalues hsrc hone (htable rfl)

/-- Local delivery preserves every old prefix cell, with no excluded table address. -/
theorem Emission.local_prefix {Q : Finset ℕ} {Λ : ℕ} {e : Entry} {x y : Data 128}
    (h : Emission Q Λ e x y false) (p : ℕ) (hp : p < x.regs heap) : y.mem p = x.mem p := by
  have hm : y.mem = h.before := by simpa using h.memory
  rw [hm]
  exact h.prefixMemory p hp


end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
