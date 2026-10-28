/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInvariant
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalEmission

/-!
# Deriving every native visit fit from the worklist envelope

The fixed arena envelope covers the current heap, every live source block and every candidate
product. This discharges the actual selector and node calls uniformly, without asking the loop
invariant to carry per-call execution advice or a separate width for each selected modulus.

## Main results

* `emit_admitted`: exact native emission from a loaded admissible entry and the common envelope.

These resource and composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- The worklist's one signed envelope derives every local native kernel fit. -/
theorem emit_admitted {a : Arena} {w : ℕ} (x : Data 128) (e : Entry)
    (ha : a.Separated) (hw : a.Ready w) (hc : a.Controls x)
    (hl : e.Loaded x) (hv : e.Valid a.n a.U) (hs : e.Stored x.mem)
    (hbitmap : a.Bitmap x.mem) (hfloor : a.floor ≤ x.regs heap)
    (hheap : x.regs heap ≤ a.ceiling)
    (hsrc : ∀ j, e.source j + (e.data j).length ≤ x.regs heap)
    (htable : x.regs outputs + x.regs outputCount < x.regs heap) :
    ∃ y, ExecWithin (w + 2) visit x y (visitTime a.n a.m a.N) ∧
      Nonempty (Emission (Nat.primesLE a.m) a.Λ e x y) := by
  rcases hc with ⟨hm, hΛ, hU, hN, hb, hcard, ht, hstack, hcap, hz, hone⟩
  have hsum := envelope_ge_sum a.ceiling a.n a.m a.Λ a.U a.N
  have hbound {z : ℤ} (hz : z.natAbs ≤ envelope a.ceiling a.n a.m a.Λ a.U a.N) :
      GenericRAM.Signed.Fits w z := GenericRAM.Signed.Fits.of_natAbs_le hw.2.2 hz
  have hunsigned := Signed.unsigned_fits_of_signed hw.2.2
  have hlen (j : Fin 3) : x.regs (arrayLength j) ≤ a.n := by
    rw [hl.2.2]
    exact hv.length_le j
  have hsource (j : Fin 3) : x.regs (arraySource j) + x.regs (arrayLength j) ≤ a.ceiling := by
    rw [hl.2.1, hl.2.2]
    exact (hsrc j).trans hheap
  have hbitmapBase : x.regs bitmap ≤ a.ceiling := by
    rw [hb]
    have h₀ := ha.1
    have h₁ := ha.2.1
    have h₂ := ha.2.2.1
    omega
  obtain ⟨y, he, hem⟩ := emit_entry x e hl (by simpa only [hU] using hv) hs
    (by rw [hm]; exact hw.1)
    (by apply hbound; simp only [hm, Int.natAbs_natCast]; omega)
    (hunsigned.of_le (modulus_budget_le_envelope x a.ceiling a.n a.m a.Λ a.U a.N hheap
      hsource hlen hm.le hΛ.le
      (by rw [hcard]; exact Nat.card_primesLE_le a.m) hbitmapBase))
    (by
      intro M _ hM
      apply hbound
      simp only [Int.natAbs_natCast]
      exact node_budget_le_envelope x a.ceiling a.n a.m a.Λ a.U a.N M hheap hlen
        (by simpa only [hm] using hM) hU.le hN.le)
    (by rw [hm, hN]; exact hw.2.1)
    (by rw [hm, hcard])
    (by
      rw [hb, hm]
      have h₀ := ha.1
      have h₁ := ha.2.1
      have h₂ := ha.2.2.1
      omega)
    (by simpa only [Arena.Bitmap, hm, hb] using hbitmap)
    (by
      intro j i hi
      apply hbound
      exact (hv.natAbs_le j i hi).trans (by omega))
    hsrc hone htable
  exact ⟨y, by simpa only [hm, hN] using he, by simpa only [hm, hΛ] using hem⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
