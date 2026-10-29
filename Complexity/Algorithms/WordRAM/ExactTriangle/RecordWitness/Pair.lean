/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Kernel

/-!
# One actual product-selected original-weight verification

The coordinate words are loaded from the original interleaved query block. The full renamed
native verifier reads the original three signed arrays, and its result is returned to the
controller. This internal call rule charges delivery, the complete scan and witness return.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- Execute one selected candidate from its actual query words. A reported witness satisfies
the original integer equation, independently of whether the modular candidate was genuine. -/
theorem exec_scanPair {w U n first length out queries count i scans a b : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hi : x.regs Reg.index = i) (hs : x.regs Reg.scans = scans)
    (hf : x.regs Reg.found = 0)
    (haWord : x.mem (queries + 2 * i) = a)
    (hbWord : x.mem (queries + 2 * i + 1) = b)
    (ha : a < n) (hb : b < n) (hc : first + length ≤ n)
    (hmem : ∀ u < n, ∀ v < n,
      x.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      x.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      x.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v))
    (hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ U ∧ (BC u v).natAbs ≤ U ∧ (AC u v).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2)
      (queries + 2 * i + scans + 6 * (n * n) + n + first + length + 32)) :
    ∃ y, ExecWithin (w + 2) scanPair x y (42 * length + 28) ∧
      Fixed n first length out queries count y ∧ y.mem = x.mem ∧
      y.regs Reg.index = i ∧ y.regs Reg.scans = scans + 1 ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔
        ∃ c, first ≤ c ∧ c < first + length ∧ AB a b + BC b c + AC a c = 0) ∧
      (y.regs Reg.found = 1 →
        y.regs Reg.witnessA = a ∧ y.regs Reg.witnessB = b ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB a b + BC b (y.regs Reg.witnessC) + AC a (y.regs Reg.witnessC) = 0) := by
  obtain ⟨d, hd, dFixed, dm, da, db, ds, di, df, -⟩ :=
    exec_deliverPair x hx hi hs haWord hbWord (hfit.of_le (by omega))
  obtain ⟨s, he, sFixed, sm, sa, sb, sf, iffFound, sw, frame⟩ :=
    exec_scan AB BC AC d dFixed da db ha hb hc (by simpa only [dm] using hmem)
      hmag hU (hfit.of_le (by omega))
  obtain ⟨y, hy, yFixed, ym, yf, ya, yb, yc, ys, yi, -⟩ :=
    exec_receiveWitness s sFixed rfl sa sb rfl
  have sIndex : s.regs Reg.index = i := (frame _ (by decide)).trans di
  have sScans : s.regs Reg.scans = scans + 1 := (frame _ (by decide)).trans ds
  have sFound : s.regs Reg.found = 0 := (frame _ (by decide)).trans (df.trans hf)
  have hexe : ExecWithin (w + 2) scanPair x y (42 * length + 28) :=
    (hd.seq (he.seq hy)).mono (by omega)
  have yflag : y.regs Reg.found = s.regs (scanBank WitnessScan.Reg.found) := by
    rcases sf with sf | sf <;> simp only [yf, sf, sFound, Nat.zero_ne_one, ↓reduceIte]
  refine ⟨y, hexe, yFixed, ym.trans (sm.trans dm), yi.trans sIndex, ys.trans sScans,
    ?_, ?_, ?_⟩
  · simpa only [yflag] using sf
  · simpa only [yflag] using iffFound
  · intro hfound
    have hsfound : s.regs (scanBank WitnessScan.Reg.found) = 1 := yflag.symm.trans hfound
    obtain ⟨lo, hi, hz⟩ := sw hsfound
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hsfound, ↓reduceIte] using ya
    · simpa only [hsfound, ↓reduceIte] using yb
    · simpa only [yc, hsfound, ↓reduceIte] using lo
    · simpa only [yc, hsfound, ↓reduceIte] using hi
    · simpa only [yc, hsfound, ↓reduceIte] using hz

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
