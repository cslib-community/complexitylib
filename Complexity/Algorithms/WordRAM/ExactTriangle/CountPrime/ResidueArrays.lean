/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Setup
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.ResidueArray

/-!
# Complete three-matrix native residue prefix

The three genuine calls preserve all original arrays below the computed workspace and each
other's already written output. All argument copies, signed remainder, decoding, stores and
loop controls are charged. This is the first memory-producing stage of the complete counter.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Compute all original unsigned residue words using only actual caller matrix data. -/
theorem exec_residueArrays {w n p k scratch a b c : ℕ} (x : Data 128)
    (u v z : ℕ → ℤ) (hp : 0 < p) (ready : CounterRegisters n p k scratch a b c x)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hu : ∀ i < n * n, GenericRAM.Signed.Fits w (u i))
    (hv : ∀ i < n * n, GenericRAM.Signed.Fits w (v i))
    (hz : ∀ i < n * n, GenericRAM.Signed.Fits w (z i))
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hw : Fits (w + 2) (addressBudget n p k scratch a b c)) :
    ∃ y, ExecWithin (w + 2) residueArrays x y (69 * (n * n) + 24) ∧
      CounterRegisters n p k scratch a b c y ∧
      (∀ i < n * n, y.mem (scratch + i) = (u i % (p : ℤ)).toNat) ∧
      (∀ i < n * n, y.mem (scratch + n * n + i) = (v i % (p : ℤ)).toNat) ∧
      (∀ i < n * n, y.mem (scratch + 2 * (n * n) + i) = (z i % (p : ℤ)).toNat) ∧
      ∀ d, d < scratch ∨ scratch + 3 * (n * n) ≤ d → y.mem d = x.mem d := by
  have h4pos : 0 < 4 ^ k := by positivity
  have h2pos : 0 < 2 ^ k := by positivity
  have fit (d : ℕ) (hd : d ≤ addressBudget n p k scratch a b c) : Fits (w + 2) d := hw.of_le hd
  have encoded (s : Data 128) (hs : CounterRegisters n p k scratch a b c s) :
      s.regs Reg.encodedModulus = encode (p : ℤ) := by
    rw [hs.layout.encodedModulus_eq]
    simp [encode]
  obtain ⟨x1, run1, val1, frame1, regs1⟩ := exec_residues Reg.inputAB Reg.residueAB x
    (by decide) (by decide) u hp ready.layout.cells_eq ready.inputAB ready.layout.residueAB_eq
    (encoded x ready) hmod hu (fit _ (by unfold addressBudget; omega))
    (fit _ (by unfold addressBudget; omega)) ha hinU
  have meta1 : CounterRegisters n p k scratch a b c x1 := ready.congr
    (fun j hj => regs1 j (by unfold MetadataRegister at hj; omega))
  obtain ⟨x2, run2, val2, frame2, regs2⟩ := exec_residues Reg.inputBC Reg.residueBC x1
    (by decide) (by decide) v hp meta1.layout.cells_eq meta1.inputBC meta1.layout.residueBC_eq
    (encoded x1 meta1) hmod hv (fit _ (by unfold addressBudget; omega))
    (fit _ (by unfold addressBudget; omega)) (by omega)
    (by intro i hi; rw [frame1 _ (Or.inl (by omega))]; exact hinV i hi)
  have meta2 : CounterRegisters n p k scratch a b c x2 := meta1.congr
    (fun j hj => regs2 j (by unfold MetadataRegister at hj; omega))
  obtain ⟨y, run3, val3, frame3, regs3⟩ := exec_residues Reg.inputAC Reg.residueAC x2
    (by decide) (by decide) z hp meta2.layout.cells_eq meta2.inputAC meta2.layout.residueAC_eq
    (encoded x2 meta2) hmod hz (fit _ (by unfold addressBudget; omega))
    (fit _ (by unfold addressBudget; omega)) (by omega)
    (by
      intro i hi
      rw [frame2 _ (Or.inl (by omega)), frame1 _ (Or.inl (by omega))]
      exact hinZ i hi)
  refine ⟨y, (run1.seq (run2.seq run3)).mono (by omega),
    meta2.congr (fun j hj => regs3 j (by unfold MetadataRegister at hj; omega)), ?_, ?_, val3, ?_⟩
  · intro i hi
    rw [frame3 _ (Or.inl (by omega)), frame2 _ (Or.inl (by omega))]
    exact val1 i hi
  · intro i hi
    rw [frame3 _ (Or.inl (by omega))]
    exact val2 i hi
  · intro d hd
    rw [frame3 _ (hd.imp (fun h => by omega) (fun h => by omega)),
      frame2 _ (hd.imp (fun h => by omega) (fun h => by omega)),
      frame1 _ (hd.imp id (fun h => by omega))]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
