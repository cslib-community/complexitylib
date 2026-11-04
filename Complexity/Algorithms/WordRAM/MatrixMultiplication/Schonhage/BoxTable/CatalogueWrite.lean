/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.DigitScan
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueState

/-!
# Charged native stores of box geometry

Both rejected and accepted slots execute a real directory store. Accepted slots also
write their three descriptor words at the actual computed compact rank. No zeroed
directory or precomputed compact-rank certificate is used by the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Scalar registers changed by the native stores and counter updates. -/
@[expose] def WriteLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.count ∨ i = Reg.slot

instance (i : Fin registers) : Decidable (WriteLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.temporary ∨
    i = Reg.count ∨ i = Reg.slot))

private theorem writeSlot_preserves (i : Fin registers) :
    ¬WriteLocal i → writeSlot.Preserves i := by decide +revert

/-- Execute the exact stores after the actual digit scan. -/
theorem exec_writeSlot {w L H D R s : ℕ} (x : Data registers)
    (hd : x.regs Reg.directory = D) (hr : x.regs Reg.records = R)
    (hs : x.regs Reg.slot = s) (hh : x.regs Reg.height = H)
    (hc : x.regs Reg.count = Nat.count (Eligible L H) s)
    (hcode : x.regs Reg.completion = recordCode L s)
    (he : x.regs Reg.stars = recordStars L s)
    (hp : x.regs Reg.population = population (recordCode L s) L)
    (hstride : x.regs Reg.starPower = recordStride L s)
    (h1 : x.regs Reg.one = 1) (h3 : x.regs Reg.three = 3) (h0 : x.regs Reg.nil = 0)
    (hfit : Fits w (D + R + 6 * (s + 1) + 12)) :
    ∃ y, ExecWithin w writeSlot x y 17 ∧
      y.mem = catalogueWrite L H D R s x.mem ∧ y.regs Reg.slot = s + 1 ∧
      y.regs Reg.count = Nat.count (Eligible L H) (s + 1) ∧
      (∀ i, ¬WriteLocal i → y.regs i = x.regs i) := by
  let r := Nat.count (Eligible L H) s
  have hrc : r ≤ s := Nat.count_le _
  have hfds : Fits w (D + s) := hfit.of_le (by omega)
  have hfr : Fits w (r + 1) := hfit.of_le (by omega)
  have hf3r : Fits w (r * 3) := hfit.of_le (by omega)
  have hfra : Fits w (R + r * 3) := hfit.of_le (by omega)
  have hfra1 : Fits w (R + r * 3 + 1) := hfit.of_le (by omega)
  have hfra2 : Fits w (R + r * 3 + 1 + 1) := hfit.of_le (by omega)
  have hfs : Fits w (s + 1) := hfit.of_le (by omega)
  let bad := (((x.set Reg.address (D + s)).write (D + s) 0).set
    Reg.temporary (x.regs Reg.temporary)).set Reg.slot (s + 1)
  let good := ((((((((((((x.set Reg.address (D + s)).write (D + s) 0).set
    Reg.temporary (r + 1)).write (D + s) (r + 1)).set Reg.address (r * 3)).set
    Reg.address (R + r * 3)).write (R + r * 3) (recordCode L s)).set
    Reg.address (R + r * 3 + 1)).write (R + r * 3 + 1) (recordStars L s)).set
    Reg.address (R + r * 3 + 1 + 1)).write (R + r * 3 + 1 + 1) (recordStride L s)).set
    Reg.count (r + 1)).set Reg.slot (s + 1)
  by_cases hlarge : H < population (recordCode L s) L
  · have hv : ¬Eligible L H s := fun h => (Nat.not_lt_of_ge h.2) hlarge
    have hy : ExecWithin w writeSlot x bad 17 := by
      ram_eval [writeSlot, bad, hd, hr, hs, hh, hp, h1, h0, hlarge, hfds, hfs,
        Reg.address, Reg.directory, Reg.records, Reg.slot, Reg.height, Reg.population,
        Reg.temporary, Reg.one, Reg.nil, Fin.mk.injEq]
    refine ⟨bad, hy, ?_, ?_, ?_, fun i hi => hy.regs_eq (writeSlot_preserves i hi)⟩
    · simp [bad, catalogueWrite, hv, directoryWord, Data.write, Data.set]
    · simp [bad, Reg.slot]
    · simpa [bad, Reg.count, Reg.slot, Reg.temporary, Reg.address,
        Nat.count_succ_eq_count hv] using hc
  · by_cases hsmall : population (recordCode L s) L < recordStars L s
    · have hv : ¬Eligible L H s := fun h => (Nat.not_lt_of_ge h.1) hsmall
      have hy : ExecWithin w writeSlot x bad 17 := by
        ram_eval [writeSlot, bad, hd, hr, hs, hh, hp, he, h1, h0,
          hlarge, hsmall, hfds, hfs, Reg.address, Reg.directory, Reg.records, Reg.slot,
          Reg.height, Reg.population, Reg.stars, Reg.temporary, Reg.one, Reg.nil, Fin.mk.injEq]
      refine ⟨bad, hy, ?_, ?_, ?_, fun i hi => hy.regs_eq (writeSlot_preserves i hi)⟩
      · simp [bad, catalogueWrite, hv, directoryWord, Data.write, Data.set]
      · simp [bad, Reg.slot]
      · simpa [bad, Reg.count, Reg.slot, Reg.temporary, Reg.address,
          Nat.count_succ_eq_count hv] using hc
    · have hv : Eligible L H s := ⟨Nat.le_of_not_lt hsmall, Nat.le_of_not_lt hlarge⟩
      have hy : ExecWithin w writeSlot x good 17 := by
        ram_eval [writeSlot, emit, good, r, hd, hr, hs, hh, hc, hcode, he, hp,
          hstride, h1, h3, h0, hlarge, hsmall, hfds, hfr, hf3r, hfra, hfra1, hfra2, hfs,
          Reg.address, Reg.directory, Reg.records, Reg.slot, Reg.height, Reg.population,
          Reg.stars, Reg.completion, Reg.starPower, Reg.temporary, Reg.count,
          Reg.one, Reg.three, Reg.nil, Fin.mk.injEq]
      refine ⟨good, hy, ?_, ?_, ?_, fun i hi => hy.regs_eq (writeSlot_preserves i hi)⟩
      · simp [good, catalogueWrite, hv, directoryWord, r, Data.write, Data.set,
          Function.update_idem, Nat.mul_comm, Nat.add_assoc]
      · simp [good, Reg.slot]
      · simp [good, Reg.count, Reg.slot, r, Nat.count_succ_eq_succ_count hv]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
