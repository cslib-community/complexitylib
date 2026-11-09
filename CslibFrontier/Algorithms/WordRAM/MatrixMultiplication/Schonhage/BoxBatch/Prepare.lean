/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.InputLayout

/-!
# Shared native construction before a query batch

The fourth original header is a query count. One extra native addition moves the shared
directory beyond the wanted-code array. The existing constructor then computes the real
table once. Eleven final instructions initialize both batch cursors and the answer pointer.
No computed table, execution, enumeration or resource certificate is supplied to the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Keep every original wanted code before the shared geometry allocation. -/
@[expose] def relocateDirectory : Code .standard registers := ram[
  BoxTable.Reg.directory ← BoxTable.Reg.directory + BoxQuery.Reg.query ]

/-- Compute actual cursors and reserve the same uncleared stack as the reusable kernel. -/
@[expose] def initializeCursors : Code .standard registers := ram[
  Reg.next ← BoxTable.Reg.arrayB + BoxTable.Reg.span;
  Reg.stop ← Reg.next + BoxQuery.Reg.query;
  BoxTable.Reg.temporary ← #1;
  Reg.output ← BoxTable.Reg.levels + BoxTable.Reg.temporary;
  Reg.output ← Reg.output * BoxTable.Reg.span;
  BoxTable.Reg.temporary ← #10;
  Reg.output ← Reg.output + BoxTable.Reg.temporary;
  BoxTable.Reg.temporary ← #5;
  Reg.output ← Reg.output * BoxTable.Reg.temporary;
  Reg.output ← Reg.output + BoxTable.Reg.values;
  Reg.output ← Reg.output + BoxTable.Reg.count ]

/-- Adapt original words, construct one real table, and initialize the actual batch. -/
@[expose] def prepare : Code .standard registers :=
  .seq BoxQuery.loadInput (.seq relocateDirectory
    (.seq (.seq BoxTable.geometry BoxTable.tile) initializeCursors))

/-- Complete ordinary-input program: shared preparation followed by all wanted queries. -/
@[expose] def program : Code .standard registers := .seq prepare queryProgram

private theorem exec_initializeCursors {w L N V K : ℕ} (x : Data registers)
    (hB : x.regs BoxTable.Reg.arrayB = 5 + 10 ^ L)
    (hT : x.regs BoxTable.Reg.span = 10 ^ L) (hQ : x.regs BoxQuery.Reg.query = N)
    (hL : x.regs BoxTable.Reg.levels = L) (hV : x.regs BoxTable.Reg.values = V)
    (hK : x.regs BoxTable.Reg.count = K)
    (hfit : Fits w (100 * (L + N + V + K + (L + 1) * 10 ^ L + 64))) :
    ∃ y, ExecWithin w initializeCursors x y 11 ∧
      y.regs Reg.next = queryBase L ∧ y.regs Reg.stop = queryBase L + N ∧
      y.regs Reg.output = V + K + 5 * BoxQuery.stackCapacity L ∧ y.mem = x.mem := by
  have hp : 0 < 10 ^ L := Nat.pow_pos (by decide)
  have hT0 : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  have fQ : Fits w (5 + 10 ^ L + 10 ^ L) := hfit.of_le (by omega)
  have fN : Fits w (5 + 10 ^ L + 10 ^ L + N) := hfit.of_le (by omega)
  have fL : Fits w (L + 1) := hfit.of_le (by omega)
  have fT : Fits w ((L + 1) * 10 ^ L) := hfit.of_le (by omega)
  have fC : Fits w ((L + 1) * 10 ^ L + 10) := hfit.of_le (by omega)
  have f1 : Fits w 1 := hfit.of_le (by omega)
  have f10 : Fits w 10 := hfit.of_le (by omega)
  have f5 : Fits w 5 := hfit.of_le (by omega)
  have fS : Fits w (((L + 1) * 10 ^ L + 10) * 5) := hfit.of_le (by omega)
  have fV : Fits w (((L + 1) * 10 ^ L + 10) * 5 + V) := hfit.of_le (by omega)
  have fK : Fits w (((L + 1) * 10 ^ L + 10) * 5 + V + K) := hfit.of_le (by omega)
  let y₀ := ((x.set Reg.next (5 + 10 ^ L + 10 ^ L)).set Reg.stop
    (5 + 10 ^ L + 10 ^ L + N)).set BoxTable.Reg.temporary 1
  let y₁ := (y₀.set Reg.output (L + 1)).set Reg.output ((L + 1) * 10 ^ L)
  let y₂ := (y₁.set BoxTable.Reg.temporary 10).set Reg.output ((L + 1) * 10 ^ L + 10)
  let y₃ := (y₂.set BoxTable.Reg.temporary 5).set Reg.output (((L + 1) * 10 ^ L + 10) * 5)
  let y := (y₃.set Reg.output (((L + 1) * 10 ^ L + 10) * 5 + V)).set Reg.output
    (((L + 1) * 10 ^ L + 10) * 5 + V + K)
  have he : ExecWithin w initializeCursors x y 11 := by
    ram_eval [initializeCursors, y, y₀, y₁, y₂, y₃, hB, hT, hQ, hL, hV, hK,
      fQ, fN, fL, fT, fC, f1, f10, f5, fS, fV, fK, Reg.next, Reg.stop, Reg.output,
      BoxTable.Reg.arrayB, BoxTable.Reg.span, BoxQuery.Reg.query, BoxTable.Reg.levels,
      BoxTable.Reg.one, BoxTable.Reg.ten, BoxTable.Reg.values, BoxTable.Reg.count,
      BoxTable.Reg.temporary, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, rfl⟩
  · simp [y, y₀, y₁, y₂, y₃, queryBase, Reg.next, Reg.stop, Reg.output,
      BoxTable.Reg.temporary]; omega
  · simp [y, y₀, y₁, y₂, y₃, queryBase, Reg.stop, Reg.output, BoxTable.Reg.temporary]; omega
  · simp [y, y₀, y₁, y₂, y₃, BoxQuery.stackCapacity]; omega

/-- The actual batch adapter constructs the retained table and initializes all batch cursors. -/
theorem exec_prepare {w L m t N A B : ℕ} (hmL : m ≤ L) (x : Data registers)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t) (hN : x.mem 4 = N)
    (hleft : ∀ i : Fin (10 ^ L), x.mem (5 + i.val) = Signed.encode (a i))
    (hright : ∀ i : Fin (10 ^ L), x.mem (5 + 10 ^ L + i.val) = Signed.encode (b i))
    (haddr : Fits (w + 2) (originalAddressBound L m t N))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) prepare x y (preparationTime L m t) ∧
      y.regs BoxTable.Reg.levels = L ∧ y.regs BoxTable.Reg.threshold = t ∧
      y.regs BoxTable.Reg.span = 10 ^ L ∧
      y.regs BoxTable.Reg.arrayA = 5 ∧ y.regs BoxTable.Reg.arrayB = 5 + 10 ^ L ∧
      y.regs BoxTable.Reg.directory = directoryBase L N ∧
      y.regs BoxTable.Reg.values = valueBase L m t N ∧
      y.regs BoxTable.Reg.count = (boxes L m t).card ∧
      y.regs Reg.next = queryBase L ∧ y.regs Reg.stop = queryBase L + N ∧
      y.regs Reg.output = outputBase L m t N ∧
      BoxQuery.Readback m t (directoryBase L N) (valueBase L m t N) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L N ≤ p ∧ p < stackBase L m t N) → y.mem p = x.mem p) := by
  have hT0 : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨u, hu, uL, um, ut, uN, uA, uB, uD, uμ⟩ :=
    BoxQuery.exec_loadInput (L := L) (m := m) (t := t) (Q := N) x hL hm ht hN
      (haddr.of_le (by unfold originalAddressBound; omega))
  let v := u.set BoxTable.Reg.directory (directoryBase L N)
  have hv : ExecWithin (w + 2) relocateDirectory u v 1 := by
    have hf : Fits (w + 2) (BoxQuery.directoryBase L + N) :=
      haddr.of_le (by unfold BoxQuery.directoryBase originalAddressBound; omega)
    have he : ExecWithin (w + 2)
        (.op (.bin .add BoxTable.Reg.directory BoxTable.Reg.directory BoxQuery.Reg.query)) u
        (u.set BoxTable.Reg.directory
          (u.regs BoxTable.Reg.directory + u.regs BoxQuery.Reg.query)) 1 :=
      ExecWithin.bin (by simpa only [BinOp.eval, uD, uN] using hf)
    simpa only [relocateDirectory, v, uD, uN, directoryBase, queryBase,
      BoxQuery.directoryBase] using he
  have htable : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ) :=
    hmag.of_natAbs_le (by
      simpa only [← Int.natCast_add, ← Int.natCast_mul, ← Int.natCast_pow,
        Int.natAbs_natCast] using BoxQuery.table_magnitudeBound_le L A B)
  obtain ⟨z, hz, zL, zm, zt, zH, zT, zD, zR, zV, zK, zA, zB, zdir, zvalues, zframe⟩ :=
    BoxTable.exec_constructor (L := L) (m := m) (t := t) (D := directoryBase L N)
      (AA := 5) (BB := 5 + 10 ^ L) v
      (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
      (fun τ => ha _) (fun τ => hb _)
      (by simpa [v, BoxTable.Reg.directory, BoxTable.Reg.levels] using uL)
      (by simpa [v, BoxTable.Reg.directory, BoxTable.Reg.inner] using um)
      (by simpa [v, BoxTable.Reg.directory, BoxTable.Reg.threshold] using ut)
      (by simp [v])
      (by simpa [v, BoxTable.Reg.directory, BoxTable.Reg.arrayA] using uA)
      (by simpa [v, BoxTable.Reg.directory, BoxTable.Reg.arrayB] using uB)
      (by unfold directoryBase queryBase; omega) (by unfold directoryBase queryBase; omega)
      (fun i => by simpa only [v, Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hleft i)
      (fun i => by simpa only [v, Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hright i)
      (haddr.of_le (constructor_address_le L m t N hmL)) htable
  have zN : z.regs BoxQuery.Reg.query = N :=
    (hz.regs_eq (by decide :
      (Code.seq BoxTable.geometry BoxTable.tile).Preserves BoxQuery.Reg.query)).trans
      (by simpa [v, BoxTable.Reg.directory, BoxQuery.Reg.query] using uN)
  have hK := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hK
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  have zV' : z.regs BoxTable.Reg.values = valueBase L m t N := zV
  obtain ⟨y, hy, yQ, yN, yO, yμ⟩ := exec_initializeCursors (L := L) (N := N)
    (V := valueBase L m t N) (K := (boxes L m t).card) z zB zT zN zL zV' zK
    (haddr.of_le (by
      unfold originalAddressBound valueBase recordBase directoryBase queryBase
      omega))
  have he : ExecWithin (w + 2) prepare x y (preparationTime L m t) :=
    (hu.seq (hv.seq (hz.seq hy))).mono (by
      unfold preparationTime BoxQuery.preparationTime
      omega)
  refine ⟨y, he, (hy.regs_eq (by decide)).trans zL,
    (hy.regs_eq (by decide)).trans zt, (hy.regs_eq (by decide)).trans zT,
    (hy.regs_eq (by decide)).trans zA, (hy.regs_eq (by decide)).trans zB,
    (hy.regs_eq (by decide)).trans zD, (hy.regs_eq (by decide)).trans zV',
    (hy.regs_eq (by decide)).trans zK, yQ, yN, yO, ?_, ?_⟩
  · constructor
    · intro i
      rw [yμ, zframe _ (by unfold directoryBase queryBase; have := i.isLt; omega)]
      simpa only [v, Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hleft i
    · intro i
      rw [yμ, zframe _ (by unfold directoryBase queryBase; have := i.isLt; omega)]
      simpa only [v, Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hright i
    · intro s hs
      rw [yμ]
      exact zdir s hs
    · intro s hs hv
      rw [yμ]
      exact zvalues s hs hv
  · intro p hp
    rw [yμ, zframe p (by unfold stackBase valueBase recordBase at hp; omega)]
    exact congrFun uμ p

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
