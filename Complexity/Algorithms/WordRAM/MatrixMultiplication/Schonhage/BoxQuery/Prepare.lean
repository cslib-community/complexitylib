/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.InputLayout
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Memory

/-!
# Actual query preparation from original input words

The native adaptation reads all four headers and computes both array pointers. The
existing complete box-table constructor then builds the shared directory, descriptors
and every retained value. The same final state supplies all memory readback consumed
by the query; no geometry, execution, time or table certificate is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Read the four actual scalar input words, leaving memory unchanged. -/
theorem exec_inputHeaders {w L m t Q : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t) (hQ : x.mem 4 = Q)
    (hfit : Fits w 4) :
    ∃ y, ExecWithin w inputHeaders x y 8 ∧ y.regs BoxTable.Reg.levels = L ∧
      y.regs BoxTable.Reg.inner = m ∧ y.regs BoxTable.Reg.threshold = t ∧
      y.regs Reg.query = Q ∧ y.mem = x.mem := by
  have h1 : Fits w 1 := hfit.of_le (by decide)
  have h2 : Fits w 2 := hfit.of_le (by decide)
  have h3 : Fits w 3 := hfit.of_le (by decide)
  let a := (((((x.set BoxTable.Reg.address 1).set BoxTable.Reg.levels L).set
    BoxTable.Reg.address 2).set BoxTable.Reg.inner m).set BoxTable.Reg.address 3).set
      BoxTable.Reg.threshold t
  let y := (a.set BoxTable.Reg.address 4).set Reg.query Q
  have he : ExecWithin w inputHeaders x y 8 := by
    ram_eval [inputHeaders, y, a, hL, hm, ht, hQ, h1, h2, h3, hfit,
      BoxTable.Reg.address, BoxTable.Reg.levels, BoxTable.Reg.inner,
      BoxTable.Reg.threshold, Reg.query, Fin.mk.injEq]
  exact ⟨y, he, by simp [y, a, BoxTable.Reg.levels, BoxTable.Reg.inner,
      BoxTable.Reg.threshold, BoxTable.Reg.address, Reg.query],
    by simp [y, a, BoxTable.Reg.inner, BoxTable.Reg.threshold, BoxTable.Reg.address, Reg.query],
    by simp [y, a, BoxTable.Reg.threshold, BoxTable.Reg.address, Reg.query], by simp [y], rfl⟩

/-- Complete original-input adaptation computes the actual span and array/directory pointers. -/
theorem exec_loadInput {w L m t Q : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t) (hQ : x.mem 4 = Q)
    (hfit : Fits w (2 * 10 ^ L + L + 16)) :
    ∃ y, ExecWithin w loadInput x y (4 * L + 21) ∧
      y.regs BoxTable.Reg.levels = L ∧ y.regs BoxTable.Reg.inner = m ∧
      y.regs BoxTable.Reg.threshold = t ∧ y.regs Reg.query = Q ∧
      y.regs BoxTable.Reg.arrayA = 5 ∧ y.regs BoxTable.Reg.arrayB = 5 + 10 ^ L ∧
      y.regs BoxTable.Reg.directory = directoryBase L ∧ y.mem = x.mem := by
  obtain ⟨a, ha, aL, am, ath, aQ, haμ⟩ := exec_inputHeaders x hL hm ht hQ
    (hfit.of_le (by omega))
  obtain ⟨b, hb, _, _, b10, _, _, hbμ, bf⟩ := BoxTable.exec_constants a
    (hfit.of_le ((by decide : 10 ≤ 16).trans (Nat.le_add_left _ _)))
  have bL : b.regs BoxTable.Reg.levels = L :=
    (bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans aL
  obtain ⟨c, hc, cT, _, hcμ, cf⟩ := BoxTable.exec_span b bL b10 (hfit.of_le (by omega))
  have cL : c.regs BoxTable.Reg.levels = L :=
    (cf _ (by decide) (by decide) (by decide)).trans bL
  have cm : c.regs BoxTable.Reg.inner = m :=
    (cf _ (by decide) (by decide) (by decide)).trans
      ((bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans am)
  have ct : c.regs BoxTable.Reg.threshold = t :=
    (cf _ (by decide) (by decide) (by decide)).trans
      ((bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ath)
  have cQ : c.regs Reg.query = Q :=
    (cf _ (by decide) (by decide) (by decide)).trans
      ((bf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans aQ)
  have hf5 : Fits w 5 := hfit.of_le (by omega)
  have hfB : Fits w (5 + 10 ^ L) := hfit.of_le (by omega)
  have hfD : Fits w (5 + 10 ^ L + 10 ^ L) := hfit.of_le (by omega)
  let y := ((c.set BoxTable.Reg.arrayA 5).set BoxTable.Reg.arrayB (5 + 10 ^ L)).set
    BoxTable.Reg.directory (5 + 10 ^ L + 10 ^ L)
  have hd : ExecWithin w inputPointers c y 3 := by
    ram_eval [inputPointers, y, cT, hf5, hfB, hfD, BoxTable.Reg.arrayA,
      BoxTable.Reg.arrayB, BoxTable.Reg.directory, BoxTable.Reg.span, Fin.mk.injEq]
  refine ⟨y, (ha.seq (hb.seq (hc.seq hd))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y, BoxTable.Reg.levels, BoxTable.Reg.arrayA,
      BoxTable.Reg.arrayB, BoxTable.Reg.directory] using cL
  · simpa [y, BoxTable.Reg.inner, BoxTable.Reg.arrayA,
      BoxTable.Reg.arrayB, BoxTable.Reg.directory] using cm
  · simpa [y, BoxTable.Reg.threshold, BoxTable.Reg.arrayA,
      BoxTable.Reg.arrayB, BoxTable.Reg.directory] using ct
  · simpa [y, Reg.query, BoxTable.Reg.arrayA, BoxTable.Reg.arrayB, BoxTable.Reg.directory] using cQ
  · simp [y, BoxTable.Reg.arrayA, BoxTable.Reg.arrayB, BoxTable.Reg.directory]
  · simp [y, BoxTable.Reg.arrayB, BoxTable.Reg.directory]
  · simp [y, directoryBase]; omega
  · exact hcμ.trans (hbμ.trans haμ)

/-- Prepare the real query table from original caller words and canonical signed leaf arrays. -/
theorem exec_prepare {w L m t A B : ℕ} (hmL : m ≤ L) (x : Data registers)
    (q : Fin (10 ^ L)) (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t) (hQ : x.mem 4 = q.val)
    (hleft : ∀ i : Fin (10 ^ L), x.mem (5 + i.val) = Signed.encode (a i))
    (hright : ∀ i : Fin (10 ^ L), x.mem (5 + 10 ^ L + i.val) = Signed.encode (b i))
    (haddr : Fits (w + 2) (originalAddressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) prepare x y (preparationTime L m t) ∧
      y.regs BoxTable.Reg.levels = L ∧ y.regs BoxTable.Reg.inner = m ∧
      y.regs BoxTable.Reg.threshold = t ∧ y.regs Reg.query = q.val ∧
      y.regs BoxTable.Reg.height = m - t ∧ y.regs BoxTable.Reg.span = 10 ^ L ∧
      y.regs BoxTable.Reg.directory = directoryBase L ∧
      y.regs BoxTable.Reg.records = recordBase L m t ∧
      y.regs BoxTable.Reg.values = valueBase L m t ∧
      y.regs BoxTable.Reg.count = (boxes L m t).card ∧
      y.regs BoxTable.Reg.arrayA = 5 ∧ y.regs BoxTable.Reg.arrayB = 5 + 10 ^ L ∧
      Readback m t (directoryBase L) (valueBase L m t) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L ≤ p ∧ p < stackBase L m t) → y.mem p = x.mem p) := by
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨u, hu, uL, um, ut, uQ, uA, uB, uD, uμ⟩ :=
    exec_loadInput (L := L) (m := m) (t := t) (Q := q.val) x hL hm ht hQ
      (haddr.of_le (by unfold originalAddressBound; omega))
  have htable : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ) :=
    hmag.of_natAbs_le (by
      simpa only [← Int.natCast_add, ← Int.natCast_mul, ← Int.natCast_pow,
        Int.natAbs_natCast] using table_magnitudeBound_le L A B)
  obtain ⟨y, hy, yL, ym, yt, yH, yT, yD, yR, yV, yK, yA, yB, ydir, yvalues, yframe⟩ :=
    BoxTable.exec_constructor (L := L) (m := m) (t := t) (D := directoryBase L)
      (AA := 5) (BB := 5 + 10 ^ L) u
      (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
      (fun τ => ha _) (fun τ => hb _) uL um ut uD uA uB
      (by unfold directoryBase; omega) (by unfold directoryBase; omega)
      (fun i => by simpa only [uμ, BoxTable.leafIndex_leafAt] using hleft i)
      (fun i => by simpa only [uμ, BoxTable.leafIndex_leafAt] using hright i)
      (haddr.of_le (constructor_address_le L m t hmL)) htable
  have yQ : y.regs Reg.query = q.val :=
    (hy.regs_eq (by decide :
      (Code.seq BoxTable.geometry BoxTable.tile).Preserves Reg.query)).trans uQ
  have he : ExecWithin (w + 2) prepare x y (preparationTime L m t) :=
    (hu.seq hy).mono (by unfold preparationTime; omega)
  refine ⟨y, he, yL, ym, yt, yQ, yH, yT, yD, yR, yV, yK, yA, yB, ?_, ?_⟩
  · constructor
    · intro i
      rw [yframe _ (by unfold directoryBase; have := i.isLt; omega), uμ]
      simpa only [BoxTable.leafIndex_leafAt] using hleft i
    · intro i
      rw [yframe _ (by unfold directoryBase; have := i.isLt; omega), uμ]
      simpa only [BoxTable.leafIndex_leafAt] using hright i
    · exact ydir
    · exact yvalues
  · intro p hp
    rw [yframe p (by unfold stackBase valueBase recordBase at hp; omega), uμ]

/-- Actual initialized preparation derives input fit and bounded final data while exposing
the same native table witness consumed by the subsequent query. -/
theorem exec_prepare_input {w L m t A B : ℕ} (hmL : m ≤ L)
    (q : Fin (10 ^ L)) (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (originalAddressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input L m t q a b) ∧
    ∃ y, ExecWithin (w + 2) prepare (State.init (input L m t q a b)).data y
        (preparationTime L m t) ∧ y.Bounded (w + 2) ∧
      y.regs BoxTable.Reg.levels = L ∧ y.regs BoxTable.Reg.inner = m ∧
      y.regs BoxTable.Reg.threshold = t ∧ y.regs Reg.query = q.val ∧
      y.regs BoxTable.Reg.height = m - t ∧ y.regs BoxTable.Reg.span = 10 ^ L ∧
      y.regs BoxTable.Reg.directory = directoryBase L ∧
      y.regs BoxTable.Reg.records = recordBase L m t ∧
      y.regs BoxTable.Reg.values = valueBase L m t ∧
      y.regs BoxTable.Reg.count = (boxes L m t).card ∧
      y.regs BoxTable.Reg.arrayA = 5 ∧ y.regs BoxTable.Reg.arrayB = 5 + 10 ^ L ∧
      Readback m t (directoryBase L) (valueBase L m t) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L ≤ p ∧ p < stackBase L m t) →
        y.mem p = (State.init (input L m t q a b) : State registers).data.mem p) := by
  have hi := input_fits q a b ha hb haddr hmag
  obtain ⟨hL, hm, ht, hQ, hleft, hright⟩ := input_readback L m t q a b
  obtain ⟨y, he, hrest⟩ := exec_prepare hmL (State.init (input L m t q a b)).data
    q a b ha hb hL hm ht hQ hleft hright haddr hmag
  exact ⟨hi, y, he, he.bounded (Data.Bounded.init hi), hrest⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
