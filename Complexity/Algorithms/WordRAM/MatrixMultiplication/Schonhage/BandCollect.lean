/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCopy
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandParameters

/-!
# Charged copies into the shared band catalogue

## Main results

* `BandPreparation.catalogue_block_le`: each band has one disjoint catalogue block.
* `BandPreparation.exec_collectBand`: the real native encoder-output copy, including
  every address calculation and the unchanged copy kernel's instruction count.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

-- Static register-frame proofs reduce the fixed finite code and register bank.
set_option maxRecDepth 4096

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every complete band block lies in the catalogue allocation. -/
theorem catalogue_block_le {L m N β : ℕ} (side : Bool) (hβ : β < numBands L m N) :
    catalogueAddress L m N side β 0 + 10 ^ L ≤ memoryEnd L m N := by
  have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
  unfold catalogueAddress memoryEnd
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  all_goals nlinarith only [hβ, ht]

/-- No band output is placed in the protected snapshot, tables or native workspace. -/
theorem catalogue_le_address (L m N β : ℕ) (side : Bool) :
    catalogueBase L m N ≤ catalogueAddress L m N side β 0 := by
  unfold catalogueAddress
  omega

/-- Address arithmetic and the full copy are charged. The copy's source and destination are
disjoint by the concrete allocation; arbitrary words outside its destination are retained. -/
theorem exec_collectBand {w L m N : ℕ} (side : Bool) (β : ℕ) (x : Data 96)
    (hx : BandParameters L m N x) (hβ : β < numBands L m N) (hb : x.regs band = β)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w (collectBand side) x y (7 * 10 ^ L + 10) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (Encoding.outputBase L)
        (catalogueAddress L m N side β 0) (10 ^ L) ∧
      BandParameters L m N y ∧ y.regs band = β := by
  let b := (if side then numBands L m N else 0) + β
  let dest := catalogueAddress L m N side β 0
  have hdest : Fits w (dest + 10 ^ L) := (memory_fits hfit).of_le
    (catalogue_block_le side hβ)
  have hd0 : Fits w dest := hdest.of_le (Nat.le_add_right _ _)
  have hp : Fits w (b * 10 ^ L) := hd0.of_le (by
    dsimp only [dest, catalogueAddress, b]
    omega)
  have hbfit : Fits w b := hp.of_le (Nat.le_mul_of_pos_right _
    (Nat.pow_pos (by decide)))
  have hs : Fits w (7 ^ L + 2) := (encoder_fits hfit).of_le (by
    have h7 := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold Encoding.addressBound
    nlinarith only [h7, Nat.zero_le L, Nat.zero_le (10 ^ L)])
  have hsrc : Fits w (Encoding.outputBase L + 10 ^ L) :=
    ((memory_fits hfit).of_le (snapshot_le_memoryEnd L m N)).of_le (by
      have h := workspace_le_snapshot L m N
      unfold Encoding.scratchBase at h
      have := Nat.zero_le (10 ^ L)
      omega)
  let start := ((((((x.set copySrc (7 ^ L + 2)).set temporary b).set temporary
    (b * 10 ^ L)).set temporary dest).set copyDst dest).set copyLen (10 ^ L))
  dsimp only [dest, catalogueAddress] at hd0
  have hhead : ExecWithin w (collectHead side) x start 6 := by
    cases side <;>
      simp only [b, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] at hbfit hp hd0 <;>
      ram_eval [collectHead, start, dest, b, catalogueAddress, hx.cells, hx.leaves,
        hx.catalogue, hx.bands, hx.fixed.two, hb, hs, hd0, hp, hbfit,
        copySrc, copyDst, copyLen, temporary, cells, two, leaves, catalogue, bands,
        band, Fin.mk.injEq, Nat.zero_add, Nat.add_zero]
  obtain ⟨y, he, hmem, _⟩ := exec_copyKernel start (small_fits hfit (by decide))
    (by simpa [start, copySrc, copyLen, temporary, Encoding.outputBase, Nat.add_comm] using hsrc)
    (by simpa [start, copyDst, copyLen, temporary] using hdest)
    (Or.inl (by
      have hlow := workspace_le_snapshot L m N
      have hcat : snapshotBase L m N ≤ catalogueBase L m N := by
        unfold catalogueBase tableBase inverseBase
        have := Nat.zero_le (2 ^ L)
        omega
      have hsep : Encoding.outputBase L + 10 ^ L ≤ dest := by
        have hn := Nat.zero_le (10 ^ L)
        unfold Encoding.scratchBase at hlow
        exact (by omega : Encoding.outputBase L + 10 ^ L ≤ snapshotBase L m N).trans
          (hcat.trans (catalogue_le_address L m N β side))
      simpa [start, copySrc, copyDst, copyLen, temporary, Encoding.outputBase, Nat.add_comm]
        using hsep))
  have hwhole : ExecWithin w (collectBand side) x y (7 * 10 ^ L + 10) := by
    apply (hhead.seq he).mono
    have hn : start.regs copyLen = 10 ^ L := by simp [start]
    rw [hn]
    omega
  refine ⟨y, hwhole, ?_, parameters_reframe hx ?_, ?_⟩
  · simpa [start, copySrc, copyDst, copyLen, temporary, Encoding.outputBase, Nat.add_comm]
      using hmem
  · intro i hi
    apply hwhole.regs_eq
    have hp : ∀ side i, i ∈ parameterRegisters → (collectBand side).Preserves i := by
      intro side
      cases side <;> simp +decide only []
    exact hp side i hi
  · exact (hwhole.regs_eq (by
      cases side <;> simp +decide only [])).trans hb

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
