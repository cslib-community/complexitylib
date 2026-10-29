/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPrepare
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCollect

/-!
# Actual native encoder calls on the prepared bands

## Main definitions

* `BandPreparation.catalogueValue`: flat shared-transform values, using the existing
  coordinate transform and the computed, padded band array.

## Main results

* `BandPreparation.exec_band`: one complete native preparation, unchanged encoder call and
  catalogue copy, with charged instructions and an explicit memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

-- The persistent-register checks reduce the fixed 96-register parameter bank.
set_option maxRecDepth 4096

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The shared catalogue uses exactly the existing flat coordinate-transform values.
`Encoding.value_final_left/right` and `bandValue_left/right` identify these with the public
`encodingL/R` of the original mathematical `bandArrayL/R`. -/
def catalogueValue (L m N : ℕ) (side : Bool) (matrix : ℕ → ℕ → ℤ) (β p : ℕ) : ℤ :=
  CoordinateTransform.value (CoordinateTransform.table (Encoding.coefficients side))
    L 0 (bandValue L m N β side matrix) p 0

/-- The guarded band only reads real bounded matrix entries; all other entries are zero. -/
theorem abs_bandValue_le {L m N β : ℕ} (side : Bool) (matrix : ℕ → ℕ → ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hmat : ∀ r < N, ∀ k < D m, |matrix r k| ≤ A)
    (a : Fin (7 ^ L)) : |bandValue L m N β side matrix a.val| ≤ A := by
  cases side <;> unfold bandValue <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    split_ifs with hq hr
    · simpa only [abs_zero] using hA
    · exact hmat _ hr _ (selected_parts_bounds a hq).2
    · simpa only [abs_zero] using hA

/-- A real call of the unchanged encoder in its low 32-register bank. Parameters in the
other registers, arbitrary input headers and arbitrary outside memory are preserved. -/
theorem exec_encoderKernel {w L m N : ℕ} (hw : 0 < w) (side : Bool)
    (arr : ℕ → ℤ) (x : Data 96) (hheader : x.mem 1 = L)
    (hinput : ∀ i < 7 ^ L, x.mem (2 + i) = encode (arr i))
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ i < 7 ^ L, |arr i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    ∃ y, ExecWithin (w + 2) ((Encoding.program side).rename encoderRegisters) x y
        (Encoding.timeBound L) ∧
      (∀ p < 10 ^ L, y.mem (Encoding.outputBase L + p) = encode
        (CoordinateTransform.value (CoordinateTransform.table (Encoding.coefficients side))
          L 0 arr p 0)) ∧
      (∀ b, ¬(Encoding.outputBase L ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
        y.mem b = x.mem b) ∧ (∀ i, 32 ≤ i.val → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hv, hf, _, _⟩ := Encoding.exec hw side arr (x.comap encoderRegisters)
    hheader hinput A hA ha hmag (encoder_fits hfit)
  refine ⟨z.extend encoderRegisters x, hz.rename encoderRegisters_injective, hv, hf, ?_⟩
  intro i hi
  change Function.extend encoderRegisters z.regs x.regs i = x.regs i
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have hv := congrArg (fun k : Fin 96 => k.val) hj
  change j.val = i.val at hv
  omega

/-- Native cost of preparing, encoding and collecting one shared band. -/
def bandTime (L : ℕ) : ℕ :=
  (13 * L + 39) * 7 ^ L + 5 + Encoding.timeBound L + (7 * 10 ^ L + 10)

/-- Every band invokes the actual encoder code and copies its complete output. Only the low
workspace and this single shared catalogue block can change. Original matrix/table data and
arbitrary caller query regions outside those blocks remain untouched. -/
theorem exec_band {w L m N : ℕ} (hw : 0 < w) (side : Bool) (β : ℕ) (x : Data 96)
    (hx : BandParameters L m N x) (hβ : β < numBands L m N) (hb : x.regs band = β)
    (htable : ∀ t < 2 ^ L, x.mem (inverseBase L m N + t) = MaskTable.lookup L m t)
    (matrix : ℕ → ℕ → ℤ)
    (hmat : ∀ r < N, ∀ k < D m,
      x.mem (matrixAddress L m N side r k) = encode (matrix r k))
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ r < N, ∀ k < D m, |matrix r k| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    ∃ y, ExecWithin (w + 2)
        (.seq (prepareBand side) (.seq ((Encoding.program side).rename encoderRegisters)
          (collectBand side))) x y (bandTime L) ∧
      BandParameters L m N y ∧ y.regs band = β ∧
      (∀ p < 10 ^ L, y.mem (catalogueAddress L m N side β p) =
        encode (catalogueValue L m N side matrix β p)) ∧
      (∀ b, ¬(1 ≤ b ∧ b < Encoding.scratchBase L + 10 ^ L) →
        ¬(catalogueAddress L m N side β 0 ≤ b ∧
          b < catalogueAddress L m N side β 0 + 10 ^ L) → y.mem b = x.mem b) := by
  obtain ⟨p, hep, hpp, hpb, hheader, hinput, hpf⟩ :=
    exec_prepareBand side β x hx hβ hb htable matrix hmat hfit
  obtain ⟨e, hee, hev, hef, her⟩ := exec_encoderKernel hw side
    (bandValue L m N β side matrix) p hheader hinput A hA
    (fun i hi => abs_bandValue_le side matrix A hA ha ⟨i, hi⟩) hmag hfit
  have hep' : BandParameters L m N e := parameters_reframe hpp (by
    intro i hi
    apply her
    have hp : ∀ i ∈ parameterRegisters, 32 ≤ i.val := by decide
    exact hp i hi)
  have heb : e.regs band = β := (her band (by decide)).trans hpb
  obtain ⟨y, hec, hmem, hyp, hyb⟩ := exec_collectBand side β e hep' hβ heb hfit
  refine ⟨y, ?_, hyp, hyb, ?_, ?_⟩
  · simpa only [bandTime, Nat.add_assoc] using hep.seq (hee.seq hec)
  · intro p hp
    have heq : catalogueAddress L m N side β p =
        catalogueAddress L m N side β 0 + p := by simp [catalogueAddress]
    rw [heq, hmem, ArrayCopy.copyPrefix_read hp]
    exact hev p hp
  · intro b hb hc
    rw [hmem, ArrayCopy.copyPrefix_outside hc]
    calc
      e.mem b = p.mem b := hef b (by
        unfold Encoding.outputBase
        have := Nat.zero_le (7 ^ L)
        omega)
      _ = x.mem b := hpf b (by
        unfold Encoding.scratchBase Encoding.outputBase at hb
        have := Nat.zero_le (10 ^ L)
        omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
