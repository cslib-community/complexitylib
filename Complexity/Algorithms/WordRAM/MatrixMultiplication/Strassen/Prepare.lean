/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Child
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Form
import Mathlib.Tactic.FinCases

/-!
# Real Strassen operand production and child entry

Both operand arrays are actually copied or arithmetically formed, then the native push
writes the child's entire frame. Child readiness and its canonical input words are derived
from these executions. No form, layout, multiplication, run or time certificate is supplied
to the program. This internal stage preserves the parent output and older frames through
the explicit footprint stated below.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Produce two actual operand forms and a complete child frame. Every form, argument,
pointer, store and push instruction is charged, including single-quadrant copies. -/
theorem exec_prepare {w p k A B a b out scratch frames frame a₁ a₂ b₁ b₂ : ℕ}
    (phase : Fin 7) (asign bsign : ℤ) (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (ha₁ : a₁ < 4) (ha₂ : a₂ < 4) (hb₁ : b₁ < 4) (hb₂ : b₂ < 4)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2)
        (prepare (phase.val + 1) a₁ a₂ asign b₁ b₂ bsign) x y (52 * (4 ^ k * p) + 50) ∧
      NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
        (scratch + 3 * (4 ^ k * p)) frames (frame + 7) y ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + j) = encode
        (if asign = 0 then u (a₁ * (4 ^ k * p) + j) else if asign < 0 then
          u (a₁ * (4 ^ k * p) + j) - u (a₂ * (4 ^ k * p) + j)
          else u (a₁ * (4 ^ k * p) + j) + u (a₂ * (4 ^ k * p) + j))) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 4 ^ k * p + j) = encode
        (if bsign = 0 then v (b₁ * (4 ^ k * p) + j) else if bsign < 0 then
          v (b₁ * (4 ^ k * p) + j) - v (b₂ * (4 ^ k * p) + j)
          else v (b₁ * (4 ^ k * p) + j) + v (b₂ * (4 ^ k * p) + j))) ∧
      y.mem (frame + 6) = phase.val + 1 ∧
      ∀ q, (q < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ q) →
        (q < frame + 6 ∨ frame + 14 ≤ q) → y.mem q = x.mem q := by
  let q := 4 ^ k * p
  have hsize : 4 ^ (k + 1) * p = 4 * q := by dsimp [q]; rw [pow_succ]; ring
  have habefore : a + 4 * q ≤ scratch := by simpa only [hsize] using hl.left_before
  have hbbefore : b + 4 * q ≤ scratch := by simpa only [hsize] using hl.right_before
  have hsbefore : scratch + 4 * q ≤ frames := by simpa only [hsize] using hl.scratch_before
  have hfbefore := hl.frames_before
  have hfitA : GenericRAM.Signed.Fits w ((A + A : ℕ) : ℤ) := hmag.of_natAbs_le (by
    rw [Int.natAbs_natCast]
    exact (forms_le_magnitudeBound p A B (k + 1)).1)
  have hfitB : GenericRAM.Signed.Fits w ((B + B : ℕ) : ℤ) := hmag.of_natAbs_le (by
    rw [Int.natAbs_natCast]
    exact (forms_le_magnitudeBound p A B (k + 1)).2)
  obtain ⟨s, hs, leftValues, leftFrame, leftRegs⟩ := exec_form Reg.inputA Reg.formA asign x u
    (by decide) (by decide) (by decide) (by decide) hc.quarter_eq ha₁ ha₂ hfitA
    (by simpa only [hsize] using hu)
    (by simpa only [hx.inputA_eq, hsize] using hleft)
    (by rw [hx.inputA_eq, hc.formA_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (Or.inl (by rw [hx.inputA_eq, hc.formA_eq]; exact habefore))
  have hsh : NodeHeader p (k + 1) a b out scratch frames frame s :=
    hx.of_regs_eq (fun i hi hi' => leftRegs i hi (by intro he; subst i; contradiction))
  have hsc : ChildBuffers p k scratch s :=
    hc.of_regs_eq (fun i hi hi' => leftRegs i (by omega) (by intro he; subst i; contradiction))
  have hright' (i : ℕ) (hi : i < 4 * q) : s.mem (s.regs Reg.inputB + i) = encode (v i) := by
    rw [hsh.inputB_eq, leftFrame _ (Or.inl (by rw [hc.formA_eq]; omega))]
    exact hright i (by simpa only [hsize] using hi)
  obtain ⟨r, hr, rightValues, rightFrame, rightRegs⟩ := exec_form Reg.inputB Reg.formB bsign s v
    (by decide) (by decide) (by decide) (by decide) hsc.quarter_eq hb₁ hb₂ hfitB
    (by simpa only [hsize] using hv) hright'
    (by rw [hsh.inputB_eq, hsc.formB_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (Or.inl (by rw [hsh.inputB_eq, hsc.formB_eq]; omega))
  have hrh : NodeHeader p (k + 1) a b out scratch frames frame r :=
    hsh.of_regs_eq (fun i hi hi' => rightRegs i hi (by intro he; subst i; contradiction))
  have hrc : ChildBuffers p k scratch r :=
    hsc.of_regs_eq (fun i hi hi' => rightRegs i (by omega) (by intro he; subst i; contradiction))
  let next : Fin 8 := ⟨phase.val + 1, by omega⟩
  obtain ⟨y, hy, hyf, hya, hyb, hyo, hys, hyd, hysz, hyp, hywords, hyparent,
    hyframe, hyregs⟩ := exec_push next r hrh.one_eq hrh.frameWidth_eq
      (by rw [hrh.frame_eq]; exact haddr.of_le (by unfold addressBound; omega))
  have he : ExecWithin (w + 2)
      (prepare (phase.val + 1) a₁ a₂ asign b₁ b₂ bsign) x y (52 * q + 50) :=
    (hs.seq (hr.seq hy)).mono (by omega)
  have hyframe' : y.regs Reg.frame = frame + 7 := by simpa only [hrh.frame_eq] using hyf
  have hready : NodeReady p k scratch (scratch + q) (scratch + 2 * q) (scratch + 3 * q)
      frames (frame + 7) y := {
    inputA_eq := hya.trans hrc.formA_eq
    inputB_eq := hyb.trans hrc.formB_eq
    output_eq := hyo.trans hrc.product_eq
    scratch_eq := hys.trans hrc.scratch_eq
    modulus_eq := (hyregs Reg.modulus (by decide)).trans hrh.modulus_eq
    depth_eq := hyd.trans hrc.depth_eq
    size_eq := hysz.trans hrc.quarter_eq
    frames_eq := (hyregs Reg.frames (by decide)).trans hrh.frames_eq
    frame_eq := hyframe'
    phase_eq := hyp
    active_eq := (hyregs Reg.active (by decide)).trans hrh.active_eq
    zero_eq := (hyregs Reg.zero (by decide)).trans hrh.zero_eq
    one_eq := (hyregs Reg.one (by decide)).trans hrh.one_eq
    four_eq := (hyregs Reg.four (by decide)).trans hrh.four_eq
    frameWidth_eq := (hyregs Reg.frameWidth (by decide)).trans hrh.frameWidth_eq
    frame_words := by simpa only [hyframe'] using hywords }
  refine ⟨y, he, hready, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hyframe _ (Or.inl (by rw [hrh.frame_eq]; omega)),
      rightFrame _ (Or.inl (by rw [hsc.formB_eq]; change scratch + j < scratch + q; omega))]
    simpa only [hc.formA_eq] using leftValues j hj
  · intro j hj
    rw [hyframe _ (Or.inl (by
      rw [hrh.frame_eq]
      change scratch + q + j < frame + 6
      omega))]
    simpa only [hsc.formB_eq] using rightValues j hj
  · simpa only [hrh.frame_eq, next] using hyparent
  · intro d hd hdf
    rw [hyframe _ (by simpa only [hrh.frame_eq] using hdf),
      rightFrame _ (by rw [hsc.formB_eq]; change d < scratch + q ∨ scratch + q + q ≤ d; omega),
      leftFrame _ (by rw [hc.formA_eq]; change d < scratch ∨ scratch + q ≤ d; omega)]

/-- Each static child dispatch produces exactly the operand pair of the existing finite
Strassen recurrence. Its readiness and input meanings follow from the two real form loops
and frame push; no precomputed operand array is assumed. -/
theorem exec_prepareChild {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 7) (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (prepareChild phase) x y (52 * (4 ^ k * p) + 50) ∧
      NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
        (scratch + 3 * (4 ^ k * p)) frames (frame + 7) y ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u phase j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 4 ^ k * p + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v phase j)) ∧
      y.mem (frame + 6) = phase.val + 1 ∧
      ∀ q, (q < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ q) →
        (q < frame + 6 ∨ frame + 14 ≤ q) → y.mem q = x.mem q := by
  fin_cases phase
  all_goals simp only [prepareChild]
  all_goals first
    | exact exec_prepare 0 1 1 x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 1 1 0 x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 2 0 (-1) x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 3 0 (-1) x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 4 1 0 x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 5 (-1) 1 x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr
    | exact exec_prepare 6 (-1) 1 x u v hx hc hl (by decide) (by decide) (by decide)
        (by decide) hu hv hleft hright hmag haddr

end Cslib.Algorithms.WordRAM.Strassen
