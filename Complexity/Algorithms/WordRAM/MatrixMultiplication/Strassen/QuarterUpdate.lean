/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Child
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Accumulate

/-!
# Native Strassen output-quarter update

The in-place coefficient loop updates one real output quarter. The other three quarters,
the returned child product, original inputs and older frames survive through its exact
footprint. This is an internal execution lemma for the controller induction.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- One actual accumulation updates its selected quarter and preserves all other quarters.
Header and child-buffer facts are derived from the actual register frame theorem. -/
theorem exec_accumulate_quarters {w p k a b out scratch frames frame A B : ℕ}
    (t : Fin 4) (subtract : Bool) (x : Data 64) (u : Fin 4 → ℕ → ℤ) (v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ s j, j < 4 ^ k * p → (u s j).natAbs ≤ A)
    (hv : ∀ j < 4 ^ k * p, (v j).natAbs ≤ B)
    (hout : ∀ s j, j < 4 ^ k * p →
      x.mem (out + s.val * (4 ^ k * p) + j) = encode (u s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode (v j))
    (hmag : GenericRAM.Signed.Fits w ((A + B : ℕ) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (accumulate t.val subtract) x y (26 * (4 ^ k * p) + 10) ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) =
        encode (if s = t then if subtract then u s j - v j else u s j + v j else u s j)) ∧
      ∀ d, (d < out + t.val * (4 ^ k * p) ∨
        out + t.val * (4 ^ k * p) + 4 ^ k * p ≤ d) → y.mem d = x.mem d := by
  let q := 4 ^ k * p
  have hsize : 4 ^ (k + 1) * p = 4 * q := by dsimp [q]; rw [pow_succ]; ring
  have ho : out + 4 * q ≤ scratch := by simpa only [hsize] using hl.output_before
  have hs : scratch + 4 * q ≤ frames := by simpa only [hsize] using hl.scratch_before
  have hf := hl.frames_before
  obtain ⟨y, hy, values, frameMem, regs⟩ := exec_accumulate subtract x (u t) v
    hc.quarter_eq t.isLt hmag (hu t) hv
    (by simpa only [hx.output_eq] using hout t)
    (by simpa only [hc.product_eq] using hprod)
    (by rw [hx.output_eq, hc.product_eq]; exact haddr.of_le (by unfold addressBound; omega))
    (Or.inr (by rw [hx.output_eq, hc.product_eq]; omega))
  refine ⟨y, hy, hx.of_regs_eq (fun i hi _ => regs i hi (by
    intro he; subst i; contradiction)), hc.of_regs_eq (fun i hi _ => regs i (by omega) (by
    intro he; subst i; contradiction)), ?_, ?_⟩
  · intro s j hj
    by_cases he : s = t
    · subst s
      simpa only [hx.output_eq, ite_true] using values j hj
    · have hne : s.val ≠ t.val := fun h => he (Fin.ext h)
      have hsep : out + s.val * q + j < out + t.val * q ∨
          out + t.val * q + q ≤ out + s.val * q + j := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hlt)
          rw [Nat.succ_mul] at hm
          omega
        · have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hgt)
          rw [Nat.succ_mul] at hm
          omega
      rw [frameMem _ (by simpa only [hx.output_eq] using hsep), hout s j hj, ite_eq_right he]
  · intro d hd
    exact frameMem d (by simpa only [hx.output_eq] using hd)

end Cslib.Algorithms.WordRAM.Strassen
