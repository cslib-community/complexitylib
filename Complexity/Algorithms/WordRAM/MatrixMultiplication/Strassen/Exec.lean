/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Traversal

/-!
# Complete native cyclic-coefficient Strassen execution

The actual fixed program computes its root power/size and frame address, initializes the
dirty root frame, executes all seven-product recursion through the explicit native stack,
and exits the real controller loop. Callers supply ordinary pointers and canonical signed
coefficient arrays with numerical separation and fits. No layout, multiplication, execution
or time certificate is an algorithm argument. The result agrees with the existing finite
Strassen recursion, whose separate correctness theorem identifies cyclic-ring matrix product.

This caller-safe kernel does not yet compose CountPrime matrix preparation, coefficient
extraction, initialized original-weight input, or its final original-input width envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Execute the complete native Strassen program from its actual runtime arguments.
Output and recursive workspace may be dirty. The bound includes setup and loop exit,
while a final flat halt, when appended by a caller, costs one additional instruction. -/
theorem exec {w p k A B a b out scratch : ℕ} (x : Data 64) (u v : ℕ → ℤ)
    (hp : 0 < p) (hpr : x.regs Reg.modulus = p) (hkr : x.regs Reg.depth = k)
    (har : x.regs Reg.inputA = a) (hbr : x.regs Reg.inputB = b)
    (hor : x.regs Reg.output = out) (hsr : x.regs Reg.scratch = scratch)
    (ha : a + 4 ^ k * p ≤ scratch) (hb : b + 4 ^ k * p ≤ scratch)
    (ho : out + 4 ^ k * p ≤ scratch)
    (hdisjA : a + 4 ^ k * p ≤ out ∨ out + 4 ^ k * p ≤ a)
    (hdisjB : b + 4 ^ k * p ≤ out ∨ out + 4 ^ k * p ≤ b)
    (hu : ∀ i < 4 ^ k * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ k * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ k * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ k * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B k : ℤ))
    (haddr : Fits (w + 2) (addressBound (scratch + 4 ^ k * p) (scratch + 4 ^ k * p) k)) :
    ∃ y, ExecWithin (w + 2) program x y (traceBudget p k + 4 * k + 32) ∧
      NodeResult p k out scratch (scratch + 4 ^ k * p) (scratch + 4 ^ k * p) u v x y := by
  let frames := scratch + 4 ^ k * p
  have hpow : 4 ^ k ≤ 4 ^ k * p := by
    have hm := Nat.mul_le_mul_left (4 ^ k) (Nat.succ_le_of_lt hp)
    simpa only [Nat.mul_one] using hm
  have hsetupFit : Fits (w + 2) (x.regs Reg.scratch + x.regs Reg.modulus *
      4 ^ x.regs Reg.depth + 4 ^ x.regs Reg.depth + x.regs Reg.depth + 16) := by
    rw [hsr, hpr, hkr, Nat.mul_comm p]
    exact haddr.of_le (by unfold addressBound; omega)
  obtain ⟨s, setupRun, ready, setupFrame⟩ := exec_setup_ready x hsetupFit
  have ready' : NodeReady p k a b out scratch frames frames s := by
    simpa only [hpr, hkr, har, hbr, hor, hsr] using ready
  have layout : NodeLayout p k a b out scratch frames frames :=
    ⟨hp, ha, hb, ho, Nat.le_refl _, Nat.le_refl _, hdisjA, hdisjB⟩
  have smem (d : ℕ) (hd : d < frames ∨ frames + 7 ≤ d) : s.mem d = x.mem d :=
    setupFrame d (by simpa only [ready'.frame_eq] using hd)
  obtain ⟨y, result, continuation⟩ := exec_ready k s u v ready' layout hu hv
    (by intro i hi; rw [smem _ (Or.inl (by omega))]; exact hleft i hi)
    (by intro i hi; rw [smem _ (Or.inl (by omega))]; exact hright i hi) hmag haddr
  have hexit : ¬(Cond.lt Reg.zero Reg.active).Holds y := by
    simp only [Cond.holds_lt, result.zero_eq, result.active_eq, lt_self_iff_false, ite_false]
    decide
  have hcontroller := continuation y 2 (ExecWithin.loop_exit hexit)
  have he : ExecWithin (w + 2) program x y (traceBudget p k + 4 * k + 32) :=
    (setupRun.seq hcontroller).mono (by rw [hkr]; omega)
  refine ⟨y, he, { result with outside := ?_ }⟩
  intro d hd
  rw [result.outside d hd]
  apply smem
  have hframes : ¬(frames ≤ d ∧ d < frames + 7 * (k + 1)) := fun h => hd (Or.inr (Or.inr h))
  omega

/-- The proved native instruction count is polynomial in the cyclic coefficient length
and grows as seven to the matrix depth. This bound concerns the actual execution in `exec`. -/
theorem exec_budget_le (p k : ℕ) : traceBudget p k + 4 * k + 32 ≤
    (42 * p * p + 240 * p + 178) * 7 ^ k + 4 * k + 32 := by
  have h := traceBudget_potential_le p k
  omega

end Cslib.Algorithms.WordRAM.Strassen
