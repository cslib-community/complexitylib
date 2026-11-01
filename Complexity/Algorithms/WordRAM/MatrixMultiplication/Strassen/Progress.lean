/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.QuarterUpdate

/-!
# Actual partial Strassen accumulations

The native return stage updates at most two quarters. During those real coefficient loops,
each output quarter contains either its previous partial sum or its next partial sum.
The mask below is a proof invariant, not data supplied to the program. Both alternatives
have the same four-contribution bound, so each actual signed addition admits its operands
without assuming cancellation or a bound on a future machine result.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- A quarter has either received the current child or retains its previous partial sum. -/
@[expose] def progressValue (p k : ℕ) (phase : Fin 7) (done : Fin 4 → Bool)
    (u v : ℕ → ℤ) (s : Fin 4) (r : ℕ) : ℤ :=
  if done s then
    Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k (phase.val + 1) u v s r
  else Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s r

/-- Quarters with zero contribution need no native write to reach the next partial sum. -/
theorem progressValue_eq_next (p k : ℕ) (phase : Fin 7) (done : Fin 4 → Bool)
    (u v : ℕ → ℤ) (s : Fin 4) (j : ℕ)
    (hzero : done s = false →
      Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase s = 0) :
    progressValue p k phase done u v s j =
      Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k (phase.val + 1) u v s j := by
  cases hd : done s
  · simp only [progressValue, hd, Bool.false_eq_true, ite_false,
      Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue_succ, hzero hd,
      zero_mul, add_zero]
  · simp only [progressValue, hd, ite_true]

/-- Both sides of the intra-stage invariant inherit the proved four-contribution bound. -/
theorem progressValue_natAbs_le {p k A B j : ℕ} (phase : Fin 7) (done : Fin 4 → Bool)
    (u v : ℕ → ℤ) (s : Fin 4)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B) (hj : j < 4 ^ k * p) :
    (progressValue p k phase done u v s j).natAbs ≤
      4 * (p * ((2 * A) * (2 * B)) * 16 ^ k) := by
  have hchild := fun t =>
    Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct_natAbs_le u v t hu hv hj
  unfold progressValue
  split
  · exact Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue_natAbs_le
      u v s (by omega) hchild
  · exact Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue_natAbs_le
      u v s (by omega) hchild

/-- One actual returned-child update advances exactly one not-yet-updated output quarter.
The child product and complete high-bank header survive the real in-place loop. -/
theorem exec_accumulate_progress {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 7) (done : Fin 4 → Bool) (t : Fin 4) (subtract : Bool)
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hnot : done t = false)
    (hsign : Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase t =
      if subtract then -1 else 1)
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) =
      encode (progressValue p k phase done u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (accumulate t.val subtract) x y (26 * (4 ^ k * p) + 10) ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) =
        encode (progressValue p k phase (Function.update done t true) u v s j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 2 * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j)) ∧
      ∀ d, (d < out + t.val * (4 ^ k * p) ∨
        out + t.val * (4 ^ k * p) + 4 ^ k * p ≤ d) → y.mem d = x.mem d := by
  let C := p * ((2 * A) * (2 * B)) * 16 ^ k
  have hfit : GenericRAM.Signed.Fits w ((4 * C + C : ℕ) : ℤ) :=
    hmag.of_natAbs_le (by
      rw [Int.natAbs_natCast]
      have hm := accumulation_le_magnitudeBound p A B k
      change 4 * C + C ≤ magnitudeBound p A B (k + 1)
      omega)
  obtain ⟨y, hy, yh, yc, values, memory⟩ := exec_accumulate_quarters t subtract x
    (progressValue p k phase done u v)
    (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase)
    hx hc hl (fun s j hj => progressValue_natAbs_le phase done u v s hu hv hj)
    (fun j hj => Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct_natAbs_le
      u v phase hu hv hj) hout hprod hfit haddr
  refine ⟨y, hy, yh, yc, ?_, ?_, memory⟩
  · intro s j hj
    rw [values s j hj]
    congr 1
    by_cases he : s = t
    · subst s
      simp only [ite_true, progressValue, hnot, Bool.false_eq_true, ite_false,
        Function.update_self,
        Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue_succ, hsign]
      cases subtract <;> simp [sub_eq_add_neg]
    · simp only [he, ite_false, progressValue, Function.update_of_ne he]
  · intro j hj
    rw [memory _ (Or.inr ?_), hprod j hj]
    have ht : t.val * (4 ^ k * p) + 4 ^ k * p ≤ 4 * (4 ^ k * p) := by
      have hm := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t.isLt)
      simpa only [Nat.succ_mul] using hm
    have ho := hl.output_before
    rw [pow_succ] at ho
    nlinarith

end Cslib.Algorithms.WordRAM.Strassen
