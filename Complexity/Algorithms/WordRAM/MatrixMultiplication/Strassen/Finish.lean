/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Receive
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Control

/-!
# Native final Strassen child return

The last actual product adds into the first output quarter, then the real parent/root pop
returns. The completed four partial sums equal the existing finite Strassen product on
every coefficient. This closes one parent's final stage, not the entire recursive traversal.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The actual seventh return stage produces every parent coefficient and performs the
real parent/root pop. All inputs to this lemma are internal current-state invariants. -/
theorem exec_stage_finish {w p k A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k 6 u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v 6 j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (stage 7) x y (26 * (4 ^ k * p) + 13) ∧
      NodeResult p (k + 1) out scratch frames frame u v x y := by
  obtain ⟨s, hs, sh, _, outputValues, _, memory⟩ := exec_returnedUpdates 6 x u v
    hx hc hl hu hv hout hprod hmag haddr
  obtain ⟨y, hy, hm, hframe, hactive, hr⟩ := exec_pop s sh.frameWidth_eq
    (by rw [sh.frame_eq]; exact haddr.of_le (by unfold addressBound; omega))
  have he := exec_stage_return 6 hs hy
  have he' : ExecWithin (w + 2) (stage 7) x y (26 * (4 ^ k * p) + 13) := by
    simpa [receiveBudget] using he.mono (show receiveBudget 6 (4 ^ k * p) + 3 ≤
      26 * (4 ^ k * p) + 13 by norm_num [receiveBudget])
  refine ⟨y, he', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    let q := 4 ^ k * p
    have hq : 0 < q := Nat.mul_pos (by positivity) hl.modulus_pos
    have hsize : 4 ^ (k + 1) * p = 4 * q := by dsimp [q]; rw [pow_succ]; ring
    let t : Fin 4 := ⟨i / q, (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [hsize] using hi)⟩
    have hmidx : t.val * q + i % q = i := by
      simpa only [t, Nat.mul_comm] using Nat.div_add_mod i q
    have hmod : i % q < q := Nat.mod_lt i hq
    rw [hm]
    have hv' := outputValues t (i % q) hmod
    have hp' := Cslib.Algorithms.MatrixMultiplication.Strassen.multiply_eq_partialValue
      hl.modulus_pos u v t hmod
    change s.mem (out + t.val * q + i % q) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k 7 u v t (i % q)) at hv'
    rw [Nat.add_assoc, hmidx, ← hp', hmidx] at hv'
    exact hv'
  · intro d hd
    rw [hm]
    apply memory d
    have hn : ¬(out ≤ d ∧ d < out + 4 ^ (k + 1) * p) := fun h => hd (Or.inl h)
    omega
  · exact (hr Reg.output (by decide) (by decide)).trans sh.output_eq
  · exact (hr Reg.modulus (by decide) (by decide)).trans sh.modulus_eq
  · exact (hr Reg.frames (by decide) (by decide)).trans sh.frames_eq
  · simpa only [sh.frames_eq, sh.frame_eq] using hframe
  · simpa only [sh.frames_eq, sh.frame_eq, sh.active_eq] using hactive
  · exact (hr Reg.zero (by decide) (by decide)).trans sh.zero_eq
  · exact (hr Reg.one (by decide) (by decide)).trans sh.one_eq
  · exact (hr Reg.four (by decide) (by decide)).trans sh.four_eq
  · exact (hr Reg.frameWidth (by decide) (by decide)).trans sh.frameWidth_eq

end Cslib.Algorithms.WordRAM.Strassen
