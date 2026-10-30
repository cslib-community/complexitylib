/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Coefficient

/-!
# Complete native multiplication of cyclic coefficient arrays

Both real input blocks are disjoint from the output in either order; they may coincide with
each other. Output cells may initially contain arbitrary dirty words. The program computes
every coefficient and preserves every memory cell outside the output. All fits use original
input magnitudes and explicit one-past-end addresses, not intermediate sum certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.CyclicIntRing

private theorem init_preserves (i : Fin 32) :
    (9 ≤ i.val ∧ i.val ≤ 12) ∨ 19 ≤ i.val →
      (ram[ Reg.coefficient ← #0; Reg.one ← #1 ] : Code .standard 32).Preserves i := by
  decide +kernel +revert

/-- Multiply two actual signed coefficient arrays in quadratic native time. Both source
blocks and all memory outside the output are preserved; no zeroed scratch is required.
The bound excludes the final halt. -/
theorem exec {w p A B : ℕ} (x : Data 32) (u v : ℕ → ℤ)
    (hlen : x.regs Reg.length = p)
    (hbound : GenericRAM.Signed.Fits w (magnitudeBound p A B : ℤ))
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B)
    (hA : ∀ i < p, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < p, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (h2p : Fits (w + 2) (2 * p))
    (ha : Fits (w + 2) (x.regs Reg.inputA + p))
    (hb : Fits (w + 2) (x.regs Reg.inputB + p))
    (hout : Fits (w + 2) (x.regs Reg.output + p))
    (hdisjA : x.regs Reg.inputA + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputA)
    (hdisjB : x.regs Reg.inputB + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputB) :
    ∃ y, ExecWithin (w + 2) program x y (42 * p * p + 9 * p + 4) ∧
      (∀ r < p, y.mem (x.regs Reg.output + r) = encode (convolution p u v r)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + p ≤ a → y.mem a = x.mem a) ∧
      ∀ i, (9 ≤ i.val ∧ i.val ≤ 12) ∨ 19 ≤ i.val → y.regs i = x.regs i := by
  let I (y : Data 32) : Prop :=
    (∀ i, (9 ≤ i.val ∧ i.val ≤ 12) ∨ 19 ≤ i.val → y.regs i = x.regs i) ∧
    y.regs Reg.one = 1 ∧ y.regs Reg.coefficient ≤ p ∧
    (∀ r < y.regs Reg.coefficient,
      y.mem (x.regs Reg.output + r) = encode (convolution p u v r)) ∧
    ∀ a, ¬(x.regs Reg.output ≤ a ∧ a < x.regs Reg.output + y.regs Reg.coefficient) →
      y.mem a = x.mem a
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt Reg.coefficient Reg.length).Holds y) :
      ∃ z, ExecWithin (w + 2) coefficient y z (42 * p + 7) ∧ I z ∧
        p - z.regs Reg.coefficient < p - y.regs Reg.coefficient := by
    obtain ⟨hregs, h1, hi, hvalues, hframe⟩ := hy
    have hl := (hregs Reg.length (by decide)).trans hlen
    have hr : y.regs Reg.coefficient < p := by simpa only [Cond.holds_lt, hl] using hc
    have hra := hregs Reg.inputA (by decide)
    have hrb := hregs Reg.inputB (by decide)
    have hro := hregs Reg.output (by decide)
    have readA (i : ℕ) (hip : i < p) :
        y.mem (y.regs Reg.inputA + i) = encode (u i) := by
      rw [hra, hframe _ (by rcases hdisjA with h | h <;> omega)]
      exact hA i hip
    have readB (i : ℕ) (hip : i < p) :
        y.mem (y.regs Reg.inputB + i) = encode (v i) := by
      rw [hrb, hframe _ (by rcases hdisjB with h | h <;> omega)]
      exact hB i hip
    obtain ⟨z, hz, hzrow, hzmem, hzregs⟩ := exec_coefficient y u v hl rfl hr h1
      hbound hu hv readA readB h2p (by simpa only [hra] using ha)
      (by simpa only [hrb] using hb) (by rw [hro]; exact hout.of_le (by omega))
    have hmem : z.mem = Function.update y.mem (x.regs Reg.output + y.regs Reg.coefficient)
        (encode (convolution p u v (y.regs Reg.coefficient))) := by
      simpa only [hro] using hzmem
    refine ⟨z, hz, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hip
      have hpi : 9 ≤ i.val ∧ (i.val ≤ 12 ∨ 18 ≤ i.val) := by
        rcases hip with h | h
        · exact ⟨h.1, Or.inl h.2⟩
        · exact ⟨by omega, Or.inr (by omega)⟩
      exact (hzregs i hpi).trans (hregs i hip)
    · exact (hzregs Reg.one (by decide)).trans h1
    · rw [hzrow]
      omega
    · intro r hri
      rw [hzrow] at hri
      rw [hmem]
      by_cases he : r = y.regs Reg.coefficient
      · subst r
        simp
      · rw [Function.update_of_ne (by omega)]
        exact hvalues r (by omega)
    · intro a ha'
      have hne : a ≠ x.regs Reg.output + y.regs Reg.coefficient := by
        intro he
        apply ha'
        rw [he, hzrow]
        omega
      rw [hmem, Function.update_of_ne hne]
      apply hframe
      intro h
      apply ha'
      rw [hzrow]
      omega
    · rw [hzrow]
      omega
  let x₀ := (x.set Reg.coefficient 0).set Reg.one 1
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  have hinit : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.coefficient ← #0; Reg.one ← #1 ]) x x₀ 2 := by ram_eval [x₀, h1]
  have hx₀ : I x₀ := by
    refine ⟨fun i hi => hinit.regs_eq (init_preserves i hi), ?_, ?_, ?_, ?_⟩
    · simp [x₀]
    · simp +decide [x₀, Reg.one, Reg.coefficient]
    · simp +decide [x₀, Reg.one, Reg.coefficient]
    · intro a _
      rfl
  obtain ⟨y, hy, hyI, hstop⟩ :=
    ExecWithin.loop_invariant I (fun y => p - y.regs Reg.coefficient) hbody hx₀
  obtain ⟨hregs, _, hi, hvalues, hframe⟩ := hyI
  have hl := (hregs Reg.length (by decide)).trans hlen
  have hend : y.regs Reg.coefficient = p := by
    simp only [Cond.holds_lt, hl] at hstop
    omega
  have he : ExecWithin (w + 2) program x y (42 * p * p + 9 * p + 4) :=
    (hinit.seq hy).mono (by
      simp +decide only [x₀, Data.set_regs, Function.update_apply, Reg.coefficient, Reg.one,
        ↓reduceIte, Nat.sub_zero]
      exact le_of_eq (by ring))
  refine ⟨y, he, ?_, ?_, hregs⟩
  · simpa only [hend] using hvalues
  · intro a ha'
    apply hframe
    rw [hend]
    omega

end Cslib.Algorithms.WordRAM.CyclicConvolution
