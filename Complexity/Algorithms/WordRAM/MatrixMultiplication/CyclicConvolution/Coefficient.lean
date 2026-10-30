/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Term
public import Complexity.Computability.WordRAM.Signed.Fits

/-!
# A complete native cyclic-convolution coefficient

The actual inner loop starts its accumulator and counter at zero. Its operand and partial-sum
fits follow from a numerical envelope of the original coefficient magnitudes. After all p
products it performs one store and advances the coefficient counter. No partial sum, arithmetic
answer, execution or running-time certificate is an argument of the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.CyclicIntRing

/-- A natural envelope for both input coefficients, products and every partial accumulator. -/
@[expose] def magnitudeBound (p A B : ℕ) : ℕ := A + B + (p + 1) * (A * B) + 1

private theorem inputA_le_bound (p A B : ℕ) : A ≤ magnitudeBound p A B := by
  unfold magnitudeBound
  omega

private theorem inputB_le_bound (p A B : ℕ) : B ≤ magnitudeBound p A B := by
  unfold magnitudeBound
  omega

private theorem product_le_bound (p A B : ℕ) : A * B ≤ magnitudeBound p A B := by
  have h := Nat.le_mul_of_pos_left (A * B) (Nat.succ_pos p)
  simp only [Nat.succ_eq_add_one] at h
  unfold magnitudeBound
  omega

private theorem partial_le_bound {p r k A B : ℕ} {u v : ℕ → ℤ}
    (hr : r < p) (hk : k ≤ p)
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B) :
    (partialConvolution p u v r k).natAbs ≤ magnitudeBound p A B := by
  have h := partialConvolution_natAbs_le hr hk hu hv
  have hmul := Nat.mul_le_mul_right (A * B) (hk.trans (Nat.le_succ p))
  simp only [Nat.succ_eq_add_one] at hmul
  unfold magnitudeBound
  omega

private theorem init_preserves (i : Fin 32) : ¬TermLocal i →
    (ram[ Reg.index ← #0; Reg.accumulator ← #0 ] : Code .standard 32).Preserves i := by
  decide +kernel +revert

private theorem coefficient_preserves (i : Fin 32) :
    9 ≤ i.val ∧ (i.val ≤ 12 ∨ 18 ≤ i.val) → coefficient.Preserves i := by
  decide +kernel +revert

/-- Compute the entire coefficient from the actual signed arrays. The bound includes the
initialization, every indexed product/addition, all loop control and the final store/increment.
The output may alias an input for this single coefficient: the store follows every read. -/
theorem exec_coefficient {w p r A B : ℕ} (x : Data 32) (u v : ℕ → ℤ)
    (hlen : x.regs Reg.length = p) (hrow : x.regs Reg.coefficient = r) (hr : r < p)
    (hone : x.regs Reg.one = 1)
    (hbound : GenericRAM.Signed.Fits w (magnitudeBound p A B : ℤ))
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B)
    (hA : ∀ i < p, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < p, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (h2p : Fits (w + 2) (2 * p))
    (ha : Fits (w + 2) (x.regs Reg.inputA + p))
    (hb : Fits (w + 2) (x.regs Reg.inputB + p))
    (hout : Fits (w + 2) (x.regs Reg.output + r)) :
    ∃ y, ExecWithin (w + 2) coefficient x y (42 * p + 7) ∧
      y.regs Reg.coefficient = r + 1 ∧
      y.mem = Function.update x.mem (x.regs Reg.output + r) (encode (convolution p u v r)) ∧
      ∀ i, 9 ≤ i.val ∧ (i.val ≤ 12 ∨ 18 ≤ i.val) → y.regs i = x.regs i := by
  let I (y : Data 32) : Prop :=
    (∀ i, ¬TermLocal i → y.regs i = x.regs i) ∧
    y.regs Reg.index ≤ p ∧
    y.regs Reg.accumulator = encode (partialConvolution p u v r (y.regs Reg.index)) ∧
    y.mem = x.mem
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt Reg.index Reg.length).Holds y) :
      ∃ z, ExecWithin (w + 2) term y z 40 ∧ I z ∧
        p - z.regs Reg.index < p - y.regs Reg.index := by
    obtain ⟨hregs, hi, hacc, hmem⟩ := hy
    have hl := (hregs Reg.length (by decide)).trans hlen
    have hr' := (hregs Reg.coefficient (by decide)).trans hrow
    have hlt : y.regs Reg.index < p := by simpa only [Cond.holds_lt, hl] using hc
    let i := y.regs Reg.index
    let j := subIndex p r i
    have hj : j < p := subIndex_lt hr hlt
    have huf : GenericRAM.Signed.Fits w (u i) :=
      hbound.of_natAbs_le ((hu i hlt).trans (inputA_le_bound p A B))
    have hvf : GenericRAM.Signed.Fits w (v j) :=
      hbound.of_natAbs_le ((hv j hj).trans (inputB_le_bound p A B))
    have hpf : GenericRAM.Signed.Fits w (u i * v j) := hbound.of_natAbs_le (by
      rw [Int.natAbs_mul]
      exact (Nat.mul_le_mul (hu i hlt) (hv j hj)).trans (product_le_bound p A B))
    have hsf : GenericRAM.Signed.Fits w (partialConvolution p u v r i) :=
      hbound.of_natAbs_le (partial_le_bound hr hi hu hv)
    have hya := hregs Reg.inputA (by decide)
    have hyb := hregs Reg.inputB (by decide)
    have hwrap : Fits (w + 2) (y.regs Reg.coefficient + y.regs Reg.length) := by
      rw [hr', hl]
      exact h2p.of_le (by omega)
    have haddrA : Fits (w + 2) (y.regs Reg.inputA + i) := by
      rw [hya]
      exact ha.of_le (by omega)
    have haddrB : Fits (w + 2) (y.regs Reg.inputB + j) := by
      rw [hyb]
      exact hb.of_le (by omega)
    obtain ⟨z, hz, hzacc, hzi, hzmem, hzregs⟩ :=
      exec_term y (u i) (v j) (partialConvolution p u v r i) huf hvf hpf hsf hwrap haddrA
        (by simpa only [hl, hr'] using haddrB) (h2p.of_le (by omega))
        (by rw [hmem, hya]; exact hA i hlt)
        (by simpa only [hl, hr', hmem, hyb] using hB j hj) hacc
        ((hregs Reg.one (by decide)).trans hone)
    refine ⟨z, hz, ⟨fun k hk => (hzregs k hk).trans (hregs k hk), ?_, ?_, hzmem.trans hmem⟩, ?_⟩
    · rw [hzi]
      omega
    · rw [hzi, partialConvolution_succ]
      exact hzacc
    · rw [hzi]
      omega
  let x₀ := (x.set Reg.index 0).set Reg.accumulator 0
  have hzero : Fits (w + 2) 0 := Nat.two_pow_pos _
  have hinit : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.index ← #0; Reg.accumulator ← #0 ]) x x₀ 2 := by
    ram_eval [x₀, hzero]
  have hx₀ : I x₀ := by
    refine ⟨fun i hi => hinit.regs_eq (init_preserves i hi), ?_, ?_, rfl⟩
    · simp +decide [x₀, Reg.index, Reg.accumulator]
    · simp +decide [x₀, Reg.index, Reg.accumulator]
  obtain ⟨z, hz, hzI, hstop⟩ :=
    ExecWithin.loop_invariant I (fun z => p - z.regs Reg.index) hbody hx₀
  obtain ⟨hzregs, hzi, hzacc, hzmem⟩ := hzI
  have hzl := (hzregs Reg.length (by decide)).trans hlen
  have hend : z.regs Reg.index = p := by
    simp only [Cond.holds_lt, hzl] at hstop
    omega
  have hzr := (hzregs Reg.coefficient (by decide)).trans hrow
  have hzo := hzregs Reg.output (by decide)
  have hz1 := (hzregs Reg.one (by decide)).trans hone
  have hza : z.regs Reg.accumulator = encode (convolution p u v r) := by
    simpa only [hend, convolution] using hzacc
  let y := ((z.set Reg.address (x.regs Reg.output + r)).write
    (x.regs Reg.output + r) (encode (convolution p u v r))).set Reg.coefficient (r + 1)
  have hnextrow : Fits (w + 2) (r + 1) := h2p.of_le (by omega)
  have hstore : ExecWithin (w + 2)
      (ram[ Reg.address ← Reg.output + Reg.coefficient; *Reg.address ← Reg.accumulator;
        Reg.coefficient ← Reg.coefficient + Reg.one ]) z y 3 := by
    ram_eval [y, hout, hnextrow, hzr, hzo, hz1, hza,
      Reg.address, Reg.output, Reg.coefficient, Reg.one, Reg.accumulator, Fin.mk.injEq]
  have he : ExecWithin (w + 2) coefficient x y (42 * p + 7) :=
    (hinit.seq (hz.seq hstore)).mono (by simp +decide [x₀, Reg.index, Reg.accumulator]; omega)
  refine ⟨y, he, by simp [y], ?_, fun i hi => he.regs_eq (coefficient_preserves i hi)⟩
  simpa only [y, Data.set_mem, Data.write_mem] using
    congrArg (fun mem => Function.update mem (x.regs Reg.output + r)
      (encode (convolution p u v r))) hzmem

end Cslib.Algorithms.WordRAM.CyclicConvolution
