/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.ArrayArithmetic.Body
public import Complexity.Computability.WordRAM.Signed.Fits

/-!
# Complete native signed array arithmetic with exact aliases

Each input is either separated from the output or has the identical base. Earlier writes
then preserve every unread source entry. This supports both disjoint Strassen operand forms
and in-place additions/subtractions into output quadrants.
-/

public section

namespace Cslib.WordRAM.Signed.ArrayArithmetic

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem init_preserves (i : Fin 16) :
    9 ≤ i.val ∧ i.val ≤ 12 →
      (ram[ Reg.index ← #0; Reg.one ← #1 ] : Code .standard 16).Preserves i := by
  decide +kernel +revert

/-- Actual native array addition/subtraction, including setup and all loop/access work.
The source-width envelope concerns only original input magnitudes. Dirty output and exact
input/output aliases are permitted. The bound excludes the final halt. -/
theorem exec {w n A B : ℕ} (subtract : Bool) (x : Data 16) (u v : ℕ → ℤ)
    (hlen : x.regs Reg.length = n) (hbound : GenericRAM.Signed.Fits w ((A + B : ℕ) : ℤ))
    (hu : ∀ i < n, (u i).natAbs ≤ A) (hv : ∀ i < n, (v i).natAbs ≤ B)
    (hA : ∀ i < n, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < n, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (ha : Fits (w + 2) (x.regs Reg.inputA + n))
    (hb : Fits (w + 2) (x.regs Reg.inputB + n))
    (hout : Fits (w + 2) (x.regs Reg.output + n))
    (hsepA : x.regs Reg.inputA + n ≤ x.regs Reg.output ∨
      x.regs Reg.output + n ≤ x.regs Reg.inputA ∨ x.regs Reg.inputA = x.regs Reg.output)
    (hsepB : x.regs Reg.inputB + n ≤ x.regs Reg.output ∨
      x.regs Reg.output + n ≤ x.regs Reg.inputB ∨ x.regs Reg.inputB = x.regs Reg.output) :
    ∃ y, ExecWithin (w + 2) (program subtract) x y (26 * n + 4) ∧
      (∀ i < n, y.mem (x.regs Reg.output + i) =
        encode (if subtract then u i - v i else u i + v i)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + n ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i := by
  let I (y : Data 16) : Prop :=
    (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) ∧ y.regs Reg.one = 1 ∧
    y.regs Reg.index ≤ n ∧
    (∀ i < y.regs Reg.index, y.mem (x.regs Reg.output + i) =
      encode (if subtract then u i - v i else u i + v i)) ∧
    ∀ a, ¬(x.regs Reg.output ≤ a ∧ a < x.regs Reg.output + y.regs Reg.index) →
      y.mem a = x.mem a
  have hbody (y : Data 16) (hy : I y) (hc : (Cond.lt Reg.index Reg.length).Holds y) :
      ∃ z, ExecWithin (w + 2) (body subtract) y z 24 ∧ I z ∧
        n - z.regs Reg.index < n - y.regs Reg.index := by
    obtain ⟨hregs, h1, hi, hvalues, hframe⟩ := hy
    have hl := (hregs Reg.length (by decide)).trans hlen
    have hlt : y.regs Reg.index < n := by simpa only [Cond.holds_lt, hl] using hc
    have hra := hregs Reg.inputA (by decide)
    have hrb := hregs Reg.inputB (by decide)
    have hro := hregs Reg.output (by decide)
    have readA : y.mem (y.regs Reg.inputA + y.regs Reg.index) = encode (u (y.regs Reg.index)) := by
      rw [hra, hframe _ (by rcases hsepA with h | h | h <;> omega)]
      exact hA _ hlt
    have readB : y.mem (y.regs Reg.inputB + y.regs Reg.index) = encode (v (y.regs Reg.index)) := by
      rw [hrb, hframe _ (by rcases hsepB with h | h | h <;> omega)]
      exact hB _ hlt
    obtain ⟨z, hz, hzi, hzmem, hzregs⟩ :=
      exec_body subtract y (u (y.regs Reg.index)) (v (y.regs Reg.index))
        (hbound.of_natAbs_le ((hu _ hlt).trans (by omega)))
        (hbound.of_natAbs_le ((hv _ hlt).trans (by omega))) readA readB
        (by rw [hra]; exact ha.of_le (by omega))
        (by rw [hrb]; exact hb.of_le (by omega))
        (by rw [hro]; exact hout.of_le (by omega)) (hout.of_le (by omega)) h1
    have hm : z.mem = Function.update y.mem (x.regs Reg.output + y.regs Reg.index)
        (encode (if subtract then u (y.regs Reg.index) - v (y.regs Reg.index)
          else u (y.regs Reg.index) + v (y.regs Reg.index))) := by
      simpa only [hro] using hzmem
    have hpres (i : Fin 16) (hip : 9 ≤ i.val ∧ i.val ≤ 12) :
        z.regs i = x.regs i := by
      have hnl : ¬BodyLocal i := by
        simp only [BodyLocal, Reg.index, Reg.address, Fin.ext_iff]
        omega
      exact (hzregs i hnl).trans (hregs i hip)
    refine ⟨z, hz, ⟨hpres, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (hzregs Reg.one (by decide)).trans h1
    · rw [hzi]
      omega
    · intro i hip
      rw [hzi] at hip
      rw [hm]
      by_cases he : i = y.regs Reg.index
      · subst i
        simp
      · rw [Function.update_of_ne (by omega)]
        exact hvalues i (by omega)
    · intro a ha'
      have hne : a ≠ x.regs Reg.output + y.regs Reg.index := by
        intro he
        apply ha'
        rw [he, hzi]
        omega
      rw [hm, Function.update_of_ne hne]
      apply hframe
      intro h
      apply ha'
      rw [hzi]
      omega
    · rw [hzi]
      omega
  let x₀ := (x.set Reg.index 0).set Reg.one 1
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  have hinit : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.index ← #0; Reg.one ← #1 ]) x x₀ 2 := by ram_eval [x₀, h1]
  have hx₀ : I x₀ := by
    refine ⟨fun i hi => hinit.regs_eq (init_preserves i hi), by simp [x₀], ?_, ?_, ?_⟩
    · simp +decide [x₀, Reg.one, Reg.index]
    · simp +decide [x₀, Reg.one, Reg.index]
    · intro _ _
      rfl
  obtain ⟨y, hy, hyI, hstop⟩ :=
    ExecWithin.loop_invariant I (fun y => n - y.regs Reg.index) hbody hx₀
  obtain ⟨hregs, _, hi, hvalues, hframe⟩ := hyI
  have hl := (hregs Reg.length (by decide)).trans hlen
  have hend : y.regs Reg.index = n := by
    simp only [Cond.holds_lt, hl] at hstop
    omega
  have he : ExecWithin (w + 2) (program subtract) x y (26 * n + 4) :=
    (hinit.seq hy).mono (by simp +decide [x₀, Reg.one, Reg.index]; omega)
  refine ⟨y, he, by simpa only [hend] using hvalues, ?_, hregs⟩
  intro a ha'
  apply hframe
  rw [hend]
  omega

/-- Both closed operation choices use fixed standard code and never read physical width. -/
theorem program_fixed (subtract : Bool) :
    ((program subtract).program Reg.output).length ≤ 128 ∧
      ¬((program subtract).program Reg.output).ReadsWidth := by
  cases subtract <;> constructor
  · decide +kernel
  · apply Code.not_readsWidth_program
    decide +kernel
  · decide +kernel
  · apply Code.not_readsWidth_program
    decide +kernel

end Cslib.WordRAM.Signed.ArrayArithmetic
