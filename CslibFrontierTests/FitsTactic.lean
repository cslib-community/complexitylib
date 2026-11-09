/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the fits tactic)

public import CslibFrontier.Tactic.Fits
public import CslibFrontier.Computability.WordRAM.ExactNotation

/-!
# Tests for `fits`
-/

public section

open Cslib.WordRAM

variable {w a b c n : ℕ}

/-! A bound follows from any word-size fact in context, whatever its name. -/

example (hfit_end : Fits w (n + 5)) (h : a ≤ n) : Fits w (a + 3) := by
  fits

example (h₁ : Fits w a) (h₂ : Fits w b) (h : c ≤ a ∨ c ≤ b) : Fits w c := by
  fits

example : Fits w n → Fits w (n / 2) := by
  intro
  fits

/-! Constants, shifts and powers of two, as in the address and mask computations of programs. -/

example (h : Fits w (n + 2)) : Fits w 0 ∧ Fits w 1 ∧ Fits w 2 := by
  fits

example (hb : Fits w (2 ^ c)) : Fits w (2 ^ c - 1) := by
  fits

example (h : Fits w (2 * a + 1)) : Fits w (a <<< 1) := by
  fits

/-- A wider word: `omega` reads `2 ^ (w + 1)` as `2 * 2 ^ w`. -/
example (h : Fits w n) : Fits (w + 1) (2 * n + 1) := by
  fits

/-! The unfolded form `v < 2 ^ w`, in the goal or in a hypothesis. -/

example (h : Fits w n) : n - 1 < 2 ^ w := by
  fits

example (h : n < 2 ^ w) (ha : a ≤ n) : Fits w a := by
  fits

/-! Hypotheses that combine word-size facts. -/

example (h : Fits w a ∧ Fits w b) : Fits w (min a b) ∧ Fits w (max a b) := by
  fits

example (h : ¬Fits w a) (hb : a ≤ b) : ¬Fits w b := by
  fits

/-! Products are atoms: give a bound on one as a term. -/

example (h : Fits w (a * b)) (hc : c ≤ a) : Fits w (c * b) := by
  fits [Nat.mul_le_mul_right b hc]

/-! A side condition inline, as an argument. -/

example (h : Fits w (n + 1)) : Fits w n ∧ Fits w (n + 1) :=
  ⟨by fits, h⟩

/-! Sibling goals stay pending. -/

set_option linter.style.multiGoal false in
example (h : Fits w n) : Fits w (n - 1) ∧ Nonempty ℕ := by
  constructor
  fits
  exact ⟨0⟩

/-! `ram_eval` and `ram_exact_eval` decide which written values fit a word with `fits`
(`reduceFits`), so a bound that follows from a fact in context needs no statement of its own. -/

/-- A register name for the examples. -/
abbrev r0 : Fin 2 := 0
/-- A register name for the examples. -/
abbrev r1 : Fin 2 := 1

example (x : Data 2) (hx : x.regs r0 = n) (hfit : Fits w (2 * n + 1)) :
    ExecWithin w ram[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 := by
  ram_eval [hx]

example (x : Data 2) (hx : x.regs r0 = n) (hfit : Fits w (2 * n + 1)) :
    Exec w ram_exact[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 := by
  ram_exact_eval [hx]

/-- Without a fact that implies the bound, the value is not known to fit and evaluation is stuck. -/
example (x : Data 2) (_hx : x.regs r0 = n) (_hfit : Fits w n) :
    ExecWithin w ram[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 ∨ True := by
  fail_if_success (left; ram_eval [_hx])
  exact Or.inr trivial

/-! Failures. -/

/-- error: fits: the goal is not a word-size bound `Fits w v` or `v < 2 ^ w`; use `omega` for other arithmetic.
  a ≤ b + 1 -/
#guard_msgs in
example (_h : Fits w a) (h : a ≤ b) : a ≤ b + 1 := by
  fits

/-- A bound that does not follow fails, rather than leaving a goal, with or without a hypothesis
`Fits w v` in context. -/
example (_h : Fits w n) : True := by
  fail_if_success have : Fits w (n + 1) := by fits
  fail_if_success have : Fits w n := by clear _h; fits
  trivial

end
