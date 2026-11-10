/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Circuit
public import CslibFrontier.Computability.WordRAM.Multiword.BankScalar
public import CslibFrontier.Computability.WordRAM.Multiword.BankArithmetic

/-!
# Compiling virtual arithmetic into checked standard RAM instructions

Each instruction graph node is expanded into concrete half-word arithmetic. Multiplication
uses the schoolbook program, subtraction propagates and checks a borrow, and shifts use the
checked digit division routine. Every emitted program has at most 4000 instructions and
executes within the same bound, independently of the physical width.

## Main definitions

* `Circuit.emit`: concrete standard-basis code for one virtual instruction.

## Main results

* `Circuit.exec_emit`: checked execution of a node, with a frame for the other bank entries.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Circuit

variable {n : ℕ}

/-- Compile one virtual instruction, preserving the original physical word width and
standard operation basis. -/
def emit (w : ℕ) (d : Fin n) : Operation n → Code .standard (Bank.capacity n + 4)
  | .constant z => Bank.constant w z d
  | .binary f a b => match f with
    | .and | .or | .xor => Bank.boolean f a b d
    | .mul => Bank.multiply a b d
    | .sub => Bank.subtract w a b d
    | .shiftRight => Bank.shift w a b d
    | _ => Bank.scalar f a b d

/-- Static code length has a uniform bound, including branch bodies that are not executed. -/
theorem size_emit (w : ℕ) (d : Fin n) (op : Operation n) : (emit w d op).size ≤ 4000 := by
  cases op with
  | constant z => rw [emit, Bank.size_constant]; decide
  | binary f a b =>
    cases f with
    | add | div | mod | shiftLeft => simp only [emit]; rw [Bank.size_scalar]; decide
    | and | or | xor => simp only [emit]; rw [Bank.size_boolean]; decide
    | mul => exact Bank.size_multiply_le a b d
    | sub => exact Bank.size_subtract_le w a b d
    | shiftRight => rw [emit, Bank.size_shift]; decide

/-- Every node executes through the concrete checked routines. The hypotheses assert only
source ordering and numerical bounds; they contain no wide-operation correctness oracle. -/
theorem exec_emit {w : ℕ} (hw : 2 ≤ w) (d : Fin n) (op : Operation n)
    (x : Data (Bank.capacity n + 4)) {v : Fin n → ℕ} (hx : Bank.Encodes w x v)
    (hearlier : op.Earlier d) (hadm : op.Admissible w v) :
    ∃ y, ExecWithin w (emit w d op) x y 4000 ∧
      Bank.Encodes w y (Function.update v d (op.eval v)) ∧ y.mem = x.mem := by
  cases op with
  | constant z =>
    obtain ⟨y, he, hy, hm, _⟩ := Bank.exec_constant hw d z hadm.1 x hx
    exact ⟨y, he.within.mono (by decide), hy, hm⟩
  | binary f a b =>
    obtain ⟨ha, hb⟩ := hearlier
    have hda : d ≠ a := fun h => by have := congrArg Fin.val h; omega
    have hdb : d ≠ b := fun h => by have := congrArg Fin.val h; omega
    cases f with
    | and =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_boolean hw (Or.inl rfl) a b d hda hdb x hx
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | or =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_boolean hw (Or.inr (Or.inl rfl))
        a b d hda hdb x hx
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | xor =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_boolean hw (Or.inr (Or.inr rfl))
        a b d hda hdb x hx
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | mul =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_multiply hw a b d x hx hadm.1
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | sub =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_subtract hw a b d hda hdb x hx
      exact ⟨y, he.mono (by decide), hy, hm⟩
    | shiftRight =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_shift hw a b d hda x hx hadm.2
      exact ⟨y, he.mono (by decide), hy, hm⟩
    | add =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_scalar hw .add a b d x hx
        hadm.2.1 hadm.2.2.1 hadm.2.2.2
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | div =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_scalar hw .div a b d x hx
        hadm.2.1 hadm.2.2.1 hadm.2.2.2
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | mod =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_scalar hw .mod a b d x hx
        hadm.2.1 hadm.2.2.1 hadm.2.2.2
      exact ⟨y, he.within.mono (by decide), hy, hm⟩
    | shiftLeft =>
      obtain ⟨y, he, hy, hm⟩ := Bank.exec_scalar hw .shiftLeft a b d x hx
        hadm.2.1 hadm.2.2.1 hadm.2.2.2
      exact ⟨y, he.within.mono (by decide), hy, hm⟩

end Cslib.WordRAM.Multiword.Circuit

end
