/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.BankOps

/-!
# Arithmetic instruction graphs for multiword RAM execution

Virtual registers are eighteen-digit entries of `Multiword.Bank`. A binary node names only
standard RAM operations. Its execution is implemented by the checked digit routines rather
than by enlarging the RAM's operation basis or physical width.

## Main definitions

* `Circuit.Operation`: a constant or a binary standard operation on virtual registers.
* `Circuit.Operation.eval`: the mathematical value of one node.
* `Circuit.Operation.Earlier`, `Circuit.Operation.Admissible`: topological-order and operand/result
  width-bound predicates for compiling an operation.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Circuit

/-- A node in a fixed register graph. Constants may depend on the physical width at code
construction time; the two arguments of a binary node are run-time register values. -/
inductive Operation (n : ℕ) where
  | constant (z : ℕ)
  | binary (f : BinOp) (a b : Fin n)
  deriving DecidableEq

namespace Operation

/-- Natural-number specification of a virtual instruction. -/
def eval {n : ℕ} (v : Fin n → ℕ) : Operation n → ℕ
  | .constant z => z
  | .binary f a b => f.eval (v a) (v b)

/-- Sources are earlier nodes in the instruction graph. -/
def Earlier {n : ℕ} (d : Fin n) : Operation n → Prop
  | .constant _ => True
  | .binary _ a b => a.val < d.val ∧ b.val < d.val

/-- Bounds needed by the concrete compiler. Multiplication, subtraction and Boolean
operations use digit routines. A right-shift count is reconstructed as a physical scalar;
the remaining operations use fitting physical operands and a fitting physical result. -/
def Admissible {n : ℕ} (w : ℕ) (v : Fin n → ℕ) (o : Operation n) : Prop :=
  o.eval v < 2 ^ (6 * w) ∧ match o with
  | .constant _ => True
  | .binary f a b => match f with
    | .and | .or | .xor | .mul | .sub => True
    | .shiftRight => Fits w (v b)
    | _ => Fits w (v a) ∧ Fits w (v b) ∧ Fits w (f.eval (v a) (v b))

end Operation

end Cslib.WordRAM.Multiword.Circuit

end
