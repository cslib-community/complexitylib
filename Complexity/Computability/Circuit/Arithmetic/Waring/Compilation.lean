/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Formula
public import Complexity.Computability.Circuit.Arithmetic.Power
public import Complexity.Computability.Circuit.Arithmetic.Waring.Basic
public import Complexity.Computability.Circuit.SimulationContext
public import Complexity.Computability.Circuit.SumOfTerms.Basic

/-!
# Compiling Waring circuits to arithmetic circuits

Each Waring term computes its linear form once, raises the result by binary powering, and
multiplies by its scale. Generic formulas compile the linear form and scaling; circuit
composition preserves sharing through the power computation. Contextual simulation then makes
the same variable block available to every term gadget and preserves every source output.

The construction accepts arbitrary coefficient symbols, with explicit symbols for zero and
one. Correctness requires their interpretations to be zero and one. Costs count all generated
gates, including unused source gates, coefficient constants and the initial zero. Multiplication
and addition counts specialize the exact arbitrary-weight formula. These are circuit costs,
not TM-time certificates for generating or evaluating encoded circuits, and no optimality of
the construction is asserted.

## Main definitions

* `Cslib.Circuits.Waring.Term.toCircuit`: linear form, binary power and final scaling.
* `Cslib.Circuits.Waring.termMultiplicationCount`: the multiplication count of a compiled term.
* `Cslib.Circuits.Waring.operationCircuit`: arithmetic gadget for a single source operation.
* `Cslib.Circuits.Waring.compile`: compile a sum-of-terms circuit with shared variable inputs.
* `Cslib.Circuits.Waring.compilationCost`: the exact charge of each source operation.

## Main results

* `Cslib.Circuits.Waring.eval_compile`: all outputs agree under a semiring interpretation.
* `Cslib.Circuits.Waring.polynomial_compile`: equality of formal polynomial outputs.
* `Cslib.Circuits.Waring.cost_program_compile`: exact arbitrary weighted cost.
* `Cslib.Circuits.Waring.mulCost_compile`, `Cslib.Circuits.Waring.addCost_compile`,
  `Cslib.Circuits.Waring.size_compile`: closed multiplication, addition and gate counts.

## References

* Adapted from LowerBound/Fusion/SumOfTerms/Waring/Translation.lean and its `Binary.lean`
  extension in [S. Schlesinger, *Algebraic circuit formalizations in
  Complexitylib*][Schlesinger2026Algebraic]. The source's separate arithmetic expression and
  contextual translation frameworks are replaced by the shared formula and circuit APIs.
-/

@[expose] public section

namespace Cslib.Circuits.Waring

universe v u

variable {C : Type v} {R : Type u} {d n m : ℕ}

/-- Compute the linear form once, use a binary-power DAG, and apply the scale once. -/
def Term.toCircuit (zero one : C) (t : Term C d) : Circuit (arithSignature C) d 1 :=
  let scale : Formula (arithSignature C) 1 :=
    .gate₂ .mul rfl (.gate (.const t.scale) Fin.elim0) (.input 0)
  scale.toCircuit.comp ((binaryPowerCircuit one d).comp
    (Formula.linearForm zero t.coefficients id).toCircuit)

/-- Term compilation preserves evaluation under any semiring interpretation of the symbols. -/
theorem Term.eval_toCircuit [Semiring R] (zero one : C) (constant : C → R)
    (hzero : constant zero = 0) (hone : constant one = 1) (t : Term C d) (x : Fin d → R) :
    (t.toCircuit zero one).eval (arithInterpretationWith C constant) x 0 = t.eval constant x := by
  rw [Term.toCircuit, Circuit.eval_comp, Formula.eval_toCircuit, Formula.eval_gate₂]
  simp only [Formula.eval_gate, Formula.eval_input, arithInterpretationWith_mul,
    arithInterpretationWith_const, Fin.cast_refl]
  rw [Circuit.eval_comp, eval_binaryPowerCircuit one constant hone,
    Formula.eval_toCircuit, Formula.eval_linearForm zero constant hzero]
  rfl

/-- Exact weighted term cost, including all coefficient and zero/one constants. -/
private theorem Term.cost_program_toCircuit (zero one : C) (weight : ArithOp C → ℕ) (t : Term C d) :
    (t.toCircuit zero one).program.cost weight =
      weight (.const zero) +
        (∑ i, (weight (.const (t.coefficients i)) + weight .mul + weight .add)) +
        (if d = 0 then weight (.const one) else binaryMultiplicationCount d * weight .mul) +
        (weight (.const t.scale) + weight .mul) := by
  rw [Term.toCircuit, Circuit.cost_program_comp, Circuit.cost_program_comp,
    Formula.cost_toCircuit, Formula.cost_linearForm, cost_program_binaryPowerCircuit,
    Formula.cost_toCircuit, Formula.cost_gate₂]
  simp [Formula.cost]

/-- The multiplication count of a compiled term, including coefficient and scale products. -/
def termMultiplicationCount (d : ℕ) : ℕ := d + binaryMultiplicationCount d + 1

/-- Exact term multiplication count, including the final scale multiplication at degree zero. -/
private theorem Term.mulCost_toCircuit (zero one : C) (t : Term C d) :
    (t.toCircuit zero one).program.cost ArithOp.mulCost = termMultiplicationCount d := by
  rw [Term.cost_program_toCircuit]
  by_cases hd : d = 0 <;> simp [ArithOp.mulCost, termMultiplicationCount, hd]

/-- There is one linear-form addition per variable, including the initial addition to zero. -/
private theorem Term.addCost_toCircuit (zero one : C) (t : Term C d) :
    (t.toCircuit zero one).program.cost ArithOp.addCost = d := by
  rw [Term.cost_program_toCircuit]
  simp [ArithOp.addCost]

/-- The total gate count includes coefficient constants, zero, scaling, and the power circuit. -/
theorem Term.size_toCircuit (zero one : C) (t : Term C d) :
    (t.toCircuit zero one).size =
      3 * d + (if d = 0 then 1 else binaryMultiplicationCount d) + 3 := by
  have h := t.cost_program_toCircuit zero one (fun _ => 1)
  simp only [Program.cost_const, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at h
  lia

/-- Binary powering adds at most twice the binary logarithm to the linear-form cost.
This includes degree zero, where only the final scale multiplication is charged. -/
theorem termMultiplicationCount_le (d : ℕ) :
    termMultiplicationCount d ≤ d + 2 * Nat.log2 d + 1 := by
  have := binaryMultiplicationCount_le_two_mul_log2 d
  unfold termMultiplicationCount
  lia

/-- One arithmetic gadget for a source operation, reading variables before source arguments. -/
def operationCircuit (zero one : C) (d : ℕ) :
    (op : SumOfTerms.Op (Term C d)) → Circuit (arithSignature C) (d + op.arity) 1
  | .add => Circuit.oneGate .add (Fin.natAdd d)
  | .term t => t.toCircuit zero one

/-- Compile every source operation, sharing the first `d` inputs as the variable context.
Any original inputs follow that context and remain available to the source program. -/
def compile (zero one : C) (c : Circuit (SumOfTerms.signature (Term C d)) n m) :
    Circuit (arithSignature C) (d + n) m :=
  c.simulateWithContext d (operationCircuit zero one d)

/-- Interpret the shared variables and preserve all source outputs, including supplied inputs. -/
theorem eval_compile [Semiring R] (zero one : C) (constant : C → R)
    (hzero : constant zero = 0) (hone : constant one = 1)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) (x : Fin d → R) (y : Fin n → R) :
    (compile zero one c).eval (arithInterpretationWith C constant) (Fin.append x y) =
      c.eval (SumOfTerms.interpretation (fun t => t.eval constant x)) y := by
  rw [compile, Circuit.eval_simulateWithContext]
  congr 1
  funext op args
  cases op with
  | add => simp [operationCircuit, Circuit.eval_oneGate, arithInterpretationWith]
  | term t =>
    have hx : Fin.append x args = x := funext fun i => Fin.append_left _ _ i
    rw [operationCircuit, hx, Term.eval_toCircuit zero one constant hzero hone]
    rfl

/-- Compiling a closed Waring circuit preserves equality of formal polynomials at every output. -/
theorem polynomial_compile {K : Type*} [CommSemiring K]
    (c : Circuit (SumOfTerms.signature (Term K d)) 0 m) :
    (compile 0 1 c).eval (arithInterpretationWith K MvPolynomial.C) MvPolynomial.X =
      c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 := by
  have h : (fun t : Term K d => t.eval MvPolynomial.C MvPolynomial.X) = Term.polynomial := by
    funext t
    simp only [Term.eval, Term.polynomial, MvPolynomial.smul_eq_C_mul]
  simpa only [Fin.append_elim0, Fin.cast_refl, Function.comp_id, h] using
    eval_compile 0 1 MvPolynomial.C MvPolynomial.C_0 MvPolynomial.C_1 c MvPolynomial.X Fin.elim0

/-- The complete generated cost of each source operation, with arbitrary constant weights. -/
def compilationCost (zero one : C) (weight : ArithOp C → ℕ) : SumOfTerms.Op (Term C d) → ℕ
  | .add => weight .add
  | .term t =>
      weight (.const zero) +
        (∑ i, (weight (.const (t.coefficients i)) + weight .mul + weight .add)) +
        (if d = 0 then weight (.const one) else binaryMultiplicationCount d * weight .mul) +
        (weight (.const t.scale) + weight .mul)

/-- Every source gate is charged exactly once, including gates unused by the chosen outputs. -/
theorem cost_program_compile (zero one : C)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) (weight : ArithOp C → ℕ) :
    (compile zero one c).program.cost weight =
      c.program.cost (compilationCost zero one weight) := by
  rw [compile, Circuit.cost_program_simulateWithContext]
  congr 1
  funext op
  cases op with
  | add => exact Circuit.cost_program_oneGate _ _ _
  | term t => exact t.cost_program_toCircuit zero one weight

/-- Uniform term costs separate the total charge into source additions and term gates. -/
private theorem cost_program_compile_of_termCost (zero one : C)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) (weight : ArithOp C → ℕ) {term : ℕ}
    (hterm : ∀ t : Term C d, (t.toCircuit zero one).program.cost weight = term) :
    (compile zero one c).program.cost weight =
      weight .add * c.program.cost SumOfTerms.addCost +
        term * c.program.cost SumOfTerms.termCost := by
  rw [compile, Circuit.cost_program_simulateWithContext]
  have h : (fun op => (operationCircuit zero one d op).program.cost weight) =
      SumOfTerms.weightedCost (weight .add) term := by
    funext op
    cases op with
    | add => exact Circuit.cost_program_oneGate _ _ _
    | term t => exact hterm t
  rw [h, SumOfTerms.cost_weightedCost]

/-- Multiplications are exactly the per-term count times the number of source term gates. -/
theorem mulCost_compile (zero one : C)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) :
    (compile zero one c).program.cost ArithOp.mulCost =
      termMultiplicationCount d * c.program.cost SumOfTerms.termCost := by
  simpa only [ArithOp.mulCost, zero_mul, zero_add] using
    cost_program_compile_of_termCost zero one c ArithOp.mulCost (Term.mulCost_toCircuit zero one)

/-- Source additions remain, and every term contributes its `d` linear-form additions. -/
theorem addCost_compile (zero one : C)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) :
    (compile zero one c).program.cost ArithOp.addCost =
      c.program.cost SumOfTerms.addCost + d * c.program.cost SumOfTerms.termCost := by
  simpa only [ArithOp.addCost, one_mul] using
    cost_program_compile_of_termCost zero one c ArithOp.addCost (Term.addCost_toCircuit zero one)

/-- The full gate count, including constants and source gates unused by the outputs. -/
theorem size_compile (zero one : C)
    (c : Circuit (SumOfTerms.signature (Term C d)) n m) :
    (compile zero one c).size = c.program.cost SumOfTerms.addCost +
      (3 * d + (if d = 0 then 1 else binaryMultiplicationCount d) + 3) *
        c.program.cost SumOfTerms.termCost := by
  simpa only [Program.cost_const, one_mul] using
    cost_program_compile_of_termCost zero one c (fun _ => 1)
      (fun t => by simpa only [Program.cost_const, one_mul] using t.size_toCircuit zero one)

end Cslib.Circuits.Waring
