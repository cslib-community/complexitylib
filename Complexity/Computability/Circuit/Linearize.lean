/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Computability.Circuit.InnerSize
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi
import Complexity.Computability.Circuit.Program
import Complexity.Foundations.Data.MvPolynomial.DualNumber
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Linearizing polynomial circuits

**Affine circuits compute affine maps** (`Cslib.Circuits.Program.exists_affine_trace`): in a
circuit over the affine basis, the value of every wire is an affine function of the input.

**Linearization** (`Cslib.Circuits.Circuit.Computes.exists_affine`). Over an infinite field, a
circuit with polynomial operations that computes a linear map `x ↦ M x` can be replaced by a
circuit over the affine basis, with the same wires, that computes the same map: nonlinear
operations do not help to compute linear maps, as in Strassen's theorem on linear complexity
[BurgisserClausenShokrollahi1997, Chapter 13]. Each gate is
replaced by its first-order Taylor expansion at the point that its arguments take on the zero
input (`Cslib.Circuits.taylorOp`, `Cslib.Circuits.Program.linearize`).

To see why this works, evaluate the circuit over the dual numbers `F[ε]`, where `ε² = 0`, at the
input `ε x`. Because the operations are polynomials, a gate whose arguments are `z + ε v` takes
the value `P(z) + ε ∑_a ∂_a P(z) v_a` (`MvPolynomial.snd_aeval_dualNumber`), where `z` is the
value of the arguments on the zero input. So where the circuit takes the value `a + ε b` at
`ε x`, the linearized circuit takes the value `a + b` at `x`
(`Cslib.Circuits.Program.trace_linearize`). Over an infinite field a polynomial is determined by
its values, so the polynomial computed at an output is the linear form `∑_j M_{ij} X_j`, whose
value at `ε x` is `ε (M x)_i`.

## Main definitions

* `Cslib.Circuits.polynomialInterpretation`: the operations given by polynomials, over any
  algebra.
* `Cslib.Circuits.taylorOp`: the affine operation of the first-order Taylor expansion.
* `Cslib.Circuits.Program.linearize`: the linearization of a program with polynomial operations.

## Main results

* `Cslib.Circuits.Program.exists_affine_trace`: affine circuits compute affine maps.
* `Cslib.Circuits.Program.trace_linearize`: the linearized program reads off the dual numbers.
* `Cslib.Circuits.Circuit.Computes.exists_affine`: linearization of circuits for linear maps.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 13
-/

@[expose] public section

open MvPolynomial TrivSqZeroExt
open scoped DualNumber Matrix

namespace Cslib.Circuits

variable {F : Type*} {n s m : ℕ}

/-- **Affine circuits compute affine maps.** In a program over the affine basis, the value of
every wire is a linear map of the input plus a constant. -/
theorem Program.exists_affine_trace [CommRing F] (p : Program (affineSignature F) n s)
    (w : Wire n s) :
    ∃ (L : (Fin n → F) →ₗ[F] F) (b : F), ∀ x, p.trace (affineInterpretation F) x w = L x + b := by
  induction p with
  | empty =>
    cases w with
    | input i => exact ⟨LinearMap.proj i, 0, fun x => by simp⟩
    | gate g => exact g.elim0
  | gate p line ih =>
    refine Wire.lastCases ?_ (fun w => ?_) w
    · obtain ⟨⟨k, c, d⟩, wires⟩ := line
      choose L b h using fun a => ih (wires a)
      refine ⟨∑ a, c a • L a, ∑ a, c a * b a + d, fun x => ?_⟩
      rw [Program.trace_gate_last]
      simp [h, mul_add, Finset.sum_add_distrib, add_assoc]
    · obtain ⟨L, b, h⟩ := ih w
      exact ⟨L, b, fun x => by rw [Program.trace_gate_castSucc, h]⟩

/-! ### Polynomial interpretations over algebras -/

section Polynomial

variable {σ : Signature} [CommRing F] (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)

/-- The interpretation over an `F`-algebra `R` in which each operation `o` substitutes its
arguments into the polynomial `P o`. Every polynomial interpretation over `F` is of this form
(`Cslib.Circuits.Interpretation.IsPolynomial`). -/
def polynomialInterpretation (R : Type*) [CommRing R] [Algebra F R] :
    Interpretation σ R :=
  fun o x => aeval x (P o)

/-- An operation of a polynomial interpretation substitutes its arguments into its
polynomial. -/
theorem polynomialInterpretation_apply (R : Type*) [CommRing R] [Algebra F R] (o : σ.Op)
    (x : Fin (σ.Arity o) → R) : polynomialInterpretation P R o x = aeval x (P o) :=
  rfl

/-- Evaluation of a program with polynomial operations commutes with algebra
homomorphisms. -/
private theorem Program.map_trace_polynomialInterpretation {R S : Type*} [CommRing R] [Algebra F R]
    [CommRing S] [Algebra F S] (φ : R →ₐ[F] S) (p : Program σ n s) (x : Fin n → R)
    (w : Wire n s) :
    φ (p.trace (polynomialInterpretation P R) x w) =
      p.trace (polynomialInterpretation P S) (fun j => φ (x j)) w :=
  congrFun (p.map_trace ⟨φ, fun o y => comp_aeval_apply y φ (P o)⟩ x) w

end Polynomial

/-! ### Linearization -/

section Linearize

variable [CommRing F] {k : ℕ}

/-- The affine operation computing the first-order Taylor expansion of `P` at `z`,
`y ↦ P(z) + ∑_a ∂_a P(z) (y_a - z_a)`. -/
noncomputable def taylorOp (P : MvPolynomial (Fin k) F) (z : Fin k → F) :
    (affineSignature F).Op :=
  ⟨k, fun a => eval z (pderiv a P), eval z P - ∑ a, eval z (pderiv a P) * z a⟩

/-- The value of the first-order Taylor expansion of `P` at `z`. -/
private theorem affineInterpretation_taylorOp (P : MvPolynomial (Fin k) F) (z y : Fin k → F) :
    affineInterpretation F (taylorOp P z) y =
      eval z P + ∑ a, eval z (pderiv a P) * (y a - z a) := by
  simp only [taylorOp, affineInterpretation_apply, mul_sub, Finset.sum_sub_distrib]
  ring

variable {σ : Signature} (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)

/-- The *linearization* of a program whose operations are the polynomials `P`: the program over
the affine basis with the same wires, in which each gate is replaced by its first-order Taylor
expansion at the point that its arguments take on the zero input. -/
noncomputable def Program.linearize : ∀ {s : ℕ}, Program σ n s → Program (affineSignature F) n s
  | _, .empty => .empty
  | _, .gate p line => (p.linearize).gate
      ⟨taylorOp (P line.op) fun a => p.trace (polynomialInterpretation P F) 0 (line.wires a),
        line.wires⟩

/-- Linearization preserves the arity of every gate. -/
private theorem Program.arity_lines_linearize (p : Program σ n s) (g : Fin s) :
    (affineSignature F).Arity ((p.linearize P).lines g).op = σ.Arity (p.lines g).op := by
  induction p with
  | empty => exact g.elim0
  | gate p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · simp only [linearize, Program.lines_gate_last, Line.mapWires_op]
      rfl
    · simp only [linearize, Program.lines_gate_castSucc, Line.mapWires_op]
      exact ih g

/-- Linearization preserves the inner gates. -/
private theorem Program.innerGates_linearize (p : Program σ n s) :
    (p.linearize P).innerGates = p.innerGates :=
  Finset.filter_congr fun g _ => by rw [arity_lines_linearize]

/-- Linearization preserves fan-in. -/
private theorem Program.fanInAtMost_linearize (p : Program σ n s) (r : ℕ) :
    (p.linearize P).FanInAtMost r ↔ p.FanInAtMost r := by
  simp only [Program.fanInAtMost_iff]
  exact forall_congr' fun g => iff_of_eq (congrArg (· ≤ r) (p.arity_lines_linearize P g))

/-- The real part of the value of a wire at the input `ε x` is its value at the zero input. -/
private theorem Program.fst_trace_dualNumber (p : Program σ n s) (x : Fin n → F) (w : Wire n s) :
    (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).fst =
      p.trace (polynomialInterpretation P F) 0 w :=
  p.map_trace_polynomialInterpretation P (fstHom F F F) _ w

/-- **The linearized program.** Where the original program takes the value `a + ε b` at the
input `ε x`, the linearized program takes the value `a + b` at the input `x`. -/
theorem Program.trace_linearize (p : Program σ n s) (x : Fin n → F) (w : Wire n s) :
    (p.linearize P).trace (affineInterpretation F) x w =
      (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).fst +
        (p.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) w).snd := by
  induction p with
  | empty =>
    cases w with
    | input i => simp
    | gate g => exact g.elim0
  | gate p line ih =>
    refine Wire.lastCases ?_ (fun w => ?_) w
    · -- The new gate is the first-order Taylor expansion of the old one.
      refine (Program.trace_gate_last _ _ _ _).trans
        ((affineInterpretation_taylorOp _ _ _).trans ?_)
      rw [Program.trace_gate_last]
      simp only [ih, polynomialInterpretation_apply, fst_aeval_dualNumber, snd_aeval_dualNumber,
        fst_trace_dualNumber, add_sub_cancel_left]
    · simpa only [linearize, Program.trace_gate_castSucc] using ih w

/-- Over an infinite field, a circuit with polynomial operations that computes `x ↦ M x` takes
the value `ε (M x)_i` at its output `i` on the input `ε x`. -/
private theorem Circuit.trace_outputs_dualNumber [IsDomain F] [Infinite F] {c : Circuit σ n m}
    {M : Matrix (Fin m) (Fin n) F}
    (hc : c.Computes (polynomialInterpretation P F) fun x => M *ᵥ x)
    (x : Fin n → F) (i : Fin m) :
    c.program.trace (polynomialInterpretation P F[ε]) (fun j => inr (x j)) (c.outputs i) =
      inr ((M *ᵥ x) i) := by
  -- The polynomial computed at the output.
  have hQ : c.program.trace (polynomialInterpretation P (MvPolynomial (Fin n) F)) X
      (c.outputs i) = ∑ j, C (M i j) * X j := by
    refine MvPolynomial.funext fun y => ?_
    have h := c.program.map_trace_polynomialInterpretation P (aeval y) X (c.outputs i)
    simp only [aeval_X] at h
    rw [← aeval_eq_eval, h]
    exact (congrFun (hc y) i).trans (by simp [Matrix.mulVec, dotProduct])
  -- Its value at `ε x`.
  have h := c.program.map_trace_polynomialInterpretation P
    (aeval fun j => (inr (x j) : F[ε])) X (c.outputs i)
  simp only [aeval_X] at h
  rw [← h, hQ]
  ext <;> simp [algebraMap_eq_inl, fst_sum, snd_sum, Matrix.mulVec, dotProduct]

end Linearize

/-- **Linearization.** Over an infinite field, a circuit with polynomial operations computing a
linear map `x ↦ M x` is matched by a circuit over the affine basis computing the same map, with
the same number of gates, the same inner gates, and the same fan-in. -/
theorem Circuit.Computes.exists_affine [Field F] [Infinite F] {σ : Signature}
    {I : Interpretation σ F} (hI : I.IsPolynomial) {c : Circuit σ n m}
    {M : Matrix (Fin m) (Fin n) F} (hc : c.Computes I fun x => M *ᵥ x) :
    ∃ c' : Circuit (affineSignature F) n m, c'.size = c.size ∧
      c'.innerSize = c.innerSize ∧ (∀ r, c'.FanInAtMost r ↔ c.FanInAtMost r) ∧
      c'.Computes (affineInterpretation F) fun x => M *ᵥ x := by
  choose P hP using hI
  obtain rfl : I = polynomialInterpretation P F := funext fun o => funext (hP o)
  refine ⟨⟨c.program.linearize P, c.outputs⟩, rfl,
    congrArg Finset.card (c.program.innerGates_linearize P),
    fun r => c.program.fanInAtMost_linearize P r, fun x => funext fun i => ?_⟩
  change (c.program.linearize P).trace _ x (c.outputs i) = _
  rw [Program.trace_linearize, Circuit.trace_outputs_dualNumber P hc]
  simp

end Cslib.Circuits
