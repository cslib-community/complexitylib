/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Foundations.Data.MvPolynomial.Hessian
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Floor.Div
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import CslibFrontier.Foundations.LinearAlgebra.Rank

/-!
# Hessian rank bounds multiplication count

At a fixed point, each multiplication adds a symmetrized outer product of gradients to the
span of the previously available Hessians. Its rank is at most two. Every wire Hessian lies in
the span of the supplied input Hessians and these contributions. Subtracting a suitable linear
combination of input Hessians therefore leaves rank at most twice the multiplication count.
A shared gate contributes once, however often its value is reused.

The theorem concerns equality of formal polynomials, over a field of any characteristic.
Agreement of polynomial functions on a finite field does not suffice. Constants and additions
are free; every multiplication, including multiplication by a scalar, costs one. Input and
output wiring is free. Supplied input polynomials may be arbitrary. When their Hessians vanish
at the chosen point, including for affine inputs, the output Hessian itself satisfies the bound.
The residual coefficients may depend on the selected wire and point; no point-independent
polynomial decomposition is asserted.

This ports the Hessian application of the Algebraic library to the native circuit API.

## Main results

* `Cslib.Circuits.Program.exists_hessian_residual`,
  `Cslib.Circuits.Circuit.exists_hessian_residual`: arbitrary supplied polynomial inputs.
* `Cslib.Circuits.Circuit.exists_helper_hessian_residual`: raw variables and helper inputs.
* `Cslib.Circuits.Program.rank_hessian_trace_le`: a bound for every program wire.
* `Cslib.Circuits.Circuit.hessian_rank_le`: output rank is at most twice multiplication count.
* `Cslib.Circuits.Circuit.hessian_rank_ceilDiv_two_le`: half the target's Hessian rank,
  rounded up, lower-bounds the multiplication count of a circuit computing it.

## References

* The source applications are Applications/Hessian.lean and
  LowerBound/Fusion/Arithmetic/Interaction/Hessian/Relative.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997] for background on arithmetic circuits.
-/

@[expose] public section

namespace Cslib.Circuits

open MvPolynomial

variable {C K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {n g m : ℕ}

private noncomputable def hessianInteraction (point : ι → K) :
    (op : ArithOp C) → (Fin op.arity → MvPolynomial ι K) → (ι → K) →ₗ[K] (ι → K)
  | .add, _ => 0
  | .const _, _ => 0
  | .mul, args => Matrix.toLin'
      (Matrix.vecMulVec (gradient point (args 0)) (gradient point (args 1)) +
        Matrix.vecMulVec (gradient point (args 1)) (gradient point (args 0)))

private theorem rank_hessianInteraction_le (point : ι → K) (op : ArithOp C)
    (args : Fin op.arity → MvPolynomial ι K) :
    (hessianInteraction point op args).rank ≤ (2 * op.mulCost : ℕ) := by
  have outer (a b : ι → K) : (Matrix.toLin' (Matrix.vecMulVec a b)).rank ≤ 1 := by
    rw [← Matrix.natCast_rank_eq_rank_toLin']
    exact_mod_cast Matrix.rank_vecMulVec_le a b
  cases op with
  | add => simp [hessianInteraction, ArithOp.mulCost]
  | const c => simp [hessianInteraction, ArithOp.mulCost]
  | mul =>
    simpa [hessianInteraction, ArithOp.mulCost, one_add_one_eq_two] using
      (LinearMap.rank_add_le _ _).trans (add_le_add
        (outer (gradient point (args 0)) (gradient point (args 1)))
        (outer (gradient point (args 1)) (gradient point (args 0))))

private theorem Program.hessian_trace_mem (p : Program (arithSignature C) n g)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K)
    (S : Submodule K ((ι → K) →ₗ[K] (ι → K)))
    (hinput : ∀ i, Matrix.toLin' (hessian point (input i)) ∈ S)
    (hgate : ∀ k, hessianInteraction point (p.lines k).op
      (fun a => p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input
        ((p.lines k).wires a)) ∈ S) (w : Wire n g) :
    Matrix.toLin' (hessian point
      (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w)) ∈ S := by
  let I : Interpretation (arithSignature C) (MvPolynomial ι K) :=
    arithInterpretationWith C (MvPolynomial.C ∘ constant)
  have step (op : ArithOp C) (args : Fin op.arity → MvPolynomial ι K)
      (hargs : ∀ a, Matrix.toLin' (hessian point (args a)) ∈ S)
      (hnew : hessianInteraction point op args ∈ S) :
      Matrix.toLin' (hessian point (I op args)) ∈ S := by
    cases op with
    | add => simpa [I] using S.add_mem (hargs 0) (hargs 1)
    | const c => simp [I]
    | mul =>
      simpa [I, hessian_mul, hessianInteraction] using
        S.add_mem (S.add_mem (S.smul_mem (MvPolynomial.eval point (args 1)) (hargs 0))
          (S.smul_mem (MvPolynomial.eval point (args 0)) (hargs 1))) hnew
  refine p.wire_induction
    (P := fun w => Matrix.toLin' (hessian point (p.trace I input w)) ∈ S)
    (fun i => ?_) (fun k ih => ?_) w
  · simpa using hinput i
  · rw [p.trace_gate]
    exact step _ _ ih (hgate k)

omit [DecidableEq ι] in
/-- For arbitrary supplied polynomial inputs, subtracting a linear combination of their
Hessians leaves rank at most twice the multiplication count. Coefficients may depend on the
program, selected wire and evaluation point; no cost is charged for supplying the inputs. -/
theorem Program.exists_hessian_residual (p : Program (arithSignature C) n g)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K) (w : Wire n g) :
    ∃ coefficients : Fin n → K,
      (hessian point
          (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w) -
        ∑ i, coefficients i • hessian point (input i)).rank ≤ 2 * p.cost ArithOp.mulCost := by
  classical
  let family := fun k => hessianInteraction point (p.lines k).op
    (fun a => p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input
      ((p.lines k).wires a))
  have hmem := p.hessian_trace_mem constant point input
    (Submodule.span K (Set.range fun i => Matrix.toLin' (hessian point (input i))) ⊔
      Submodule.span K (Set.range family))
    (fun i => Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
    (fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)) w
  obtain ⟨source, hsource, residual, hresidual, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨coefficients, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hsource
  have heq : Matrix.toLin' (hessian point
      (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w) -
        ∑ i, coefficients i • hessian point (input i)) = residual := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hcoeff, ← hsum, add_sub_cancel_left]
  have h := LinearMap.rank_le_sum_of_mem_span residual family
    (fun k => 2 * (p.lines k).op.mulCost) hresidual
    (fun k => rank_hessianInteraction_le point (p.lines k).op _)
  rw [← heq, ← Matrix.natCast_rank_eq_rank_toLin', ← Nat.cast_sum, ← Finset.mul_sum,
    ← p.cost_eq_sum] at h
  exact ⟨coefficients, by exact_mod_cast h⟩

omit [DecidableEq ι] in
/-- With input Hessians zero at the chosen point, every wire's Hessian rank is at most twice
the number of multiplication gates. Inputs may be arbitrary affine polynomials. -/
theorem Program.rank_hessian_trace_le (p : Program (arithSignature C) n g)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K)
    (hinput : ∀ i, hessian point (input i) = 0) (w : Wire n g) :
    (hessian point
      (p.trace (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input w)).rank ≤
        2 * p.cost ArithOp.mulCost := by
  classical
  obtain ⟨coefficients, h⟩ := p.exists_hessian_residual constant point input w
  simpa [hinput] using h

omit [DecidableEq ι] in
/-- A circuit computing a formal polynomial from arbitrary supplied polynomials has a
source-adjusted Hessian of rank at most twice its multiplication count. -/
theorem Circuit.exists_hessian_residual (c : Circuit (arithSignature C) n m)
    (constant : C → K) (point : ι → K) (input : Fin n → MvPolynomial ι K)
    (j : Fin m) (polynomial : MvPolynomial ι K)
    (hcompute : c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant)) input j =
      polynomial) :
    ∃ coefficients : Fin n → K,
      (hessian point polynomial - ∑ i, coefficients i • hessian point (input i)).rank ≤
        2 * c.program.cost ArithOp.mulCost := by
  rw [← hcompute]
  exact c.program.exists_hessian_residual constant point input (c.outputs j)

/-- When raw variables and helper polynomials are supplied, only helper Hessians need to be
subtracted: the raw variables have zero Hessian. -/
theorem Circuit.exists_helper_hessian_residual {k : ℕ}
    (c : Circuit (arithSignature C) (n + k) m) (constant : C → K) (point : Fin n → K)
    (helpers : Fin k → MvPolynomial (Fin n) K) (j : Fin m) (polynomial : MvPolynomial (Fin n) K)
    (hcompute : c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant))
      (Fin.append X helpers) j = polynomial) :
    ∃ coefficients : Fin k → K,
      (hessian point polynomial - ∑ i, coefficients i • hessian point (helpers i)).rank ≤
        2 * c.program.cost ArithOp.mulCost := by
  obtain ⟨coefficients, h⟩ := c.exists_hessian_residual constant point _ j polynomial hcompute
  refine ⟨fun i => coefficients (Fin.natAdd n i), ?_⟩
  simpa only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, hessian_X, smul_zero,
    Finset.sum_const_zero, zero_add] using h

/-- A formal polynomial computed by an arithmetic circuit has Hessian rank at most twice the
number of multiplication gates. This applies separately to every selected output. -/
theorem Circuit.hessian_rank_le (c : Circuit (arithSignature C) n m) (constant : C → K)
    (point : Fin n → K) (j : Fin m) :
    (hessian point
      (c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant)) X j)).rank ≤
        2 * c.program.cost ArithOp.mulCost :=
  c.program.rank_hessian_trace_le constant point X (hessian_X point) (c.outputs j)

/-- Half the target's Hessian rank, rounded up, lower-bounds the multiplication count.
The computation premise is equality of formal polynomials. -/
theorem Circuit.hessian_rank_ceilDiv_two_le (c : Circuit (arithSignature C) n m)
    (constant : C → K) (point : Fin n → K) (j : Fin m) (polynomial : MvPolynomial (Fin n) K)
    (hcompute : c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant)) X j = polynomial) :
    (hessian point polynomial).rank ⌈/⌉ 2 ≤ c.program.cost ArithOp.mulCost := by
  apply (ceilDiv_le_iff_le_mul (by decide)).mpr
  rw [← hcompute]
  exact c.hessian_rank_le constant point j

end Cslib.Circuits
