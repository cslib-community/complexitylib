/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Foundations.Data.MvPolynomial.PowerSum

/-!
# Reverse-mode differentiation of arithmetic circuits (Baur–Strassen)

Baur and Strassen proved that a function and all its first partial derivatives can be computed
together at a constant factor of the cost of the function alone [BaurStrassen1983]; Morgenstern
gave the reverse-mode formulation used here [Morgenstern1985]. See also
[Bürgisser, Clausen and Shokrollahi, §7.2][BurgisserClausenShokrollahi1997].

`Cslib.Circuits.Circuit.withGradient c j seed zero` runs the gates of `c`, emits the constant
gates `seed` and `zero`, and then walks the gates of `c` from the last to the first, keeping for
every wire an *adjoint* wire. The adjoint of output `j` starts at `seed`, every other adjoint at
`zero`. An addition gate adds its adjoint into the adjoints of both arguments. A multiplication
gate `u * v` with adjoint `a` adds `a * v` into the adjoint of `u` and `a * u` into the adjoint
of `v`. A wire read several times receives one contribution per read. The circuit keeps the outputs
of `c` and appends the adjoints of the `n` inputs.

The model is the library's: circuits over `Cslib.Circuits.arithSignature K`, with fan-in two
addition and multiplication and a constant gate for each element of `K`, computing polynomials
formally. Size counts every gate, constant gates included. There is no subtraction, so the
construction works over any commutative semiring.

* **Correctness.** Output `n + i` is `C seed * ∂(c j)/∂X i`
  (`Cslib.Circuits.Circuit.polynomial_withGradient_natAdd`). The underlying evaluation theorem
  (`Cslib.Circuits.Circuit.sum_eval_withGradient_natAdd`) holds for every additive map satisfying
  the Leibniz rule and vanishing on the constants.
* **Cost.** The size is exactly `s + 2 + 2 · #additions + 4 · #multiplications`, so at most
  `5 s + 2` for a circuit with `s` gates; the number of multiplications is exactly three times that
  of `c`. The latter is Baur and Strassen's factor three; it counts multiplications by constants,
  which their nonscalar measure does not.
* **Lower bounds.** A lower bound `S` for computing the gradient of `f` gives the lower bound
  `(S - 2) / 5` on the size of any circuit computing `f`, and `S / 3` on its multiplications
  (`Cslib.Circuits.Circuit.le_five_mul_size_add_two_of_gradient`,
  `Cslib.Circuits.Circuit.le_three_mul_mulCost_of_gradient`).

For the power sum `∑ i, X i ^ (d + 1)` with `d + 1` invertible in `K`, the gradient scaled by
`(d + 1)⁻¹` is the power map `(X 0 ^ d, …, X (n - 1) ^ d)`
(`Cslib.Circuits.Circuit.exists_pow_of_psum`). Strassen's degree bound [Strassen1973] (see
[Bürgisser, Clausen and Shokrollahi, Chapter 8][BurgisserClausenShokrollahi1997]) shows that the
power map needs about `n log₂ d` nonscalar multiplications, so the single power sum needs a third
of that. The degree bound is not formalized here; the reduction is stated as a lower-bound
transfer (`Cslib.Circuits.Circuit.le_three_mul_mulCost_of_psum`).

## Main definitions

* `Cslib.Circuits.Circuit.withGradient`: the circuit with the gradient of one output appended.

## Main results

* `Cslib.Circuits.Circuit.eval_withGradient_castAdd`,
  `Cslib.Circuits.Circuit.polynomial_withGradient_castAdd`: the original outputs are kept.
* `Cslib.Circuits.Circuit.sum_eval_withGradient_natAdd`: the new outputs are the adjoints.
* `Cslib.Circuits.Circuit.polynomial_withGradient_natAdd`: the new outputs are the partial
  derivatives.
* `Cslib.Circuits.Circuit.cost_program_withGradient`, `Cslib.Circuits.Circuit.size_withGradient`,
  `Cslib.Circuits.Circuit.size_withGradient_le`, `Cslib.Circuits.Circuit.mulCost_withGradient`,
  `Cslib.Circuits.Circuit.addCost_withGradient`: exact costs.
* `Cslib.Circuits.Program.cost_addCost_add_cost_mulCost_le`: additions and multiplications
  together are at most the number of gates.
* `Cslib.Circuits.Circuit.exists_gradient`: the Baur–Strassen theorem for arithmetic circuits.
* `Cslib.Circuits.Circuit.le_five_mul_size_add_two_of_gradient`,
  `Cslib.Circuits.Circuit.le_three_mul_mulCost_of_gradient`: lower-bound transfer.
* `Cslib.Circuits.Circuit.exists_pow_of_psum`,
  `Cslib.Circuits.Circuit.le_three_mul_mulCost_of_psum`: power sums and power maps.

## References

* [W. Baur and V. Strassen, *The complexity of partial derivatives*][BaurStrassen1983]
* [J. Morgenstern, *How to compute fast a function and all its derivatives*][Morgenstern1985]
* [V. Strassen, *Die Berechnungskomplexität von elementarsymmetrischen Funktionen und von
  Interpolationskoeffizienten*][Strassen1973]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997]
-/

public section

namespace Cslib.Circuits

universe u

variable {C : Type u} {n : ℕ}

namespace ReverseMode

/-- The state of the backward pass: a program extending the forward program, the copy of each
forward wire, the adjoint accumulator of each forward wire and the kept output wires. -/
private structure State (C : Type u) (n g m : ℕ) where
  {size : ℕ}
  program : Program (arithSignature C) n size
  value : Wire n g → Wire n size
  adjoint : Wire n g → Wire n size
  kept : Fin m → Wire n size

variable {g m : ℕ}

/-- Emit one gate. -/
@[reducible] private def State.push (s : State C n g m) (op : ArithOp C)
    (args : Fin op.arity → Wire n s.size) : State C n g m :=
  ⟨s.program.gate ⟨op, args⟩, Wire.castSucc ∘ s.value, Wire.castSucc ∘ s.adjoint,
    Wire.castSucc ∘ s.kept⟩

/-- The new wire emitted by `push`. -/
private abbrev State.last (s : State C n g m) : Wire n (s.size + 1) := .gate (Fin.last s.size)

/-- Add `t` into the adjoint of `w`. -/
@[reducible] private def State.accumulate (s : State C n g m) (w : Wire n g)
    (t : Wire n s.size) : State C n g m :=
  ⟨s.program.gate ⟨.add, ![s.adjoint w, t]⟩, Wire.castSucc ∘ s.value,
    Function.update (Wire.castSucc ∘ s.adjoint) w s.last, Wire.castSucc ∘ s.kept⟩

/-- Forget the last forward wire. -/
@[reducible] private def State.restrict (s : State C n (g + 1) m) : State C n g m :=
  ⟨s.program, s.value ∘ Wire.castSucc, s.adjoint ∘ Wire.castSucc, s.kept⟩

/-- Process the last forward gate, with operation `op` reading `wires`. -/
private def State.step (s : State C n (g + 1) m) :
    (op : ArithOp C) → (Fin op.arity → Wire n g) → State C n g m
  | .add, wires =>
      let r := s.restrict
      let a := s.adjoint (.gate (Fin.last g))
      (r.accumulate (wires 0) a).accumulate (wires 1) (Wire.castSucc a)
  | .mul, wires =>
      let r := s.restrict
      let a := s.adjoint (.gate (Fin.last g))
      let r₁ := r.push .mul ![a, r.value (wires 1)]
      let r₂ := r₁.accumulate (wires 0) r.last
      let r₃ := r₂.push .mul ![Wire.castSucc (Wire.castSucc a), r₂.value (wires 0)]
      r₃.accumulate (wires 1) r₂.last
  | .const _, _ => s.restrict

/-- The backward pass over the lines of `p`, from the last to the first. -/
private def backward : {g : ℕ} → Program (arithSignature C) n g → State C n g m → State C n 0 m
  | _, .empty, s => s
  | _, .gate p line, s => backward p (s.step line.op line.wires)

/-- The state before the backward pass: the forward circuit followed by the constant gates
`seed` and `zero`; the adjoint of output `j` is `seed` and every other adjoint is `zero`. -/
private def init {m : ℕ} (c : Circuit (arithSignature C) n m) (j : Fin m) (seed zero : C) :
    State C n c.size m :=
  let p₁ := c.program.gate ⟨.const seed, Fin.elim0⟩
  let p₂ := p₁.gate ⟨.const zero, Fin.elim0⟩
  ⟨p₂, fun w => Wire.castSucc (Wire.castSucc w),
    fun w => if w = c.outputs j then Wire.castSucc (.gate (Fin.last c.size))
      else .gate (Fin.last (c.size + 1)),
    fun k => Wire.castSucc (Wire.castSucc (c.outputs k))⟩

end ReverseMode

open ReverseMode in
/-- Reverse-mode differentiation [BaurStrassen1983]: the circuit `c` followed by `n` further
outputs, the adjoints of the inputs for output `j`, seeded by the constant `seed`. The constant
`zero` initializes the other adjoints. Outputs `0, …, m - 1` are those of `c`; with `seed = 1` and
`zero = 0`, output `m + i` computes the partial derivative of output `j` along input `i`. -/
def Circuit.withGradient {m : ℕ} (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) : Circuit (arithSignature C) n (m + n) :=
  let s := backward c.program (init c j seed zero)
  ⟨s.program, Fin.append s.kept fun i => s.adjoint (.input i)⟩

namespace ReverseMode

variable {g m : ℕ}

section Semantics

variable {R : Type*} [CommSemiring R] (constant : C → R) (x : Fin n → R)
  {M : Type*} [AddCommMonoid M] [Module R M] (D : R → M)

local notation "I" => arithInterpretationWith C constant

/-- The state computes the forward values `v` and the kept values `out`. -/
private def State.Represents (s : State C n g m) (v : Wire n g → R) (out : Fin m → R) : Prop :=
  s.program.trace I x ∘ s.value = v ∧ s.program.trace I x ∘ s.kept = out

/-- The adjoint-weighted sum of the derivatives of the forward values. -/
private def State.adjointSum (s : State C n g m) (v : Wire n g → R) : M :=
  ∑ w, s.program.trace I x (s.adjoint w) • D (v w)

variable {constant x D}

private theorem State.trace_push_castSucc (s : State C n g m) (op : ArithOp C)
    (args : Fin op.arity → Wire n s.size) (w : Wire n s.size) :
    (s.push op args).program.trace I x w.castSucc = s.program.trace I x w :=
  Program.trace_gate_castSucc _ _ _ _ _

private theorem State.represents_push {s : State C n g m} {v : Wire n g → R}
    {out : Fin m → R} (h : s.Represents constant x v out) (op : ArithOp C)
    (args : Fin op.arity → Wire n s.size) :
    (s.push op args).Represents constant x v out := by
  obtain ⟨hv, ho⟩ := h
  refine ⟨?_, ?_⟩
  · funext w
    exact (s.trace_push_castSucc op args _).trans (congrFun hv w)
  · funext k
    exact (s.trace_push_castSucc op args _).trans (congrFun ho k)

private theorem State.adjointSum_push (s : State C n g m) (op : ArithOp C)
    (args : Fin op.arity → Wire n s.size) (v : Wire n g → R) :
    (s.push op args).adjointSum constant x D v = s.adjointSum constant x D v := by
  unfold State.adjointSum
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (s.push op args).adjoint w = (s.adjoint w).castSucc from rfl,
    s.trace_push_castSucc]

private theorem State.trace_accumulate_castSucc (s : State C n g m) (w : Wire n g)
    (t : Wire n s.size) (u : Wire n s.size) :
    (s.accumulate w t).program.trace I x u.castSucc = s.program.trace I x u :=
  Program.trace_gate_castSucc _ _ _ _ _

private theorem State.represents_accumulate {s : State C n g m} {v : Wire n g → R}
    {out : Fin m → R} (h : s.Represents constant x v out) (w : Wire n g) (t : Wire n s.size) :
    (s.accumulate w t).Represents constant x v out := by
  obtain ⟨hv, ho⟩ := h
  refine ⟨?_, ?_⟩
  · funext u
    exact (s.trace_accumulate_castSucc w t _).trans (congrFun hv u)
  · funext k
    exact (s.trace_accumulate_castSucc w t _).trans (congrFun ho k)

private theorem State.trace_adjoint_accumulate (s : State C n g m) (w : Wire n g)
    (t : Wire n s.size) (u : Wire n g) :
    (s.accumulate w t).program.trace I x ((s.accumulate w t).adjoint u) =
      s.program.trace I x (s.adjoint u) + if u = w then s.program.trace I x t else 0 := by
  by_cases hu : u = w
  · subst hu
    simp only [State.accumulate, Function.update_self, ite_true]
    exact Program.trace_gate_last _ _ _ _
  · simp only [State.accumulate, Function.update_of_ne hu, Function.comp_apply, hu, ite_false,
      add_zero]
    exact Program.trace_gate_castSucc _ _ _ _ _

private theorem State.adjointSum_accumulate (s : State C n g m) (w : Wire n g)
    (t : Wire n s.size) (v : Wire n g → R) :
    (s.accumulate w t).adjointSum constant x D v =
      s.adjointSum constant x D v + s.program.trace I x t • D (v w) := by
  have h : ∀ u, (s.accumulate w t).program.trace I x ((s.accumulate w t).adjoint u) • D (v u) =
      s.program.trace I x (s.adjoint u) • D (v u) +
        if u = w then s.program.trace I x t • D (v w) else 0 := by
    intro u
    rw [State.trace_adjoint_accumulate, add_smul, ite_smul, zero_smul]
    by_cases hu : u = w
    · subst hu; rfl
    · rw [ite_eq_right hu, ite_eq_right hu]
  rw [State.adjointSum, Finset.sum_congr rfl fun u _ => h u, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ w, ite_eq_left (Finset.mem_univ w)]
  rfl

private theorem sum_wire_succ {N : Type*} [AddCommMonoid N] (f : Wire n (g + 1) → N) :
    ∑ w, f w = ∑ w : Wire n g, f w.castSucc + f (.gate (Fin.last g)) := by
  rw [← (Wire.equiv n (g + 1)).symm.sum_comp, ← (Wire.equiv n g).symm.sum_comp,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc, add_assoc]
  rfl

private theorem sum_wire_zero {N : Type*} [AddCommMonoid N] (f : Wire n 0 → N) :
    ∑ w, f w = ∑ i, f (.input i) := by
  rw [← (Wire.equiv n 0).symm.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_zero, add_zero]
  rfl

private theorem State.adjointSum_restrict (s : State C n (g + 1) m) (v : Wire n (g + 1) → R) :
    s.adjointSum constant x D v =
      s.restrict.adjointSum constant x D (v ∘ Wire.castSucc) +
        s.program.trace I x (s.adjoint (.gate (Fin.last g))) • D (v (.gate (Fin.last g))) := by
  unfold State.adjointSum
  rw [sum_wire_succ]
  rfl

private theorem State.represents_restrict {s : State C n (g + 1) m} {v : Wire n (g + 1) → R}
    {out : Fin m → R} (h : s.Represents constant x v out) :
    s.restrict.Represents constant x (v ∘ Wire.castSucc) out :=
  ⟨by rw [← h.1]; rfl, h.2⟩

private theorem State.represents_step {s : State C n (g + 1) m} {v : Wire n (g + 1) → R}
    {out : Fin m → R} (h : s.Represents constant x v out) (op : ArithOp C)
    (wires : Fin op.arity → Wire n g) :
    (s.step op wires).Represents constant x (v ∘ Wire.castSucc) out := by
  have hr := State.represents_restrict h
  cases op with
  | add => exact State.represents_accumulate (State.represents_accumulate hr _ _) _ _
  | mul => exact State.represents_accumulate (State.represents_push (State.represents_accumulate
      (State.represents_push hr _ _) _ _) _ _) _ _
  | const c => exact hr

private theorem State.adjointSum_step (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) (hconst : ∀ c, D (constant c) = 0)
    {s : State C n (g + 1) m} {v : Wire n (g + 1) → R} {out : Fin m → R}
    (h : s.Represents constant x v out) (op : ArithOp C) (wires : Fin op.arity → Wire n g)
    (hlast : v (.gate (Fin.last g)) = I op fun a => v (wires a).castSucc) :
    (s.step op wires).adjointSum constant x D (v ∘ Wire.castSucc) =
      s.adjointSum constant x D v := by
  rw [State.adjointSum_restrict, hlast]
  cases op with
  | add =>
    simp only [State.step]
    rw [State.adjointSum_accumulate, State.adjointSum_accumulate,
      State.trace_accumulate_castSucc]
    simp only [arithInterpretationWith, hadd, smul_add, Function.comp_apply]
    rw [add_assoc]
  | mul =>
    simp only [State.step]
    rw [State.adjointSum_accumulate, State.adjointSum_push, State.adjointSum_accumulate,
      State.adjointSum_push]
    have hval : ∀ w, s.program.trace I x (s.value w) = v w := fun w => congrFun h.1 w
    simp only [Program.trace_gate_last, Program.trace_gate_castSucc, arithInterpretationWith_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply, hval, hmul]
    rw [smul_add, mul_smul, mul_smul, add_assoc, add_comm (_ • _ • D (v (wires 0).castSucc))]
  | const c =>
    simp only [State.step, arithInterpretationWith, hconst, smul_zero, add_zero]

private theorem backward_represents : ∀ {g : ℕ} (p : Program (arithSignature C) n g)
    {s : State C n g m} {out : Fin m → R}, s.Represents constant x (p.trace I x) out →
    (backward p s).Represents constant x (Program.empty.trace I x) out
  | _, .empty, _, _, h => h
  | _, .gate p line, s, out, h => by
    refine backward_represents p ?_
    have h' := State.represents_step h line.op line.wires
    convert h' using 2
    funext w
    exact (Program.trace_gate_castSucc p line I x w).symm

private theorem backward_adjointSum (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) (hconst : ∀ c, D (constant c) = 0) :
    ∀ {g : ℕ} (p : Program (arithSignature C) n g) {s : State C n g m} {out : Fin m → R},
    s.Represents constant x (p.trace I x) out →
    (backward p s).adjointSum constant x D (Program.empty.trace I x) =
      s.adjointSum constant x D (p.trace I x)
  | _, .empty, _, _, _ => rfl
  | _, .gate p line, s, out, h => by
    have hv : (p.gate line).trace I x ∘ Wire.castSucc = p.trace I x := by
      funext w
      exact Program.trace_gate_castSucc p line I x w
    have hs := State.represents_step h line.op line.wires
    rw [hv] at hs
    refine (backward_adjointSum hadd hmul hconst p hs).trans ?_
    rw [← State.adjointSum_step hadd hmul hconst h line.op line.wires
      (by
        rw [Program.trace_gate_last]
        congr 1
        funext a
        exact (Program.trace_gate_castSucc p line I x _).symm), hv]

private theorem init_represents (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) :
    (init c j seed zero).Represents constant x (c.program.trace I x) (c.eval I x) := by
  refine ⟨?_, ?_⟩ <;> funext w <;>
    exact (Program.trace_gate_castSucc _ _ _ _ _).trans (Program.trace_gate_castSucc _ _ _ _ _)

private theorem init_adjointSum (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) (hzero : constant zero = 0) :
    (init c j seed zero).adjointSum constant x D (c.program.trace I x) =
      constant seed • D (c.eval I x j) := by
  have h : ∀ w, (init c j seed zero).program.trace I x ((init c j seed zero).adjoint w) •
      D (c.program.trace I x w) =
        if w = c.outputs j then constant seed • D (c.eval I x j) else 0 := by
    intro w
    by_cases hw : w = c.outputs j
    · subst hw
      simp only [init, ite_true]
      rw [Program.trace_gate_castSucc, Program.trace_gate_last]
      rfl
    · simp only [init, hw, ite_false]
      rw [Program.trace_gate_last]
      simp only [arithInterpretationWith_const, hzero, zero_smul]
  rw [State.adjointSum, Finset.sum_congr rfl fun w _ => h w, Finset.sum_ite_eq' Finset.univ,
    ite_eq_left (Finset.mem_univ _)]

end Semantics

section Cost

/-- The gates the backward pass emits for one forward gate, weighted by `cost`. -/
private def backwardCost (cost : ArithOp C → ℕ) : ArithOp C → ℕ
  | .add => 2 * cost .add
  | .mul => 2 * cost .mul + 2 * cost .add
  | .const _ => 0

private theorem State.cost_step (s : State C n (g + 1) m) (op : ArithOp C)
    (wires : Fin op.arity → Wire n g) (cost : ArithOp C → ℕ) :
    (s.step op wires).program.cost cost = s.program.cost cost + backwardCost cost op := by
  cases op with
  | add =>
    change s.program.cost cost + cost .add + cost .add = _
    simp only [backwardCost]
    omega
  | mul =>
    change s.program.cost cost + cost .mul + cost .add + cost .mul + cost .add = _
    simp only [backwardCost]
    omega
  | const c => rfl

private theorem cost_backward (cost : ArithOp C → ℕ) :
    ∀ {g : ℕ} (p : Program (arithSignature C) n g) (s : State C n g m),
    (backward p s).program.cost cost = s.program.cost cost + p.cost (backwardCost cost)
  | _, .empty, _ => rfl
  | _, .gate p line, s => by
    change (backward p (s.step line.op line.wires)).program.cost cost = _
    rw [cost_backward cost p, State.cost_step, Program.cost_gate]
    omega

private theorem cost_backwardCost {g : ℕ} (p : Program (arithSignature C) n g)
    (cost : ArithOp C → ℕ) :
    p.cost (backwardCost cost) =
      2 * cost .add * p.cost ArithOp.addCost +
        2 * (cost .mul + cost .add) * p.cost ArithOp.mulCost := by
  have h : ∀ op : ArithOp C, backwardCost cost op =
      2 * cost .add * op.addCost + 2 * (cost .mul + cost .add) * op.mulCost := by
    intro op
    cases op <;> simp only [backwardCost, ArithOp.addCost, ArithOp.mulCost] <;> ring
  simp only [Program.cost_eq_sum, h, Finset.sum_add_distrib, ← Finset.mul_sum]

end Cost

end ReverseMode

open ReverseMode

variable {m : ℕ}

/-- An arithmetic program has at most as many additions and multiplications together as gates. -/
theorem Program.cost_addCost_add_cost_mulCost_le {g : ℕ} (p : Program (arithSignature C) n g) :
    p.cost ArithOp.addCost + p.cost ArithOp.mulCost ≤ g := by
  have h : p.cost ArithOp.addCost + p.cost ArithOp.mulCost =
      p.cost fun op => op.addCost + op.mulCost := by
    simp only [Program.cost_eq_sum, Finset.sum_add_distrib]
  rw [h]
  refine (p.cost_le_mul (b := 1) fun op => ?_).trans_eq (one_mul g)
  cases op <;> simp [ArithOp.addCost, ArithOp.mulCost]

section Evaluation

variable {R : Type*} [CommSemiring R] (constant : C → R)

/-- Reverse-mode differentiation keeps the outputs of the original circuit. -/
theorem Circuit.eval_withGradient_castAdd (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) (x : Fin n → R) (k : Fin m) :
    (c.withGradient j seed zero).eval (arithInterpretationWith C constant) x (k.castAdd n) =
      c.eval (arithInterpretationWith C constant) x k := by
  have h := backward_represents (constant := constant) (x := x) c.program
    (init_represents (constant := constant) (x := x) c j seed zero)
  simp only [Circuit.eval, Circuit.withGradient, Function.comp_apply, Fin.append_left]
  exact congrFun h.2 k

/-- **Adjoints.** For every additive map `D` obeying the Leibniz rule and vanishing on the
constants, the new outputs of reverse-mode differentiation, weighted by `D` of the inputs, sum to
`seed` times `D` of output `j`. For `D` a partial derivative this identifies the new outputs with
the partial derivatives. -/
theorem Circuit.sum_eval_withGradient_natAdd {M : Type*} [AddCommMonoid M] [Module R M]
    (D : R → M) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) (hconst : ∀ c, D (constant c) = 0)
    (c : Circuit (arithSignature C) n m) (j : Fin m) (seed zero : C) (hzero : constant zero = 0)
    (x : Fin n → R) :
    ∑ i, (c.withGradient j seed zero).eval (arithInterpretationWith C constant) x
        (Fin.natAdd m i) • D (x i) =
      constant seed • D (c.eval (arithInterpretationWith C constant) x j) := by
  have h := backward_adjointSum (constant := constant) (x := x) hadd hmul hconst c.program
    (init_represents (constant := constant) (x := x) c j seed zero)
  rw [init_adjointSum (constant := constant) (x := x) (D := D) c j seed zero hzero,
    State.adjointSum, sum_wire_zero] at h
  rw [← h]
  simp only [Circuit.eval, Circuit.withGradient, Function.comp_apply, Fin.append_right]
  rfl

end Evaluation

section Cost

/-- The exact weighted cost of reverse-mode differentiation: the forward circuit, the two
constant gates, two additions per addition, and two multiplications and two additions per
multiplication. -/
theorem Circuit.cost_program_withGradient (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) (cost : ArithOp C → ℕ) :
    (c.withGradient j seed zero).program.cost cost =
      c.program.cost cost + cost (.const seed) + cost (.const zero) +
        2 * cost .add * c.program.cost ArithOp.addCost +
        2 * (cost .mul + cost .add) * c.program.cost ArithOp.mulCost := by
  change (backward c.program (init c j seed zero)).program.cost cost = _
  rw [cost_backward, cost_backwardCost]
  change c.program.cost cost + cost (.const seed) + cost (.const zero) + _ = _
  ring

/-- The exact size of reverse-mode differentiation. -/
theorem Circuit.size_withGradient (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) :
    (c.withGradient j seed zero).size =
      c.size + 2 + 2 * c.program.cost ArithOp.addCost + 4 * c.program.cost ArithOp.mulCost := by
  have h := c.cost_program_withGradient j seed zero fun _ => 1
  rw [Program.cost_const, Program.cost_const] at h
  omega

/-- Reverse-mode differentiation multiplies the size by at most five, plus two constant gates. -/
theorem Circuit.size_withGradient_le (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) : (c.withGradient j seed zero).size ≤ 5 * c.size + 2 := by
  have h := Program.cost_addCost_add_cost_mulCost_le c.program
  rw [c.size_withGradient]
  omega

/-- Reverse-mode differentiation exactly triples the number of multiplications. -/
theorem Circuit.mulCost_withGradient (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) :
    (c.withGradient j seed zero).program.cost ArithOp.mulCost =
      3 * c.program.cost ArithOp.mulCost := by
  rw [c.cost_program_withGradient]
  simp only [ArithOp.mulCost]
  omega

/-- The number of additions after reverse-mode differentiation. -/
theorem Circuit.addCost_withGradient (c : Circuit (arithSignature C) n m) (j : Fin m)
    (seed zero : C) :
    (c.withGradient j seed zero).program.cost ArithOp.addCost =
      3 * c.program.cost ArithOp.addCost + 2 * c.program.cost ArithOp.mulCost := by
  rw [c.cost_program_withGradient]
  simp only [ArithOp.addCost]
  omega

end Cost

section Polynomial

open MvPolynomial

variable {K : Type u} [CommSemiring K]

/-- Reverse-mode differentiation keeps the polynomials of the original circuit. -/
theorem Circuit.polynomial_withGradient_castAdd (c : Circuit (arithSignature K) n m)
    (j : Fin m) (seed zero : K) (k : Fin m) :
    (c.withGradient j seed zero).polynomial (k.castAdd n) = c.polynomial k :=
  c.eval_withGradient_castAdd MvPolynomial.C j seed zero X k

/-- **Correctness of reverse-mode differentiation.** Output `m + i` computes `seed` times the
partial derivative of output `j` along `X i`. -/
theorem Circuit.polynomial_withGradient_natAdd (c : Circuit (arithSignature K) n m) (j : Fin m)
    (seed : K) (i : Fin n) :
    (c.withGradient j seed 0).polynomial (Fin.natAdd m i) =
      MvPolynomial.C seed * pderiv i (c.polynomial j) := by
  classical
  have h := c.sum_eval_withGradient_natAdd MvPolynomial.C (pderiv i) (fun a b => map_add _ a b)
    (fun a b => Derivation.leibniz _ a b) (fun _ => pderiv_C) j seed 0 (map_zero MvPolynomial.C) X
  simpa [pderiv_X, Pi.single_apply, Circuit.polynomial] using h

/-- **The Baur–Strassen theorem** for arithmetic circuits [BaurStrassen1983]: if a circuit with
`s` gates computes `f` (as output `j`), then a circuit with at most `5 s + 2` gates and three
times the multiplications computes `f` and all its first partial derivatives. -/
theorem Circuit.exists_gradient (c : Circuit (arithSignature K) n m) (j : Fin m) :
    ∃ d : Circuit (arithSignature K) n (n + 1), d.size ≤ 5 * c.size + 2 ∧
      d.program.cost ArithOp.mulCost = 3 * c.program.cost ArithOp.mulCost ∧
      d.polynomial 0 = c.polynomial j ∧ ∀ i, d.polynomial i.succ = pderiv i (c.polynomial j) := by
  let e := c.withGradient j 1 0
  refine ⟨⟨e.program, Fin.cons (e.outputs (j.castAdd n)) fun i => e.outputs (Fin.natAdd m i)⟩,
    c.size_withGradient_le j 1 0, c.mulCost_withGradient j 1 0, ?_, fun i => ?_⟩
  · exact c.polynomial_withGradient_castAdd j 1 0 j
  · have h := c.polynomial_withGradient_natAdd j 1 i
    rw [map_one, one_mul] at h
    exact h

/-- **Lower-bound transfer for size.** If every circuit computing the gradient of `f` has at least
`S` gates, then every circuit computing `f` has at least `(S - 2) / 5` gates. -/
theorem Circuit.le_five_mul_size_add_two_of_gradient {f : MvPolynomial (Fin n) K} {S : ℕ}
    (hS : ∀ d : Circuit (arithSignature K) n n, (∀ i, d.polynomial i = pderiv i f) → S ≤ d.size)
    (c : Circuit (arithSignature K) n m) (j : Fin m) (hc : c.polynomial j = f) :
    S ≤ 5 * c.size + 2 := by
  obtain ⟨d, hsize, -, -, hd⟩ := c.exists_gradient j
  exact (hS ⟨d.program, d.outputs ∘ Fin.succ⟩ fun i => (hd i).trans (by rw [hc])).trans hsize

/-- **Lower-bound transfer for multiplications.** If every circuit computing the gradient of `f`
has at least `S` multiplications, then every circuit computing `f` has at least `S / 3`. -/
theorem Circuit.le_three_mul_mulCost_of_gradient {f : MvPolynomial (Fin n) K} {S : ℕ}
    (hS : ∀ d : Circuit (arithSignature K) n n, (∀ i, d.polynomial i = pderiv i f) →
      S ≤ d.program.cost ArithOp.mulCost)
    (c : Circuit (arithSignature K) n m) (j : Fin m) (hc : c.polynomial j = f) :
    S ≤ 3 * c.program.cost ArithOp.mulCost := by
  obtain ⟨d, -, hmul, -, hd⟩ := c.exists_gradient j
  exact (hS ⟨d.program, d.outputs ∘ Fin.succ⟩ fun i => (hd i).trans (by rw [hc])).trans_eq hmul

/-- **Power sums to power maps.** If `u * (d + 1) = 1` in `K`, a circuit with `s` gates computing
the power sum `∑ i, X i ^ (d + 1)` yields a circuit with at most `5 s + 2` gates and three times
the multiplications computing the power map `(X 0 ^ d, …, X (n - 1) ^ d)`. -/
theorem Circuit.exists_pow_of_psum {d : ℕ} {u : K} (hu : u * (d + 1) = 1)
    (c : Circuit (arithSignature K) n m) (j : Fin m)
    (hc : c.polynomial j = psum (Fin n) K (d + 1)) :
    ∃ e : Circuit (arithSignature K) n n, e.size ≤ 5 * c.size + 2 ∧
      e.program.cost ArithOp.mulCost = 3 * c.program.cost ArithOp.mulCost ∧
      ∀ i, e.polynomial i = X i ^ d := by
  let g := c.withGradient j u 0
  refine ⟨⟨g.program, fun i => g.outputs (Fin.natAdd m i)⟩, c.size_withGradient_le j u 0,
    c.mulCost_withGradient j u 0, fun i => ?_⟩
  have h := c.polynomial_withGradient_natAdd j u i
  rw [hc, pderiv_psum_succ, ← mul_assoc] at h
  refine h.trans ?_
  have hu' : MvPolynomial.C u * (d + 1 : MvPolynomial (Fin n) K) = 1 := by
    rw [show (d + 1 : MvPolynomial (Fin n) K) = MvPolynomial.C ((d : K) + 1) by
      rw [map_add, map_natCast, map_one], ← map_mul, hu, map_one]
  rw [hu', one_mul]

/-- **Lower-bound transfer for power sums.** If `d + 1` is invertible in `K` and every circuit
computing the power map `(X 0 ^ d, …, X (n - 1) ^ d)` has at least `S` multiplications, then every
circuit computing the power sum `∑ i, X i ^ (d + 1)` has at least `S / 3`. Strassen's degree bound
[Strassen1973] provides such an `S` of order `n log₂ d`; it is not formalized here. -/
theorem Circuit.le_three_mul_mulCost_of_psum {d : ℕ} {u : K} (hu : u * (d + 1) = 1) {S : ℕ}
    (hS : ∀ e : Circuit (arithSignature K) n n, (∀ i, e.polynomial i = X i ^ d) →
      S ≤ e.program.cost ArithOp.mulCost)
    (c : Circuit (arithSignature K) n m) (j : Fin m)
    (hc : c.polynomial j = psum (Fin n) K (d + 1)) :
    S ≤ 3 * c.program.cost ArithOp.mulCost := by
  obtain ⟨e, -, hmul, he⟩ := c.exists_pow_of_psum hu j hc
  exact (hS e he).trans_eq hmul

end Polynomial

end Cslib.Circuits
