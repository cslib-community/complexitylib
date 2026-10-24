/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Smolensky.Gates
public import Complexity.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Pointwise

/-!
# Smolensky's approximation of circuits

A circuit of the AC⁰[p] basis of depth `d` agrees with a function of degree at most
`((p - 1) ℓ) ^ d` over any commutative ring `R` of characteristic `p`, such as `ZMod p` or a
finite field of order `p ^ k`, on all but `size · 2 ^ n / 2 ^ ℓ` inputs
(`exists_lowDegree_approx`) [Razborov1987], [Smolensky1987].

The circuit is evaluated on pairs: the true function computed by a wire, and its approximant
(`pairInterpretation`). An operation applied to pairs computes the true function of its arguments
and applies the gate approximator of `exists_gate_approx` chosen for these true arguments to their
approximants. So the approximants multiply degrees by `(p - 1) ℓ` per level of depth, and they are
exact at every input where no gate approximator errs on its true arguments, which leaves at most
`2 ^ n / 2 ^ ℓ` inputs per gate.

## Main definitions

* `Cslib.Circuits.Boolean.Smolensky.inputPair`: the inputs as pairs of a bit and its value in `R`.
* `Cslib.Circuits.Boolean.Smolensky.gateApprox`: the gate approximator chosen for an operation.
* `Cslib.Circuits.Boolean.Smolensky.pairInterpretation`: the interpretation on pairs of a true
  function and its approximant.
* `Cslib.Circuits.Boolean.Smolensky.errorSet`: the inputs on which the approximator of a gate errs.

## Main results

* `Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx`: Smolensky's approximation theorem.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString

variable {R : Type*} [CommRing R] {p : ℕ} {n ℓ : ℕ}

/-- The inputs as pairs: the input bit and its value in `R`. -/
def inputPair (i : Fin n) : (BitString n → Bool) × (BitString n → R) :=
  (fun x => x i, fun x => bitVal R (x i))

variable [DecidableEq R] [Fact p.Prime] [CharP R p]

variable (R p) in
/-- The gate approximator chosen by `exists_gate_approx` for an operation whose arguments depend on
the input as `u`. -/
noncomputable def gateApprox (hℓ : 1 ≤ ℓ) (op : Unbounded.extSignature.Op)
    (u : BitString n → Fin (Unbounded.extSignature.Arity op) → Bool) :
    (Fin (Unbounded.extSignature.Arity op) → R) → R :=
  Classical.choose (exists_gate_approx (R := R) (p := p) hℓ op u)

variable (R p) in
private theorem gateApprox_spec (hℓ : 1 ≤ ℓ) (op : Unbounded.extSignature.Op)
    (u : BitString n → Fin (Unbounded.extSignature.Arity op) → Bool) :
    (∀ (D : ℕ) (v : Fin (Unbounded.extSignature.Arity op) → BitString n → R),
      (∀ k, v k ∈ lowDegree R (Fin n) D) →
        (fun x => gateApprox R p hℓ op u fun k => v k x) ∈
          lowDegree R (Fin n) ((p - 1) * ℓ * D)) ∧
      #(univ.filter fun x => gateApprox R p hℓ op u (fun k => bitVal R (u x k)) ≠
          bitVal R (Unbounded.extInterpretation (modGate p) op (u x))) * 2 ^ ℓ ≤ 2 ^ n :=
  Classical.choose_spec (exists_gate_approx (R := R) (p := p) hℓ op u)

variable (R p) in
/-- The interpretation on pairs of a true function and its approximant. -/
noncomputable def pairInterpretation (hℓ : 1 ≤ ℓ) :
    Interpretation Unbounded.extSignature ((BitString n → Bool) × (BitString n → R)) :=
  fun op args => (fun x => Unbounded.extInterpretation (modGate p) op fun a => (args a).1 x,
    fun x => gateApprox R p hℓ op (fun x a => (args a).1 x) fun a => (args a).2 x)

variable {g : ℕ} (hℓ : 1 ≤ ℓ) (P : Program Unbounded.extSignature n g)

/-- The true functions of the pair evaluation are the gate functions of the program. -/
private theorem fst_trace_pair (w : Wire n g) (x : BitString n) :
    (P.trace (pairInterpretation R p hℓ) inputPair w).1 x =
      P.trace (Unbounded.extInterpretation (modGate p)) x w := by
  -- the first components form a homomorphism to the pointwise lift, then evaluate at `x`
  let h : Homomorphism (pairInterpretation R p hℓ)
      ((Unbounded.extInterpretation (modGate p)).pointwise (BitString n)) :=
    ⟨Prod.fst, fun _ _ => rfl⟩
  exact (congrFun (congrFun (P.map_trace h inputPair) w) x).trans
    (P.trace_pointwise_apply _ _ w x)

/-- The pair at a gate is its operation applied to the pairs at its wires. -/
private theorem trace_pair_gate (k : Fin g) :
    P.trace (pairInterpretation R p hℓ) inputPair (.gate k) =
      pairInterpretation R p hℓ (P.lines k).op fun a =>
        P.trace (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a) :=
  (P.lines_eval (pairInterpretation R p hℓ) inputPair k).symm

/-- **Degrees of the approximants**: at most `((p - 1) ℓ) ^ depth`. -/
theorem snd_trace_pair_mem (w : Wire n g) :
    (P.trace (pairInterpretation R p hℓ) inputPair w).2 ∈
      lowDegree R (Fin n) (((p - 1) * ℓ) ^ P.wireDepths w) := by
  have hp := (Fact.out : p.Prime).two_le
  have hbase : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine P.wire_induction (P := fun w => (P.trace (pairInterpretation R p hℓ) inputPair w).2 ∈
    lowDegree R (Fin n) (((p - 1) * ℓ) ^ P.wireDepths w)) (fun i => ?_) (fun k ih => ?_) w
  · simp only [Program.wireDepths_input, pow_zero]
    exact bitVal_mem_lowDegree i
  · rw [trace_pair_gate, Program.wireDepths_gateWire]
    have hpos := P.depths_pos k
    have hdeg := (gateApprox_spec R p hℓ (P.lines k).op (fun x a =>
      (P.trace (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a)).1 x)).1
      (((p - 1) * ℓ) ^ (P.depths k - 1)) _ fun a => lowDegree_mono
        (Nat.pow_le_pow_right hbase (by have := P.wireDepths_lines_lt k a; omega)) (ih a)
    rw [show P.depths k = (P.depths k - 1) + 1 by omega, pow_succ']
    exact hdeg

variable (R p) in
/-- The inputs on which the approximator chosen for gate `k` errs on its true arguments. -/
noncomputable def errorSet (k : Fin g) : Finset (BitString n) :=
  univ.filter fun x => gateApprox R p hℓ (P.lines k).op
      (fun x a => (P.trace (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a)).1 x)
      (fun a => bitVal R
        ((P.trace (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a)).1 x)) ≠
    bitVal R (Unbounded.extInterpretation (modGate p) (P.lines k).op
      (fun a => (P.trace (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a)).1 x))

private theorem card_errorSet_mul_le (k : Fin g) : #(errorSet R p hℓ P k) * 2 ^ ℓ ≤ 2 ^ n :=
  (gateApprox_spec R p hℓ (P.lines k).op _).2

/-- **Exactness of the approximants** where no gate approximator errs. -/
private theorem snd_trace_pair_eq {x : BitString n} (hx : ∀ k, x ∉ errorSet R p hℓ P k)
    (w : Wire n g) :
    (P.trace (pairInterpretation R p hℓ) inputPair w).2 x =
      bitVal R ((P.trace (pairInterpretation R p hℓ) inputPair w).1 x) := by
  refine P.wire_induction (P := fun w =>
    (P.trace (pairInterpretation R p hℓ) inputPair w).2 x =
    bitVal R ((P.trace (pairInterpretation R p hℓ) inputPair w).1 x)) (fun i => rfl)
    (fun k ih => ?_) w
  rw [trace_pair_gate]
  have := hx k
  simp only [errorSet, mem_filter, mem_univ, true_and, not_not] at this
  change gateApprox R p hℓ (P.lines k).op _ (fun a => (P.trace
    (pairInterpretation R p hℓ) inputPair ((P.lines k).wires a)).2 x) = _
  simp only [ih]
  exact this

/-- **Smolensky's approximation theorem.** A circuit of the AC⁰[p] basis of depth `d` agrees with a
function of degree at most `((p - 1) ℓ) ^ d` over a commutative ring `R` of characteristic `p` on
all but `size · 2 ^ n / 2 ^ ℓ` inputs, for every `ℓ ≥ 1`. -/
theorem exists_lowDegree_approx (hℓ : 1 ≤ ℓ) (C : Circuit Unbounded.extSignature n 1) :
    ∃ Q ∈ lowDegree R (Fin n) (((p - 1) * ℓ) ^ C.depth),
      #(univ.filter fun x =>
        Q x ≠ bitVal R (C.eval (Unbounded.extInterpretation (modGate p)) x 0)) *
        2 ^ ℓ ≤ C.size * 2 ^ n := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  have hbase : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨(C.program.trace (pairInterpretation R p hℓ) inputPair (C.outputs 0)).2,
    lowDegree_mono (Nat.pow_le_pow_right hbase (C.outputDepths_le_depth 0))
      (snd_trace_pair_mem hℓ C.program _), ?_⟩
  -- the inputs where the approximant errs are inputs where some gate approximator errs
  have hsub : (univ.filter fun x =>
      (C.program.trace (pairInterpretation R p hℓ) inputPair (C.outputs 0)).2 x ≠
        bitVal R (C.eval (Unbounded.extInterpretation (modGate p)) x 0)) ⊆
      univ.biUnion (errorSet R p hℓ C.program) := fun x hx => by
    rw [mem_filter] at hx
    by_contra hno
    simp only [mem_biUnion, mem_univ, true_and, not_exists] at hno
    exact hx.2 ((snd_trace_pair_eq hℓ C.program hno _).trans (by
      rw [fst_trace_pair]
      rfl))
  calc _ ≤ #(univ.biUnion (errorSet R p hℓ C.program)) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ k, #(errorSet R p hℓ C.program k)) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ ∑ _k : Fin C.size, 2 ^ n := by
        rw [sum_mul]
        exact sum_le_sum fun k _ => card_errorSet_mul_le hℓ C.program k
    _ = C.size * 2 ^ n := by simp

end Cslib.Circuits.Boolean.Smolensky
