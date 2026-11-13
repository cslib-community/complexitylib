/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import Cslib.Computability.Circuit.Synthesis
import Mathlib.Data.Fin.VecNotation

/-!
# Synthesis over the arithmetic basis

Constants, sums and products can be synthesized over an arithmetic signature without importing
polynomial families, degree bounds or projections. The constant symbols have arbitrary type
`K` and are interpreted in a carrier `R` by a supplied map. The primitive rules need only
addition and multiplication on `R`; the finite-sum rule needs an additive commutative monoid.
There is no semiring assumption on `K`.

The declarations retain their names, statements and proofs from the VP module. VP publicly
imports this module, while value-level clients can import it directly.

## Main results

* `Cslib.Circuits.Synthesis.arith_const`: a constant costs one gate.
* `Cslib.Circuits.Synthesis.arith_add`: adding two available functions costs one gate.
* `Cslib.Circuits.Synthesis.arith_mul`: multiplying two available functions costs one gate.
* `Cslib.Circuits.Synthesis.arith_sum`: synthesize a finite sum from its summands and zero.
-/

public section

namespace Cslib.Circuits

universe u

variable {K : Type u} {n : ℕ}
variable {R : Type*} {constant : K → R} {s : Set ((Fin n → R) → R)} {f g : (Fin n → R) → R}

/-- A constant costs one gate. -/
theorem Synthesis.arith_const [Add R] [Mul R] (a : K) :
    Synthesis (arithInterpretationWith K constant) s {fun _ => constant a} 1 :=
  Synthesis.gate (σ := arithSignature K) (.const a) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- The sum of two available functions costs one gate. -/
theorem Synthesis.arith_add [Add R] [Mul R] (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (arithInterpretationWith K constant) s {fun x => f x + g x} 1 :=
  Synthesis.gate (σ := arithSignature K) .add ![f, g] fun i => by fin_cases i <;> assumption

/-- The product of two available functions costs one gate. -/
theorem Synthesis.arith_mul [Add R] [Mul R] (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (arithInterpretationWith K constant) s {fun x => f x * g x} 1 :=
  Synthesis.gate (σ := arithSignature K) .mul ![f, g] fun i => by fin_cases i <;> assumption

/-- A finite sum costs its summands and one addition each, when zero is available. -/
theorem Synthesis.arith_sum {ι : Type*} [AddCommMonoid R] [Mul R] (indices : Finset ι)
    (summand : ι → (Fin n → R) → R) (cost : ι → ℕ) (hzero : (fun _ => 0) ∈ s)
    (h : ∀ i ∈ indices, Synthesis (arithInterpretationWith K constant) s {summand i} (cost i)) :
    Synthesis (arithInterpretationWith K constant) s {fun x => ∑ i ∈ indices, summand i x}
      (∑ i ∈ indices, (cost i + 1)) := by
  have := Synthesis.finset_fold (· + ·) 1 (fun f g => Synthesis.arith_add (Set.mem_insert f {g})
    (Set.mem_insert_of_mem f rfl)) indices (Synthesis.of_mem hzero) h
  simpa only [Finset.sum_eq_fold, Nat.add_zero] using this

end Cslib.Circuits
