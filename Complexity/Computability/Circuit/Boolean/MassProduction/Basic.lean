/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Replication
public import Complexity.Computability.Circuit.Boolean.NonconstantCost
public import Cslib.Computability.Circuit.Boolean.Complexity

/-!
# Boolean circuit mass production

Mass complexity is the minimum cost of evaluating a Boolean function on several independent
input blocks. Constants are free; NOT, AND and OR each cost one. The circuits and interpretation
are CSLib's, and the minimum is the existing weighted source complexity with raw inputs supplied.

The discrete exponential copy budget is `2 ^ (numerator * inputs / denominator)`, with natural
division implementing the floor. The bounding constant is chosen before the input length,
function and number of copies. These definitions state the eventual and every-positive-length
versions; the exponential-range theorem requires further constructions.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.massComplexity`: minimum cost of independent copies.
* `Cslib.Circuits.Boolean.MassProduction.rationalCopyBudget`: discrete copy budget
  `2 ^ (numerator * inputs / denominator)`.
* `Cslib.Circuits.Boolean.MassProduction.MassProductionBound`: the bound at one input length.
* `Cslib.Circuits.Boolean.MassProduction.MassProducesAt`,
  `Cslib.Circuits.Boolean.MassProduction.MassProducesAtAllLengths`: the eventual and all-length
  rational-rate statements.
* `Cslib.Circuits.Boolean.MassProduction.ExponentialMassProduction`: the all-length statement
  for every fixed nonnegative rational exponent below one.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.massComplexity_le_iff`: a finite budget has a circuit.
* `Cslib.Circuits.Boolean.MassProduction.massComplexity_mono`: monotonicity in the copy count.
* `Cslib.Circuits.Boolean.MassProduction.massComplexity_le_complexity`: comparison with size.
* `Cslib.Circuits.Boolean.MassProduction.massComplexity_le_replicate`: the naive upper bound.

## References

* Adapted from MassProduction/Statement.lean and MassProduction/DirectProduct.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

variable {n k : ℕ} {f : (Fin n → Bool) → Bool}

/-- Minimum cost of evaluating `f` on independent blocks, with constants free. -/
noncomputable def massComplexity (f : (Fin n → Bool) → Bool) (k : ℕ) : ℕ∞ :=
  ecomplexityFrom interpretation nonconstantCost (directProduct f k) id

/-- Every finite bound is witnessed by a circuit with that nonconstant-gate budget. -/
theorem massComplexity_le_iff {b : ℕ} : massComplexity f k ≤ b ↔
    ∃ c : Circuit signature (k * n) k, c.Computes interpretation (directProduct f k) ∧
      c.program.cost nonconstantCost ≤ b :=
  ecomplexityFrom_le_iff

/-- The Boolean basis implements every finite direct product, including at zero inputs. -/
theorem massComplexity_ne_top : massComplexity f k ≠ ⊤ :=
  ecomplexityFrom_ne_top_iff.mpr (Interpretation.IsComplete.exists_computes _)

/-- Some circuit attains the minimum cost. This is an existence theorem, not an efficient
algorithm for finding a minimum circuit. -/
theorem exists_computes_cost_eq_massComplexity :
    ∃ c : Circuit signature (k * n) k, c.Computes interpretation (directProduct f k) ∧
      (c.program.cost nonconstantCost : ℕ∞) = massComplexity f k :=
  exists_computesFrom_cost_eq_ecomplexityFrom (ecomplexityFrom_ne_top_iff.mp massComplexity_ne_top)

/-- Charging only nonconstant gates costs at most the minimum size, which counts every gate. -/
theorem massComplexity_le_complexity :
    massComplexity f k ≤ complexity interpretation (directProduct f k) := by
  obtain ⟨c, hc, hsize⟩ :=
    exists_computes_size_eq_complexity (I := interpretation) (f := directProduct f k)
  exact massComplexity_le_iff.mpr ⟨c, hc, (Program.cost_nonconstantCost_le _).trans hsize.le⟩

/-- Evaluating zero copies of `f` has mass complexity zero. -/
@[simp] theorem massComplexity_zero : massComplexity f 0 = 0 :=
  ecomplexityFrom_directProduct_zero

/-- Discarding copies cannot increase minimum cost, including discarding all copies. -/
theorem massComplexity_mono {small large : ℕ} (h : small ≤ large) :
    massComplexity f small ≤ massComplexity f large :=
  ecomplexityFrom_directProduct_mono h

/-- Naive independent replication costs at most the number of copies times one-copy cost. -/
theorem massComplexity_le_replicate (k : ℕ) :
    massComplexity f k ≤ (k : ℕ∞) * ecomplexityFrom interpretation nonconstantCost (single f) id :=
  ecomplexityFrom_directProduct_le k

/-- Rewiring every input block adds no cost. -/
theorem massComplexity_comp_wiring_le {p : ℕ} (select : Fin n → Fin p) (k : ℕ) :
    massComplexity (fun x => f (x ∘ select)) k ≤ massComplexity f k :=
  ecomplexityFrom_directProduct_comp_wiring_le select k

/-- The copy budget at rational exponent `numerator / denominator`, rounding down. -/
def rationalCopyBudget (numerator denominator inputs : ℕ) : ℕ :=
  2 ^ (numerator * inputs / denominator)

/-- `rationalCopyBudget` is monotone in the numerator. -/
theorem rationalCopyBudget_mono_numerator {small large denominator inputs : ℕ}
    (h : small ≤ large) :
    rationalCopyBudget small denominator inputs ≤ rationalCopyBudget large denominator inputs :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right (Nat.mul_le_mul_right inputs h))

/-- `rationalCopyBudget` is monotone in the input length. -/
theorem rationalCopyBudget_mono_inputs {numerator denominator small large : ℕ}
    (h : small ≤ large) :
    rationalCopyBudget numerator denominator small ≤
      rationalCopyBudget numerator denominator large :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right (Nat.mul_le_mul_left numerator h))

/-- The uniform bound at one input length, for every function and positive allowed copy count. -/
def MassProductionBound (numerator denominator constant inputs : ℕ) : Prop :=
  ∀ (f : (Fin inputs → Bool) → Bool) (copies : ℕ), 0 < copies →
    copies ≤ rationalCopyBudget numerator denominator inputs →
      massComplexity f copies ≤ (constant * (2 ^ inputs / inputs) : ℕ)

/-- Decreasing the allowed numerator preserves a bound at one input length. -/
theorem MassProductionBound.mono_numerator {small large denominator constant inputs : ℕ}
    (h : MassProductionBound large denominator constant inputs) (hle : small ≤ large) :
    MassProductionBound small denominator constant inputs :=
  fun f copies hc hb => h f copies hc (hb.trans (rationalCopyBudget_mono_numerator hle))

/-- Eventual mass production at a fixed rational exponent. The constant and cutoff may depend
on the exponent, but are uniform in input length, function and number of copies. -/
def MassProducesAt (numerator denominator : ℕ) : Prop :=
  ∃ constant cutoff : ℕ, ∀ inputs : ℕ, 0 < inputs → cutoff ≤ inputs →
    MassProductionBound numerator denominator constant inputs

/-- Mass production at every positive input length, with one constant for the fixed exponent. -/
def MassProducesAtAllLengths (numerator denominator : ℕ) : Prop :=
  ∃ constant : ℕ, ∀ inputs : ℕ, 0 < inputs →
    MassProductionBound numerator denominator constant inputs

/-- Every fixed nonnegative rational exponent below one has an all-length bound. -/
def ExponentialMassProduction : Prop :=
  ∀ numerator denominator : ℕ, 0 < denominator → numerator < denominator →
    MassProducesAtAllLengths numerator denominator

/-- An all-length bound holds eventually. -/
theorem MassProducesAtAllLengths.eventually {numerator denominator : ℕ}
    (h : MassProducesAtAllLengths numerator denominator) :
    MassProducesAt numerator denominator := by
  obtain ⟨constant, h⟩ := h
  exact ⟨constant, 0, fun inputs positive _ => h inputs positive⟩

/-- Decreasing the allowed numerator preserves eventual mass production. -/
theorem MassProducesAt.mono_numerator {small large denominator : ℕ}
    (h : MassProducesAt large denominator) (hle : small ≤ large) :
    MassProducesAt small denominator := by
  obtain ⟨constant, cutoff, h⟩ := h
  exact ⟨constant, cutoff, fun inputs hp hc => (h inputs hp hc).mono_numerator hle⟩

/-- Decreasing the allowed numerator preserves all-length mass production. -/
theorem MassProducesAtAllLengths.mono_numerator {small large denominator : ℕ}
    (h : MassProducesAtAllLengths large denominator) (hle : small ≤ large) :
    MassProducesAtAllLengths small denominator := by
  obtain ⟨constant, h⟩ := h
  exact ⟨constant, fun inputs hp => (h inputs hp).mono_numerator hle⟩

end Cslib.Circuits.Boolean.MassProduction
