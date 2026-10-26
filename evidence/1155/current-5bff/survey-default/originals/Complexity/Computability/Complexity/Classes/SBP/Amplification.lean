/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SBP
public import Complexity.Computability.Complexity.Classes.SharpP.Power
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Uniform gap amplification for SBP

The powering argument for multiplicative gap amplification in [Watson2012], Sections 1.1
and 3, works uniformly for polynomial-time unary repetition counts. A fixed dominating
length polynomial also handles any polynomially bounded requested exponent, even when
that request is not itself computable. The witness remains #P, and the positive threshold
remains polynomial-time with binary output. This is gap amplification, not an additive
error bound on a normalized acceptance probability.

## Main results

* `exists_SBP_gap_pow_polyTime`: a positive unary polynomial-time exponent gives a uniform gap.
* `exists_SBP_gap_pow_polyBounded`: a polynomially bounded requested exponent gives a uniform gap.

## References

* [T. Watson, *The Complexity of Estimating Min-Entropy*][Watson2012], Sections 1.1 and 3.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Uniform SBP gap strengthening by positive, polynomial-time unary powers. Both the #P
numerator and the positive binary-output threshold are raised to the same input-dependent power. -/
theorem exists_SBP_gap_pow_polyTime (hA : A ∈ SBP enc) {r : α → ℕ}
    (hr : ComputableInPolyTime r enc encUnary) (hpos : ∀ a, 0 < r a) :
    ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧
        (a ∉ A → 2 ^ r a * f a < k a) := by
  have hr := hr.tidy
  have this : ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableTidilyInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 ^ r a * f a < k a) := by
    obtain ⟨f, hf, k, hk, hkpos, h⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
    refine ⟨_, SharpP.pow_mem_polyTime hf (.of_tidy hr), fun a => k a ^ r a,
      hk.tidy.binary_pow' hr, fun a => pow_pos (hkpos a) _, fun a => ⟨?_, ?_⟩⟩
    · intro ha
      exact Nat.pow_le_pow_left ((h a).1 ha) (r a)
    · intro ha
      simpa only [mul_pow] using
        Nat.pow_lt_pow_left ((h a).2 ha) (Nat.ne_of_gt (hpos a))
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-- **Uniform SBP amplification.** One #P witness and one positive polynomial-time binary
threshold achieve gap `2 ^ r(a)` for every polynomially bounded requested exponent. The request
need not be computable: the proof uses a fixed length polynomial dominating it, plus one to
ensure positive repetition even when the request is zero. -/
theorem exists_SBP_gap_pow_polyBounded (hA : A ∈ SBP enc) (r : α → ℕ)
    (hr : PolyBounded (fun a => (enc a).length) r) :
    ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧
        (a ∉ A → 2 ^ r a * f a < k a) := by
  obtain ⟨c, d, hb⟩ := hr.exists_le
  let q : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d + 1
  have hq : ComputableInPolyTime (fun a => q.eval (enc a).length) enc encUnary := by
    fun_prop
  have hpos (a : α) : 0 < q.eval (enc a).length := by simp [q]
  obtain ⟨f, hf, k, hk, hkpos, h⟩ := exists_SBP_gap_pow_polyTime hA hq hpos
  refine ⟨f, hf, k, hk, hkpos, fun a => ⟨(h a).1, fun ha => ?_⟩⟩
  have hle : r a ≤ q.eval (enc a).length := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    exact (hb a).trans (Nat.le_succ _)
  exact (Nat.mul_le_mul_right (f a) (Nat.pow_le_pow_right (by decide) hle)).trans_lt ((h a).2 ha)

end Cslib.Complexity
