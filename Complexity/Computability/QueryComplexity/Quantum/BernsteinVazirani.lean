/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search
public import Complexity.Foundations.Quantum.HadamardTransform
import Complexity.Foundations.BooleanAnalysis.HadamardRectangles

/-!
# The Bernstein–Vazirani algorithm

**The Bernstein–Vazirani problem** [Bernstein, Vazirani][BernsteinVazirani1997], as stated in
[de Wolf, §2.4.2][deWolf2019]: the input `x ∈ {0,1}^N`, with `N = 2^n` query positions identified
with the bit strings `a ∈ {0,1}^n`, is the truth table `x_a = s ⬝ᵥ a` of a linear function for an
unknown `s ∈ {0,1}^n`; the goal is to find `s`.

Here the positions `Fin N` are identified with the bit strings `K → Bool` by an equivalence `e`,
and `Cslib.Quantum.linearTable e s` is the input. The algorithm
(`Cslib.Quantum.bernsteinVazirani`) starts in `|0, 1⟩` (`Cslib.Quantum.bernsteinVaziraniInit`),
applies the Hadamard transform to the query register, makes one phase query, which multiplies the
amplitude of `|a⟩` by `(-1)^{s ⬝ᵥ a}`, and applies the Hadamard transform again. **One query
recovers `s` exactly**: the final state is the basis state `|s, 1⟩`
(`Cslib.Quantum.run_bernsteinVazirani`), so measuring the query register gives `s` with
probability `1` (`Cslib.Quantum.regProb_run_bernsteinVazirani`).

Classically `n` queries are needed, since each answer is a single bit; that information-theoretic
lower bound is not formalized here. The exponential separation of
`Complexity/Computability/QueryComplexity/Quantum/Simon.lean` uses the same Hadamard transforms.

## Main definitions

* `Cslib.Quantum.linearTable`: the truth table of the linear function `a ↦ s ⬝ᵥ a`.
* `Cslib.Quantum.bernsteinVazirani`, `Cslib.Quantum.bernsteinVaziraniInit`: the algorithm and its
  initial state.

## Main results

* `Cslib.Quantum.run_bernsteinVazirani`: after one query the state is `|s, 1⟩`.
* `Cslib.Quantum.regProb_run_bernsteinVazirani`: measuring the query register gives `s` with
  certainty.

## References

* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.2
-/

public section

namespace Cslib.Quantum

open Finset BitString

variable {N : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

/-- The truth table of the linear function `a ↦ s ⬝ᵥ a`, with the query positions identified with
the bit strings by `e`. -/
@[expose] def linearTable (e : Fin N ≃ (K → Bool)) (s : K → Bool) : Fin N → Bool :=
  fun i => s ⬝ᵥ e i

/-- **The Bernstein–Vazirani algorithm**: the Hadamard transform on the query register, one query,
and the Hadamard transform again. -/
noncomputable def bernsteinVazirani (e : Fin N ≃ (K → Bool)) :
    ℕ → State N Unit →ₗᵢ[ℂ] State N Unit :=
  fun _ => hadamardTransform (e.prodCongr (Equiv.refl (Bool × Unit)))

/-- The initial state `|0, 1⟩` of the Bernstein–Vazirani algorithm: the query register holds the
zero string and the control bit is `1`. -/
noncomputable def bernsteinVaziraniInit (e : Fin N ≃ (K → Bool)) : State N Unit :=
  ket (e.symm 0, true, ())

private theorem ite_neg_one_one (b : Bool) :
    (if b then (-1 : ℂ) else 1) = ((signVal b : ℝ) : ℂ) := by
  cases b <;> simp

/-- **One query recovers `s`**: after one query on the truth table of `a ↦ s ⬝ᵥ a`, the
Bernstein–Vazirani algorithm is in the basis state `|s, 1⟩`. -/
theorem run_bernsteinVazirani (e : Fin N ≃ (K → Bool)) (s : K → Bool) :
    run (bernsteinVazirani e) (bernsteinVaziraniInit e) (linearTable e s) 1 =
      ket (e.symm s, true, ()) := by
  have h2 : (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) * ((2 ^ Fintype.card K : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
  ext ⟨i, b, u⟩
  simp only [run, bernsteinVazirani, bernsteinVaziraniInit, hadamardTransform_apply,
    phaseOracle_apply, ket_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm, Prod.map,
    Equiv.refl_apply, Equiv.refl_symm, Equiv.apply_symm_apply]
  cases b
  · simp
  · simp only [Bool.true_and, linearTable, Equiv.apply_symm_apply, ite_neg_one_one,
      Prod.mk.injEq, and_true, EmbeddingLike.apply_eq_iff_eq, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true, zero_dotProduct, Bool.zero_eq_false, signVal_false,
      Complex.ofReal_one]
    have key : ∑ x : K → Bool, ((signVal (x ⬝ᵥ e i) : ℝ) : ℂ) *
        (((signVal (s ⬝ᵥ x) : ℝ) : ℂ) * (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ)) =
        (((Real.sqrt (2 ^ Fintype.card K))⁻¹ : ℝ) : ℂ) *
          ((∑ x : K → Bool, signVal (e i ⬝ᵥ x) * signVal (s ⬝ᵥ x) : ℝ) : ℂ) := by
      push_cast
      rw [mul_sum]
      exact sum_congr rfl fun x _ => by rw [dotProduct_comm x (e i)]; ring
    rw [key, sum_signVal_dotProduct_mul_signVal_dotProduct]
    simp only [e.eq_symm_apply]
    split_ifs
    · rw [← mul_assoc, h2]
    · simp

/-- **Measuring the query register gives `s` with certainty.** -/
theorem regProb_run_bernsteinVazirani (e : Fin N ≃ (K → Bool)) (s : K → Bool) :
    regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) (linearTable e s) 1)
      (e.symm s) = 1 := by
  rw [run_bernsteinVazirani, regProb, measureProb_ket]
  simp

end Cslib.Quantum
