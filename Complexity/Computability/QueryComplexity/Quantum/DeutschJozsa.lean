/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.DeutschJozsa
public import Complexity.Computability.QueryComplexity.Quantum.BernsteinVazirani

/-!
# The Deutsch–Jozsa algorithm

**The Deutsch–Jozsa problem** [Deutsch, Jozsa][DeutschJozsa1992], as stated in
[de Wolf, §2.4.1][deWolf2019]: for `N = 2^n`, the input `x ∈ {0,1}^N`, with positions identified
with the bit strings `{0,1}^n` by an equivalence `e`, is promised to be constant or balanced. The
goal is to decide which.

**The algorithm.** Apply the Hadamard transform to the query register, make one phase query, apply
the Hadamard transform again, and measure whether the query register holds `0ⁿ`. This is the
circuit `Cslib.Quantum.bernsteinVazirani e` with initial state `Cslib.Quantum.bernsteinVaziraniInit
e`; de Wolf §2.4.2 notes that the Bernstein–Vazirani algorithm "is exactly the same as the
Deutsch-Jozsa algorithm". The circuit is reused here rather than redefined.

**Analysis.** After the query the amplitude of `|z, 1⟩` is `2^{-n} ∑_a (-1)^{x_a + a ⬝ z}`
(`Cslib.Quantum.run_bernsteinVazirani_apply`), the Walsh–Hadamard coefficient of `(-1)^x` at `z`.
At `z = 0ⁿ` it is `2^{-n} ∑_a (-1)^{x_a}`, so the query register holds `0ⁿ` with probability
`(2^{-n} ∑_i (-1)^{x_i})²` (`Cslib.Quantum.regProb_run_bernsteinVazirani_zero`). That is `1` on a
constant input and `0` on a balanced one (`Cslib.BitString.IsBalanced.sum_signVal_eq_zero`). So
**one query solves the problem with certainty**
(`Cslib.Quantum.deutschJozsa_regProb_eq_bitVal`). The original algorithm of Deutsch and Jozsa used
two queries. The one-query version, with a phase oracle, is due to Cleve, Ekert, Macchiavello and
Mosca [CleveEkertMacchiavelloMosca1998], as de Wolf §2.4.1 records.

**The separation.** Every deterministic decision tree solving the problem needs `2^{n-1} + 1`
queries (`Complexity/Computability/QueryComplexity/DeutschJozsa.lean`). The bound holds in the same
bit-query model on the same input. `Cslib.Quantum.deutschJozsa_separation` combines the two. The
separation is for exact computation only. The problem is easy for bounded-error randomized
algorithms (de Wolf §2.4.1): three random queries err with probability at most `1/4` on the
promise (`Complexity/Computability/QueryComplexity/Randomized/DeutschJozsa.lean`).

## Main results

* `Cslib.Quantum.regProb_run_bernsteinVazirani_zero`: the probability of measuring `0ⁿ`.
* `Cslib.Quantum.regProb_run_bernsteinVazirani_zero_of_const`,
  `Cslib.Quantum.regProb_run_bernsteinVazirani_zero_of_isBalanced`: probability `1` on constant
  inputs and `0` on balanced ones.
* `Cslib.Quantum.deutschJozsa_regProb_eq_bitVal`: one query decides the problem exactly.
* `Cslib.Quantum.deutschJozsa_separation`: one exact quantum query against `2^{n-1} + 1`
  deterministic queries.

## References

* [D. Deutsch, R. Jozsa, *Rapid solution of problems by quantum computation*][DeutschJozsa1992]
* [R. Cleve, A. Ekert, C. Macchiavello, M. Mosca, *Quantum algorithms
  revisited*][CleveEkertMacchiavelloMosca1998]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.1–§2.4.2
-/

public section

namespace Cslib.Quantum

open Finset BitString QueryComplexity

variable {N : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- The `N` positions are the `2^n` strings of `n` bits. -/
private theorem card_eq_two_pow (e : Fin N ≃ (K → Bool)) : N = 2 ^ Fintype.card K := by
  classical
  simpa using Fintype.card_congr e

/-- **The probability of measuring `0ⁿ`** after the Hadamard–query–Hadamard circuit on input `x`
is `(2^{-n} ∑_i (-1)^{x_i})²`. -/
theorem regProb_run_bernsteinVazirani_zero (e : Fin N ≃ (K → Bool)) (x : Fin N → Bool) :
    regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) x 1) (e.symm 0) =
      (((2 : ℝ) ^ Fintype.card K)⁻¹ * ∑ i, signVal (x i)) ^ 2 := by
  rw [regProb_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, Fintype.univ_unit, sum_singleton, mem_singleton,
    Bool.true_eq_false, not_false_eq_true, sum_insert, run_bernsteinVazirani_apply, ite_true,
    Bool.false_eq_true, ite_false, norm_zero, ne_eq, OfNat.ofNat_ne_zero, zero_pow, add_zero,
    Equiv.apply_symm_apply, dotProduct_zero, Bool.zero_eq_false, signVal_false, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 2
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

/-- On a **constant** input, the circuit measures `0ⁿ` with certainty. -/
theorem regProb_run_bernsteinVazirani_zero_of_const (e : Fin N ≃ (K → Bool)) (c : Bool) :
    regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) (fun _ => c) 1) (e.symm 0) =
      1 := by
  have hN : (N : ℝ) = 2 ^ Fintype.card K := by
    exact_mod_cast card_eq_two_pow e
  rw [regProb_run_bernsteinVazirani_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hN,
    inv_mul_cancel_left₀ (by positivity)]
  cases c <;> simp

/-- On a **balanced** input, the circuit never measures `0ⁿ`. -/
theorem regProb_run_bernsteinVazirani_zero_of_isBalanced (e : Fin N ≃ (K → Bool))
    {x : Fin N → Bool} (hx : IsBalanced x) :
    regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) x 1) (e.symm 0) = 0 := by
  rw [regProb_run_bernsteinVazirani_zero, hx.sum_signVal_eq_zero]
  simp

/-- **The Deutsch–Jozsa algorithm decides the problem with certainty using one query**
[Cleve, Ekert, Macchiavello, Mosca][CleveEkertMacchiavelloMosca1998]: for every total `F` that
solves the problem, on every constant or balanced input `x` the probability of measuring `0ⁿ`
after one query is exactly `F x`, read as `0` or `1`. -/
theorem deutschJozsa_regProb_eq_bitVal (e : Fin N ≃ (K → Bool)) {F : (Fin N → Bool) → Bool}
    (hF : SolvesDeutschJozsa F) {x : Fin N → Bool} (hx : (∃ c, x = fun _ => c) ∨ IsBalanced x) :
    regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) x 1) (e.symm 0) =
      bitVal ℝ (F x) := by
  rcases hx with ⟨c, rfl⟩ | hx
  · rw [regProb_run_bernsteinVazirani_zero_of_const, hF.const, bitVal_true]
  · rw [regProb_run_bernsteinVazirani_zero_of_isBalanced e hx, hF.balanced x hx, bitVal_false]

/-- **The exact quantum–deterministic separation for Deutsch–Jozsa**, in the bit-query model on
`N = 2^n` positions with `n ≥ 1`. From a unit initial state, one quantum query decides every
constant or balanced input with certainty. Every deterministic decision tree solving the problem
(as a total function `F` correct on the promise inputs) has depth at least `2^{n-1} + 1`. -/
theorem deutschJozsa_separation (e : Fin N ≃ (K → Bool)) (hK : 0 < Fintype.card K) :
    ‖bernsteinVaziraniInit e‖ = 1 ∧
    (∀ F : (Fin N → Bool) → Bool, SolvesDeutschJozsa F → ∀ x, (∃ c, x = fun _ => c) ∨ IsBalanced x →
      regProb (run (bernsteinVazirani e) (bernsteinVaziraniInit e) x 1) (e.symm 0) =
        bitVal ℝ (F x)) ∧
    ∀ F : (Fin N → Bool) → Bool, SolvesDeutschJozsa F →
      2 ^ (Fintype.card K - 1) + 1 ≤ DecisionTree.complexity F := by
  refine ⟨norm_bernsteinVaziraniInit e, fun F hF x hx => deutschJozsa_regProb_eq_bitVal e hF hx,
    fun F hF => complexity_ge_of_solvesDeutschJozsa ?_ hF⟩
  rw [Fintype.card_fin, card_eq_two_pow e, ← pow_succ', Nat.sub_add_cancel hK]

end Cslib.Quantum
