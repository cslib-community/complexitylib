/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Search
public import Complexity.Computability.QueryComplexity.NisanSzegedy
public import Complexity.Computability.QueryComplexity.Threshold

/-!
# Quantum query lower bounds by polynomials

The *polynomial method* of [Beals, Buhrman, Cleve, Mosca, de Wolf][BealsBuhrmanCleveMoscaDeWolf2001]
bounds the queries of a quantum algorithm below by the degree of a polynomial. In the query model
of `Cslib.Quantum.run`, each amplitude of the state after `t` queries is, as a function of the input
`x`, a complex function of degree at most `t` on the cube (`Cslib.Quantum.amplitude_mem_lowDegree`):
the oracle multiplies each amplitude by `1 - 2 b x_i`, of degree `1`, and the isometries between
queries take linear combinations of amplitudes, which keeps the degree. So the probability
`∑_{p ∈ S} |ψ_p|²` of measuring an outcome in a set `S` is a real function of degree at most `2T`
(`Cslib.Quantum.measureProb_run_mem_lowDegree`), the sum of the squares of the real and imaginary
parts of the amplitudes (`Cslib.BitString.re_mem_lowDegree`, `Cslib.BitString.im_mem_lowDegree`).

An algorithm that accepts each input `x` with probability within `ε` of `f(x)` thus gives an
`ε`-approximation of `f` of degree at most `2T`, so `adeg_ε(f) ≤ 2T`
(`Cslib.Quantum.approxDegree_le_two_mul`), and `deg(f) ≤ 2T` if it computes `f` exactly
(`Cslib.Quantum.degree_le_two_mul`). The Nisan–Szegedy argument
(`Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc`), applied to this
polynomial with values in `[0, 1]`, bounds the block sensitivity: `bs(f) ≤ 8 T²` for exact
algorithms and `bs(f) ≤ 16 T²` for error `1/3` (`Cslib.Quantum.blockSensitivity_le_eight_mul_sq`,
`Cslib.Quantum.blockSensitivity_le_sixteen_mul_sq`).
With `D(f) ≤ bs(f)³` a deterministic decision tree of depth at most `4096 T⁶` computes `f`
(`Cslib.Quantum.complexity_le_mul_pow_six`); the quartic bound `D(f) ≤ 20736 T⁴`, through spectral
sensitivity, is in `Complexity.Computability.QueryComplexity.Quantum.Adversary`. Since
`bs(OR_N) = N`, computing the disjunction of `N` bits with error `1/3` takes `T ≥ √N / 4` queries
(`Cslib.Quantum.card_le_sixteen_mul_sq_of_threshold_one_right`): the decision form of the search
lower bound, whose search form is the BBBV bound `Cslib.Quantum.card_sub_two_le`. Since
`deg(PARITY_N) = N`, computing the parity of `N` bits exactly takes `T ≥ N / 2` queries
(`Cslib.Quantum.card_le_two_mul_of_parity`).

**Source mapping** (numbering of arXiv:quant-ph/9802049v3). The source models a network as
unitaries `U₀, O, U₁, …, O, U_T` on `m` qubits, where the query `O` maps `|i, b, z⟩` to
`|i, b ⊕ x_i, z⟩`, followed by a measurement of the final state (§3.2). Here the isometries are
arbitrary, the workspace is any finite type, and the oracle is the controlled phase oracle, which
is the bit oracle conjugated by Hadamard gates on the control bit (`Cslib.Quantum.phaseOracle`).
Lemma 4.1 is `amplitude_mem_lowDegree`, and Lemma 4.2 is `measureProb_run_mem_lowDegree`, for an
arbitrary set of outcomes. Theorem 4.3 (`Q_E(f) ≥ deg(f)/2`) is `degree_le_two_mul` and
Theorem 4.8 (`Q_2(f) ≥ adeg(f)/2`) is `approxDegree_le_two_mul`, for an arbitrary error `ε`.
Theorem 4.13 (`Q_E(f) ≥ √(bs(f)/8)` and `Q_2(f) ≥ √(bs(f)/16)`) is
`blockSensitivity_le_eight_mul_sq` and `blockSensitivity_le_sixteen_mul_sq`, and Theorem 5.4
(`D(f) ≤ 4096 Q_2(f)⁶`) is `complexity_le_mul_pow_six`. The bound `√N / 4` for `OR_N` and the
bound `N / 2` for exact `PARITY_N` are stated in §6. Like the source, these bounds hold for each
algorithm; there is no separate definition of quantum query complexity.

## Main results

* `Cslib.Quantum.amplitude_mem_lowDegree`: after `t` queries the amplitudes have degree at most
  `t`.
* `Cslib.Quantum.measureProb_run_mem_lowDegree`: after `T` queries the probability of an outcome
  set has degree at most `2T`.
* `Cslib.Quantum.approxDegree_le_two_mul`, `Cslib.Quantum.degree_le_two_mul`: `adeg_ε(f) ≤ 2T`,
  and `deg(f) ≤ 2T` for exact algorithms.
* `Cslib.Quantum.blockSensitivity_le_eight_mul_sq`,
  `Cslib.Quantum.blockSensitivity_le_sixteen_mul_sq`: `bs(f) ≤ 8 T²` for exact algorithms and
  `bs(f) ≤ 16 T²` for error `1/3`.
* `Cslib.Quantum.complexity_le_mul_pow_six`: `D(f) ≤ 4096 T⁶` for error `1/3`.
* `Cslib.Quantum.card_le_sixteen_mul_sq_of_threshold_one_right`: computing `OR_N` with error `1/3`
  needs `N ≤ 16 T²`.
* `Cslib.Quantum.card_le_two_mul_of_parity`: computing `PARITY_N` exactly needs `N ≤ 2T`.

## References

* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
-/

public section

namespace Cslib

namespace BitString

variable {ι : Type*} {D : ℕ}

/-- The monomials over `ℂ` are the monomials over `ℝ`, which take the values `0` and `1`. -/
private theorem monomial_complex (S : Finset ι) (x : ι → Bool) :
    monomial ℂ S x = (monomial ℝ S x : ℂ) := by
  rw [monomial_apply, monomial_apply]
  split_ifs <;> simp

/-- The real and imaginary parts of a complex function of degree at most `D` on the cube have
degree at most `D`. -/
private theorem re_im_mem_lowDegree {f : (ι → Bool) → ℂ} (hf : f ∈ lowDegree ℂ ι D) :
    (fun x => (f x).re) ∈ lowDegree ℝ ι D ∧ (fun x => (f x).im) ∈ lowDegree ℝ ι D := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, hS, rfl⟩ := hg
    simp only [monomial_complex, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨monomial_mem_lowDegree hS, const_mem_lowDegree D 0⟩
  | zero => exact ⟨const_mem_lowDegree D 0, const_mem_lowDegree D 0⟩
  | add g h _ _ hg hh =>
    simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
    exact ⟨Submodule.add_mem _ hg.1 hh.1, Submodule.add_mem _ hg.2 hh.2⟩
  | smul c g _ hg =>
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im]
    exact ⟨Submodule.sub_mem _ (Submodule.smul_mem _ c.re hg.1) (Submodule.smul_mem _ c.im hg.2),
      Submodule.add_mem _ (Submodule.smul_mem _ c.re hg.2) (Submodule.smul_mem _ c.im hg.1)⟩

/-- The real part of a complex function of degree at most `D` on the cube has degree at most
`D`. -/
theorem re_mem_lowDegree {f : (ι → Bool) → ℂ} (hf : f ∈ lowDegree ℂ ι D) :
    (fun x => (f x).re) ∈ lowDegree ℝ ι D :=
  (re_im_mem_lowDegree hf).1

/-- The imaginary part of a complex function of degree at most `D` on the cube has degree at most
`D`. -/
theorem im_mem_lowDegree {f : (ι → Bool) → ℂ} (hf : f ∈ lowDegree ℂ ι D) :
    (fun x => (f x).im) ∈ lowDegree ℝ ι D :=
  (re_im_mem_lowDegree hf).2

end BitString

namespace Quantum

open Finset BitString QueryComplexity

variable {N : ℕ} {W : Type*} [Fintype W]

/-- A linear map of a finite-dimensional Euclidean space takes each coordinate to a linear
combination of the coordinates of its argument. -/
private theorem linearMap_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (ψ : EuclideanSpace ℂ ι) (p : ι) :
    (L ψ).ofLp p = ∑ q, (L (EuclideanSpace.single q 1)).ofLp p * ψ.ofLp q := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr ψ]
  simp [map_sum, map_smul, mul_comm]

/-- **The amplitudes after `t` queries are polynomials of degree at most `t`**
[Beals, Buhrman, Cleve, Mosca, de Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: for every basis state
`p`, the amplitude of `p` after `t` queries is, as a function of the input, a complex function of
degree at most `t` on the cube. -/
theorem amplitude_mem_lowDegree (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (t : ℕ)
    (p : Fin N × Bool × W) :
    (fun x => (run U ψ₀ x t).ofLp p) ∈ lowDegree ℂ (Fin N) t := by
  classical
  induction t generalizing p with
  | zero => exact const_mem_lowDegree (R := ℂ) (ι := Fin N) 0 ((U 0 ψ₀).ofLp p)
  | succ t ih =>
    have h : (fun x => (run U ψ₀ x (t + 1)).ofLp p) = ∑ q, fun x =>
        (U (t + 1) (EuclideanSpace.single q 1)).ofLp p *
          ((if q.2.1 && x q.1 then -1 else 1) * (run U ψ₀ x t).ofLp q) := by
      funext x
      have := linearMap_apply_eq_sum (U (t + 1)).toLinearMap (phaseOracle x (run U ψ₀ x t)) p
      simp only [LinearIsometry.coe_toLinearMap] at this
      simp only [run, Finset.sum_apply, this, phaseOracle_apply]
    rw [h]
    refine sum_mem_lowDegree _ fun q _ => ?_
    obtain ⟨i, b, w⟩ := q
    have hfac : (fun x : Fin N → Bool => (if b && x i then -1 else 1 : ℂ)) ∈
        lowDegree ℂ (Fin N) 1 := by
      cases b
      · simpa using const_mem_lowDegree (R := ℂ) (ι := Fin N) 1 1
      · convert Submodule.sub_mem _ (one_mem_lowDegree (R := ℂ) (ι := Fin N) 1)
          (Submodule.smul_mem _ (2 : ℂ) (bitVal_mem_lowDegree (R := ℂ) i)) using 1
        funext x
        cases hx : x i <;> norm_num [bitVal, hx]
    have := Submodule.smul_mem _ ((U (t + 1) (EuclideanSpace.single (i, b, w) 1)).ofLp p)
      (mul_mem_lowDegree hfac (ih (i, b, w)))
    rw [Nat.add_comm 1 t] at this
    exact this

/-- **The acceptance probability after `T` queries is a polynomial of degree at most `2T`**
[Beals, Buhrman, Cleve, Mosca, de Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: for every set `S` of
outcomes, the probability that measuring the state after `T` queries gives an outcome in `S` is, as
a function of the input, a real function of degree at most `2T` on the cube. -/
theorem measureProb_run_mem_lowDegree (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W)
    (T : ℕ) (S : Finset (Fin N × Bool × W)) :
    (fun x => measureProb (run U ψ₀ x T) S) ∈ lowDegree ℝ (Fin N) (2 * T) := by
  have h : (fun x => measureProb (run U ψ₀ x T) S) = ∑ p ∈ S,
      ((fun x => ((run U ψ₀ x T).ofLp p).re) ^ 2 + (fun x => ((run U ψ₀ x T).ofLp p).im) ^ 2) := by
    funext x
    simp only [measureProb, Finset.sum_apply, Pi.add_apply, Pi.pow_apply, Complex.sq_norm,
      Complex.normSq_apply]
    refine sum_congr rfl fun p _ => ?_
    ring
  rw [h]
  exact sum_mem_lowDegree _ fun p _ => Submodule.add_mem _
    (pow_mem_lowDegree (re_mem_lowDegree (amplitude_mem_lowDegree U ψ₀ T p)) 2)
    (pow_mem_lowDegree (im_mem_lowDegree (amplitude_mem_lowDegree U ψ₀ T p)) 2)

/-- For a unit initial state, the probability of an outcome set lies in `[0, 1]`. -/
private theorem measureProb_run_mem_Icc (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) (x : Fin N → Bool) :
    measureProb (run U ψ₀ x T) S ∈ Set.Icc (-0 : ℝ) (1 + 0) := by
  refine ⟨by simpa using measureProb_nonneg _ S, ?_⟩
  have := measureProb_le_measureProb_univ (run U ψ₀ x T) S
  rw [measureProb_univ, norm_run, hψ₀] at this
  simpa using this

/-- **Approximate degree bounds quantum queries** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm accepts every input `x`, by an
outcome in `S`, with probability within `ε` of `f(x)`, then `adeg_ε(f) ≤ 2T`. -/
theorem approxDegree_le_two_mul {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε) :
    approxDegree ε f ≤ 2 * T :=
  approxDegree_le_of_mem_lowDegree (measureProb_run_mem_lowDegree U ψ₀ T S) h

/-- **Degree bounds exact quantum queries** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm accepts every input `x`, by an
outcome in `S`, with probability exactly `f(x)`, then `deg(f) ≤ 2T`. -/
theorem degree_le_two_mul {f : BooleanFunction N} (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    (ψ₀ : State N W) (T : ℕ) (S : Finset (Fin N × Bool × W))
    (h : ∀ x, measureProb (run U ψ₀ x T) S = bitVal ℝ (f x)) :
    degree f ≤ 2 * T := by
  have := approxDegree_le_two_mul (f := f) (ε := 0) U ψ₀ T S fun x => by simp [h x]
  rwa [approxDegree_zero] at this

/-- **Block sensitivity bounds exact quantum queries** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm accepts every input `x`, by an
outcome in `S`, with probability exactly `f(x)`, then `bs(f) ≤ 8 T²`. -/
theorem blockSensitivity_le_eight_mul_sq {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, measureProb (run U ψ₀ x T) S = bitVal ℝ (f x)) :
    blockSensitivity f ≤ 8 * T ^ 2 :=
  (blockSensitivity_le_two_mul_degree_sq f).trans <| by
    have := Nat.pow_le_pow_left (degree_le_two_mul U ψ₀ T S h) 2
    rw [mul_pow] at this
    omega

/-- **Block sensitivity bounds bounded-error quantum queries**: if a `T`-query algorithm with a unit
initial state accepts every input `x`, by an outcome in `S`, with probability within `ε < 1/2` of
`f(x)`, then `(1 - 2ε) bs(f) ≤ 8 (1 - ε) T²`. -/
theorem one_sub_two_mul_mul_blockSensitivity_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε < 1) :
    (1 - 2 * ε) * blockSensitivity f ≤ 8 * (1 - ε) * T ^ 2 := by
  have := one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc
    (measureProb_run_mem_lowDegree U ψ₀ T S) h (measureProb_run_mem_Icc U hψ₀ T S) hε
  push_cast at this
  linarith

/-- **Block sensitivity bounds bounded-error quantum queries** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm with a unit initial state accepts
every input `x`, by an outcome in `S`, with probability within `1/3` of `f(x)`, then
`bs(f) ≤ 16 T²`. -/
theorem blockSensitivity_le_sixteen_mul_sq {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    blockSensitivity f ≤ 16 * T ^ 2 := by
  have := Quantum.one_sub_two_mul_mul_blockSensitivity_le U hψ₀ T S h (by norm_num)
  have h' : (blockSensitivity f : ℝ) ≤ 16 * T ^ 2 := by linarith
  exact_mod_cast h'

/-- **Deterministic simulation of bounded-error quantum queries** [Beals, Buhrman, Cleve, Mosca,
de Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm with a unit initial state
accepts every input `x`, by an outcome in `S`, with probability within `1/3` of `f(x)`, then a
deterministic decision tree of depth at most `4096 T⁶` computes `f`. -/
theorem complexity_le_mul_pow_six {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    DecisionTree.complexity f ≤ 4096 * T ^ 6 :=
  (DecisionTree.complexity_le_blockSensitivity_pow_three f).trans
    ((Nat.pow_le_pow_left (blockSensitivity_le_sixteen_mul_sq U hψ₀ T S h) 3).trans_eq (by ring))

/-- **The search lower bound, decision form** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm with a unit initial state
computes the disjunction `OR_N` of its `N` input bits with error at most `1/3`, accepting every
input `x`, by an outcome in `S`, with probability within `1/3` of `OR_N(x)`, then `N ≤ 16 T²`. -/
theorem card_le_sixteen_mul_sq_of_threshold_one_right (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (threshold N 1 x)| ≤ 1 / 3) :
    N ≤ 16 * T ^ 2 :=
  blockSensitivity_threshold_one_right.symm.trans_le
    (blockSensitivity_le_sixteen_mul_sq U hψ₀ T S h)

/-- **Exact parity takes `N / 2` queries** [Beals, Buhrman, Cleve, Mosca, de
Wolf][BealsBuhrmanCleveMoscaDeWolf2001]: if a `T`-query algorithm accepts every input `x`, by an
outcome in `S`, with probability exactly the parity of `x`, then `N ≤ 2T`. -/
theorem card_le_two_mul_of_parity (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, measureProb (run U ψ₀ x T) S = bitVal ℝ (parity N x)) :
    N ≤ 2 * T :=
  degree_parity.symm.trans_le (degree_le_two_mul U ψ₀ T S h)

end Quantum

end Cslib
