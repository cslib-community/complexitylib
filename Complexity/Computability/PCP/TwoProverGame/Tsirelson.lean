/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.TwoProverGame.CHSH
public import Complexity.Computability.PCP.TwoProverGame.Quantum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tsirelson's bound for the CHSH game

For a quantum strategy with binary answers, the *correlation* on questions `(x, y)` is the
expectation `⟨ψ|A_x ⊗ B_y|ψ⟩` of the observables `A_x = X_x^0 - X_x^1` and `B_y = Y_y^0 - Y_y^1`
(`Cslib.PCP.QuantumStrategy.correlation`), that is,
`Pr[a = b] - Pr[a ≠ b]` (`Cslib.PCP.QuantumStrategy.correlation_eq`). A strategy wins CHSH with
probability `1/2 + (E₀₀ + E₀₁ + E₁₀ - E₁₁)/8` (`Cslib.PCP.TwoProverGame.quantumWinProb_chsh`).

**Tsirelson's inequality** [Cirel'son][Cirelson1980] bounds the CHSH expression of the correlations
by `2√2` (`Cslib.PCP.QuantumStrategy.chsh_correlation_le`). The proof is the vector argument: with
`u_x = (A_x ⊗ 1)ψ` and `v_y = (1 ⊗ B_y)ψ`, the correlation is `Re ⟨u_x, v_y⟩`, every vector has
norm at most `1` because `A_x² ≤ 1` and `B_y² ≤ 1` for any two-outcome POVM, and
`Re⟨u₀, v₀ + v₁⟩ + Re⟨u₁, v₀ - v₁⟩ ≤ ‖v₀ + v₁‖ + ‖v₀ - v₁‖ ≤ 2√2` by Cauchy–Schwarz and the
parallelogram law (`Cslib.PCP.TwoProverGame.chsh_re_inner_le`). Hence every quantum strategy wins
CHSH with probability at most `1/2 + √2/4 = cos²(π/8)`
(`Cslib.PCP.TwoProverGame.quantumWinProb_chsh_le`, `Cslib.PCP.TwoProverGame.quantumValue_chsh_le`)
[Cleve, Høyer, Toner, Watrous, §3.1][CleveHoyerTonerWatrous2004].

The measurements are arbitrary POVMs, not only projective ones, and the dimensions are arbitrary
finite types. The model is the finite-dimensional tensor-product model with a pure shared state.

## Main definitions

* `Cslib.PCP.QuantumStrategy.correlation`: the correlation `⟨ψ|A_x ⊗ B_y|ψ⟩` of a strategy with
  binary answers.

## Main results

* `Cslib.PCP.TwoProverGame.quantumWinProb_chsh`: the CHSH winning probability in terms of the
  correlations.
* `Cslib.PCP.TwoProverGame.chsh_re_inner_le`: the CHSH inequality for vectors of norm at most `1`.
* `Cslib.PCP.QuantumStrategy.chsh_correlation_le`: Tsirelson's inequality.
* `Cslib.PCP.TwoProverGame.quantumValue_chsh_le`: the entangled value of CHSH is at most
  `cos²(π/8)`.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.PCP

open Matrix Quantum
open scoped Kronecker Real ComplexOrder

namespace QuantumStrategy

variable {X Y ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The **correlation** `⟨ψ|A_x ⊗ B_y|ψ⟩` of a strategy with binary answers on questions `(x, y)`,
where `A_x` and `B_y` are the observables `E_false - E_true` of the two measurements. -/
noncomputable def correlation (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) (y : Y) : ℝ :=
  (star S.state.ofLp ⬝ᵥ (((S.alice x).observable ⊗ₖ (S.bob y).observable) *ᵥ S.state.ofLp)).re

/-- The probability that a strategy with binary answers answers `(a, b)` on questions `(x, y)`. -/
noncomputable def prob (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) (y : Y) (a b : Bool) :
    ℝ :=
  (star S.state.ofLp ⬝ᵥ (((S.alice x).effect a ⊗ₖ (S.bob y).effect b) *ᵥ S.state.ofLp)).re

private theorem sub_kronecker' {l m n p : Type*} (A₁ A₂ : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact sub_mul _ _ _

private theorem kronecker_sub' {l m n p : Type*} (A : Matrix l m ℂ) (B₁ B₂ : Matrix n p ℂ) :
    A ⊗ₖ (B₁ - B₂) = A ⊗ₖ B₁ - A ⊗ₖ B₂ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact mul_sub _ _ _

/-- The correlation is `Pr[a = b] - Pr[a ≠ b]`. -/
theorem correlation_eq (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) (y : Y) :
    S.correlation x y = S.prob x y false false + S.prob x y true true - S.prob x y false true -
      S.prob x y true false := by
  simp only [correlation, prob, POVM.observable, sub_kronecker', kronecker_sub', sub_mulVec,
    dotProduct_sub, Complex.sub_re]
  ring

theorem sum_prob (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) (y : Y) :
    S.prob x y false false + S.prob x y true true + S.prob x y false true +
      S.prob x y true false = 1 := by
  have h := ((S.alice x).kronecker (S.bob y)).sum_prob S.state
  rw [S.norm_state, one_pow, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool] at h
  simp only [POVM.prob, POVM.kronecker] at h
  simp only [prob]
  linarith

/-- The correlation as an inner product `Re ⟨(A_x ⊗ 1)ψ, (1 ⊗ B_y)ψ⟩`. -/
private theorem correlation_eq_re_inner (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) (y : Y) :
    S.correlation x y = RCLike.re (inner ℂ
      (WithLp.toLp 2 (((S.alice x).observable ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (ι × κ))
      (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ (S.bob y).observable) *ᵥ S.state.ofLp))) := by
  have key : star (((S.alice x).observable ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ S.state.ofLp) ⬝ᵥ
      (((1 : Matrix ι ι ℂ) ⊗ₖ (S.bob y).observable) *ᵥ S.state.ofLp) =
      star S.state.ofLp ⬝ᵥ (((S.alice x).observable ⊗ₖ (S.bob y).observable) *ᵥ
        S.state.ofLp) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_kronecker,
      (S.alice x).isHermitian_observable.eq, conjTranspose_one, ← mul_kronecker_mul, mul_one,
      one_mul]
  rw [correlation, ← key, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, dotProduct_comm]
  rfl

private theorem norm_alice_le (S : QuantumStrategy X Y Bool Bool ι κ) (x : X) :
    ‖(WithLp.toLp 2 (((S.alice x).observable ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (ι × κ))‖ ≤ 1 := by
  refine (norm_toLp_mulVec_le_of_posSemidef ?_ S.state).trans_eq S.norm_state
  rw [conjTranspose_kronecker, (S.alice x).isHermitian_observable.eq, conjTranspose_one,
    ← mul_kronecker_mul, mul_one, ← one_kronecker_one, ← sub_kronecker']
  exact (S.alice x).posSemidef_one_sub_observable_mul_self.kronecker PosSemidef.one

private theorem norm_bob_le (S : QuantumStrategy X Y Bool Bool ι κ) (y : Y) :
    ‖(WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ (S.bob y).observable) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (ι × κ))‖ ≤ 1 := by
  refine (norm_toLp_mulVec_le_of_posSemidef ?_ S.state).trans_eq S.norm_state
  rw [conjTranspose_kronecker, (S.bob y).isHermitian_observable.eq, conjTranspose_one,
    ← mul_kronecker_mul, mul_one, ← one_kronecker_one, ← kronecker_sub']
  exact PosSemidef.one.kronecker (S.bob y).posSemidef_one_sub_observable_mul_self

end QuantumStrategy

namespace TwoProverGame

/-- The **CHSH inequality for vectors**: for vectors `u₀, u₁, v₀, v₁` of norm at most `1` in an
inner product space, `Re⟨u₀,v₀⟩ + Re⟨u₀,v₁⟩ + Re⟨u₁,v₀⟩ - Re⟨u₁,v₁⟩ ≤ 2√2`. -/
theorem chsh_re_inner_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {u₀ u₁ v₀ v₁ : E} (hu₀ : ‖u₀‖ ≤ 1) (hu₁ : ‖u₁‖ ≤ 1) (hv₀ : ‖v₀‖ ≤ 1) (hv₁ : ‖v₁‖ ≤ 1) :
    RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) + RCLike.re (inner 𝕜 u₁ v₀) -
      RCLike.re (inner 𝕜 u₁ v₁) ≤ 2 * √2 := by
  have h₀ : RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) ≤ ‖v₀ + v₁‖ := by
    rw [← map_add, ← inner_add_right]
    exact (re_inner_le_norm u₀ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₀)
  have h₁ : RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁) ≤ ‖v₀ - v₁‖ := by
    rw [← map_sub, ← inner_sub_right]
    exact (re_inner_le_norm u₁ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₁)
  have hpar := parallelogram_law_with_norm 𝕜 v₀ v₁
  have hv₀' : ‖v₀‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv₀
  have hv₁' : ‖v₁‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv₁
  have hs : (2 * √2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt zero_le_two]; norm_num
  have hab : ‖v₀ + v₁‖ + ‖v₀ - v₁‖ ≤ 2 * √2 := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [hs]
    nlinarith [sq_nonneg (‖v₀ + v₁‖ - ‖v₀ - v₁‖)]
  linarith

end TwoProverGame

namespace QuantumStrategy

variable {X Y ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Tsirelson's inequality** [Cirel'son][Cirelson1980]: the CHSH expression of the correlations
of any quantum strategy with binary answers is at most `2√2`. -/
theorem chsh_correlation_le (S : QuantumStrategy X Y Bool Bool ι κ) (x₀ x₁ : X) (y₀ y₁ : Y) :
    S.correlation x₀ y₀ + S.correlation x₀ y₁ + S.correlation x₁ y₀ - S.correlation x₁ y₁ ≤
      2 * √2 := by
  simp only [correlation_eq_re_inner]
  exact TwoProverGame.chsh_re_inner_le (S.norm_alice_le x₀) (S.norm_alice_le x₁)
    (S.norm_bob_le y₀) (S.norm_bob_le y₁)

end QuantumStrategy

namespace TwoProverGame

/-- The winning probability of a quantum strategy for CHSH in terms of its correlations. -/
theorem quantumWinProb_chsh {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : QuantumStrategy Bool Bool Bool Bool ι κ) :
    chsh.quantumWinProb S = 1 / 2 + (S.correlation false false + S.correlation false true +
      S.correlation true false - S.correlation true true) / 8 := by
  rw [quantumWinProb_eq_sum]
  simp only [chsh_questions_apply, Fintype.sum_bool]
  simp only [chsh, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false, Bool.and_true,
    Bool.and_false, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false]
  have h1 := S.correlation_eq false false
  have h2 := S.correlation_eq false true
  have h3 := S.correlation_eq true false
  have h4 := S.correlation_eq true true
  have h5 := S.sum_prob false false
  have h6 := S.sum_prob false true
  have h7 := S.sum_prob true false
  have h8 := S.sum_prob true true
  simp only [QuantumStrategy.prob] at h1 h2 h3 h4 h5 h6 h7 h8
  linarith

theorem cos_sq_pi_div_eight : Real.cos (π / 8) ^ 2 = 1 / 2 + √2 / 4 := by
  rw [Real.cos_pi_div_eight, div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **Tsirelson's bound**: every quantum strategy wins CHSH with probability at most `cos²(π/8)`. -/
theorem quantumWinProb_chsh_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (S : QuantumStrategy Bool Bool Bool Bool ι κ) :
    chsh.quantumWinProb S ≤ Real.cos (π / 8) ^ 2 := by
  rw [quantumWinProb_chsh, cos_sq_pi_div_eight]
  linarith [S.chsh_correlation_le false true false true]

/-- The entangled value of CHSH is at most `cos²(π/8)`. -/
theorem quantumValue_chsh_le : chsh.quantumValue ≤ Real.cos (π / 8) ^ 2 :=
  chsh.quantumValue_le (sq_nonneg _) fun S => quantumWinProb_chsh_le S

end TwoProverGame

end Cslib.PCP
