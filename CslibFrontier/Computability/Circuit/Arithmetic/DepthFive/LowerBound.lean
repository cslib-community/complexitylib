/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Asymptotics
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.CircuitRank
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.ImmRank
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.WordSum

/-!
# A lower bound for homogeneous depth-five circuits computing `IMM`

Over a field of characteristic zero, a syntactically homogeneous `ΣΠΣΠΣ` circuit computing the
iterated matrix multiplication polynomial `IMM_{n,n}` has at least `n ^ (√n / 400)` gates, for
every good choice of the parameters of the rank measure and every `n ≥ exp 29200`. This compares
the two bounds on the measure `R` for the balanced layer schedule:

`D * exp (-13 * √n) ≤ R (IMM_{n,n}) ≤ 2 * S ^ 2 * D * exp (132 * √n) * n ^ (-√n / 100)`.

The lower bound is the rank bound for `IMM` and the upper bound is the rank bound for circuits of
size `S`. Cancelling the slice dimension `D > 0` gives
`n ^ (√n / 100) ≤ 2 * S ^ 2 * exp (145 * √n)`, and `2 * exp (145 * √n) ≤ n ^ (√n / 200)` once
`log n ≥ 29200`.

The size counts the lower product, middle sum and upper product gates of the normalized model
`Cslib.Circuits.DepthFive.Circuit`, which is at most the gate count of the source, so the bound
is slightly stronger than the source's.

## Main results

* `Cslib.Circuits.DepthFive.rpow_le_size_of_good`: the lower bound for good parameters.
* `Cslib.Circuits.DepthFive.rpow_le_size`: the lower bound for every `n ≥ exp 29200`.
* `Cslib.Circuits.DepthFive.exists_forall_rpow_le_size`: the lower bound for all sufficiently
  large `n`, with a threshold independent of the field.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §6 (unrefereed preprint)
-/

public section

open MvPolynomial Cslib.Circuits.Arithmetic

namespace Cslib.Circuits.DepthFive

variable {p : Params} [NeZero p.n]

/-- `IMM_{n,n}` is homogeneous of degree `n`. -/
theorem isHomogeneous_imm (K : Type*) [CommSemiring K] (n : ℕ) [NeZero n] :
    (imm K n n).IsHomogeneous n := by
  rw [imm_eq_sum_paths]
  refine IsHomogeneous.sum _ _ _ fun P _ => ?_
  simpa using IsHomogeneous.prod Finset.univ (fun t => (X (P.edge t) : MvPolynomial _ K))
    (fun _ => 1) fun t _ => isHomogeneous_X K _

/-- For good parameters and `n ≥ exp 29200`, every homogeneous depth-five circuit computing
`IMM_{n,n}` over a field of characteristic zero has size at least `n ^ (√n / 400)`. -/
theorem rpow_le_size_of_good (hp : p.Good) (hn : Real.exp 29200 ≤ p.n) {K : Type*} [Field K]
    [CharZero K] (c : Circuit K (Fin p.n × Fin p.n × Fin p.n))
    (hc : c.polynomial = imm K p.n p.n) :
    (p.n : ℝ) ^ (√(p.n : ℝ) / 400) ≤ c.size := by
  classical
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos
  set x := √(p.n : ℝ) with hx
  have hx1 : 1 ≤ x := hp.one_le_sqrt
  have hD : (0 : ℝ) < p.D := by
    have h₁ : 0 < p.v.multichoose p.a :=
      Nat.multichoose_eq _ _ ▸ Nat.choose_pos (by have := hp.v_pos; omega)
    have h₂ : 0 < p.u.multichoose p.b :=
      Nat.multichoose_eq _ _ ▸ Nat.choose_pos (by have := hp.u_pos; omega)
    exact_mod_cast Nat.mul_pos h₁ h₂
  -- the two bounds on the measure
  have hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False :=
    fun t t' h ht ht' => by simp [p.not_isV_succ ht h] at ht'
  have hlow := rankMeasure_imm_ge hp p.card_isV hadj (Params.sum_wordWeight_le hp) K
  have hR : (0 : ℝ) < rankMeasure p.layerVar (p.k, p.m) (p.a, p.b) (imm K p.n p.n) :=
    (mul_pos hD (Real.exp_pos _)).trans_le hlow
  have himm : imm K p.n p.n ≠ 0 := fun h => by simp [h] at hR
  have hdeg : c.degree = p.n :=
    IsHomogeneous.inj_right (hc ▸ c.isHomogeneous_polynomial) (isHomogeneous_imm K p.n) himm
  have hup := rankMeasure_circuit_le (s := p.layerVar) hp
    (by rw [Fintype.card_subtype]; exact card_varV p.card_isV)
    (by rw [Fintype.card_subtype]; exact card_varU p.card_isV) c hdeg
  rw [hc, ← hx] at hup
  rw [← hx] at hlow
  -- cancel `D` and collect the exponentials
  set A := (p.n : ℝ) ^ (x / 100) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hn0 _
  have hinv : (p.n : ℝ) ^ (-x / 100) = A⁻¹ := by rw [hA, ← Real.rpow_neg hn0.le]; congr 1; ring
  have hmain : A ≤ 2 * c.upper * max (c.lower : ℝ) 1 * Real.exp (145 * x) := by
    have h := hlow.trans hup
    rw [hinv] at h
    have h' : p.D * (A * Real.exp (-(8 + 5) * x)) ≤
        p.D * (2 * c.upper * max (c.lower : ℝ) 1 * Real.exp (132 * x)) := by
      have := mul_le_mul_of_nonneg_right h hA0.le
      calc p.D * (A * Real.exp (-(8 + 5) * x)) = p.D * Real.exp (-(8 + 5) * x) * A := by ring
        _ ≤ 2 * c.upper * max (c.lower : ℝ) 1 * p.D * Real.exp (132 * x) * A⁻¹ * A := this
        _ = p.D * (2 * c.upper * max (c.lower : ℝ) 1 * Real.exp (132 * x)) := by
          rw [mul_assoc _ A⁻¹ A, inv_mul_cancel₀ hA0.ne']; ring
    have h'' := le_of_mul_le_mul_left h' hD
    have he : Real.exp (145 * x) = Real.exp (132 * x) * Real.exp ((8 + 5) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have he' : Real.exp (-(8 + 5) * x) * Real.exp ((8 + 5) * x) = 1 := by
      rw [← Real.exp_add, show -(8 + 5) * x + (8 + 5) * x = 0 by ring, Real.exp_zero]
    calc A = A * Real.exp (-(8 + 5) * x) * Real.exp ((8 + 5) * x) := by
          rw [mul_assoc, he', mul_one]
      _ ≤ 2 * c.upper * max (c.lower : ℝ) 1 * Real.exp (132 * x) * Real.exp ((8 + 5) * x) :=
          mul_le_mul_of_nonneg_right h'' (Real.exp_pos _).le
      _ = _ := by rw [he]; ring
  -- the gate counts are at most the size
  have hU : 0 < c.upper := by
    rcases Nat.eq_zero_or_pos c.upper with h | h
    · have hA' : A ≤ 0 := by simpa [h] using hmain
      exact absurd hA' (not_le.2 hA0)
    · exact h
  have hS1 : (c.upper : ℝ) ≤ c.size := by
    exact_mod_cast (by rw [Circuit.size]; omega : c.upper ≤ c.size)
  have hS2 : max (c.lower : ℝ) 1 ≤ c.size := by
    refine max_le ?_ ?_
    · exact_mod_cast (by rw [Circuit.size]; omega : c.lower ≤ c.size)
    · exact_mod_cast (by rw [Circuit.size]; omega : 1 ≤ c.size)
  have hS0 : (0 : ℝ) ≤ c.size := Nat.cast_nonneg _
  have hmain' : A ≤ 2 * Real.exp (145 * x) * (c.size : ℝ) ^ 2 := by
    refine hmain.trans ?_
    have : (c.upper : ℝ) * max (c.lower : ℝ) 1 ≤ (c.size : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul hS1 hS2 (le_max_of_le_right zero_le_one) hS0
    nlinarith [Real.exp_pos (145 * x)]
  -- absorb the exponential
  set B := (p.n : ℝ) ^ (x / 400) with hB
  have hB0 : 0 < B := Real.rpow_pos_of_pos hn0 _
  have hAB : A = B ^ 2 * B ^ 2 := by
    rw [← pow_add, hA, hB, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
  have hlog : 29200 ≤ Real.log (p.n : ℝ) := (Real.le_log_iff_exp_le hn0).2 hn
  have hexp : 2 * Real.exp (145 * x) ≤ B ^ 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp x :=
      (by linarith : (2 : ℝ) ≤ x + 1).trans (Real.add_one_le_exp x)
    calc 2 * Real.exp (145 * x) ≤ Real.exp x * Real.exp (145 * x) := by gcongr
      _ = Real.exp (146 * x) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (Real.log (p.n : ℝ) * (x / 400 * 2)) := by
          apply Real.exp_le_exp.2
          nlinarith
      _ = B ^ 2 := by
          rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.rpow_def_of_pos hn0]
          norm_num
  have hsq : B ^ 2 ≤ (c.size : ℝ) ^ 2 := by
    have h : B ^ 2 * B ^ 2 ≤ B ^ 2 * (c.size : ℝ) ^ 2 :=
      hAB ▸ hmain'.trans (mul_le_mul_of_nonneg_right hexp (sq_nonneg _))
    exact le_of_mul_le_mul_left h (pow_pos hB0 2)
  exact (sq_le_sq₀ hB0.le hS0).1 hsq

/-- **Homogeneous depth-five lower bound for `IMM`.** Over a field of characteristic zero, every
syntactically homogeneous `ΣΠΣΠΣ` circuit computing `IMM_{n,n}` has size at least
`n ^ (√n / 400)`, for every `n ≥ exp 29200`. -/
theorem rpow_le_size {n : ℕ} [NeZero n] (hn : Real.exp 29200 ≤ n) {K : Type*} [Field K]
    [CharZero K] (c : Circuit K (Fin n × Fin n × Fin n)) (hc : c.polynomial = imm K n n) :
    (n : ℝ) ^ (√(n : ℝ) / 400) ≤ c.size := by
  have h20 : 2 ^ 20 ≤ n := by
    have h : ((2 : ℝ) ^ 20) ≤ Real.exp 29200 := by
      have h₁ : Real.exp 29200 = Real.exp 1460 ^ 20 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h₁]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1460]) 20
    exact_mod_cast h.trans hn
  have : NeZero (paramsOf n).n := ‹NeZero n›
  exact rpow_le_size_of_good (p := paramsOf n) (good_paramsOf h20) hn c hc

/-- **Homogeneous depth-five lower bound for `IMM`**,
[OpenAI, Corollary 6.1][OpenAI2026DepthFive]: there is an absolute `n₀` such that, over every
field of characteristic zero and for every `n ≥ n₀`, every syntactically homogeneous `ΣΠΣΠΣ`
circuit computing `IMM_{n,n}` has size at least `n ^ (√n / 400)`. -/
theorem exists_forall_rpow_le_size :
    ∃ n₀ : ℕ, ∀ (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ c : Circuit K (Fin n × Fin n × Fin n), c.polynomial = imm K n n →
        (n : ℝ) ^ (√(n : ℝ) / 400) ≤ c.size :=
  ⟨⌈Real.exp 29200⌉₊, fun _ _ _ _ _ hn c hc =>
    rpow_le_size ((Nat.le_ceil _).trans (Nat.cast_le.2 hn)) c hc⟩

end Cslib.Circuits.DepthFive
