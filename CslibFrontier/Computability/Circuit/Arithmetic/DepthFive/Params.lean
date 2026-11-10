/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Parameters of the depth-five rank measure

The lower bound for homogeneous depth-five circuits computing `IMM_{n,n}` uses a rank measure
with several integer parameters [OpenAI, (2.2)][OpenAI2026DepthFive]: the degree `n`, an excess
`s` near `√n`, the numbers `k = (n - s) / 2` and `m = (n + s) / 2` of matrix layers that are
differentiated and multiplied, and the degrees `a` and `b` of the slice on which the operator
acts. `Cslib.Circuits.DepthFive.Params` records these integers, and the derived quantities are
functions of it.

The proofs use the parameters only through finitely many inequalities, which hold for the
source's choice of `s`, `a` and `b` when `n` is large [OpenAI, Lemma 2.1][OpenAI2026DepthFive].
`Params.Good` collects exactly these inequalities with explicit constants. The rank bounds are
proved for every good parameter choice, and one module proves that the source's choice is
eventually good. Each field of `Params.Good` names the result that uses it.

## Main definitions

* `Cslib.Circuits.DepthFive.Params`: the integers `n`, `s`, `k`, `m`, `a`, `b`.
* `Params.v`, `Params.u`: the numbers of differentiated and multiplied variables.
* `Params.D`: the dimension of the slice of bidegree `(a, b)`.
* `Params.ρ`, `Params.lam`, `Params.α`, `Params.β`, `Params.q`: the ratios of the source.
* `Params.H`: the weight `H_e = ∑ i ≤ e, q ^ |i - lam * e|` of a factor of degree `e`.
* `Params.Good`: the inequalities between the parameters that the proofs use.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], (2.2) and Lemma 2.1 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive

/-- The integer parameters of the rank measure: `k` of the `n` matrix layers are differentiated
and the other `m = k + s` are multiplied, on the slice of bidegree `(a, b)`. -/
structure Params where
  /-- The number of matrix layers, their size, and the degree of the polynomial. -/
  n : ℕ
  /-- The excess of multiplied over differentiated layers. -/
  s : ℕ
  /-- The number of differentiated layers. -/
  k : ℕ
  /-- The number of multiplied layers. -/
  m : ℕ
  /-- The degree of the slice in the differentiated variables. -/
  a : ℕ
  /-- The degree of the slice in the multiplied variables. -/
  b : ℕ
  /-- The layers are split into differentiated and multiplied ones. -/
  hkm : k + m = n
  /-- The multiplied layers exceed the differentiated ones by `s`. -/
  hks : k + s = m

namespace Params

variable (p : Params)

/-- The number of differentiated variables. -/
def v : ℕ := p.k * p.n ^ 2

/-- The number of multiplied variables. -/
def u : ℕ := p.m * p.n ^ 2

/-- The dimension of the slice of bidegree `(a, b)`. -/
def D : ℕ := p.v.multichoose p.a * p.u.multichoose p.b

/-- The ratio `ρ = k / m` of differentiated to multiplied layers. -/
noncomputable def ρ : ℝ := p.k / p.m

/-- The slope `λ = k / n` of the source. -/
noncomputable def lam : ℝ := p.k / p.n

/-- The ratio `α = a / (a + v)`. -/
noncomputable def α : ℝ := p.a / (p.a + p.v)

/-- The ratio `β = b / (b + u)`. -/
noncomputable def β : ℝ := p.b / (p.b + p.u)

/-- The base `q = α ^ ((1 + ρ) / 2)` of the factor weights. -/
noncomputable def q : ℝ := p.α ^ ((1 + p.ρ) / 2)

/-- The weight `H_e = ∑ i ≤ e, q ^ |i - λ e|` of a factor of degree `e`. -/
noncomputable def H (e : ℕ) : ℝ := ∑ i ∈ Finset.range (e + 1), p.q ^ |(i : ℝ) - p.lam * e|

/-- The inequalities between the parameters that the rank bounds use. They hold for the source's
parameters when `n` is large [OpenAI, Lemma 2.1][OpenAI2026DepthFive]. -/
structure Good : Prop where
  /-- Positivity of the derived quantities. -/
  n_pos : 0 < p.n
  /-- Positivity of the derived quantities. -/
  k_pos : 0 < p.k
  /-- `s ≥ √n / 2`: the excess is of order `√n`. -/
  le_s : √(p.n : ℝ) / 2 ≤ p.s
  /-- `s ≤ √n`. -/
  s_le : (p.s : ℝ) ≤ √(p.n : ℝ)
  /-- `λ ≥ 3 / 8`. -/
  lam_ge : 3 / 8 ≤ p.lam
  /-- `a ≥ k`: the slice can be differentiated `k` times. -/
  k_le_a : p.k ≤ p.a
  /-- `4 n ≤ a`. -/
  four_n_le_a : 4 * p.n ≤ p.a
  /-- `4 n ≤ b`. -/
  four_n_le_b : 4 * p.n ≤ p.b
  /-- `α⁻¹ ≤ √n`. -/
  α_ge : (√(p.n : ℝ))⁻¹ ≤ p.α
  /-- `α ^ ρ ≤ β`. -/
  α_rpow_le_β : p.α ^ p.ρ ≤ p.β
  /-- `β ≤ α ^ ρ * exp (2 / b)`: the rounding error of `b`. -/
  β_le_α_rpow : p.β ≤ p.α ^ p.ρ * Real.exp (2 / p.b)
  /-- `β ≤ 2 / √n`. -/
  β_le : p.β ≤ 2 / √(p.n : ℝ)
  /-- `q ≤ 2 / √n`. -/
  q_le : p.q ≤ 2 / √(p.n : ℝ)
  /-- `q ≤ n ^ (-2 / 5)`. -/
  q_le_rpow : p.q ≤ (p.n : ℝ) ^ (-(2 : ℝ) / 5)
  /-- `q ≤ 1 / 2`. -/
  q_le_half : p.q ≤ 1 / 2

variable {p}

theorem Good.s_pos (hp : p.Good) : 0 < p.s := by
  have h : (0 : ℝ) < √(p.n : ℝ) / 2 := by
    have : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos
    positivity
  exact_mod_cast h.trans_le hp.le_s

theorem Good.m_pos (hp : p.Good) : 0 < p.m := by
  have := p.hks; have := hp.k_pos; omega

theorem Good.v_pos (hp : p.Good) : 0 < p.v :=
  Nat.mul_pos hp.k_pos (pow_pos hp.n_pos 2)

theorem Good.u_pos (hp : p.Good) : 0 < p.u :=
  Nat.mul_pos hp.m_pos (pow_pos hp.n_pos 2)

theorem Good.a_pos (hp : p.Good) : 0 < p.a := by
  have := hp.four_n_le_a; have := hp.n_pos; omega

theorem Good.b_pos (hp : p.Good) : 0 < p.b := by
  have := hp.four_n_le_b; have := hp.n_pos; omega

theorem Good.ρ_pos (hp : p.Good) : 0 < p.ρ := by
  have : (0 : ℝ) < p.k := by exact_mod_cast hp.k_pos
  have : (0 : ℝ) < p.m := by exact_mod_cast hp.m_pos
  exact div_pos ‹_› ‹_›

theorem Good.ρ_lt_one (hp : p.Good) : p.ρ < 1 := by
  have hm : (0 : ℝ) < p.m := by exact_mod_cast hp.m_pos
  rw [ρ, div_lt_one hm]
  exact_mod_cast (by have := p.hks; have := hp.s_pos; omega : p.k < p.m)

theorem Good.α_pos (hp : p.Good) : 0 < p.α := by
  have : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
  have : (0 : ℝ) < p.v := by exact_mod_cast hp.v_pos
  exact div_pos ‹_› (by positivity)

theorem Good.α_lt_one (hp : p.Good) : p.α < 1 := by
  have ha : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
  have hv : (0 : ℝ) < p.v := by exact_mod_cast hp.v_pos
  rw [α, div_lt_one (by positivity)]
  linarith

theorem Good.β_pos (hp : p.Good) : 0 < p.β := by
  have : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
  have : (0 : ℝ) < p.u := by exact_mod_cast hp.u_pos
  exact div_pos ‹_› (by positivity)

theorem Good.q_pos (hp : p.Good) : 0 < p.q :=
  Real.rpow_pos_of_pos hp.α_pos _

end Params

end Cslib.Circuits.DepthFive
