/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Midrijanis
public import CslibFrontier.Computability.QueryComplexity.Quantum.Polynomial
public import CslibFrontier.Computability.QueryComplexity.SpectralSensitivity
import CslibFrontier.Computability.QueryComplexity.Quantum.Progress
import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Spectral sensitivity bounds quantum queries, and `D(f) = O(Q(f)⁴)`

A `T`-query algorithm computing `f` with error `ε ≤ 1/2` gives
`(1 - 2√(ε(1-ε))) λ(f) ≤ 2T` (`Cslib.Quantum.one_sub_mul_spectralSensitivity_le`), where `λ(f)`
is the spectral sensitivity (`Cslib.BitString.spectralSensitivity`). With Huang's
`deg(f) ≤ λ(f)²` (`Cslib.QueryComplexity.degree_le_spectralSensitivity_sq`) this gives
`deg(f) ≤ 1296 T²` at error `1/3` (`Cslib.Quantum.degree_le_mul_sq`), and with Midrijanis's
`D(f) ≤ deg(f) bs(f)` and the polynomial method's `bs(f) ≤ 16 T²` it gives the theorem of
[Aaronson, Ben-David, Kothari, Rao, Tal][AaronsonBenDavidKothariRaoTal2021]:
a deterministic decision tree of depth at most `20736 T⁴ = (12 T)⁴` computes `f`
(`Cslib.Quantum.complexity_le_mul_pow_four`). This improves the `4096 T⁶` of
`Cslib.Quantum.complexity_le_mul_pow_six` once `T ≥ 3`.

**The adversary argument.** Let `ψₓᵗ` be the state after `t` queries on input `x`, and fix
nonnegative weights `u` and `w` on the cube. The progress measure sums
`u(x) w(x ⊕ eᵢ) |⟨ψₓᵗ, ψ_{x ⊕ eᵢ}ᵗ⟩|` over the sensitive edges `(x, i)` of `f`.
* Before any query all states are equal, so the measure is the form
  `⟨u, A_f w⟩ = ∑_x ∑_{i sensitive at x} u(x) w(x ⊕ eᵢ)`.
* The inputs `x` and `x ⊕ eᵢ` have oracles that differ only on query index `i` with control bit
  `1`, so one query changes their overlap by `2 ⟨Π_i ψₓ, Π_i ψ_{x ⊕ eᵢ}⟩`
  `2 ⟨Π_i ψ, Π_i φ⟩`. By applying `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le`
  (`CslibFrontier.Computability.QueryComplexity.Quantum.Progress`), `2ab ≤ a² + b²`, and
  `∑_i ‖Π_i ψ‖² ≤ 1`, counting each edge from both of its ends, a query lowers the measure by
  at most `‖u‖² + ‖w‖²`.
* At the end, inputs with different values of `f` have overlap at most `2√(ε(1-ε))`, because
  `|⟨ψ, φ⟩|² + (p - q)² ≤ 1` for unit states whose acceptance probabilities are `p` and `q`
  (`Cslib.Quantum.norm_inner_sq_add_sq_measureProb_sub_le_one`).

So `(1 - 2√(ε(1-ε))) ⟨u, A_f w⟩ ≤ T (‖u‖² + ‖w‖²)`
(`Cslib.Quantum.one_sub_mul_sum_sensitiveCoords_le`), and unit vectors bound `λ(f)` by
`Cslib.BitString.spectralSensitivity_le_of_forall_sum_le`.

**Source mapping** (numbering of arXiv:2010.12629v1). `complexity_le_mul_pow_four` is
Theorem 2, `D(f) = O(Q(f)⁴)`, proved as in the source (p. 2) from Midrijanis's inequality (4),
`bs(f) = O(Q(f)²)` and Theorem 3. `degree_le_mul_sq` is Theorem 3, `deg(f) = O(Q(f)²)`, from
Theorem 1 and Lemma 9. `one_sub_mul_spectralSensitivity_le` is the part `λ(f) = O(Q(f))` of
Lemma 9 (for total functions). The source proves Lemma 9 by taking the spectral adversary matrix
`Γ = A_f` and citing `Q(f) = Ω(SA(f))` [BSS03 in the source]; here the progress-measure argument
for this `Γ` is carried out directly in the query model of `Cslib.Quantum.run`, with weights from
two nonnegative unit vectors in place of a principal eigenvector. The constants `2`, `36`, `1296`
and `20736` are those of this proof; the source states only `O(·)` bounds. Like the polynomial
method, the bounds hold for each algorithm; there is no separate definition of quantum query
complexity.

## Main results

* `Cslib.Quantum.inner_phaseOracle_update_not`: one query changes the overlap of the states on
  neighboring inputs by `2 ⟨Π_i ψ, Π_i φ⟩`.
* `Cslib.Quantum.one_sub_mul_sum_sensitiveCoords_le`: the adversary bound for the sensitivity graph.
* `Cslib.Quantum.one_sub_mul_spectralSensitivity_le`: `(1 - 2√(ε(1-ε))) λ(f) ≤ 2T`.
* `Cslib.Quantum.spectralSensitivity_le_thirty_six_mul`: `λ(f) ≤ 36 T` at error `1/3`.
* `Cslib.Quantum.degree_le_mul_sq`: `deg(f) ≤ 1296 T²` at error `1/3`.
* `Cslib.Quantum.complexity_le_mul_pow_four`: `D(f) ≤ 20736 T⁴` at error `1/3`.

## References

* [S. Aaronson, S. Ben-David, R. Kothari, S. Rao, A. Tal, *Degree vs. approximate degree and
  quantum implications of Huang's sensitivity theorem*][AaronsonBenDavidKothariRaoTal2021]
* [G. Midrijanis, *Exact quantum query complexity for total Boolean functions*][Midrijanis2004]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
-/

public section

namespace Cslib.Quantum

open Finset Function BitString QueryComplexity

variable {N : ℕ} {W : Type*} [Fintype W]

/-- **One query on neighboring inputs**: the oracles of `x` and of `x ⊕ eᵢ` differ only on query
index `i` with control bit `1`, so applying them changes the overlap of two states by
`2 ⟨Π_i ψ, Π_i φ⟩`. -/
theorem inner_phaseOracle_update_not (x : Fin N → Bool) (i : Fin N) (ψ φ : State N W) :
    inner ℂ (phaseOracle x ψ) (phaseOracle (update x i (!x i)) φ) =
      inner ℂ ψ φ - 2 * inner ℂ (ctrlProj i ψ) (ctrlProj i φ) := by
  classical
  rw [inner_phaseOracle_phaseOracle]
  have h : univ.filter (fun j => x j ≠ update x i (!x i) j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst hj; cases hx : x j <;> simp [hx]
    · simp [hj]
  rw [h, sum_singleton]

/-- A query algorithm with a unit initial state and error `ε ≤ 1/2` leaves the states on inputs
with different values of `f` with overlap at most `2√(ε(1-ε))`. -/
theorem norm_inner_run_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) {x y : Fin N → Bool} (hxy : f x ≠ f y) :
    ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ 2 * √(ε * (1 - ε)) := by
  have hx := norm_run U ψ₀ x T ▸ hψ₀
  have hy := norm_run U ψ₀ y T ▸ hψ₀
  obtain ⟨hx₁, hx₂⟩ := abs_le.1 (h x)
  obtain ⟨hy₁, hy₂⟩ := abs_le.1 (h y)
  cases hfx : f x <;> cases hfy : f y <;> simp only [hfx, hfy, ne_eq, not_true_eq_false] at hxy
  · simp only [hfx, hfy, bitVal_false, bitVal_true, sub_zero] at hx₂ hy₁
    rw [← norm_inner_symm]
    exact norm_inner_le_two_mul_sqrt_of_measureProb hy hx (by linarith) hx₂ hε
  · simp only [hfx, hfy, bitVal_false, bitVal_true, sub_zero] at hx₁ hy₂
    exact norm_inner_le_two_mul_sqrt_of_measureProb hx hy (by linarith) hy₂ hε

/-- **The adversary bound for the sensitivity graph**: if a `T`-query algorithm with a unit
initial state accepts every input `x`, by an outcome in `S`, with probability within `ε ≤ 1/2` of
`f(x)`, then for all nonnegative weights `u` and `w` on the cube,
`(1 - 2√(ε(1-ε))) ⟨u, A_f w⟩ ≤ T (‖u‖² + ‖w‖²)`, where `A_f` is the adjacency matrix of the
sensitivity graph. -/
theorem one_sub_mul_sum_sensitiveCoords_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) {u w : BitString N → ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (1 - 2 * √(ε * (1 - ε))) * ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) ≤
      T * (∑ x, u x ^ 2 + ∑ x, w x ^ 2) := by
  classical
  set R := (univ : Finset (BitString N × BitString N)).filter fun p =>
    (sensitivityGraph f).Adj p.1 p.2
  have hadj : ∀ {x y : BitString N} {i : Fin N}, (sensitivityGraph f).Adj x y → x i ≠ y i →
      y = update x i (!x i) := by
    intro x y i hxy hne
    obtain ⟨j, -, rfl⟩ := sensitivityGraph_adj.1 hxy
    by_cases hji : j = i
    · subst hji; rfl
    · exact (hne (by simp [update_of_ne (Ne.symm hji)])).elim
  have hbound := one_sub_mul_sum_le_of_sq_le U hψ₀ T R (fun p => u p.1 * w p.2)
    (fun p hp => by
      obtain ⟨i, hi, hp2⟩ := sensitivityGraph_adj.1 (mem_filter.1 hp).2
      exact norm_inner_run_le U hψ₀ T S h hε (hp2 ▸ hi.symm))
    (fun p _ => u p.1 ^ 2) (fun p _ => w p.2 ^ 2) (fun x => u x ^ 2) (fun y => w y ^ 2)
    (fun p _ => mul_nonneg (hu _) (hw _)) (fun _ _ _ _ => sq_nonneg _) (fun _ _ _ _ => sq_nonneg _)
    (fun _ _ _ _ => by ring_nf; rfl) (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
    (fun x _ i => by
      refine (sum_le_sum_of_subset_of_nonneg (t := {(x, update x i (!x i))}) ?_
        fun _ _ _ => sq_nonneg _).trans_eq (by simp)
      intro p hp
      obtain ⟨hpR, hne, rfl⟩ := mem_filter.1 hp
      exact mem_singleton.2 (Prod.ext rfl (hadj (mem_filter.1 hpR).2 hne)))
    (fun y _ i => by
      refine (sum_le_sum_of_subset_of_nonneg (t := {(update y i (!y i), y)}) ?_
        fun _ _ _ => sq_nonneg _).trans_eq (by simp)
      intro p hp
      obtain ⟨hpR, hne, rfl⟩ := mem_filter.1 hp
      exact mem_singleton.2 (Prod.ext (hadj (mem_filter.1 hpR).2.symm hne.symm) rfl))
  have hsumR : ∑ p ∈ R, u p.1 * w p.2 =
      ∑ x, ∑ i ∈ sensitiveCoords f x, u x * w (update x i (!x i)) := by
    rw [sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_filter, show (univ.filter fun y => (sensitivityGraph f).Adj x y) =
        (sensitivityGraph f).neighborFinset x by ext; simp, neighborFinset_sensitivityGraph]
    exact sum_image fun i _ j _ hij => BitString.update_not_injective x hij
  rw [hsumR] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (add_le_add (sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _)
      (sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _)) (Nat.cast_nonneg _))

/-- **Spectral sensitivity bounds quantum queries**: if a `T`-query algorithm with a unit initial
state accepts every input `x`, by an outcome in `S`, with probability within `ε ≤ 1/2` of `f(x)`,
then `(1 - 2√(ε(1-ε))) λ(f) ≤ 2T` [AaronsonBenDavidKothariRaoTal2021], Lemma 9, with the
constant of this proof. -/
theorem one_sub_mul_spectralSensitivity_le {f : BooleanFunction N} {ε : ℝ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W)) (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * spectralSensitivity f ≤ 2 * T := by
  set c := 1 - 2 * √(ε * (1 - ε))
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h fun _ => false)
  have hc : 0 ≤ c := one_sub_two_mul_sqrt_nonneg ε
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_mul]
    positivity
  have hlam : spectralSensitivity f ≤ 2 * T / c := by
    refine spectralSensitivity_le_of_forall_sum_le (by positivity)
      fun u w hu hw hu1 hw1 => ?_
    have := one_sub_mul_sum_sensitiveCoords_le U hψ₀ T S h hε hu hw
    rw [hu1, hw1] at this
    rw [le_div_iff₀ hc0]
    linarith
  rwa [le_div_iff₀ hc0, mul_comm] at hlam

/-- **Spectral sensitivity bounds bounded-error quantum queries**: if a `T`-query algorithm with a
unit initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3` of
`f(x)`, then `λ(f) ≤ 36 T`. -/
theorem spectralSensitivity_le_thirty_six_mul {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    spectralSensitivity f ≤ 36 * T := by
  have := one_sub_mul_spectralSensitivity_le U hψ₀ T S h (by norm_num)
  -- `2√(2/9) ≤ 17/18`, since `8/9 = 288/324 ≤ 289/324`
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hlam := spectralSensitivity_nonneg f
  nlinarith

/-- **Degree is at most quadratic in bounded-error quantum queries**: if a `T`-query algorithm with
a unit initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3`
of `f(x)`, then `deg(f) ≤ 1296 T²` [AaronsonBenDavidKothariRaoTal2021], Theorem 3, with the
constant of this proof. -/
theorem degree_le_mul_sq {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    degree f ≤ 1296 * T ^ 2 := by
  have h₁ := degree_le_spectralSensitivity_sq f
  have h₂ := pow_le_pow_left₀ (spectralSensitivity_nonneg f)
    (spectralSensitivity_le_thirty_six_mul U hψ₀ T S h) 2
  have : (degree f : ℝ) ≤ 1296 * T ^ 2 := by nlinarith
  exact_mod_cast this

/-- **Deterministic simulation of bounded-error quantum queries with a quartic overhead**: if a
`T`-query algorithm with a unit initial state accepts every input `x`, by an outcome in `S`, with
probability within `1/3` of `f(x)`, then a deterministic decision tree of depth at most
`20736 T⁴ = (12 T)⁴` computes `f` [AaronsonBenDavidKothariRaoTal2021], Theorem 2, with the
constant of this proof. -/
theorem complexity_le_mul_pow_four {f : BooleanFunction N}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (f x)| ≤ 1 / 3) :
    DecisionTree.complexity f ≤ 20736 * T ^ 4 :=
  (DecisionTree.complexity_le_degree_mul_blockSensitivity f).trans
    ((Nat.mul_le_mul (degree_le_mul_sq U hψ₀ T S h)
      (blockSensitivity_le_sixteen_mul_sq U hψ₀ T S h)).trans_eq (by ring))

end Cslib.Quantum
