/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Correlation.Asymptotics
public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian
public import Complexity.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exponentially small correlation with quadratic forms

Circuits of fan-in at most two over any basis on `Bool`, with at most `c n` gates of positive
arity, have correlation `2^{-Ω(n)}` with a nonconstructively chosen family of bilinear forms
`xᵀ R y` over `𝔽₂`, for every `c < c* = 1 + 1/(2A) ≈ 2.78125`. Here `A = 2p ≈ 0.2807` is the
Gaussian layout coefficient of the frontier method
(`Cslib.Circuits.Frontier.layoutBound_gaussian`), and
`c* = (1 + L)/2` for the coefficient `L = 1 + 1/A ≈ 4.5625` of the worst-case frontier lower bound
(`Cslib.Circuits.Frontier.circuitLowerBound_gaussian`). Correlation is measured in the terms of the
average-case frontier lower bound: `correlation S T = 2 · agreement S T - 1`
(`Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one`), so a correlation of absolute
value at most `ε` is an agreement of at most `1/2 + ε/2`. The circuit model and the gate count
(`Cslib.Circuits.Circuit.innerSize`) are those of `Cslib.Circuits.Frontier.AverageCaseBound`. The
best previously published average-case bounds for the full binary basis are `2.5 n`, for an
explicit affine extractor [Chen–Kabanets][ChenKabanets2015], and `2.6 n`, for non-explicit
quadratic extractors [Golovnev–Kulikov–Smal–Tamaki][GKST2016]. Because the family here is chosen
nonconstructively, the comparable bound is the non-explicit one; nothing here improves on the
explicit `2.5 n`.

## The argument

For a quadratic form `f` over `𝔽₂` and a cut `X` of the coordinates, Lindsey's lemma bounds the
signed sum of `(-1)^f` over every rectangle `R` for `X` by `√(|R| 2^{n - ρ(X)})`, where the cut
rank `ρ(X)` is the rank of the block of the polar matrix with rows `X` and columns `Xᶜ`
(`Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le`). Partition the inputs into
`K` rectangle classes for one cut on which the circuit is constant; Cauchy–Schwarz over the
classes gives `correlation² ≤ K · 2^{-ρ(X)}`
(`Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le`). Two partitions apply:

* if the circuit leaves the inputs `D` unread, its two output classes are rectangles for `D`;
* along a layout of the graph of the circuit, the inputs with a given output and a given state of
  the read-once branching program of its constraint network, at the layer where exactly `⌊n/2⌋`
  inputs have been read, form `2 · 2^w` rectangle classes for a layout of width `w`.

If every set of `⌊n/2⌋` coordinates has cut rank at least `⌊n/2⌋ - τ n`, balancing the two at
`θ n` unread inputs, with `θ = (1/2 - A (c - 1))/(1 + A)`, gives the rate `(c* - c)/(2L) - τ/2`
(`Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le`), and `(c* - c)/(2L)` for a
sublinear deficiency (`eventually_abs_correlation_quadForm_le_gaussian`).

## A nonconstructively chosen family

A matrix is submatrix-robust with deficiency `t` when every square block with `k` rows has rank at
least `k - t`. Counting spanning sets of columns shows that for `t = 2 ⌊√m⌋ + 1` such an `m × m`
matrix over `𝔽₂` exists (`Matrix.exists_submatrixRobust`). The family `hardForm n = xᵀ R y` uses a
fixed such matrix `R = robustMatrix ⌊n/2⌋` between the first `⌊n/2⌋` coordinates `x` and the next
`⌊n/2⌋` coordinates `y`. The matrix is **chosen nonconstructively by `Classical.choose`**; no
efficient construction is supplied. Its bisection cut rank is at least `⌊n/2⌋ - O(√n)`
(`half_le_cutRank_hardMatrix`).

*Remark, not formalized.* Taking instead the lexicographically first robust matrix makes the family
computable in `E^NP`: whether some robust matrix extends a given prefix is one `NP` query of length
`2^{O(n)}` (guess the matrix and check its fewer than `4^{n/2}` pairs of row and column sets), so
the matrix is found bit by bit in time `2^{O(n)}`. Nothing in this file states or proves this
uniformity.

## Main definitions

* `Cslib.Circuits.Frontier.leftHalf`, `Cslib.Circuits.Frontier.rightHalf`: embeddings of the first
  and second `⌊n/2⌋` coordinates into `Fin n`.
* `Cslib.Circuits.Frontier.robustMatrix`: a fixed submatrix-robust `k × k` matrix over `𝔽₂`.
* `Cslib.Circuits.Frontier.hardMatrix`: the `n × n` matrix placing `robustMatrix ⌊n/2⌋` between the
  left and right halves.
* `Cslib.Circuits.Frontier.hardForm`: a nonconstructively chosen family of bilinear forms
  `xᵀ R y`.

## Main results

* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_gaussian`: correlation `2^{-γ n}`
  below `c n` gates for every family of quadratic forms whose bisection cut rank is
  `⌊n/2⌋ - o(n)`, for every `γ < (c* - c)/(2L)`.
* `Cslib.Circuits.Frontier.half_le_cutRank_hardMatrix`: the bisection cut rank of the chosen
  family.
* `Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le`: the headline bound for the
  chosen family.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt`: below `c n`
  gates, for any `c < c*`, a fixed rate `γ > 0`.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le`: below `2.77 n` gates,
  correlation `2^{-γ n}` for a fixed `γ > 0`.

## References

* [R. Chen, V. Kabanets, *Correlation bounds and #SAT algorithms for small linear-size
  circuits*][ChenKabanets2015]
* [A. Golovnev, A. S. Kulikov, A. V. Smal, S. Tamaki, *Circuit size lower bounds and #SAT upper
  bounds through a general framework*][GKST2016]
* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix Real

universe v

/-! ### The Gaussian rate -/

/-- The threshold and the rate of the Gaussian layout coefficient `A = 2p` in closed form:
`c* = 1 + π / (6 arccos ((1 + 2√2)/4))` and `L = 1 + π / (3 arccos ((1 + 2√2)/4))`. -/
private theorem gaussian_rate_eq (c : ℝ) :
    (1 + 1 / (2 * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + 1 / (2 * Gaussian.gaussianCoefficient))) =
      (1 + π / (6 * arccos ((1 + 2 * √2) / 4)) - c) /
        (2 * (1 + π / (3 * arccos ((1 + 2 * √2) / 4)))) := by
  have h := Gaussian.one_add_inv_two_mul_gaussianCoefficient
  have hp := Gaussian.gaussianCoefficient_pos
  have h' : 1 / (2 * Gaussian.gaussianCoefficient) = π / (3 * arccos ((1 + 2 * √2) / 4)) := by
    linarith
  have h4 : 1 / (2 * (2 * Gaussian.gaussianCoefficient)) =
      π / (6 * arccos ((1 + 2 * √2) / 4)) := by
    have e1 : 1 / (2 * (2 * Gaussian.gaussianCoefficient)) =
        1 / (2 * Gaussian.gaussianCoefficient) / 2 := by
      field_simp
    rw [e1, h']
    ring
  rw [h4, h']

/-- **The threshold is above `2.78`**: `c* = 1 + π / (6 arccos ((1 + 2√2)/4)) ≥ 139/50`, since
`c* = (1 + L)/2` and `L ≥ 114/25` (`Gaussian.circuitCoefficient_ge_456`). -/
theorem correlationThreshold_ge : (139 / 50 : ℝ) ≤ 1 + π / (6 * arccos ((1 + 2 * √2) / 4)) := by
  have h := Gaussian.circuitCoefficient_ge_456
  have : π / (6 * arccos ((1 + 2 * √2) / 4)) = π / (3 * arccos ((1 + 2 * √2) / 4)) / 2 := by
    rw [div_div]
    ring_nf
  rw [this]
  linarith

/-- **Exponentially small correlation below `2.78 n` gates.** If every set of `⌊n/2⌋` coordinates
has cut rank at least `⌊n/2⌋ - o(n)` in `Q_n + Q_nᵀ`, then for every `c ≥ 1/2` and every
`γ < (c* - c)/(2L)`, with `c* = 1 + π / (6 arccos ((1 + 2√2)/4)) ≈ 2.78125` and
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`, for all large `n` every circuit of fan-in at most
two, over any basis on `Bool` and accepting any set of values, with at most `c n` gates of positive
arity has correlation at most `2^{-γ n}` in absolute value with the quadratic form of `Q_n`. -/
theorem eventually_abs_correlation_quadForm_le_gaussian {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + π / (6 * arccos ((1 + 2 * √2) / 4)) - c) /
      (2 * (1 + π / (3 * arccos ((1 + 2 * √2) / 4)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_of_isLittleO
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hc
    (by rwa [gaussian_rate_eq]) Q e he hQ

/-! ### A nonconstructively chosen family -/

/-- The coordinate of an input of length `n` holding the entry `a` of its left half `x`: the left
half is the first `⌊n/2⌋` coordinates. -/
def leftHalf (n : ℕ) (a : Fin (n / 2)) : Fin n :=
  ⟨a, by omega⟩

/-- The coordinate of an input of length `n` holding the entry `b` of its right half `y`: the right
half is the next `⌊n/2⌋` coordinates. For odd `n` the last coordinate is in neither half. -/
def rightHalf (n : ℕ) (b : Fin (n / 2)) : Fin n :=
  ⟨n / 2 + b, by omega⟩

/-- The embedding `leftHalf n` of the first `⌊n/2⌋` coordinates into `Fin n` is injective. -/
theorem leftHalf_injective (n : ℕ) : Function.Injective (leftHalf n) :=
  fun a b h => Fin.ext (by simpa [leftHalf] using congrArg Fin.val h)

/-- The embedding `rightHalf n` of the second `⌊n/2⌋` coordinates into `Fin n` is injective. -/
theorem rightHalf_injective (n : ℕ) : Function.Injective (rightHalf n) :=
  fun a b h => Fin.ext (by simpa [rightHalf] using congrArg Fin.val h)

/-- The two halves are disjoint. -/
private theorem disjoint_range_leftHalf_rightHalf (n : ℕ) :
    Disjoint (range (leftHalf n)) (range (rightHalf n)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have := congrArg Fin.val hb
  simp only [leftHalf, rightHalf] at this
  omega

/-- A fixed submatrix-robust `k × k` matrix over `𝔽₂` with deficiency `2 ⌊√k⌋ + 1`, chosen once
and for all by `Classical.choose` from `Matrix.exists_submatrixRobust`. -/
noncomputable def robustMatrix (k : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Classical.choose (Matrix.exists_submatrixRobust k)

/-- The chosen matrix `robustMatrix k` is submatrix-robust with deficiency `2 * Nat.sqrt k + 1`. -/
theorem robustMatrix_submatrixRobust (k : ℕ) :
    (robustMatrix k).SubmatrixRobust (2 * Nat.sqrt k + 1) :=
  Classical.choose_spec (Matrix.exists_submatrixRobust k)

/-- The matrix of the chosen family: `robustMatrix ⌊n/2⌋` in the block whose rows are the left
half and whose columns are the right half, and zeros elsewhere. -/
noncomputable def hardMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  extendBlock (leftHalf n) (rightHalf n) (robustMatrix (n / 2))

/-- **The nonconstructively chosen family**: on inputs of length `n`, the quadratic form of
`hardMatrix n`, which is the bilinear form `xᵀ R y` of `R = robustMatrix ⌊n/2⌋` between the left
half `x` and the right half `y` (`hardForm_apply`). The matrix `R` is chosen by
`Classical.choose`. -/
noncomputable def hardForm (n : ℕ) : (Fin n → Bool) → Bool :=
  BitString.quadForm (hardMatrix n)

/-- The chosen family is the bilinear form `xᵀ R y` of `R = robustMatrix ⌊n/2⌋`. -/
theorem hardForm_apply (n : ℕ) (x : Fin n → Bool) :
    hardForm n x = decide ((fun a => BitString.bitVal (ZMod 2) (x (leftHalf n a))) ⬝ᵥ
      robustMatrix (n / 2) *ᵥ (fun b => BitString.bitVal (ZMod 2) (x (rightHalf n b))) = 1) :=
  BitString.quadForm_eq_of_submatrix (leftHalf_injective n) (rightHalf_injective n)
    (submatrix_extendBlock (leftHalf_injective n) (rightHalf_injective n) _)
    (fun _ _ h => extendBlock_eq_zero _ h) x

/-- **Bisection cut rank of the chosen family.** Every set of `⌊n/2⌋` coordinates has cut rank
at least `⌊n/2⌋ - (2 (2 ⌊√⌊n/2⌋⌋ + 1) + 1)` in the polar matrix of `hardMatrix n`. -/
theorem half_le_cutRank_hardMatrix (n : ℕ) {U : Set (Fin n)} (hU : U.ncard = n / 2) :
    n / 2 ≤ (hardMatrix n + (hardMatrix n)ᵀ).cutRank U + (2 * (2 * Nat.sqrt (n / 2) + 1) + 1) :=
  (robustMatrix_submatrixRobust (n / 2)).le_cutRank_add (leftHalf_injective n)
    (rightHalf_injective n) (disjoint_range_leftHalf_rightHalf n)
    (submatrix_extendBlock (leftHalf_injective n) (rightHalf_injective n) _)
    (fun _ _ h => extendBlock_eq_zero _ h)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hU

/-- The deficiency `2 (2 ⌊√⌊n/2⌋⌋ + 1) + 1` of the chosen family is sublinear. -/
private theorem isLittleO_hardDeficiency :
    (fun n : ℕ => ((2 * (2 * Nat.sqrt (n / 2) + 1) + 1 : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) := by
  rw [isLittleO_iff]
  intro ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop, (8 / ε) ^ 2 + 6 / ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h8 : (0 : ℝ) ≤ 8 / ε := by positivity
  have h6 : (0 : ℝ) ≤ 6 / ε := by positivity
  have hsqrt : (Nat.sqrt (n / 2) : ℝ) ≤ √n :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self n 2))
  have hss : √n * √n = n := Real.mul_self_sqrt hn0
  have hroot : 8 / ε ≤ √n := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (8 / ε)])
  have hs0 : 0 ≤ √n := Real.sqrt_nonneg _
  have h4 : 4 * √n ≤ ε / 2 * n := by
    have hm := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ ε / 2 * √n)
    have e1 : ε / 2 * √n * (8 / ε) = 4 * √n := by field_simp; ring
    have e2 : ε / 2 * √n * √n = ε / 2 * n := by rw [mul_assoc, hss]
    linarith
  have h3 : 3 ≤ ε / 2 * n := by
    have : 6 / ε * ε = 6 := by field_simp
    nlinarith
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  linarith

/-- The bisection hypothesis for the chosen family, in the form used by the asymptotic bounds. -/
private theorem half_le_cutRank_hardMatrix_add (n : ℕ) (U : Set (Fin n)) (hU : U.ncard = n / 2) :
    ((n / 2 : ℕ) : ℝ) ≤ (hardMatrix n + (hardMatrix n)ᵀ).cutRank U +
      ((2 * (2 * Nat.sqrt (n / 2) + 1) + 1 : ℕ) : ℝ) := by
  exact_mod_cast half_le_cutRank_hardMatrix n hU

/-- **Exponentially small correlation with the chosen family below `2.78 n` gates.** For every
`c ≥ 1/2` and every `γ < (c* - c)/(2L)`, with `c* = 1 + π / (6 arccos ((1 + 2√2)/4)) ≈ 2.78125`
and `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`, for all large `n` every circuit of fan-in at
most two, over any basis on `Bool` and accepting any set of values, with at most `c n` gates of
positive arity has correlation at most `2^{-γ n}` in absolute value with `hardForm n`. -/
theorem eventually_abs_correlation_hardForm_le {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + π / (6 * arccos ((1 + 2 * √2) / 4)) - c) /
      (2 * (1 + π / (3 * arccos ((1 + 2 * √2) / 4))))) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_gaussian hc hγ hardMatrix _ isLittleO_hardDeficiency
    (Eventually.of_forall half_le_cutRank_hardMatrix_add)

/-- **Every coefficient below the threshold.** For every `c < c*`, where
`c* = 1 + π / (6 arccos ((1 + 2√2)/4)) ≈ 2.78125`, some fixed `γ > 0` bounds, for all large `n`,
the correlation of every circuit of fan-in at most two, over any basis on `Bool` and accepting any
set of values, with at most `c n` gates of positive arity, with `hardForm n` by `2^{-γ n}`. -/
theorem exists_eventually_abs_correlation_hardForm_le_of_lt {c : ℝ}
    (hc : c < 1 + π / (6 * arccos ((1 + 2 * √2) / 4))) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  set c' := max c (1 / 2)
  set L := 1 + π / (3 * arccos ((1 + 2 * √2) / 4))
  have hL : 0 < L := by linarith [Gaussian.circuitCoefficient_ge_456]
  have hc' : c' < 1 + π / (6 * arccos ((1 + 2 * √2) / 4)) :=
    max_lt hc (by linarith [correlationThreshold_ge])
  set r := (1 + π / (6 * arccos ((1 + 2 * √2) / 4)) - c') / (2 * L)
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [eventually_abs_correlation_hardForm_le.{v} (le_max_right c (1 / 2))
    (γ := r / 2) (by linarith)] with n hn
  intro σ I Acc C hfan hsize
  exact hn σ I Acc C hfan
    (hsize.trans (mul_le_mul_of_nonneg_right (le_max_left c _) (Nat.cast_nonneg n)))

/-- **Below `2.77 n` gates.** Some fixed `γ > 0` bounds, for all large `n`, the correlation of
every circuit of fan-in at most two, over any basis on `Bool` and accepting any set of values, with
at most `2.77 n` gates of positive arity, with `hardForm n` by `2^{-γ n}`. -/
theorem exists_eventually_abs_correlation_hardForm_le :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 →
        (C.innerSize : ℝ) ≤ 277 / 100 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt (by linarith [correlationThreshold_ge])

end Cslib.Circuits.Frontier
