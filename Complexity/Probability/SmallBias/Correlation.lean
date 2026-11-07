/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.SmallBias
import Complexity.Foundations.Analysis.InnerProductSpace.NearlyOrthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Codes from small-bias lists: nearly uncorrelated codewords and short correlation lists

A list `r : Z → ι → Bool` of bit strings, indexed by a finite type `Z`, encodes a message
`x : ι → Bool` as the word `z ↦ r z ⬝ᵥ x` of inner products modulo two: the linear code whose
generator matrix has the rows `r z`. Suppose the list is `δ`-biased, that is, the uniform
distribution over the list is `δ`-biased (`Cslib.BitString.IsSmallBias`). Then the word of a
nonzero message is nearly balanced, `|∑ z, signVal (r z ⬝ᵥ x)| ≤ δ |Z|`
(`Cslib.BitString.abs_sum_signVal_dotProduct_le`), and the words of distinct messages are nearly
uncorrelated (`Cslib.BitString.abs_sum_signVal_mul_signVal_dotProduct_le`), since their exclusive
or is the word of the nonzero message `x + y`. This is the code of [KaneWilliams2016],
`arXiv:1511.07860v1`, Proposition 2 and Corollary 6.1 (labels `eps-biased` and `uncorrFunctCor`),
in `±1` correlation form.

Few codewords then correlate with any fixed word `T : Z → Bool`: for `δ, γ ≥ 0`, at most
`1 / (γ ^ 2 - δ)` messages `x` have `|∑ z, signVal (T z) * signVal (r z ⬝ᵥ x)| ≥ γ |Z|`
(`Cslib.BitString.card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le`). This is
[KaneWilliams2016], Lemma 6.1 (label `uncorrAgreeLem`), with explicit constants; it follows from
`card_mul_sub_le_one_of_abs_inner_ge` for the `±1` words in `EuclideanSpace ℝ Z`.

## Main results

* `Cslib.BitString.sum_signVal_dotProduct_eq`: the sign sum of a word is `|Z|` times a bias of the
  list.
* `Cslib.BitString.abs_sum_signVal_dotProduct_le`: the word of a nonzero message is nearly
  balanced.
* `Cslib.BitString.abs_sum_signVal_mul_signVal_dotProduct_le`: the words of distinct messages are
  nearly uncorrelated.
* `Cslib.BitString.card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le`: few codewords correlate
  with a fixed word.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Section 6
* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
-/

public section

namespace Cslib.BitString

open Finset Probability
open scoped RealInnerProductSpace

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z]

/-- The sign sum of the word `z ↦ r z ⬝ᵥ x` is `|Z|` times the bias of the list `r` at the
support of `x`. -/
theorem sum_signVal_dotProduct_eq [Nonempty Z] (r : Z → ι → Bool) (x : ι → Bool) :
    ∑ z, signVal (r z ⬝ᵥ x) =
      Fintype.card Z * bias ((PMF.uniformOfFintype Z).map r) {i | x i} := by
  have hZ : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card, mul_div_cancel₀ _ hZ]
  exact sum_congr rfl fun z _ => by rw [dotProduct_comm, signVal_dotProduct]

/-- **The word of a nonzero message is nearly balanced**: if the list `r` is `δ`-biased and
`x ≠ 0`, then `|∑ z, signVal (r z ⬝ᵥ x)| ≤ δ |Z|`. -/
theorem abs_sum_signVal_dotProduct_le [Nonempty Z] {δ : ℝ} {r : Z → ι → Bool}
    (hr : IsSmallBias δ ((PMF.uniformOfFintype Z).map r)) {x : ι → Bool} (hx : x ≠ 0) :
    |∑ z, signVal (r z ⬝ᵥ x)| ≤ δ * Fintype.card Z := by
  rw [sum_signVal_dotProduct_eq, abs_mul, Nat.abs_cast, mul_comm]
  refine mul_le_mul_of_nonneg_right (hr _ ?_) (Nat.cast_nonneg _)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  refine ⟨i, mem_filter.mpr ⟨mem_univ i, ?_⟩⟩
  revert hi
  cases x i <;> simp

/-- **The words of distinct messages are nearly uncorrelated** ([KaneWilliams2016],
`arXiv:1511.07860v1`, Corollary 6.1, in `±1` form): if the list `r` is `δ`-biased and `x ≠ y`,
then `|∑ z, signVal (r z ⬝ᵥ x) * signVal (r z ⬝ᵥ y)| ≤ δ |Z|`. -/
theorem abs_sum_signVal_mul_signVal_dotProduct_le [Nonempty Z] {δ : ℝ} {r : Z → ι → Bool}
    (hr : IsSmallBias δ ((PMF.uniformOfFintype Z).map r)) {x y : ι → Bool} (hxy : x ≠ y) :
    |∑ z, signVal (r z ⬝ᵥ x) * signVal (r z ⬝ᵥ y)| ≤ δ * Fintype.card Z := by
  have hsum : ∑ z, signVal (r z ⬝ᵥ x) * signVal (r z ⬝ᵥ y) = ∑ z, signVal (r z ⬝ᵥ (x + y)) :=
    sum_congr rfl fun z _ => by rw [dotProduct_add, ← signVal_xor]; rfl
  rw [hsum]
  exact abs_sum_signVal_dotProduct_le hr fun h =>
    hxy (funext fun i => (BooleanRing.add_eq_zero' (x i) (y i)).mp (congrFun h i))

/-- The `±1` word of a Boolean function, as a vector of `EuclideanSpace ℝ Z`. -/
private noncomputable def signWord (f : Z → Bool) : EuclideanSpace ℝ Z :=
  WithLp.toLp 2 fun z => signVal (f z)

private theorem inner_signWord (f g : Z → Bool) :
    ⟪signWord f, signWord g⟫ = ∑ z, signVal (f z) * signVal (g z) := by
  simp [signWord, PiLp.inner_apply, mul_comm]

private theorem norm_signWord_sq (f : Z → Bool) : ‖signWord f‖ ^ 2 = Fintype.card Z := by
  rw [← real_inner_self_eq_norm_sq, inner_signWord]
  simp [signVal_mul_self]

/-- **Few codewords correlate with a fixed word** ([KaneWilliams2016], `arXiv:1511.07860v1`,
Lemma 6.1, with explicit constants): if the list `r` is `δ`-biased with `δ ≥ 0` and `γ ≥ 0`, then
the messages `x` whose words have correlation at least `γ |Z|` in absolute value with a fixed word
`T` number at most `1 / (γ ^ 2 - δ)`, in the form `#{x | …} * (γ ^ 2 - δ) ≤ 1`. -/
theorem card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le [Nonempty Z] {δ γ : ℝ} (hδ : 0 ≤ δ)
    (hγ : 0 ≤ γ) {r : Z → ι → Bool} (hr : IsSmallBias δ ((PMF.uniformOfFintype Z).map r))
    (T : Z → Bool) :
    (#{x : ι → Bool | γ * Fintype.card Z ≤ |∑ z, signVal (T z) * signVal (r z ⬝ᵥ x)|} : ℝ) *
      (γ ^ 2 - δ) ≤ 1 := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  refine card_mul_sub_le_one_of_abs_inner_ge _ (fun x => signWord fun z => r z ⬝ᵥ x)
    (signWord T) hZ hδ hγ (norm_signWord_sq T).le (fun x _ => (norm_signWord_sq _).le)
    (fun x _ y _ hxy => ?_) (fun x hx => ?_)
  · rw [inner_signWord]
    exact abs_sum_signVal_mul_signVal_dotProduct_le hr hxy
  · rw [inner_signWord]
    exact (mem_filter.mp hx).2

end Cslib.BitString
