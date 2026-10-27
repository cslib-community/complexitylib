/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Mixing
public import Complexity.Probability.SmallBias

/-!
# Cayley graphs of the Boolean cube

The Cayley graph of the cube `ι → Bool` with generators `s₁, …, s_d` joins each `u` to `u + sⱼ`
along its `j`-th edge (`Cslib.RotationMap.cubeCayley`). Every bit string is its own negative, so
this is an undirected `d`-regular multigraph and the rotation map is an involution.

Its walk operator multiplies the Fourier coefficient of each function at `S` by the bias of the
generators at `S` (`Cslib.RotationMap.fourierCoeff_walk_cubeCayley`). The characters are therefore
its eigenvectors, and by Plancherel's identity its spectral expansion is at most the bias of the
generators: if the uniform distribution over the generators is `ε`-biased with `ε ≥ 0`, then
`λ(G) ≤ ε` (`Cslib.RotationMap.spectralExpansion_cubeCayley_le`). The expander mixing lemma then
counts the edges between two sets (`Cslib.RotationMap.card_interedges_cubeCayley_le`), again for
`ε ≥ 0`. This is the mixing estimate (6.3) in the proof
of [OpenAI2026ETH, Lemma 6.1], whose bipartite double cover has left vertex `u` joined by its
`j`-th edge to right vertex `u + sⱼ`.

## Main definitions

* `Cslib.RotationMap.cubeCayley`: the Cayley graph of the cube with given generators.

## Main results

* `Cslib.RotationMap.fourierCoeff_walk_cubeCayley`: the walk is diagonal in the Fourier basis.
* `Cslib.RotationMap.spectralExpansion_cubeCayley_le`: small-bias generators give small spectral
  expansion.
* `Cslib.RotationMap.card_interedges_cubeCayley_le`: the edge count between two sets.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset Cslib.BitString Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} {d : ℕ}

/-- Every bit string is its own negative. -/
private theorem add_self_bitString (x : ι → Bool) : x + x = 0 :=
  funext fun i => by simp only [Pi.add_apply, Pi.zero_apply]; cases x i <;> rfl

/-- The Cayley graph of the cube with generators `s j`: the `j`-th edge at `u` leads to `u + s j`,
where it is also the `j`-th edge. -/
def cubeCayley (s : Fin d → ι → Bool) : RotationMap (ι → Bool) (Fin d) where
  rot p := (p.1 + s p.2, p.2)
  rot_involutive p := by
    ext1
    · change p.1 + s p.2 + s p.2 = p.1
      rw [add_assoc, add_self_bitString, add_zero]
    · rfl

/-- The `j`-th neighbor of `u` is `u + s j`. -/
@[simp]
theorem cubeCayley_neighbor (s : Fin d → ι → Bool) (u : ι → Bool) (j : Fin d) :
    (cubeCayley s).neighbor u j = u + s j :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- The walk operator of a Cayley graph of the cube multiplies each Fourier coefficient by the bias
of the generators. -/
theorem fourierCoeff_walk_cubeCayley [NeZero d] (s : Fin d → ι → Bool) (f : (ι → Bool) → ℝ)
    (S : Finset ι) :
    fourierCoeff ((cubeCayley s).walk f) S =
      bias ((uniformOfFintype (Fin d)).map s) S * fourierCoeff f S := by
  rw [bias_uniformOfFintype_map]
  simp only [fourierCoeff, walk_apply, cubeCayley_neighbor]
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun j _ => ?_
  rw [Fintype.expect_equiv (Equiv.addRight (s j)) _ (fun k => f k * chi ℝ S (k + s j))
    (fun i => by simp only [Equiv.coe_addRight, add_assoc, add_self_bitString, add_zero]),
    Finset.mul_expect]
  refine Finset.expect_congr rfl fun u _ => ?_
  rw [chi_add]
  ring

/-- **Small-bias generators give small spectral expansion**: if the uniform distribution over the
generators is `ε`-biased, with `ε ≥ 0`, the spectral expansion of the Cayley graph is at most
`ε`. -/
theorem spectralExpansion_cubeCayley_le [NeZero d] (s : Fin d → ι → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : IsSmallBias ε ((uniformOfFintype (Fin d)).map s)) :
    (cubeCayley s).spectralExpansion ≤ ε := by
  refine spectralExpansion_le hε fun f hf => ?_
  have h₀ : fourierCoeff f ∅ = 0 := by simpa [fourierCoeff] using hf
  rw [show (𝔼 v, (cubeCayley s).walk f v ^ 2) =
      𝔼 v, (cubeCayley s).walk f v * (cubeCayley s).walk f v by simp [sq],
    show (𝔼 v, f v ^ 2) = 𝔼 v, f v * f v by simp [sq],
    expect_mul_eq_sum_fourierCoeff_mul, expect_mul_eq_sum_fourierCoeff_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [fourierCoeff_walk_cubeCayley]
  by_cases hS : S = ∅
  · subst hS
    simp [h₀]
  · have hb := hs S (Finset.nonempty_iff_ne_empty.mpr hS)
    have : bias ((uniformOfFintype (Fin d)).map s) S ^ 2 ≤ ε ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (bias ((uniformOfFintype (Fin d)).map s) S)])
        ((le_abs_self _).trans hb)
    nlinarith [sq_nonneg (fourierCoeff f S)]

/-- **Edges between two sets of a small-bias Cayley graph** (the mixing estimate (6.3) of
[OpenAI2026ETH]): if the generators are `ε`-biased, with `ε ≥ 0`, the number of edges from `U` to
`V` is at most `d |U| |V| / 2^|ι| + ε d √(|U| |V|)`. -/
theorem card_interedges_cubeCayley_le [NeZero d] (s : Fin d → ι → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : IsSmallBias ε ((uniformOfFintype (Fin d)).map s)) (U V : Finset (ι → Bool)) :
    (#((cubeCayley s).interedges U V) : ℝ) ≤
      d * #U * #V / 2 ^ Fintype.card ι + ε * d * √((#U : ℝ) * #V) := by
  have h := (cubeCayley s).abs_card_interedges_sub_le_mul_sqrt U V
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at h
  push_cast at h
  have hlam := spectralExpansion_cubeCayley_le s hε hs
  have hsq : 0 ≤ (d : ℝ) * √((#U : ℝ) * #V) := by positivity
  have := mul_le_mul_of_nonneg_right hlam hsq
  linarith [le_abs_self ((#((cubeCayley s).interedges U V) : ℝ) -
    d * #U * #V / 2 ^ Fintype.card ι)]

end Cslib.RotationMap
