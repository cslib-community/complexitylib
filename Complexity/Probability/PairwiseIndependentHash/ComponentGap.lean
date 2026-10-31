/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.PiProduct
public import Complexity.Probability.PairwiseIndependentHash.SliceGap
import Complexity.Foundations.Combinatorics.Expander.PairShearTranslation
import Complexity.Foundations.Data.Finset.Expect

/-!
# The spectral gap of the product walk over channels and free bits

The averaging walk of the sampler moves several independent components: `J` conditioned
channels, with slice coordinates `Frame (P j) H 1 × ZMod (L j) ^ H`, and one block of free bits,
identified with the torus `ZMod M ^ H` (for `M = 2 ^ q`, the bit strings of length `H q`). On the
torus, the generators `affineGenerator` act by the affine action alone (`torusMove`). The product
walk (`componentMove`) picks one component and makes one affine move there.

* **The torus.** For `H ≥ 2`, the coordinate-pair bound
  `expect_sq_sub_expect_le_pairShearTranslation` with a trivial spectator gives the Poincaré
  inequality with constant `2048 H`, uniformly in `M` (`expect_sq_le_torusMove`).
* **The product.** Each channel satisfies the Poincaré inequality with constant `38912 H²`
  (`expect_sq_le_affineMove`), and so does the torus. Poincaré inequalities tensorize
  (`mul_expect_sq_le_piPerms`, `mul_expect_sq_le_boxProdPerms`), so the product satisfies it with
  the same constant (`expect_sq_le_componentMove`). Since the product has `J + 1` times as many
  moves, its gap is the single-component gap divided by the number `J + 1` of components:
  `λ₂ ≤ 1 - 1 / (77824 (J + 1) H ^ 4)` and, for the lazy walk, spectral expansion at most
  `1 - 1 / (155648 (J + 1) H ^ 4)`, uniformly in the primes `P j`, the sides `L j` and `M`.
* **Conditional averaging.** Transported to the product of the retention slices of identifiers
  `y j` (`componentEquiv`), the lazy walk contracts the variance by that bound squared per step,
  uniformly in the identifiers (`expect_walk_pow_componentMove_sub_expect_sq_le`).

This is the product walk of the proof of Lemma 6.2 of the OpenAI preprint on derandomizing
logarithmic space [OpenAI2026LogSpace]: the free bits as `(ℤ / 2^q ℤ) ^ H` with the affine action
on that coordinate alone, and "the lazy walk from Lemma 6.1 [applied] to a uniformly selected
component", with gap `γ_H / J_comp`. The preprint's single-component gap comes from Shalom's
property (T); the elementary route through coordinate pairs and frames follows OpenAI's Lean
development, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc` (`ExactDerandomization.Analysis.Square.square_gap`, `slice_frame`,
`frame_gap`, `slice_gap`). The statements and the proofs here are independent of that code, which
was not consulted.

## Main definitions

* `Cslib.Probability.torusMove`: the affine moves of the free-bit torus.
* `Cslib.Probability.componentMove`: the moves of the product walk over channels and free bits.
* `Cslib.Probability.componentEquiv`: coordinates on a product of retention slices.

## Main results

* `Cslib.Probability.expect_sq_le_torusMove`: the Poincaré inequality on the torus.
* `Cslib.Probability.expect_sq_le_componentMove`: the Poincaré inequality for the product walk.
* `Cslib.Probability.secondEigenvalue_ofPerms_componentMove_le`,
  `Cslib.Probability.spectralExpansion_lazy_ofPerms_componentMove_le`: the gap `γ / (J + 1)`.
* `Cslib.Probability.expect_walk_pow_componentMove_sub_expect_sq_le`: conditional averaging over
  channels and free bits.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset Function Matrix RotationMap
open scoped BigOperators

variable {H M : ℕ}

/-! ### The free-bit torus -/

variable (H M) in
/-- **The affine moves of the free-bit torus** `ZMod M ^ H`: the generators `affineGenerator`
acting on the torus alone, `w ↦ (1 + E_ab) w` and `w ↦ w + e_i`. -/
@[expose] def torusMove (k : {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) :
    Equiv.Perm (Fin H → ZMod M) :=
  affineSL (ZMod M) (affineGenerator H k).1 fun i ↦ ((affineGenerator H k).2 i : ZMod M)

@[simp]
theorem torusMove_inl (p : {p : Fin H × Fin H // p.1 ≠ p.2}) (w : Fin H → ZMod M) :
    torusMove H M (.inl p) w = update w p.1.1 (w p.1.1 + w p.1.2) := by
  simp only [torusMove, affineGenerator, Sum.elim_inl, affineSL_apply,
    SpecialLinearGroup.map_transvection, SpecialLinearGroup.transvection_mulVec, map_one, one_mul]
  exact funext fun _ ↦ by simp

@[simp]
theorem torusMove_inr (i : Fin H) (w : Fin H → ZMod M) :
    torusMove H M (.inr i) w = update w i (w i + 1) := by
  ext j
  simp only [torusMove, affineGenerator, Sum.elim_inr, affineSL_apply, map_one,
    SpecialLinearGroup.coe_one, one_mulVec, Pi.add_apply, update_apply]
  split_ifs with h
  · subst h
    simp
  · simp [h]

/-- **The Poincaré inequality for the free-bit torus** `ZMod M ^ H`, for `H ≥ 2`, uniformly in
`M`: every real function `f` of mean zero has second moment at most `2048 H` times its total squared
change along the affine moves. -/
theorem expect_sq_le_torusMove [NeZero M] (hH : 2 ≤ H) (f : (Fin H → ZMod M) → ℝ)
    (hf : 𝔼 w, f w = 0) :
    𝔼 w, f w ^ 2 ≤ 2048 * H * ∑ k, 𝔼 w, (f (torusMove H M k w) - f w) ^ 2 := by
  set D := ∑ k, 𝔼 w, (f (torusMove H M k w) - f w) ^ 2
  have hterm (k) : 𝔼 w, (f (torusMove H M k w) - f w) ^ 2 ≤ D :=
    single_le_sum (f := fun k ↦ 𝔼 w, (f (torusMove H M k w) - f w) ^ 2)
      (fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ k)
  have hH2 : Nontrivial (Fin H) := Fin.nontrivial_iff_two_le.2 hH
  choose σ hσ using fun i : Fin H ↦ exists_ne i
  -- The coordinate-pair bound with a trivial spectator.
  set F : Unit × (Fin H → ZMod M) → ℝ := fun p ↦ f p.2 with hF
  have hU (φ : (Fin H → ZMod M) → ℝ) : 𝔼 p : Unit × (Fin H → ZMod M), φ p.2 = 𝔼 w, φ w := by
    simp [Fintype.expect_prod_type]
  have h := expect_sq_sub_expect_le_pairShearTranslation (fun _ _ ↦ Equiv.refl Unit) σ hσ F
  have hL : 𝔼 p, (F p - 𝔼 w, F (p.1, w)) ^ 2 = 𝔼 w, f w ^ 2 := by
    simp only [hF, hf, sub_zero]
    exact hU fun w ↦ f w ^ 2
  have hpair (i : Fin H) (k : Fin 4) :
      𝔼 p, (F (pairShearTranslationMove (Equiv.refl Unit) (Equiv.refl Unit) i (σ i) k p) -
        F p) ^ 2 ≤ D := by
    have hσi : i ≠ σ i := (hσ i).symm
    fin_cases k
    · have := hterm (.inl ⟨(i, σ i), hσi⟩)
      simp only [torusMove_inl] at this
      refine le_trans (le_of_eq ?_) this
      rw [← hU]
      rfl
    · have := hterm (.inl ⟨(σ i, i), hσi.symm⟩)
      simp only [torusMove_inl] at this
      refine le_trans (le_of_eq ?_) this
      rw [← hU]
      rfl
    · have := hterm (.inr i)
      simp only [torusMove_inr] at this
      refine le_trans (le_of_eq ?_) this
      rw [← hU]
      rfl
    · have := hterm (.inr (σ i))
      simp only [torusMove_inr] at this
      refine le_trans (le_of_eq ?_) this
      rw [← hU]
      rfl
  rw [hL] at h
  refine h.trans ?_
  calc 512 * ∑ i, ∑ k, 𝔼 p, (F (pairShearTranslationMove (Equiv.refl Unit) (Equiv.refl Unit)
        i (σ i) k p) - F p) ^ 2 ≤ 512 * ∑ _i : Fin H, ∑ _k : Fin 4, D := by
        gcongr with i _ k _
        exact hpair i k
    _ = 2048 * H * D := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring


/-! ### Channels and free bits -/

variable {J : ℕ}

variable (H M) in
/-- **The moves of the product walk** on the coordinates of `J` channels and the free-bit torus:
`(∀ j, Frame (P j) H 1 × ZMod (L j) ^ H) × ZMod M ^ H`. A move applies an affine move to one
channel (`affineMove`) or to the torus (`torusMove`). -/
@[expose] def componentMove (P L : Fin J → ℕ) :
    (Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
        ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) →
      Equiv.Perm ((∀ j, Frame (P j) H 1 × (Fin H → ZMod (L j))) × (Fin H → ZMod M)) :=
  boxProdPerms (piPerms fun j ↦ affineMove (P j) H (L j) 1) (torusMove H M)

/-- The product walk has `(J + 1) H ^ 2` moves. -/
theorem card_componentMove_index :
    Fintype.card ((Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
      ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H)) = (J + 1) * H ^ 2 := by
  rw [Fintype.card_sum, Fintype.card_sigma, card_affineGenerator_index]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

variable {P L : Fin J → ℕ} [∀ j, Fact (P j).Prime] [∀ j, NeZero (L j)] [NeZero M]

/-- **The Poincaré inequality for the product walk** over `J` channels and the free-bit torus, for
`H ≥ 3`, uniformly in the primes `P j`, the sides `L j`, the torus modulus `M` and `J`: every real
function of mean zero has second moment at most `38912 H²` times its total squared change along the
moves. -/
theorem expect_sq_le_componentMove (hH : 3 ≤ H)
    (f : (∀ j, Frame (P j) H 1 × (Fin H → ZMod (L j))) × (Fin H → ZMod M) → ℝ)
    (hf : 𝔼 p, f p = 0) :
    𝔼 p, f p ^ 2 ≤ 38912 * H ^ 2 * ∑ k, 𝔼 p, (f (componentMove H M P L k p) - f p) ^ 2 := by
  have hH0 : (0 : ℝ) < 38912 * H ^ 2 := by
    have : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    positivity
  -- Each component satisfies the Poincaré inequality with constant `1 / (38912 H²)`.
  have hc {V K : Type} [Fintype V] [Fintype K] (σ : K → Equiv.Perm V)
      (h : ∀ g : V → ℝ, 𝔼 v, g v = 0 →
        𝔼 v, g v ^ 2 ≤ 38912 * H ^ 2 * ∑ k, 𝔼 v, (g (σ k v) - g v) ^ 2)
      (g : V → ℝ) (hg : 𝔼 v, g v = 0) :
      1 / (38912 * H ^ 2) * 𝔼 v, g v ^ 2 ≤ ∑ k, 𝔼 v, (g (σ k v) - g v) ^ 2 := by
    rw [one_div_mul_eq_div, div_le_iff₀ hH0]
    linarith [h g hg]
  have htorus (g : (Fin H → ZMod M) → ℝ) (hg : 𝔼 w, g w = 0) :
      𝔼 w, g w ^ 2 ≤ 38912 * H ^ 2 * ∑ k, 𝔼 w, (g (torusMove H M k w) - g w) ^ 2 := by
    refine (expect_sq_le_torusMove (by omega) g hg).trans ?_
    have hD : 0 ≤ ∑ k, 𝔼 w, (g (torusMove H M k w) - g w) ^ 2 :=
      sum_nonneg fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _
    have : (2048 * H : ℝ) ≤ 38912 * H ^ 2 := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hD
  have h := mul_expect_sq_le_boxProdPerms
    (σ := piPerms fun j ↦ affineMove (P j) H (L j) 1) (τ := torusMove H M)
    (fun g hg ↦ mul_expect_sq_le_piPerms _
      (fun j ↦ hc _ fun g hg ↦ expect_sq_le_affineMove hH g hg) g hg)
    (hc _ htorus) f hf
  rw [one_div_mul_eq_div, div_le_iff₀ hH0, mul_comm] at h
  exact h

/-- **The second eigenvalue of the product walk** over `J` channels and the free-bit torus is at
most `1 - 1 / (77824 (J + 1) H ^ 4)`, for `H ≥ 3`, uniformly in the moduli: the single-component
gap `1 / (77824 H ^ 4)` divided by the number `J + 1` of components. -/
theorem secondEigenvalue_ofPerms_componentMove_le (hH : 3 ≤ H) :
    (ofPerms (componentMove H M P L)).secondEigenvalue ≤ 1 - 1 / (77824 * (J + 1) * H ^ 4) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  rcases subsingleton_or_nontrivial
      ((∀ j, Frame (P j) H 1 × (Fin H → ZMod (L j))) × (Fin H → ZMod M)) with hV | hV
  · rw [secondEigenvalue_eq_zero_of_subsingleton, sub_nonneg]
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ H ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ H))
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    nlinarith
  have : Nonempty ((Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
      ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H)) := ⟨.inr (.inr ⟨0, by omega⟩)⟩
  have h := secondEigenvalue_ofPerms_le (componentMove H M P L) (c := 1 / (38912 * H ^ 2))
    fun f hf ↦ by
      have := expect_sq_le_componentMove hH f hf
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      linarith
  refine h.trans_eq ?_
  rw [card_componentMove_index]
  push_cast
  field_simp
  ring

/-- **The spectral gap of the lazy product walk** over `J` channels and the free-bit torus: its
spectral expansion is at most `1 - 1 / (155648 (J + 1) H ^ 4)`, for `H ≥ 3`, uniformly in the
primes, the sides and the torus modulus. -/
theorem spectralExpansion_lazy_ofPerms_componentMove_le (hH : 3 ≤ H) :
    (ofPerms (componentMove H M P L)).lazy.spectralExpansion ≤
      1 - 1 / (155648 * (J + 1) * H ^ 4) := by
  have h₁ :=
    (ofPerms (componentMove H M P L)).spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two
  have h₂ := secondEigenvalue_ofPerms_componentMove_le (M := M) (P := P) (L := L) hH
  have : 1 / (155648 * ((J : ℝ) + 1) * H ^ 4) = (1 / (77824 * (J + 1) * H ^ 4)) / 2 := by
    rw [div_div]
    ring
  rw [this]
  linarith

variable (M) in
/-- **Coordinates on a product of retention slices**: a family of channels retaining the
identifiers `y j`, together with free bits, is a family of slice coordinates together with the
free bits. -/
@[expose] def componentEquiv (hL : ∀ j, L j ≤ P j) (y : ∀ j, ZMod (P j)) :
    (∀ j, RetentionSlice (P j) H 1 (L j) (y j)) × (Fin H → ZMod M) ≃
      (∀ j, Frame (P j) H 1 × (Fin H → ZMod (L j))) × (Fin H → ZMod M) :=
  (Equiv.piCongrRight fun j ↦ sliceEquiv (hL j) (y j)).prodCongr (Equiv.refl _)

/-- **Conditional averaging over channels and free bits** (the `L²` case of Lemma 6.2): on the
product of the retention slices of identifiers `y j` of `J` channels with free bits in
`ZMod M ^ H`, `t` steps of the lazy product walk contract the variance by
`(1 - 1 / (155648 (J + 1) H ^ 4)) ^ (2 t)`, for `H ≥ 3`, uniformly in the primes, the sides, the
identifiers and the torus modulus. -/
theorem expect_walk_pow_componentMove_sub_expect_sq_le (hH : 3 ≤ H) (hL : ∀ j, L j ≤ P j)
    (y : ∀ j, ZMod (P j))
    (f : (∀ j, RetentionSlice (P j) H 1 (L j) (y j)) × (Fin H → ZMod M) → ℝ) (t : ℕ) :
    𝔼 A, ((((ofPerms (componentMove H M P L)).lazy.reindex
        (componentEquiv M hL y).symm).walk ^ t) f A - 𝔼 B, f B) ^ 2 ≤
      (1 - 1 / (155648 * (J + 1) * H ^ 4)) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  have : Nonempty ((Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
      ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H)) := ⟨.inr (.inr ⟨0, by omega⟩)⟩
  set G := (ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm
  refine (G.expect_walk_pow_sub_expect_sq_le t f).trans ?_
  rw [spectralExpansion_reindex]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (spectralExpansion_nonneg _)
      (spectralExpansion_lazy_ofPerms_componentMove_le hH) _)
    (expect_nonneg fun _ _ ↦ sq_nonneg _)

end Cslib.Probability
