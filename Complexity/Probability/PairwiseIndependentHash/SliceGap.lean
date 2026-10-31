/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.ElementaryMove
public import Complexity.Foundations.Combinatorics.Expander.Lazy
public import Complexity.Foundations.LinearAlgebra.Matrix.Transvection
public import Complexity.Probability.PairwiseIndependentHash.ConditionalAveraging
import Complexity.Foundations.Combinatorics.Expander.PairShearTranslation
import Complexity.Foundations.Data.Finset.Expect

/-!
# The spectral gap of the affine walk on slice coordinates

On the slice coordinates `(F, w) ∈ Frame P H 1 × ZMod L ^ H` of a retention slice
(`Cslib.Probability.sliceEquiv`), the **affine moves** (`affineMove`) are the moves `coordMove`
of the elementary matrices `1 + E_ab` of `SL_H(ℤ)`, `a ≠ b`, and of the unit translations `e_i`:

`(F, w) ↦ ((1 + E_ab) F, (1 + E_ab) w)`,  `(F, w) ↦ (F, w + e_i)`.

For a prime `P` and `H ≥ 3`, the lazy walk on these `H ^ 2` moves and their inverses has spectral
expansion at most `1 - 1 / (155648 H ^ 4)`, **uniformly in `P` and `L`**
(`spectralExpansion_lazy_ofPerms_affineMove_le`). This is the gap hypothesis of conditional
averaging (`expect_walk_pow_sliceGraph_sub_expect_sq_le`) for frames of length one, which is thereby
discharged (`expect_walk_pow_sliceGraph_affineMove_sub_expect_sq_le`).

The proof is a Poincaré inequality (`expect_sq_le_affineMove`) assembled from two parts. Write
`g F = 𝔼 w, f (F, w)`, so that `𝔼 f² = 𝔼 g² + 𝔼 (f - g)²` for `f` of mean zero.

* **The box part.** The coordinate-pair bound `expect_sq_sub_expect_le_pairShearTranslation`, with
  the frames as the spectator `Y` and the elementary matrices acting on them, bounds
  `𝔼 (f - g)²` by the squared changes of `f` along the affine moves: its pair moves are affine
  moves.
* **The frame part.** A frame of length one is a nonzero vector (`Frame.equivNeZero`), on which
  `1 + E_ab` acts by the elementary move (`Frame.mapSL_transvection_apply_zero`). So the Poincaré
  inequality for the elementary moves on the nonzero vectors of `(ZMod P) ^ H`
  (`exists_expect_sq_sub_le_elementaryMove`), whose averages are masked averages over all vectors,
  becomes one on the frames (`exists_expect_sq_sub_le_mapSL_transvection`). It bounds `𝔼 g²` by the
  squared changes of `g` along the elementary matrices, and by Jensen's inequality these are at
  most those of `f` along the affine moves, since an affine move acts on `w` by a bijection.

The second eigenvalue then follows from `secondEigenvalue_ofPerms_le`, and the lazy walk halves
the gap.

This is the uniform gap of Lemma 6.1 of the OpenAI preprint on derandomizing logarithmic space
[OpenAI2026LogSpace], for its action on the coordinates `(F, w)` of the proof of its Lemma 6.2, in
the case of frames of length one (`h₀ = 2`). The preprint derives the gap from Shalom's property
(T) of `SL_H(ℤ) ⋉ ℤ^H` and its transitive action. The elementary route, from the uniform
two-dimensional gap through the coordinate pairs to the frames, follows OpenAI's Lean
development, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc` (`ExactDerandomization.Analysis.Square.square_gap`, `slice_frame`,
`frame_gap`, `slice_gap`). The statements and the proofs here are independent of that code, which
was not consulted.

## Main definitions

* `Cslib.Probability.Frame.equivNeZero`: frames of length one are nonzero vectors.
* `Cslib.Probability.affineGenerator`: the elementary matrices and the unit translations.
* `Cslib.Probability.affineMove`: their moves on slice coordinates.

## Main results

* `Cslib.Probability.Frame.card_one`: there are `P ^ H - 1` frames of length one.
* `Cslib.Probability.exists_expect_sq_sub_le_mapSL_transvection`: the Poincaré inequality for the
  elementary matrices on frames of length one, uniformly in `P`.
* `Cslib.Probability.expect_sq_le_affineMove`: the Poincaré inequality for the affine moves on
  `Frame P H 1 × ZMod L ^ H`, uniformly in `P` and `L`.
* `Cslib.Probability.secondEigenvalue_ofPerms_affineMove_le`,
  `Cslib.Probability.spectralExpansion_lazy_ofPerms_affineMove_le`: the uniform spectral gap.
* `Cslib.Probability.expect_walk_pow_sliceGraph_affineMove_sub_expect_sq_le`: conditional
  averaging on every retention slice, with the gap hypothesis discharged.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset Function Matrix RotationMap
open scoped BigOperators

variable {P H L : ℕ}

/-- The integer matrix `1` acts trivially on frames. -/
@[simp]
theorem Frame.mapSL_one {r : ℕ} (F : Frame P H r) : Frame.mapSL 1 F = F :=
  Subtype.ext <| funext fun j ↦ by simp

/-! ### Frames of length one -/

section FrameOne

variable [Fact P.Prime]

/-- **A frame of length one is a nonzero vector.** -/
@[expose] def Frame.equivNeZero : Frame P H 1 ≃ {v : Fin H → ZMod P // v ≠ 0} where
  toFun F := ⟨F.1 0, linearIndependent_unique_iff.1 F.2⟩
  invFun v := ⟨fun _ ↦ v.1, linearIndependent_unique_iff.2 v.2⟩
  left_inv F := Subtype.ext <| funext fun i ↦ by rw [Subsingleton.elim i 0]
  right_inv _ := rfl

@[simp]
theorem Frame.equivNeZero_apply (F : Frame P H 1) : (Frame.equivNeZero F).1 = F.1 0 :=
  rfl

/-- There are `P ^ H - 1` frames of length one. -/
theorem Frame.card_one : Fintype.card (Frame P H 1) = P ^ H - 1 := by
  rw [Fintype.card_congr Frame.equivNeZero, Fintype.card_subtype_compl, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, Fintype.card_unique]

omit [Fact P.Prime] in
/-- The elementary matrix `1 + E_ab` acts on a frame of length one by the elementary move
`F ↦ F + F b • e a`. -/
theorem Frame.mapSL_transvection_apply_zero {a b : Fin H} (h : a ≠ b) (F : Frame P H 1) :
    (Frame.mapSL (SpecialLinearGroup.transvection h 1) F).1 0 =
      RotationMap.elementaryMove a b (F.1 0) := by
  rw [Frame.mapSL_apply, SpecialLinearGroup.map_transvection,
    SpecialLinearGroup.transvection_mulVec, map_one, one_mul]
  rfl

/-- A sum over the frames of length one is a sum over the nonzero vectors. -/
theorem Frame.sum_one_eq {M : Type*} [AddCommMonoid M] (Φ : (Fin H → ZMod P) → M) :
    ∑ F : Frame P H 1, Φ (F.1 0) = ∑ v, if v = 0 then 0 else Φ v := by
  calc ∑ F : Frame P H 1, Φ (F.1 0) = ∑ v : {v : Fin H → ZMod P // v ≠ 0}, Φ v.1 := by
        rw [← Equiv.sum_comp Frame.equivNeZero.symm]
        rfl
    _ = _ := by
        rw [← Finset.sum_subtype (univ.filter (· ≠ 0)) (by simp) (fun v ↦ Φ v), sum_filter]
        exact sum_congr rfl fun v _ ↦ by split_ifs <;> simp_all

/-- The masked uniform average over all vectors is a multiple of the average over the frames of
length one. -/
private theorem expect_ite_eq (Φ : (Fin H → ZMod P) → ℝ) :
    𝔼 v, (if v = 0 then 0 else Φ v) =
      (Fintype.card (Frame P H 1) / Fintype.card (Fin H → ZMod P) : ℝ) *
        𝔼 F : Frame P H 1, Φ (F.1 0) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ← Frame.sum_one_eq]
  rcases isEmpty_or_nonempty (Frame P H 1) with hF | hF
  · simp
  have hN : (0 : ℝ) < Fintype.card (Frame P H 1) := by exact_mod_cast Fintype.card_pos
  field_simp

/-- The sum over ordered pairs of distinct coordinates. -/
private theorem sum_sum_erase_eq {M : Type*} [AddCommMonoid M] (ψ : Fin H → Fin H → M) :
    ∑ a, ∑ b ∈ univ.erase a, ψ a b = ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2}, ψ p.1.1 p.1.2 := by
  rw [← Finset.sum_subtype (univ.filter fun p : Fin H × Fin H ↦ p.1 ≠ p.2) (by simp)
    (fun p ↦ ψ p.1 p.2), sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← filter_ne', sum_filter]
  exact sum_congr rfl fun b _ ↦ by simp only [ne_comm]

/-- **The Poincaré inequality for the elementary matrices on frames of length one**, for a prime
`P` and `H ≥ 3`, uniformly in `P`: every real function `g` on the frames has, about some constant,
a second moment at most `36864 H²` times its total squared change along the elementary matrices
`1 + E_ab`, `a ≠ b`. -/
theorem exists_expect_sq_sub_le_mapSL_transvection (hH : 3 ≤ H) (g : Frame P H 1 → ℝ) :
    ∃ m : ℝ, 𝔼 F, (g F - m) ^ 2 ≤ 36864 * H ^ 2 *
      ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2},
        𝔼 F, (g (Frame.mapSL (SpecialLinearGroup.transvection p.2 1) F) - g F) ^ 2 := by
  have := Frame.nonempty (P := P) (r := 1) (H := H) (by omega)
  -- `g` as a function on all vectors.
  set G : (Fin H → ZMod P) → ℝ := fun v ↦
    if h : v = 0 then 0 else g (Frame.equivNeZero.symm ⟨v, h⟩) with hG
  have hGF (F : Frame P H 1) : G (F.1 0) = g F := by
    have h := (Frame.equivNeZero F).2
    simp only [hG, Frame.equivNeZero_apply] at h ⊢
    simp only [h, dite_false]
    exact congrArg g (Frame.equivNeZero.symm_apply_apply F)
  obtain ⟨m, hm⟩ := RotationMap.exists_expect_sq_sub_le_elementaryMove hH G
  refine ⟨m, ?_⟩
  set c : ℝ := Fintype.card (Frame P H 1) / Fintype.card (Fin H → ZMod P)
  have hc : 0 < c := by
    have : (0 : ℝ) < Fintype.card (Frame P H 1) := by exact_mod_cast Fintype.card_pos
    positivity
  have hL : 𝔼 v, (if v = 0 then 0 else (G v - m) ^ 2) = c * 𝔼 F, (g F - m) ^ 2 := by
    rw [expect_ite_eq]
    simp only [hGF]
    rfl
  have hR (a b : Fin H) (h : a ≠ b) :
      𝔼 v, (G (RotationMap.elementaryMove a b v) - G v) ^ 2 =
        c * 𝔼 F, (g (Frame.mapSL (SpecialLinearGroup.transvection h 1) F) - g F) ^ 2 := by
    have h0 (v : Fin H → ZMod P) : (G (RotationMap.elementaryMove a b v) - G v) ^ 2 =
        if v = 0 then 0 else (G (RotationMap.elementaryMove a b v) - G v) ^ 2 := by
      split_ifs with hv
      · subst hv
        simp [RotationMap.elementaryMove]
      · rfl
    rw [expect_congr rfl fun v _ ↦ h0 v, expect_ite_eq]
    simp only [← Frame.mapSL_transvection_apply_zero h, hGF]
    rfl
  rw [hL, sum_sum_erase_eq (fun a b ↦ 𝔼 v, (G (RotationMap.elementaryMove a b v) - G v) ^ 2)]
    at hm
  have hsum : ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2},
      𝔼 v, (G (RotationMap.elementaryMove p.1.1 p.1.2 v) - G v) ^ 2 =
        c * ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2},
          𝔼 F, (g (Frame.mapSL (SpecialLinearGroup.transvection p.2 1) F) - g F) ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ ↦ hR _ _ p.2
  rw [hsum, mul_left_comm] at hm
  exact le_of_mul_le_mul_left hm hc

end FrameOne

/-! ### The affine moves -/

variable (H) in
/-- **The generators of the affine walk**: the elementary matrices `1 + E_ab` for `a ≠ b`, and
the unit translations by `e_i`. -/
@[expose] def affineGenerator :
    {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H → SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ) :=
  Sum.elim (fun p ↦ (SpecialLinearGroup.transvection p.2 1, 0)) fun i ↦ (1, Pi.single i 1)

variable (P H L) in
/-- **The affine moves on slice coordinates** `(F, w)`: the moves `coordMove` of the generators,
`(F, w) ↦ ((1 + E_ab) F, (1 + E_ab) w)` and `(F, w) ↦ (F, w + e_i)`. -/
@[expose] def affineMove (r : ℕ) (k : {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) :
    Equiv.Perm (Frame P H r × (Fin H → ZMod L)) :=
  coordMove (affineGenerator H k).1 (affineGenerator H k).2

@[simp]
theorem affineMove_inl {r : ℕ} (p : {p : Fin H × Fin H // p.1 ≠ p.2})
    (q : Frame P H r × (Fin H → ZMod L)) :
    affineMove P H L r (.inl p) q =
      (Frame.mapSL (SpecialLinearGroup.transvection p.2 1) q.1,
        update q.2 p.1.1 (q.2 p.1.1 + q.2 p.1.2)) := by
  simp only [affineMove, affineGenerator, coordMove, Sum.elim_inl, Equiv.prodCongr_apply,
    Prod.map, affineSL_apply, SpecialLinearGroup.map_transvection,
    SpecialLinearGroup.transvection_mulVec, map_one, one_mul]
  exact Prod.ext rfl (funext fun _ ↦ by simp)

@[simp]
theorem affineMove_inr {r : ℕ} (i : Fin H) (q : Frame P H r × (Fin H → ZMod L)) :
    affineMove P H L r (.inr i) q = (q.1, update q.2 i (q.2 i + 1)) := by
  obtain ⟨F, w⟩ := q
  ext j
  · simp [affineMove, affineGenerator, coordMove]
  · simp only [affineMove, affineGenerator, coordMove, Sum.elim_inr, Equiv.prodCongr_apply,
      Prod.map_snd, affineSL_apply, map_one, SpecialLinearGroup.coe_one, one_mulVec, Pi.add_apply,
      update_apply]
    split_ifs with h
    · subst h
      simp
    · simp [h]

/-- There are `H ^ 2` generators: `H (H - 1)` elementary matrices and `H` translations. -/
theorem card_affineGenerator_index :
    Fintype.card ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) = H ^ 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype]
  have : (univ.filter fun p : Fin H × Fin H ↦ p.1 ≠ p.2) = (univ : Finset (Fin H)).offDiag := by
    ext p
    simp
  rw [this, offDiag_card, card_univ, Fintype.card_fin]
  have : H ≤ H * H := Nat.le_mul_self H
  rw [Nat.sub_add_cancel this, sq]

/-- Averaging over the second coordinate contracts the squared change along a product
permutation. -/
private theorem sq_expect_sub_expect_le {Y W : Type*} [Fintype W] (π : Equiv.Perm Y)
    (τ : Equiv.Perm W) (f : Y × W → ℝ) (y : Y) :
    (𝔼 w, f (π y, w) - 𝔼 w, f (y, w)) ^ 2 ≤ 𝔼 w, (f (π.prodCongr τ (y, w)) - f (y, w)) ^ 2 := by
  have h : 𝔼 w, f (π y, w) = 𝔼 w, f (π y, τ w) :=
    (Fintype.expect_equiv τ (fun w ↦ f (π y, τ w)) (fun w ↦ f (π y, w)) fun _ ↦ rfl).symm
  rw [h, ← expect_sub_distrib]
  exact sq_expect_le_expect_sq univ _

/-- **The Poincaré inequality for the affine walk on slice coordinates** `Frame P H 1 × ZMod L ^ H`,
for a prime `P` and `H ≥ 3`, uniformly in `P` and `L`: every real function `f` of mean zero has
second moment at most `38912 H²` times its total squared change along the affine moves. -/
theorem expect_sq_le_affineMove [Fact P.Prime] [NeZero L] (hH : 3 ≤ H)
    (f : Frame P H 1 × (Fin H → ZMod L) → ℝ) (hf : 𝔼 p, f p = 0) :
    𝔼 p, f p ^ 2 ≤ 38912 * H ^ 2 * ∑ k, 𝔼 p, (f (affineMove P H L 1 k p) - f p) ^ 2 := by
  have := Frame.nonempty (P := P) (r := 1) (H := H) (by omega)
  set D := ∑ k, 𝔼 p, (f (affineMove P H L 1 k p) - f p) ^ 2
  have hD0 : 0 ≤ D := sum_nonneg fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _
  have hterm (k) : 𝔼 p, (f (affineMove P H L 1 k p) - f p) ^ 2 ≤ D :=
    single_le_sum (f := fun k ↦ 𝔼 p, (f (affineMove P H L 1 k p) - f p) ^ 2)
      (fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ k)
  -- Split `f` into its averages `g` over the box coordinate and the rest.
  set g : Frame P H 1 → ℝ := fun F ↦ 𝔼 w, f (F, w) with hg
  have hsplit : 𝔼 p, f p ^ 2 = 𝔼 F, g F ^ 2 + 𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 := by
    have h := Fintype.expect_add_sq_of_expect_fiber_eq_zero g
      (g := fun p ↦ f p - g p.1) (Fintype.expect_sub_expect_fiber f)
    simpa only [add_sub_cancel, Fintype.expect_prod_type, Fintype.expect_const] using h
  -- The box part, by the coordinate-pair bound with partners `σ i ≠ i`.
  have hH2 : Nontrivial (Fin H) := Fin.nontrivial_iff_two_le.2 (by omega)
  choose σ hσ using fun i : Fin H ↦ exists_ne i
  let ρ : Fin H → Fin H → Equiv.Perm (Frame P H 1) := fun i j ↦
    if h : i = j then Equiv.refl _ else Frame.mapSL (SpecialLinearGroup.transvection h 1)
  have hρ {i j : Fin H} (h : i ≠ j) :
      ρ i j = Frame.mapSL (SpecialLinearGroup.transvection h 1) := by
    simp [ρ, h]
  have hpair (i : Fin H) (k : Fin 4) :
      𝔼 p, (f (RotationMap.pairShearTranslationMove (ρ i (σ i)) (ρ (σ i) i) i (σ i) k p) -
        f p) ^ 2 ≤ D := by
    have hσi : i ≠ σ i := (hσ i).symm
    fin_cases k
    · refine le_trans (le_of_eq ?_) (hterm (.inl ⟨(i, σ i), hσi⟩))
      refine expect_congr rfl fun p _ ↦ ?_
      simp [RotationMap.pairShearTranslationMove, hρ hσi]
    · refine le_trans (le_of_eq ?_) (hterm (.inl ⟨(σ i, i), hσi.symm⟩))
      refine expect_congr rfl fun p _ ↦ ?_
      simp [RotationMap.pairShearTranslationMove, hρ hσi.symm]
    · refine le_trans (le_of_eq ?_) (hterm (.inr i))
      refine expect_congr rfl fun p _ ↦ ?_
      simp [RotationMap.pairShearTranslationMove]
    · refine le_trans (le_of_eq ?_) (hterm (.inr (σ i)))
      refine expect_congr rfl fun p _ ↦ ?_
      simp [RotationMap.pairShearTranslationMove]
  have hbox : 𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 ≤ 2048 * H * D := by
    refine (RotationMap.expect_sq_sub_expect_le_pairShearTranslation ρ σ (fun i ↦ hσ i) f).trans ?_
    calc 512 * ∑ i, ∑ k, 𝔼 p, (f (RotationMap.pairShearTranslationMove (ρ i (σ i)) (ρ (σ i) i)
          i (σ i) k p) - f p) ^ 2 ≤ 512 * ∑ _i : Fin H, ∑ _k : Fin 4, D := by
          gcongr with i _ k _
          exact hpair i k
      _ = 2048 * H * D := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  -- The frame part, by the Poincaré inequality on frames and Jensen's inequality.
  obtain ⟨m, hm⟩ := exists_expect_sq_sub_le_mapSL_transvection hH g
  have hg0 : 𝔼 F, g F = 0 := by rw [← Fintype.expect_prod_type]; exact hf
  have hgm : 𝔼 F, g F ^ 2 ≤ 𝔼 F, (g F - m) ^ 2 := by
    have : 𝔼 F, (g F - m) ^ 2 = 𝔼 F, g F ^ 2 + m ^ 2 := by
      have h1 : 𝔼 F, (g F - m) ^ 2 = 𝔼 F, (g F ^ 2 + m ^ 2) - 2 * m * 𝔼 F, g F := by
        rw [mul_expect, ← expect_sub_distrib]
        exact expect_congr rfl fun F _ ↦ by ring
      rw [h1, hg0, expect_add_distrib, Fintype.expect_const]
      ring
    rw [this]
    nlinarith [sq_nonneg m]
  have hframe : ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2},
      𝔼 F, (g (Frame.mapSL (SpecialLinearGroup.transvection p.2 1) F) - g F) ^ 2 ≤ D := by
    calc _ ≤ ∑ p : {p : Fin H × Fin H // p.1 ≠ p.2},
          𝔼 q, (f (affineMove P H L 1 (.inl p) q) - f q) ^ 2 := by
          refine sum_le_sum fun p _ ↦ ?_
          rw [Fintype.expect_prod_type]
          exact expect_le_expect fun F _ ↦ sq_expect_sub_expect_le _ _ f F
      _ ≤ D := by
          refine le_trans ?_ (Fintype.sum_sum_type _).symm.le
          exact le_add_of_nonneg_right
            (sum_nonneg fun _ _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _)
  have hHD : (H : ℝ) * D ≤ H ^ 2 * D := by
    have : (H : ℝ) ≤ H ^ 2 := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hD0
  have hHsq : (0 : ℝ) ≤ H ^ 2 := sq_nonneg _
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hframe (by positivity : (0 : ℝ) ≤ 36864 * H ^ 2)]


/-- For `H ≥ 2` there are at least two frames of length one. -/
private theorem nontrivial_frame_one [Fact P.Prime] (hH : 2 ≤ H) : Nontrivial (Frame P H 1) := by
  have h0 : (Pi.single ⟨0, by omega⟩ 1 : Fin H → ZMod P) ≠ 0 := by simp
  have h1 : (Pi.single ⟨1, by omega⟩ 1 : Fin H → ZMod P) ≠ 0 := by simp
  refine ⟨Frame.equivNeZero.symm ⟨_, h0⟩, Frame.equivNeZero.symm ⟨_, h1⟩, fun h ↦ ?_⟩
  have := congrFun (congrArg Subtype.val (Frame.equivNeZero.symm.injective h)) ⟨0, by omega⟩
  simp [Fin.ext_iff] at this

/-- **The second eigenvalue of the affine walk** on slice coordinates
`Frame P H 1 × ZMod L ^ H` is at most `1 - 1 / (77824 H ^ 4)`, for a prime `P` and `H ≥ 3`,
uniformly in `P` and `L`. -/
theorem secondEigenvalue_ofPerms_affineMove_le [Fact P.Prime] [NeZero L] (hH : 3 ≤ H) :
    (ofPerms (affineMove P H L 1)).secondEigenvalue ≤ 1 - 1 / (77824 * H ^ 4) := by
  have := nontrivial_frame_one (P := P) (H := H) (by omega)
  have : Nonempty ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) := ⟨.inr ⟨0, by omega⟩⟩
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have h := secondEigenvalue_ofPerms_le (affineMove P H L 1) (c := 1 / (38912 * H ^ 2))
    fun f hf ↦ by
      have := expect_sq_le_affineMove hH f hf
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      linarith
  refine h.trans_eq ?_
  rw [card_affineGenerator_index]
  push_cast
  field_simp
  ring

/-- **The spectral gap of the lazy affine walk** on slice coordinates `Frame P H 1 × ZMod L ^ H`:
its spectral expansion is at most `1 - 1 / (155648 H ^ 4)`, for a prime `P` and `H ≥ 3`,
uniformly in `P` and `L`. -/
theorem spectralExpansion_lazy_ofPerms_affineMove_le [Fact P.Prime] [NeZero L] (hH : 3 ≤ H) :
    (ofPerms (affineMove P H L 1)).lazy.spectralExpansion ≤ 1 - 1 / (155648 * H ^ 4) := by
  have h₁ :=
    (ofPerms (affineMove P H L 1)).spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two
  have h₂ := secondEigenvalue_ofPerms_affineMove_le (P := P) (L := L) hH
  have : 1 / (155648 * (H : ℝ) ^ 4) = (1 / (77824 * H ^ 4)) / 2 := by
    rw [div_div]
    ring
  rw [this]
  linarith

/-- **Conditional averaging with the affine walk**: on the retention slice of every identifier
`y`, `t` steps of the lazy affine walk contract the conditional variance by
`(1 - 1 / (155648 H ^ 4)) ^ (2 t)`, for a prime `P`, `H ≥ 3` and `1 ≤ L ≤ P`, uniformly in `P`,
`L` and `y`. This discharges the gap hypothesis of
`expect_walk_pow_sliceGraph_sub_expect_sq_le` for frames of length one. -/
theorem expect_walk_pow_sliceGraph_affineMove_sub_expect_sq_le [Fact P.Prime] [NeZero L]
    (hH : 3 ≤ H) (hL : L ≤ P) (y : ZMod P) (f : RetentionSlice P H 1 L y → ℝ) (t : ℕ) :
    𝔼 A, (((sliceGraph L hL y (ofPerms (affineMove P H L 1)).lazy).walk ^ t) f A - 𝔼 B, f B) ^ 2 ≤
      (1 - 1 / (155648 * H ^ 4)) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  have : Nonempty ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) := ⟨.inr ⟨0, by omega⟩⟩
  exact expect_walk_pow_sliceGraph_sub_expect_sq_le hL _
    (spectralExpansion_lazy_ofPerms_affineMove_le hH) y f t

end Cslib.Probability
