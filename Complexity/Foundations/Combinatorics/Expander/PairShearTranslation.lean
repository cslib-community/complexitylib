/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.RelativeShearTranslation
import Complexity.Foundations.Probability.EfronStein

/-!
# Shears and translations of coordinate pairs

Let `Y` be a finite set and consider functions on `Y × (Fin H → ZMod L)`. For a pair `i ≠ j` of
coordinates, the elementary moves are (`pairShearTranslationMove`): the elementary shears
`w ↦ w + w j • e i` and `w ↦ w + w i • e j`, which also act on `Y` by given permutations `ρ`, `ρ'`,
and the unit translations `w ↦ w + e i` and `w ↦ w + e j`. These are the moves of the elementary
matrices of `SL_H(ℤ)` and of the unit translations on a retention slice `Frame P H r × (ZMod L)^H`,
where `ρ` is the action of the same elementary matrix on the frames.

The second moment of `f` about its average over the whole tuple `w` is at most `512` times the sum,
over the coordinates `i`, of the total squared change of `f` along the moves of a pair `(i, σ i)`
with `σ i ≠ i` (`expect_sq_sub_expect_le_pairShearTranslation`). Such a `σ` exists only when
`H ≠ 1`; for `H = 1` the hypothesis cannot hold, and the bound says nothing. The proof combines:

* the Efron–Stein inequality (`Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update`), which
  reduces the distance from the functions of `y` alone to the distances from the functions not
  depending on one coordinate `w i`;
* the best-approximation property of the average over `w i`
  (`Fintype.expect_sq_sub_expect_update_le`), which bounds that distance by the distance from the
  average over the pair `(w i, w j)`;
* the relative Poincaré inequality with a spectator
  (`expect_sq_sub_expect_fiber_le_twistedShearTranslation`), applied to `f` with the pair
  `(w i, w j)` resampled and everything else as the spectator
  (`expect_sq_sub_expect_update_le_pairShearTranslation`).

This is the step from the coordinate-pair projections `P_ij` to the projection onto the vectors
fixed by all translations in the OpenAI preprint on derandomizing logarithmic space
[OpenAI, proof of Lemma 6.1][OpenAI2026LogSpace], where the commuting projections are telescoped;
here the Efron–Stein inequality takes the place of the telescoping. The elementary lift of the
relative gap to frames is in OpenAI's Lean development, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc` (`slice_frame`, `frame_gap`, `slice_gap`). The statements and the proof here
are independent of that code, which was not consulted.

## Main definitions

* `Cslib.RotationMap.pairShearTranslationMove`: the four moves of a coordinate pair.

## Main results

* `Cslib.RotationMap.expect_sq_sub_expect_update_le_pairShearTranslation`: one coordinate, from
  the moves of a pair containing it.
* `Cslib.RotationMap.expect_sq_sub_expect_le_pairShearTranslation`: all coordinates.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

open Finset Function
open scoped BigOperators

namespace Cslib.RotationMap

variable {Y : Type*} [Fintype Y] {H L : ℕ}

/-- The four moves of the coordinate pair `(i, j)` on `Y × (Fin H → ZMod L)`: the elementary
shears `w ↦ w + w j • e i` (with `ρ` on `Y`) and `w ↦ w + w i • e j` (with `ρ'` on `Y`), and the
unit translations `w ↦ w + e i` and `w ↦ w + e j`. -/
@[expose]
def pairShearTranslationMove (ρ ρ' : Equiv.Perm Y) (i j : Fin H) :
    Fin 4 → Y × (Fin H → ZMod L) → Y × (Fin H → ZMod L) :=
  ![fun p ↦ (ρ p.1, update p.2 i (p.2 i + p.2 j)), fun p ↦ (ρ' p.1, update p.2 j (p.2 j + p.2 i)),
    fun p ↦ (p.1, update p.2 i (p.2 i + 1)), fun p ↦ (p.1, update p.2 j (p.2 j + 1))]

/-- Overwriting the coordinates `i` and then `j` of `w`. -/
private abbrev upd2 (i j : Fin H) (w : Fin H → ZMod L) (a b : ZMod L) : Fin H → ZMod L :=
  update (update w i a) j b

omit [Fintype Y] in
private theorem upd2_upd2 (i j : Fin H) (w : Fin H → ZMod L) (a b a' b' : ZMod L) :
    upd2 i j (upd2 i j w a b) a' b' = upd2 i j w a' b' := by
  funext k
  simp only [upd2, update_apply]
  split_ifs <;> simp_all

omit [Fintype Y] in
private theorem update_upd2_fst {i j : Fin H} (hij : i ≠ j) (w : Fin H → ZMod L) (a b c : ZMod L) :
    update (upd2 i j w a b) i c = upd2 i j w c b := by
  funext k
  simp only [upd2, update_apply]
  split_ifs <;> simp_all

omit [Fintype Y] in
private theorem upd2_apply_fst {i j : Fin H} (hij : i ≠ j) (w : Fin H → ZMod L) (a b : ZMod L) :
    upd2 i j w a b i = a := by
  simp [upd2, hij]

variable [NeZero L]

/-- Resampling the pair `(i, j)` of a uniformly random tuple keeps it uniformly random. -/
private theorem expect_upd2 (i j : Fin H) (Φ : Y × (Fin H → ZMod L) → ℝ) :
    𝔼 q : (Y × (Fin H → ZMod L)) × (ZMod L × ZMod L), Φ (q.1.1, upd2 i j q.1.2 q.2.1 q.2.2) =
      𝔼 p, Φ p := by
  rw [Fintype.expect_prod_type, Fintype.expect_prod_type, Fintype.expect_prod_type]
  refine expect_congr rfl fun y _ ↦ ?_
  simp only [Fintype.expect_prod_type, upd2]
  rw [Fintype.expect_expect_update (fun s ↦ 𝔼 b, Φ (y, update s j b)) i,
    Fintype.expect_expect_update (fun s ↦ Φ (y, s)) j]

/-- **One coordinate, from the moves of a pair containing it**: the second moment of `f` about its
average over `w i` is at most `512` times the total squared change of `f` along the four moves of
the pair `(i, j)`, for `i ≠ j`. -/
theorem expect_sq_sub_expect_update_le_pairShearTranslation (ρ ρ' : Equiv.Perm Y) {i j : Fin H}
    (hij : i ≠ j) (f : Y × (Fin H → ZMod L) → ℝ) :
    𝔼 p, (f p - 𝔼 a, f (p.1, update p.2 i a)) ^ 2 ≤
      512 * ∑ k, 𝔼 p, (f (pairShearTranslationMove ρ ρ' i j k p) - f p) ^ 2 := by
  -- The average over the pair `(w i, w j)`.
  set G : Y × (Fin H → ZMod L) → ℝ := fun p ↦ 𝔼 a, 𝔼 b, f (p.1, upd2 i j p.2 a b) with hG
  have hGinv (p : Y × (Fin H → ZMod L)) (a b : ZMod L) : G (p.1, upd2 i j p.2 a b) = G p := by
    simp only [hG, upd2_upd2]
  refine (Fintype.expect_sq_sub_expect_update_le i f G fun p c ↦ ?_).trans ?_
  · have := hGinv p c (update p.2 i c j)
    simpa only [upd2, update_eq_self] using this
  -- The relative Poincaré inequality, with everything but the pair as the spectator.
  set F : (Y × (Fin H → ZMod L)) × (ZMod L × ZMod L) → ℝ :=
    fun q ↦ f (q.1.1, upd2 i j q.1.2 q.2.1 q.2.2) with hF
  have hA := expect_sq_sub_expect_fiber_le_twistedShearTranslation
    (ρ.prodCongr (Equiv.refl _)) (ρ'.prodCongr (Equiv.refl _)) F
  have hL : 𝔼 q, (F q - 𝔼 v, F (q.1, v)) ^ 2 = 𝔼 p, (f p - G p) ^ 2 := by
    rw [← expect_upd2 i j fun p ↦ (f p - G p) ^ 2]
    refine expect_congr rfl fun q _ ↦ ?_
    rw [hGinv]
    simp only [hF, hG, Fintype.expect_prod_type]
  have hR (k : Fin 4) : 𝔼 q, (F (twistedShearTranslationMove (ρ.prodCongr (Equiv.refl _))
      (ρ'.prodCongr (Equiv.refl _)) L k q) - F q) ^ 2 =
      𝔼 p, (f (pairShearTranslationMove ρ ρ' i j k p) - f p) ^ 2 := by
    rw [← expect_upd2 i j fun p ↦ (f (pairShearTranslationMove ρ ρ' i j k p) - f p) ^ 2]
    refine expect_congr rfl fun q _ ↦ ?_
    obtain ⟨⟨y, w⟩, a, b⟩ := q
    fin_cases k <;>
      simp [hF, twistedShearTranslationMove, pairShearTranslationMove, shearFst_apply,
        shearSnd_apply, upd2_apply_fst hij, update_upd2_fst hij, upd2]
  rw [hL] at hA
  refine hA.trans_eq ?_
  simp only [hR]

/-- **All coordinates, from the moves of coordinate pairs**: if `σ i ≠ i` for every coordinate `i`,
the second moment of `f` about its average over the whole tuple is at most `512` times the sum over
`i` of the total squared change of `f` along the four moves of the pair `(i, σ i)`, where `ρ i j`
acts on `Y` with the shear `w ↦ w + w j • e i`. -/
theorem expect_sq_sub_expect_le_pairShearTranslation {Y : Type} [Fintype Y]
    (ρ : Fin H → Fin H → Equiv.Perm Y) (σ : Fin H → Fin H) (hσ : ∀ i, σ i ≠ i)
    (f : Y × (Fin H → ZMod L) → ℝ) :
    𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 ≤
      512 * ∑ i, ∑ k, 𝔼 p,
        (f (pairShearTranslationMove (ρ i (σ i)) (ρ (σ i) i) i (σ i) k p) - f p) ^ 2 := by
  refine (Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update f).trans ?_
  rw [mul_sum]
  exact sum_le_sum fun i _ ↦
    expect_sq_sub_expect_update_le_pairShearTranslation _ _ (hσ i).symm f

end Cslib.RotationMap
