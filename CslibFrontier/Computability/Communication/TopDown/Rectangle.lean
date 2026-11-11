/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.RoundProtocol
public import CslibFrontier.Foundations.BooleanAnalysis.MirrorSets
import Mathlib.Tactic.Linarith

/-!
# Density rectangles

The invariant of Korten's top-down adversary [Korten, Sections 3 and 4][Korten2026] is a
*density rectangle* `X × Y` (`DensityRectangle`): two nonempty sets of deficit at most `k`, one of
which consists of `(r, k)`-limits of the other for some rate `0 < r ≤ p`. The rate may be smaller
than `p`, since density limits need not be monotone in the rate. A density rectangle of rate
below `3 / 4` is not separated by any coordinate (`DensityRectangle.not_separated`), and after a
message of `m` bits from Alice, some message leaves a density rectangle with deficit
`max (194 k) (2 k + 2 + m)` and rate `32768 k p` (`DensityRectangle.select_left_message`): the
strong mirror-set lemma (`Cslib.BitString.exists_mirror_set`) turns the limits around when
they face the wrong player.

## Main definitions

* `Cslib.Communication.DensityRectangle`: density rectangles.

## Main results

* `Cslib.Communication.DensityRectangle.not_separated`: no coordinate separates a density
  rectangle.
* `Cslib.Communication.DensityRectangle.select_left_message`: a message keeps a density rectangle.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Communication

open Cslib.BitString Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A *density rectangle* `X × Y` of rate `p` and deficit `k`: `X` and `Y` are nonempty of deficit
at most `k`, and for some rate `0 < r ≤ p`, the points of one of them are `(r, k)`-limits of the
other. -/
def DensityRectangle (X Y : Finset (ι → Bool)) (p k : ℝ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧ uniformDeficit X ≤ k ∧ uniformDeficit Y ≤ k ∧
    ∃ r : ℝ, 0 < r ∧ r ≤ p ∧
      ((∀ x ∈ X, IsDensityLimit Y r k x) ∨ (∀ y ∈ Y, IsDensityLimit X r k y))

/-- Density rectangles are symmetric. -/
theorem DensityRectangle.swap {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) : DensityRectangle Y X p k := by
  rcases h with ⟨hX, hY, hdX, hdY, r, hr, hrp, hl | hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inr hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inl hl⟩

/-- No coordinate separates a density rectangle of rate below `3 / 4`. -/
theorem DensityRectangle.not_separated {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) (hp : p < 3 / 4) (i : ι) :
    ¬ ∀ x ∈ X, ∀ y ∈ Y, x i ≠ y i := by
  intro hsep
  rcases h with ⟨hX, hY, _, _, r, hr, hrp, hl | hl⟩
  · obtain ⟨x, hx⟩ := hX
    obtain ⟨y, hy, he⟩ := (hl x hx).exists_mem_apply_eq hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he.symm
  · obtain ⟨y, hy⟩ := hY
    obtain ⟨x, hx, he⟩ := (hl y hy).exists_mem_apply_eq hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he

/-- **One message keeps a density rectangle**: if Alice sends one of at most `2 ^ m` messages, some
message leaves a density rectangle of rate `p'` and deficit `k'`, for `k ≥ 1`, `k' ≥ 194 k`,
`k' ≥ 2 k + 2 + m` and `32768 k p ≤ p' ≤ 1 / 4`. -/
theorem DensityRectangle.select_left_message {M : Type*} [Fintype M]
    {X Y : Finset (ι → Bool)} {p p' k k' m : ℝ} (h : DensityRectangle X Y p k)
    (send : (ι → Bool) → M) (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m)
    (hk : 1 ≤ k) (hkk : 194 * k ≤ k') (hcost : 2 * k + 2 + m ≤ k')
    (hscale : 32768 * k * p ≤ p') (hp' : p' ≤ 1 / 4) :
    ∃ (a : M) (X' : Finset (ι → Bool)), X' ⊆ X ∧ (∀ x ∈ X', send x = a) ∧
      DensityRectangle X' Y p' k' := by
  classical
  rcases h with ⟨hX, hY, hdX, hdY, r, hr, hrp, hl⟩
  have hkmono : k ≤ k' := by linarith
  have hp0 : 0 ≤ p := hr.le.trans hrp
  have hpmono : p ≤ p' := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hk)]
  have hselect (Z : Finset (ι → Bool)) (hZX : Z ⊆ X) (hZ : Z.Nonempty)
      (hdef : uniformDeficit Z + m ≤ k') (s : ℝ) (hs : 0 < s) (hsp : s ≤ p')
      (hlim : ∀ z ∈ Z, IsDensityLimit Y s k' z) :
      ∃ (a : M) (X' : Finset (ι → Bool)), X' ⊆ X ∧ (∀ x ∈ X', send x = a) ∧
        DensityRectangle X' Y p' k' := by
    obtain ⟨a, hne, hd⟩ := exists_uniformDeficit_fiber_le Z hZ send hM
    refine ⟨a, Z.filter (fun x => send x = a), (filter_subset _ _).trans hZX,
      (fun x hx => (mem_filter.mp hx).2), hne, hY, hd.trans hdef, hdY.trans hkmono,
      s, hs, hsp, Or.inl ?_⟩
    exact fun x hx => hlim x (mem_filter.mp hx).1
  rcases hl with hl | hl
  · apply hselect X (Subset.refl _) hX (by linarith) r hr (hrp.trans hpmono)
    intro x hx
    exact (hl x hx).mono_right hr.le (by linarith [hrp.trans hpmono]) hkmono
  · let q := 32768 * k * r
    have hqpos : 0 < q := by dsimp [q]; positivity
    have hqp : q ≤ p' :=
      (mul_le_mul_of_nonneg_left hrp (show 0 ≤ 32768 * k by positivity)).trans hscale
    obtain ⟨Z, hZX, hZ, hdef, hlim⟩ := exists_mirror_set Y X hY hk hdY hr rfl
      (show q ≤ 1 / 2 by linarith) hl
    apply hselect Z hZX hZ (by linarith) q hqpos hqp
    intro z hz
    exact (hlim z hz).mono_right hqpos.le (by linarith) hkk

end Cslib.Communication
