/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.StochasticAtom
public import Complexity.Probability.PairwiseIndependentHash.RetentionChannel

/-!
# Dense atoms over affine channels at two rates

A dense atom (`Matrix.denseAtom`) ranks its row over a channel at the atom's scale `f` and is
masked by a *usage* channel at a lower rate `t ≤ f` [OpenAI2026LogSpace, (5.11)]. For the affine
retention channels over `𝔽_P` both are one seed with two boxes: the usage channel has a smaller
side `L_t ≤ ⌈P a⌉`. So it retains a subset (`Cslib.Probability.affineRetains_of_le`). Given that
the usage channel retains `y`, another identifier `w` is retained at rate `f = a ^ H` with
probability at most `2 ^ H f`, by pairwise independence at two rates
(`Cslib.Probability.card_affineRetains_and_affineRetains_le`). This is the cross-rate pair bound
of [OpenAI2026LogSpace, Lemma 3.1] used in the proof of Lemma 5.1. With it, the dense atom
identity holds for these channels at two rates (`Cslib.Probability.expect_denseAtom_affineRetains`).

## Main results

* `Cslib.Probability.card_filter_and_le_of_dens_le`: a conditional probability bound as a count.
* `Cslib.Probability.card_affineRetains_and_affineRetains_le`: the cross-rate pair bound.
* `Cslib.Probability.expect_denseAtom_affineRetains`: the dense atom identity at two rates.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 3.1 and Lemma 5.1 (preprint, not peer reviewed)
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

variable {V : Type*} {P H : ℕ} [Fact P.Prime]

omit [Fact P.Prime] in
/-- A **conditional probability bound as a count**: if `Pr[B ∧ A] ≤ q Pr[A]` for uniform seeds,
then among the seeds satisfying `A`, at most a `q` fraction also satisfy `B`. -/
theorem card_filter_and_le_of_dens_le {Ω : Type*} [Fintype Ω] {A B : Ω → Prop} [DecidablePred A]
    [DecidablePred B] {q : ℝ} (h : (dens {t | B t ∧ A t} : ℝ) ≤ q * dens {t | A t}) :
    (#{t | A t ∧ B t} : ℝ) ≤ q * #{t | A t} := by
  have hcard : ∀ T : Finset Ω, ((dens T : ℚ≥0) : ℝ) = #T / Fintype.card Ω := fun T => by
    rw [dens_eq_card_div_card]; push_cast; rfl
  rw [hcard, hcard, ← mul_div_assoc] at h
  have hset : ({t | A t ∧ B t} : Finset Ω) = ({t | B t ∧ A t} : Finset Ω) :=
    filter_congr fun _ _ => and_comm
  rw [hset]
  rcases (Fintype.card Ω).eq_zero_or_pos with h0 | h0
  · have : (univ : Finset Ω) = ∅ := univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp h0)
    simp [this]
  · exact (div_le_div_iff_of_pos_right (by exact_mod_cast h0)).mp h

/-- **The cross-rate pair bound for affine channels.** Let `ident : V → ZMod P` be injective,
`1 ≤ P a`, `a ≤ 1`, and `L_t ≤ P`. Among the seeds whose box of side `L_t` retains `y`, those
whose box of side `⌈P a⌉` also retains `w ≠ y` form at most a `2 ^ H a ^ H` fraction. -/
theorem card_affineRetains_and_affineRetains_le {ident : V → ZMod P}
    (hident : Function.Injective ident) {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) {Lt : ℕ}
    (hLt : Lt ≤ P) {w y : V} (hwy : w ≠ y) :
    (#{s | affineRetains P H Lt s (ident y) ∧ affineRetains P H ⌈P * a⌉₊ s (ident w)} : ℝ) ≤
      2 ^ H * a ^ H * #{s | affineRetains P H Lt s (ident y)} := by
  obtain ⟨hL, -, hup, -, -⟩ := affineRetains_rates (H := H) hPa ha
  refine card_filter_and_le_of_dens_le ?_
  rw [dens_affineRetains_and_affineRetains hL hLt (hident.ne hwy), dens_affineRetains hLt]
  push_cast
  exact mul_le_mul_of_nonneg_right hup (by positivity)

/-- **The dense atom identity for affine channels at two rates** [OpenAI2026LogSpace, Lemma 5.1].
The rank channel retains with side `⌈P a⌉` (rate `f = a ^ H`), the usage channel with a side
`0 < L_t ≤ ⌈P a⌉`. For every nonnegative row of mass at most `M`, the conditional mean of the
dense atom given the usage channel is `k (G x y / f)`, once `K ≥ 2 (1 + 2 ^ H M / η)`. -/
theorem expect_denseAtom_affineRetains [Fintype V] {ident : V → ZMod P}
    (hident : Function.Injective ident) {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) {Lt : ℕ}
    (hLt0 : 0 < Lt) (hLt : Lt ≤ ⌈P * a⌉₊) {k h ρ : ℝ → ℝ} {K : ℕ} {G : Matrix V V ℝ} {x y : V}
    (hkh : ∀ d, k d ≠ 0 → h d = 1) (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ r, r ≤ η → ρ r = 1) (hG0 : ∀ w, 0 ≤ G x w) {M : ℝ}
    (hGM : ∑ w, G x w ≤ M) (hK : 2 * (1 + 2 ^ H * M / η) ≤ K) :
    𝔼 s ∈ ({s | affineRetains P H Lt s (ident y)} :
        Finset (Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P))),
      Matrix.denseAtom (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
        (fun s v => affineRetains P H Lt s (ident v)) k h ρ K (a ^ H) G s x y =
      k (G x y / a ^ H) := by
  obtain ⟨hL, -, -, -, -⟩ := affineRetains_rates (H := H) hPa ha
  have hLtP : Lt ≤ P := hLt.trans hL
  have ha0 : 0 < a := by
    by_contra h0
    have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hP (not_lt.mp h0)]
  have hS : ({s | affineRetains P H Lt s (ident y)} :
      Finset (Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P))).Nonempty := by
    rw [← card_pos]
    by_contra h0
    have h := dens_affineRetains (H := H) hLtP (ident y)
    rw [dens_eq_card_div_card, Nat.eq_zero_of_not_pos h0, Nat.cast_zero, zero_div] at h
    have : (0 : ℚ≥0) < ((Lt : ℚ≥0) / P) ^ H := by
      have : (0 : ℚ≥0) < P := by exact_mod_cast (Fact.out : P.Prime).pos
      positivity
    exact absurd h this.ne
  have hp : ∀ w, w ≠ y → (#{s | affineRetains P H Lt s (ident y) ∧
      affineRetains P H ⌈P * a⌉₊ s (ident w)} : ℝ) ≤
      2 ^ H * a ^ H * #{s | affineRetains P H Lt s (ident y)} := fun w hwy =>
    card_affineRetains_and_affineRetains_le hident hPa ha hLtP hwy
  exact Matrix.expect_denseAtom (Y := fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
    (Yt := fun s v => affineRetains P H Lt s (ident v)) (c := 2 ^ H) hS hkh hρ0 hρ1 hη hρη
    (pow_pos ha0 H) hG0 hGM (by positivity) hK hp

end Cslib.Probability
