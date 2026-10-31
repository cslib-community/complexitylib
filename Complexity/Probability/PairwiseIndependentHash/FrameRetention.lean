/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ColumnDetector
public import Complexity.Probability.PairwiseIndependentHash.FrameChannel
import Complexity.Probability.PairwiseIndependentHash.Shift
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Retention estimates for frame-conditioned channels

A frame-conditioned channel `A = (a₀, F)` (`Cslib.Probability.FrameChannel`) is a uniformly random
polynomial channel `y ↦ a₀ + ∑ j, y ^ (j + 1) • M j` conditioned on its coefficient columns `M`
forming a frame, i.e. being linearly independent. Its single evaluations have the exact
retention probability `(L / P) ^ H` (`dens_eval_mem_retentionBox`). Here we prove the pair and
lower-tail estimates, following the proof of Lemma 3.1 of the OpenAI preprint
[OpenAI2026LogSpace, Lemma 3.1 and its proof, pp. 9–10]:

* The *frame density* `q_fr = #frames / #matrices` (`frameDensity`) is
  `∏_{i < r} (1 - P ^ i / P ^ H)` (`frameDensity_eq_prod`), by Mathlib's count of linearly
  independent families, and it is at least `1 / 2` for `r < H` (`one_div_two_le_frameDensity`).
* Without the frame condition, the polynomial channel (`polyChannelEval`) is a pairwise
  independent hash family as soon as it has a non-constant column (`r ≥ 1`):
  `isPairwiseIndependentHash_polyChannelEval`.
* Conditioning on the frame increases the probability of any event by at most the factor
  `1 / q_fr` (`dens_frameChannel_le`).

Together these give the pair bound `π₁ π₂ / q_fr` for two distinct identifiers
(`dens_eval_mem_and_eval_mem_le`) and the Chebyshev lower tail `4 / (#A π q_fr)`
(`dens_two_mul_card_filter_eval_mem_lt_le`). So frame-conditioned channels satisfy the detector
interface `Cslib.Probability.RetentionChannels` with constants `c_π = 1`, `C_π = 2 ^ H`,
`C_pair = 2 ^ H / q_fr` and `C_var = 4 / q_fr` (`retentionChannels_frameRetains`), and for
`r < H` with the constants `2 ^ (H + 1)` and `8`, which depend on `H` only
(`retentionChannels_frameRetains_of_lt`).

## Main definitions

* `Cslib.Probability.frameDensity`: the probability `q_fr` that a uniformly random family of `r`
  vectors in `ZMod P ^ H` is a frame.
* `Cslib.Probability.polyChannelEval`: the value of a polynomial channel with unrestricted
  coefficient columns.
* `Cslib.Probability.frameRetains`: a frame-conditioned channel retains an identifier.

## Main results

* `Cslib.Probability.card_frame`: there are `∏_{i < r} (P ^ H - P ^ i)` frames.
* `Cslib.Probability.frameDensity_eq_prod`, `Cslib.Probability.frameDensity_pos`,
  `Cslib.Probability.one_div_two_le_frameDensity`: the frame density and its bounds.
* `Cslib.Probability.isPairwiseIndependentHash_polyChannelEval`: unrestricted polynomial channels
  are pairwise independent.
* `Cslib.Probability.dens_frameChannel_le`: the transfer from unrestricted to frame-conditioned
  channels.
* `Cslib.Probability.dens_eval_mem_and_eval_mem_le`: the pair bound.
* `Cslib.Probability.dens_two_mul_card_filter_eval_mem_lt_le`: the lower tail.
* `Cslib.Probability.retentionChannels_frameRetains`,
  `Cslib.Probability.retentionChannels_frameRetains_of_lt`: frame-conditioned channels satisfy the
  detector interface.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 3.1 (preprint, not peer reviewed)
-/

public section

namespace Cslib.Probability

open Finset

variable {P H r : ℕ}

section Density

variable (P H r) in
/-- The **frame density** `q_fr`: the probability that a uniformly random family of `r` vectors
in `ZMod P ^ H` is a frame [OpenAI2026LogSpace, proof of Lemma 3.1]. -/
noncomputable def frameDensity [NeZero P] : ℝ :=
  Fintype.card (Frame P H r) / Fintype.card (Fin r → Fin H → ZMod P)

/-- The frame density is nonnegative. -/
theorem frameDensity_nonneg [NeZero P] : 0 ≤ frameDensity P H r := by
  rw [frameDensity]
  positivity

variable [Fact P.Prime]

/-- **Counting frames**: for `r ≤ H` there are `∏_{i < r} (P ^ H - P ^ i)` frames of length `r`
in `ZMod P ^ H`. -/
theorem card_frame (hr : r ≤ H) :
    Fintype.card (Frame P H r) = ∏ i : Fin r, (P ^ H - P ^ (i : ℕ)) := by
  rw [← Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := ZMod P) (V := Fin H → ZMod P) (k := r)
    (by rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ZMod.card] at h

/-- The frame density is `∏_{i < r} (1 - P ^ i / P ^ H)` for `r ≤ H`. -/
theorem frameDensity_eq_prod (hr : r ≤ H) :
    frameDensity P H r = ∏ i : Fin r, (1 - (P : ℝ) ^ (i : ℕ) / P ^ H) := by
  have hP : (P : ℝ) ^ H ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : P.Prime).ne_zero)
  have hle (i : Fin r) : P ^ (i : ℕ) ≤ P ^ H :=
    Nat.pow_le_pow_right (Fact.out : P.Prime).pos (by omega)
  rw [frameDensity, card_frame hr]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_prod, Nat.cast_pow]
  rw [← Fin.prod_const r ((P : ℝ) ^ H), ← prod_div_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (hle i), one_sub_div hP]
  push_cast
  rfl

/-- `1 - P ^ r / P ^ H ≤ ∏_{i < r} (1 - P ^ i / P ^ H)` for `r ≤ H` and `P ≥ 2`. Each step
uses `(1 - u) ^ 2 ≥ 1 - P u`. -/
private theorem one_sub_le_prod_one_sub {p : ℝ} (hp : 2 ≤ p) {H : ℕ} :
    ∀ r ≤ H, 1 - p ^ r / p ^ H ≤ ∏ i : Fin r, (1 - p ^ (i : ℕ) / p ^ H)
  | 0, _ => by
    rw [Fin.prod_univ_zero, pow_zero, sub_le_self_iff]
    positivity
  | r + 1, hr => by
    rw [Fin.prod_univ_castSucc, Fin.val_last]
    simp only [Fin.val_castSucc]
    have ih := one_sub_le_prod_one_sub hp (H := H) r (by omega)
    have hu0 : 0 ≤ p ^ r / p ^ H := by positivity
    have hu1 : p ^ r / p ^ H ≤ 1 :=
      div_le_one_of_le₀ (pow_le_pow_right₀ (by linarith) (show r ≤ H by omega)) (by positivity)
    calc 1 - p ^ (r + 1) / p ^ H = 1 - p * (p ^ r / p ^ H) := by rw [pow_succ]; ring
      _ ≤ (1 - p ^ r / p ^ H) * (1 - p ^ r / p ^ H) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (by linarith)

/-- For `r < H`, at least half of all families of `r` vectors in `ZMod P ^ H` are frames. -/
theorem one_div_two_le_frameDensity (hr : r < H) : 1 / 2 ≤ frameDensity P H r := by
  have hp : (2 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).two_le
  have hpos : (0 : ℝ) < P ^ H := by positivity
  have hr' : (P : ℝ) ^ r * P ≤ P ^ H := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by linarith) hr
  have hfrac : (P : ℝ) ^ r / P ^ H ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < P) r]
  rw [frameDensity_eq_prod hr.le]
  linarith [one_sub_le_prod_one_sub hp r hr.le]

/-- For `r ≤ H` the frame density is positive. -/
theorem frameDensity_pos (hr : r ≤ H) : 0 < frameDensity P H r := by
  have := Frame.nonempty (P := P) hr
  rw [frameDensity]
  exact div_pos (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)

end Density

section Unrestricted

/-- The value `∑ j, y ^ (j + 1) • M j + a₀` at `y` of the polynomial channel with unrestricted
coefficient columns `M` and constant column `a₀`, for the seed `s = (M, a₀)`. -/
def polyChannelEval (s : (Fin r → Fin H → ZMod P) × (Fin H → ZMod P)) (y : ZMod P) :
    Fin H → ZMod P :=
  ∑ j : Fin r, y ^ (j.val + 1) • s.1 j + s.2

/-- A frame-conditioned channel evaluates as the unrestricted polynomial channel with the same
columns. -/
theorem FrameChannel.eval_eq_polyChannelEval (A : FrameChannel P H r) (y : ZMod P) :
    A.eval y = polyChannelEval (A.2.1, A.1) y :=
  add_comm _ _

/-- The coefficient part `M ↦ (y ↦ ∑ j, y ^ (j + 1) • M j)` of a polynomial channel, as an
additive map. -/
private def polyCoeffHom : (Fin r → Fin H → ZMod P) →+ (ZMod P → Fin H → ZMod P) where
  toFun M y := ∑ j : Fin r, y ^ (j.val + 1) • M j
  map_zero' := by
    funext y
    simp
  map_add' M N := by
    funext y
    simp [smul_add, sum_add_distrib]

variable [Fact P.Prime]

/-- **Unrestricted polynomial channels are pairwise independent**: with at least one
non-constant column, the values of a uniformly random polynomial channel at two distinct
identifiers are independent and uniform [OpenAI2026LogSpace, proof of Lemma 3.1]. The difference
of the values at `x₁ ≠ x₂` takes every value already through the first column, since
`x₁ - x₂` is invertible. -/
theorem isPairwiseIndependentHash_polyChannelEval (hr : 0 < r) :
    IsPairwiseIndependentHash (polyChannelEval (P := P) (H := H) (r := r)) := by
  refine isPairwiseIndependentHash_add_of_surjective (polyCoeffHom (P := P) (H := H) (r := r))
    fun x₁ x₂ hx c ↦ ?_
  have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  refine ⟨Pi.single ⟨0, hr⟩ ((x₁ - x₂)⁻¹ • c), ?_⟩
  simp only [polyCoeffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Fintype.sum_eq_single ⟨0, hr⟩ fun j hj ↦ by rw [Pi.single_eq_of_ne hj, smul_zero],
    Fintype.sum_eq_single ⟨0, hr⟩ fun j hj ↦ by rw [Pi.single_eq_of_ne hj, smul_zero],
    Pi.single_eq_same, ← sub_smul, smul_smul, zero_add, pow_one, pow_one,
    mul_inv_cancel₀ hne, one_smul]

end Unrestricted

section Transfer

variable [NeZero P]

/-- **Transfer to frame conditioning**: an event about the seed `(M, a₀)` of a polynomial channel
has, under frame conditioning, at most its unrestricted probability divided by the frame density
`q_fr` [OpenAI2026LogSpace, proof of Lemma 3.1]. -/
theorem dens_frameChannel_le (E : (Fin r → Fin H → ZMod P) × (Fin H → ZMod P) → Prop)
    [DecidablePred E] :
    (dens {A : FrameChannel P H r | E (A.2.1, A.1)} : ℝ) ≤ dens {s | E s} / frameDensity P H r := by
  have hinj : #{A : FrameChannel P H r | E (A.2.1, A.1)} ≤ #{s | E s} :=
    card_le_card_of_injOn (fun A ↦ (A.2.1, A.1)) (fun A hA ↦ by simpa using hA)
      fun A _ B _ h ↦ by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2 (Subtype.ext h.1)
  have hQ : (0 : ℝ) < Fintype.card (Fin r → Fin H → ZMod P) := by exact_mod_cast Fintype.card_pos
  rw [dens_eq_card_div_card, dens_eq_card_div_card, frameDensity, Fintype.card_prod,
    Fintype.card_prod]
  push_cast
  rw [div_div_div_eq, mul_comm (#{s | E s} : ℝ), mul_assoc, mul_div_mul_left _ _ hQ.ne',
    mul_comm (Fintype.card (Fin H → ZMod P) : ℝ)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hinj) (by positivity)

variable [Fact P.Prime] {L L₁ L₂ : ℕ}

/-- **Pair bound under frame conditioning**: for distinct identifiers `w ≠ y` and sides
`L₁, L₂ ≤ P`, a frame-conditioned channel with `r ≥ 1` retains `w` in the box of side `L₁` and `y`
in the box of side `L₂` with probability at most `(L₁ / P) ^ H (L₂ / P) ^ H / q_fr`
[OpenAI2026LogSpace, proof of Lemma 3.1, item 2]. -/
theorem dens_eval_mem_and_eval_mem_le (hr : 0 < r) (hL₁ : L₁ ≤ P) (hL₂ : L₂ ≤ P) {w y : ZMod P}
    (hwy : w ≠ y) :
    (dens {A : FrameChannel P H r |
        A.eval w ∈ retentionBox P H L₁ ∧ A.eval y ∈ retentionBox P H L₂} : ℝ) ≤
      ((L₁ : ℝ) / P) ^ H * ((L₂ : ℝ) / P) ^ H / frameDensity P H r := by
  have h := dens_frameChannel_le (P := P) (H := H) (r := r)
    fun s ↦ polyChannelEval s w ∈ retentionBox P H L₁ ∧ polyChannelEval s y ∈ retentionBox P H L₂
  simp only [← FrameChannel.eval_eq_polyChannelEval] at h
  rw [(isPairwiseIndependentHash_polyChannelEval hr).dens_filter_apply_mem_and_apply_mem hwy,
    card_retentionBox hL₁, card_retentionBox hL₂, Fintype.card_fun, Fintype.card_fin,
    ZMod.card] at h
  push_cast at h
  rw [div_pow, div_pow]
  convert h using 1
  rw [dens_eq_card_div_card]
  push_cast
  rfl

/-- **Lower tail under frame conditioning**: for `r ≥ 1`, `L ≤ P` and `π = (L / P) ^ H`, a
frame-conditioned channel retains fewer than `#A π / 2` identifiers of `A` with probability at
most `4 / (#A π) / q_fr` [OpenAI2026LogSpace, proof of Lemma 3.1, item 3]. -/
theorem dens_two_mul_card_filter_eval_mem_lt_le (hr : 0 < r) (hL : L ≤ P) (A : Finset (ZMod P))
    (hpos : 0 < (#A : ℝ) * ((L : ℝ) / P) ^ H) :
    (dens {s : FrameChannel P H r |
        2 * (#{y ∈ A | s.eval y ∈ retentionBox P H L} : ℝ) < #A * ((L : ℝ) / P) ^ H} : ℝ) ≤
      4 / (#A * ((L : ℝ) / P) ^ H) / frameDensity P H r := by
  have hrate : ((#(retentionBox P H L) : ℝ) / Fintype.card (Fin H → ZMod P)) =
      ((L : ℝ) / P) ^ H := by
    rw [card_retentionBox hL, Fintype.card_fun, Fintype.card_fin, ZMod.card, div_pow]
    push_cast
    rfl
  have ht := (isPairwiseIndependentHash_polyChannelEval (H := H) hr
    ).dens_two_mul_card_filter_apply_mem_lt_le (𝕜 := ℝ) A (retentionBox P H L) (by rwa [hrate])
  rw [hrate] at ht
  have h := dens_frameChannel_le (P := P) (H := H) (r := r)
    fun s ↦ 2 * (#{y ∈ A | polyChannelEval s y ∈ retentionBox P H L} : ℝ) <
      #A * ((L : ℝ) / P) ^ H
  simp only [← FrameChannel.eval_eq_polyChannelEval] at h
  exact h.trans (div_le_div_of_nonneg_right ht (frameDensity_nonneg))

end Transfer

section Interface

variable (P H) in
/-- The identifier `y` is **retained** by the frame-conditioned channel `s` when its value
`s.eval y` lies in the retention box of side `L`. -/
abbrev frameRetains [NeZero P] (L : ℕ) (s : FrameChannel P H r) (y : ZMod P) : Prop :=
  s.eval y ∈ retentionBox P H L

/-- A positive rate `a` from `1 ≤ P a`. -/
private theorem pos_of_one_le_mul {P a : ℝ} (hP : 0 ≤ P) (hPa : 1 ≤ P * a) : 0 < a := by
  by_contra h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hP (not_lt.1 h)]

variable {V : Type*} [Fact P.Prime]

/-- **Frame-conditioned channels satisfy the detector interface.** Let `ident : V → ZMod P` be
injective, `1 ≤ r ≤ H`, `1 ≤ P a`, `a ≤ 1` and `L = ⌈P a⌉`. Retaining `v` when a uniformly random
frame-conditioned channel retains `ident v`, for each of two channels, gives retention channels at
rate `f = a ^ H` with retention probability `π = (L / P) ^ H` and constants `c_π = 1`,
`C_π = 2 ^ H`, `C_pair = 2 ^ H / q_fr` and `C_var = 4 / q_fr`, where `q_fr` is the frame
density [OpenAI2026LogSpace, Lemma 3.1, items 1–3]. -/
theorem retentionChannels_frameRetains {ident : V → ZMod P} (hident : Function.Injective ident)
    (hr0 : 0 < r) (hr : r ≤ H) {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) :
    RetentionChannels (fun (s : FrameChannel P H r) v ↦ frameRetains P H ⌈P * a⌉₊ s (ident v))
      (fun (s : FrameChannel P H r) v ↦ frameRetains P H ⌈P * a⌉₊ s (ident v)) (a ^ H)
      ((((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H) 1 (2 ^ H) (2 ^ H / frameDensity P H r)
      (4 / frameDensity P H r) := by
  obtain ⟨hL, hlow, hup, -, -⟩ := affineRetains_rates (P := P) (H := H) hPa ha
  set π : ℝ := (((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H
  have hq := frameDensity_pos (P := P) hr
  have hπ : 0 < π := (pow_pos (pos_of_one_le_mul (Nat.cast_nonneg P) hPa) H).trans_le hlow
  have hdens : ∀ v, (dens {s : FrameChannel P H r | frameRetains P H ⌈P * a⌉₊ s (ident v)} : ℝ) =
      π := fun v ↦ by
    rw [dens_eval_mem_retentionBox hr hL]
    push_cast
    rfl
  refine ⟨hdens, hdens, by rw [one_mul]; exact hlow, hup, fun w y hwy ↦ ?_, fun A hA ↦ ?_⟩
  · refine (dens_eval_mem_and_eval_mem_le hr0 hL hL (hident.ne hwy)).trans ?_
    rw [hdens, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
    exact mul_le_mul_of_nonneg_right hup hπ.le
  · have hcard : #(A.image ident) = #A := card_image_of_injective A hident
    have hfilter : ∀ s : FrameChannel P H r,
        #{x ∈ A | s.eval (ident x) ∈ retentionBox P H ⌈P * a⌉₊} =
          #{y ∈ A.image ident | s.eval y ∈ retentionBox P H ⌈P * a⌉₊} := fun s ↦ by
      rw [filter_image, card_image_of_injective _ hident]
    have hpos : 0 < (#(A.image ident) : ℝ) * π :=
      mul_pos (by exact_mod_cast (hA.image ident).card_pos) hπ
    have := dens_two_mul_card_filter_eval_mem_lt_le hr0 hL (A.image ident) hpos
    simp only [hcard, ← hfilter] at this
    rwa [div_right_comm] at this

/-- **Frame-conditioned channels with constants depending only on `H`.** For `1 ≤ r < H`, the
frame density is at least `1 / 2`, so the channels of `retentionChannels_frameRetains` satisfy the
detector interface with `c_π = 1`, `C_π = 2 ^ H`, `C_pair = 2 ^ (H + 1)` and `C_var = 8`
[OpenAI2026LogSpace, Lemma 3.1, items 1–3]. -/
theorem retentionChannels_frameRetains_of_lt {ident : V → ZMod P}
    (hident : Function.Injective ident) (hr0 : 0 < r) (hr : r < H) {a : ℝ} (hPa : 1 ≤ P * a)
    (ha : a ≤ 1) :
    RetentionChannels (fun (s : FrameChannel P H r) v ↦ frameRetains P H ⌈P * a⌉₊ s (ident v))
      (fun (s : FrameChannel P H r) v ↦ frameRetains P H ⌈P * a⌉₊ s (ident v)) (a ^ H)
      ((((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H) 1 (2 ^ H) (2 ^ (H + 1)) 8 := by
  have h := retentionChannels_frameRetains hident hr0 hr.le hPa ha
  have hq := one_div_two_le_frameDensity (P := P) hr
  have hq0 : 0 < frameDensity P H r := by linarith
  have hpair : 2 ^ H / frameDensity P H r ≤ 2 ^ (H + 1) := by
    rw [div_le_iff₀ hq0, pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) H]
  have hvar : 4 / frameDensity P H r ≤ 8 := by
    rw [div_le_iff₀ hq0]
    linarith
  refine ⟨h.dens_X, h.dens_Y, h.lower, h.upper, fun w y hwy ↦ (h.pair w y hwy).trans ?_,
    fun A hA ↦ (h.tail A hA).trans ?_⟩
  · have := pos_of_one_le_mul (Nat.cast_nonneg P) hPa
    gcongr
  · have : 0 < (((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H := by
      have := pos_of_one_le_mul (Nat.cast_nonneg P) hPa
      exact (by positivity : (0 : ℝ) < 1 * a ^ H).trans_le h.lower
    have := mul_pos (by exact_mod_cast hA.card_pos : (0 : ℝ) < #A) this
    gcongr

end Interface

end Cslib.Probability
