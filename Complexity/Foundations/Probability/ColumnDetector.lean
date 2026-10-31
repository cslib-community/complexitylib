/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.KthLargest
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Column detectors from retention channels

A *column detector* decides, with true expectations over random retained sets, whether a column
of a nonnegative matrix `G` has many substantial entries. It is the detector of the OpenAI preprint
(2026-09-23), Section 4.2, idea 3 in issue #474 [OpenAI2026LogSpace], which chooses the column
multipliers of the correction-and-copy hierarchy.

**Channels.** Two *retention channels* `X : ι → V → Prop` and `Y : κ → V → Prop` select random
sets of vertices from independent uniform seeds `s : ι` and `t : κ`; independence is built in,
since the seed space is the product `ι × κ`. `Cslib.Probability.RetentionChannels` records the
properties that the detector uses, at rate `f` [OpenAI2026LogSpace, (4.8), (4.9)]:

* every vertex is retained with the same probability `π`, with `c_π f ≤ π ≤ C_π f`;
* for `w ≠ y`, `Pr[Y(w) ∧ Y(y)] ≤ C_pair f Pr[Y(y)]`;
* a nonempty set `A` retains fewer than `|A| π / 2` members of `X` with probability at most
  `C_var / (|A| π)`.

**The detector.** For a draw `T` of the terminal channel `Y`, the *row gate* of row `x` is
`ρ (rank_K {G x w / f : w ∈ T})` (`Matrix.rowGate`); it is one unless `K` retained entries of the
row exceed `η f`. For a draw `S` of the start channel `X`, the *trial* at column `y` is
`rank_J {ϕ (G x y / f) * gate x : x ∈ S}` (`Matrix.detectorTrial`), where `rank_j` is the `j`-th
largest value padded with zeros (`Finset.kthLargest`). The *detector number* `U y` is the
expectation of the trial over both channels, conditioned on `Y(y)` (`Matrix.columnDetector`).

**The detector lemma** [OpenAI2026LogSpace, Lemma 4.3]. Let `ϕ` be zero through `δ₀` and one from
`δ₁`, and `ρ` one through `η > 0`, both with values in `[0, 1]`.

1. If the rows of `G ≥ 0` sum to at most `k`, the gate rank satisfies `K ≥ 160 (1 + C_pair k / η)`,
   and `R` satisfies `c_π R ≥ max (4 J, 40 C_var)`, then a column with more than `R / f` entries
   at least `δ₁ f` has `U y ≥ 19 / 20` (`Matrix.le_columnDetector`).
2. If `U y > 1 / 4`, the column has more than `J / (4 C_π f)` entries above `δ₀ f`
   (`Matrix.lt_card_of_lt_columnDetector`).

Each statement uses only the hypotheses it needs; for instance the second needs neither the
row-sum bound nor the row gates' threshold.

The first statement uses no independence between the row gates of different rows; it combines
Markov's inequality for the gate failures with the lower tail of the start channel.

## Main definitions

* `Cslib.Probability.RetentionChannels`: the channel properties used by the detector.
* `Matrix.rowGate`, `Matrix.detectorTrial`, `Matrix.columnDetector`: the detector.

## Main results

* `Matrix.columnDetector_nonneg`, `Matrix.columnDetector_le_one`: detector numbers lie in `[0, 1]`.
* `Matrix.card_filter_rowGate_lt_one_mul_le`: a row gate fails on few terminal draws.
* `Matrix.le_columnDetector`: columns with many large entries are detected.
* `Matrix.lt_card_of_lt_columnDetector`: detected columns have many substantial entries.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.2 and Lemma 4.3 (preprint, not peer reviewed)
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability

/-- **Retention channels** `X` and `Y` at rate `f`, with independent uniform seeds `s : ι` and
`t : κ`: every vertex is retained by either channel with the same probability `π`,
`c_π f ≤ π ≤ C_π f`; two distinct vertices `w ≠ y` are both retained by `Y` with probability at
most `C_pair f` times that of `y`; and a nonempty set `A` retains fewer than `|A| π / 2` members
of `X` with probability at most `C_var / (|A| π)`. These are the properties
[OpenAI2026LogSpace, (4.8), (4.9)] that the detectors use. -/
structure RetentionChannels {V ι κ : Type*} [Fintype ι] [Fintype κ] (X : ι → V → Prop)
    (Y : κ → V → Prop) [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
    (f π cπ Cπ Cpair Cvar : ℝ) : Prop where
  dens_X : ∀ v, (dens {s | X s v} : ℝ) = π
  dens_Y : ∀ v, (dens {t | Y t v} : ℝ) = π
  lower : cπ * f ≤ π
  upper : π ≤ Cπ * f
  pair : ∀ w y, w ≠ y → (dens {t | Y t w ∧ Y t y} : ℝ) ≤ Cpair * f * dens {t | Y t y}
  tail : ∀ A : Finset V, A.Nonempty →
    (dens {s | 2 * (#{x ∈ A | X s x} : ℝ) < #A * π} : ℝ) ≤ Cvar / (#A * π)

end Cslib.Probability

namespace Matrix

open Cslib.Probability

variable {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]

section Definitions

/-- The **row gate** of row `x` for a draw `T` of the terminal channel:
`ρ (rank_K {G x w / f : w ∈ T})` [OpenAI2026LogSpace, (4.11)]. -/
@[expose] noncomputable def rowGate (ρ : ℝ → ℝ) (K : ℕ) (f : ℝ) (G : Matrix V V ℝ)
    (T : Finset V) (x : V) : ℝ :=
  ρ (kthLargest K T fun w => G x w / f)

/-- A **detector trial** at column `y`, for draws `S` of the start channel and `T` of the terminal
channel: `rank_J {ϕ (G x y / f) * rowGate x : x ∈ S}` [OpenAI2026LogSpace, (4.12)]. -/
@[expose] noncomputable def detectorTrial (ϕ ρ : ℝ → ℝ) (J K : ℕ) (f : ℝ) (G : Matrix V V ℝ)
    (S T : Finset V) (y : V) : ℝ :=
  kthLargest J S fun x => ϕ (G x y / f) * rowGate ρ K f G T x

/-- The **detector number** of column `y`: the expectation of the detector trial over the seeds of
both channels, conditioned on `Y(y)` [OpenAI2026LogSpace, (4.12)]. -/
@[expose] noncomputable def columnDetector (X : ι → V → Prop) (Y : κ → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] (ϕ ρ : ℝ → ℝ) (J K : ℕ) (f : ℝ)
    (G : Matrix V V ℝ) (y : V) : ℝ :=
  𝔼 s, 𝔼 t ∈ {t | Y t y}, detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y

end Definitions

variable {X : ι → V → Prop} {Y : κ → V → Prop} [∀ s v, Decidable (X s v)]
  [∀ t v, Decidable (Y t v)] {ϕ ρ : ℝ → ℝ} {J K : ℕ} {f : ℝ} {G : Matrix V V ℝ} {y : V}

private theorem dens_cast {α : Type*} [Fintype α] (s : Finset α) :
    ((dens s : ℚ≥0) : ℝ) = #s / Fintype.card α := by
  rw [dens_eq_card_div_card]; push_cast; rfl

private theorem columnDetector_eq_sum :
    columnDetector X Y ϕ ρ J K f G y =
      (∑ s, ∑ t ∈ {t | Y t y}, detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y) /
        (Fintype.card ι * #({t | Y t y} : Finset κ)) := by
  rw [columnDetector, Fintype.expect_eq_sum_div_card]
  simp only [expect_eq_sum_div_card]
  rw [← Finset.sum_div, div_div, mul_comm (#({t | Y t y} : Finset κ) : ℝ)]

omit [Fintype V] in
theorem detectorTrial_nonneg {S T : Finset V} : 0 ≤ detectorTrial ϕ ρ J K f G S T y :=
  kthLargest_nonneg

omit [Fintype V] in
theorem detectorTrial_le_one (hϕ0 : ∀ t, 0 ≤ ϕ t) (hϕ1 : ∀ t, ϕ t ≤ 1)
    (hρ1 : ∀ t, ρ t ≤ 1) {S T : Finset V} : detectorTrial ϕ ρ J K f G S T y ≤ 1 :=
  kthLargest_le zero_le_one fun _ _ =>
    (mul_le_mul_of_nonneg_left (hρ1 _) (hϕ0 _)).trans (by rw [mul_one]; exact hϕ1 _)

theorem columnDetector_nonneg : 0 ≤ columnDetector X Y ϕ ρ J K f G y := by
  rw [columnDetector]
  exact expect_nonneg fun _ _ => expect_nonneg fun _ _ => detectorTrial_nonneg

theorem columnDetector_le_one (hϕ0 : ∀ t, 0 ≤ ϕ t) (hϕ1 : ∀ t, ϕ t ≤ 1)
    (hρ1 : ∀ t, ρ t ≤ 1) : columnDetector X Y ϕ ρ J K f G y ≤ 1 := by
  rw [columnDetector_eq_sum]
  refine div_le_one_of_le₀ ?_ (by positivity)
  calc ∑ s, ∑ t ∈ {t | Y t y}, detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y
      ≤ ∑ _s : ι, ∑ _t ∈ ({t | Y t y} : Finset κ), (1 : ℝ) :=
        sum_le_sum fun _ _ => sum_le_sum fun _ _ => detectorTrial_le_one hϕ0 hϕ1 hρ1
    _ = Fintype.card ι * #({t | Y t y} : Finset κ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]

omit [Fintype κ] in
/-- **Row gates rarely fail** [OpenAI2026LogSpace, proofs of Lemmas 4.3 (1) and 5.1]. Let row `x`
of `G ≥ 0` sum to at most `k`, and let `ρ` be one through `η > 0`. Let `T` be a finite set of
terminal draws on which every vertex `w ≠ y` is retained at most a `c f` fraction of the time.
Then the row gate of `x` is below one on at most a `(1 + c k / η) / K` fraction of `T`.

The gate can fail only if `K` retained entries exceed `η f`. At most `k / (η f)` entries do, and
the retention counts of these entries over `T` sum to at most `#T (1 + c k / η)`, counting `y`
itself once; this is Markov's inequality. No independence between rows is used. -/
theorem card_filter_rowGate_lt_one_mul_le (T : Finset κ) (x : V) (hf : 0 < f) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ t, t ≤ η → ρ t = 1) (hG0 : ∀ w, 0 ≤ G x w) {k : ℝ}
    (hGk : ∑ w, G x w ≤ k) (hK : 0 < K) {c : ℝ} (hc : 0 ≤ c)
    (hpair : ∀ w, w ≠ y → (#{t ∈ T | Y t w} : ℝ) ≤ c * f * #T) :
    (#{t ∈ T | rowGate ρ K f G {w | Y t w} x < 1} : ℝ) * K ≤ #T * (1 + c * k / η) := by
  classical
  set W : Finset V := {w | η * f < G x w}
  have hW : (#W : ℝ) * (η * f) ≤ k :=
    (card_filter_mul_le_sum univ _ (fun w => G x w) (fun w _ => hG0 w)
      fun _ _ hw => hw.le).trans hGk
  have hbadK : ∀ t ∈ T, rowGate ρ K f G {w | Y t w} x < 1 → (K : ℝ) ≤ #{w ∈ W | Y t w} := by
    intro t _ ht
    have hlt : η < kthLargest K {w | Y t w} (fun w => G x w / f) := by
      by_contra hle
      rw [rowGate, hρη _ (not_lt.mp hle)] at ht
      exact lt_irrefl _ ht
    have hcard := (lt_kthLargest_iff hK hη.le).mp hlt
    have hsub : ({w ∈ ({w | Y t w} : Finset V) | η < G x w / f} : Finset V) ⊆
        {w ∈ W | Y t w} := fun w hw => by
      simp only [mem_filter, mem_univ, true_and, W] at hw ⊢
      exact ⟨by rw [lt_div_iff₀ hf] at hw; exact hw.2, hw.1⟩
    exact_mod_cast hcard.trans (card_le_card hsub)
  have hMarkov : (#{t ∈ T | rowGate ρ K f G {w | Y t w} x < 1} : ℝ) * K ≤
      ∑ t ∈ T, (#{w ∈ W | Y t w} : ℝ) :=
    card_filter_mul_le_sum T _ _ (fun _ _ => by positivity) hbadK
  have hswap : ∑ t ∈ T, (#{w ∈ W | Y t w} : ℝ) = ∑ w ∈ W, (#{t ∈ T | Y t w} : ℝ) := by
    simp only [natCast_card_filter]
    exact sum_comm
  have hterm : ∀ w ∈ W, (#{t ∈ T | Y t w} : ℝ) ≤ (if y = w then (#T : ℝ) else 0) +
      c * f * #T := by
    intro w _
    by_cases hwy : y = w
    · have hle : (#{t ∈ T | Y t w} : ℝ) ≤ #T := by exact_mod_cast card_filter_le _ _
      have : 0 ≤ c * f * #T := by positivity
      simp only [hwy, ↓reduceIte]
      linarith
    · simp only [hwy, ↓reduceIte, zero_add]
      exact hpair w (Ne.symm hwy)
  have hWf : (#W : ℝ) * f ≤ k / η := by
    rw [le_div_iff₀ hη]; linarith
  calc (#{t ∈ T | rowGate ρ K f G {w | Y t w} x < 1} : ℝ) * K
      ≤ ∑ w ∈ W, ((if y = w then (#T : ℝ) else 0) + c * f * #T) :=
        hMarkov.trans (hswap ▸ sum_le_sum hterm)
    _ = (if y ∈ W then (#T : ℝ) else 0) + #W * (c * f * #T) := by
        rw [sum_add_distrib, sum_ite_eq, sum_const, nsmul_eq_mul]
    _ ≤ #T + #T * c * (#W * f) := by
        have : (if y ∈ W then (#T : ℝ) else 0) ≤ #T := by split_ifs <;> [exact le_rfl; positivity]
        nlinarith
    _ ≤ #T + #T * c * (k / η) := by gcongr
    _ = #T * (1 + c * k / η) := by ring

variable {π cπ Cπ Cpair Cvar : ℝ}

omit [Fintype V] in
private theorem card_X (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar) (v : V) :
    (#({s | X s v} : Finset ι) : ℝ) = π * Fintype.card ι := by
  have h := hch.dens_X v
  rw [dens_cast] at h
  rcases (Fintype.card ι).eq_zero_or_pos with h0 | h0
  · have : (#({s | X s v} : Finset ι)) = 0 := Nat.eq_zero_of_le_zero
      (h0 ▸ card_le_univ _)
    simp [this, h0]
  · rw [← h]; field_simp

/-- **Detected columns have many substantial entries** [OpenAI2026LogSpace, Lemma 4.3 (2)]: if
`ϕ` vanishes through `δ₀` and the detector number of column `y` exceeds `1 / 4`, more than
`J / (4 C_π f)` entries of the column exceed `δ₀ f`. -/
theorem lt_card_of_lt_columnDetector (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hϕ0 : ∀ t, 0 ≤ ϕ t) (hϕ1 : ∀ t, ϕ t ≤ 1) {δ₀ : ℝ}
    (hϕδ : ∀ t, t ≤ δ₀ → ϕ t = 0) (hρ1 : ∀ t, ρ t ≤ 1) (hJ : 0 < J)
    (hU : 1 / 4 < columnDetector X Y ϕ ρ J K f G y) :
    J / (4 * Cπ * f) < #({x | δ₀ * f < G x y} : Finset V) := by
  set A0 : Finset V := {x | δ₀ * f < G x y}
  set T : Finset κ := {t | Y t y}
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  -- a trial is at most the number of retained substantial entries over `J`
  have htrial : ∀ s t, detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y ≤
      (#{x ∈ A0 | X s x} : ℝ) / J := by
    intro s t
    rcases le_or_gt (detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y) 0 with h | h
    · exact h.trans (by positivity)
    have hcard := (lt_kthLargest_iff hJ le_rfl).mp h
    have hsub : ({x ∈ ({x | X s x} : Finset V) |
        0 < ϕ (G x y / f) * rowGate ρ K f G {w | Y t w} x}) ⊆ {x ∈ A0 | X s x} := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, A0] at hx ⊢
      refine ⟨?_, hx.1⟩
      by_contra hle
      have : G x y / f ≤ δ₀ := by rw [div_le_iff₀ hf]; linarith
      rw [hϕδ _ this, zero_mul] at hx
      exact lt_irrefl _ hx.2
    have hJle : (J : ℝ) ≤ #{x ∈ A0 | X s x} := by exact_mod_cast hcard.trans (card_le_card hsub)
    rw [le_div_iff₀ hJr]
    calc detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y * J ≤ 1 * J :=
          mul_le_mul_of_nonneg_right (detectorTrial_le_one hϕ0 hϕ1 hρ1) hJr.le
      _ ≤ _ := by rw [one_mul]; exact hJle
  -- summing over the start seeds counts each substantial entry with its retention probability
  have hsumX : ∑ s, (#{x ∈ A0 | X s x} : ℝ) = #A0 * (π * Fintype.card ι) := by
    simp only [natCast_card_filter]
    rw [sum_comm]
    simp only [← natCast_card_filter, card_X hch, sum_const, nsmul_eq_mul]
  have hT : 0 < #T := by
    rw [card_pos]
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    have : columnDetector X Y ϕ ρ J K f G y = 0 := by
      rw [columnDetector_eq_sum]; simp [T, hT]
    linarith
  have hι : 0 < Fintype.card ι := by
    rw [Fintype.card_pos_iff]
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : columnDetector X Y ϕ ρ J K f G y = 0 := by
      rw [columnDetector_eq_sum]; simp
    linarith
  have hTr : (0 : ℝ) < #T := by exact_mod_cast hT
  have hιr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have hUle : columnDetector X Y ϕ ρ J K f G y ≤ #A0 * π / J := by
    rw [columnDetector_eq_sum, div_le_div_iff₀ (by positivity) hJr]
    calc (∑ s, ∑ t ∈ T, detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y) * J
        ≤ (∑ s, ∑ _t ∈ T, (#{x ∈ A0 | X s x} : ℝ) / J) * J :=
          mul_le_mul_of_nonneg_right
            (sum_le_sum fun s _ => sum_le_sum fun t _ => htrial s t) hJr.le
      _ = #T * ∑ s, (#{x ∈ A0 | X s x} : ℝ) := by
          simp only [sum_const, nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
          exact sum_congr rfl fun s _ => by field_simp
      _ = #A0 * π * (Fintype.card ι * #T) := by rw [hsumX]; ring
  have hπ : 0 < π := by
    by_contra hπ
    have : #A0 * π / J ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (not_lt.mp hπ)) hJr.le
    linarith
  have hCπ : 0 < Cπ * f := hπ.trans_le hch.upper
  have h1 : J / 4 < #A0 * π := by
    have := hU.trans_le hUle
    rw [lt_div_iff₀ hJr] at this
    linarith
  rw [div_lt_iff₀ (by nlinarith)]
  calc (J : ℝ) = J / 4 * 4 := by ring
    _ < #A0 * π * 4 := by linarith
    _ ≤ #A0 * (Cπ * f) * 4 := by gcongr; exact hch.upper
    _ = #A0 * (4 * Cπ * f) := by ring

omit [Fintype V] in
private theorem card_pos_of_dens {α : Type*} [Fintype α] {s : Finset α} {π : ℝ} (hπ : 0 < π)
    (h : (dens s : ℝ) = π) : 0 < Fintype.card α ∧ 0 < #s := by
  rw [dens_cast] at h
  rcases (Fintype.card α).eq_zero_or_pos with h0 | h0
  · simp [h0] at h; linarith
  refine ⟨h0, Nat.pos_of_ne_zero fun hs => ?_⟩
  simp [hs] at h; linarith

/-- **Columns with many large entries are detected** [OpenAI2026LogSpace, Lemma 4.3 (1)]. Let the
rows of `G ≥ 0` sum to at most `k`, let `ϕ` be one from `δ₁`, let `ρ ≤ 1` be one through `η > 0`,
let the gate rank satisfy `K ≥ 160 (1 + C_pair k / η)`, and let `c_π R ≥ 4 J` and
`c_π R ≥ 40 C_var`. If more than `R / f` entries of column `y` are at least `δ₁ f`, its detector
number is at least `19 / 20`. -/
theorem le_columnDetector (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar) (hf : 0 < f)
    (hcπ : 0 < cπ) (hCpair : 0 ≤ Cpair) {δ₁ : ℝ} (hϕδ : ∀ t, δ₁ ≤ t → ϕ t = 1)
    (hρ1 : ∀ t, ρ t ≤ 1) {η : ℝ} (hη : 0 < η)
    (hρη : ∀ t, t ≤ η → ρ t = 1) (hG0 : ∀ x w, 0 ≤ G x w) {k : ℝ}
    (hGk : ∀ x, ∑ w, G x w ≤ k) (hK : 160 * (1 + Cpair * k / η) ≤ K) (hJ : 0 < J) {R : ℝ}
    (hRJ : 4 * J ≤ cπ * R) (hRvar : 40 * Cvar ≤ cπ * R)
    (hy : R / f < #({x | δ₁ * f ≤ G x y} : Finset V)) :
    19 / 20 ≤ columnDetector X Y ϕ ρ J K f G y := by
  classical
  set A : Finset V := {x | δ₁ * f ≤ G x y}
  set T : Finset κ := {t | Y t y}
  set D : ℝ := 1 + Cpair * k / η
  set gate : κ → V → ℝ := fun t x => rowGate ρ K f G {w | Y t w} x
  have hπ : 0 < π := (mul_pos hcπ hf).trans_le hch.lower
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hnπ : cπ * R < #A * π := by
    have h1 : R < #A * f := by rwa [div_lt_iff₀ hf] at hy
    calc cπ * R < cπ * (#A * f) := mul_lt_mul_of_pos_left h1 hcπ
      _ = #A * (cπ * f) := by ring
      _ ≤ #A * π := mul_le_mul_of_nonneg_left hch.lower (by positivity)
  have hnπ0 : 0 < (#A : ℝ) * π := by linarith
  have hA : A.Nonempty := by
    rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
    exact pos_of_mul_pos_left hnπ0 hπ.le
  obtain ⟨hι, -⟩ := card_pos_of_dens hπ (hch.dens_X y)
  obtain ⟨hκ, hT⟩ := card_pos_of_dens hπ (hch.dens_Y y)
  have hκr : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hκ
  have hιr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have hTr : (0 : ℝ) < #T := by exact_mod_cast hT
  have hD : 1 ≤ D := by
    have : 0 ≤ Cpair * k / η := by
      have hk : 0 ≤ k := (sum_nonneg fun w _ => hG0 y w).trans (hGk y)
      positivity
    linarith
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := by linarith
    exact_mod_cast this
  -- Markov's inequality for the row gates: each row fails its gate on few terminal draws
  have hgate : ∀ x, (#{t ∈ T | gate t x < 1} : ℝ) * K ≤ #T * D := fun x =>
    card_filter_rowGate_lt_one_mul_le T x hf hη hρη (hG0 x) (hGk x) hKpos hCpair fun w hwy => by
      have hp := hch.pair w y hwy
      rw [dens_cast, dens_cast, ← mul_div_assoc, div_le_div_iff_of_pos_right hκr] at hp
      have hset : ({t ∈ T | Y t w} : Finset κ) = ({t | Y t w ∧ Y t y} : Finset κ) := by
        ext t; simp only [T, mem_filter, mem_univ, true_and]; tauto
      rw [hset]
      exact hp
  -- the expected number of retained large rows that fail their gate
  set N : ι → ℝ := fun s => #{x ∈ A | X s x}
  set L : ι → κ → ℝ := fun s t => #{x ∈ A | X s x ∧ gate t x < 1}
  have hL0 : ∀ s t, 0 ≤ L s t := fun _ _ => by positivity
  have hsumL : ∑ s, ∑ t ∈ T, L s t ≤ #A * π * Fintype.card ι * (#T * D / K) := by
    have heq : ∑ s, ∑ t ∈ T, L s t =
        ∑ x ∈ A, (#{s | X s x} : ℝ) * #{t ∈ T | gate t x < 1} := by
      have h1 : ∀ s t, L s t = ∑ x ∈ A,
          (if X s x then (1 : ℝ) else 0) * (if gate t x < 1 then 1 else 0) := fun s t => by
        simp only [L, natCast_card_filter, ite_zero_mul_ite_zero, mul_one]
      simp only [h1, natCast_card_filter, sum_mul_sum]
      exact (sum_congr rfl fun s _ => sum_comm).trans sum_comm
    rw [heq]
    have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
    calc ∑ x ∈ A, (#{s | X s x} : ℝ) * #{t ∈ T | gate t x < 1}
        ≤ ∑ _x ∈ A, π * Fintype.card ι * (#T * D / K) := by
          refine sum_le_sum fun x _ => ?_
          rw [card_X hch]
          exact mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hKr]; exact hgate x)
            (by positivity)
      _ = #A * π * Fintype.card ι * (#T * D / K) := by
          rw [sum_const, nsmul_eq_mul]; ring
  -- outside two bad events, at least `J` retained large rows pass their gates
  have hgood : ∀ s t, ¬ 2 * N s < #A * π → ¬ #A * π < 4 * L s t →
      1 ≤ detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y := by
    intro s t h1 h2
    push Not at h1 h2
    have hsplit : N s = L s t + #{x ∈ A | X s x ∧ ¬ gate t x < 1} := by
      simp only [N, L, natCast_card_filter, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      by_cases hX : X s x <;> by_cases hg : gate t x < 1 <;> simp [hX, hg]
    have hJle : (J : ℝ) ≤ #{x ∈ A | X s x ∧ ¬ gate t x < 1} := by
      have : 4 * (J : ℝ) < #A * π := hRJ.trans_lt hnπ
      linarith
    refine (le_kthLargest_iff hJ one_pos).mpr ?_
    refine Nat.cast_le.mp (hJle.trans ?_)
    refine Nat.cast_le.mpr (card_le_card fun x hx => ?_)
    simp only [mem_filter, mem_univ, true_and, A] at hx ⊢
    refine ⟨hx.2.1, ?_⟩
    have hϕx : ϕ (G x y / f) = 1 := hϕδ _ (by rw [le_div_iff₀ hf]; exact hx.1)
    have hgx : gate t x = 1 := le_antisymm (hρ1 _) (not_lt.mp hx.2.2)
    simp only [gate] at hgx
    rw [hϕx, hgx, one_mul]
  -- sum the pointwise bound `trial ≥ 1 - [bad start draw] - [many gate failures]`
  set b1 : ι → ℝ := fun s => if 2 * N s < #A * π then 1 else 0
  set b2 : ι → κ → ℝ := fun s t => if #A * π < 4 * L s t then 1 else 0
  have hpoint : ∀ s t, 1 - b1 s - b2 s t ≤
      detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y := by
    intro s t
    have h0 : 0 ≤ detectorTrial ϕ ρ J K f G {x | X s x} {w | Y t w} y := detectorTrial_nonneg
    by_cases h1 : 2 * N s < #A * π
    · have : 0 ≤ b2 s t := by simp only [b2]; split_ifs <;> norm_num
      simp only [b1, h1, ↓reduceIte]
      linarith
    by_cases h2 : #A * π < 4 * L s t
    · simp only [b1, b2, h1, h2, ↓reduceIte]
      linarith
    · simp only [b1, b2, h1, h2, ↓reduceIte, sub_zero]
      exact hgood s t h1 h2
  have hb1 : ∑ s, b1 s ≤ Cvar / (#A * π) * Fintype.card ι := by
    have ht := hch.tail A hA
    rw [dens_cast, div_le_iff₀ hιr] at ht
    simp only [b1, N]
    rw [sum_boole]
    exact ht
  have hb2 : ∑ s, ∑ t ∈ T, b2 s t ≤ 4 / (#A * π) * ∑ s, ∑ t ∈ T, L s t := by
    rw [mul_sum]
    refine sum_le_sum fun s _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun t _ => ?_
    simp only [b2]
    split_ifs with h
    · rw [div_mul_eq_mul_div, le_div_iff₀ hnπ0]; linarith
    · have := hL0 s t; positivity
  have hvar : Cvar / (#A * π) ≤ 1 / 40 := by
    rw [div_le_div_iff₀ hnπ0 (by norm_num)]; linarith
  have hgatebound : 4 / (#A * π) * (#A * π * Fintype.card ι * (#T * D / K)) ≤
      Fintype.card ι * #T / 40 := by
    have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
    have : 4 / (#A * π) * (#A * π * Fintype.card ι * (#T * D / K)) =
        4 * D / K * (Fintype.card ι * #T) := by
      field_simp
    rw [this, div_eq_mul_one_div (Fintype.card ι * (#T : ℝ)) 40, mul_comm _ (1 / 40 : ℝ)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [div_le_iff₀ hKr]; linarith
  rw [columnDetector_eq_sum, le_div_iff₀ (by positivity)]
  have h4 : 0 ≤ 4 / (#A * π) := by positivity
  calc 19 / 20 * (Fintype.card ι * #T : ℝ)
      ≤ Fintype.card ι * #T - #T * (Cvar / (#A * π) * Fintype.card ι) -
          4 / (#A * π) * (#A * π * Fintype.card ι * (#T * D / K)) := by
        nlinarith [mul_le_mul_of_nonneg_left hvar (by positivity : (0 : ℝ) ≤ #T * Fintype.card ι)]
    _ ≤ Fintype.card ι * #T - #T * ∑ s, b1 s - ∑ s, ∑ t ∈ T, b2 s t := by
        nlinarith [mul_le_mul_of_nonneg_left hb1 hTr.le, mul_le_mul_of_nonneg_left hsumL h4]
    _ = ∑ s, ∑ t ∈ T, (1 - b1 s - b2 s t) := by
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, mul_one]
        rw [← mul_sum]
    _ ≤ _ := sum_le_sum fun s _ => sum_le_sum fun t _ => hpoint s t

end Matrix
