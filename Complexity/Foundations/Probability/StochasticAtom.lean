/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ColumnDetector
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stochastic atoms

A *stochastic atom* represents a deterministic number, such as a matrix entry, as the conditional
mean of a bounded table over a random retained set. The table has few nonzero entries in each
row on every draw. This is idea 6 in issue #474: the dense atoms of the OpenAI preprint
[OpenAI2026LogSpace, Section 5.1–5.2].

**The dense atom.** Fix a row `x` of a nonnegative matrix `G`, a scale `a > 0`, and two retention
channels on one seed space `κ`: a *rank channel* `Y`, over whose retained set the row gate ranks
the row, and a *usage channel* `Yt`, which masks the table. In the preprint, `Y` and `Yt` retain at
rates `a` and `t ≤ a`. For a draw `s`, the row gate is `R = ρ (rank_K {G x w / a : Y s w})`
(`Matrix.rowGate`). The *preparatory value* is `h (G x y / a) · R` (`Matrix.atomPrep`), and its
conditional mean given `Yt(y)` is the *normalizer* `q_y` (`Matrix.atomNormalizer`). The atom is
`1{Yt s y} · k (G x y / a) · R / c(q_y)`, with the clipped denominator `c(q) = max (1/2) (min 1 q)`
(`Matrix.denseAtom`) [OpenAI2026LogSpace, (5.10), (5.11)].

**The identity** [OpenAI2026LogSpace, Lemma 5.1]. Suppose `h = 1` wherever `k ≠ 0`, the row has
mass at most `M`, `ρ ∈ [0, 1]` is one through `η > 0`, each vertex `w ≠ y` is retained by `Y`
on at most a `c a` fraction of the draws with `Yt(y)`, and `K ≥ 2 (1 + c M / η)`. Then the gate
is full on at least half of these draws (`Matrix.card_filter_rowGate_lt_one_mul_le`), so
`q_y ≥ 1/2`. The clipping does nothing, and the conditional mean of the atom is exactly
`k (G x y / a)` (`Matrix.expect_denseAtom`). The atom is bounded by `2 |k (G x y / a)|`
(`Matrix.abs_denseAtom_le`). The preprint takes `K` larger, so that the gate fails with
probability at most `1/8` and `q_y ≥ 7/8`; the identity only needs `q_y ≥ 1/2`.

**Row support** [OpenAI2026LogSpace, Lemma 5.5, first part]. If `k` vanishes through `e ≥ 0`, `ρ`
vanishes from `g ≤ e` on, and `Yt ⊆ Y`, then on every draw the row has fewer than `K` nonzero
atom entries (`Matrix.card_filter_denseAtom_ne_zero_lt`). The same holds for the preparatory
values and any other `m (G x y / a) · R` (`Matrix.card_filter_mul_rowGate_ne_zero_lt`). This
holds for every real matrix, with no sign or accuracy hypothesis.

**Bins** [OpenAI2026LogSpace, (5.6), (5.7)]. For a switch `χ`, zero through `1/2` and one from
`1`, and decreasing scales `b`, the weights `ω₀(w) = χ (w / b₀)` and
`ω_{k+1}(w) = χ (w / b_{k+1}) − χ (w / b_k)` (`Cslib.binWeight`) telescope
(`Cslib.sum_range_binWeight`). So `w = ∑_{k ≤ n} w ω_k(w)` once `w ≥ b_n`
(`Cslib.sum_range_mul_binWeight`). The weight `ω_{k+1}` is supported in `(b_{k+1}/2, b_k)`
(`Cslib.binWeight_succ_ne_zero`). A dense entry is split into these bins before the atoms are
formed.

## Main definitions

* `Matrix.atomPrep`, `Matrix.atomNormalizer`, `Matrix.denseAtom`: the dense atom.
* `Cslib.binWeight`: the bin weights.

## Main results

* `Matrix.expect_denseAtom`, `Matrix.expect_denseAtom_of_retentionChannels`: the dense atom
  identity.
* `Matrix.abs_denseAtom_le`: the atom is bounded.
* `Matrix.card_filter_mul_rowGate_ne_zero_lt`, `Matrix.card_filter_denseAtom_ne_zero_lt`: row
  support.
* `Cslib.sum_range_binWeight`, `Cslib.sum_range_mul_binWeight`, `Cslib.binWeight_nonneg`,
  `Cslib.binWeight_succ_ne_zero`: the bins.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 5.1–5.2 (preprint, not peer reviewed)
-/

public section

open Finset
open scoped BigOperators

namespace Matrix

variable {V κ : Type*} [Fintype V]

section Support

variable {ρ m : ℝ → ℝ} {K : ℕ} {a : ℝ} {G : Matrix V V ℝ}

omit [Fintype V] in
/-- **Row support** [OpenAI2026LogSpace, Lemma 5.5]: if `m` vanishes through `e ≥ 0` and the
gate function `ρ` vanishes from `g ≤ e` on, then fewer than `K > 0` retained entries `y ∈ T` have
`m (G x y / a) · rowGate x ≠ 0`. Indeed `K` such entries would all exceed `e`, so the `K`-th
largest value would exceed `g` and close the gate. -/
theorem card_filter_mul_rowGate_ne_zero_lt (T : Finset V) (x : V) (hK : 0 < K) {e g : ℝ}
    (he : 0 ≤ e) (hm : ∀ d, d ≤ e → m d = 0) (hg : g ≤ e) (hρ : ∀ r, g ≤ r → ρ r = 0) :
    #{y ∈ T | m (G x y / a) * rowGate ρ K a G T x ≠ 0} < K := by
  by_contra hle
  rw [not_lt] at hle
  have hsub : ({y ∈ T | m (G x y / a) * rowGate ρ K a G T x ≠ 0} : Finset V) ⊆
      {y ∈ T | e < G x y / a} := fun y hy => by
    rw [mem_filter] at hy ⊢
    refine ⟨hy.1, not_le.mp fun h => hy.2 ?_⟩
    rw [hm _ h, zero_mul]
  have hrank : e < kthLargest K T (fun w => G x w / a) :=
    (lt_kthLargest_iff hK he).mpr (hle.trans (card_le_card hsub))
  have hgate : rowGate ρ K a G T x = 0 := hρ _ (hg.trans hrank.le)
  have hne : ({y ∈ T | m (G x y / a) * rowGate ρ K a G T x ≠ 0} : Finset V).Nonempty :=
    card_pos.mp (hK.trans_le hle)
  obtain ⟨y, hy⟩ := hne
  rw [mem_filter, hgate, mul_zero] at hy
  exact hy.2 rfl

end Support

section DenseAtom

variable [Fintype κ] (Y Yt : κ → V → Prop) [∀ s v, Decidable (Y s v)]
  [∀ s v, Decidable (Yt s v)] (k h ρ : ℝ → ℝ) (K : ℕ) (a : ℝ) (G : Matrix V V ℝ)

/-- The **preparatory value** `h (G x y / a) · rowGate x` of a dense atom, for the retained set
`T` of the rank channel [OpenAI2026LogSpace, (5.10)]. -/
@[expose] noncomputable def atomPrep (T : Finset V) (x y : V) : ℝ :=
  h (G x y / a) * rowGate ρ K a G T x

/-- The **normalizer** `q_y` of a dense atom: the conditional mean of the preparatory value given
that the usage channel retains `y` [OpenAI2026LogSpace, (5.10)]. -/
@[expose] noncomputable def atomNormalizer (x y : V) : ℝ :=
  𝔼 s ∈ ({s | Yt s y} : Finset κ), atomPrep h ρ K a G {w | Y s w} x y

/-- The **dense atom** at `(x, y)` on the draw `s`:
`1{Yt s y} · k (G x y / a) · rowGate x / c(q_y)`, with `c(q) = max (1/2) (min 1 q)`
[OpenAI2026LogSpace, (5.11)]. -/
@[expose] noncomputable def denseAtom (s : κ) (x y : V) : ℝ :=
  if Yt s y then
    k (G x y / a) * rowGate ρ K a G {w | Y s w} x /
      max (1 / 2) (min 1 (atomNormalizer Y Yt h ρ K a G x y))
  else 0

variable {Y Yt k h ρ K a G}

omit [Fintype κ] in
/-- The clipped denominator is at least `1/2`. -/
private theorem half_le_clip (q : ℝ) : (1 / 2 : ℝ) ≤ max (1 / 2) (min 1 q) := le_max_left _ _

/-- **The dense atom is bounded**: `|B(x, y)| ≤ 2 |k (G x y / a)|` on every draw, when
`ρ ∈ [0, 1]` [OpenAI2026LogSpace, Lemma 5.1]. -/
theorem abs_denseAtom_le (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) (s : κ) (x y : V) :
    |denseAtom Y Yt k h ρ K a G s x y| ≤ 2 * |k (G x y / a)| := by
  rw [denseAtom]
  split_ifs
  · have hR0 : 0 ≤ rowGate ρ K a G {w | Y s w} x := hρ0 _
    have hR1 : rowGate ρ K a G {w | Y s w} x ≤ 1 := hρ1 _
    have hc := half_le_clip (atomNormalizer Y Yt h ρ K a G x y)
    have hc0 : 0 < max (1 / 2) (min 1 (atomNormalizer Y Yt h ρ K a G x y)) :=
      lt_of_lt_of_le (by norm_num) hc
    rw [abs_div, abs_mul, abs_of_nonneg hR0, abs_of_pos hc0, div_le_iff₀ hc0]
    calc |k (G x y / a)| * rowGate ρ K a G {w | Y s w} x ≤ |k (G x y / a)| * 1 :=
          mul_le_mul_of_nonneg_left hR1 (abs_nonneg _)
      _ = 2 * |k (G x y / a)| * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  · simp

/-- **Row support of the dense atom** [OpenAI2026LogSpace, Lemmas 5.1 and 5.5]: if `k` vanishes
through `e ≥ 0`, `ρ` vanishes from `g ≤ e` on, and the usage channel retains only vertices that
the rank channel retains, then on every draw fewer than `K > 0` atoms of a row are nonzero. -/
theorem card_filter_denseAtom_ne_zero_lt (hYt : ∀ s v, Yt s v → Y s v) (hK : 0 < K) {e g : ℝ}
    (he : 0 ≤ e) (hk : ∀ d, d ≤ e → k d = 0) (hg : g ≤ e) (hρ : ∀ r, g ≤ r → ρ r = 0) (s : κ)
    (x : V) : #{y | denseAtom Y Yt k h ρ K a G s x y ≠ 0} < K := by
  refine lt_of_le_of_lt (card_le_card fun y hy => ?_)
    (card_filter_mul_rowGate_ne_zero_lt (a := a) (G := G) {w | Y s w} x hK he hk hg hρ)
  rw [mem_filter] at hy ⊢
  rw [denseAtom] at hy
  split_ifs at hy with hy'
  · refine ⟨by simpa using hYt s y hy', fun h0 => hy.2 ?_⟩
    rw [h0, zero_div]
  · exact absurd rfl hy.2

/-- **The dense atom identity** [OpenAI2026LogSpace, Lemma 5.1]. Let `h = 1` wherever `k ≠ 0`,
let row `x` of `G ≥ 0` have mass at most `M`, let `ρ ∈ [0, 1]` be one through `η > 0`, and let
`K ≥ 2 (1 + c M / η)`. Suppose the usage channel retains `y` on some draw, and every vertex
`w ≠ y` is retained by the rank channel on at most a `c a` fraction of those draws. Then the
conditional mean of the dense atom given `Yt(y)` is exactly `k (G x y / a)`. -/
theorem expect_denseAtom {x y : V} (hS : ({s | Yt s y} : Finset κ).Nonempty)
    (hkh : ∀ d, k d ≠ 0 → h d = 1) (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ r, r ≤ η → ρ r = 1) (ha : 0 < a) (hG0 : ∀ w, 0 ≤ G x w) {M : ℝ}
    (hGM : ∑ w, G x w ≤ M) {c : ℝ} (hc : 0 ≤ c) (hK : 2 * (1 + c * M / η) ≤ K)
    (hpair : ∀ w, w ≠ y → (#{s | Yt s y ∧ Y s w} : ℝ) ≤ c * a * #{s | Yt s y}) :
    𝔼 s ∈ ({s | Yt s y} : Finset κ), denseAtom Y Yt k h ρ K a G s x y = k (G x y / a) := by
  set S : Finset κ := {s | Yt s y}
  set R : κ → ℝ := fun s => rowGate ρ K a G {w | Y s w} x
  by_cases hk0 : k (G x y / a) = 0
  · rw [hk0]
    refine expect_eq_zero fun s _ => ?_
    rw [denseAtom, hk0]
    split_ifs <;> simp
  have hh1 : h (G x y / a) = 1 := hkh _ hk0
  have hSr : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hKr : (0 : ℝ) < K := by
    have : 0 ≤ c * M / η := by
      have hM : 0 ≤ M := (sum_nonneg fun w _ => hG0 w).trans hGM
      positivity
    linarith
  have hKpos : 0 < K := by exact_mod_cast hKr
  -- the gate fails on at most half of the conditioning draws
  have hfail : (#{s ∈ S | R s < 1} : ℝ) * K ≤ #S * (1 + c * M / η) :=
    card_filter_rowGate_lt_one_mul_le S x ha hη hρη hG0 hGM hKpos hc fun w hwy => by
      have hset : ({s ∈ S | Y s w} : Finset κ) = ({s | Yt s y ∧ Y s w} : Finset κ) := by
        ext s; simp only [S, mem_filter, mem_univ, true_and]
      rw [hset]
      exact hpair w hwy
  have hhalf : (#{s ∈ S | R s < 1} : ℝ) ≤ #S / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  -- so the normalizer, the mean gate, lies in `[1/2, 1]`
  have hq : atomNormalizer Y Yt h ρ K a G x y = 𝔼 s ∈ S, R s := by
    simp only [atomNormalizer, atomPrep, hh1, one_mul, S, R]
  have hR1 : ∀ s, 1 - (if R s < 1 then 1 else 0) ≤ R s := fun s => by
    split_ifs with h
    · simp only [sub_self]; exact hρ0 _
    · simpa using not_lt.mp h
  have hq_lo : 1 / 2 ≤ 𝔼 s ∈ S, R s := by
    rw [expect_eq_sum_div_card, le_div_iff₀ hSr]
    calc 1 / 2 * (#S : ℝ) ≤ #S - #{s ∈ S | R s < 1} := by linarith
      _ = ∑ s ∈ S, (1 - (if R s < 1 then 1 else 0)) := by
          rw [sum_sub_distrib, sum_boole, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ s ∈ S, R s := sum_le_sum fun s _ => hR1 s
  have hq_hi : 𝔼 s ∈ S, R s ≤ 1 := expect_le hS fun s _ => hρ1 _
  have hclip : max (1 / 2) (min 1 (atomNormalizer Y Yt h ρ K a G x y)) = 𝔼 s ∈ S, R s := by
    rw [hq, min_eq_right hq_hi, max_eq_right hq_lo]
  have hpos : 0 < 𝔼 s ∈ S, R s := lt_of_lt_of_le (by norm_num) hq_lo
  -- the atom is `k · R / q` on the conditioning draws
  have hterm : ∀ s ∈ S, denseAtom Y Yt k h ρ K a G s x y =
      (k (G x y / a) / 𝔼 s ∈ S, R s) * R s := fun s hs => by
    have hs' : Yt s y := by simpa [S] using hs
    simp only [denseAtom, hs', ↓reduceIte, hclip, R]
    ring
  rw [expect_congr rfl hterm, ← mul_expect, div_mul_cancel₀ _ hpos.ne']

/-- **The dense atom identity for retention channels** [OpenAI2026LogSpace, Lemma 5.1], when the
usage channel is the rank channel `Y` at the atom's scale `f`, as for corrections and detector
scores. With `RetentionChannels` at rate `f > 0` and `c_π > 0`, the pair bound supplies the
retention hypothesis with `c = C_pair`. -/
theorem expect_denseAtom_of_retentionChannels {ι : Type*} [Fintype ι] {X : ι → V → Prop}
    [∀ s v, Decidable (X s v)] {π cπ Cπ Cpair Cvar : ℝ}
    (hch : Cslib.Probability.RetentionChannels X Y a π cπ Cπ Cpair Cvar) (ha : 0 < a)
    (hcπ : 0 < cπ) (hCpair : 0 ≤ Cpair) {x y : V} (hkh : ∀ d, k d ≠ 0 → h d = 1)
    (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ} (hη : 0 < η)
    (hρη : ∀ r, r ≤ η → ρ r = 1) (hG0 : ∀ w, 0 ≤ G x w) {M : ℝ} (hGM : ∑ w, G x w ≤ M)
    (hK : 2 * (1 + Cpair * M / η) ≤ K) :
    𝔼 s ∈ ({s | Y s y} : Finset κ), denseAtom Y Y k h ρ K a G s x y = k (G x y / a) := by
  have hcard : ∀ T : Finset κ, ((dens T : ℚ≥0) : ℝ) = #T / Fintype.card κ := fun T => by
    rw [dens_eq_card_div_card]; push_cast; rfl
  have hπ : 0 < π := (mul_pos hcπ ha).trans_le hch.lower
  have hκ : (0 : ℝ) < Fintype.card κ := by
    have h := hch.dens_Y y
    rw [hcard] at h
    rcases (Fintype.card κ).eq_zero_or_pos with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero] at h; linarith
    · exact_mod_cast h0
  have hS : ({s | Y s y} : Finset κ).Nonempty := by
    rw [← card_pos]
    by_contra h0
    have h := hch.dens_Y y
    rw [hcard, Nat.eq_zero_of_not_pos h0, Nat.cast_zero, zero_div] at h
    linarith
  refine expect_denseAtom hS hkh hρ0 hρ1 hη hρη ha hG0 hGM hCpair hK fun w hwy => ?_
  have hp := hch.pair w y hwy
  rw [hcard, hcard, ← mul_div_assoc, div_le_div_iff_of_pos_right hκ] at hp
  have hset : ({s | Y s y ∧ Y s w} : Finset κ) = ({s | Y s w ∧ Y s y} : Finset κ) := by
    ext s; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [hset]
  exact hp

end DenseAtom

end Matrix

namespace Cslib

/-- The **bin weights** for the scales `b`: `ω₀(w) = χ (w / b₀)` and
`ω_{k+1}(w) = χ (w / b_{k+1}) − χ (w / b_k)` [OpenAI2026LogSpace, (5.6)]. -/
@[expose] noncomputable def binWeight (χ : ℝ → ℝ) (b : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, w => χ (w / b 0)
  | k + 1, w => χ (w / b (k + 1)) - χ (w / b k)

variable {χ : ℝ → ℝ} {b : ℕ → ℝ}

/-- **The bin weights telescope**: `∑_{k ≤ n} ω_k(w) = χ (w / b_n)`. -/
theorem sum_range_binWeight (n : ℕ) (w : ℝ) :
    ∑ k ∈ range (n + 1), binWeight χ b k w = χ (w / b n) := by
  induction n with
  | zero => simp [binWeight]
  | succ n ih => rw [sum_range_succ, ih, binWeight]; ring

/-- **Bin decomposition** [OpenAI2026LogSpace, (5.7)]: if `χ` is one from `1` on and
`0 < b_n ≤ w`, then `w = ∑_{k ≤ n} w ω_k(w)`. -/
theorem sum_range_mul_binWeight (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {n : ℕ} (hb : 0 < b n) {w : ℝ}
    (hw : b n ≤ w) : ∑ k ∈ range (n + 1), w * binWeight χ b k w = w := by
  rw [← mul_sum, sum_range_binWeight, hχ1 _ ((one_le_div₀ hb).mpr hw), mul_one]

/-- For `0 ≤ w`, the ratio `w / b` grows as the positive scale `b` shrinks. -/
private theorem div_le_div_scale {w : ℝ} (hw : 0 ≤ w) {k : ℕ} (hb : ∀ k, 0 < b k)
    (hanti : Antitone b) : w / b k ≤ w / b (k + 1) :=
  div_le_div_of_nonneg_left hw (hb _) (hanti (Nat.le_succ k))

/-- **The bin weights are nonnegative** for a monotone switch that vanishes at `0`, decreasing
positive scales and `0 ≤ w`. -/
theorem binWeight_nonneg (hχ : Monotone χ) (hχ0 : χ 0 = 0) (hb : ∀ k, 0 < b k)
    (hanti : Antitone b) {w : ℝ} (hw : 0 ≤ w) (k : ℕ) : 0 ≤ binWeight χ b k w := by
  cases k with
  | zero =>
    rw [binWeight, ← hχ0]
    exact hχ (div_nonneg hw (hb 0).le)
  | succ k =>
    rw [binWeight, sub_nonneg]
    exact hχ (div_le_div_scale hw hb hanti)

/-- **Bin support** [OpenAI2026LogSpace, (5.8)]: if `χ` is zero through `1/2` and one from `1`
on, then `ω_{k+1}(w) ≠ 0` forces `b_{k+1} / 2 < w < b_k`, for decreasing positive scales. -/
theorem binWeight_succ_ne_zero (hχ0 : ∀ t, t ≤ 1 / 2 → χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hb : ∀ k, 0 < b k) (hanti : Antitone b) {k : ℕ} {w : ℝ}
    (hω : binWeight χ b (k + 1) w ≠ 0) : b (k + 1) / 2 < w ∧ w < b k := by
  rw [binWeight] at hω
  rcases lt_or_ge w 0 with hw | hw
  · exfalso
    have h1 : w / b (k + 1) ≤ 1 / 2 := (div_neg_of_neg_of_pos hw (hb _)).le.trans (by norm_num)
    have h2 : w / b k ≤ 1 / 2 := (div_neg_of_neg_of_pos hw (hb _)).le.trans (by norm_num)
    rw [hχ0 _ h1, hχ0 _ h2, sub_zero] at hω
    exact hω rfl
  have hmono := div_le_div_scale hw hb hanti (k := k)
  constructor
  · by_contra h
    have h1 : w / b (k + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (hb _)]; linarith
    rw [hχ0 _ h1, hχ0 _ (hmono.trans h1), sub_zero] at hω
    exact hω rfl
  · by_contra h
    have h1 : 1 ≤ w / b k := (one_le_div₀ (hb _)).mpr (not_lt.mp h)
    rw [hχ1 _ h1, hχ1 _ (h1.trans hmono), sub_self] at hω
    exact hω rfl

end Cslib
