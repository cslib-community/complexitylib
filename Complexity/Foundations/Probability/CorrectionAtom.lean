/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.StochasticAtom
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Correction atoms with an incoming gate

A *correction atom* represents an entry `Q (G x y / f) · g₀(y)` of a correction matrix as the
conditional mean of a bounded table, like the dense atoms of
`Complexity.Foundations.Probability.StochasticAtom`. Its table also has few nonzero entries in each
*column*. That bound is what lets later error estimates sum over the sources of a column. This is
idea 6 in issue #474, following the OpenAI preprint [OpenAI2026LogSpace, Sections 5.3 and 5.5].

**The incoming gate.** A draw is a pair `(s, t)` of independent seeds: `s` for the start channel
`X`, which retains sources, and `t` for the terminal channel (rank channel `Y`, usage channel
`Yt`). The *auxiliary score* of a source `x'` at column `y` is `I (G x' y / f, rank_K {G x' w / f :
Y t w})` (`Matrix.auxScore`). The *incoming gate* of column `y` is
`τ (rank_{K_c} {aux x' y : X s x'})` (`Matrix.incomingGate`) [OpenAI2026LogSpace, (5.12)]. The atom
is
`1{Yt t y} · Q (G x y / f) · R · T_y / c(q_y) · g₀(y)` (`Matrix.correctionAtom`), where `R` is the
row gate of `x`, `T_y` the incoming gate, `c(q) = max (1/2) (min 1 q)`, and `q_y` the conditional
mean of the preparatory value `h (G x y / f) · R · T_y` given `X(x)` and `Yt(y)`
(`Matrix.correctionPrep`, `Matrix.correctionNormalizer`) [OpenAI2026LogSpace, (5.13), (5.14)].

**The identity** [OpenAI2026LogSpace, Lemma 5.3]. The conditional mean of the atom is exactly
`Q (G x y / f) · g₀(y)` (`Matrix.expect_correctionAtom`). The row gate fails on at most a quarter
of the conditioning draws, by `Matrix.card_filter_rowGate_lt_one_mul_le`. The auxiliary score can
exceed the gate's threshold only on a fixed set `D` of sources, and the incoming gate fails only
if `K_c` members of `D` are retained (`Matrix.card_filter_incomingGate_lt_one_mul_le`). When
`g₀(y) ≠ 0`, the hypothesis `p · #D ≤ B` (the preprint's column bound (5.2)) makes this rare too.
When `g₀(y) = 0` both sides vanish and no bound on `D` is needed. Both gates are then full on half
of the draws, and the normalization principle (`Finset.expect_mul_div_clip_eq`) applies. The
failure bounds use no independence between gates.

**The incoming cap** [OpenAI2026LogSpace, (5.18), Lemma 5.6]. If `I = 1` wherever `Q` and `ρ` are
both nonzero, and `τ` vanishes from `g ≤ 1` on, then on every draw a column has fewer than `K_c`
retained sources with a nonzero atom (`Matrix.card_filter_correctionAtom_col_ne_zero_lt`). `K_c`
such sources would all have score one, which closes the incoming gate
(`Matrix.incomingGate_eq_zero`). Rows have fewer than `K` nonzero atoms, as for dense atoms
(`Matrix.card_filter_correctionAtom_row_ne_zero_lt`).

## Main definitions

* `Matrix.auxScore`, `Matrix.incomingGate`: the auxiliary score and the incoming gate.
* `Matrix.correctionPrep`, `Matrix.correctionNormalizer`, `Matrix.correctionAtom`: the atom.

## Main results

* `Finset.expect_mul_div_clip_eq`: the normalization principle.
* `Finset.card_filter_le_card_filter_mul_le`: few draws retain many members of a sparse set.
* `Matrix.card_filter_incomingGate_lt_one_mul_le`: the incoming gate rarely fails.
* `Matrix.expect_correctionAtom`: the correction atom identity.
* `Matrix.abs_correctionAtom_le`: the atom is bounded.
* `Matrix.incomingGate_eq_zero`, `Matrix.card_filter_correctionAtom_col_ne_zero_lt`,
  `Matrix.card_filter_correctionAtom_row_ne_zero_lt`: the incoming cap and the support bounds.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 5.1, 5.3 and 5.5 (preprint, not peer reviewed)
-/

public section

open Finset
open scoped BigOperators

namespace Finset

variable {Ω : Type*}

/-- **The normalization principle** [OpenAI2026LogSpace, Section 5.1]. Let a gate `γ` take values
in `[0, 1]` on a nonempty finite set `S` of draws, and be below one on at most half of them. Then
dividing by its clipped mean `c(q) = max (1/2) (min 1 q)` removes the gate's bias:
`𝔼_S [m · γ / c(𝔼_S γ)] = m`. -/
theorem expect_mul_div_clip_eq {S : Finset Ω} (hS : S.Nonempty) {γ : Ω → ℝ}
    (hγ0 : ∀ s ∈ S, 0 ≤ γ s) (hγ1 : ∀ s ∈ S, γ s ≤ 1) (hfail : 2 * (#{s ∈ S | γ s < 1} : ℝ) ≤ #S)
    (m : ℝ) : 𝔼 s ∈ S, m * γ s / max (1 / 2) (min 1 (𝔼 s ∈ S, γ s)) = m := by
  have hSr : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hγ : ∀ s ∈ S, 1 - (if γ s < 1 then 1 else 0) ≤ γ s := fun s hs => by
    split_ifs with h
    · rw [sub_self]; exact hγ0 s hs
    · simpa using not_lt.mp h
  have hlo : 1 / 2 ≤ 𝔼 s ∈ S, γ s := by
    rw [expect_eq_sum_div_card, le_div_iff₀ hSr]
    calc 1 / 2 * (#S : ℝ) ≤ #S - #{s ∈ S | γ s < 1} := by linarith
      _ = ∑ s ∈ S, (1 - (if γ s < 1 then 1 else 0)) := by
          rw [sum_sub_distrib, sum_boole, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ s ∈ S, γ s := sum_le_sum hγ
  have hhi : 𝔼 s ∈ S, γ s ≤ 1 := expect_le hS hγ1
  have hpos : 0 < 𝔼 s ∈ S, γ s := lt_of_lt_of_le (by norm_num) hlo
  rw [min_eq_right hhi, max_eq_right hlo]
  simp only [mul_div_assoc]
  rw [← mul_expect, ← expect_div, div_self hpos.ne', mul_one]

variable {V : Type*}

/-- **Few draws retain many members of a sparse set** (Markov's inequality). Let every member
`w ≠ x` of `D` be retained on at most a `p` fraction of the draws in `S`. Then at most a
`(1 + p #D) / K` fraction of the draws retain `K > 0` members of `D`. The vertex `x` itself
contributes at most one per draw. -/
theorem card_filter_le_card_filter_mul_le {ι : Type*} (X : ι → V → Prop) [∀ s v, Decidable (X s v)]
    (S : Finset ι) (D : Finset V) (x : V) {p : ℝ} (hp : 0 ≤ p)
    (hpair : ∀ w ∈ D, w ≠ x → (#{s ∈ S | X s w} : ℝ) ≤ p * #S) (K : ℕ) :
    (#{s ∈ S | K ≤ #{w ∈ D | X s w}} : ℝ) * K ≤ #S * (1 + p * #D) := by
  classical
  have hMarkov : (#{s ∈ S | K ≤ #{w ∈ D | X s w}} : ℝ) * K ≤ ∑ s ∈ S, (#{w ∈ D | X s w} : ℝ) :=
    card_filter_mul_le_sum S _ _ (fun _ _ => by positivity) fun s _ hs => by exact_mod_cast hs
  have hswap : ∑ s ∈ S, (#{w ∈ D | X s w} : ℝ) = ∑ w ∈ D, (#{s ∈ S | X s w} : ℝ) := by
    simp only [natCast_card_filter]
    exact sum_comm
  have hterm : ∀ w ∈ D, (#{s ∈ S | X s w} : ℝ) ≤ (if x = w then (#S : ℝ) else 0) + p * #S := by
    intro w hw
    by_cases hxw : x = w
    · have hle : (#{s ∈ S | X s w} : ℝ) ≤ #S := by exact_mod_cast card_filter_le _ _
      have : 0 ≤ p * #S := by positivity
      simp only [hxw, ↓reduceIte]
      linarith
    · simp only [hxw, ↓reduceIte, zero_add]
      exact hpair w hw (Ne.symm hxw)
  calc (#{s ∈ S | K ≤ #{w ∈ D | X s w}} : ℝ) * K
      ≤ ∑ w ∈ D, ((if x = w then (#S : ℝ) else 0) + p * #S) :=
        hMarkov.trans (hswap ▸ sum_le_sum hterm)
    _ = (if x ∈ D then (#S : ℝ) else 0) + #D * (p * #S) := by
        rw [sum_add_distrib, sum_ite_eq, sum_const, nsmul_eq_mul]
    _ ≤ #S * (1 + p * #D) := by
        have : (if x ∈ D then (#S : ℝ) else 0) ≤ #S := by split_ifs <;> [exact le_rfl; positivity]
        nlinarith

end Finset

namespace Matrix

variable {V ι κ : Type*} [Fintype V]

section Definitions

variable (I : ℝ → ℝ → ℝ) (τ : ℝ → ℝ) (K Kc : ℕ) (f : ℝ) (G : Matrix V V ℝ)

/-- The **auxiliary score** of the entry `(x, y)` for the retained set `T` of the rank channel:
`I (G x y / f, rank_K {G x w / f : w ∈ T})` [OpenAI2026LogSpace, (5.5)]. -/
@[expose] noncomputable def auxScore (T : Finset V) (x y : V) : ℝ :=
  I (G x y / f) (kthLargest K T fun w => G x w / f)

/-- The **incoming gate** of column `y`: `τ (rank_{K_c} {auxScore x y : x ∈ S})` over the retained
set `S` of sources [OpenAI2026LogSpace, (5.12)]. -/
@[expose] noncomputable def incomingGate (S T : Finset V) (y : V) : ℝ :=
  τ (kthLargest Kc S fun x => auxScore I K f G T x y)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (X : ι → V → Prop) (Y Yt : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Yt t v)]
  (Q h ρ : ℝ → ℝ) (g₀ : V → ℝ)

/-- The **preparatory value** of a correction atom: `h (G x y / f) · R · T_y`, with the row gate
`R` and the incoming gate `T_y` [OpenAI2026LogSpace, (5.13)]. -/
@[expose] noncomputable def correctionPrep (S T : Finset V) (x y : V) : ℝ :=
  h (G x y / f) * rowGate ρ K f G T x * incomingGate I τ K Kc f G S T y

/-- The **normalizer** `q_y` of a correction atom: the mean of the preparatory value over the
draws that retain `x` in the start channel and `y` in the usage channel
[OpenAI2026LogSpace, (5.13)]. -/
@[expose] noncomputable def correctionNormalizer (x y : V) : ℝ :=
  𝔼 d ∈ ({s | X s x} : Finset ι) ×ˢ ({t | Yt t y} : Finset κ),
    correctionPrep I τ K Kc f G h ρ {w | X d.1 w} {w | Y d.2 w} x y

/-- The **correction atom** at `(x, y)` on the draw `d = (s, t)`:
`1{Yt t y} · Q (G x y / f) · R · T_y / c(q_y) · g₀(y)` [OpenAI2026LogSpace, (5.14)]. -/
@[expose] noncomputable def correctionAtom (d : ι × κ) (x y : V) : ℝ :=
  if Yt d.2 y then
    Q (G x y / f) * (rowGate ρ K f G {w | Y d.2 w} x *
        incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y) /
      max (1 / 2) (min 1 (correctionNormalizer I τ K Kc f G X Y Yt h ρ x y)) * g₀ y
  else 0

end Definitions

variable {I : ℝ → ℝ → ℝ} {τ : ℝ → ℝ} {K Kc : ℕ} {f : ℝ} {G : Matrix V V ℝ}

omit [Fintype V] in
/-- **The incoming cap** [OpenAI2026LogSpace, Lemma 5.6]: if `τ` vanishes from `g ≤ 1` on and at
least `K_c > 0` retained sources have auxiliary score at least one at column `y`, the incoming
gate of `y` is closed. -/
theorem incomingGate_eq_zero {S T : Finset V} {y : V} (hKc : 0 < Kc) {g : ℝ} (hg : g ≤ 1)
    (hτ : ∀ r, g ≤ r → τ r = 0) (hcard : Kc ≤ #{x ∈ S | 1 ≤ auxScore I K f G T x y}) :
    incomingGate I τ K Kc f G S T y = 0 :=
  hτ _ (hg.trans ((le_kthLargest_iff hKc one_pos).mpr hcard))

/-- **The incoming gate rarely fails** [OpenAI2026LogSpace, proof of Lemma 5.3]. Let `τ` be one
through `τ₀ ≥ 0` and `I` vanish when its first argument is at most `e`, so a score above `τ₀`
needs a source in `D = {x' | e < G x' y / f}`. If every member `w ≠ x` of `D` is retained on at
most a `p` fraction of the draws in `S`, then for every terminal set `T` the incoming gate is
below one on at most a `(1 + p #D) / K_c` fraction of `S`. -/
theorem card_filter_incomingGate_lt_one_mul_le (X : ι → V → Prop)
    [∀ s v, Decidable (X s v)] (S : Finset ι) (T : Finset V) (x y : V) (hKc : 0 < Kc)
    {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) (hττ : ∀ r, r ≤ τ₀ → τ r = 1) {e : ℝ}
    (hI : ∀ v r, v ≤ e → I v r = 0) {p : ℝ} (hp : 0 ≤ p)
    (hpair : ∀ w, e < G w y / f → w ≠ x → (#{s ∈ S | X s w} : ℝ) ≤ p * #S) :
    (#{s ∈ S | incomingGate I τ K Kc f G {w | X s w} T y < 1} : ℝ) * Kc ≤
      #S * (1 + p * #({w | e < G w y / f} : Finset V)) := by
  set D : Finset V := {w | e < G w y / f}
  refine le_trans ?_ (card_filter_le_card_filter_mul_le X S D x hp
    (fun w hw hwx => hpair w (by simpa [D] using hw) hwx) Kc)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Nat.cast_le.mpr (card_le_card fun s hs => ?_)
  rw [mem_filter] at hs ⊢
  refine ⟨hs.1, ?_⟩
  have hlt : τ₀ < kthLargest Kc {w | X s w} fun w => auxScore I K f G T w y := by
    by_contra hle
    rw [incomingGate, hττ _ (not_lt.mp hle)] at hs
    exact lt_irrefl _ hs.2
  refine ((lt_kthLargest_iff hKc hτ₀).mp hlt).trans (card_le_card fun w hw => ?_)
  rw [mem_filter] at hw ⊢
  refine ⟨?_, by simpa using hw.1⟩
  simp only [D, mem_filter, mem_univ, true_and]
  by_contra hle
  rw [auxScore, hI _ _ (not_lt.mp hle)] at hw
  exact absurd hw.2 (not_lt.mpr hτ₀)

omit [Fintype V] in
/-- A product of two gates with values in `[0, 1]` is at most one. -/
private theorem mul_le_one_of_gate {r t : ℝ} (hr : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    r * t ≤ 1 :=
  (mul_le_mul_of_nonneg_right hr ht0).trans (by rw [one_mul]; exact ht1)

variable [Fintype ι] [Fintype κ] {X : ι → V → Prop} {Y Yt : κ → V → Prop}
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Yt t v)]
  {Q h ρ : ℝ → ℝ} {g₀ : V → ℝ}

/-- **The correction atom is bounded**: `|F(x, y)| ≤ 2 |Q (G x y / f)| |g₀(y)|` on every draw,
when the row and incoming gate functions take values in `[0, 1]`. -/
theorem abs_correctionAtom_le (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) (hτ0 : ∀ r, 0 ≤ τ r)
    (hτ1 : ∀ r, τ r ≤ 1) (d : ι × κ) (x y : V) :
    |correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ d x y| ≤ 2 * |Q (G x y / f)| * |g₀ y| := by
  rw [correctionAtom]
  split_ifs
  · set γ := rowGate ρ K f G {w | Y d.2 w} x *
      incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y
    have hγ0 : 0 ≤ γ := mul_nonneg (hρ0 _) (hτ0 _)
    have hγ1 : γ ≤ 1 := mul_le_one_of_gate (hρ1 _) (hτ0 _) (hτ1 _)
    set c := max (1 / 2) (min 1 (correctionNormalizer I τ K Kc f G X Y Yt h ρ x y))
    have hc : (1 / 2 : ℝ) ≤ c := le_max_left _ _
    have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hγ0, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_iff₀ hc0]
    calc |Q (G x y / f)| * γ ≤ |Q (G x y / f)| * 1 := mul_le_mul_of_nonneg_left hγ1 (abs_nonneg _)
      _ = 2 * |Q (G x y / f)| * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  · rw [abs_zero]; positivity

/-- **Row support** [OpenAI2026LogSpace, Lemma 5.6]: if `Q` vanishes through `e ≥ 0` and `ρ`
vanishes from `g ≤ e` on, then on every draw fewer than `K > 0` correction atoms of a row are
nonzero among the vertices the rank channel retains. -/
theorem card_filter_correctionAtom_row_ne_zero_lt (hK : 0 < K) {e g : ℝ} (he : 0 ≤ e)
    (hQ : ∀ v, v ≤ e → Q v = 0) (hg : g ≤ e) (hρ : ∀ r, g ≤ r → ρ r = 0) (d : ι × κ) (x : V) :
    #{y ∈ ({w | Y d.2 w} : Finset V) | correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ d x y ≠ 0} <
      K := by
  refine lt_of_le_of_lt (card_le_card fun y hy => ?_)
    (card_filter_mul_rowGate_ne_zero_lt (a := f) (G := G) {w | Y d.2 w} x hK he hQ hg hρ)
  rw [mem_filter] at hy ⊢
  refine ⟨hy.1, fun h0 => hy.2 ?_⟩
  rw [correctionAtom]
  split_ifs
  · rw [← mul_assoc, h0, zero_mul, zero_div, zero_mul]
  · rfl

/-- **Column support: the incoming cap** [OpenAI2026LogSpace, (5.18), Lemma 5.6]. Suppose the
auxiliary score is one wherever `Q` and `ρ` are both nonzero, and `τ` vanishes from `g ≤ 1` on.
Then on every draw fewer than `K_c > 0` retained sources have a nonzero atom in column `y`:
`K_c` of them would close the incoming gate, which makes the whole column zero. -/
theorem card_filter_correctionAtom_col_ne_zero_lt (hKc : 0 < Kc)
    (hIQ : ∀ v r, Q v ≠ 0 → ρ r ≠ 0 → I v r = 1) {g : ℝ} (hg : g ≤ 1)
    (hτ : ∀ r, g ≤ r → τ r = 0) (d : ι × κ) (y : V) :
    #{x ∈ ({w | X d.1 w} : Finset V) | correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ d x y ≠ 0} <
      Kc := by
  by_contra hle
  rw [not_lt] at hle
  have hgate : incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y = 0 := by
    refine incomingGate_eq_zero hKc hg hτ (hle.trans (card_le_card fun x hx => ?_))
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, le_of_eq (hIQ _ _ (fun hQ => hx.2 ?_) (fun hρ => hx.2 ?_)).symm⟩
    · rw [correctionAtom]; split_ifs <;> simp [hQ]
    · rw [correctionAtom]; split_ifs <;> simp [rowGate, hρ]
  obtain ⟨x, hx⟩ := card_pos.mp (hKc.trans_le hle)
  rw [mem_filter, correctionAtom, hgate] at hx
  split_ifs at hx <;> simp at hx

/-- **The correction atom identity, including zero multipliers** [OpenAI2026LogSpace, Lemma 5.3].
Let `h = 1` wherever `Q ≠ 0`; let `ρ, τ ∈ [0, 1]`, with `ρ` one through `η > 0` and `τ` one
through `τ₀ ≥ 0`; and let `I` vanish when its first argument is at most `e`. Let row `x` of
`G ≥ 0` have mass at most `M`. Suppose the draws retaining `x` in `X` and `y` in `Yt` are
nonempty, and two pair bounds hold. Every `w ≠ y` is retained by `Y` on at most a `c f` fraction
of the draws with `Yt(y)`. Every `w ≠ x` is retained by `X` on at most a `p` fraction of the draws
with `X(x)`. If `g₀(y) ≠ 0`, let the sources that can score satisfy
`p · #{w | e < G w y / f} ≤ B`. Then, for `K ≥ 4 (1 + c M / η)` and `K_c ≥ 4 (1 + B)`, the
conditional mean of the atom is exactly `Q (G x y / f) · g₀(y)`. -/
theorem expect_correctionAtom {x y : V} (hSx : ({s | X s x} : Finset ι).Nonempty)
    (hSy : ({t | Yt t y} : Finset κ).Nonempty) (hQh : ∀ v, Q v ≠ 0 → h v = 1)
    (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ} (hη : 0 < η) (hρη : ∀ r, r ≤ η → ρ r = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀)
    (hττ : ∀ r, r ≤ τ₀ → τ r = 1) {e : ℝ} (hI : ∀ v r, v ≤ e → I v r = 0) (hf : 0 < f)
    (hG0 : ∀ w, 0 ≤ G x w) {M : ℝ} (hGM : ∑ w, G x w ≤ M) {c : ℝ} (hc : 0 ≤ c)
    (hK : 4 * (1 + c * M / η) ≤ K)
    (hpairY : ∀ w, w ≠ y → (#{t | Yt t y ∧ Y t w} : ℝ) ≤ c * f * #{t | Yt t y}) {p : ℝ}
    (hp : 0 ≤ p) (hpairX : ∀ w, w ≠ x → (#{s | X s x ∧ X s w} : ℝ) ≤ p * #{s | X s x}) {B : ℝ}
    (hB : g₀ y ≠ 0 → p * #({w | e < G w y / f} : Finset V) ≤ B) (hKc : 4 * (1 + B) ≤ Kc) :
    𝔼 d ∈ ({s | X s x} : Finset ι) ×ˢ ({t | Yt t y} : Finset κ),
      correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ d x y = Q (G x y / f) * g₀ y := by
  set Sx : Finset ι := {s | X s x}
  set Sy : Finset κ := {t | Yt t y}
  set C := Sx ×ˢ Sy
  set γ : ι × κ → ℝ := fun d => rowGate ρ K f G {w | Y d.2 w} x *
    incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y
  -- trivial cases: a zero entry or a zero multiplier
  by_cases hz : Q (G x y / f) * g₀ y = 0
  · rw [hz]
    refine expect_eq_zero fun d _ => ?_
    rw [correctionAtom]
    split_ifs
    · rcases mul_eq_zero.mp hz with h0 | h0 <;> simp [h0]
    · rfl
  obtain ⟨hQ0, hg0⟩ := mul_ne_zero_iff.mp hz
  have hh1 : h (G x y / f) = 1 := hQh _ hQ0
  have hSxr : (0 : ℝ) < #Sx := by exact_mod_cast hSx.card_pos
  have hSyr : (0 : ℝ) < #Sy := by exact_mod_cast hSy.card_pos
  have hM : 0 ≤ M := (sum_nonneg fun w _ => hG0 w).trans hGM
  have hKr : (0 : ℝ) < K := by
    have : 0 ≤ c * M / η := by positivity
    linarith
  have hBnn : 0 ≤ B := (by positivity : (0 : ℝ) ≤ p * #({w | e < G w y / f} : Finset V)).trans
    (hB hg0)
  have hKcr : (0 : ℝ) < Kc := by linarith
  -- the row gate fails on at most a quarter of the terminal draws
  have hR : (#{t ∈ Sy | rowGate ρ K f G {w | Y t w} x < 1} : ℝ) * 4 ≤ #Sy := by
    have h := card_filter_rowGate_lt_one_mul_le Sy x hf hη hρη hG0 hGM (by exact_mod_cast hKr) hc
      fun w hwy => by
        have hset : ({t ∈ Sy | Y t w} : Finset κ) = ({t | Yt t y ∧ Y t w} : Finset κ) := by
          ext t; simp only [Sy, mem_filter, mem_univ, true_and]
        rw [hset]
        exact hpairY w hwy
    nlinarith
  -- the incoming gate fails on at most a quarter of the start draws, for every terminal set
  have hT : ∀ T : Finset V,
      (#{s ∈ Sx | incomingGate I τ K Kc f G {w | X s w} T y < 1} : ℝ) * 4 ≤ #Sx := by
    intro T
    have h := card_filter_incomingGate_lt_one_mul_le (τ := τ) (K := K) (f := f) (G := G) X Sx T x
      y (by exact_mod_cast hKcr) hτ₀ hττ
      hI hp fun w _ hwx => by
        have hset : ({s ∈ Sx | X s w} : Finset ι) = ({s | X s x ∧ X s w} : Finset ι) := by
          ext s; simp only [Sx, mem_filter, mem_univ, true_and]
        rw [hset]
        exact hpairX w hwx
    have h1 : #Sx * (1 + p * #({w | e < G w y / f} : Finset V)) ≤ #Sx * (1 + B) := by
      have := hB hg0
      gcongr
    nlinarith
  -- so the product gate fails on at most half of the conditioning draws
  have hfail : 2 * (#{d ∈ C | γ d < 1} : ℝ) ≤ #C := by
    have hsplit : ∀ d, (if γ d < 1 then (1 : ℝ) else 0) ≤
        (if rowGate ρ K f G {w | Y d.2 w} x < 1 then 1 else 0) +
          (if incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y < 1 then 1 else 0) := by
      intro d
      by_cases h1 : rowGate ρ K f G {w | Y d.2 w} x < 1
      · split_ifs <;> norm_num
      by_cases h2 : incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y < 1
      · split_ifs <;> norm_num
      have hr : rowGate ρ K f G {w | Y d.2 w} x = 1 := le_antisymm (hρ1 _) (not_lt.mp h1)
      have ht : incomingGate I τ K Kc f G {w | X d.1 w} {w | Y d.2 w} y = 1 :=
        le_antisymm (hτ1 _) (not_lt.mp h2)
      simp only [γ, hr, ht, mul_one, lt_irrefl, ↓reduceIte]
      norm_num
    have hcount : (#{d ∈ C | γ d < 1} : ℝ) ≤
        #Sx * #{t ∈ Sy | rowGate ρ K f G {w | Y t w} x < 1} +
          ∑ t ∈ Sy, (#{s ∈ Sx | incomingGate I τ K Kc f G {w | X s w} {w | Y t w} y < 1} : ℝ) := by
      rw [natCast_card_filter]
      refine (sum_le_sum fun d _ => hsplit d).trans_eq ?_
      rw [sum_add_distrib, sum_product, sum_product_right]
      simp only [sum_const, nsmul_eq_mul, ← natCast_card_filter]
    have hsum : (∑ t ∈ Sy,
        (#{s ∈ Sx | incomingGate I τ K Kc f G {w | X s w} {w | Y t w} y < 1} : ℝ)) * 4 ≤
          #Sy * #Sx := by
      rw [sum_mul]
      calc ∑ t ∈ Sy, (#{s ∈ Sx | incomingGate I τ K Kc f G {w | X s w} {w | Y t w} y < 1} :
            ℝ) * 4 ≤ ∑ _t ∈ Sy, (#Sx : ℝ) := sum_le_sum fun t _ => hT _
        _ = #Sy * #Sx := by rw [sum_const, nsmul_eq_mul]
    have hC : (#C : ℝ) = #Sx * #Sy := by rw [card_product]; push_cast; ring
    rw [hC]
    nlinarith [mul_le_mul_of_nonneg_left hR hSxr.le]
  -- the normalizer is the mean of the product gate, and the normalization principle applies
  have hq : correctionNormalizer I τ K Kc f G X Y Yt h ρ x y = 𝔼 d ∈ C, γ d := by
    simp only [correctionNormalizer, correctionPrep, hh1, one_mul, γ, C, Sx, Sy]
  have hterm : ∀ d ∈ C, correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ d x y =
      Q (G x y / f) * γ d / max (1 / 2) (min 1 (𝔼 d ∈ C, γ d)) * g₀ y := fun d hd => by
    have hd' : Yt d.2 y := by simpa [C, Sy] using (mem_product.mp hd).2
    simp only [correctionAtom, hd', ↓reduceIte, hq, γ]
  have key : 𝔼 d ∈ C, Q (G x y / f) * γ d / max (1 / 2) (min 1 (𝔼 d ∈ C, γ d)) =
      Q (G x y / f) :=
    expect_mul_div_clip_eq (hSx.product hSy) (fun d _ => mul_nonneg (hρ0 _) (hτ0 _))
      (fun d _ => mul_le_one_of_gate (hρ1 _) (hτ0 _) (hτ1 _)) hfail _
  rw [expect_congr rfl hterm, ← expect_mul, key]

end Matrix
