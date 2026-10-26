/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Multilinearity
public import Complexity.Foundations.Data.Hamming.Expansion
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial soundness of the multilinearity test

This module proves the soundness theorem of Babai, Fortnow and Lund for the multilinearity test:
if in every direction fewer than an `ε` fraction of the axis-parallel lines carry a restriction of
`f` that is not affine, then `f` agrees with a multilinear function outside a
`3 n ^ 2 (ε + 1 / |F|)` fraction of the points, when `|F| ≥ 40 n ^ 2` and `ε ≤ 1 / (800 n ^ 3)`
(`Cslib.Code.exists_isMultilinear_hammingDist_lt`)
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991].

The test here reads whole lines, so its wrong lines are the lines that are not *correct* in the
sense of [Babai, Fortnow, Lund, Definition 5.3][BabaiFortnowLund1991]. For every `δ ∈ (0, 1]` a
`δ`-wrong line is not correct, so our hypothesis implies theirs for every such `δ`; our conclusion
is theirs with the `δ` term removed, which is what their bound gives as `δ` tends to `0`. Their
condition `δ ≤ 1 / (400 n ^ 2)` has no counterpart.

The proof follows theirs.

* **Self-improvement** (`Cslib.Code.IsMultilinear.hammingDist_le_of_two_mul_le`,
  [Babai, Fortnow, Lund, Lemma 5.10][BabaiFortnowLund1991]): a multilinear function that agrees
  with `f` on at least half of the points agrees with it outside at most
  `(2 n + 1) ∑ᵢ |Wᵢ| + 2 n ^ 2 |F| ^ (n - 1)` points, where `Wᵢ` is the set of points whose line
  in direction `i` is wrong. Let `B` be the set where they differ and `S` the points of `B` on no
  wrong line. A point on a line through a point of `S` that is outside `S` is on a wrong line, or
  is the unique point of a correct line where the two distinct affine restrictions agree. The
  Expansion Lemma (`Cslib.card_le_two_mul_card_lineClosure_sdiff`) bounds `S` by `2 n` times
  those points.
* **Induction on the dimension**, replacing their tree coloring
  [Babai, Fortnow, Lund, Lemma 5.12][BabaiFortnowLund1991]: the wrong points of the slices
  `x 0 = t` average to at most those of `f`, so when `f` has few wrong points, at least two
  slices have few (Markov's inequality with thresholds decreasing by a factor `1 - 1 / |F|` per
  dimension). By induction they are close to multilinear functions; interpolating those
  (`Cslib.Code.exists_isMultilinear_hammingDist_le_of_slices`, the interpolation step of
  [Babai, Fortnow, Lund, Lemma 5.11][BabaiFortnowLund1991]) gives a multilinear function within
  half of the points, and self-improvement brings it within a fifth.

The induction on slices in one direction, which needs only two good slices, is our
simplification of their tree argument over hyperplanes in all directions.

## Main results

* `Cslib.Code.IsMultilinear.hammingDist_le_of_two_mul_le`: the self-improvement lemma.
* `Cslib.Code.exists_isMultilinear_hammingDist_lt`: polynomial soundness of the multilinearity
  test.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991], Section 5
-/

@[expose] public section

namespace Cslib.Code

open Finset Function

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The points where the restrictions of `f` and `g` to the line in direction `i` are both affine
and distinct, but `f` and `g` agree: at most one on each line. -/
private def agreePoints (f g : (Fin n → F) → F) (i : Fin n) : Finset (Fin n → F) :=
  {x | IsAffineFun (lineRestrict f x i) ∧ lineRestrict f x i ≠ lineRestrict g x i ∧ f x = g x}

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem lineRestrict_update (f : (Fin n → F) → F) (x : Fin n → F) (i : Fin n) (t : F) :
    lineRestrict f (update x i t) i = lineRestrict f x i := by
  funext s
  simp [lineRestrict]

/-- Each line in direction `i` has at most one point where two distinct affine restrictions
agree, so there are at most `|F| ^ (n - 1)` such points. -/
private theorem card_agreePoints_le {f g : (Fin n → F) → F} (hg : IsMultilinear g) (i : Fin n) :
    #(agreePoints f g i) ≤ Fintype.card F ^ (n - 1) := by
  have hfib : #{y : Fin n → F | y i = 0} = Fintype.card F ^ (n - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset F) i (mem_univ 0)
    simpa [Fintype.piFinset_univ] using this
  rw [← hfib]
  refine card_le_card_of_injOn (fun x => update x i 0) (fun x _ => by simp) ?_
  intro x hx x' hx' hxx'
  simp only [agreePoints, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
  have hf : lineRestrict f x i = lineRestrict f x' i := by
    rw [← lineRestrict_update f x i 0, ← lineRestrict_update f x' i 0]
    exact congrArg (lineRestrict f · i) hxx'
  have hg' : lineRestrict g x i = lineRestrict g x' i := by
    rw [← lineRestrict_update g x i 0, ← lineRestrict_update g x' i 0]
    exact congrArg (lineRestrict g · i) hxx'
  have hxi : x i = x' i := by
    by_contra hne
    refine hx.2.1 (hx.1.eq_of_eq_of_eq (hg x i) hne ?_ ?_)
    · simpa [lineRestrict] using hx.2.2
    · rw [hf, hg']
      simpa [lineRestrict] using hx'.2.2
  calc x = update (update x i 0) i (x i) := by simp
    _ = update (update x' i 0) i (x' i) := by
      rw [show update x i 0 = update x' i 0 from hxx', hxi]
    _ = x' := by simp

/-- **The self-improvement lemma**: a multilinear function `g` that agrees with `f` on at least half
of the points agrees with it outside at most `(2 n + 1) ∑ᵢ |Wᵢ| + 2 n ^ 2 |F| ^ (n - 1)` points,
where `Wᵢ = wrongPoints f i` [Babai, Fortnow, Lund, Lemma 5.10][BabaiFortnowLund1991]. -/
theorem IsMultilinear.hammingDist_le_of_two_mul_le {f g : (Fin n → F) → F} (hg : IsMultilinear g)
    (h : 2 * hammingDist f g ≤ Fintype.card F ^ n) :
    hammingDist f g ≤
      (2 * n + 1) * ∑ i, #(wrongPoints f i) + 2 * n ^ 2 * Fintype.card F ^ (n - 1) := by
  let B : Finset (Fin n → F) := {x | f x ≠ g x}
  let W : Finset (Fin n → F) := univ.biUnion (wrongPoints f)
  let I : Finset (Fin n → F) := univ.biUnion (agreePoints f g)
  let S : Finset (Fin n → F) := B \ W
  have hB : #B = hammingDist f g := rfl
  -- A point outside `S` on a line through a point of `S` is wrong or an agreement point.
  have hcl : lineClosure S \ S ⊆ W ∪ I := by
    intro y hy
    simp only [mem_sdiff, mem_lineClosure] at hy
    obtain ⟨⟨i, t, hs⟩, hyS⟩ := hy
    simp only [S, B, W, mem_sdiff, mem_filter, mem_univ, true_and, mem_biUnion,
      not_exists] at hs hyS
    simp only [W, I, mem_union, mem_biUnion, mem_univ, true_and]
    by_cases hyW : ∃ j, y ∈ wrongPoints f j
    · exact Or.inl hyW
    right
    push Not at hyW
    have hfy : f y = g y := by
      by_contra hne
      exact hyS ⟨hne, hyW⟩
    have hcorr : IsAffineFun (lineRestrict f y i) := by
      have := hs.2 i
      simp only [wrongPoints, mem_filter, mem_univ, true_and, not_not] at this
      rwa [lineRestrict_update] at this
    refine ⟨i, ?_⟩
    simp only [agreePoints, mem_filter, mem_univ, true_and]
    refine ⟨hcorr, fun heq => hs.1 ?_, hfy⟩
    have := congrFun heq t
    simpa [lineRestrict] using this
  have hexp : #S ≤ 2 * n * #(lineClosure S \ S) := by
    refine card_le_two_mul_card_lineClosure_sdiff ?_
    exact (Nat.mul_le_mul_left 2 (card_le_card sdiff_subset)).trans (hB ▸ h)
  have hW : #W ≤ ∑ i, #(wrongPoints f i) := card_biUnion_le
  have hI : #I ≤ n * Fintype.card F ^ (n - 1) := by
    refine card_biUnion_le.trans ?_
    calc ∑ i, #(agreePoints f g i) ≤ ∑ _i : Fin n, Fintype.card F ^ (n - 1) :=
          sum_le_sum fun i _ => card_agreePoints_le hg i
      _ = n * Fintype.card F ^ (n - 1) := by simp
  have hBS : #B ≤ #S + #W := by
    refine (card_le_card ?_).trans (card_union_le S W)
    intro x hx
    by_cases hxW : x ∈ W
    · exact mem_union_right _ hxW
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxW⟩)
  have hcl' := (card_le_card hcl).trans (card_union_le W I)
  rw [← hB]
  calc #B ≤ 2 * n * (#W + #I) + #W := by nlinarith
    _ ≤ 2 * n * (∑ i, #(wrongPoints f i) + n * Fintype.card F ^ (n - 1)) +
          ∑ i, #(wrongPoints f i) := by gcongr
    _ = _ := by ring

/-- The wrong points of the slices `x 0 = t` add up to at most those of `f`. -/
private theorem sum_sum_card_wrongPoints_le (f : (Fin (n + 1) → F) → F) :
    ∑ t, ∑ j : Fin n, #(wrongPoints (fun y => f (Fin.cons t y)) j) ≤
      ∑ i, #(wrongPoints f i) := by
  rw [Fin.sum_univ_succ, sum_comm]
  simp only [← card_wrongPoints_succ]
  exact Nat.le_add_left _ _

/-- The induction on the dimension: with thresholds decreasing by a factor `1 - 1 / |F|` per
dimension, a function with few wrong points is within `γ` of a multilinear function. -/
private theorem exists_isMultilinear_hammingDist_le_mul {ε₀ γ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hγ : ε₀ + 2 * γ ≤ 1 / 2) :
    ∀ k : ℕ, (2 * k + 1) * ε₀ + 2 * k ^ 2 / (Fintype.card F : ℝ) ≤ γ →
      ∀ h : (Fin k → F) → F, (∑ i, (#(wrongPoints h i) : ℝ)) <
        (1 - 1 / (Fintype.card F : ℝ)) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k →
        ∃ g, IsMultilinear g ∧ (hammingDist h g : ℝ) ≤ γ * (Fintype.card F : ℝ) ^ k := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast (by omega : 1 ≤ Fintype.card F)
  have key : (1 - 1 / (Fintype.card F : ℝ)) * Fintype.card F = Fintype.card F - 1 := by
    field_simp
  intro k
  induction k with
  | zero =>
    intro hk h _
    refine ⟨h, fun _ i => i.elim0, ?_⟩
    simp only [hammingDist_self, Nat.cast_zero, pow_zero, mul_one]
    simp only [CharP.cast_eq_zero, mul_zero, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div] at hk
    linarith
  | succ k ih =>
    intro hk f hf
    have hk' : (2 * k + 1) * ε₀ + 2 * k ^ 2 / (Fintype.card F : ℝ) ≤ γ := by
      refine le_trans ?_ hk
      push_cast
      gcongr <;> nlinarith
    -- The threshold of the slices.
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
        θ = (1 - 1 / (Fintype.card F : ℝ)) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k := ⟨_, rfl⟩
    rw [← hθ] at ih
    have hT : (∑ i, (#(wrongPoints f i) : ℝ)) < ((Fintype.card F : ℝ) - 1) * θ := by
      calc _ < _ := hf
        _ = ((1 - 1 / (Fintype.card F : ℝ)) * Fintype.card F) *
            ((1 - 1 / (Fintype.card F : ℝ)) ^ k * ε₀ * (Fintype.card F : ℝ) ^ k) := by ring
        _ = _ := by rw [key, hθ]
    have hθpos : 0 < θ := by
      have h0 : (0 : ℝ) ≤ ∑ i, (#(wrongPoints f i) : ℝ) := by positivity
      have : 0 < ((Fintype.card F : ℝ) - 1) * θ := h0.trans_lt hT
      exact pos_of_mul_pos_right this (by linarith)
    -- At least two slices have fewer than `θ` wrong points.
    let good : Finset F := {t | (∑ j, (#(wrongPoints (fun y => f (Fin.cons t y)) j) : ℝ)) < θ}
    have hbad : (#goodᶜ : ℝ) * θ < ((Fintype.card F : ℝ) - 1) * θ := by
      calc (#goodᶜ : ℝ) * θ = ∑ _t ∈ goodᶜ, θ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ t ∈ goodᶜ, (∑ j, (#(wrongPoints (fun y => f (Fin.cons t y)) j) : ℝ)) := by
            refine sum_le_sum fun t ht => ?_
            simp only [good, mem_compl, mem_filter, mem_univ, true_and, not_lt] at ht
            exact ht
        _ ≤ ∑ t, (∑ j, (#(wrongPoints (fun y => f (Fin.cons t y)) j) : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
        _ ≤ ∑ i, (#(wrongPoints f i) : ℝ) := by exact_mod_cast sum_sum_card_wrongPoints_le f
        _ < _ := hT
    have hlt : (#goodᶜ : ℝ) < Fintype.card F - 1 := lt_of_mul_lt_mul_right hbad hθpos.le
    have hlt' : #goodᶜ + 1 < Fintype.card F := by
      have : ((#goodᶜ + 1 : ℕ) : ℝ) < Fintype.card F := by push_cast; linarith
      exact_mod_cast this
    have hcard : #good + #goodᶜ = Fintype.card F := card_add_card_compl good
    obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := one_lt_card.mp (by omega : 1 < #good)
    simp only [good, mem_filter, mem_univ, true_and] at ht₁ ht₂
    obtain ⟨g₁, hg₁, hd₁⟩ := ih hk' _ ht₁
    obtain ⟨g₂, hg₂, hd₂⟩ := ih hk' _ ht₂
    obtain ⟨g, hg, hfg⟩ := exists_isMultilinear_hammingDist_le_of_slices f h12 hg₁ hg₂
    refine ⟨g, hg, ?_⟩
    -- The wrong points of `f` are few.
    have hpow : (1 - 1 / (Fintype.card F : ℝ)) ^ (k + 1) ≤ 1 := by
      refine pow_le_one₀ ?_ ?_
      · rw [sub_nonneg, div_le_one hq]
        exact hq1
      · have : 0 ≤ 1 / (Fintype.card F : ℝ) := by positivity
        linarith
    have hTle : (∑ i, (#(wrongPoints f i) : ℝ)) ≤ ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by
      calc _ ≤ _ := hf.le
        _ ≤ 1 * ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by gcongr
        _ = ε₀ * (Fintype.card F : ℝ) ^ (k + 1) := by ring
    have hW0 : (#(wrongPoints f 0) : ℝ) ≤ ∑ i, (#(wrongPoints f i) : ℝ) :=
      single_le_sum (f := fun i => (#(wrongPoints f i) : ℝ)) (fun i _ => by positivity)
        (mem_univ (0 : Fin (k + 1)))
    -- The interpolation is within half of the points.
    have hhalf : (hammingDist f g : ℝ) ≤ (ε₀ + 2 * γ) * (Fintype.card F : ℝ) ^ (k + 1) := by
      calc (hammingDist f g : ℝ) ≤ #(wrongPoints f 0) +
            (Fintype.card F : ℝ) * ((hammingDist (fun y => f (Fin.cons t₁ y)) g₁ : ℝ) +
              hammingDist (fun y => f (Fin.cons t₂ y)) g₂) := by exact_mod_cast hfg
        _ ≤ ε₀ * (Fintype.card F : ℝ) ^ (k + 1) + (Fintype.card F : ℝ) *
              (γ * (Fintype.card F : ℝ) ^ k + γ * (Fintype.card F : ℝ) ^ k) := by
            gcongr
            linarith
        _ = (ε₀ + 2 * γ) * (Fintype.card F : ℝ) ^ (k + 1) := by ring
    have h2 : 2 * hammingDist f g ≤ Fintype.card F ^ (k + 1) := by
      have hqpow : 0 ≤ (Fintype.card F : ℝ) ^ (k + 1) := by positivity
      have : ((2 * hammingDist f g : ℕ) : ℝ) ≤ ((Fintype.card F ^ (k + 1) : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    -- Self-improvement brings it within `γ`.
    have hself := hg.hammingDist_le_of_two_mul_le h2
    rw [Nat.add_sub_cancel] at hself
    have hself' : (hammingDist f g : ℝ) ≤ (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        (∑ i, (#(wrongPoints f i) : ℝ)) + 2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ k := by
      exact_mod_cast hself
    calc (hammingDist f g : ℝ) ≤ _ := hself'
      _ ≤ (2 * ((k + 1 : ℕ) : ℝ) + 1) * (ε₀ * (Fintype.card F : ℝ) ^ (k + 1)) +
            2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ k := by gcongr
      _ = ((2 * ((k + 1 : ℕ) : ℝ) + 1) * ε₀ + 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / Fintype.card F) *
            (Fintype.card F : ℝ) ^ (k + 1) := by
          field_simp
          ring
      _ ≤ γ * (Fintype.card F : ℝ) ^ (k + 1) := by gcongr

/-- **Polynomial soundness of the multilinearity test**: if in every direction fewer than an `ε`
fraction of the lines carry a restriction of `f` that is not affine, `|F| ≥ 40 n ^ 2` and
`ε ≤ 1 / (800 n ^ 3)`, then some multilinear function agrees with `f` outside fewer than a
`3 n ^ 2 (ε + 1 / |F|)` fraction of the points
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991], for the whole-line test, where their
`δ` term vanishes. -/
theorem exists_isMultilinear_hammingDist_lt (f : (Fin n → F) → F) {ε : ℝ} (hn : 0 < n)
    (hq : 40 * n ^ 2 ≤ Fintype.card F) (hε : ε ≤ 1 / (800 * n ^ 3))
    (hW : ∀ i, (#(wrongPoints f i) : ℝ) < ε * Fintype.card F ^ n) :
    ∃ g, IsMultilinear g ∧
      (hammingDist f g : ℝ) < 3 * n ^ 2 * (ε + 1 / Fintype.card F) * Fintype.card F ^ n := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqr : 40 * (n : ℝ) ^ 2 ≤ Fintype.card F := by exact_mod_cast hq
  have hεpos : 0 < ε := by
    have h0 : (0 : ℝ) ≤ #(wrongPoints f ⟨0, hn⟩) := by positivity
    have : 0 < ε * (Fintype.card F : ℝ) ^ n := h0.trans_lt (hW ⟨0, hn⟩)
    exact pos_of_mul_pos_left this (by positivity)
  have hsum : (∑ i, (#(wrongPoints f i) : ℝ)) < n * ε * (Fintype.card F : ℝ) ^ n := by
    calc (∑ i, (#(wrongPoints f i) : ℝ)) < ∑ _i : Fin n, ε * (Fintype.card F : ℝ) ^ n :=
          sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ fun i _ => hW i
      _ = n * ε * (Fintype.card F : ℝ) ^ n := by simp [mul_assoc]
  -- Run the induction with `ε₀ = 2 n ε` and `γ = 1 / 5`.
  have hn3 : (1 : ℝ) ≤ n ^ 3 := one_le_pow₀ hnr
  have hεn : 800 * n ^ 3 * ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  have hqn : 2 * (n : ℝ) ^ 2 / Fintype.card F ≤ 1 / 20 := by
    rw [div_le_iff₀ hq0]
    nlinarith
  have hpow : (1 : ℝ) / 2 ≤ (1 - 1 / (Fintype.card F : ℝ)) ^ n := by
    have h1q : 1 / (Fintype.card F : ℝ) ≤ 1 := by
      rw [div_le_one hq0]
      nlinarith
    have hb := one_add_mul_le_pow (a := -(1 / (Fintype.card F : ℝ))) (by linarith) n
    have : (n : ℝ) * (1 / (Fintype.card F : ℝ)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hq0]
      nlinarith
    rw [← sub_eq_add_neg] at hb
    nlinarith
  have hn2 : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have hn3' : (n : ℝ) ^ 2 ≤ n ^ 3 := by nlinarith
  obtain ⟨g, hg, hfg⟩ := exists_isMultilinear_hammingDist_le_mul (F := F) (ε₀ := 2 * n * ε)
    (γ := 1 / 5) (by positivity) (by nlinarith) n (by nlinarith) f (by
      calc (∑ i, (#(wrongPoints f i) : ℝ)) < n * ε * (Fintype.card F : ℝ) ^ n := hsum
        _ = 1 / 2 * (2 * n * ε) * (Fintype.card F : ℝ) ^ n := by ring
        _ ≤ (1 - 1 / (Fintype.card F : ℝ)) ^ n * (2 * n * ε) * (Fintype.card F : ℝ) ^ n := by
          gcongr)
  refine ⟨g, hg, ?_⟩
  have h2 : 2 * hammingDist f g ≤ Fintype.card F ^ n := by
    have hqpow : 0 ≤ (Fintype.card F : ℝ) ^ n := by positivity
    have : ((2 * hammingDist f g : ℕ) : ℝ) ≤ ((Fintype.card F ^ n : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hself := hg.hammingDist_le_of_two_mul_le h2
  have hself' : (hammingDist f g : ℝ) ≤ (2 * (n : ℝ) + 1) * (∑ i, (#(wrongPoints f i) : ℝ)) +
      2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by
    exact_mod_cast hself
  have hqn1 : (Fintype.card F : ℝ) ^ (n - 1) * Fintype.card F = (Fintype.card F : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hqpow : 0 ≤ (Fintype.card F : ℝ) ^ (n - 1) := by positivity
  calc (hammingDist f g : ℝ) ≤ _ := hself'
    _ < (2 * n + 1) * (n * ε * (Fintype.card F : ℝ) ^ n) +
          2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by gcongr
    _ ≤ 3 * n ^ 2 * ε * (Fintype.card F : ℝ) ^ n +
          2 * (n : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ (n - 1) := by
        have : 0 ≤ ε * (Fintype.card F : ℝ) ^ n := by positivity
        nlinarith
    _ ≤ 3 * n ^ 2 * (ε + 1 / Fintype.card F) * (Fintype.card F : ℝ) ^ n := by
        rw [← hqn1]
        field_simp
        nlinarith

end Cslib.Code
