/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Decode
public import CslibFrontier.Foundations.Combinatorics.Hypergeometric.Miss
import CslibFrontier.Foundations.Data.Fintype.AgreeOn
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Density of good direct-product seeds

This module completes the counting analysis of the direct-product decoder `dpDecode` of
[Impagliazzo, Jaiswal, Kabanets and Wigderson][ImpagliazzoJaiswalKabanetsWigderson2010] (preprint
of 2009-10-19, Theorem 1.2; Carmosino, Impagliazzo, Kabanets and Kolokolova cite it as their
Theorem 4.1). It is stated for the library formulation of the decoder module: uniform `k`-tuples
with a random position subset in place of IJKW's `k`-sets.

The per-seed theorem `card_filter_dpDecode_err_le_ge` assumes two things about a seed `(P, b₀)`:
the consistent tuples have density at least `δ / 2`, and at most an `ε / 64` fraction of them
have `ε k / 64` or more disagreements with `f`. This module shows that a `δ / 4` fraction of the
pairs `(P, b₀)`, with `P` an `s`-subset, satisfy both, provided `C'` agrees with `f ^ k` on a `δ`
fraction of tuples. It then counts the seeds `(P, b₀, v)` that decode well. The density step has
two parts. A seed whose class among the agreeing tuples is small is rare
(`card_filter_card_filter_agree_lt_le`). A consistent tuple of an agreeing seed disagrees with
`f` only outside `P`, and a random `s`-subset rarely misses `ε k / 64` positions, so heavy
consistent tuples are rare (`sum_sum_card_heavy_le`, via
`card_filter_disjoint_powersetCard_le`). In the tuple formulation this takes the place of IJKW's
Lemmas 3.11–3.12 (excellent edges are abundant, and a random seed is good with noticeable
probability); the per-seed analysis of their Lemmas 3.8–3.10 is in the decoder module.

The constants (`2 s ≤ k`, `s ≥ (64 / ε) log (512 / (ε δ ^ 2))`, `m ≥ (16 / δ) log (8 / ε)` and the
fraction `δ / 8`) are ours, derived for the tuple formulation; they are not IJKW's. The results
are counting statements about a pure function; `DirectProduct.Complexity` bounds the decoder's
circuit size.

## Main definitions

* `agreeing`: the tuples on which `C'` agrees with the direct product of `f`; `mem_agreeing`
  characterizes membership.

## Main results

* `card_filter_card_filter_agree_lt_le`: few tuples have a small class.
* `sum_sum_card_heavy_le`: heavy consistent tuples are rare.
* `sum_card_filter_good_ge`: a `δ / 4` fraction of the pairs `(P, b₀)` satisfy the per-seed
  hypotheses.
* `card_filter_seed_dpDecode_err_le_ge`: a `δ / 8` fraction of seeds `(P, b₀, v)` decode `f` with
  error at most `ε #U`.

## References

* [ImpagliazzoJaiswalKabanetsWigderson2010]
* [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.DirectProduct

open Finset

variable {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V] {k : ℕ}

/-- The tuples on which `C'` agrees with the direct product of `f`. -/
def agreeing (C' : (Fin k → U) → Fin k → V) (f : U → V) : Finset (Fin k → U) :=
  {y | ∀ j, C' y j = f (y j)}

omit [DecidableEq U] in
@[simp]
theorem mem_agreeing {C' : (Fin k → U) → Fin k → V} {f : U → V} {y : Fin k → U} :
    y ∈ agreeing C' f ↔ ∀ j, C' y j = f (y j) := by
  unfold agreeing
  simp

/-- **Small classes are rare**: grouping tuples by their values on `P`, the tuples of a set `G`
whose class meets `G` in fewer than `t` tuples number at most `#U ^ #P * t`. -/
theorem card_filter_card_filter_agree_lt_le (G : Finset (Fin k → U)) (P : Finset (Fin k))
    {t : ℝ} (ht : 0 ≤ t) :
    (#{b ∈ G | (#{y ∈ G | ∀ i ∈ P, y i = b i} : ℝ) < t} : ℝ) ≤ Fintype.card U ^ #P * t := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨d, -⟩
  · simp only [filter_empty, card_empty, Nat.cast_zero]
    positivity
  set ρ : (Fin k → U) → (Fin k → U) := fun b => P.piecewise b d
  have hρ : ∀ b y, ρ y = ρ b ↔ ∀ i ∈ P, y i = b i := by
    intro b y
    constructor
    · intro h i hi
      have := congrFun h i
      simpa [ρ, P.piecewise_eq_of_mem _ _ hi] using this
    · intro h
      funext i
      by_cases hi : i ∈ P
      · simp [ρ, P.piecewise_eq_of_mem _ _ hi, h i hi]
      · simp [ρ, P.piecewise_eq_of_notMem _ _ hi]
  set B := G.filter fun b => (#{y ∈ G | ∀ i ∈ P, y i = b i} : ℝ) < t
  have himage : #(B.image ρ) ≤ Fintype.card U ^ #P := by
    have hinj : Set.InjOn (fun z : Fin k → U => fun i : P => z i)
        (Set.range ρ) := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
      funext i
      by_cases hi : i ∈ P
      · exact congrFun h ⟨i, hi⟩
      · simp [ρ, P.piecewise_eq_of_notMem _ _ hi]
    calc #(B.image ρ) = #((B.image ρ).image fun z : Fin k → U => fun i : P => z i) :=
          (card_image_of_injOn (hinj.mono fun z hz => by
            obtain ⟨b, -, rfl⟩ := mem_image.1 hz; exact ⟨b, rfl⟩)).symm
      _ ≤ Fintype.card (P → U) := card_le_univ _
      _ = Fintype.card U ^ #P := by simp
  have hfib : ∀ z ∈ B.image ρ, (#{b ∈ B | ρ b = z} : ℝ) ≤ t := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hz
    have hbt := (mem_filter.1 hb).2
    refine le_trans ?_ hbt.le
    exact_mod_cast card_le_card fun y hy => by
      simp only [B, mem_filter] at hy ⊢
      exact ⟨hy.1.1, (hρ b y).1 hy.2⟩
  calc (#B : ℝ) = ∑ z ∈ B.image ρ, (#{b ∈ B | ρ b = z} : ℝ) := by
        exact_mod_cast card_eq_sum_card_image ρ B
    _ ≤ ∑ _z ∈ B.image ρ, t := sum_le_sum hfib
    _ = #(B.image ρ) * t := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card U ^ #P * t := by
        gcongr
        exact_mod_cast himage

/-- **Heavy consistent tuples are rare.** Summed over the `s`-subsets `P` and the agreeing seeds
`b₀`, the consistent tuples with at least `α k` disagreements number at most
`#U ^ (k - s) #U ^ k C(k, s) exp (-α s)`. A consistent tuple of an agreeing seed has no
disagreement in `P`, and a random `s`-subset rarely misses `α k` positions
(`card_filter_disjoint_powersetCard_le`). -/
theorem sum_sum_card_heavy_le (C' : (Fin k → U) → Fin k → V) (f : U → V) (s : ℕ) (hk : 0 < k)
    (α : ℝ) :
    ∑ P ∈ univ.powersetCard s, ∑ b₀ ∈ agreeing C' f,
        (#{y ∈ consistent C' P b₀ | α * k ≤ #(disagreements C' f y)} : ℝ) ≤
      Fintype.card U ^ (k - s) * Fintype.card U ^ k * k.choose s * Real.exp (-(α * s)) := by
  classical
  set n := Fintype.card U
  set heavy := ({y : Fin k → U | α * k ≤ #(disagreements C' f y)} : Finset (Fin k → U))
  -- per subset
  have hP : ∀ P ∈ univ.powersetCard s, ∑ b₀ ∈ agreeing C' f,
      (#{y ∈ consistent C' P b₀ | α * k ≤ #(disagreements C' f y)} : ℝ) ≤
        n ^ (k - s) * #{y ∈ heavy | Disjoint (disagreements C' f y) P} := by
    intro P hPs
    have hPc : #Pᶜ = k - s := by
      rw [card_compl, Fintype.card_fin, (mem_powersetCard.1 hPs).2]
    set H' := heavy.filter fun y => Disjoint (disagreements C' f y) P
    have hstep : ∀ b₀ ∈ agreeing C' f,
        #{y ∈ consistent C' P b₀ | α * k ≤ #(disagreements C' f y)} ≤
          #{y ∈ H' | ∀ i ∈ P, b₀ i = y i} := by
      intro b₀ hb₀
      have hagree : ∀ j, C' b₀ j = f (b₀ j) := by simpa using hb₀
      refine card_le_card fun y hy => ?_
      simp only [mem_consistent, H', heavy, mem_filter, mem_univ, true_and] at hy ⊢
      obtain ⟨⟨hyP, hyC⟩, hyH⟩ := hy
      refine ⟨⟨hyH, ?_⟩, fun i hi => (hyP i hi).symm⟩
      rw [disjoint_left]
      intro j hj hjP
      rw [mem_disagreements] at hj
      exact hj (by rw [hyC j hjP, hagree j, hyP j hjP])
    have hcount : ∑ b₀ ∈ agreeing C' f,
        #{y ∈ consistent C' P b₀ | α * k ≤ #(disagreements C' f y)} ≤ n ^ (k - s) * #H' :=
      calc _ ≤ ∑ b₀ ∈ agreeing C' f, #{y ∈ H' | ∀ i ∈ P, b₀ i = y i} := sum_le_sum hstep
        _ ≤ ∑ b₀ : Fin k → U, #{y ∈ H' | ∀ i ∈ P, b₀ i = y i} :=
          sum_le_sum_of_subset (subset_univ _)
        _ = ∑ y ∈ H', #{b₀ : Fin k → U | ∀ i ∈ P, b₀ i = y i} :=
          sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (fun (b₀ y : Fin k → U) => ∀ i ∈ P, b₀ i = y i) (s := univ) (t := H')
        _ = n ^ (k - s) * #H' := by
          have hc : ∀ y ∈ H', #{b₀ : Fin k → U | ∀ i ∈ P, b₀ i = y i} = n ^ (k - s) :=
            fun y _ => by rw [← hPc]; exact Fintype.card_filter_forall_mem_eq P y
          rw [sum_const_nat hc, mul_comm]
    exact_mod_cast hcount
  refine (sum_le_sum hP).trans ?_
  rw [← mul_sum]
  have hmiss : ∑ P ∈ univ.powersetCard s, (#{y ∈ heavy | Disjoint (disagreements C' f y) P} : ℝ)
      ≤ n ^ k * k.choose s * Real.exp (-(α * s)) := by
    calc ∑ P ∈ univ.powersetCard s, (#{y ∈ heavy | Disjoint (disagreements C' f y) P} : ℝ)
        = ∑ y ∈ heavy, (#{P ∈ univ.powersetCard s | Disjoint (disagreements C' f y) P} : ℝ) := by
          simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          exact sum_comm
      _ ≤ ∑ _y ∈ heavy, (k.choose s * Real.exp (-(α * s)) : ℝ) := by
          refine sum_le_sum fun y hy => ?_
          have hD : α * k ≤ #(disagreements C' f y) := (mem_filter.1 hy).2
          have h := card_filter_disjoint_powersetCard_le (subset_univ (disagreements C' f y)) s
          rw [card_powersetCard, card_univ, Fintype.card_fin] at h
          refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
          rw [neg_le_neg_iff, le_div_iff₀ (by exact_mod_cast hk)]
          nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
      _ ≤ ∑ _y : Fin k → U, (k.choose s * Real.exp (-(α * s)) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
      _ = n ^ k * k.choose s * Real.exp (-(α * s)) := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  calc (n : ℝ) ^ (k - s) * ∑ P ∈ univ.powersetCard s,
        (#{y ∈ heavy | Disjoint (disagreements C' f y) P} : ℝ)
      ≤ n ^ (k - s) * (n ^ k * k.choose s * Real.exp (-(α * s))) :=
        mul_le_mul_of_nonneg_left hmiss (by positivity)
    _ = _ := by ring

/-- **Many good seeds.** If `C'` agrees with the direct product of `f` on a `δ` fraction of
tuples and `s ≥ (64 / ε) log (512 / (ε δ ^ 2))`, then, summed over the `s`-subsets `P`, the
agreeing seeds `b₀` that satisfy both hypotheses of `card_filter_dpDecode_err_le_ge` number at
least `δ / 4 C(k, s) #U ^ k`. The constants are ours. -/
theorem sum_card_filter_good_ge (C' : (Fin k → U) → Fin k → V) (f : U → V) {s : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hε1 : ε ≤ 1) (hδ1 : δ ≤ 1)
    (hG : δ * Fintype.card U ^ k ≤ #(agreeing C' f)) (hsk : s ≤ k)
    (hs : 64 / ε * Real.log (512 / (ε * δ ^ 2)) ≤ s) :
    δ / 4 * k.choose s * Fintype.card U ^ k ≤
      ∑ P ∈ univ.powersetCard s, (#{b₀ ∈ agreeing C' f |
        δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        (#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} : ℝ) := by
  classical
  have hεδ : 0 < ε * δ ^ 2 := by positivity
  have hεδ1 : ε * δ ^ 2 ≤ 1 := by
    simpa using mul_le_mul hε1 (pow_le_one₀ hδ.le hδ1) (by positivity) zero_le_one
  have hlog : 0 < Real.log (512 / (ε * δ ^ 2)) :=
    Real.log_pos (by rw [lt_div_iff₀ hεδ]; linarith)
  have hs0 : 0 < s := by
    have : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
    exact_mod_cast this
  have hk : 0 < k := lt_of_lt_of_le hs0 hsk
  rcases isEmpty_or_nonempty U with hU | hU
  · rw [Fintype.card_eq_zero, Nat.cast_zero, zero_pow hk.ne', mul_zero]
    exact sum_nonneg fun _ _ => by positivity
  have hn : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hexp : Real.exp (-(ε / 64 * s)) ≤ ε * δ ^ 2 / 512 := by
    have h1 : Real.log (512 / (ε * δ ^ 2)) ≤ ε / 64 * s := by
      calc Real.log (512 / (ε * δ ^ 2)) = ε / 64 * (64 / ε * Real.log (512 / (ε * δ ^ 2))) := by
            field_simp
        _ ≤ ε / 64 * s := mul_le_mul_of_nonneg_left hs (by positivity)
    calc Real.exp (-(ε / 64 * s)) ≤ Real.exp (-Real.log (512 / (ε * δ ^ 2))) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ε * δ ^ 2 / 512 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  -- each agreeing seed is good, sparse, or dense with a heavy tail
  have hsplit : ∀ P : Finset (Fin k), (#(agreeing C' f) : ℝ) ≤
      #{b₀ ∈ agreeing C' f |
        δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        (#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} +
      #{b₀ ∈ agreeing C' f | ¬δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀)} +
      #{b₀ ∈ agreeing C' f | δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        ¬(#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} := by
    intro P
    have h := (card_le_card (s := agreeing C' f) (t := ((agreeing C' f).filter fun b₀ =>
        δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        (#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)) ∪
      ((agreeing C' f).filter fun b₀ =>
        ¬δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀)) ∪
      ((agreeing C' f).filter fun b₀ => δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        ¬(#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀))) fun b hb => by
      simp only [mem_union, mem_filter]
      tauto).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    exact_mod_cast h
  -- sparse seeds: their class among the agreeing tuples is small
  have hsparse : ∀ P ∈ univ.powersetCard s,
      (#{b₀ ∈ agreeing C' f | ¬δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀)} : ℝ) ≤
        δ / 2 * Fintype.card U ^ k := by
    intro P hPs
    have hPs' : #P = s := (mem_powersetCard.1 hPs).2
    have hPc : #Pᶜ = k - s := by rw [card_compl, Fintype.card_fin, hPs']
    have hA := card_filter_card_filter_agree_lt_le (agreeing C' f) P
      (t := δ / 2 * Fintype.card U ^ #Pᶜ) (by positivity)
    refine le_trans (Nat.cast_le.2 (card_le_card fun b hb => ?_)) (hA.trans_eq ?_)
    · simp only [mem_filter, not_le] at hb ⊢
      refine ⟨hb.1, lt_of_le_of_lt ?_ hb.2⟩
      refine Nat.cast_le.2 (card_le_card fun y hy => ?_)
      simp only [mem_filter] at hy
      have hyG : ∀ j, C' y j = f (y j) := by simpa using hy.1
      have hbG : ∀ j, C' b j = f (b j) := by simpa using hb.1
      rw [mem_consistent]
      exact ⟨hy.2, fun i hi => by rw [hyG, hbG, hy.2 i hi]⟩
    · rw [hPc, hPs', mul_left_comm, ← pow_add, Nat.add_sub_of_le hsk]
  -- dense seeds with a heavy tail: Markov against `sum_sum_card_heavy_le`
  have hheavy : ∀ P ∈ univ.powersetCard s,
      (#{b₀ ∈ agreeing C' f | δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        ¬(#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} : ℝ) * (ε / 64 * (δ / 2 * Fintype.card U ^ (k - s))) ≤
        ∑ b₀ ∈ agreeing C' f,
          (#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) := by
    intro P hPs
    have hPc : #Pᶜ = k - s := by
      rw [card_compl, Fintype.card_fin, (mem_powersetCard.1 hPs).2]
    rw [← nsmul_eq_mul]
    refine (card_nsmul_le_sum _ _ _ fun b hb => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
    simp only [mem_filter, not_le] at hb
    obtain ⟨-, hdense, htail⟩ := hb
    rw [hPc] at hdense
    exact le_trans (mul_le_mul_of_nonneg_left hdense (by positivity)) htail.le
  have hB := sum_sum_card_heavy_le C' f s hk (ε / 64)
  have hc : 0 < ε / 64 * (δ / 2 * (Fintype.card U : ℝ) ^ (k - s)) := by positivity
  have hT : ∑ P ∈ univ.powersetCard s,
      (#{b₀ ∈ agreeing C' f | δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        ¬(#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} : ℝ) ≤ δ / 4 * k.choose s * Fintype.card U ^ k := by
    refine le_of_mul_le_mul_right ?_ hc
    rw [sum_mul]
    refine (sum_le_sum hheavy).trans (hB.trans ?_)
    calc (Fintype.card U : ℝ) ^ (k - s) * Fintype.card U ^ k * k.choose s *
          Real.exp (-(ε / 64 * s))
        ≤ Fintype.card U ^ (k - s) * Fintype.card U ^ k * k.choose s * (ε * δ ^ 2 / 512) := by
          gcongr
      _ = δ / 4 * k.choose s * Fintype.card U ^ k *
          (ε / 64 * (δ / 2 * Fintype.card U ^ (k - s))) := by ring
  have hS : ∑ P ∈ univ.powersetCard s,
      (#{b₀ ∈ agreeing C' f | ¬δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀)} : ℝ) ≤
        k.choose s * (δ / 2 * Fintype.card U ^ k) := by
    refine (sum_le_sum hsparse).trans_eq ?_
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum := sum_le_sum fun P (_ : P ∈ univ.powersetCard s) => hsplit P
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_add_distrib, sum_add_distrib] at hsum
  have hGC := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg (k.choose s) : (0 : ℝ) ≤ _)
  linarith

omit [DecidableEq U] in
/-- **Direct-product decoding** (IJKW, preprint of 2009-10-19, Theorem 1.2; CIKK, Theorem 4.1),
counting form for the tuple formulation. Suppose `C'` agrees with the direct product of `f` on
a `δ` fraction of `k`-tuples, `2 s ≤ k`, `s ≥ (64 / ε) log (512 / (ε δ ^ 2))` and
`m ≥ (16 / δ) log (8 / ε)`. Then at least a `δ / 8` fraction of seeds `(P, b₀, v)`, with `P`
an `s`-subset of positions, `b₀` a tuple and `v` a vector of `m` trials, give a hypothesis
`dpDecode C' dflt P b₀ v` that differs from `f` on at most `ε #U` inputs. The constants are
ours, derived for the tuple formulation; they are not IJKW's. -/
theorem card_filter_seed_dpDecode_err_le_ge (C' : (Fin k → U) → Fin k → V) (f : U → V)
    (dflt : V) {s m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hε1 : ε ≤ 1) (hδ1 : δ ≤ 1)
    (hG : δ * Fintype.card U ^ k ≤ #(agreeing C' f)) (hsk : 2 * s ≤ k)
    (hs : 64 / ε * Real.log (512 / (ε * δ ^ 2)) ≤ s) (hm : 16 / δ * Real.log (8 / ε) ≤ m) :
    δ / 8 * k.choose s * Fintype.card U ^ k * Fintype.card (Trial U k) ^ m ≤
      #((univ.powersetCard s ×ˢ (univ : Finset ((Fin k → U) × (Fin m → Trial U k)))).filter
        fun (P, b₀, v) => (#{x | dpDecode C' dflt P b₀ v x ≠ f x} : ℝ) ≤ ε * Fintype.card U) := by
  classical
  have hsk' : s ≤ k := by omega
  have hgood := sum_card_filter_good_ge C' f hε hδ hε1 hδ1 hG hsk' hs
  have hcount : (#((univ.powersetCard s ×ˢ
        (univ : Finset ((Fin k → U) × (Fin m → Trial U k)))).filter fun (P, b₀, v) =>
          (#{x | dpDecode C' dflt P b₀ v x ≠ f x} : ℝ) ≤ ε * Fintype.card U) : ℝ) =
      ∑ P ∈ univ.powersetCard s, ∑ b₀ : Fin k → U,
        (#{v : Fin m → Trial U k |
          (#{x | dpDecode C' dflt P b₀ v x ≠ f x} : ℝ) ≤ ε * Fintype.card U} : ℝ) := by
    rw [card_filter, ← univ_product_univ, sum_product, Nat.cast_sum]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_product, Nat.cast_sum]
    refine sum_congr rfl fun b₀ _ => ?_
    rw [card_filter, Nat.cast_sum]
  rw [hcount]
  have hlog : Real.log (4 / δ) ≤ Real.log (512 / (ε * δ ^ 2)) := by
    have hεδ : 0 < ε * δ ^ 2 := by positivity
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hδ hεδ]
    nlinarith [mul_le_mul hε1 hδ1 hδ.le zero_le_one]
  calc δ / 8 * k.choose s * Fintype.card U ^ k * Fintype.card (Trial U k) ^ m
      = δ / 4 * k.choose s * Fintype.card U ^ k * ((Fintype.card (Trial U k) : ℝ) ^ m / 2) := by
        ring
    _ ≤ (∑ P ∈ univ.powersetCard s, (#{b₀ ∈ agreeing C' f |
        δ / 2 * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀) ∧
        (#{y ∈ consistent C' P b₀ | ε / 64 * k ≤ #(disagreements C' f y)} : ℝ) ≤
          ε / 64 * #(consistent C' P b₀)} : ℝ)) *
        ((Fintype.card (Trial U k) : ℝ) ^ m / 2) :=
        mul_le_mul_of_nonneg_right hgood (by positivity)
    _ ≤ _ := by
        rw [sum_mul]
        refine sum_le_sum fun P hP => ?_
        have hPc : #Pᶜ = k - s := by
          rw [card_compl, Fintype.card_fin, (mem_powersetCard.1 hP).2]
        rw [← nsmul_eq_mul]
        refine (card_nsmul_le_sum _ _ _ fun b₀ hb₀ => ?_).trans
          (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity)
        obtain ⟨-, hdense, htail⟩ := mem_filter.1 hb₀
        refine card_filter_dpDecode_err_le_ge C' f dflt P b₀ m hε hδ hε1 hδ1 (by omega) ?_ hm
          hdense htail
        rw [hPc]
        calc 64 / ε * Real.log (4 / δ) ≤ 64 / ε * Real.log (512 / (ε * δ ^ 2)) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ ≤ s := hs
          _ ≤ (k - s : ℕ) := by exact_mod_cast (by omega : s ≤ k - s)

end Cslib.Circuits.Boolean.DirectProduct
