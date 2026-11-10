/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Parallel repetition and error reduction for public-coin games

The `m`-fold parallel repetition `Cslib.Complexity.AMGame.repeatShape m g` of a game shape `g`
plays `m` copies of `g` at once. Each move sends the `m` copies' messages concatenated, and
`Cslib.Complexity.AMGame.copyTranscript m i g w` reads the transcript of copy `i` out of a
transcript `w` of the repetition (`Cslib.BitString.listRow`). Since all coins are public, the value
of the repetition on a product of nonnegative payoffs, one for each copy, is the product of the
values (`Cslib.Complexity.AMGame.value_repeatShape_prod`). Merlin may coordinate the copies, but
this does not help him.

The majority of `2 k` copies (`Cslib.Complexity.AMGame.majority`) turns a game of value at least
`2 / 3` into one of value at least `1 - (8 / 9) ^ k`, and a game of value at most `1 / 3` into one
of value at most `(8 / 9) ^ k / 2`. The majority indicator is at most
`2 ^ (-(k + 1)) ∏ᵢ (1 + [copy i accepts])`, and the value of this product factors over the copies.
This gives error reduction for every pattern of moves, as for `AM` itself
(`Cslib.Complexity.mem_AM_iff_forall_errorExponent`) [Babai][Babai1985],
[Babai and Moran][BabaiMoran1988].

## Main definitions

* `Cslib.Complexity.AMGame.copyTranscript`, `Cslib.Complexity.AMGame.repeatShape`.
* `Cslib.Complexity.AMGame.majority`, `Cslib.Complexity.AMGame.amplifiedVerifier`: majority vote
  over parallel copies.
* `Cslib.Complexity.IsAMGameVerifierWithErrorExponent`: error at most `2 ^ (-e(n))`.

## Main results

* `Cslib.Complexity.AMGame.value_repeatShape_prod`: parallel repetition is multiplicative.
* `Cslib.Complexity.AMGame.value_majority_ge`, `Cslib.Complexity.AMGame.value_majority_le`: the
  majority vote amplifies completeness and soundness.
* `Cslib.Complexity.mem_AMGameClass_iff_forall_errorExponent`: **error reduction** for every
  pattern of moves.

## References

* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM AMGame

variable {α : Type}

namespace AMGame

/-- The transcript of copy `i` inside a transcript of the `m`-fold parallel repetition. -/
def copyTranscript (m i : ℕ) : List (AMMove × ℕ) → List Bool → List Bool
  | [], _ => []
  | (_, n) :: g, w => BitString.listRow n i w ++ copyTranscript m i g (w.drop (m * n))

/-- The `m`-fold parallel repetition of a game shape. -/
def repeatShape (m : ℕ) (g : List (AMMove × ℕ)) : List (AMMove × ℕ) :=
  g.map fun x => (x.1, m * x.2)

private theorem sup'_prod_pi {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (φ : ι → κ → ℚ) (hφ : ∀ i y, 0 ≤ φ i y) :
    univ.sup' univ_nonempty (fun z : ι → κ => ∏ i, φ i (z i)) =
      ∏ i, univ.sup' univ_nonempty (φ i) := by
  refine le_antisymm (sup'_le _ _ fun z _ => Finset.prod_le_prod₀ (fun i _ => hφ i _)
    fun i _ => le_sup' (φ i) (mem_univ _)) ?_
  choose z hz using fun i => exists_mem_eq_sup' univ_nonempty (φ i)
  calc ∏ i, univ.sup' univ_nonempty (φ i) = ∏ i, φ i (z i) := prod_congr rfl fun i _ => (hz i).2
    _ ≤ _ := le_sup' (fun z : ι → κ => ∏ i, φ i (z i)) (mem_univ z)

private theorem inf'_prod_pi {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (φ : ι → κ → ℚ) (hφ : ∀ i y, 0 ≤ φ i y) :
    univ.inf' univ_nonempty (fun z : ι → κ => ∏ i, φ i (z i)) =
      ∏ i, univ.inf' univ_nonempty (φ i) := by
  choose z hz using fun i => exists_mem_eq_inf' univ_nonempty (φ i)
  refine le_antisymm ?_ (le_inf' _ _ fun z' _ => Finset.prod_le_prod₀
    (fun i _ => le_inf' _ _ fun y _ => hφ i y) fun i _ => inf'_le (φ i) (mem_univ _))
  calc univ.inf' univ_nonempty (fun z : ι → κ => ∏ i, φ i (z i)) ≤ ∏ i, φ i (z i) :=
        inf'_le (fun z : ι → κ => ∏ i, φ i (z i)) (mem_univ z)
    _ = _ := prod_congr rfl fun i _ => (hz i).2.symm

private theorem sup'_equiv {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β)
    (φ : β → ℚ) : univ.sup' univ_nonempty (fun a => φ (e a)) = univ.sup' univ_nonempty φ :=
  le_antisymm (sup'_le _ _ fun a _ => le_sup' φ (mem_univ _))
    (sup'_le _ _ fun b _ => by
      have := le_sup' (fun a => φ (e a)) (mem_univ (e.symm b))
      rwa [Equiv.apply_symm_apply] at this)

private theorem inf'_equiv {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β)
    (φ : β → ℚ) : univ.inf' univ_nonempty (fun a => φ (e a)) = univ.inf' univ_nonempty φ :=
  le_antisymm (le_inf' _ _ fun b _ => by
      have := inf'_le (fun a => φ (e a)) (mem_univ (e.symm b))
      rwa [Equiv.apply_symm_apply] at this)
    (le_inf' _ _ fun a _ => inf'_le φ (mem_univ _))

/-- Copy `i` of a transcript that starts with a move of `m * n` bits starts with block `i` of
that move. -/
theorem copyTranscript_ofFn_append {m n : ℕ} (i : Fin m) (b : AMMove)
    (g : List (AMMove × ℕ))
    (r : Fin (m * n) → Bool) (t : List Bool) :
    copyTranscript m i ((b, n) :: g) (List.ofFn r ++ t) =
      List.ofFn (BitString.block r i) ++ copyTranscript m i g t := by
  rw [copyTranscript, List.drop_left' List.length_ofFn, BitString.listRow_eq_ofFn,
    BitString.ofList_ofFn_append]

/-- **Parallel repetition of public-coin games is multiplicative.** -/
theorem value_repeatShape_prod (b : Bool) (m : ℕ) (g : List (AMMove × ℕ))
    (f : Fin m → List Bool → ℚ) (hf : ∀ i t, 0 ≤ f i t) :
    value b (repeatShape m g) (fun w => ∏ i, f i (copyTranscript m i g w)) =
      ∏ i, value b g (f i) := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [repeatShape, List.map_cons] at ih ⊢
      rw [value_arthur]
      simp only [copyTranscript_ofFn_append]
      simp only [ih (fun i t => f i _ ) (fun i t => hf i _), value_arthur]
      rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm n m]
      congr 1
      rw [Fintype.prod_sum]
      exact Fintype.sum_equiv BitString.blocksEquiv _ _ fun r => rfl
    · simp only [repeatShape, List.map_cons] at ih ⊢
      have hnn (i : Fin m) (y : Fin n → Bool) :
          0 ≤ value b g fun t => f i (List.ofFn y ++ t) := value_nonneg _ _ fun t => hf i _
      cases b
      · rw [value_merlin_false]
        simp only [copyTranscript_ofFn_append]
        simp only [ih (fun i t => f i _ ) (fun i t => hf i _), value_merlin_false]
        rw [← inf'_prod_pi _ hnn]
        exact inf'_equiv BitString.blocksEquiv
          (fun z => ∏ i, value false g fun t => f i (List.ofFn (z i) ++ t))
      · rw [value_merlin_true]
        simp only [copyTranscript_ofFn_append]
        simp only [ih (fun i t => f i _ ) (fun i t => hf i _), value_merlin_true]
        rw [← sup'_prod_pi _ hnn]
        exact sup'_equiv BitString.blocksEquiv
          (fun z => ∏ i, value true g fun t => f i (List.ofFn (z i) ++ t))

/-- Majority of `2 k` parallel copies of a game: more than `k` copies accept. -/
def majority (g : List (AMMove × ℕ)) (k : ℕ) (W : List Bool → Bool) (w : List Bool) : Bool :=
  decide (k < (List.range (2 * k)).countP fun i => W (copyTranscript (2 * k) i g w))

private theorem prod_one_add_toNat {m : ℕ} (b : Fin m → Bool) :
    ∏ i, (1 + ((b i).toNat : ℚ)) = 2 ^ #{i | b i = true} := by
  have h (i : Fin m) : (1 + ((b i).toNat : ℚ)) = if b i = true then 2 else 1 := by
    cases b i <;> norm_num
  simp only [h]
  rw [prod_ite, prod_const, prod_const_one, mul_one]

private theorem majority_toNat_le (g : List (AMMove × ℕ)) (k : ℕ) (W : List Bool → Bool)
    (w : List Bool) :
    ((majority g k W w).toNat : ℚ) ≤
      1 / 2 ^ (k + 1) * ∏ i : Fin (2 * k), (1 + ((W (copyTranscript (2 * k) i g w)).toNat : ℚ)) +
        0 := by
  rw [prod_one_add_toNat (fun i : Fin (2 * k) => W (copyTranscript (2 * k) i g w)), add_zero]
  unfold majority
  rw [List.countP_range_eq_card_filter]
  by_cases hk : k < #{i : Fin (2 * k) | W (copyTranscript (2 * k) (↑i) g w) = true}
  · rw [decide_eq_true hk, Bool.toNat_true, Nat.cast_one, one_div,
      ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ (by norm_num) hk
  · rw [decide_eq_false hk, Bool.toNat_false, Nat.cast_zero]
    positivity

private theorem not_majority_toNat_le (g : List (AMMove × ℕ)) (k : ℕ) (W : List Bool → Bool)
    (w : List Bool) :
    ((!majority g k W w).toNat : ℚ) ≤
      1 / 2 ^ k * ∏ i : Fin (2 * k), (1 + ((!W (copyTranscript (2 * k) i g w)).toNat : ℚ)) + 0 := by
  rw [prod_one_add_toNat (fun i : Fin (2 * k) => !W (copyTranscript (2 * k) i g w)), add_zero]
  unfold majority
  rw [List.countP_range_eq_card_filter]
  by_cases hk : k < #{i : Fin (2 * k) | W (copyTranscript (2 * k) (↑i) g w) = true}
  · rw [decide_eq_true hk, Bool.not_true, Bool.toNat_false, Nat.cast_zero]
    positivity
  · rw [decide_eq_false hk, Bool.not_false, Bool.toNat_true, Nat.cast_one, one_div,
      ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    refine pow_le_pow_right₀ (by norm_num) ?_
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
      (fun i => W (copyTranscript (2 * k) (↑i) g w) = true)
    simp only [card_univ, Fintype.card_fin, Bool.not_eq_true] at hsum
    have : #{i : Fin (2 * k) | (!W (copyTranscript (2 * k) (↑i) g w)) = true} =
        #{i : Fin (2 * k) | W (copyTranscript (2 * k) (↑i) g w) = false} := by
      simp only [Bool.not_eq_true']
    omega

/-- **Soundness of majority repetition.** -/
theorem value_majority_le (g : List (AMMove × ℕ)) (k : ℕ) (W : List Bool → Bool)
    (h : 3 * value true g (fun t => ((W t).toNat : ℚ)) ≤ 1) :
    value true (repeatShape (2 * k) g) (fun w => ((majority g k W w).toNat : ℚ)) ≤
      (8 / 9) ^ k / 2 := by
  set v := value true g (fun t => ((W t).toNat : ℚ))
  have hv : 0 ≤ v := value_nonneg _ _ fun t => by positivity
  calc _ ≤ _ := value_mono _ _ (majority_toNat_le g k W)
    _ = 1 / 2 ^ (k + 1) * (1 + v) ^ (2 * k) + 0 := by
      rw [value_affine _ _ _ (by positivity), value_repeatShape_prod _ _ _
        (fun _ t => 1 + ((W t).toNat : ℚ)) (fun _ t => by positivity), prod_const, card_univ,
        Fintype.card_fin]
      rw [value_const_add]
    _ ≤ 1 / 2 ^ (k + 1) * (4 / 3) ^ (2 * k) + 0 := by
      gcongr
      linarith
    _ = (8 / 9) ^ k / 2 := by
      rw [pow_mul, pow_succ]
      field_simp
      rw [← mul_pow]
      norm_num

private theorem toNat_not_cast (b : Bool) : (((!b).toNat : ℕ) : ℚ) = 1 - (b.toNat : ℚ) := by
  cases b <;> norm_num

/-- **Completeness of majority repetition.** -/
theorem value_majority_ge (g : List (AMMove × ℕ)) (k : ℕ) (W : List Bool → Bool)
    (h : 2 ≤ 3 * value true g (fun t => ((W t).toNat : ℚ))) :
    1 - (8 / 9) ^ k ≤
      value true (repeatShape (2 * k) g) (fun w => ((majority g k W w).toNat : ℚ)) := by
  have hc (b : Bool) : ((b.toNat : ℕ) : ℚ) = 1 - ((!b).toNat : ℚ) := by cases b <;> norm_num
  simp only [hc (majority _ _ _ _)]
  rw [value_one_sub, Bool.not_true]
  set v := value true g (fun t => ((W t).toNat : ℚ))
  have hdual : value false g (fun t => ((!W t).toNat : ℚ)) = 1 - v := by
    simp only [toNat_not_cast]
    rw [value_one_sub, Bool.not_false]
  have hu : 0 ≤ value false g (fun t => ((!W t).toNat : ℚ)) :=
    value_nonneg _ _ fun t => by positivity
  have key : value false (repeatShape (2 * k) g) (fun w => ((!majority g k W w).toNat : ℚ)) ≤
      (8 / 9) ^ k := by
    calc _ ≤ _ := value_mono _ _ (not_majority_toNat_le g k W)
      _ = 1 / 2 ^ k * (1 + (1 - v)) ^ (2 * k) + 0 := by
        rw [value_affine _ _ _ (by positivity), value_repeatShape_prod _ _ _
          (fun _ t => 1 + ((!W t).toNat : ℚ)) (fun _ t => by positivity), prod_const, card_univ,
          Fintype.card_fin, ← hdual]
        rw [value_const_add]
      _ ≤ 1 / 2 ^ k * (4 / 3) ^ (2 * k) + 0 := by
        gcongr
        · linarith
        · linarith
      _ = (8 / 9) ^ k := by
        rw [pow_mul]
        field_simp
        rw [← mul_pow]
        norm_num
  linarith

theorem computableInPolyTime_copyTranscript {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (AMMove × Polynomial ℕ)) {len m i : γ → ℕ} {w : γ → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => copyTranscript (m x) (i x) (evalShape G (len x)) (w x))
      encIn encBits := by
  induction G generalizing w with
  | nil => exact ComputableInPolyTime.const _
  | cons x G ih =>
    have hn : ComputableInPolyTime (fun c => x.2.eval (len c)) encIn encUnary :=
      (ComputableInPolyTime.unary_eval x.2).comp hlen
    exact ComputableInPolyTime.bitsAppend (.bitsRowWithInput hn hi hw)
      (ih (.bitsDropWithInput hw (ComputableInPolyTime.unary_mul.comp (hm.prod hn))))

theorem computableInPolyTime_majority {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (AMMove × Polynomial ℕ)) {len k : γ → ℕ} {W : γ → List Bool → Bool}
    {w : γ → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary) (hk : ComputableInPolyTime k encIn encUnary)
    (hW : ComputableInPolyTime (fun p : γ × List Bool => W p.1 p.2) (encPair encIn encBits)
      encBool)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => majority (evalShape G (len x)) (k x) (W x) (w x))
      encIn encBool := by
  unfold majority
  have h2k : ComputableInPolyTime (fun x => 2 * k x) encIn encUnary :=
    ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hk)
  have hrow : ComputableInPolyTime (fun p : γ × ℕ =>
      W p.1 (copyTranscript (2 * k p.1) p.2 (evalShape G (len p.1)) (w p.1)))
      (encPair encIn encUnary) encBool :=
    hW.comp ((ComputableInPolyTime.fst _ _).prod (computableInPolyTime_copyTranscript G
      (hlen.comp (.fst _ _)) (h2k.comp (.fst _ _)) (.snd _ _) (hw.comp (.fst _ _))))
  exact ComputableInPolyTime.unary_lt' hk (ComputableInPolyTime.countPWithInput
    (ComputableInPolyTime.range.comp h2k) hrow)

/-- Parallel repetition of a polynomial game shape, `M(n)` copies. -/
noncomputable def repeatShapePoly (M : Polynomial ℕ) (G : List (AMMove × Polynomial ℕ)) :
    List (AMMove × Polynomial ℕ) :=
  G.map fun x => (x.1, M * x.2)

theorem evalShape_repeatShapePoly (M : Polynomial ℕ) (G : List (AMMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (repeatShapePoly M G) n = repeatShape (M.eval n) (evalShape G n) := by
  simp [evalShape, repeatShapePoly, repeatShape]

theorem map_fst_repeatShapePoly (M : Polynomial ℕ) (G : List (AMMove × Polynomial ℕ)) :
    (repeatShapePoly M G).map Prod.fst = G.map Prod.fst := by
  simp [repeatShapePoly]

/-- The majority of `2 k` parallel runs of a game verifier. -/
def amplifiedVerifier (enc : α ↪ List Bool) (G : List (AMMove × Polynomial ℕ))
    (k : Polynomial ℕ) (V : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  majority (evalShape G (enc x.1).length) (k.eval (enc x.1).length) (fun t => V (x.1, t)) x.2

theorem computableInPolyTime_amplifiedVerifier {enc : α ↪ List Bool}
    (G : List (AMMove × Polynomial ℕ)) (k : Polynomial ℕ) {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (amplifiedVerifier enc G k V) (encPair enc encBits) encBool :=
  computableInPolyTime_majority G
    ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _))
    ((ComputableInPolyTime.unary_eval k).comp
      ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _)))
    (hV.comp (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod (.snd _ _))) (.snd _ _)

theorem eight_ninths_pow_le (e : ℕ) : (8 / 9 : ℚ) ^ (6 * e) ≤ (1 / 2) ^ e := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) e

end AMGame

/-- A game verifier with error at most `2 ^ (-e(n))`: on a member Merlin's optimal acceptance
probability is at least `1 - 2 ^ (-e(n))`, on a non-member at most `2 ^ (-e(n))`. -/
def IsAMGameVerifierWithErrorExponent (enc : α ↪ List Bool) (e : Polynomial ℕ)
    (G : List (AMMove × Polynomial ℕ)) (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ e.eval (enc a).length * (2 ^ arthurBits (evalShape G (enc a).length) -
      count (evalShape G (enc a).length) fun t => V (a, t)) ≤
      2 ^ arthurBits (evalShape G (enc a).length)) ∧
    (a ∉ A → 2 ^ e.eval (enc a).length * count (evalShape G (enc a).length)
      (fun t => V (a, t)) ≤ 2 ^ arthurBits (evalShape G (enc a).length))

theorem isAMGameVerifierWithErrorExponent_iff_value {enc : α ↪ List Bool} {e : Polynomial ℕ}
    {G : List (AMMove × Polynomial ℕ)} {V : α × List Bool → Bool} {A : Set α} :
    IsAMGameVerifierWithErrorExponent enc e G V A ↔ ∀ a,
      (a ∈ A → 2 ^ e.eval (enc a).length * (1 - value true (evalShape G (enc a).length)
        (fun t => ((V (a, t)).toNat : ℚ))) ≤ 1) ∧
      (a ∉ A → 2 ^ e.eval (enc a).length * value true (evalShape G (enc a).length)
        (fun t => ((V (a, t)).toNat : ℚ)) ≤ 1) := by
  refine forall_congr' fun a => and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_)
  · have hle := count_le_two_pow (evalShape G (enc a).length) fun t => V (a, t)
    rw [← Nat.cast_le (α := ℚ)]
    push_cast [hle]
    rw [count_eq]
    have hp : (0 : ℚ) < 2 ^ arthurBits (evalShape G (enc a).length) := by positivity
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [← Nat.cast_le (α := ℚ)]
    push_cast
    rw [count_eq]
    have hp : (0 : ℚ) < 2 ^ arthurBits (evalShape G (enc a).length) := by positivity
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

theorem IsAMGameVerifierWithErrorExponent.isAMGameVerifier {enc : α ↪ List Bool}
    {e : Polynomial ℕ} {G : List (AMMove × Polynomial ℕ)} {V : α × List Bool → Bool} {A : Set α}
    (h : IsAMGameVerifierWithErrorExponent enc e G V A) (he : ∀ n, 2 ≤ e.eval n) :
    IsAMGameVerifier enc G V A := by
  rw [isAMGameVerifierWithErrorExponent_iff_value] at h
  rw [isAMGameVerifier_iff_value]
  intro a
  have h4 : (4 : ℚ) ≤ 2 ^ e.eval (enc a).length := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (he (enc a).length)
    norm_num at this ⊢
    exact this
  have hv0 : 0 ≤ value true (evalShape G (enc a).length) (fun t => ((V (a, t)).toNat : ℚ)) :=
    value_nonneg _ _ fun t => by positivity
  have hv1 : value true (evalShape G (enc a).length) (fun t => ((V (a, t)).toNat : ℚ)) ≤ 1 :=
    value_le_one _ _ fun t => by cases V (a, t) <;> norm_num
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have := (h a).1 ha; nlinarith
  · have := (h a).2 ha; nlinarith

/-- **Error reduction for public-coin games**: parallel repetition with a majority vote. A problem
has a game verifier of pattern `π` exactly when it has one with error at most `2 ^ (-e(n))` for
every polynomial `e`. -/
theorem mem_AMGameClass_iff_forall_errorExponent {enc : α ↪ List Bool} {π : List AMMove}
    {A : Set α} :
    A ∈ AMGameClass enc π ↔ ∀ e : Polynomial ℕ, ∃ (G : List (AMMove × Polynomial ℕ))
      (V : α × List Bool → Bool), G.map Prod.fst = π ∧
        ComputableInPolyTime V (encPair enc encBits) encBool ∧
          IsAMGameVerifierWithErrorExponent enc e G V A := by
  constructor
  · rintro ⟨G, V, hG, hV, hA⟩ e
    refine ⟨repeatShapePoly (2 * (6 * e)) G, amplifiedVerifier enc G (6 * e) V,
      by rw [map_fst_repeatShapePoly, hG], computableInPolyTime_amplifiedVerifier _ _ hV, ?_⟩
    rw [isAMGameVerifier_iff_value] at hA
    rw [isAMGameVerifierWithErrorExponent_iff_value]
    intro a
    have hk : (6 * e).eval (enc a).length = 6 * e.eval (enc a).length := by
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    have hs : evalShape (repeatShapePoly (2 * (6 * e)) G) (enc a).length =
        repeatShape (2 * (6 * e).eval (enc a).length) (evalShape G (enc a).length) := by
      simp only [evalShape_repeatShapePoly, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [hs]
    simp only [amplifiedVerifier]
    rw [hk]
    have hpow := eight_ninths_pow_le (e.eval (enc a).length)
    have h2 : (2 : ℚ) ^ e.eval (enc a).length * (1 / 2) ^ e.eval (enc a).length = 1 := by
      rw [← mul_pow]; norm_num
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · have := value_majority_ge _ (6 * e.eval (enc a).length) (fun t => V (a, t)) ((hA a).1 ha)
      calc _ ≤ (2 : ℚ) ^ e.eval (enc a).length * (1 / 2) ^ e.eval (enc a).length := by
            gcongr; linarith
        _ = 1 := h2
    · have := value_majority_le _ (6 * e.eval (enc a).length) (fun t => V (a, t)) ((hA a).2 ha)
      have hp0 : (0 : ℚ) ≤ (8 / 9) ^ (6 * e.eval (enc a).length) := by positivity
      calc _ ≤ (2 : ℚ) ^ e.eval (enc a).length * (1 / 2) ^ e.eval (enc a).length := by
            gcongr; linarith
        _ = 1 := h2
  · intro h
    obtain ⟨G, V, hG, hV, hA⟩ := h 2
    exact ⟨G, V, hG, hV, hA.isAMGameVerifier fun n => by simp⟩

end Cslib.Complexity
