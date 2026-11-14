/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.Repetition

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The round collapse `AM[k] = AM`

The collapse of Babai and Moran [Babai][Babai1985], [Babai and Moran][BabaiMoran1988],
[Arora and Barak, Section 8.2][AroraBarak09]. Every public-coin Arthur–Merlin game with a fixed
pattern of moves is in `AM`, and a pattern that has an Arthur move somewhere before a Merlin move
gives exactly `AM`.

The core step is the swap `Cslib.Complexity.AMGameClass_swap`: a Merlin message followed by Arthur's
coins can be replaced by the coins followed by the message. Write the game as
`σ, M (q bits), A (p bits), τ`.

1. Amplify the game by a majority of `48` parallel copies
   (`Cslib.Complexity.AMGame.amplifiedVerifier`). Its value is then at least `15 / 16` on members
   and at most `1 / 32` on non-members, and Merlin's message has `Q = 48 q` bits.
2. Arthur sends the coins of the `A` move for `2 k` independent copies of the rest of the game,
   with `k = 6 (Q + 4)`. Merlin then sends one message of `Q` bits, common to all copies, and the
   copies of `τ` run in parallel. The verifier takes the majority vote
   (`Cslib.Complexity.AMGame.swapVerifier`).
3. On a member, Merlin sends the best message of the amplified game, and the majority vote keeps
   its value up to `(8 / 9) ^ k`. On a non-member, each fixed message fails the majority except
   with probability `(8 / 9) ^ k / 2`. A union bound over the `2 ^ Q` messages gives
   `2 ^ Q (8 / 9) ^ k / 2 ≤ 1 / 32` (`Cslib.Complexity.AMGame.value_swap_le`,
   `Cslib.Complexity.AMGame.value_swap_ge`).

With merging of consecutive moves of the same player (`Cslib.Complexity.AMGameClass_merge`) and
padding (`Cslib.Complexity.AMGameClass_insert`), any pattern after a leading `A M` reduces to `A M`
one move at a time. A leading `A M` can always be inserted.

## Main results

* `Cslib.Complexity.AMGameClass_swap`: **the swap** `σ M A τ ⊆ σ A M τ`.
* `Cslib.Complexity.AMGameClass_subset_AM`: every fixed pattern gives a subclass of `AM`.
* `Cslib.Complexity.AMGameClass_eq_AM`: a pattern with `A M` as a sublist gives exactly `AM`.
* `Cslib.Complexity.AMk_eq_AM`: **`AM[k] = AM`** for every constant `k ≥ 2`.
* `Cslib.Complexity.MAk_eq_AM`: `MA[k] = AM` for every constant `k ≥ 3`.
* `Cslib.Complexity.AMGameClass_merlin_arthur_merlin`: `MAM = AM` [Babai][Babai1985].

The speedup `AM[2 t(n)] = AM[t(n)]` for polynomially many rounds of [Babai and
Moran][BabaiMoran1988] needs patterns that depend on the input length and is not proved here. Nor
is the simulation of private coins by public coins.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM AMGame

variable {α : Type}

namespace AMGame

private theorem sup'_le_sum {ι : Type} [Fintype ι] [Nonempty ι] (φ : ι → ℚ) (h : ∀ i, 0 ≤ φ i) :
    univ.sup' univ_nonempty φ ≤ ∑ i, φ i :=
  sup'_le _ _ fun i _ => single_le_sum (fun j _ => h j) (mem_univ i)

/-- The verifier of the swapped game. The transcript is `s` (`L` bits), then Arthur's coins `R`
for `2 k` copies of the rest of the game (`P` bits), then Merlin's message `y` (`q` bits), then
the `2 k` copies of the rest of the game. It accepts when more than `k` copies accept on
`s ++ y ++ (copy i)`. -/
def swapVerifier (L P q : ℕ) (g' : List (AMMove × ℕ)) (k : ℕ) (V : List Bool → Bool)
    (w : List Bool) : Bool :=
  majority g' k (fun u => V (w.take L ++ ((w.drop (L + P)).take q ++ u)))
    ((w.drop L).take P ++ w.drop (L + P + q))

private theorem swapVerifier_apply {L P q : ℕ} (g' : List (AMMove × ℕ)) (k : ℕ)
    (V : List Bool → Bool)
    {s : List Bool} (hs : s.length = L) (R : Fin P → Bool) (y : Fin q → Bool) (t : List Bool) :
    swapVerifier L P q g' k V (s ++ (List.ofFn R ++ (List.ofFn y ++ t))) =
      majority g' k (fun u => V (s ++ (List.ofFn y ++ u))) (List.ofFn R ++ t) := by
  have h1 : s ++ (List.ofFn R ++ (List.ofFn y ++ t)) = (s ++ List.ofFn R) ++ (List.ofFn y ++ t) :=
    by simp
  have h2 : s ++ (List.ofFn R ++ (List.ofFn y ++ t)) = (s ++ List.ofFn R ++ List.ofFn y) ++ t :=
    by simp
  have e1 : (s ++ (List.ofFn R ++ (List.ofFn y ++ t))).take L = s := List.take_left' hs
  have e2 : ((s ++ (List.ofFn R ++ (List.ofFn y ++ t))).drop (L + P)).take q = List.ofFn y := by
    rw [h1, List.drop_left' (by simp [hs]), List.take_left' List.length_ofFn]
  have e3 : ((s ++ (List.ofFn R ++ (List.ofFn y ++ t))).drop L).take P = List.ofFn R := by
    rw [List.drop_left' hs, List.take_left' List.length_ofFn]
  have e4 : (s ++ (List.ofFn R ++ (List.ofFn y ++ t))).drop (L + P + q) = t := by
    rw [h2, List.drop_left' (by simp [hs]; omega)]
  rw [swapVerifier, e1, e2, e3, e4]

private theorem value_repeatShape_cons_arthur (b : Bool) (k p : ℕ) (τ : List (AMMove × ℕ))
    (f : List Bool → ℚ) :
    value b (repeatShape k ((.arthur, p) :: τ)) f =
      (∑ R : Fin (k * p) → Bool, value b (repeatShape k τ) fun t => f (List.ofFn R ++ t)) /
        2 ^ (k * p) := rfl

/-- The pointwise upper bound behind the swap: the union bound over Merlin's message. -/
private theorem swap_pointwise_le (τ : List (AMMove × ℕ)) (q p k : ℕ)
    (W : (Fin q → Bool) → List Bool → Bool) :
    (∑ R : Fin (2 * k * p) → Bool, univ.sup' univ_nonempty fun y : Fin q → Bool =>
        value true (repeatShape (2 * k) τ) fun t =>
          ((majority ((.arthur, p) :: τ) k (W y) (List.ofFn R ++ t)).toNat : ℚ)) /
        2 ^ (2 * k * p) ≤
      3 * univ.sup' univ_nonempty (fun y : Fin q → Bool =>
          value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ)) +
        2 ^ q * ((8 / 9) ^ k / 2) := by
  set H : (Fin (2 * k * p) → Bool) → (Fin q → Bool) → ℚ := fun R y =>
    value true (repeatShape (2 * k) τ) fun t =>
      ((majority ((.arthur, p) :: τ) k (W y) (List.ofFn R ++ t)).toNat : ℚ) with hH
  have hH0 (R y) : 0 ≤ H R y := value_nonneg _ _ fun t => by positivity
  have hH1 (R y) : H R y ≤ 1 := value_le_one _ _ fun t => by
    cases majority ((.arthur, p) :: τ) k (W y) (List.ofFn R ++ t) <;> norm_num
  have hP : (0 : ℚ) < 2 ^ (2 * k * p) := by positivity
  set m := univ.sup' univ_nonempty (fun y : Fin q → Bool =>
    value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ)) with hm
  have hm0 : 0 ≤ m := (value_nonneg _ _ fun t => by positivity).trans
    (le_sup' (fun y : Fin q → Bool => value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ))
      (mem_univ fun _ => false))
  have hε : (0 : ℚ) ≤ 2 ^ q * ((8 / 9) ^ k / 2) := by positivity
  by_cases hc : 1 ≤ 3 * m
  · have : (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p) ≤ 1 := by
      rw [div_le_one hP]
      calc _ ≤ ∑ _R : Fin (2 * k * p) → Bool, (1 : ℚ) :=
            sum_le_sum fun R _ => sup'_le _ _ fun y _ => hH1 R y
        _ = _ := by simp
    exact this.trans (by linarith)
  · push Not at hc
    have hF (y : Fin q → Bool) : (∑ R, H R y) / 2 ^ (2 * k * p) ≤ (8 / 9) ^ k / 2 := by
      have := value_majority_le ((.arthur, p) :: τ) k (W y) (by
        have := le_sup' (fun y : Fin q → Bool =>
          value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ)) (mem_univ y)
        linarith)
      rwa [value_repeatShape_cons_arthur] at this
    calc (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p)
        ≤ (∑ R, ∑ y, H R y) / 2 ^ (2 * k * p) := by
          gcongr with R
          exact sup'_le_sum _ (hH0 R)
      _ = ∑ y, (∑ R, H R y) / 2 ^ (2 * k * p) := by
          rw [sum_comm]; simp only [div_eq_mul_inv, sum_mul]
      _ ≤ ∑ _y : Fin q → Bool, (8 / 9 : ℚ) ^ k / 2 := sum_le_sum fun y _ => hF y
      _ = 2 ^ q * ((8 / 9) ^ k / 2) := by simp
      _ ≤ _ := by linarith

/-- The pointwise lower bound behind the swap: Merlin keeps his best message. -/
private theorem swap_pointwise_ge (τ : List (AMMove × ℕ)) (q p k : ℕ)
    (W : (Fin q → Bool) → List Bool → Bool) :
    3 * univ.sup' univ_nonempty (fun y : Fin q → Bool =>
          value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ)) + (-2 - (8 / 9) ^ k) ≤
      (∑ R : Fin (2 * k * p) → Bool, univ.sup' univ_nonempty fun y : Fin q → Bool =>
        value true (repeatShape (2 * k) τ) fun t =>
          ((majority ((.arthur, p) :: τ) k (W y) (List.ofFn R ++ t)).toNat : ℚ)) /
        2 ^ (2 * k * p) := by
  set H : (Fin (2 * k * p) → Bool) → (Fin q → Bool) → ℚ := fun R y =>
    value true (repeatShape (2 * k) τ) fun t =>
      ((majority ((.arthur, p) :: τ) k (W y) (List.ofFn R ++ t)).toNat : ℚ) with hH
  have hH0 (R y) : 0 ≤ H R y := value_nonneg _ _ fun t => by positivity
  have hP : (0 : ℚ) < 2 ^ (2 * k * p) := by positivity
  have hrhs : 0 ≤ (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p) :=
    div_nonneg (sum_nonneg fun R _ => (hH0 R fun _ => false).trans
      (le_sup' (H R) (mem_univ _))) hP.le
  obtain ⟨y₀, _, hy₀⟩ := exists_mem_eq_sup' univ_nonempty (fun y : Fin q → Bool =>
    value true ((.arthur, p) :: τ) fun u => ((W y u).toNat : ℚ))
  rw [hy₀]
  have hv1 : value true ((.arthur, p) :: τ) (fun u => ((W y₀ u).toNat : ℚ)) ≤ 1 :=
    value_le_one _ _ fun t => by cases W y₀ t <;> norm_num
  have hpow : (0 : ℚ) ≤ (8 / 9) ^ k := by positivity
  by_cases hc : 2 ≤ 3 * value true ((.arthur, p) :: τ) (fun u => ((W y₀ u).toNat : ℚ))
  · have hF := value_majority_ge ((.arthur, p) :: τ) k (W y₀) hc
    rw [value_repeatShape_cons_arthur] at hF
    have hF' : 1 - (8 / 9) ^ k ≤ (∑ R, H R y₀) / 2 ^ (2 * k * p) := hF
    have : (∑ R, H R y₀) / 2 ^ (2 * k * p) ≤
        (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p) := by
      gcongr with R
      exact le_sup' (H R) (mem_univ y₀)
    linarith
  · push Not at hc
    linarith

/-- **The swap, upper bound.** -/
theorem value_swap_le (σ τ : List (AMMove × ℕ)) (q p k : ℕ) (V : List Bool → Bool) :
    value true (σ ++ (.arthur, 2 * k * p) :: (.merlin, q) :: repeatShape (2 * k) τ)
        (fun w =>
          ((swapVerifier (transcriptLength σ) (2 * k * p) q ((.arthur, p) :: τ) k V w).toNat : ℚ))
      ≤ 3 * value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ) (fun w => ((V w).toNat : ℚ)) +
        2 ^ q * ((8 / 9) ^ k / 2) := by
  rw [value_append, value_append, ← value_affine _ _ _ (by norm_num : (0 : ℚ) ≤ 3)]
  refine value_mono_of_length _ _ fun s hs => ?_
  rw [value_arthur, value_merlin_true]
  simp only [value_merlin_true, swapVerifier_apply _ _ _ hs]
  exact swap_pointwise_le τ q p k (fun y u => V (s ++ (List.ofFn y ++ u)))

/-- **The swap, lower bound.** -/
theorem value_swap_ge (σ τ : List (AMMove × ℕ)) (q p k : ℕ) (V : List Bool → Bool) :
    3 * value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ) (fun w => ((V w).toNat : ℚ)) +
        (-2 - (8 / 9) ^ k) ≤
      value true (σ ++ (.arthur, 2 * k * p) :: (.merlin, q) :: repeatShape (2 * k) τ)
        (fun w =>
          ((swapVerifier (transcriptLength σ) (2 * k * p) q ((.arthur, p) :: τ) k V w).toNat :
            ℚ)) := by
  rw [value_append, value_append, ← value_affine _ _ _ (by norm_num : (0 : ℚ) ≤ 3)]
  refine value_mono_of_length _ _ fun s hs => ?_
  rw [value_arthur, value_merlin_true]
  simp only [value_merlin_true, swapVerifier_apply _ _ _ hs]
  exact swap_pointwise_ge τ q p k (fun y u => V (s ++ (List.ofFn y ++ u)))

private theorem two_pow_mul_eight_ninths_le (q : ℕ) :
    (2 : ℚ) ^ q * ((8 / 9) ^ (6 * (q + 4)) / 2) ≤ 1 / 32 := by
  have h1 := eight_ninths_pow_le (q + 4)
  have h2 : (2 : ℚ) ^ q * (1 / 2) ^ (q + 4) = 1 / 16 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc (2 : ℚ) ^ q * ((8 / 9) ^ (6 * (q + 4)) / 2) ≤ 2 ^ q * ((1 / 2) ^ (q + 4) / 2) := by
        gcongr
    _ = 1 / 32 := by
      rw [← mul_div_assoc, h2]
      norm_num

/-- The numerical heart of the swap: amplify with `48` copies, then swap with `2 k` copies. -/
private theorem swap_game_bounds (σ τ : List (AMMove × ℕ)) (q p k : ℕ)
    (hk : k = 6 * (2 * 24 * q + 4))
    (V : List Bool → Bool) (P : Prop)
    (h₁ : P → 2 ≤ 3 * value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ)
      (fun t => ((V t).toNat : ℚ)))
    (h₂ : ¬ P → 3 * value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ)
      (fun t => ((V t).toNat : ℚ)) ≤ 1) :
    (P → 2 ≤ 3 * value true (repeatShape (2 * 24) σ ++ (.arthur, 2 * k * (2 * 24 * p)) ::
        (.merlin, 2 * 24 * q) :: repeatShape (2 * k) (repeatShape (2 * 24) τ))
      (fun w => ((swapVerifier (transcriptLength (repeatShape (2 * 24) σ)) (2 * k * (2 * 24 * p))
        (2 * 24 * q) ((.arthur, 2 * 24 * p) :: repeatShape (2 * 24) τ) k
        (majority (σ ++ (.merlin, q) :: (.arthur, p) :: τ) 24 V) w).toNat : ℚ))) ∧
    (¬ P → 3 * value true (repeatShape (2 * 24) σ ++ (.arthur, 2 * k * (2 * 24 * p)) ::
        (.merlin, 2 * 24 * q) :: repeatShape (2 * k) (repeatShape (2 * 24) τ))
      (fun w => ((swapVerifier (transcriptLength (repeatShape (2 * 24) σ)) (2 * k * (2 * 24 * p))
        (2 * 24 * q) ((.arthur, 2 * 24 * p) :: repeatShape (2 * 24) τ) k
        (majority (σ ++ (.merlin, q) :: (.arthur, p) :: τ) 24 V) w).toNat : ℚ)) ≤ 1) := by
  have hrep : repeatShape (2 * 24) σ ++ (.merlin, 2 * 24 * q) :: (.arthur, 2 * 24 * p) ::
      repeatShape (2 * 24) τ = repeatShape (2 * 24) (σ ++ (.merlin, q) :: (.arthur, p) :: τ) := by
    simp [repeatShape]
  have hle := value_swap_le (repeatShape (2 * 24) σ) (repeatShape (2 * 24) τ) (2 * 24 * q)
    (2 * 24 * p) k
    (majority (σ ++ (.merlin, q) :: (.arthur, p) :: τ) 24 V)
  have hge := value_swap_ge (repeatShape (2 * 24) σ) (repeatShape (2 * 24) τ) (2 * 24 * q)
    (2 * 24 * p) k
    (majority (σ ++ (.merlin, q) :: (.arthur, p) :: τ) 24 V)
  rw [hrep] at hle hge
  have hε : (2 : ℚ) ^ (2 * 24 * q) * ((8 / 9) ^ k / 2) ≤ 1 / 32 := by
    rw [hk]; exact two_pow_mul_eight_ninths_le _
  have hε0 : (0 : ℚ) ≤ (8 / 9) ^ k := by positivity
  have hε1 : (8 / 9 : ℚ) ^ k ≤ 1 / 16 := by
    rw [hk]
    calc _ ≤ (1 / 2 : ℚ) ^ (2 * 24 * q + 4) := eight_ninths_pow_le _
      _ ≤ (1 / 2) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have h24 : (8 / 9 : ℚ) ^ 24 ≤ 1 / 16 := by norm_num
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · have := value_majority_ge _ 24 V (h₁ hP)
    linarith
  · have := value_majority_le _ 24 V (h₂ hP)
    linarith

end AMGame

/-- **Swapping Merlin's message past Arthur's coins** (the Babai–Moran swap). -/
theorem AMGameClass_swap {enc : α ↪ List Bool} (σ τ : List AMMove) :
    AMGameClass enc (σ ++ .merlin :: .arthur :: τ) ⊆
      AMGameClass enc (σ ++ .arthur :: .merlin :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  obtain ⟨Gσ, G', rfl, hσ, h'⟩ := List.map_eq_append_iff.1 hG
  obtain ⟨⟨x₁, qM⟩, G'', rfl, hx₁, h''⟩ := List.map_eq_cons_iff.1 h'
  obtain ⟨⟨x₂, pA⟩, Gτ, rfl, hx₂, hτ⟩ := List.map_eq_cons_iff.1 h''
  dsimp only at hx₁ hx₂
  subst hx₁ hx₂
  rw [isAMGameVerifier_iff_value] at hA
  set M₀ : Polynomial ℕ := Polynomial.C 48 with hM₀def
  set V₁ := amplifiedVerifier enc (Gσ ++ (.merlin, qM) :: (.arthur, pA) :: Gτ) 24 V with hV₁def
  set K : Polynomial ℕ := 6 * (M₀ * qM + 4) with hKdef
  set V₃ : α × List Bool → Bool := fun x =>
    swapVerifier ((transcriptLengthPoly (repeatShapePoly M₀ Gσ)).eval (enc x.1).length)
      ((2 * K * (M₀ * pA)).eval (enc x.1).length) ((M₀ * qM).eval (enc x.1).length)
      (evalShape ((.arthur, M₀ * pA) :: repeatShapePoly M₀ Gτ) (enc x.1).length)
      (K.eval (enc x.1).length) (fun t => V₁ (x.1, t)) x.2 with hV₃def
  refine ⟨repeatShapePoly M₀ Gσ ++ (.arthur, 2 * K * (M₀ * pA)) :: (.merlin, M₀ * qM) ::
    repeatShapePoly (2 * K) (repeatShapePoly M₀ Gτ), V₃, ?_, ?_, ?_⟩
  · simp [map_fst_repeatShapePoly, hσ, hτ]
  · have hlen : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
    have hev (P : Polynomial ℕ) : ComputableInPolyTime
        (fun x : α × List Bool => P.eval (enc x.1).length) (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval P).comp hlen
    have hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool :=
      computableInPolyTime_amplifiedVerifier _ _ hV
    have hx2 : ComputableInPolyTime (fun x : α × List Bool => x.2) (encPair enc encBits)
        encBits := .snd _ _
    have hL := hev (transcriptLengthPoly (repeatShapePoly M₀ Gσ))
    have hP := hev (2 * K * (M₀ * pA))
    have hq := hev (M₀ * qM)
    have hLP := ComputableInPolyTime.unary_add' hL hP
    have hLPq := ComputableInPolyTime.unary_add' hLP hq
    have hW : ComputableInPolyTime (fun p : (α × List Bool) × List Bool =>
        V₁ (p.1.1,
          p.1.2.take ((transcriptLengthPoly (repeatShapePoly M₀ Gσ)).eval (enc p.1.1).length) ++
          ((p.1.2.drop ((transcriptLengthPoly (repeatShapePoly M₀ Gσ)).eval (enc p.1.1).length +
              (2 * K * (M₀ * pA)).eval (enc p.1.1).length)).take
            ((M₀ * qM).eval (enc p.1.1).length) ++ p.2)))
        (encPair (encPair enc encBits) encBits) encBool := by
      have hf : ComputableInPolyTime (fun p : (α × List Bool) × List Bool => p.1)
          (encPair (encPair enc encBits) encBits) (encPair enc encBits) := .fst _ _
      refine hV₁.comp (((ComputableInPolyTime.fst _ _).comp hf).prod ?_)
      exact .bitsAppend (.bitsTakeWithInput (hx2.comp hf) (hL.comp hf))
        (.bitsAppend (.bitsTakeWithInput (.bitsDropWithInput (hx2.comp hf) (hLP.comp hf))
          (hq.comp hf)) (.snd _ _))
    exact computableInPolyTime_majority ((.arthur, M₀ * pA) :: repeatShapePoly M₀ Gτ) hlen
      (hev K) hW (.bitsAppend (.bitsTakeWithInput (.bitsDropWithInput hx2 hL) hP)
        (.bitsDropWithInput hx2 hLPq))
  · rw [isAMGameVerifier_iff_value]
    intro a
    have hM : M₀.eval (enc a).length = 48 := Polynomial.eval_C
    have hK : K.eval (enc a).length = 6 * (2 * 24 * qM.eval (enc a).length + 4) := by
      simp only [hKdef, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, hM]
    have h3 : evalShape (repeatShapePoly M₀ Gσ ++ (.arthur, 2 * K * (M₀ * pA)) ::
        (.merlin, M₀ * qM) ::
        repeatShapePoly (2 * K) (repeatShapePoly M₀ Gτ)) (enc a).length =
        repeatShape (2 * 24) (evalShape Gσ (enc a).length) ++
          (.arthur, 2 * K.eval (enc a).length * (2 * 24 * pA.eval (enc a).length)) ::
          (.merlin, 2 * 24 * qM.eval (enc a).length) ::
          repeatShape (2 * K.eval (enc a).length)
            (repeatShape (2 * 24) (evalShape Gτ (enc a).length)) := by
      simp only [evalShape_append, evalShape_cons, evalShape_repeatShapePoly, Polynomial.eval_mul,
        Polynomial.eval_ofNat, hM]
    have hV₃ (t : List Bool) : V₃ (a, t) =
        swapVerifier (transcriptLength (repeatShape (2 * 24) (evalShape Gσ (enc a).length)))
          (2 * K.eval (enc a).length * (2 * 24 * pA.eval (enc a).length))
          (2 * 24 * qM.eval (enc a).length)
          ((.arthur, 2 * 24 * pA.eval (enc a).length) ::
            repeatShape (2 * 24) (evalShape Gτ (enc a).length)) (K.eval (enc a).length)
          (majority (evalShape Gσ (enc a).length ++ (.merlin, qM.eval (enc a).length) ::
            (.arthur, pA.eval (enc a).length) :: evalShape Gτ (enc a).length) 24
            fun t => V (a, t)) t := by
      simp only [hV₃def, hV₁def, amplifiedVerifier, ← transcriptLength_evalShape,
        evalShape_repeatShapePoly,
        evalShape_append, evalShape_cons, evalShape_repeatShapePoly, Polynomial.eval_mul,
        Polynomial.eval_ofNat, hM]
    have hA' := hA a
    rw [evalShape_append, evalShape_cons, evalShape_cons] at hA'
    rw [h3]
    simp only [hV₃]
    exact swap_game_bounds _ _ _ _ _ hK _ _ hA'.1 hA'.2

private theorem AMGameClass_arthur_merlin_append_subset {enc : α ↪ List Bool} (τ : List AMMove) :
    AMGameClass enc (.arthur :: .merlin :: τ) ⊆ AMGameClass enc [.arthur, .merlin] := by
  induction τ with
  | nil => exact le_rfl
  | cons x τ ih =>
    refine le_trans ?_ ih
    cases x
    · exact (AMGameClass_swap [.arthur] τ).trans (AMGameClass_merge [] (.merlin :: τ) .arthur)
    · exact AMGameClass_merge [.arthur] τ .merlin

/-- **Every fixed-pattern public-coin game is in `AM`** [Babai][Babai1985],
[Babai and Moran][BabaiMoran1988]. -/
theorem AMGameClass_subset_AM {enc : α ↪ List Bool} (π : List AMMove) :
    AMGameClass enc π ⊆ AM enc := by
  rw [← AMGameClass_arthur_merlin]
  exact (AMGameClass_mono ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))).trans
    (AMGameClass_arthur_merlin_append_subset π)

/-- **Round collapse**: a pattern containing an Arthur move followed later by a Merlin move gives
exactly `AM`. -/
theorem AMGameClass_eq_AM {enc : α ↪ List Bool} {π : List AMMove}
    (h : List.Sublist [.arthur, .merlin] π) : AMGameClass enc π = AM enc :=
  le_antisymm (AMGameClass_subset_AM π)
    (by rw [← AMGameClass_arthur_merlin]; exact AMGameClass_mono h)

/-- **`AM[k] = AM`** for every constant `k ≥ 2` [Babai][Babai1985],
[Babai and Moran][BabaiMoran1988]. -/
theorem AMk_eq_AM {enc : α ↪ List Bool} {k : ℕ} (hk : 2 ≤ k) : AMk enc k = AM enc := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  exact AMGameClass_eq_AM (((List.nil_sublist _).cons_cons _).cons_cons _)

/-- **`MA[k] = AM`** for every constant `k ≥ 3` [Babai][Babai1985],
[Babai and Moran][BabaiMoran1988]. -/
theorem MAk_eq_AM {enc : α ↪ List Bool} {k : ℕ} (hk : 3 ≤ k) : MAk enc k = AM enc := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  exact AMGameClass_eq_AM ((((List.nil_sublist _).cons_cons _).cons_cons _).cons _)

/-- **`MAM = AM`** [Babai][Babai1985]. -/
theorem AMGameClass_merlin_arthur_merlin {enc : α ↪ List Bool} :
    AMGameClass enc [.merlin, .arthur, .merlin] = AM enc :=
  MAk_eq_AM (k := 3) le_rfl

end Cslib.Complexity
