/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.IP.Games
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Public coins emulate a count over private coins

The emulation of private coins by public coins of [Goldwasser and Sipser][GoldwasserSipser1986]
([Arora and Barak, Theorem 8.8][AroraBarak07]), for an arbitrary `0`/`1`
payoff. Let `g` be a private-coin game shape (`Cslib.Complexity.IPMove`) and
`V : List Bool → Bool` a payoff on complete transcripts. The count
`Cslib.Complexity.IPGame.count g V` sums over the verifier's messages and maximises over the
prover's. A public-coin game of shape `Emulation.shape B Z g` lets Merlin prove lower bounds on this
count to Arthur.

At a verifier move of `n` bits, Arthur sends the seed of an affine hash to `B` bits of strings of
`n + Z` bits (`Cslib.Complexity.SetLowerBound.hashZero`). Merlin answers with a claim, the number
`b ≤ B` of `true` bits in a block of `B` bits, a message `m` of `n` bits and padding `z` of `Z`
bits. The claim `b` says that the continuation after `m` has count at least `2 ^ b`. With the
current claim `κ`, Merlin's answer must hash to zero and the first `Z + κ - (b + K)` bits of `z`
must be `false`: when the claim `κ` is honest, about `2 ^ (κ - b)` messages have continuations
worth `2 ^ b`, each padded in `2 ^ (b + K - κ)` ways, so the padded set has about `2 ^ K`
elements. At a prover move Merlin sends the prover's message. At the end Arthur accepts when the
last claim is `0` and `V` accepts the transcript (`Cslib.Complexity.Emulation.check`).

* **Soundness** (`Cslib.Complexity.Emulation.value_le`): for `B ≤ K`, `μ > 0` and an initial
  claim `κ ≤ K`, the value is at most `c (B + 1) 2 ^ K / (μ 2 ^ B) + μ ^ c N / 2 ^ κ`, where `c`
  is the number of verifier moves and `N` the count. A claim `b` is *generous* for a message `m`
  when `2 ^ κ N_m > μ 2 ^ b N`; the generous messages number at most `2 ^ κ / (μ 2 ^ b)`, so a
  random hash finds a padded generous answer with probability at most `2 ^ K / (μ 2 ^ B)` (the first
  moment bound), for each of the `B + 1` claims. Otherwise the claim is not generous and the
  induction applies.
* **Completeness** (`Cslib.Complexity.Emulation.one_sub_le_value`): for `B ≤ K`, `B + K ≤ Z`,
  at most `B` verifier bits and an initial claim `κ ≤ B` with `2 ^ κ ≤ N`, the value is at least
  `1 - c (B + 1) 2 ^ B / 2 ^ K`. Some scale `β ≤ B` carries a `1 / (B + 1)` share of the count, the
  messages whose continuations are worth `2 ^ β` padded are at least `2 ^ K / (B + 1)`, and a random
  hash misses them with probability at most `(B + 1) 2 ^ B / 2 ^ K` (the second moment bound).

With `B` polynomial and `K = B + O(log B)` both errors are `O(1 / c)`, while the initial claim
can be `log₂` of the count up to a factor `μ ^ c`, polynomial for a constant number of rounds.
This is the core of `IP[k] ⊆ AM[k + 2]` (`CslibFrontier.Computability.Complexity.Classes.IP.Games.
GoldwasserSipser`). The claims are exact numbers of bits, not rounded to powers of two of the
counts, which removes the separate normalisation of the set lower bound protocol.

## Main definitions

* `Cslib.Complexity.Emulation.shape`, `Cslib.Complexity.Emulation.shapePoly`: the public-coin
  game shape.
* `Cslib.Complexity.Emulation.check`: the public-coin verifier.
* `Cslib.Complexity.Emulation.countFrom`: the count after a transcript prefix.

## Main results

* `Cslib.Complexity.Emulation.value_le`: soundness.
* `Cslib.Complexity.Emulation.one_sub_le_value`: completeness.
* `Cslib.Complexity.Emulation.computableInPolyTime_check`: the verifier is polynomial-time.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM SetLowerBound

namespace IPGame

/-- The number of verifier moves of a private-coin game shape. -/
def verifierMoves (g : List (IPMove × ℕ)) : ℕ := (g.map Prod.fst).count .verifier

@[simp] theorem verifierMoves_nil : verifierMoves [] = 0 := rfl

@[simp] theorem verifierMoves_verifier (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierMoves ((.verifier, n) :: g) = verifierMoves g + 1 := by
  simp [verifierMoves]

@[simp] theorem verifierMoves_prover (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierMoves ((.prover, n) :: g) = verifierMoves g := by
  simp [verifierMoves]

/-- A count of a `0`/`1`-bounded payoff is at most `2 ^ verifierBits g`. -/
theorem count_le_two_pow (g : List (IPMove × ℕ)) (f : List Bool → ℕ) (hf : ∀ t, f t ≤ 1) :
    count g f ≤ 2 ^ verifierBits g := by
  have h := count_eq_value g f
  have hv : AMGame.value true (toAM g) (fun t => (f t : ℚ)) ≤ 1 :=
    AMGame.value_le_one _ _ fun t => by exact_mod_cast hf t
  have : (count g f : ℚ) ≤ 2 ^ verifierBits g := by
    rw [h]
    have : (0 : ℚ) < 2 ^ verifierBits g := by positivity
    nlinarith
  exact_mod_cast this

/-- The count of a concatenation of shapes: the count of the first shape, whose payoff is the count
of the second. -/
theorem count_append (g h : List (IPMove × ℕ)) (f : List Bool → ℕ) :
    count (g ++ h) f = count g fun t => count h fun u => f (t ++ u) := by
  induction g generalizing f with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [List.cons_append, count_verifier, ih, List.append_assoc]
    · simp only [List.cons_append, count_prover, ih, List.append_assoc]

end IPGame

namespace Emulation

open IPGame

/-! ### The public-coin game -/

/-- The public-coin shape emulating a private-coin shape: a verifier move of `n` bits becomes
Arthur's hash seed of `B (n + Z) + B` bits followed by Merlin's claim, message and padding of
`B + (n + Z)` bits, and a prover move of `n` bits becomes a Merlin move of `n` bits. -/
def shape (B Z : ℕ) : List (IPMove × ℕ) → List (AMMove × ℕ)
  | [] => []
  | (.verifier, n) :: g => (.arthur, B * (n + Z) + B) :: (.merlin, B + (n + Z)) :: shape B Z g
  | (.prover, n) :: g => (.merlin, n) :: shape B Z g

/-- The move pattern of `Cslib.Complexity.Emulation.shape`. -/
def pattern : List IPMove → List AMMove
  | [] => []
  | .verifier :: π => .arthur :: .merlin :: pattern π
  | .prover :: π => .merlin :: pattern π

theorem map_fst_shape (B Z : ℕ) (g : List (IPMove × ℕ)) :
    (shape B Z g).map Prod.fst = pattern (g.map Prod.fst) := by
  induction g with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x <;> simp [shape, pattern, ih]

theorem pattern_append (π σ : List IPMove) : pattern (π ++ σ) = pattern π ++ pattern σ := by
  induction π with
  | nil => rfl
  | cons x π ih => cases x <;> simp [pattern, ih]

/-- The polynomial public-coin shape emulating a polynomial private-coin shape. -/
noncomputable def shapePoly (B Z : Polynomial ℕ) : List (IPMove × Polynomial ℕ) →
    List (AMMove × Polynomial ℕ)
  | [] => []
  | (.verifier, n) :: G => (.arthur, B * (n + Z) + B) :: (.merlin, B + (n + Z)) :: shapePoly B Z G
  | (.prover, n) :: G => (.merlin, n) :: shapePoly B Z G

theorem evalShape_shapePoly (B Z : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    AMGame.evalShape (shapePoly B Z G) n = shape (B.eval n) (Z.eval n) (evalShape G n) := by
  induction G with
  | nil => rfl
  | cons x G ih =>
    obtain ⟨_ | _, p⟩ := x
    · change _ = shape _ _ ((.verifier, p.eval n) :: evalShape G n)
      simp only [shapePoly, AMGame.evalShape_cons, ih, shape, Polynomial.eval_add,
        Polynomial.eval_mul]
    · change _ = shape _ _ ((.prover, p.eval n) :: evalShape G n)
      simp only [shapePoly, AMGame.evalShape_cons, ih, shape]

theorem map_fst_shapePoly (B Z : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ)) :
    (shapePoly B Z G).map Prod.fst = pattern (G.map Prod.fst) := by
  induction G with
  | nil => rfl
  | cons x G ih =>
    obtain ⟨_ | _, n⟩ := x <;> simp [shapePoly, pattern, ih]

/-- The public-coin verifier emulating the count of the payoff `V` on the shape `g`, with current
claim `κ` and transcript prefix `p`, on Arthur's and Merlin's messages `w`. At a verifier move of
`n` bits it reads Arthur's seed `r`, Merlin's claim `b` (the number of `true` bits in a block of
`B` bits), message `m` and padding `z`, and checks that `m ++ z` hashes to zero and that the first
`Z + κ - (b + K)` bits of `z` are `false`. At a prover move it reads the prover's message. At the
end it accepts when the claim is `0` and `V` accepts the transcript. -/
def check (B Z K : ℕ) (V : List Bool → Bool) :
    List (IPMove × ℕ) → ℕ → List Bool → List Bool → Bool
  | [], κ, p, _ => decide (κ = 0) && V p
  | (.verifier, n) :: g, κ, p, w =>
    let r := w.take (B * (n + Z) + B)
    let y := w.drop (B * (n + Z) + B)
    let b := (y.take B).count true
    let x := (y.drop B).take (n + Z)
    hashZero B (n + Z) r x &&
      (!((x.drop n).take (Z + κ - (b + K))).any fun b => b) &&
      check B Z K V g b (p ++ x.take n) ((y.drop B).drop (n + Z))
  | (.prover, n) :: g, κ, p, w => check B Z K V g κ (p ++ w.take n) (w.drop n)

/-- The count of the payoff `V` on the shape `g` after the transcript prefix `p`. -/
def countFrom (g : List (IPMove × ℕ)) (V : List Bool → Bool) (p : List Bool) : ℕ :=
  count g fun t => (V (p ++ t)).toNat

theorem countFrom_nil (V : List Bool → Bool) (p : List Bool) :
    countFrom [] V p = (V p).toNat := by
  simp [countFrom, count]

theorem countFrom_verifier (n : ℕ) (g : List (IPMove × ℕ)) (V : List Bool → Bool) (p : List Bool) :
    countFrom ((.verifier, n) :: g) V p = ∑ m : Fin n → Bool, countFrom g V (p ++ List.ofFn m) := by
  simp [countFrom, count, List.append_assoc]

theorem countFrom_prover (n : ℕ) (g : List (IPMove × ℕ)) (V : List Bool → Bool) (p : List Bool) :
    countFrom ((.prover, n) :: g) V p =
      univ.sup fun y : Fin n → Bool => countFrom g V (p ++ List.ofFn y) := by
  simp [countFrom, count, List.append_assoc]

theorem countFrom_le_two_pow (g : List (IPMove × ℕ)) (V : List Bool → Bool) (p : List Bool) :
    countFrom g V p ≤ 2 ^ verifierBits g :=
  count_le_two_pow g _ fun _ => Bool.toNat_le _

theorem check_nil (B Z K : ℕ) (V : List Bool → Bool) (κ : ℕ) (p w : List Bool) :
    check B Z K V [] κ p w = (decide (κ = 0) && V p) := rfl

theorem check_prover_ofFn (B Z K : ℕ) (V : List Bool → Bool) (n : ℕ) (g : List (IPMove × ℕ))
    (κ : ℕ) (p : List Bool) (y : Fin n → Bool) (t : List Bool) :
    check B Z K V ((.prover, n) :: g) κ p (List.ofFn y ++ t) =
      check B Z K V g κ (p ++ List.ofFn y) t := by
  simp only [check, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]

theorem check_verifier_ofFn (B Z K : ℕ) (V : List Bool → Bool) (n : ℕ) (g : List (IPMove × ℕ))
    (κ : ℕ) (p : List Bool) (r : Fin (B * (n + Z) + B) → Bool) (c : Fin B → Bool)
    (m : Fin n → Bool) (z : Fin Z → Bool) (t : List Bool) :
    check B Z K V ((.verifier, n) :: g) κ p
        (List.ofFn r ++ (List.ofFn c ++ (List.ofFn m ++ List.ofFn z) ++ t)) =
      (hashZero B (n + Z) (List.ofFn r) (List.ofFn m ++ List.ofFn z) &&
        (!((List.ofFn z).take (Z + κ - ((List.ofFn c).count true + K))).any fun b => b) &&
        check B Z K V g ((List.ofFn c).count true) (p ++ List.ofFn m) t) := by
  have h1 : (List.ofFn c ++ (List.ofFn m ++ List.ofFn z) ++ t).take B = List.ofFn c := by
    rw [List.append_assoc]; exact List.take_left' List.length_ofFn
  have h2 : (List.ofFn c ++ (List.ofFn m ++ List.ofFn z) ++ t).drop B =
      List.ofFn m ++ List.ofFn z ++ t := by
    rw [List.append_assoc]; exact List.drop_left' List.length_ofFn
  have h3 : (List.ofFn m ++ List.ofFn z ++ t).take (n + Z) = List.ofFn m ++ List.ofFn z :=
    List.take_left' (by simp)
  have h4 : (List.ofFn m ++ List.ofFn z ++ t).drop (n + Z) = t :=
    List.drop_left' (by simp)
  simp only [check, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, h1, h2,
    h3, h4]

/-- Values of `a && F t` for a constant `a`. -/
private theorem value_and_left (h : List (AMMove × ℕ)) (a : Bool) (F : List Bool → Bool) :
    AMGame.value true h (fun t => ((a && F t).toNat : ℚ)) =
      (a.toNat : ℚ) * AMGame.value true h fun t => ((F t).toNat : ℚ) := by
  cases a
  · simpa using AMGame.value_const true h 0
  · simp

private theorem value_verifier_inner (B Z K : ℕ) (V : List Bool → Bool) (n : ℕ)
    (g : List (IPMove × ℕ)) (κ : ℕ) (p : List Bool) (r : Fin (B * (n + Z) + B) → Bool)
    (c : Fin B → Bool) (m : Fin n → Bool) (z : Fin Z → Bool) :
    AMGame.value true (shape B Z g) (fun t => ((check B Z K V ((.verifier, n) :: g) κ p
        (List.ofFn r ++ (List.ofFn (Fin.append c (Fin.append m z)) ++ t))).toNat : ℚ)) =
      ((BitString.LinearHash.affineHash (seedEquiv B (n + Z) r) (Fin.append m z) = 0 ∧
          (!((List.ofFn z).take (Z + κ - ((List.ofFn c).count true + K))).any fun b => b) = true :
          Bool).toNat : ℚ) *
        AMGame.value true (shape B Z g) fun t =>
          ((check B Z K V g ((List.ofFn c).count true) (p ++ List.ofFn m) t).toNat : ℚ) := by
  simp only [List.ofFn_fin_append]
  have hx : hashZero B (n + Z) (List.ofFn r) (List.ofFn m ++ List.ofFn z) =
      decide (BitString.LinearHash.affineHash (seedEquiv B (n + Z) r) (Fin.append m z) = 0) := by
    rw [← List.ofFn_fin_append]
    exact Bool.eq_iff_iff.2 ((hashZero_ofFn r _).trans decide_eq_true_iff.symm)
  simp only [check_verifier_ofFn, hx]
  rw [value_and_left]
  congr 1

private theorem exists_eq_append (B n Z : ℕ) (y : Fin (B + (n + Z)) → Bool) :
    ∃ (c : Fin B → Bool) (m : Fin n → Bool) (z : Fin Z → Bool),
      y = Fin.append c (Fin.append m z) :=
  ⟨fun i => y (Fin.castAdd _ i), fun i => y (Fin.natAdd B (Fin.castAdd Z i)),
    fun i => y (Fin.natAdd B (Fin.natAdd n i)), by
      conv_lhs => rw [← Fin.append_castAdd_natAdd (f := y)]
      congr 1
      exact (Fin.append_castAdd_natAdd (f := fun i => y (Fin.natAdd B i))).symm⟩

private theorem value_verifier (B Z K : ℕ) (V : List Bool → Bool) (n : ℕ) (g : List (IPMove × ℕ))
    (κ : ℕ) (p : List Bool) :
    AMGame.value true (shape B Z ((.verifier, n) :: g))
        (fun t => ((check B Z K V ((.verifier, n) :: g) κ p t).toNat : ℚ)) =
      (∑ r : Fin (B * (n + Z) + B) → Bool, univ.sup' univ_nonempty fun y : Fin (B + (n + Z)) →
        Bool => AMGame.value true (shape B Z g) fun t => ((check B Z K V ((.verifier, n) :: g) κ p
          (List.ofFn r ++ (List.ofFn y ++ t))).toNat : ℚ)) / 2 ^ (B * (n + Z) + B) := by
  rw [shape, AMGame.value_arthur]
  simp only [AMGame.value_merlin_true]

/-- Padding of `Z` bits whose first `d` bits are `false`. -/
private theorem card_padding (Z d : ℕ) :
    #{z : Fin Z → Bool | (!((List.ofFn z).take d).any fun b => b) = true} = 2 ^ (Z - d) := by
  have hmin : ∀ z : Fin Z → Bool, (List.ofFn z).take d = (List.ofFn z).take (min d Z) := by
    grind [List.take_eq_take_min, List.length_ofFn]
  simp only [hmin]
  rw [BitString.card_filter_take (min_le_right d Z) fun w => (!w.any fun b => b) = true,
    BitString.card_filter_not_any, mul_one]
  congr 1
  omega

/-! ### Soundness -/

/-- **Soundness of the emulation.** With `c` verifier moves, a count `N` after the prefix `p` and
the claim `κ ≤ K`, Merlin wins the public-coin game with probability at most
`c (B + 1) 2 ^ K / (μ 2 ^ B) + μ ^ c N / 2 ^ κ`, for every `μ > 0`. -/
theorem value_le (B Z K μ : ℕ) (hBK : B ≤ K) (hμ : 0 < μ) (V : List Bool → Bool)
    (g : List (IPMove × ℕ)) (κ : ℕ) (hκ : κ ≤ K) (p : List Bool) :
    AMGame.value true (shape B Z g) (fun t => ((check B Z K V g κ p t).toNat : ℚ)) ≤
      verifierMoves g * ((B + 1) * 2 ^ K / (μ * 2 ^ B)) +
        μ ^ verifierMoves g * countFrom g V p / 2 ^ κ := by
  induction g generalizing κ p with
  | nil =>
    rw [shape, AMGame.value_nil, check_nil, verifierMoves_nil, countFrom_nil]
    by_cases h : κ = 0 ∧ V p = true
    · obtain ⟨rfl, hV⟩ := h
      simp [hV]
    · have : (decide (κ = 0) && V p) = false := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using h
      rw [this]
      simp only [Bool.toNat_false, Nat.cast_zero]
      positivity
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · -- verifier move
      have hP : (0 : ℚ) < 2 ^ (B * (n + Z) + B) := by positivity
      rw [value_verifier, verifierMoves_verifier, countFrom_verifier]
      set N := ∑ m : Fin n → Bool, countFrom g V (p ++ List.ofFn m) with hN
      -- the messages on which the claim `b` is generous
      let T (b : ℕ) : Finset (Fin n → Bool) :=
        {m | μ * 2 ^ b * N < 2 ^ κ * countFrom g V (p ++ List.ofFn m)}
      have hT (b : ℕ) : μ * 2 ^ b * #(T b) ≤ 2 ^ κ := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · have hTe : T b = ∅ := by
            refine filter_eq_empty_iff.2 fun m _ hm => ?_
            have hle : countFrom g V (p ++ List.ofFn m) ≤ N :=
              single_le_sum (f := fun m : Fin n → Bool => countFrom g V (p ++ List.ofFn m))
                (fun _ _ => Nat.zero_le _) (mem_univ m)
            rw [h0] at hm hle
            rw [Nat.le_zero.1 hle] at hm
            simp at hm
          rw [hTe, card_empty, mul_zero]
          exact Nat.zero_le _
        · have hsum : μ * 2 ^ b * #(T b) * N ≤ 2 ^ κ * N := by
            calc μ * 2 ^ b * #(T b) * N = ∑ _m ∈ T b, μ * 2 ^ b * N := by
                  rw [sum_const, smul_eq_mul]; ring
              _ ≤ ∑ m ∈ T b, 2 ^ κ * countFrom g V (p ++ List.ofFn m) :=
                  sum_le_sum fun m hm => (mem_filter.1 hm).2.le
              _ ≤ ∑ m, 2 ^ κ * countFrom g V (p ++ List.ofFn m) :=
                  sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
              _ = 2 ^ κ * N := by rw [← mul_sum]
          exact Nat.le_of_mul_le_mul_right hsum hpos
      -- the padded answers with a generous claim
      let S (b : ℕ) : Finset (Fin (n + Z) → Bool) :=
        (T b ×ˢ (univ.filter fun z : Fin Z → Bool =>
          (!((List.ofFn z).take (Z + κ - (b + K))).any fun b => b) = true)).map
            (Fin.appendEquiv n Z).toEmbedding
      have hS (b : ℕ) : #(S b) = #(T b) * 2 ^ (Z - (Z + κ - (b + K))) := by
        rw [card_map, card_product, card_padding]
      have hmemS (b : ℕ) (m : Fin n → Bool) (z : Fin Z → Bool) (hm : m ∈ T b)
          (hz : (!((List.ofFn z).take (Z + κ - (b + K))).any fun b => b) = true) :
          Fin.append m z ∈ S b :=
        mem_map.2 ⟨(m, z), mem_product.2 ⟨hm, mem_filter.2 ⟨mem_univ _, hz⟩⟩, rfl⟩
      -- the seeds for which a generous claim succeeds
      have hh := (BitString.LinearHash.isPairwiseIndependentHash_affineHash B
        (n + Z)).comp_seedEquiv (seedEquiv B (n + Z))
      let bad (b : ℕ) : Finset (Fin (B * (n + Z) + B) → Bool) :=
        {r | 0 ∈ (S b).image (BitString.LinearHash.affineHash (seedEquiv B (n + Z) r))}
      have hbad (b : ℕ) : μ * #(bad b) * 2 ^ B ≤ 2 ^ K * 2 ^ (B * (n + Z) + B) := by
        have h1 : #(bad b) * 2 ^ B ≤ #(S b) * 2 ^ (B * (n + Z) + B) := by
          simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
            hh.card_filter_mem_image_mul_le (S b) 0
        have h2 : μ * #(S b) ≤ 2 ^ K := by
          rw [hS]
          calc μ * (#(T b) * 2 ^ (Z - (Z + κ - (b + K))))
              ≤ μ * (#(T b) * 2 ^ (b + (K - κ))) := by
                gcongr
                omega
            _ = μ * 2 ^ b * #(T b) * 2 ^ (K - κ) := by rw [pow_add]; ring
            _ ≤ 2 ^ κ * 2 ^ (K - κ) := Nat.mul_le_mul_right _ (hT b)
            _ = 2 ^ K := by rw [← pow_add]; congr 1; omega
        calc μ * #(bad b) * 2 ^ B = μ * (#(bad b) * 2 ^ B) := by ring
          _ ≤ μ * (#(S b) * 2 ^ (B * (n + Z) + B)) := Nat.mul_le_mul_left _ h1
          _ = μ * #(S b) * 2 ^ (B * (n + Z) + B) := by ring
          _ ≤ 2 ^ K * 2 ^ (B * (n + Z) + B) := Nat.mul_le_mul_right _ h2
      -- pointwise bound on Merlin's best answer
      have hpt (r : Fin (B * (n + Z) + B) → Bool) :
          (univ.sup' univ_nonempty fun y : Fin (B + (n + Z)) → Bool =>
            AMGame.value true (shape B Z g) fun t => ((check B Z K V ((.verifier, n) :: g) κ p
              (List.ofFn r ++ (List.ofFn y ++ t))).toNat : ℚ)) ≤
          (∑ b ∈ range (B + 1), if r ∈ bad b then (1 : ℚ) else 0) +
            (verifierMoves g * ((B + 1) * 2 ^ K / (μ * 2 ^ B)) +
              μ ^ (verifierMoves g + 1) * N / 2 ^ κ) := by
        refine sup'_le _ _ fun y _ => ?_
        obtain ⟨c, m, z, rfl⟩ := exists_eq_append B n Z y
        rw [value_verifier_inner]
        have hbB : (List.ofFn c).count true ≤ B := by
          simpa using List.count_le_length (a := true) (l := List.ofFn c)
        have hsum_nonneg : (0 : ℚ) ≤ ∑ b ∈ range (B + 1), if r ∈ bad b then (1 : ℚ) else 0 :=
          sum_nonneg fun _ _ => by split_ifs <;> norm_num
        have hE_nonneg : (0 : ℚ) ≤ verifierMoves g * ((B + 1) * 2 ^ K / (μ * 2 ^ B)) +
            μ ^ (verifierMoves g + 1) * N / 2 ^ κ := by positivity
        by_cases hloc : BitString.LinearHash.affineHash (seedEquiv B (n + Z) r)
            (Fin.append m z) = 0 ∧ (!((List.ofFn z).take
              (Z + κ - ((List.ofFn c).count true + K))).any fun b => b) = true
        · rw [decide_eq_true hloc, Bool.toNat_true, Nat.cast_one, one_mul]
          by_cases hm : m ∈ T ((List.ofFn c).count true)
          · have hr : r ∈ bad ((List.ofFn c).count true) :=
              mem_filter.2 ⟨mem_univ _, mem_image.2 ⟨_, hmemS _ m z hm hloc.2, hloc.1⟩⟩
            have h1 : (1 : ℚ) ≤ ∑ b ∈ range (B + 1), if r ∈ bad b then (1 : ℚ) else 0 := by
              have := single_le_sum (f := fun b => if r ∈ bad b then (1 : ℚ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (mem_range.2 (Nat.lt_succ_of_le hbB))
              simpa only [hr, ite_true] using this
            have hv : AMGame.value true (shape B Z g) (fun t => ((check B Z K V g
                ((List.ofFn c).count true) (p ++ List.ofFn m) t).toNat : ℚ)) ≤ 1 :=
              AMGame.value_le_one _ _ fun t => by
                cases check B Z K V g ((List.ofFn c).count true) (p ++ List.ofFn m) t <;> norm_num
            linarith
          · have hle : 2 ^ κ * countFrom g V (p ++ List.ofFn m) ≤
                μ * 2 ^ ((List.ofFn c).count true) * N := by
              by_contra hcon
              exact hm (mem_filter.2 ⟨mem_univ _, not_le.1 hcon⟩)
            refine (ih _ (hbB.trans hBK) _).trans ?_
            have hle' : (μ : ℚ) ^ verifierMoves g * countFrom g V (p ++ List.ofFn m) /
                2 ^ ((List.ofFn c).count true) ≤ μ ^ (verifierMoves g + 1) * N / 2 ^ κ := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              have hq : (2 : ℚ) ^ κ * countFrom g V (p ++ List.ofFn m) ≤
                  μ * 2 ^ ((List.ofFn c).count true) * N := by
                exact_mod_cast hle
              calc (μ : ℚ) ^ verifierMoves g * countFrom g V (p ++ List.ofFn m) * 2 ^ κ
                  = μ ^ verifierMoves g * (2 ^ κ * countFrom g V (p ++ List.ofFn m)) := by ring
                _ ≤ μ ^ verifierMoves g * (μ * 2 ^ ((List.ofFn c).count true) * N) := by gcongr
                _ = μ ^ (verifierMoves g + 1) * N * 2 ^ ((List.ofFn c).count true) := by ring
            linarith
        · rw [decide_eq_false hloc, Bool.toNat_false, Nat.cast_zero, zero_mul]
          linarith
      -- average over Arthur's seeds
      rw [div_le_iff₀ hP]
      refine (sum_le_sum fun r _ => hpt r).trans ?_
      rw [sum_add_distrib, sum_comm, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      have hb' : ∀ b ∈ range (B + 1), (∑ r : Fin (B * (n + Z) + B) → Bool,
          if r ∈ bad b then (1 : ℚ) else 0) ≤ 2 ^ K * 2 ^ (B * (n + Z) + B) / (μ * 2 ^ B) := by
        intro b _
        have hfilt : (univ.filter fun r => r ∈ bad b) = bad b := by
          ext r; simp only [mem_filter, mem_univ, true_and]
        rw [sum_boole, hfilt, le_div_iff₀ (by positivity)]
        have := hbad b
        calc (#(bad b) : ℚ) * (μ * 2 ^ B) = ((μ * #(bad b) * 2 ^ B : ℕ) : ℚ) := by
              push_cast; ring
          _ ≤ ((2 ^ K * 2 ^ (B * (n + Z) + B) : ℕ) : ℚ) := by exact_mod_cast this
          _ = _ := by push_cast; ring
      have hsum := sum_le_sum hb'
      rw [sum_const, card_range, nsmul_eq_mul] at hsum
      have hμq : (0 : ℚ) < μ := by exact_mod_cast hμ
      push_cast at hsum ⊢
      have key : ((B : ℚ) + 1) * (2 ^ K * 2 ^ (B * (n + Z) + B) / (μ * 2 ^ B)) +
          (2 : ℚ) ^ (B * (n + Z) + B) * (verifierMoves g * ((B + 1) * 2 ^ K / (μ * 2 ^ B)) +
            μ ^ (verifierMoves g + 1) * N / 2 ^ κ) =
          ((verifierMoves g + 1) * ((B + 1) * 2 ^ K / (μ * 2 ^ B)) +
            μ ^ (verifierMoves g + 1) * N / 2 ^ κ) * 2 ^ (B * (n + Z) + B) := by
        field_simp
        ring
      linarith
    · -- prover move
      rw [shape, AMGame.value_merlin_true, verifierMoves_prover, countFrom_prover]
      refine sup'_le _ _ fun y _ => ?_
      simp only [check_prover_ofFn]
      refine (ih κ hκ _).trans ?_
      gcongr
      exact_mod_cast Finset.le_sup (f := fun y : Fin n → Bool => countFrom g V (p ++ List.ofFn y))
        (mem_univ y)

/-! ### Completeness -/

private theorem count_ofFn_lt (B β : ℕ) (hβ : β ≤ B) :
    (List.ofFn fun i : Fin B => decide (i.val < β)).count true = β := by
  have h : (List.ofFn fun i : Fin B => decide (i.val < β)) =
      List.replicate β true ++ List.replicate (B - β) false := by
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_append, List.length_replicate,
      List.getElem_replicate]
    split_ifs with h3 <;> simp [h3]
  rw [h, List.count_append, List.count_replicate_self, List.count_replicate]
  simp

/-- A number below `2 ^ (B + 1)` is at most the sum of the powers of two below it. -/
private theorem le_sum_two_pow (B x : ℕ) (hx : x < 2 ^ (B + 1)) :
    x ≤ ∑ β ∈ range (B + 1), if 2 ^ β ≤ x then 2 ^ β else 0 := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · exact Nat.zero_le _
  have hlog : Nat.log 2 x ≤ B := Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' hx)
  have hiff (β : ℕ) : 2 ^ β ≤ x ↔ β < Nat.log 2 x + 1 := by
    rw [Nat.lt_succ_iff]
    exact (Nat.le_log_iff_pow_le (by norm_num) hpos.ne').symm
  have hsplit : (∑ β ∈ range (B + 1), if 2 ^ β ≤ x then 2 ^ β else 0) =
      ∑ β ∈ range (Nat.log 2 x + 1), 2 ^ β := by
    rw [← sum_filter]
    congr 1
    ext β
    simp only [mem_filter, mem_range, hiff]
    omega
  rw [hsplit, Nat.geomSum_eq le_rfl]
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x
  omega

/-- **Completeness of the emulation.** With `c` verifier moves of at most `B` bits in total, a
count at least `2 ^ κ` after the prefix `p` and the claim `κ ≤ B`, Merlin wins the public-coin
game with probability at least `1 - c (B + 1) 2 ^ B / 2 ^ K`, when `B ≤ K` and `B + K ≤ Z`. -/
theorem one_sub_le_value (B Z K : ℕ) (hBK : B ≤ K) (hZ : B + K ≤ Z) (V : List Bool → Bool)
    (g : List (IPMove × ℕ)) (hg : verifierBits g ≤ B) (κ : ℕ) (hκ : κ ≤ B)
    (p : List Bool) (hN : 2 ^ κ ≤ countFrom g V p) :
    1 - verifierMoves g * ((B + 1) * 2 ^ B / 2 ^ K) ≤
      AMGame.value true (shape B Z g) (fun t => ((check B Z K V g κ p t).toNat : ℚ)) := by
  induction g generalizing κ p with
  | nil =>
    rw [countFrom_nil] at hN
    have hV : V p = true := by grind
    have hκ0 : κ = 0 := by
      rw [hV] at hN
      rcases Nat.eq_zero_or_pos κ with h | h
      · exact h
      · have : 2 ^ 1 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) h
        simp at hN
        omega
    rw [shape, AMGame.value_nil, check_nil, verifierMoves_nil, hκ0, hV]
    simp
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · -- verifier move
      have hP : (0 : ℚ) < 2 ^ (B * (n + Z) + B) := by positivity
      have hg' : verifierBits g ≤ B := by
        rw [verifierBits_verifier] at hg; omega
      rw [countFrom_verifier] at hN
      -- the messages that leave at least `2 ^ β` accepting continuations
      let U (β : ℕ) : Finset (Fin n → Bool) :=
        univ.filter fun m => 2 ^ β ≤ countFrom g V (p ++ List.ofFn m)
      have hlt (m : Fin n → Bool) : countFrom g V (p ++ List.ofFn m) < 2 ^ (B + 1) :=
        lt_of_le_of_lt ((countFrom_le_two_pow g V _).trans
          (Nat.pow_le_pow_right (by norm_num) hg'))
          (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B))
      have hsumU : 2 ^ κ ≤ ∑ β ∈ range (B + 1), 2 ^ β * #(U β) := by
        refine hN.trans ?_
        calc ∑ m : Fin n → Bool, countFrom g V (p ++ List.ofFn m)
            ≤ ∑ m : Fin n → Bool, ∑ β ∈ range (B + 1),
                if 2 ^ β ≤ countFrom g V (p ++ List.ofFn m) then 2 ^ β else 0 :=
              sum_le_sum fun m _ => le_sum_two_pow B _ (hlt m)
          _ = ∑ β ∈ range (B + 1), 2 ^ β * #(U β) := by
              rw [sum_comm]
              refine sum_congr rfl fun β _ => ?_
              rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
      -- pigeonhole: some `β` carries a `1 / (B + 1)` share
      obtain ⟨β, hβ, hβU⟩ : ∃ β ∈ range (B + 1), 2 ^ κ ≤ (B + 1) * (2 ^ β * #(U β)) := by
        by_contra hcon
        push Not at hcon
        have h1 : (B + 1) * ∑ β ∈ range (B + 1), 2 ^ β * #(U β) <
            ∑ _β ∈ range (B + 1), 2 ^ κ := by
          rw [mul_sum]
          exact sum_lt_sum_of_nonempty nonempty_range_add_one hcon
        rw [sum_const, card_range, smul_eq_mul] at h1
        have h2 := Nat.mul_le_mul_left (B + 1) hsumU
        omega
      have hβB : β ≤ B := Nat.lt_succ_iff.1 (mem_range.1 hβ)
      -- the padded set of good answers
      let S : Finset (Fin (n + Z) → Bool) :=
        (U β ×ˢ (univ.filter fun z : Fin Z → Bool =>
          (!((List.ofFn z).take (Z + κ - (β + K))).any fun b => b) = true)).map
            (Fin.appendEquiv n Z).toEmbedding
      have hS : 2 ^ K ≤ (B + 1) * #S := by
        rw [card_map, card_product, card_padding]
        have he : Z - (Z + κ - (β + K)) = β + K - κ := by omega
        rw [he]
        calc 2 ^ K = 2 ^ κ * 2 ^ (K - κ) := by rw [← pow_add]; congr 1; omega
          _ ≤ (B + 1) * (2 ^ β * #(U β)) * 2 ^ (K - κ) := Nat.mul_le_mul_right _ hβU
          _ = (B + 1) * (#(U β) * 2 ^ (β + (K - κ))) := by rw [pow_add]; ring
          _ = (B + 1) * (#(U β) * 2 ^ (β + K - κ)) := by congr 3; omega
      have hSne : S.Nonempty := by
        rw [← card_pos]
        rcases Nat.eq_zero_or_pos #S with h | h
        · rw [h, mul_zero] at hS
          exact absurd hS (Nat.two_pow_pos K).not_ge
        · exact h
      -- the seeds that miss the good answers
      have hh := (BitString.LinearHash.isPairwiseIndependentHash_affineHash B
        (n + Z)).comp_seedEquiv (seedEquiv B (n + Z))
      let miss : Finset (Fin (B * (n + Z) + B) → Bool) :=
        univ.filter fun r => 0 ∉ S.image (BitString.LinearHash.affineHash (seedEquiv B (n + Z) r))
      have hmiss : (#miss : ℚ) ≤ (B + 1) * 2 ^ B / 2 ^ K * 2 ^ (B * (n + Z) + B) := by
        have h1 : #miss * #S ≤ 2 ^ B * 2 ^ (B * (n + Z) + B) := by
          simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
            hh.card_filter_notMem_image_mul_le hSne 0
        have h2 : #miss * 2 ^ K ≤ (B + 1) * 2 ^ B * 2 ^ (B * (n + Z) + B) := by
          calc #miss * 2 ^ K ≤ #miss * ((B + 1) * #S) := Nat.mul_le_mul_left _ hS
            _ = (B + 1) * (#miss * #S) := by ring
            _ ≤ (B + 1) * (2 ^ B * 2 ^ (B * (n + Z) + B)) := Nat.mul_le_mul_left _ h1
            _ = (B + 1) * 2 ^ B * 2 ^ (B * (n + Z) + B) := by ring
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact_mod_cast h2
      -- pointwise bound on Merlin's best answer
      have hδ : (0 : ℚ) ≤ verifierMoves g * ((B + 1) * 2 ^ B / 2 ^ K) := by positivity
      have hpt (r : Fin (B * (n + Z) + B) → Bool) :
          1 - verifierMoves g * ((B + 1) * 2 ^ B / 2 ^ K) - (if r ∈ miss then (1 : ℚ) else 0) ≤
            univ.sup' univ_nonempty fun y : Fin (B + (n + Z)) → Bool =>
              AMGame.value true (shape B Z g) fun t => ((check B Z K V ((.verifier, n) :: g) κ p
                (List.ofFn r ++ (List.ofFn y ++ t))).toNat : ℚ) := by
        split_ifs with hr
        · have h0 := AMGame.value_nonneg true (shape B Z g) (f := fun t =>
            ((check B Z K V ((.verifier, n) :: g) κ p (List.ofFn r ++
              (List.ofFn (fun _ : Fin (B + (n + Z)) => false) ++ t))).toNat : ℚ))
            fun t => by positivity
          refine le_trans ?_ (le_trans h0 (le_sup' (fun y : Fin (B + (n + Z)) → Bool =>
            AMGame.value true (shape B Z g) fun t => ((check B Z K V ((.verifier, n) :: g) κ p
              (List.ofFn r ++ (List.ofFn y ++ t))).toNat : ℚ)) (mem_univ _)))
          linarith
        · rw [sub_zero]
          have h0 : 0 ∈ S.image (BitString.LinearHash.affineHash (seedEquiv B (n + Z) r)) := by
            by_contra h
            exact hr (mem_filter.2 ⟨mem_univ _, h⟩)
          obtain ⟨x, hxS, hx0⟩ := mem_image.1 h0
          obtain ⟨⟨m, z⟩, hmz, rfl⟩ := mem_map.1 hxS
          obtain ⟨hm, hz⟩ := mem_product.1 hmz
          have hm' := (mem_filter.1 hm).2
          have hz' := (mem_filter.1 hz).2
          let c : Fin B → Bool := fun i => decide (i.val < β)
          have hc : (List.ofFn c).count true = β := count_ofFn_lt B β hβB
          refine le_trans ?_ (le_sup' _ (mem_univ (Fin.append c (Fin.append m z))))
          rw [value_verifier_inner, hc]
          have hloc : BitString.LinearHash.affineHash (seedEquiv B (n + Z) r)
              (Fin.append m z) = 0 ∧ (!((List.ofFn z).take
                (Z + κ - (β + K))).any fun b => b) = true := ⟨hx0, hz'⟩
          rw [decide_eq_true hloc, Bool.toNat_true, Nat.cast_one, one_mul]
          exact ih hg' β hβB _ hm'
      -- average over Arthur's seeds
      rw [value_verifier, verifierMoves_verifier, le_div_iff₀ hP]
      refine le_trans ?_ (sum_le_sum fun r _ => hpt r)
      rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, sum_boole]
      have hfilt : (univ.filter fun r : Fin (B * (n + Z) + B) → Bool => r ∈ miss) = miss := by
        ext r; simp only [mem_filter, mem_univ, true_and]
      rw [hfilt]
      push_cast
      nlinarith
    · -- prover move
      rw [countFrom_prover] at hN
      obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty
        fun y : Fin n → Bool => countFrom g V (p ++ List.ofFn y)
      rw [hy] at hN
      rw [shape, AMGame.value_merlin_true, verifierMoves_prover]
      refine le_trans ?_ (le_sup' _ (mem_univ y))
      simp only [check_prover_ofFn]
      exact ih (by rwa [verifierBits_prover] at hg) κ hκ _ hN

/-! ### Polynomial time -/

/-- **The public-coin verifier is polynomial-time** on a polynomial shape `G` evaluated at a
polynomial-time length `len`, with polynomial-time parameters `B`, `Z`, `K`, claim `κ`, prefix `p`
and messages `w`, when the payoff `V` is polynomial-time on polynomial-time transcripts. -/
theorem computableInPolyTime_check {γ : Type} {encIn : γ ↪ List Bool}
    (G : List (IPMove × Polynomial ℕ)) {B Z K len : γ → ℕ} {V : γ → List Bool → Bool}
    (hB : ComputableInPolyTime B encIn encUnary) (hZ : ComputableInPolyTime Z encIn encUnary)
    (hK : ComputableInPolyTime K encIn encUnary) (hlen : ComputableInPolyTime len encIn encUnary)
    (hV : ∀ {q : γ → List Bool}, ComputableInPolyTime q encIn encBits →
      ComputableInPolyTime (fun x => V x (q x)) encIn encBool)
    {κ : γ → ℕ} {p w : γ → List Bool} (hκ : ComputableInPolyTime κ encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits) (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => check (B x) (Z x) (K x) (V x) (evalShape G (len x)) (κ x) (p x)
      (w x)) encIn encBool := by
  induction G generalizing κ p w with
  | nil =>
    have h := ComputableInPolyTime.bool_and' (ComputableInPolyTime.decide_eq' hκ
      (ComputableInPolyTime.const 0)) (hV hp)
    exact h.of_enc_eq fun x => rfl
  | cons y G ih =>
    obtain ⟨_ | _, q⟩ := y
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      have hnZ := ComputableInPolyTime.unary_add' hn hZ
      have hP := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hB hnZ) hB
      have hr := ComputableInPolyTime.bitsTakeWithInput hw hP
      have hy := ComputableInPolyTime.bitsDropWithInput hw hP
      have hb := ComputableInPolyTime.bitsCountWithInput
        (ComputableInPolyTime.bitsTakeWithInput hy hB) (ComputableInPolyTime.const true)
      have hyB := ComputableInPolyTime.bitsDropWithInput hy hB
      have hx := ComputableInPolyTime.bitsTakeWithInput hyB hnZ
      have hhash := computableInPolyTime_hashZero hB hnZ hr hx
      have hpad := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bitsAnyWithInput
        (test := fun _ b => b)
        (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.bitsDropWithInput hx hn)
          (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hZ hκ)
            (ComputableInPolyTime.unary_add' hb hK)))
        (ComputableInPolyTime.snd _ _))
      have hrec := ih hb (ComputableInPolyTime.bitsAppend hp
        (ComputableInPolyTime.bitsTakeWithInput hx hn))
        (ComputableInPolyTime.bitsDropWithInput hyB hnZ)
      exact (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hhash hpad)
        hrec).of_enc_eq fun x => rfl
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      exact (ih hκ (ComputableInPolyTime.bitsAppend hp
        (ComputableInPolyTime.bitsTakeWithInput hw hn))
        (ComputableInPolyTime.bitsDropWithInput hw hn)).of_enc_eq fun x => rfl

end Emulation

end Cslib.Complexity
