/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Private-coin interactive games with a fixed pattern of moves

The interactive proofs with a constant number of rounds of
[Goldwasser and Sipser][GoldwasserSipser1986], in the form of `IP[k]` in
[Arora and Barak, Definition 8.6][AroraBarak09]. A move is `IPMove.verifier` (the verifier sends a
message computed from its private coins) or `IPMove.prover` (the prover sends a message). A shape
`List (IPMove × ℕ)` lists the moves with their lengths, and a polynomial shape evaluates to a
shape at the length `n` of the encoded instance (`Cslib.Complexity.IPGame.evalShape`).

The verifier is deterministic given its coins: a pair of polynomial-time functions, the message
`msg (a, c, j, p)` at its move number `j` after the transcript `p` with coins `c`, and the
decision `dec (a, c, t)` on the whole transcript `t`. The coins are `ρ(n)` bits and the prover
never sees them. A message is read as a string of the length of its move
(`Cslib.BitString.ofList`), so every verifier respects the shape.

The value of a game is counted exactly, as for public-coin games
(`Cslib.Complexity.AMGame.count`). `Cslib.Complexity.IPGame.count` sums over the verifier's
messages and takes the maximum over the prover's messages. At a complete transcript the payoff
`Cslib.Complexity.IPGame.acceptedCoins` counts the coins that agree with every verifier message of
the transcript (`Cslib.Complexity.IPGame.agrees`) and accept it. The resulting
`Cslib.Complexity.IPGame.bestCount` is the number of coins accepted against an optimal prover:
every deterministic prover `P`, which sees the move number and the transcript so far, is accepted
on at most `bestCount` coin strings (`Cslib.Complexity.IPGame.card_filter_run_le_bestCount`), and
some prover attains it (`Cslib.Complexity.IPGame.exists_card_filter_run_eq_bestCount`). So the
count agrees with the definition of `IP[k]` by acceptance probabilities against all provers
(`Cslib.Complexity.isIPGameVerifier_iff_provers`). Randomized provers do no better than the best
deterministic one, so they are not modelled.

A problem `A` is in `IPGameClass enc π` when some polynomial shape with move pattern `π`, some
polynomial `ρ` and some polynomial-time verifier accept at least two thirds of the coin strings on
members against an optimal prover, and at most one third on non-members. `IPk enc k` is the
alternating pattern of `k` moves, the verifier first. A public-coin verifier is a private-coin
verifier that sends its coins as its messages, so `AMGameClass π ⊆ IPGameClass π` and
`AM[k] ⊆ IP[k]`.

The bookkeeping of shapes shared by the later constructions is here too: how
`Cslib.Complexity.IPGame.evalShape`, `Cslib.Complexity.IPGame.verifierBits`,
`Cslib.Complexity.IPGame.verifierMoves` and `Cslib.Complexity.IPGame.count` behave on
concatenations, and the bound `Cslib.Complexity.IPGame.count_le_two_pow` of a count of a
`0`/`1`-valued payoff.

## Main definitions

* `Cslib.Complexity.IPMove`, `Cslib.Complexity.IPGame.count`, `Cslib.Complexity.IPGame.agrees`,
  `Cslib.Complexity.IPGame.run`, `Cslib.Complexity.IPGame.acceptedCoins`,
  `Cslib.Complexity.IPGame.bestCount`, `Cslib.Complexity.IPGame.countAt`,
  `Cslib.Complexity.IPGame.verifierMoves`.
* `Cslib.Complexity.IsIPGameVerifier`, `Cslib.Complexity.IPGameClass`, `Cslib.Complexity.IPk`:
  `IP[k]`.

## Main results

* `Cslib.Complexity.IPGame.card_filter_run_le_bestCount`,
  `Cslib.Complexity.IPGame.exists_card_filter_run_eq_bestCount`: the count is the maximum over
  deterministic provers.
* `Cslib.Complexity.isIPGameVerifier_iff_provers`: the class in terms of provers.
* `Cslib.Complexity.AMGameClass_subset_IPGameClass`, `Cslib.Complexity.AMk_subset_IPk`: public
  coins are private coins.

Parallel repetition is in `CslibFrontier.Computability.Complexity.Classes.IP.Games.Repetition`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- A move of a private-coin interactive game. -/
inductive IPMove where
  /-- The verifier sends a message computed from its private coins. -/
  | verifier
  /-- The prover sends a message. -/
  | prover
  deriving DecidableEq, Repr

/-- The public-coin move with the same speaker: the verifier is Arthur, the prover is Merlin. -/
def IPMove.toAM : IPMove → AMMove
  | .verifier => .arthur
  | .prover => .merlin

/-- The public-coin move pattern with the same speakers. -/
def AMMove.toIP : AMMove → IPMove
  | .arthur => .verifier
  | .merlin => .prover

@[simp] theorem IPMove.toAM_toIP (x : AMMove) : (x.toIP).toAM = x := by cases x <;> rfl

@[simp] theorem AMMove.toIP_toAM (x : IPMove) : (x.toAM).toIP = x := by cases x <;> rfl

namespace IPGame

/-- The count of a private-coin game shape `g` on a payoff `f`: a sum over the verifier's messages
and a maximum over the prover's messages, with `f` evaluated on the complete transcript. -/
def count : List (IPMove × ℕ) → (List Bool → ℕ) → ℕ
  | [], f => f []
  | (.verifier, n) :: g, f => ∑ m : Fin n → Bool, count g fun t => f (List.ofFn m ++ t)
  | (.prover, n) :: g, f => univ.sup fun y : Fin n → Bool => count g fun t => f (List.ofFn y ++ t)

theorem count_nil (f : List Bool → ℕ) : count [] f = f [] := rfl

theorem count_verifier (n : ℕ) (g : List (IPMove × ℕ)) (f : List Bool → ℕ) :
    count ((.verifier, n) :: g) f = ∑ m : Fin n → Bool, count g fun t => f (List.ofFn m ++ t) :=
  rfl

theorem count_prover (n : ℕ) (g : List (IPMove × ℕ)) (f : List Bool → ℕ) :
    count ((.prover, n) :: g) f =
      univ.sup fun y : Fin n → Bool => count g fun t => f (List.ofFn y ++ t) :=
  rfl

/-- Total length of a transcript of a game. -/
def transcriptLength (g : List (IPMove × ℕ)) : ℕ := (g.map Prod.snd).sum

theorem count_mono_of_length (g : List (IPMove × ℕ)) {f f' : List Bool → ℕ}
    (h : ∀ t : List Bool, t.length = transcriptLength g → f t ≤ f' t) : count g f ≤ count g f' := by
  induction g generalizing f f' with
  | nil => exact h [] rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · refine sum_le_sum fun m _ => ih fun t ht => h _ ?_
      simp only [transcriptLength, List.map_cons, List.sum_cons, List.length_append,
        List.length_ofFn] at ht ⊢
      omega
    · refine Finset.sup_mono_fun fun y _ => ih fun t ht => h _ ?_
      simp only [transcriptLength, List.map_cons, List.sum_cons, List.length_append,
        List.length_ofFn] at ht ⊢
      omega

theorem count_congr_of_length (g : List (IPMove × ℕ)) {f f' : List Bool → ℕ}
    (h : ∀ t : List Bool, t.length = transcriptLength g → f t = f' t) : count g f = count g f' :=
  le_antisymm (count_mono_of_length g fun t ht => (h t ht).le)
    (count_mono_of_length g fun t ht => (h t ht).ge)

/-- The public-coin shape with the same moves. -/
def toAM (g : List (IPMove × ℕ)) : List (AMMove × ℕ) := g.map fun x => (x.1.toAM, x.2)

/-- The number of bits the verifier sends in a game shape. -/
def verifierBits (g : List (IPMove × ℕ)) : ℕ := AMGame.arthurBits (toAM g)

@[simp] theorem toAM_nil : toAM [] = [] := rfl

@[simp] theorem toAM_cons (x : IPMove × ℕ) (g : List (IPMove × ℕ)) :
    toAM (x :: g) = (x.1.toAM, x.2) :: toAM g := rfl

theorem toAM_append (g h : List (IPMove × ℕ)) : toAM (g ++ h) = toAM g ++ toAM h := by
  simp [toAM]

theorem verifierBits_verifier (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierBits ((.verifier, n) :: g) = n + verifierBits g := rfl

theorem verifierBits_prover (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierBits ((.prover, n) :: g) = verifierBits g := rfl

theorem verifierBits_append (g h : List (IPMove × ℕ)) :
    verifierBits (g ++ h) = verifierBits g + verifierBits h := by
  induction g with
  | nil => simp [verifierBits, AMGame.arthurBits]
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · rw [List.cons_append, verifierBits_verifier, verifierBits_verifier, ih, Nat.add_assoc]
    · rw [List.cons_append, verifierBits_prover, verifierBits_prover, ih]

/-- The number of verifier moves of a private-coin game shape. -/
def verifierMoves (g : List (IPMove × ℕ)) : ℕ := (g.map Prod.fst).count .verifier

@[simp] theorem verifierMoves_nil : verifierMoves [] = 0 := rfl

@[simp] theorem verifierMoves_verifier (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierMoves ((.verifier, n) :: g) = verifierMoves g + 1 := by
  simp [verifierMoves]

@[simp] theorem verifierMoves_prover (n : ℕ) (g : List (IPMove × ℕ)) :
    verifierMoves ((.prover, n) :: g) = verifierMoves g := by
  simp [verifierMoves]

/-- The count of a private-coin game is `2 ^ B` times the value of the public-coin game with the
same moves, where `B` is the number of bits the verifier sends. -/
theorem count_eq_value (g : List (IPMove × ℕ)) (f : List Bool → ℕ) :
    (count g f : ℚ) = 2 ^ verifierBits g * AMGame.value true (toAM g) fun t => (f t : ℚ) := by
  induction g generalizing f with
  | nil => simp [count, verifierBits, AMGame.arthurBits, AMGame.value_nil]
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · rw [count, verifierBits_verifier, toAM_cons]
      change _ = _ * AMGame.value true ((.arthur, n) :: toAM g) _
      rw [AMGame.value_arthur, Nat.cast_sum]
      simp only [ih]
      rw [← mul_sum, pow_add]
      field_simp
    · rw [count, verifierBits_prover, toAM_cons]
      change _ = _ * AMGame.value true ((.merlin, n) :: toAM g) _
      rw [AMGame.value_merlin_true, ← sup'_eq_sup univ_nonempty]
      rw [Finset.apply_sup'_eq_sup'_comp univ_nonempty (Nat.cast : ℕ → ℚ)
        fun x y => Nat.cast_max x y]
      rw [Finset.apply_sup'_eq_sup'_comp univ_nonempty (fun x : ℚ => 2 ^ verifierBits g * x)
        fun x y => mul_max_of_nonneg x y (by positivity)]
      exact sup'_congr univ_nonempty rfl fun y _ => ih _

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

/-! ### Verifiers with private coins -/

variable {C : Type}

/-- Whether the transcript `t` of the moves `g` agrees with the messages of the verifier `msg`,
where `j` moves with transcript `p` came before. Before the verifier's move number `j` it sends
`msg j p`, read as a string of the length of the move. -/
def agrees (msg : ℕ → List Bool → List Bool) : List (IPMove × ℕ) → ℕ → List Bool → List Bool → Bool
  | [], _, _, _ => true
  | (.verifier, n) :: g, j, p, t =>
    decide (t.take n = List.ofFn (BitString.ofList n (msg j p))) &&
      agrees msg g (j + 1) (p ++ t.take n) (t.drop n)
  | (.prover, n) :: g, j, p, t => agrees msg g (j + 1) (p ++ t.take n) (t.drop n)

/-- The run of a deterministic prover `P` against the verifier `msg`, from move `j` after the
transcript `p`. The prover sees the move number and the transcript so far. -/
def run (msg : ℕ → List Bool → List Bool) (P : ℕ → List Bool → List Bool) :
    List (IPMove × ℕ) → ℕ → List Bool → List Bool
  | [], _, _ => []
  | (.verifier, n) :: g, j, p =>
    List.ofFn (BitString.ofList n (msg j p)) ++
      run msg P g (j + 1) (p ++ List.ofFn (BitString.ofList n (msg j p)))
  | (.prover, n) :: g, j, p =>
    List.ofFn (BitString.ofList n (P j p)) ++
      run msg P g (j + 1) (p ++ List.ofFn (BitString.ofList n (P j p)))

/-- `agrees` on a transcript that starts with the message of a verifier move. -/
theorem agrees_verifier_ofFn (msg : ℕ → List Bool → List Bool) (n : ℕ)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (m : Fin n → Bool) (t : List Bool) :
    agrees msg ((.verifier, n) :: g) j p (List.ofFn m ++ t) =
      (decide (m = BitString.ofList n (msg j p)) &&
        agrees msg g (j + 1) (p ++ List.ofFn m) t) := by
  simp only [agrees, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  congr 1
  exact Bool.eq_iff_iff.2 (by simp only [decide_eq_true_eq]; exact List.ofFn_inj)

/-- `agrees` on a transcript that starts with the message of a prover move. -/
theorem agrees_prover_ofFn (msg : ℕ → List Bool → List Bool) (n : ℕ)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (y : Fin n → Bool) (t : List Bool) :
    agrees msg ((.prover, n) :: g) j p (List.ofFn y ++ t) =
      agrees msg g (j + 1) (p ++ List.ofFn y) t := by
  simp only [agrees, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]

/-- The run depends only on the prover's answers from move `j` on, after extensions of `p`. -/
theorem run_congr (msg : ℕ → List Bool → List Bool) {P P' : ℕ → List Bool → List Bool}
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool)
    (h : ∀ i q, j ≤ i → p.IsPrefix q → P i q = P' i q) :
    run msg P g j p = run msg P' g j p := by
  induction g generalizing j p with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [run]
      rw [ih (j + 1) _ fun i q hi hq => h i q (by omega) ((List.prefix_append _ _).trans hq)]
    · simp only [run]
      rw [h j p le_rfl List.prefix_rfl]
      rw [ih (j + 1) _ fun i q hi hq => h i q (by omega) ((List.prefix_append _ _).trans hq)]

/-- Splitting a count of coins by the first message of the verifier. -/
private theorem card_filter_verifier (msg : C → ℕ → List Bool → List Bool) (n : ℕ) (j : ℕ)
    (p : List Bool) (S : Finset C) (F : C → List Bool → Bool) :
    #(S.filter fun c => F c (List.ofFn (BitString.ofList n (msg c j p))) = true) =
      ∑ m : Fin n → Bool, #((S.filter fun c => BitString.ofList n (msg c j p) = m).filter
        fun c => F c (List.ofFn m) = true) := by
  rw [card_eq_sum_card_fiberwise (f := fun c => BitString.ofList n (msg c j p))
    (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun m _ => ?_
  rw [filter_filter, filter_filter]
  congr 1
  exact filter_congr fun c _ => ⟨fun ⟨h1, h2⟩ => ⟨h2, h2 ▸ h1⟩, fun ⟨h1, h2⟩ => ⟨h1 ▸ h2, h1⟩⟩

/-- The count of the coins agreeing with a transcript that starts with a verifier message `m`. -/
private theorem card_filter_agrees_verifier (msg : C → ℕ → List Bool → List Bool) (n : ℕ)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (S : Finset C) (D : C → List Bool → Bool)
    (m : Fin n → Bool) (t : List Bool) :
    #(S.filter fun c => (agrees (msg c) ((.verifier, n) :: g) j p (List.ofFn m ++ t) &&
        D c (List.ofFn m ++ t)) = true) =
      #((S.filter fun c => BitString.ofList n (msg c j p) = m).filter fun c =>
        (agrees (msg c) g (j + 1) (p ++ List.ofFn m) t && D c (List.ofFn m ++ t)) = true) := by
  rw [filter_filter]
  congr 1
  refine filter_congr fun c _ => ?_
  rw [agrees_verifier_ofFn]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1.symm, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1.symm, h2⟩, h3⟩⟩

/-- The count of the coins agreeing with a transcript that starts with a prover message `y`. -/
private theorem card_filter_agrees_prover (msg : C → ℕ → List Bool → List Bool) (n : ℕ)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (S : Finset C) (D : C → List Bool → Bool)
    (y : Fin n → Bool) (t : List Bool) :
    #(S.filter fun c => (agrees (msg c) ((.prover, n) :: g) j p (List.ofFn y ++ t) &&
        D c (List.ofFn y ++ t)) = true) =
      #(S.filter fun c =>
        (agrees (msg c) g (j + 1) (p ++ List.ofFn y) t && D c (List.ofFn y ++ t)) = true) := by
  congr 1
  exact filter_congr fun c _ => by rw [agrees_prover_ofFn]

/-- **The count bounds every prover**, from move `j` after the transcript `p`, for the coins in
`S`. The coins in `S` are those consistent with `p`, and `D c t` is the decision on the rest `t`
of the transcript. -/
theorem card_filter_run_le (msg : C → ℕ → List Bool → List Bool) (P : ℕ → List Bool → List Bool)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (S : Finset C) (D : C → List Bool → Bool) :
    #(S.filter fun c => D c (run (msg c) P g j p) = true) ≤
      count g fun t => #(S.filter fun c => (agrees (msg c) g j p t && D c t) = true) := by
  induction g generalizing j p S D with
  | nil => exact le_rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · have hL : #(S.filter fun c => D c (run (msg c) P ((.verifier, n) :: g) j p) = true) =
          #(S.filter fun c => (fun c u => D c (u ++ run (msg c) P g (j + 1) (p ++ u))) c
            (List.ofFn (BitString.ofList n (msg c j p))) = true) := rfl
      rw [hL, card_filter_verifier msg n j p S
        (fun c u => D c (u ++ run (msg c) P g (j + 1) (p ++ u))), count_verifier]
      refine sum_le_sum fun m _ => ?_
      refine (ih (j + 1) (p ++ List.ofFn m) _ (fun c t => D c (List.ofFn m ++ t))).trans ?_
      exact le_of_eq (count_congr_of_length g fun t _ =>
        (card_filter_agrees_verifier msg n g j p S D m t).symm)
    · set y := BitString.ofList n (P j p)
      have hL : #(S.filter fun c => D c (run (msg c) P ((.prover, n) :: g) j p) = true) =
          #(S.filter fun c => (fun c t => D c (List.ofFn y ++ t)) c
            (run (msg c) P g (j + 1) (p ++ List.ofFn y)) = true) := rfl
      rw [hL]
      refine (ih (j + 1) (p ++ List.ofFn y) S (fun c t => D c (List.ofFn y ++ t))).trans ?_
      rw [count_prover]
      refine le_trans (le_of_eq (count_congr_of_length g fun t _ =>
        (card_filter_agrees_prover msg n g j p S D y t).symm)) ?_
      exact le_sup (f := fun y : Fin n → Bool => count g fun t =>
        #(S.filter fun c => (agrees (msg c) ((.prover, n) :: g) j p (List.ofFn y ++ t) &&
          D c (List.ofFn y ++ t)) = true)) (mem_univ y)

/-- **Some prover attains the count**, from move `j` after the transcript `p`, for the coins in
`S`. -/
theorem exists_card_filter_run_eq (msg : C → ℕ → List Bool → List Bool)
    (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (S : Finset C) (D : C → List Bool → Bool) :
    ∃ P : ℕ → List Bool → List Bool, #(S.filter fun c => D c (run (msg c) P g j p) = true) =
      count g fun t => #(S.filter fun c => (agrees (msg c) g j p t && D c t) = true) := by
  induction g generalizing j p S D with
  | nil => exact ⟨fun _ _ => [], rfl⟩
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · choose P hP using fun m : Fin n → Bool =>
        ih (j + 1) (p ++ List.ofFn m) (S.filter fun c => BitString.ofList n (msg c j p) = m)
          (fun c t => D c (List.ofFn m ++ t))
      set Q : ℕ → List Bool → List Bool := fun i q => P (BitString.ofList n (q.drop p.length)) i q
      refine ⟨Q, ?_⟩
      have hL : #(S.filter fun c => D c (run (msg c) Q ((.verifier, n) :: g) j p) = true) =
          #(S.filter fun c => (fun c u => D c (u ++ run (msg c) Q g (j + 1) (p ++ u))) c
            (List.ofFn (BitString.ofList n (msg c j p))) = true) := rfl
      rw [hL, card_filter_verifier msg n j p S
        (fun c u => D c (u ++ run (msg c) Q g (j + 1) (p ++ u))), count_verifier]
      refine sum_congr rfl fun m _ => ?_
      have hrun (c : C) : run (msg c) Q g (j + 1) (p ++ List.ofFn m) =
          run (msg c) (P m) g (j + 1) (p ++ List.ofFn m) := by
        refine run_congr _ g (j + 1) _ fun i q _ hq => ?_
        obtain ⟨s, rfl⟩ := hq
        simp only [Q, List.append_assoc, List.drop_left, BitString.ofList_ofFn_append]
      simp only [hrun]
      rw [hP m]
      exact count_congr_of_length g fun t _ =>
        (card_filter_agrees_verifier msg n g j p S D m t).symm
    · set φ : (Fin n → Bool) → ℕ := fun y => count g fun t =>
        #(S.filter fun c => (agrees (msg c) g (j + 1) (p ++ List.ofFn y) t &&
          D c (List.ofFn y ++ t)) = true)
      obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty φ
      obtain ⟨P, hP⟩ := ih (j + 1) (p ++ List.ofFn y) S (fun c t => D c (List.ofFn y ++ t))
      set Q : ℕ → List Bool → List Bool := fun i q => if i = j then List.ofFn y else P i q
      refine ⟨Q, ?_⟩
      have hQ : BitString.ofList n (Q j p) = y := by simp [Q]
      have hrun (c : C) : run (msg c) Q g (j + 1) (p ++ List.ofFn y) =
          run (msg c) P g (j + 1) (p ++ List.ofFn y) :=
        run_congr _ g (j + 1) _ fun i q hi _ => ite_eq_right (by omega)
      have hL : #(S.filter fun c => D c (run (msg c) Q ((.prover, n) :: g) j p) = true) =
          #(S.filter fun c => (fun c t => D c (List.ofFn y ++ t)) c
            (run (msg c) P g (j + 1) (p ++ List.ofFn y)) = true) := by
        simp only [run, hQ, hrun]
      rw [hL, hP, count_prover]
      change φ y = _
      rw [← hy]
      congr 1 with y' : 1
      exact count_congr_of_length g fun t _ =>
        (card_filter_agrees_prover msg n g j p S D y' t).symm


/-! ### Accepted coins -/

/-- The coins that agree with the transcript `t` of the moves `g` and accept it. -/
def acceptedCoins {ρ : ℕ} (msg : BitString ρ → ℕ → List Bool → List Bool)
    (dec : BitString ρ → List Bool → Bool) (g : List (IPMove × ℕ)) (t : List Bool) : ℕ :=
  #(univ.filter fun c => (agrees (msg c) g 0 [] t && dec c t) = true)

/-- The number of coins accepted against an optimal prover. -/
def bestCount {ρ : ℕ} (msg : BitString ρ → ℕ → List Bool → List Bool)
    (dec : BitString ρ → List Bool → Bool) (g : List (IPMove × ℕ)) : ℕ :=
  count g (acceptedCoins msg dec g)

/-- **The count bounds every prover**: against every deterministic prover `P`, at most
`bestCount msg dec g` coins accept. -/
theorem card_filter_run_le_bestCount {ρ : ℕ} (msg : BitString ρ → ℕ → List Bool → List Bool)
    (dec : BitString ρ → List Bool → Bool) (g : List (IPMove × ℕ))
    (P : ℕ → List Bool → List Bool) :
    #(univ.filter fun c => dec c (run (msg c) P g 0 []) = true) ≤ bestCount msg dec g :=
  card_filter_run_le msg P g 0 [] univ dec

/-- **Some prover attains the count**: some deterministic prover makes exactly
`bestCount msg dec g` coins accept. -/
theorem exists_card_filter_run_eq_bestCount {ρ : ℕ}
    (msg : BitString ρ → ℕ → List Bool → List Bool) (dec : BitString ρ → List Bool → Bool)
    (g : List (IPMove × ℕ)) :
    ∃ P : ℕ → List Bool → List Bool,
      #(univ.filter fun c => dec c (run (msg c) P g 0 []) = true) = bestCount msg dec g :=
  exists_card_filter_run_eq msg g 0 [] univ dec

/-- Evaluate the move lengths of a polynomial game shape at `n`. -/
def evalShape (G : List (IPMove × Polynomial ℕ)) (n : ℕ) : List (IPMove × ℕ) :=
  G.map fun x => (x.1, x.2.eval n)

@[simp] theorem evalShape_nil (n : ℕ) : evalShape [] n = [] := rfl

theorem evalShape_cons (v : IPMove) (p : Polynomial ℕ) (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    evalShape ((v, p) :: G) n = (v, p.eval n) :: evalShape G n := rfl

theorem evalShape_append (G H : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (G ++ H) n = evalShape G n ++ evalShape H n := by
  simp [evalShape]

theorem verifierMoves_evalShape (G : List (IPMove × Polynomial ℕ)) (n : ℕ) :
    verifierMoves (evalShape G n) = (G.map Prod.fst).count .verifier := by
  simp [verifierMoves, evalShape, Function.comp_def]

end IPGame

open IPGame

/-- The count of a private-coin game verifier on the instance `a`: the number of coin strings of
`ρ(n)` bits that an optimal prover makes accept, where `n` is the length of the encoded instance.
The verifier sends `msg (a, c, j, p)` at its move `j` after the transcript `p`, with coins `c`,
and finally accepts the transcript `t` when `dec (a, c, t)`. -/
def IPGame.countAt (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool)
    (a : α) : ℕ :=
  bestCount (fun c j p => msg (a, List.ofFn c, j, p)) (fun c t => dec (a, List.ofFn c, t))
    (evalShape G (enc a).length) (ρ := ρ.eval (enc a).length)

/-- `(msg, dec)` is a private-coin game verifier for `A` with the polynomial shape `G` and
`ρ(n)` coins: on a member an optimal prover is accepted on at least two thirds of the coin
strings, and on a non-member on at most one third of them, whatever the prover does. -/
def IsIPGameVerifier (enc : α ↪ List Bool) (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 * 2 ^ ρ.eval (enc a).length ≤ 3 * IPGame.countAt enc G ρ msg dec a) ∧
    (a ∉ A → 3 * IPGame.countAt enc G ρ msg dec a ≤ 2 ^ ρ.eval (enc a).length)

/-- The input of a verifier's message function: the instance, the coins, the move number in unary
and the transcript so far, nested to the right. The instance is encoded with `enc`, the coins and
the transcript as raw bits. -/
abbrev IPGame.encMsgInput (enc : α ↪ List Bool) : α × List Bool × ℕ × List Bool ↪ List Bool :=
  encPair enc (encPair encBits (encPair encUnary encBits))

/-- The input of a verifier's decision: the instance, the coins and the whole transcript, nested to
the right. The instance is encoded with `enc`, the coins and the transcript as raw bits. -/
abbrev IPGame.encDecInput (enc : α ↪ List Bool) : α × List Bool × List Bool ↪ List Bool :=
  encPair enc (encPair encBits encBits)

/-- The problems with polynomial-time private-coin game verifiers whose moves follow the pattern
`π`, with polynomially many coins and polynomially long messages, with respect to the encoding
`enc` of instances [Goldwasser and Sipser][GoldwasserSipser1986]. -/
def IPGameClass (enc : α ↪ List Bool) (π : List IPMove) : Set (Set α) :=
  {A | ∃ (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool),
    G.map Prod.fst = π ∧
      ComputableInPolyTime msg (IPGame.encMsgInput enc) encBits ∧
      ComputableInPolyTime dec (IPGame.encDecInput enc) encBool ∧
      IsIPGameVerifier enc G ρ msg dec A}

/-- `IP[k]`: `k` alternating moves, the verifier first. -/
def IPk (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  IPGameClass enc ((alternatingMoves .arthur k).map AMMove.toIP)

/-- **Private-coin game verifiers in terms of provers**: on a member some deterministic prover is
accepted on at least two thirds of the coin strings, and on a non-member every deterministic
prover is accepted on at most one third of them. -/
theorem isIPGameVerifier_iff_provers {enc : α ↪ List Bool} {G : List (IPMove × Polynomial ℕ)}
    {ρ : Polynomial ℕ} {msg : α × List Bool × ℕ × List Bool → List Bool}
    {dec : α × List Bool × List Bool → Bool} {A : Set α} :
    IsIPGameVerifier enc G ρ msg dec A ↔ ∀ a,
      (a ∈ A → ∃ P : ℕ → List Bool → List Bool, 2 * 2 ^ ρ.eval (enc a).length ≤
        3 * #(univ.filter fun c : BitString (ρ.eval (enc a).length) => dec (a, List.ofFn c,
          run (fun j p => msg (a, List.ofFn c, j, p)) P (evalShape G (enc a).length) 0 []) =
            true)) ∧
      (a ∉ A → ∀ P : ℕ → List Bool → List Bool,
        3 * #(univ.filter fun c : BitString (ρ.eval (enc a).length) => dec (a, List.ofFn c,
          run (fun j p => msg (a, List.ofFn c, j, p)) P (evalShape G (enc a).length) 0 []) =
            true) ≤ 2 ^ ρ.eval (enc a).length) := by
  refine forall_congr' fun a => and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_)
  · constructor
    · intro h
      obtain ⟨P, hP⟩ := exists_card_filter_run_eq_bestCount
        (fun c j p => msg (a, List.ofFn c, j, p)) (fun c t => dec (a, List.ofFn c, t))
        (evalShape G (enc a).length)
      exact ⟨P, by rw [hP]; exact h⟩
    · rintro ⟨P, hP⟩
      exact hP.trans (Nat.mul_le_mul_left 3 (card_filter_run_le_bestCount
        (fun c j p => msg (a, List.ofFn c, j, p)) (fun c t => dec (a, List.ofFn c, t))
        (evalShape G (enc a).length) P))
  · constructor
    · intro h P
      exact (Nat.mul_le_mul_left 3 (card_filter_run_le_bestCount
        (fun c j p => msg (a, List.ofFn c, j, p)) (fun c t => dec (a, List.ofFn c, t))
        (evalShape G (enc a).length) P)).trans h
    · intro h
      obtain ⟨P, hP⟩ := exists_card_filter_run_eq_bestCount
        (fun c j p => msg (a, List.ofFn c, j, p)) (fun c t => dec (a, List.ofFn c, t))
        (evalShape G (enc a).length)
      have := h P
      rw [hP] at this
      exact this


/-! ### Public coins are private coins -/

namespace IPGame

/-- The number of bits Merlin sends in a public-coin game shape. -/
def merlinBits : List (AMMove × ℕ) → ℕ
  | [] => 0
  | (.arthur, _) :: g => merlinBits g
  | (.merlin, n) :: g => n + merlinBits g

theorem transcriptLength_eq_arthurBits_add_merlinBits (g : List (AMMove × ℕ)) :
    AMGame.transcriptLength g = AMGame.arthurBits g + merlinBits g := by
  induction g with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [AMGame.transcriptLength, List.map_cons, List.sum_cons, AMGame.arthurBits,
        merlinBits] at ih ⊢
      omega
    · simp only [AMGame.transcriptLength, List.map_cons, List.sum_cons, AMGame.arthurBits,
        merlinBits] at ih ⊢
      omega

theorem transcriptLength_toAM (g : List (IPMove × ℕ)) :
    AMGame.transcriptLength (toAM g) = transcriptLength g := by
  simp [AMGame.transcriptLength, transcriptLength, toAM, Function.comp_def]

theorem verifierBits_le_transcriptLength (g : List (IPMove × ℕ)) :
    verifierBits g ≤ transcriptLength g := by
  rw [← transcriptLength_toAM, transcriptLength_eq_arthurBits_add_merlinBits]
  exact Nat.le_add_right _ _

/-- The private-coin shape with the same moves as a public-coin shape. -/
def ofAM (g : List (AMMove × ℕ)) : List (IPMove × ℕ) := g.map fun x => (x.1.toIP, x.2)

@[simp] theorem ofAM_nil : ofAM [] = [] := rfl

@[simp] theorem ofAM_cons (x : AMMove × ℕ) (g : List (AMMove × ℕ)) :
    ofAM (x :: g) = (x.1.toIP, x.2) :: ofAM g := rfl

theorem transcriptLength_ofAM (g : List (AMMove × ℕ)) :
    transcriptLength (ofAM g) = AMGame.transcriptLength g := by
  simp only [transcriptLength, AMGame.transcriptLength, ofAM, List.map_map]
  rfl

/-- Whether the coins `w` agree with Arthur's messages in the transcript `t` of `g`: at each of
Arthur's moves the next bits of `w` are Arthur's message, and at each of Merlin's moves the next
bits of `w` are skipped. -/
def matchArthur : List (AMMove × ℕ) → List Bool → List Bool → Bool
  | [], _, _ => true
  | (.arthur, n) :: g, w, t =>
    decide (t.take n = List.ofFn (BitString.ofList n w)) && matchArthur g (w.drop n) (t.drop n)
  | (.merlin, n) :: g, w, t => matchArthur g (w.drop n) (t.drop n)

/-- The verifier that sends its coins as Arthur's messages agrees with a transcript exactly when
its coins agree with Arthur's messages. The coins used so far are as many as the bits of the
transcript so far. -/
theorem agrees_reveal (g : List (AMMove × ℕ)) (j : ℕ) (p w t : List Bool)
    (ht : t.length = AMGame.transcriptLength g) :
    agrees (fun _ q => w.drop q.length) (ofAM g) j p t = matchArthur g (w.drop p.length) t := by
  induction g generalizing j p t with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · simp only [AMGame.transcriptLength, List.map_cons, List.sum_cons] at ht
      have hlen : (t.take n).length = n := List.length_take_of_le (by omega)
      simp only [ofAM_cons, AMMove.toIP, agrees, matchArthur]
      rw [ih (j + 1) (p ++ t.take n) (t.drop n) (by simp [AMGame.transcriptLength]; omega),
        List.length_append, hlen, List.drop_drop]
    · simp only [AMGame.transcriptLength, List.map_cons, List.sum_cons] at ht
      have hlen : (t.take n).length = n := List.length_take_of_le (by omega)
      simp only [ofAM_cons, AMMove.toIP, agrees, matchArthur]
      rw [ih (j + 1) (p ++ t.take n) (t.drop n) (by simp [AMGame.transcriptLength]; omega),
        List.length_append, hlen, List.drop_drop]

/-- Exactly `2 ^ merlinBits g` coin strings agree with Arthur's messages in a transcript: Arthur's
bits are determined, Merlin's are free. -/
theorem card_filter_matchArthur (g : List (AMMove × ℕ)) (t : List Bool)
    (ht : t.length = AMGame.transcriptLength g) :
    #(univ.filter fun w : BitString (AMGame.transcriptLength g) =>
      matchArthur g (List.ofFn w) t = true) = 2 ^ merlinBits g := by
  induction g generalizing t with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · have ht' : t.length = n + AMGame.transcriptLength g := ht
      have hlen : (t.take n).length = n := List.length_take_of_le (by omega)
      change #(univ.filter fun w : Fin (n + AMGame.transcriptLength g) → Bool =>
        matchArthur ((.arthur, n) :: g) (List.ofFn w) t = true) = 2 ^ merlinBits g
      have key := BitString.card_filter_ofFn_add n (AMGame.transcriptLength g) fun u v =>
        (decide (t.take n = List.ofFn (BitString.ofList n u)) &&
          matchArthur g v (t.drop n)) = true
      have hw (w : Fin (n + AMGame.transcriptLength g) → Bool) :
          matchArthur ((.arthur, n) :: g) (List.ofFn w) t =
            (decide (t.take n = List.ofFn (BitString.ofList n ((List.ofFn w).take n))) &&
              matchArthur g ((List.ofFn w).drop n) (t.drop n)) := by
        simp only [matchArthur, BitString.ofList_take]
      simp only [hw]
      rw [key]
      simp only [BitString.ofList_ofFn]
      rw [Finset.sum_eq_single (BitString.ofList n (t.take n))]
      · rw [BitString.ofFn_ofList hlen]
        simp only [decide_true, Bool.true_and]
        exact ih (t.drop n) (by rw [List.length_drop]; omega)
      · intro u _ hu
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun v _ => ?_)
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h
        exact absurd (by rw [h, BitString.ofList_ofFn]) hu
      · exact fun h => absurd (mem_univ _) h
    · change #(univ.filter fun w : Fin (n + AMGame.transcriptLength g) → Bool =>
        matchArthur ((.merlin, n) :: g) (List.ofFn w) t = true) = 2 ^ (n + merlinBits g)
      have ht' : t.length = n + AMGame.transcriptLength g := ht
      have key := BitString.card_filter_ofFn_add n (AMGame.transcriptLength g) fun _ v =>
        matchArthur g v (t.drop n) = true
      have hw (w : Fin (n + AMGame.transcriptLength g) → Bool) :
          matchArthur ((.merlin, n) :: g) (List.ofFn w) t =
            matchArthur g ((List.ofFn w).drop n) (t.drop n) := rfl
      simp only [hw]
      rw [key]
      simp only [ih (t.drop n) (by rw [List.length_drop]; omega), sum_const, card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul, pow_add]

/-- The coins accepting a transcript of the verifier that sends its coins as Arthur's messages
and then runs the public-coin verifier `V`. -/
theorem acceptedCoins_reveal (g : List (AMMove × ℕ)) (V : List Bool → Bool) {K : ℕ}
    (hK : K = AMGame.transcriptLength g) (t : List Bool)
    (ht : t.length = AMGame.transcriptLength g) :
    acceptedCoins (ρ := K) (fun c _ q => (List.ofFn c).drop q.length) (fun _ t => V t) (ofAM g)
      t = 2 ^ merlinBits g * (V t).toNat := by
  subst hK
  unfold acceptedCoins
  simp only [agrees_reveal g 0 [] _ t ht, List.length_nil, List.drop_zero]
  cases V t
  · simp
  · simp only [Bool.and_true, Bool.toNat_true, mul_one]
    exact card_filter_matchArthur g t ht

private theorem count_ofAM_mul (g : List (AMMove × ℕ)) (k : ℕ) (V : List Bool → Bool) :
    count (ofAM g) (fun t => k * (V t).toNat) = k * AMGame.count g V := by
  induction g generalizing V with
  | nil => rfl
  | cons x g ih =>
    obtain ⟨_ | _, n⟩ := x
    · change (∑ m : Fin n → Bool, count (ofAM g) fun t => k * (V (List.ofFn m ++ t)).toNat) =
        k * ∑ r : Fin n → Bool, AMGame.count g fun t => V (List.ofFn r ++ t)
      simp only [ih, mul_sum]
    · change (univ.sup fun y : Fin n → Bool =>
          count (ofAM g) fun t => k * (V (List.ofFn y ++ t)).toNat) =
        k * univ.sup fun y : Fin n → Bool => AMGame.count g fun t => V (List.ofFn y ++ t)
      simp only [ih]
      rw [Finset.apply_sup_eq_sup_comp (fun x => k * x)
        (fun x y => (Nat.mul_max_mul_left k x y).symm) (by simp)]
      rfl

/-- The count of the verifier that sends its coins as Arthur's messages is `2 ^ merlinBits g`
times the count of the public-coin game. -/
theorem bestCount_reveal (g : List (AMMove × ℕ)) (V : List Bool → Bool) {K : ℕ}
    (hK : K = AMGame.transcriptLength g) :
    bestCount (ρ := K) (fun c _ q => (List.ofFn c).drop q.length) (fun _ t => V t) (ofAM g) =
      2 ^ merlinBits g * AMGame.count g V := by
  unfold bestCount
  rw [count_congr_of_length (ofAM g) fun t ht => acceptedCoins_reveal g V hK t
    (by rw [ht, transcriptLength_ofAM])]
  exact count_ofAM_mul g _ V

theorem evalShape_map_toIP (G : List (AMMove × Polynomial ℕ)) (n : ℕ) :
    evalShape (G.map fun x => (x.1.toIP, x.2)) n = ofAM (AMGame.evalShape G n) := by
  simp [evalShape, AMGame.evalShape, ofAM]

end IPGame

/-- **Public coins are private coins**: a public-coin game verifier gives a private-coin game
verifier with the same pattern of moves, which sends its coins as Arthur's messages. -/
theorem AMGameClass_subset_IPGameClass {enc : α ↪ List Bool} (π : List AMMove) :
    AMGameClass enc π ⊆ IPGameClass enc (π.map AMMove.toIP) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  refine ⟨G.map fun x => (x.1.toIP, x.2), AMGame.transcriptLengthPoly G,
    fun x => x.2.1.drop x.2.2.2.length, fun x => V (x.1, x.2.2), ?_, ?_, ?_, fun a => ?_⟩
  · simp [← hG]
  · fun_prop
  · fun_prop
  · set n := (enc a).length
    have hK := (AMGame.transcriptLength_evalShape G n).symm
    have hcount : IPGame.countAt enc (G.map fun x => (x.1.toIP, x.2))
        (AMGame.transcriptLengthPoly G) (fun x => x.2.1.drop x.2.2.2.length)
        (fun x => V (x.1, x.2.2)) a = 2 ^ merlinBits (AMGame.evalShape G n) *
          AMGame.count (AMGame.evalShape G n) fun t => V (a, t) := by
      unfold IPGame.countAt
      rw [evalShape_map_toIP]
      exact bestCount_reveal _ (fun t => V (a, t)) hK
    rw [hcount, hK, transcriptLength_eq_arthurBits_add_merlinBits, pow_add]
    obtain ⟨h1, h2⟩ := hA a
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · have := Nat.mul_le_mul_right (2 ^ merlinBits (AMGame.evalShape G n)) (h1 ha)
      linarith
    · have := Nat.mul_le_mul_right (2 ^ merlinBits (AMGame.evalShape G n)) (h2 ha)
      linarith

/-- **`AM[k] ⊆ IP[k]`**. -/
theorem AMk_subset_IPk {enc : α ↪ List Bool} (k : ℕ) : AMk enc k ⊆ IPk enc k :=
  AMGameClass_subset_IPGameClass _

end Cslib.Complexity
