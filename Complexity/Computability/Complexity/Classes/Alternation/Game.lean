/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.Game
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Alternating polynomial time as a game of moves

An alternating machine running within `t` steps plays a game of `t` moves, each chosen by the
player that the state labels. Through the strict table (`Turing.MultiTapeATM.strict`, in
`Complexity.Computability.Machines.Turing.MultiTape.Alternating.Game`), which spends two coins on
each step of the machine, acceptance within `t` moves when every branch halts within `t` steps is
the game of `2 * t` single-bit moves, alternately chosen by an existential and a universal player,
in which the existential player wins when the strict table, replayed from the moves, emits `[true]`
(`Turing.MultiTapeATM.acceptsWithin_iff_alternation`). The moves are the blocks of length `1` of the
alternating quantifiers `Cslib.Complexity.Alternation` of the polynomial hierarchy.

Since replaying the strict table of a fixed finite machine is polynomial-time
(`Turing.MultiTapeATM.computableInPolyTime_gameVerifier`), every problem in `AP` has a
polynomial-time game verifier (`Cslib.Complexity.IsGameVerifier`): a polynomial-time `V` and a
polynomial `p` such that `a ∈ A` exactly when the existential player wins the game of
`2 * p (enc a).length` moves with `V (a, ·)` as the winning condition
(`Cslib.Complexity.exists_isGameVerifier_of_mem_AP`). Conversely, the guess-then-verify machine
plays the game of a polynomial-time game verifier
(`Cslib.Complexity.IsGameVerifier.mem_AP`, in
`Complexity.Computability.Complexity.Classes.Alternation.GuessVerify`).

## Main definitions

* `Cslib.Complexity.IsGameVerifier`: a verifier of a game of polynomially many moves.

## Main results

* `Cslib.Complexity.alternation_const`, `Cslib.Complexity.alternation_congr_of_length`,
  `Cslib.Complexity.alternation_true_one_cons`, `Cslib.Complexity.alternation_false_one_cons`:
  alternating quantifiers over single-bit moves.
* `Turing.MultiTapeATM.acceptsWithin_iff_alternation`: acceptance within `n` moves is the game of
  `2 * n` moves on the strict table.
* `Turing.MultiTapeATM.DecidesInTime.isGameVerifier`: a machine deciding a problem within
  `c * ((enc a).length + 1) ^ d` steps gives a game verifier.
* `Cslib.Complexity.exists_isGameVerifier_of_mem_AP`: every problem in `AP` has a polynomial-time
  game verifier.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-! ### Single-bit moves -/

section Moves

variable {q : Bool} {ns : List ℕ} {P : List Bool → Prop}

/-- Alternating quantifiers over a predicate that ignores the strings are vacuous. -/
theorem alternation_const {p : Prop} : Alternation q ns (fun _ => p) ↔ p := by
  induction ns generalizing q with
  | nil => exact alternation_nil
  | cons n ns ih =>
    cases q
    · rw [alternation_false_cons]
      exact ⟨fun h => ih.mp (h (List.replicate n false) (List.length_replicate ..)),
        fun h _ _ => ih.mpr h⟩
    · rw [alternation_true_cons]
      exact ⟨fun ⟨_, _, h⟩ => ih.mp h, fun h => ⟨List.replicate n false, List.length_replicate ..,
        ih.mpr h⟩⟩

/-- Alternating quantifiers only apply the predicate to strings of the total length of the
blocks. -/
theorem Alternation.mono_of_length {Q : List Bool → Prop}
    (h : ∀ w, w.length = ns.sum → P w → Q w) : Alternation q ns P → Alternation q ns Q := by
  induction ns generalizing q P Q with
  | nil => simpa only [alternation_nil] using h [] rfl
  | cons n ns ih =>
    have h' (w : List Bool) (hw : w.length = n) (v : List Bool) (hv : v.length = ns.sum)
        (hP : P (w ++ v)) : Q (w ++ v) := h _ (by simp [hw, hv]) hP
    cases q
    · exact fun hP w hw => ih (h' w hw) (hP w hw)
    · exact fun ⟨w, hw, hP⟩ => ⟨w, hw, ih (h' w hw) hP⟩

/-- Alternating quantifiers over two predicates that agree on the strings of the total length of
the blocks agree. -/
theorem alternation_congr_of_length {Q : List Bool → Prop}
    (h : ∀ w, w.length = ns.sum → (P w ↔ Q w)) : Alternation q ns P ↔ Alternation q ns Q :=
  ⟨.mono_of_length fun w hw => (h w hw).1, .mono_of_length fun w hw => (h w hw).2⟩

/-- The total length of the single-bit moves. -/
theorem sum_replicate_one (n : ℕ) : (List.replicate n 1).sum = n := by
  simp

/-- An existential move of one bit. -/
theorem alternation_true_one_cons :
    Alternation true (1 :: ns) P ↔ ∃ b : Bool, Alternation false ns fun v => P (b :: v) := by
  rw [alternation_true_cons]
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hw
    exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact ⟨[b], rfl, h⟩

/-- A universal move of one bit. -/
theorem alternation_false_one_cons :
    Alternation false (1 :: ns) P ↔ ∀ b : Bool, Alternation true ns fun v => P (b :: v) := by
  rw [alternation_false_cons]
  constructor
  · exact fun h b => h [b] rfl
  · intro h w hw
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hw
    exact h b

/-- One round of the game: an existential move, then a universal move. -/
theorem alternation_replicate_succ {n : ℕ} :
    Alternation true (List.replicate (2 * (n + 1)) 1) P ↔
      ∃ x : Bool, ∀ y : Bool, Alternation true (List.replicate (2 * n) 1)
        fun v => P (x :: y :: v) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.replicate_succ, alternation_true_one_cons]
  simp only [List.replicate_succ, alternation_false_one_cons]

end Moves

end Cslib.Complexity

namespace Turing.MultiTapeATM

open Cslib.Complexity Strict

variable {k : ℕ} {State : Type}

/-- **Acceptance as a game of moves.** If every list of `n` moves from `c` reaches a halted
configuration, `c` accepts within `n` moves exactly when the existential player wins the game of
`2 * n` alternate single-bit moves, the existential first, in which the strict table replayed from
the moves ends with output `[true]`. -/
theorem acceptsWithin_iff_alternation (atm : MultiTapeATM k Bool State) {input : List Bool}
    {n : ℕ} {c : Cfg k Bool State input}
    (hn : ∀ coins : List Bool, coins.length = n → (atm.toPTM.stepCoins coins c).state = none) :
    atm.AcceptsWithin n c ↔ Alternation true (List.replicate (2 * n) 1)
      fun w => (atm.strict.stepCoins w (cfg c none)).output = [true] := by
  induction n generalizing c with
  | zero =>
    have hhalt : c.state = none := hn [] rfl
    simp [AcceptsWithin, hhalt, cfg]
  | succ n ih =>
    rcases hs : c.state with _ | q
    · rw [atm.acceptsWithin_of_halted hs]
      simp only [stepCoins_cfg_of_halted atm hs]
      rw [alternation_const]
      simp [cfg]
    · have hn' (b : Bool) : ∀ coins : List Bool, coins.length = n →
          (atm.toPTM.stepCoins coins (atm.next b c)).state = none :=
        fun coins hlen => hn (b :: coins) (by simp [hlen])
      rw [alternation_replicate_succ]
      simp only [stepCoins_cfg atm hs]
      cases hq : atm.universal q
      · rw [atm.acceptsWithin_succ_of_existential hs hq]
        simp only [Bool.false_eq_true, ↓reduceIte, ← ih (hn' _)]
        exact ⟨fun ⟨b, h⟩ => ⟨b, fun _ => h⟩, fun ⟨b, h⟩ => ⟨b, h false⟩⟩
      · rw [atm.acceptsWithin_succ_of_universal hs hq]
        simp only [↓reduceIte, ← ih (hn' _)]
        exact ⟨fun h => ⟨false, h⟩, fun ⟨_, h⟩ => h⟩

/-- **A machine under a time bound plays a game of moves** on its input: if every computation
path of at least `t` steps ends halted, the machine accepts exactly when the existential player
wins the game of `2 * t` alternate moves in which the strict table, replayed from the moves on the
input, emits `[true]`. -/
theorem accepts_iff_alternation (atm : MultiTapeATM k Bool State) {input : List Bool} {t : ℕ}
    (ht : atm.toPTM.toNTM.RunsInTime input t) :
    atm.Accepts input ↔ Alternation true (List.replicate (2 * t) 1)
      fun w => atm.strict.runClosedCoins w input = [true] := by
  rw [accepts_iff_acceptsWithin ht,
    acceptsWithin_iff_alternation atm fun _ hlen => state_stepCoins_eq_none ht hlen]
  refine alternation_congr fun w => ?_
  rw [MultiTapePTM.runClosedCoins, MultiTapePTM.tapes_runClosedConfigFromCoins,
    initialConfig_strict]

end Turing.MultiTapeATM

/-! ### Game verifiers -/

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- `V` verifies `A` through a game of `p (enc a).length` rounds of two single-bit moves, the first
chosen by an existential player and the second by a universal player: `a ∈ A` exactly when the
existential player wins, that is, can choose its moves so that `V (a, w) = true` for the moves `w`
whatever the universal player chooses. -/
def IsGameVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ Alternation true (List.replicate (2 * p.eval (enc a).length) 1)
    fun w => V (a, w) = true

end Cslib.Complexity

namespace Turing.MultiTapeATM

open Cslib.Complexity

variable {k : ℕ} {State : Type} {α : Type} {enc : α ↪ List Bool}

/-- **A machine deciding a problem gives a game verifier**: if `atm` decides `A` within
`c * ((enc a).length + 1) ^ d` steps, then its game verifier verifies `A` through games of
`c * ((enc a).length + 1) ^ d` rounds. -/
theorem DecidesInTime.isGameVerifier {atm : MultiTapeATM k Bool State} {A : Set α} {c d : ℕ}
    (h : atm.DecidesInTime enc A fun a => c * ((enc a).length + 1) ^ d) :
    IsGameVerifier enc (Polynomial.C c * (Polynomial.X + 1) ^ d) (atm.gameVerifier enc) A := by
  intro a
  have heval : (Polynomial.C c * (Polynomial.X + 1) ^ d : Polynomial ℕ).eval (enc a).length =
      c * ((enc a).length + 1) ^ d := by
    simp
  rw [heval, (h a).2, accepts_iff_alternation atm (h a).1]
  exact alternation_congr fun w => by simp [gameVerifier]

end Turing.MultiTapeATM

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Every problem in `AP` has a polynomial-time game verifier.** -/
theorem exists_isGameVerifier_of_mem_AP (h : A ∈ AP enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsGameVerifier enc p V A := by
  obtain ⟨t, ht, k, State, hfinite, atm, hdecides⟩ := h
  obtain ⟨c, d, hle⟩ := ht.exists_le
  exact ⟨_, atm.gameVerifier enc, atm.computableInPolyTime_gameVerifier,
    (hdecides.mono hle).isGameVerifier⟩

end Cslib.Complexity
