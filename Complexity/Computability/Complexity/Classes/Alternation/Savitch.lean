/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.GuessVerify
public import Complexity.Computability.Complexity.Classes.Alternation.TQBF
public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# `AP = PSPACE`

Savitch's midpoint recursion (`Cslib.Reachability.reach`) is a game
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]: to show that `v` is reachable from
`u` within `2 ^ (i + 1)` steps, the existential player names a midpoint `m`, the universal player
picks one of the two halves, from `u` to `m` or from `m` to `v`, and the game goes on at level `i`;
at level `0`, `v` must be `u` or one edge away. With single-bit moves
(`Cslib.Reachability.midpointGame`), a level takes `w` rounds in which the existential player
writes a midpoint of width `w` (`Cslib.Reachability.midpointMoves`; the universal player's moves
there do not matter) and one round in which the universal player picks the half. The existential
player wins the game of `2 * ((w + 1) * i)` moves exactly when the recursion holds at level `i`
(`Cslib.Reachability.alternation_midpointGame_iff`). The winning condition is a loop over the
levels (`Cslib.Reachability.midpointGame_eq_iterate`), polynomial-time in the moves.

A problem in `PSPACE` is decided by a nondeterministic machine within polynomial space, and
acceptance is Savitch's recursion on the codes of its finite views, at depth the width of the codes
(`Turing.MultiTapeNTM.savitchDecide_eq_true_iff`). The midpoint game on these codes
(`Cslib.Complexity.savitchVerifier`) is therefore a polynomial-time game verifier of the problem,
once its number of moves is padded to a polynomial in the length of the instance; moves after those
of the game do not matter (`Cslib.Complexity.alternation_append_iff`). The guess-then-verify machine
plays the game (`Cslib.Complexity.IsGameVerifier.mem_AP`), so `PSPACE ⊆ AP`
(`Cslib.Complexity.PSPACE_subset_AP`). With `AP ⊆ PSPACE` (`Cslib.Complexity.AP_subset_PSPACE`),
this is `AP = PSPACE` (`Cslib.Complexity.AP_eq_PSPACE`) [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981] [Sipser, Section 10.3][Sipser2013]
[Arora and Barak, Section 5.3][AroraBarak09]: the problems with polynomial-time game verifiers are
exactly those in `PSPACE` (`Cslib.Complexity.mem_PSPACE_iff_exists_isGameVerifier`). Like `AP` and
`PSPACE`, the statements are relative to the encoding of instances.

## Main definitions

* `Cslib.Reachability.midpointMoves`, `Cslib.Reachability.midpointGame`: Savitch's midpoint game.
* `Cslib.Reachability.midpointStep`: a level of the game.
* `Cslib.Complexity.savitchVerifier`: the midpoint game on the codes of the views of a machine.

## Main results

* `Cslib.Complexity.alternation_append_iff`: trailing moves that do not matter.
* `Cslib.Reachability.alternation_midpointGame_iff`: the midpoint game is Savitch's recursion.
* `Cslib.Complexity.computableInPolyTime_savitchVerifier`: the game is polynomial-time.
* `Cslib.Complexity.exists_isGameVerifier_of_mem_PSPACE`: every problem in `PSPACE` has a
  polynomial-time game verifier.
* `Cslib.Complexity.PSPACE_subset_AP`, `Cslib.Complexity.AP_eq_PSPACE`: `AP = PSPACE`.
* `Cslib.Complexity.mem_PSPACE_iff_exists_isGameVerifier`: `PSPACE` is the class of games of
  polynomially many moves with a polynomial-time winning condition.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-! ### Blocks of moves -/

section Blocks

variable {q : Bool} {ns ms : List ℕ} {P : List Bool → Prop}

/-- **Trailing moves that do not matter.** If the predicate only reads the moves of the blocks
`ns`, the further blocks `ms` do not change the game. -/
theorem alternation_append_iff (h : ∀ z, P z ↔ P (z.take ns.sum)) :
    Alternation q (ns ++ ms) P ↔ Alternation q ns P := by
  induction ns generalizing q P with
  | nil =>
    simp only [List.sum_nil, List.take_zero] at h
    rw [List.nil_append, alternation_congr h, alternation_const, alternation_nil]
  | cons n ns ih =>
    have h' (w : List Bool) (hw : w.length = n) (v : List Bool) :
        P (w ++ v) ↔ P (w ++ v.take ns.sum) := by
      rw [h (w ++ v), List.sum_cons, List.take_append, hw, List.take_of_length_le (by omega),
        Nat.add_sub_cancel_left]
    cases q
    · rw [List.cons_append, alternation_false_cons, alternation_false_cons]
      exact forall_congr' fun w => imp_congr_right fun hw => ih fun v => h' w hw v
    · rw [List.cons_append, alternation_true_cons, alternation_true_cons]
      exact exists_congr fun w => and_congr_right fun hw => ih fun v => h' w hw v

end Blocks

end Cslib.Complexity

namespace Cslib.Reachability

open Cslib.Complexity

/-! ### The midpoint game -/

/-- The midpoint chosen at a level of the game: the moves of the existential player in its first
`w` rounds. -/
def midpointMoves (w : ℕ) (z : List Bool) : List Bool :=
  (List.range w).map fun j => z.getD (2 * j) false

/-- A midpoint has width `w`. -/
private theorem length_midpointMoves (w : ℕ) (z : List Bool) : (midpointMoves w z).length = w := by
  simp [midpointMoves]

/-- The first round of a level writes the first bit of the midpoint. -/
private theorem midpointMoves_cons_cons (w : ℕ) (x y : Bool) (z : List Bool) :
    midpointMoves (w + 1) (x :: y :: z) = x :: midpointMoves w z := by
  simp [midpointMoves, List.range_succ_eq_map, Nat.mul_succ]

/-- The midpoint only reads the first `2 * w` moves. -/
private theorem midpointMoves_take {w n : ℕ} (hn : 2 * w ≤ n) (z : List Bool) :
    midpointMoves w (z.take n) = midpointMoves w z := by
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega)]

/-- **Savitch's midpoint game** on words of width `w`, at level `i`, between `u` and `v`. At level
`0` the existential player wins when `v` is `u` or one edge away. At level `i + 1`, in each of
`w` rounds the existential player chooses one bit of a midpoint `m`, and the universal player's
moves do not matter; in one more round the universal player chooses a half, and the game goes on
at level `i` between `u` and `m`, or between `m` and `v`. -/
def midpointGame (edge : List Bool → List Bool → Bool) (w : ℕ) :
    ℕ → List Bool → List Bool → List Bool → Bool
  | 0, u, v, _ => reach edge w 0 u v
  | i + 1, u, v, z =>
    if z.getD (2 * w + 1) false then
      midpointGame edge w i (midpointMoves w z) v (z.drop (2 * w + 2))
    else midpointGame edge w i u (midpointMoves w z) (z.drop (2 * w + 2))

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-- The game at level `i` reads only its first `2 * ((w + 1) * i)` moves. -/
private theorem midpointGame_take (i : ℕ) (u v z : List Bool) :
    midpointGame edge w i u v (z.take (2 * ((w + 1) * i))) = midpointGame edge w i u v z := by
  induction i generalizing u v z with
  | zero => rfl
  | succ i ih =>
    have hdrop : (z.take (2 * ((w + 1) * (i + 1)))).drop (2 * w + 2) =
        (z.drop (2 * w + 2)).take (2 * ((w + 1) * i)) := by
      rw [List.drop_take]
      congr 1
      ring_nf
      omega
    have hget : (z.take (2 * ((w + 1) * (i + 1)))).getD (2 * w + 1) false =
        z.getD (2 * w + 1) false := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_take_of_lt (by nlinarith)]
    have hmid : midpointMoves w (z.take (2 * ((w + 1) * (i + 1)))) = midpointMoves w z :=
      midpointMoves_take (by nlinarith) z
    simp only [midpointGame, hget, hmid, hdrop, ih]

/-- The existential player chooses a midpoint in `w` rounds. -/
private theorem alternation_midpointMoves (j : ℕ) {ns : List ℕ} :
    ∀ R : List Bool → List Bool → Prop,
      Alternation true (List.replicate (2 * j) 1 ++ ns)
        (fun z => R (midpointMoves j z) (z.drop (2 * j))) ↔
      ∃ m : List Bool, m.length = j ∧ Alternation true ns (R m) := by
  induction j with
  | zero =>
    intro R
    simp [midpointMoves]
  | succ j ih =>
    intro R
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
      List.cons_append, List.cons_append, alternation_true_one_cons]
    have key (x : Bool) := ih fun m => R (x :: m)
    simp only [alternation_false_one_cons, midpointMoves_cons_cons, List.drop_succ_cons, key]
    constructor
    · rintro ⟨x, h⟩
      obtain ⟨m, hm, h⟩ := h false
      exact ⟨x :: m, by simp [hm], h⟩
    · rintro ⟨_ | ⟨x, m⟩, hm, h⟩
      · simp at hm
      · exact ⟨x, fun _ => ⟨m, by simpa using hm, h⟩⟩

/-- The universal player chooses a half in one round. -/
private theorem alternation_half {ns : List ℕ} (S : Bool → List Bool → Prop) :
    Alternation true (1 :: 1 :: ns) (fun z => S (z.getD 1 false) (z.drop 2)) ↔
      ∀ d, Alternation true ns (S d) := by
  rw [alternation_true_one_cons]
  simp only [alternation_false_one_cons, List.getD_cons_succ, List.getD_cons_zero,
    List.drop_succ_cons, List.drop_zero]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨false, h⟩⟩

/-- **Savitch's midpoint game is reachability.** The existential player wins the game at level
`i` between `u` and `v`, of `2 * ((w + 1) * i)` moves, exactly when `v` is reachable from `u` by
Savitch's midpoint recursion at level `i` (`Cslib.Reachability.reach`). -/
theorem alternation_midpointGame_iff (i : ℕ) (u v : List Bool) :
    Alternation true (List.replicate (2 * ((w + 1) * i)) 1)
      (fun z => midpointGame edge w i u v z = true) ↔ reach edge w i u v = true := by
  induction i generalizing u v with
  | zero => simp [midpointGame]
  | succ i ih =>
    have hsplit : List.replicate (2 * ((w + 1) * (i + 1))) 1 =
        List.replicate (2 * w) 1 ++ (1 :: 1 :: List.replicate (2 * ((w + 1) * i)) 1) := by
      rw [← List.replicate_succ, ← List.replicate_succ, ← List.replicate_add]
      congr 1
      ring
    have hgame (z : List Bool) : midpointGame edge w (i + 1) u v z =
        (fun m z' => if z'.getD 1 false then midpointGame edge w i m v (z'.drop 2)
          else midpointGame edge w i u m (z'.drop 2)) (midpointMoves w z) (z.drop (2 * w)) := by
      simp only [midpointGame, List.getD_eq_getElem?_getD, List.getElem?_drop, List.drop_drop]
    rw [hsplit]
    simp only [hgame]
    rw [alternation_midpointMoves w (fun m z' => (if z'.getD 1 false then
      midpointGame edge w i m v (z'.drop 2) else midpointGame edge w i u m (z'.drop 2)) = true)]
    have key (m : List Bool) := alternation_half (ns := List.replicate (2 * ((w + 1) * i)) 1)
      (fun d z'' => (if d then midpointGame edge w i m v z'' else
        midpointGame edge w i u m z'') = true)
    simp only [key]
    simp only [reach, List.any_eq_true, Bool.and_eq_true, BitString.mem_enumList]
    refine exists_congr fun m => and_congr_right fun _ => ?_
    constructor
    · intro h
      exact ⟨(ih u m).mp (by simpa using h false), (ih m v).mp (by simpa using h true)⟩
    · rintro ⟨h₁, h₂⟩ (_ | _)
      · simpa using (ih u m).mpr h₁
      · simpa using (ih m v).mpr h₂

end Cslib.Reachability

namespace Cslib.Reachability

/-! ### The midpoint game in polynomial time -/

/-- One level of the midpoint game on the state `(u, v, moves)`. -/
def midpointStep (w : ℕ) (s : List Bool × List Bool × List Bool) :
    List Bool × List Bool × List Bool :=
  if s.2.2.getD (2 * w + 1) false then (midpointMoves w s.2.2, s.2.1, s.2.2.drop (2 * w + 2))
  else (s.1, midpointMoves w s.2.2, s.2.2.drop (2 * w + 2))

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-- The midpoint game is a loop of its levels. -/
theorem midpointGame_eq_iterate (i : ℕ) (u v z : List Bool) :
    midpointGame edge w i u v z =
      reach edge w 0 ((midpointStep w)^[i] (u, v, z)).1 ((midpointStep w)^[i] (u, v, z)).2.1 := by
  induction i generalizing u v z with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    unfold midpointGame midpointStep
    split <;> exact ih ..

open _root_.Turing _root_.Turing.MultiTapeTM

/-- A level of the midpoint game is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_midpointStep :
    Turing.MultiTapeTM.ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      midpointStep p.1 p.2) (encPair encUnary (encPair encBits (encPair encBits encBits)))
      (encPair encBits (encPair encBits encBits)) := by
  unfold midpointStep midpointMoves
  fun_prop

end Cslib.Reachability

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Reachability

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

section Verifier

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State) (c d : ℕ)

/-- **The verifier of Savitch's midpoint game** on the codes of the views of `ntm` on `enc a`,
from the code of the initial view to the accepting code, at depth the width of the codes. -/
noncomputable def savitchVerifier (x : α × List Bool) : Bool :=
  midpointGame ntm.codeEdge (ntm.viewCodeWidth c d (enc x.1))
    (ntm.viewCodeWidth c d (enc x.1))
    (MultiTapeNTM.viewCode (ntm.codeWidth c d (enc x.1)) (ntm.initView (enc x.1)))
    (MultiTapeNTM.acceptCode (ntm.codeWidth c d (enc x.1))) x.2

/-- The verifier of the midpoint game is polynomial-time. -/
theorem computableInPolyTime_savitchVerifier :
    Turing.MultiTapeTM.ComputableInPolyTime (savitchVerifier (enc := enc) ntm c d)
      (encPair enc encBits)
      encBool := by
  have hword : ComputableInPolyTime (fun x : α × List Bool => enc x.1) (encPair enc encBits)
      encBits :=
    (ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl).comp
      (ComputableInPolyTime.fst enc encBits)
  have hwidth : ComputableInPolyTime (fun x : α × List Bool => ntm.codeWidth c d (enc x.1))
      (encPair enc encBits) encUnary :=
    (MultiTapeNTM.computableInPolyTime_codeWidth c d).comp (ComputableInPolyTime.fst enc encBits)
  have hw : ComputableInPolyTime
      (fun x : α × List Bool => ntm.viewCodeWidth c d (enc x.1)) (encPair enc encBits)
      encUnary :=
    (ntm.computableInPolyTime_viewCodeWidth c d).comp hword
  have hinit : ComputableInPolyTime (fun x : α × List Bool =>
      (MultiTapeNTM.viewCode (ntm.codeWidth c d (enc x.1)) (ntm.initView (enc x.1)),
        MultiTapeNTM.acceptCode (ntm.codeWidth c d (enc x.1)), x.2))
      (encPair enc encBits) (encPair encBits (encPair encBits encBits)) :=
    (MultiTapeNTM.computableInPolyTime_viewCode_initView hwidth hword).prod
      ((MultiTapeNTM.computableInPolyTime_acceptCode hwidth).prod
        (ComputableInPolyTime.snd enc encBits))
  have hloop := ComputableInPolyTime.iterateWith_of_bounded_growth hw hw hinit
    computableInPolyTime_midpointStep
    (growth := fun x => 2 * ntm.viewCodeWidth c d (enc x.1))
    (ComputableInPolyTime.polyBounded (by fun_prop)) fun x s => by
      unfold midpointStep
      split <;> simp only [length_encPair, encBits_apply, List.length_drop,
        length_midpointMoves] <;> omega
  have hfst := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have hsnd := (ComputableInPolyTime.fst encBits encBits).comp
    (ComputableInPolyTime.snd encBits (encPair encBits encBits))
  have hfinal : ComputableInPolyTime (fun s : List Bool × List Bool × List Bool =>
      decide (s.1 = s.2.1) || ntm.codeEdge s.1 s.2.1) (encPair encBits (encPair encBits encBits))
      encBool :=
    ComputableInPolyTime.bool_or.comp ((ComputableInPolyTime.decide_eq' hfst hsnd).prod
      (ntm.computableInPolyTime_codeEdge hfst hsnd))
  convert hfinal.comp hloop using 1
  funext x
  rw [savitchVerifier, midpointGame_eq_iterate]
  rfl

end Verifier


/-- **Every problem in `PSPACE` has a polynomial-time game verifier**: the verifier of Savitch's
midpoint game on the codes of the views of a nondeterministic machine deciding it within polynomial
space. The game has `2 * ((W + 1) * W)` moves for the width `W` of the codes, padded to a
polynomial number. -/
theorem exists_isGameVerifier_of_mem_PSPACE (h : A ∈ PSPACE enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      Turing.MultiTapeTM.ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsGameVerifier enc p
        V A := by
  obtain ⟨k, State, _, ntm, s, hs, hA⟩ := PSPACE_subset_NPSPACE h
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  -- the number of rounds of the game is polynomially bounded
  have hrounds : ComputableInPolyTime
      (fun a => (ntm.viewCodeWidth c d (enc a) + 1) * ntm.viewCodeWidth c d (enc a))
      enc encUnary := by
    have := (ntm.computableInPolyTime_viewCodeWidth c d).comp
      (ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl)
    fun_prop
  obtain ⟨p, hr⟩ := hrounds.polyBounded.exists_polynomial
  refine ⟨p, savitchVerifier (enc := enc) ntm c d,
    computableInPolyTime_savitchVerifier ntm c d, fun a => ?_⟩
  set w := ntm.viewCodeWidth c d (enc a)
  have hle : 2 * ((w + 1) * w) ≤ 2 * p.eval (enc a).length :=
    Nat.mul_le_mul_left 2 (hr a)
  rw [(hA.recognizesInSpace a).2,
    ← MultiTapeNTM.savitchDecide_eq_true_iff (hA.recognizesInSpace a).1 (hcd a),
    MultiTapeNTM.savitchDecide,
    savitch_eq, ← Nat.add_sub_cancel' hle, List.replicate_add, alternation_append_iff
      fun z => by rw [Cslib.Complexity.sum_replicate_one, savitchVerifier, savitchVerifier,
        midpointGame_take]]
  exact (alternation_midpointGame_iff _ _ _).symm

/-- **`PSPACE ⊆ AP`** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]: a problem in
`PSPACE` is Savitch's midpoint game on the views of a machine deciding it, which the
guess-then-verify machine plays in polynomial time. -/
theorem PSPACE_subset_AP : PSPACE enc ⊆ AP enc := fun _ hA =>
  let ⟨_, _, hV, h⟩ := exists_isGameVerifier_of_mem_PSPACE hA
  h.mem_AP hV

/-- **`AP = PSPACE`** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Theorem 10.21][Sipser2013]. -/
theorem AP_eq_PSPACE : AP enc = PSPACE enc :=
  AP_subset_PSPACE.antisymm PSPACE_subset_AP

/-- **The problems with polynomial-time game verifiers are exactly those in `PSPACE`.** -/
theorem mem_PSPACE_iff_exists_isGameVerifier : A ∈ PSPACE enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      Turing.MultiTapeTM.ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsGameVerifier enc p
        V A :=
  ⟨exists_isGameVerifier_of_mem_PSPACE, fun ⟨_, _, hV, h⟩ => h.mem_PSPACE hV⟩

end Cslib.Complexity
