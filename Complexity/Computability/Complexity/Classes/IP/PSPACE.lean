/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.GameTree
public import Complexity.Computability.Complexity.Classes.IP.Simulation
public import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# `IP ⊆ PSPACE`

Every problem with an interactive proof is decided within polynomial space
(`Cslib.Complexity.IP_subset_PSPACE`) [Arora and Barak, Chapter 8][AroraBarak09]
[Sipser, Section 10.4][Sipser2013].

The model is that of `Cslib.Complexity.IP`. The verifier is strict oracle PPT: one finite fair-coin
oracle machine `M` and one clock `t = c * (n + 1) ^ d`, for instances encoded with `n` bits, realize
it against every stateful prover. So the coins are private and there are at most `t` of them, one
per instruction; the verifier sends at most `t` messages, each shorter than `t`, and reads at most
the first `t` bits of every reply. Provers are arbitrary: randomized, stateful and
computationally unbounded; they see the messages but not the coins. The thresholds are `2 / 3`
and `1 / 3`.

The proof computes the acceptance probability of the optimal prover exactly, as a count of coin
values:

* Fixing the `t` coins of the run leaves programs making word requests
  (`Cslib.Complexity.Interaction.coinFamily`), and acceptance averages over the coins
  (`Cslib.Complexity.Interaction.acceptProb_eq_sum`). The programs form a bounded family
  (`Cslib.Complexity.Interaction.isBounded_coinFamily`), so the value `W` of the empty history
  (`Cslib.Complexity.Interaction.value`) bounds every prover by `W / 2 ^ t`, and the optimal prover
  attains it. With completeness `2 / 3` and soundness `1 / 3`, an instance is a member exactly when
  `2 ^ t < 2 * W` (`Cslib.Complexity.mem_iff_two_pow_lt_value`).
* `W` is the value of a game tree whose messages and replies are coded by the words of length
  `t + 1` containing a `true`, enumerated by a binary counter
  (`Cslib.Complexity.Interaction.image_decodeWord_iterate_firstCode`,
  `Cslib.Complexity.Interaction.gameTree_value_eq`). Its leaf values count the accepting coin
  values, within polynomial space
  (`Cslib.Complexity.Interaction.computableInPolySpace_countAccepts`).
* The explicit-stack evaluator of the game tree (`Cslib.Complexity.Interaction.evaluate`) runs for
  `2 ^ ((t + 1) * (2 * t + 1))` steps, with at most `t` frames of `O(t)` bits each
  (`Cslib.Complexity.Interaction.length_encEvalState_iterate_le`), so it computes `W` within
  polynomial space (`Cslib.Complexity.Interaction.evaluate_eq`,
  `Cslib.Complexity.Interaction.computableInPolySpace_evaluate`), in exponential time.

The converse inclusion `PSPACE ⊆ IP`, and so `IP = PSPACE`, is not formalized here.

## Main definitions

* `Cslib.Complexity.Interaction.decodeWord`, `Cslib.Complexity.Interaction.firstCode`,
  `Cslib.Complexity.Interaction.lastCode`: the codes of the short words.
* `Cslib.Complexity.Interaction.leafValue`: the leaf values, the accepting programs.
* `Cslib.Complexity.Interaction.evalStep`, `Cslib.Complexity.Interaction.evaluate`: the evaluation.

## Main results

* `Cslib.Complexity.Interaction.image_decodeWord_iterate_firstCode`: the codes enumerate the short
  words.
* `Cslib.Complexity.Interaction.gameTree_value_eq`: the value is the value of the game tree.
* `Cslib.Complexity.Interaction.evaluate_eq`: the evaluation computes the value.
* `Cslib.Complexity.Interaction.computableInPolySpace_evaluate`: within polynomial space.
* `Cslib.Complexity.mem_iff_two_pow_lt_value`: the value decides the problem.
* `Cslib.Complexity.IP_subset_PSPACE`: `IP ⊆ PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity.Interaction

open Finset
open Cslib.BitString (increment lsbValue)

/-! ### Enumerating the short words -/

/-- The word coded by `u`: what follows its first `true`. -/
def decodeWord (u : List Bool) : List Bool := u.drop (u.idxOf true + 1)

/-- The code of a word `w` of length at most `L` among the words of length `L + 1`: `L - |w|`
zeros, a one, then `w`. -/
def encodeWord (L : ℕ) (w : List Bool) : List Bool :=
  List.replicate (L - w.length) false ++ true :: w

private theorem idxOf_true_replicate_false_append (n : ℕ) (w : List Bool) :
    (List.replicate n false ++ true :: w).idxOf true = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.idxOf_cons_ne _ (by simp), ih]

/-- Decoding inverts coding. -/
private theorem decodeWord_encodeWord (L : ℕ) (w : List Bool) : decodeWord
    (encodeWord L w) = w := by
  rw [decodeWord, encodeWord, idxOf_true_replicate_false_append, List.drop_append]
  simp

private theorem length_encodeWord {L : ℕ} {w : List Bool} (hw : w.length ≤ L) :
    (encodeWord L w).length = L + 1 := by
  simp only [encodeWord, List.length_append, List.length_replicate, List.length_cons]
  lia

private theorem true_mem_encodeWord (L : ℕ) (w : List Bool) : true ∈ encodeWord L w := by
  simp [encodeWord]

private theorem length_decodeWord_le {L : ℕ} {u : List Bool} (hu : u.length = L + 1) :
    (decodeWord u).length ≤ L := by
  simp only [decodeWord, List.length_drop]
  lia

/-- A word with a `true` is its first `true` preceded by zeros and followed by its decoding. -/
private theorem eq_replicate_append_decodeWord : ∀ {u : List Bool}, true ∈ u →
    u = List.replicate (u.idxOf true) false ++ true :: decodeWord u
  | b :: u, h => by
    cases b
    · have hu : true ∈ u := by simpa using h
      rw [decodeWord, List.idxOf_cons_ne _ (by simp)]
      have := eq_replicate_append_decodeWord hu
      rw [decodeWord] at this
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
      exact congrArg _ this
    · simp [decodeWord]

/-- Coding inverts decoding on the words of length `L + 1` with a `true`. -/
private theorem encodeWord_decodeWord {L : ℕ} {u : List Bool} (hu : u.length = L + 1)
    (ht : true ∈ u) :
    encodeWord L (decodeWord u) = u := by
  have h := eq_replicate_append_decodeWord ht
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_replicate, List.length_cons, hu] at hlen
  rw [encodeWord, show L - (decodeWord u).length = u.idxOf true by lia]
  exact h.symm

variable (L : ℕ)

/-- The first code, `1` in binary. -/
def firstCode : List Bool := true :: List.replicate L false

/-- Whether a code is the last one, all ones. -/
def lastCode (u : List Bool) : Bool := decide (u = List.replicate (L + 1) true)

/-- The number of codes, and of the words of length at most `L`. -/
def codeCount : ℕ := 2 ^ (L + 1) - 1

private theorem iterate_firstCode (i : ℕ) :
    increment^[i] (firstCode L) = increment^[i + 1] (List.replicate (L + 1) false) := by
  rw [Function.iterate_succ_apply]
  rfl

variable {L}

/-- The `i`-th code has value `i + 1` and length `L + 1`. -/
private theorem lsbValue_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    lsbValue (increment^[i] (firstCode L)) = i + 1 ∧
      (increment^[i] (firstCode L)).length = L + 1 := by
  rw [iterate_firstCode]
  exact BitString.iterate_increment (L + 1) (i + 1) (by simp only [codeCount] at hi; lia)

/-- The last code is the `codeCount L`-th. -/
private theorem lastCode_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    lastCode L (increment^[i] (firstCode L)) = decide (i + 1 = codeCount L) := by
  obtain ⟨hv, hl⟩ := lsbValue_iterate_firstCode hi
  have hall := BitString.lsbValue_replicate_true (L + 1)
  simp only [lastCode, decide_eq_decide]
  constructor
  · intro h
    rw [h] at hv
    simp only [codeCount]
    lia
  · intro h
    refine BitString.lsbValue_injective (by simp [hl]) ?_
    simp only [codeCount] at h
    lia

private theorem true_mem_iterate_firstCode {i : ℕ} (hi : i < codeCount L) :
    true ∈ increment^[i] (firstCode L) := by
  by_contra h
  have := BitString.lsbValue_eq_zero_of_true_not_mem h
  rw [(lsbValue_iterate_firstCode hi).1] at this
  lia

/-- **The codes enumerate the short words**: decoding the first `codeCount L` codes gives every word
of length at most `L` exactly once. -/
theorem image_decodeWord_iterate_firstCode :
    (range (codeCount L)).image (fun i => decodeWord (increment^[i] (firstCode L))) =
      BitString.shortWords L := by
  ext w
  simp only [mem_image, mem_range, BitString.mem_shortWords]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact length_decodeWord_le (lsbValue_iterate_firstCode hi).2
  · intro hw
    have hlen := length_encodeWord hw
    have hpos := BitString.lsbValue_pos_of_true_mem (true_mem_encodeWord L w)
    have hlt := BitString.lsbValue_lt (encodeWord L w)
    rw [hlen] at hlt
    refine ⟨lsbValue (encodeWord L w) - 1, by simp only [codeCount]; lia, ?_⟩
    rw [iterate_firstCode, Nat.sub_add_cancel hpos, ← hlen, BitString.iterate_increment_lsbValue,
      decodeWord_encodeWord]

private theorem injOn_decodeWord_iterate_firstCode :
    Set.InjOn (fun i => decodeWord (increment^[i] (firstCode L))) (range (codeCount L)) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  have hu := encodeWord_decodeWord (lsbValue_iterate_firstCode hi).2 (true_mem_iterate_firstCode hi)
  have hv := encodeWord_decodeWord (lsbValue_iterate_firstCode hj).2 (true_mem_iterate_firstCode hj)
  simp only at h
  have := congrArg lsbValue (hu.symm.trans ((congrArg (encodeWord L) h).trans hv))
  rw [(lsbValue_iterate_firstCode hi).1, (lsbValue_iterate_firstCode hj).1] at this
  lia

/-! ### The value as a game tree -/

section GameTree

variable {R : Type} [Fintype R] (F : R → WordQueryComp Unit Bool)

/-- The history coded by a game-tree history of codes, the most recent first. -/
def decodeHistory (hs : List (List Bool × List Bool)) : History :=
  (hs.map fun p => (decodeWord p.1, decodeWord p.2)).reverse

@[simp] theorem decodeHistory_nil : decodeHistory [] = [] := rfl

@[simp] theorem decodeHistory_cons (p : List Bool × List Bool)
    (hs : List (List Bool × List Bool)) :
    decodeHistory (p :: hs) = decodeHistory hs ++ [(decodeWord p.1, decodeWord p.2)] := by
  simp [decodeHistory]

/-- The leaf value of a game-tree history: the number of accepting programs. -/
def leafValue (hs : List (List Bool × List Bool)) : ℕ :=
  accepted F (decodeHistory hs)

/-- **The value is the value of the game tree** of the codes of the short words, with sums capped
at a bound on the number of coin values. -/
theorem gameTree_value_eq {cap : ℕ} (hcap : Fintype.card R ≤ cap) (n : ℕ)
    (hs : List (List Bool × List Bool)) :
    GameTree.value (codeCount L) cap (firstCode L) increment (leafValue F) n hs =
      value F L n (decodeHistory hs) := by
  have hle (n : ℕ) (h : History) : value F L n h ≤ cap :=
    (value_le_card n h).trans ((Finset.card_le_univ _).trans hcap)
  induction n generalizing hs with
  | zero => exact min_eq_right (hle 0 _)
  | succ n ih =>
    rw [GameTree.value, ← min_eq_right (hle (n + 1) (decodeHistory hs)), value]
    congr 2
    simp only [ih, decodeHistory_cons]
    have hsup (m : List Bool) : ((range (codeCount L)).sup fun j =>
        value F L n (decodeHistory hs ++ [(m, decodeWord (increment^[j] (firstCode L)))])) =
        (BitString.shortWords L).sup fun y => value F L n (decodeHistory hs ++ [(m, y)]) := by
      rw [← image_decodeWord_iterate_firstCode, Finset.sup_image]
      rfl
    simp only [hsup]
    rw [← image_decodeWord_iterate_firstCode,
      Finset.sum_image injOn_decodeWord_iterate_firstCode]

end GameTree

/-! ### Polynomial-time parts -/

section PolyTime

open _root_.Turing _root_.Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Decoding a word is polynomial-time. -/
private theorem computableTidilyInPolyTime_decodeWord :
    ComputableTidilyInPolyTime decodeWord encBits encBits := by
  have hidx : ComputableTidilyInPolyTime (fun u : List Bool => u.idxOf true + 1) encBits
      encUnary := by
    have h := (idxOf encBool).comp (bitsToList.prod (const (encMid := encBool) true))
    have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
      ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
    exact hsucc.comp h
  exact bitsDropWithInput id' hidx

/-- Decoding a history is polynomial-time. -/
private theorem computableTidilyInPolyTime_decodeHistory :
    ComputableTidilyInPolyTime decodeHistory (encList (encPair encBits encBits)) encHistory := by
  have hd := computableTidilyInPolyTime_decodeWord
  unfold decodeHistory
  fun_prop

end PolyTime

/-! ### The evaluation -/

section Evaluation

variable {α : Type} (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
  (M : _root_.Turing.MultiTapePTM k Bool Control Unit) (fuel : α → ℕ)

/-- The states of the evaluation: the instance, the stack and the value being returned. -/
abbrev EvalState (α : Type) := α × List (GameTree.Frame (List Bool)) × Option ℕ

/-- One step of the evaluation of the game tree of the verifier `M` on `a`, with `fuel a` coins,
rounds and message lengths. -/
def evalStep (s : EvalState α) : EvalState α :=
  (s.1, GameTree.step (fuel s.1) (2 ^ fuel s.1) (firstCode (fuel s.1)) BitString.increment
    (lastCode (fuel s.1)) (leafValue (coinFamily M (fuel s.1) (enc s.1))) s.2)

/-- The number of steps of the evaluation, a bound on `GameTree.time`. -/
def evalTime (a : α) : ℕ := 2 ^ ((fuel a + 1) * (2 * fuel a + 1))

/-- The value computed by the evaluation. -/
def evaluate (a : α) : ℕ :=
  ((evalStep enc M fuel)^[evalTime fuel a] (a, [], none)).2.2.getD 0

/-- The evaluation keeps its instance and runs the game-tree evaluator. -/
private theorem iterate_evalStep (a : α) (st : List (GameTree.Frame (List Bool)) × Option ℕ)
    (j : ℕ) :
    (evalStep enc M fuel)^[j] (a, st) = (a, (GameTree.step (fuel a) (2 ^ fuel a)
      (firstCode (fuel a)) increment (lastCode (fuel a))
        (leafValue (coinFamily M (fuel a) (enc a))))^[j] st) := by
  induction j generalizing st with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]; rfl

/-- **The evaluation computes the value** of the verifier on `a`. -/
theorem evaluate_eq (a : α) :
    evaluate enc M fuel a = value (coinFamily M (fuel a) (enc a)) (fuel a) (fuel a) [] := by
  have hN : 0 < codeCount (fuel a) := by
    simp only [codeCount]
    have := Nat.one_lt_two_pow (n := fuel a + 1) (by lia)
    lia
  have htime : GameTree.time (codeCount (fuel a)) (fuel a) ≤ evalTime fuel a := by
    refine (GameTree.time_le _).trans (le_of_eq ?_)
    rw [evalTime, codeCount, Nat.sub_add_cancel (Nat.one_le_two_pow), ← pow_mul]
  rw [evaluate, iterate_evalStep, GameTree.iterate_step_eval hN
    (fun i hi => lastCode_iterate_firstCode hi) htime]
  simp only [Option.getD_some]
  rw [gameTree_value_eq _ (by simp), decodeHistory_nil]

/-- Returning a value into the stack, with its explicit cases. -/
private def returnStep (L cap : ℕ) (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    List (GameTree.Frame (List Bool)) × Option ℕ :=
  if st.isEmpty then (st, some v)
  else
    let f := st.headD ([], [], 0, 0)
    if lastCode L f.2.1 then
      if lastCode L f.1 then (st.tail, some (min cap (f.2.2.1 + max f.2.2.2 v)))
      else ((increment f.1, firstCode L, min cap (f.2.2.1 + max f.2.2.2 v), 0) :: st.tail, none)
    else ((f.1, increment f.2.1, f.2.2.1, max f.2.2.2 v) :: st.tail, none)

/-- A value returned into the stack, by `returnStep`. -/
private theorem step_some_eq (L cap : ℕ) (leaf : List (List Bool × List Bool) → ℕ)
    (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    GameTree.step L cap (firstCode L) increment (lastCode L) leaf (st, some v) =
      returnStep L cap st v := by
  rcases st with _ | ⟨⟨u, w, sm, ac⟩, st⟩
  · rfl
  · rfl

/-- Pushing a frame, or returning the leaf value at the maximal depth. -/
def pushStep (L : ℕ) (st : List (GameTree.Frame (List Bool))) (v : ℕ) :
    List (GameTree.Frame (List Bool)) × Option ℕ :=
  if st.length = L then (st, some v) else ((firstCode L, firstCode L, v, 0) :: st, none)

/-- A node without a returned value, by `pushStep`. -/
theorem step_none_eq (L cap : ℕ) (leaf : List (List Bool × List Bool) → ℕ)
    (st : List (GameTree.Frame (List Bool))) :
    GameTree.step L cap (firstCode L) increment (lastCode L) leaf (st, none) =
      pushStep L st (min cap (leaf (GameTree.history st))) := rfl

/-- One step of the evaluation, as a case distinction calling the leaf value once. -/
private theorem evalStep_eq (s : EvalState α) : evalStep enc M fuel s =
    if s.2.2.isSome then (s.1, returnStep (fuel s.1) (2 ^ fuel s.1) s.2.1 (s.2.2.getD 0))
    else (s.1, pushStep (fuel s.1) s.2.1 (min (2 ^ fuel s.1)
      (leafValue (coinFamily M (fuel s.1) (enc s.1)) (GameTree.history s.2.1)))) := by
  obtain ⟨a, st, _ | v⟩ := s
  · rfl
  · exact congrArg _ (step_some_eq _ _ _ st v)

end Evaluation

/-! ### The evaluation in polynomial space -/

section Space

open _root_.Turing _root_.Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {γ : Type} {input : γ ↪ List Bool}

@[local fun_prop] private theorem max_pt {left right : γ → ℕ}
    (hl : ComputableTidilyInPolyTime left input encNat)
    (hr : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun x => max (left x) (right x)) input encNat := by
  simp only [max_def]
  exact ite_decide (binary_le' hl hr) hr hl

@[local fun_prop] private theorem min_pt {left right : γ → ℕ}
    (hl : ComputableTidilyInPolyTime left input encNat)
    (hr : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun x => min (left x) (right x)) input encNat := by
  simp only [min_def]
  exact ite_decide (binary_le' hl hr) hl hr

@[local fun_prop] private theorem firstCode_pt {count : γ → ℕ}
    (h : ComputableTidilyInPolyTime count input encUnary) :
    ComputableTidilyInPolyTime (fun x => firstCode (count x)) input encBits :=
  bitsCons (const true) ((bitsReplicate false).comp h)

@[local fun_prop] private theorem lastCode_pt {count : γ → ℕ} {word : γ → List Bool}
    (h : ComputableTidilyInPolyTime count input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits) :
    ComputableTidilyInPolyTime (fun x => lastCode (count x) (word x)) input encBool := by
  have hsucc : ComputableTidilyInPolyTime (· + 1) encUnary encUnary :=
    ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime
  exact decide_eq' hword ((bitsReplicate true).comp (hsucc.comp h))

variable {α : Type} (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
  (M : _root_.Turing.MultiTapePTM k Bool Control Unit) (fuel : α → ℕ)

/-- Frames, encoded by their fields. -/
abbrev encFrame : GameTree.Frame (List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits (encPair encNat encNat))

/-- States of the evaluation, encoded by their fields. -/
abbrev encEvalState : EvalState α ↪ List Bool :=
  encPair enc (encPair (encList encFrame) (encOption encNat))

variable {enc fuel} (hfuel : ComputableTidilyInPolyTime fuel enc encUnary)
include hfuel

/-- Returning a value into the stack is polynomial-time. -/
private theorem computableTidilyInPolyTime_returnStep :
    ComputableTidilyInPolyTime (fun s : EvalState α =>
      (s.1, returnStep (fuel s.1) (2 ^ fuel s.1) s.2.1 (s.2.2.getD 0)))
      (encEvalState enc) (encEvalState enc) := by
  have hfuel' : ComputableTidilyInPolyTime (fun s : EvalState α => fuel s.1) (encEvalState enc)
      encUnary := hfuel.comp (fst _ _)
  unfold returnStep
  fun_prop

/-- Pushing a frame is polynomial-time. -/
private theorem computableTidilyInPolyTime_pushStep :
    ComputableTidilyInPolyTime (fun p : EvalState α × ℕ =>
      (p.1.1, pushStep (fuel p.1.1) p.1.2.1 p.2))
      (encPair (encEvalState enc) encNat) (encEvalState enc) := by
  have hfuel' : ComputableTidilyInPolyTime (fun p : EvalState α × ℕ => fuel p.1.1)
      (encPair (encEvalState enc) encNat) encUnary := hfuel.comp (by fun_prop)
  unfold pushStep
  fun_prop

/-- **The leaf value within polynomial space**: the count of accepting coins, capped. -/
private theorem computableTidilyInPolySpace_leaf [Finite Control] :
    ComputableTidilyInPolySpace (fun s : EvalState α => min (2 ^ fuel s.1)
      (leafValue (coinFamily M (fuel s.1) (enc s.1)) (GameTree.history s.2.1)))
      (encEvalState enc) encNat := by
  have hcount := (computableInPolySpace_countAccepts M enc fuel (.of_tidy hfuel)).tidy
  have hdec := computableTidilyInPolyTime_decodeHistory
  have harg : ComputableTidilyInPolyTime (fun s : EvalState α =>
      (s.1, decodeHistory (GameTree.history s.2.1))) (encEvalState enc)
      (encPair enc encHistory) := by
    unfold GameTree.history
    fun_prop
  have hcap : ComputableTidilyInPolyTime (fun s : EvalState α => 2 ^ fuel s.1)
      (encEvalState enc) encNat := binary_two_pow.comp (hfuel.comp (fst _ _))
  have hmin : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => min p.1 p.2) (encPair encNat encNat)
      encNat := by fun_prop
  refine ((ComputableTidilyInPolySpace.of_polyTime hmin).comp
    ((ComputableTidilyInPolySpace.of_polyTime hcap).prod (hcount.comp
      (ComputableTidilyInPolySpace.of_polyTime harg)))).congr fun s => ?_
  simp only [leafValue, countAccepts_eq_accepted]

/-- **A step of the evaluation within polynomial space.** -/
private theorem computableTidilyInPolySpace_evalStep [Finite Control] :
    ComputableTidilyInPolySpace (evalStep enc M fuel) (encEvalState enc) (encEvalState enc) := by
  have hcond : ComputableTidilyInPolyTime (fun s : EvalState α => s.2.2.isSome)
      (encEvalState enc) encBool := by fun_prop
  refine (ComputableTidilyInPolySpace.ite (.of_polyTime hcond)
    (.of_polyTime (computableTidilyInPolyTime_returnStep hfuel))
    ((ComputableTidilyInPolySpace.of_polyTime (computableTidilyInPolyTime_pushStep hfuel)).comp
      ((ComputableTidilyInPolySpace.of_polyTime id').prod
        (computableTidilyInPolySpace_leaf M hfuel)))).congr fun s => ?_
  rw [evalStep_eq]

omit hfuel in
/-- A number at most `2 ^ L` has a binary encoding of length at most `L + 1`. -/
private theorem length_encNat_le {m L : ℕ} (h : m ≤ 2 ^ L) : (encNat m).length ≤ L + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by lia)))

omit hfuel in
/-- **The states of the evaluation are of polynomial size.** -/
theorem length_encEvalState_iterate_le (a : α) (j : ℕ) :
    (encEvalState enc ((evalStep enc M fuel)^[j] (a, [], none))).length ≤
      2 * (enc a).length + 2 * fuel a * (14 * fuel a + 21) + fuel a + 4 := by
  rw [iterate_evalStep]
  have hgood := GameTree.good_iterate_step (D := fuel a) (cap := 2 ^ fuel a)
    (first := firstCode (fuel a)) (next := BitString.increment) (last := lastCode (fuel a))
    (leaf := leafValue (coinFamily M (fuel a) (enc a)))
    (P := fun u => u.length = fuel a + 1) (by simp [firstCode])
    (fun u hu => by simpa using hu) j
  set st := (GameTree.step (fuel a) (2 ^ fuel a) (firstCode (fuel a)) BitString.increment
    (lastCode (fuel a)) (leafValue (coinFamily M (fuel a) (enc a))))^[j] ([], none)
  have hframe : ∀ f ∈ st.1, (encFrame f).length ≤ 7 * fuel a + 10 := by
    intro f hf
    obtain ⟨hu, hw, hs, ha⟩ := hgood.frames f hf
    have hs' := length_encNat_le hs
    have ha' := length_encNat_le ha
    simp only [encFrame, length_encPair, encBits_apply, hu, hw] at hs' ha' ⊢
    lia
  have hlist := length_encList_le encFrame st.1 hframe
  have hdepth := Nat.mul_le_mul_right (2 * (7 * fuel a + 10) + 1) hgood.length
  have hret : (encOption encNat st.2).length ≤ fuel a + 2 := by
    rcases hst : st.2 with _ | v
    · simp
    · have := length_encNat_le (hgood.value v hst)
      simp only [encOption_some, List.length_cons]
      lia
  simp only [encEvalState, length_encPair]
  nlinarith

omit hfuel in
/-- **The evaluation within polynomial space.** -/
theorem computableInPolySpace_evaluate [Finite Control] [Inhabited α]
    (hfuel : ComputableInPolyTime fuel enc encUnary) :
    ComputableInPolySpace (evaluate enc M fuel) enc encNat := by
  have hfuel := hfuel.tidy
  refine .of_tidy ?_
  have hn : ComputableTidilyInPolyTime (evalTime fuel) enc encNat := by
    have hexp : ComputableTidilyInPolyTime (fun a => (fuel a + 1) * (2 * fuel a + 1)) enc
        encUnary := by
      have h1 := unary_add.comp (hfuel.prod (const (encMid := encUnary) 1))
      have h2 := unary_add.comp ((unary_mul.comp ((const (encMid := encUnary) 2).prod hfuel)).prod
        (const (encMid := encUnary) 1))
      exact unary_mul.comp (h1.prod h2)
    exact binary_two_pow.comp hexp
  have hinit : ComputableTidilyInPolyTime (fun a : α => ((a, [], none) : EvalState α)) enc
      (encEvalState enc) := by fun_prop
  have hlen := hfuel.polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hlen
  have hit := ComputableTidilyInPolySpace.iterate hn (.of_polyTime hinit)
    (computableTidilyInPolySpace_evalStep M hfuel)
    (B := fun a => 2 * (enc a).length + 2 * fuel a * (14 * fuel a + 21) + fuel a + 4)
    (((((PolyBounded.const 2).mul .self).add (((PolyBounded.const 2).mul hlen).mul
      (((PolyBounded.const 14).mul hlen).add (.const 21)))).add hlen).add (.const 4))
    (fun a j _ => length_encEvalState_iterate_le M a j)
  have hpost : ComputableTidilyInPolyTime (fun s : EvalState α => s.2.2.getD 0)
      (encEvalState enc) encNat := by fun_prop
  exact (ComputableTidilyInPolySpace.of_polyTime hpost).comp hit

end Space

end Cslib.Complexity.Interaction

namespace Cslib.Complexity

open Cslib.Probability Interaction _root_.Turing _root_.Turing.MultiTapeTM

private theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ENNReal) / b ≤ c / d ↔ a * d ≤ b * c := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  rw [mul_comm (c : ENNReal)]
  exact_mod_cast Iff.rfl

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {Control : Type}

/-- **The value decides an interactive proof.** If the verifier `V` is realized, against every
stateful prover, by the run of the oracle machine `M` under the clock `fuel a`, then a member of the
problem is exactly an instance on which the value of the programs of `fuel a` coins exceeds half the
number of coin values: completeness `2 / 3` and the optimal prover give more than half, soundness
`1 / 3` and the bound on all provers give less. -/
theorem mem_iff_two_pow_lt_value {V : α → WordOracleComp Unit Bool} {A : Set α}
    {M : MultiTapePTM k Bool Control Unit} {fuel : α → ℕ}
    (hV : ∀ a (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (encBool <$> V a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (M.runOracle (fuel a) (enc a))).run s)
    (hA : IsInteractiveProof V A (2 / 3) (1 / 3)) (a : α) :
    a ∈ A ↔ 2 ^ fuel a < 2 * value (coinFamily M (fuel a) (enc a)) (fuel a) (fuel a) [] := by
  set t := fuel a
  set W := value (coinFamily M t (enc a)) t t []
  have hbounded := isBounded_coinFamily M t (enc a)
  have hacc (P : Prover Unit) : acceptProb (V a) P =
      (2 ^ t : ENNReal)⁻¹ * ∑ r, acceptFrom P P.init (some (coinFamily M t (enc a) r)) :=
    acceptProb_eq_sum M (hV a) P
  have hpos : 2 ^ t ≠ 0 := by positivity
  have hcast : ((2 ^ t : ℕ) : ENNReal) = 2 ^ t := by push_cast; rfl
  have hupper (P : Prover Unit) : acceptProb (V a) P ≤ (W : ENNReal) / (2 ^ t : ℕ) := by
    rw [hacc, ENNReal.div_eq_inv_mul, hcast]
    exact mul_le_mul_right (sum_acceptFrom_le_value hbounded P) _
  have hopt : acceptProb (V a) (optimalProver (coinFamily M t (enc a)) t t) =
      (W : ENNReal) / (2 ^ t : ℕ) := by
    rw [hacc, ENNReal.div_eq_inv_mul, hcast, sum_acceptFrom_optimalProver hbounded]
  constructor
  · intro ha
    obtain ⟨P, hP⟩ := hA.complete a ha
    have h := hP.trans (hupper P)
    rw [show (2 / 3 : ENNReal) = ((2 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      natCast_div_le_natCast_div_iff (by norm_num) hpos] at h
    have := Nat.one_le_two_pow (n := t)
    lia
  · intro hlt
    by_contra ha
    have h := hopt ▸ hA.sound a ha (optimalProver _ t t)
    rw [show (1 / 3 : ENNReal) = ((1 : ℕ) : ENNReal) / ((3 : ℕ) : ENNReal) by norm_num,
      natCast_div_le_natCast_div_iff hpos (by norm_num)] at h
    lia

/-- **`IP ⊆ PSPACE`** [Arora and Barak, Chapter 8][AroraBarak09] [Sipser, Section
10.4][Sipser2013]: a problem with an interactive proof, whose verifier is strict oracle PPT with
private coins, against all randomized stateful provers, is decided within polynomial space. The
decider evaluates the game tree of the optimal prover over the messages and replies no longer than
the clock of the verifier, counting the accepting coin values at its leaves
(`Cslib.Complexity.Interaction.evaluate`), and compares the count with half the number of coin
values (`Cslib.Complexity.mem_iff_two_pow_lt_value`). -/
theorem IP_subset_PSPACE (enc : α ↪ List Bool) : IP enc ⊆ PSPACE enc := by
  rintro A ⟨V, hV, hA⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · exact P_subset_PSPACE ⟨fun _ => false, ComputableInPolyTime.const false,
      fun a => isEmptyElim a⟩
  let _ : Inhabited α := Classical.inhabited_of_nonempty hα
  obtain ⟨_, k, Control, _, M, c, d, hreal⟩ := hV
  set fuel : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hfuel : ComputableTidilyInPolyTime fuel enc encUnary := by
    have hlen : ComputableTidilyInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    exact ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      hlen).of_enc_eq fun a => by simp [fuel]
  have hdec : ComputableTidilyInPolySpace
      (fun a => decide (2 ^ fuel a < 2 * evaluate enc M fuel a)) enc encBool := by
    have hcap : ComputableTidilyInPolyTime (fun a => 2 ^ fuel a) enc encNat :=
      ComputableTidilyInPolyTime.binary_two_pow.comp hfuel
    have hpost : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < 2 * p.2))
        (encPair encNat encNat) encBool :=
      ComputableTidilyInPolyTime.binary_lt' (ComputableTidilyInPolyTime.fst _ _)
        (ComputableTidilyInPolyTime.binary_mul' (ComputableTidilyInPolyTime.const 2)
          (ComputableTidilyInPolyTime.snd _ _))
    exact (ComputableTidilyInPolySpace.of_polyTime hpost).comp
      ((ComputableTidilyInPolySpace.of_polyTime hcap).prod
        (computableInPolySpace_evaluate M (.of_tidy hfuel)).tidy)
  refine mem_PSPACE_of_computableInPolySpace (.of_tidy hdec) fun a => ?_
  rw [mem_iff_two_pow_lt_value (fun a S oracle s => hreal a S oracle s) hA a, evaluate_eq,
    decide_eq_true_iff]

end Cslib.Complexity
