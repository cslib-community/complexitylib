/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Foundations.Data.BitString.ShortWords

/-!
# The optimal prover against private coins

Fixing the private coins of a verifier leaves a deterministic program making word requests
(`Cslib.Complexity.WordQueryComp`). A verifier whose coins range over a finite set `R` is thus a
family `F : R → WordQueryComp Unit Bool` of such programs, one for every value of the coins, and a
prover interacting with the verifier interacts with `F r` for a uniformly random `r` that it does
not see. It sees only the messages, so after a history of messages and replies
(`Cslib.Complexity.Interaction.History`) the coin values still in play are those of the programs
that sent exactly the messages of the history; what remains of each of them is
`Cslib.Complexity.Interaction.after`.

The value of a history (`Cslib.Complexity.Interaction.value`) counts the programs that accept on
it, plus, for every next message, the best value over the replies. The best reply cannot depend
on the coins: it is chosen once for all the programs sending that message. Sums and maxima range
over the words of length at most `L` (`Cslib.BitString.shortWords`), which suffices for
a bounded family (`Cslib.Complexity.Interaction.IsBounded`): every program makes at most `D`
requests, every message has length at most `L`, and only the first `L` bits of a reply matter.

For a bounded family, the value of the empty history is the largest number of accepting programs
in expectation over the provers: every prover, randomized and stateful, is accepted on average
over `r` with probability at most the value divided by the number of coin values
(`Cslib.Complexity.Interaction.sum_acceptFrom_le_value`), and the deterministic prover that answers
every history with a best reply (`Cslib.Complexity.Interaction.optimalProver`) attains it
(`Cslib.Complexity.Interaction.sum_acceptFrom_optimalProver`). This is the optimal prover of the
proof of `IP ⊆ PSPACE` [Arora and Barak, Chapter 8][AroraBarak09]
[Sipser, Section 10.4][Sipser2013].

The outcome of a program on a history (`Cslib.Complexity.Interaction.outcome`) is also its run
against the history as a replay (`Cslib.Complexity.Interaction.outcome_eq_replay`), which is how a
deterministic machine evaluates it.

## Main definitions

* `Cslib.Complexity.Interaction.History`, `Cslib.Complexity.Interaction.after`,
  `Cslib.Complexity.Interaction.outcome`: histories and what remains of a program after them.
* `Cslib.Complexity.Interaction.acceptFrom`: the probability that a prover accepts from a state.
* `Cslib.Complexity.Interaction.value`: the value of a history.
* `Cslib.Complexity.Interaction.IsBounded`: bounds on rounds, messages and the replies read.
* `Cslib.Complexity.Interaction.optimalProver`: the prover answering with best replies.
* `Cslib.Complexity.Interaction.replay`: a run against a history.

## Main results

* `Cslib.Complexity.Interaction.sum_acceptFrom_le_value`: no prover beats the value.
* `Cslib.Complexity.Interaction.sum_acceptFrom_optimalProver`: the optimal prover attains it.
* `Cslib.Complexity.Interaction.value_le_card`: the value is at most the number of coin values.
* `Cslib.Complexity.Interaction.outcome_eq_replay`: outcomes are replays.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity.Interaction

open Cslib.Probability

variable {α : Type}

/-! ### Histories -/

/-- A history of an interaction: the messages of the verifier, each with the reply of the prover,
in order. -/
abbrev History := List (List Bool × List Bool)

/-- What remains of the program `p` after the history `h`, if `p` sends exactly the messages of
`h` when it receives its replies. -/
def after : WordQueryComp Unit α → History → Option (WordQueryComp Unit α)
  | p, [] => some p
  | .pure _, _ :: _ => none
  | .liftBind q next, (m, y) :: h => if m = q.2 then after (next y) h else none

@[simp] theorem after_nil (p : WordQueryComp Unit α) : after p [] = some p := by
  cases p <;> rfl

@[simp] theorem after_pure_cons (a : α) (x : List Bool × List Bool) (h : History) :
    after (pure a : WordQueryComp Unit α) (x :: h) = none := rfl

theorem after_query_bind_cons (m : List Bool) (next : List Bool → WordQueryComp Unit α)
    (m' y : List Bool) (h : History) :
    after (OracleComp.query ((), m) >>= next) ((m', y) :: h) =
      if m' = m then after (next y) h else none := rfl

/-- What remains after a concatenation is what remains of what remains. -/
private theorem after_append (p : WordQueryComp Unit α) (h e : History) :
    after p (h ++ e) = (after p h).bind (after · e) := by
  induction h generalizing p with
  | nil => simp
  | cons x h ih =>
    obtain ⟨m, y⟩ := x
    cases p with
    | pure a => rfl
    | liftBind q next =>
      simp only [List.cons_append, after]
      split_ifs
      · exact ih _
      · rfl

/-- The outcome of a program after a history: it has finished with a result, it sends a message,
or it does not send the messages of the history. -/
inductive Outcome where
  /-- The program has finished with this result. -/
  | done (result : Bool)
  /-- The program sends this message. -/
  | ask (message : List Bool)
  /-- The program does not send the messages of the history. -/
  | invalid
  deriving DecidableEq

/-- The outcome of `p` after the history `h`. -/
def outcome (p : WordQueryComp Unit Bool) (h : History) : Outcome :=
  match after p h with
  | none => .invalid
  | some (.pure b) => .done b
  | some (.liftBind q _) => .ask q.2

/-- A program that is still in play after a one-step extension sent its message. -/
private theorem outcome_eq_ask_of_after_append_singleton {p : WordQueryComp Unit Bool} {h : History}
    {m y : List Bool} (hp : (after p (h ++ [(m, y)])).isSome) : outcome p h = .ask m := by
  rw [after_append] at hp
  unfold outcome
  rcases hah : after p h with _ | ⟨b⟩ | ⟨q, next⟩ <;> simp only [hah] at hp
  · simp at hp
  · simp at hp
  · change (if m = q.2 then after (next y) [] else none).isSome = true at hp
    split_ifs at hp with hm
    · rw [hm]
    · simp at hp

/-! ### Acceptance against a prover -/

/-- The probability that the prover `P`, from its state `s`, makes what remains of a program
accept; `0` when nothing remains. -/
noncomputable def acceptFrom {Operation : Type} (P : Prover Operation) (s : P.State) :
    Option (WordQueryComp Operation Bool) → ENNReal
  | none => 0
  | some p => ((OracleComp.interpret P.respond p).run s).map Prod.fst true

@[simp] theorem acceptFrom_none {Operation : Type} (P : Prover Operation) (s : P.State) :
    acceptFrom P s none = 0 := rfl

private theorem acceptFrom_pure {Operation : Type} (P : Prover Operation) (s : P.State) (b : Bool) :
    acceptFrom P s (some (pure b)) = if b then 1 else 0 := by
  simp only [acceptFrom, OracleComp.interpret_pure, StateT.run_pure,
    Probability.PMF.monad_pure_eq_pure, PMF.pure_map, PMF.pure_apply]
  cases b <;> simp

/-- A message is answered by the prover, and what remains continues from its new state. -/
private theorem acceptFrom_query_bind (P : Prover Unit) (s : P.State) (m : List Bool)
    (next : List Bool → WordQueryComp Unit Bool) :
    acceptFrom P s (some (OracleComp.query ((), m) >>= next)) =
      ∑' ys : List Bool × P.State, (P.respond ((), m)).run s ys * acceptFrom P ys.2
        (some (next ys.1)) := by
  simp only [acceptFrom, OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_apply]

/-! ### The value of a history -/

variable {R : Type} [Fintype R] (F : R → WordQueryComp Unit Bool) (L : ℕ)

open Classical in
/-- The number of coin values whose programs accept after the history `h`. -/
def accepted (h : History) : ℕ :=
  (Finset.univ.filter fun r => outcome (F r) h = .done true).card

/-- The value of the history `h` with `n` rounds to go: the accepting programs, plus, for every
next message of length at most `L`, the best value over the replies of length at most `L`. -/
noncomputable def value : ℕ → History → ℕ
  | 0, h => accepted F h
  | n + 1, h => accepted F h + ∑ m ∈ BitString.shortWords L, (BitString.shortWords L).sup fun y =>
      value n (h ++ [(m, y)])

/-- A family of programs makes at most `D` requests, sends messages of length at most `L`, and
reads only the first `L` bits of each reply. -/
structure IsBounded (D L : ℕ) : Prop where
  /-- Every program has finished after `D` messages. -/
  rounds : ∀ r h m, outcome (F r) h = .ask m → h.length < D
  /-- Every message has length at most `L`. -/
  message : ∀ r h m, outcome (F r) h = .ask m → m.length ≤ L
  /-- Only the first `L` bits of a reply matter. -/
  reply : ∀ r h m y e, outcome (F r) (h ++ (m, y) :: e) = outcome (F r) (h ++ (m, y.take L) :: e)

variable {F L} {D : ℕ}

/-- The value of a history depends only on the outcomes of its extensions. -/
theorem value_congr {h h' : History}
    (hh : ∀ r e, outcome (F r) (h ++ e) = outcome (F r) (h' ++ e)) (n : ℕ) :
    value F L n h = value F L n h' := by
  induction n generalizing h h' with
  | zero =>
    simp only [value, accepted]
    congr 1
    ext r
    simpa using congrArg (· = Outcome.done true) (hh r [])
  | succ n ih =>
    have hacc : accepted F h = accepted F h' := by
      simp only [accepted]
      congr 1
      ext r
      simpa using congrArg (· = Outcome.done true) (hh r [])
    simp only [value, hacc]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => Finset.sup_congr rfl fun y _ => ih ?_)
    intro r e
    simpa only [List.append_assoc, List.singleton_append] using hh r ((m, y) :: e)

/-- Only the first `L` bits of a reply matter to the value. -/
private theorem value_take (hF : IsBounded F D L) (n : ℕ) (h : History) (m y : List Bool) :
    value F L n (h ++ [(m, y)]) = value F L n (h ++ [(m, y.take L)]) :=
  value_congr (fun r e => by
    simpa only [List.append_assoc, List.singleton_append] using hF.reply r h m y e) n

open Classical in
/-- **The value is at most the number of coin values** whose programs follow the history. -/
theorem value_le_card (n : ℕ) (h : History) :
    value F L n h ≤ (Finset.univ.filter fun r => outcome (F r) h ≠ .invalid).card := by
  induction n generalizing h with
  | zero =>
    refine Finset.card_le_card fun r hr => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [hr]
    exact nofun
  | succ n ih =>
    simp only [value, accepted]
    have hstep (m : List Bool) :
        ((BitString.shortWords L).sup fun y => value F L n (h ++ [(m, y)])) ≤
        (Finset.univ.filter fun r => outcome (F r) h = .ask m).card :=
      Finset.sup_le fun y _ => (ih _).trans (Finset.card_le_card fun r hr => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        refine outcome_eq_ask_of_after_append_singleton (y := y) ?_
        unfold outcome at hr
        rcases hah : after (F r) (h ++ [(m, y)]) with _ | p
        · simp [hah] at hr
        · rfl)
    refine (Nat.add_le_add_left (Finset.sum_le_sum fun m _ => hstep m) _).trans ?_
    rw [← Finset.card_biUnion (fun m _ m' _ hmm' => Finset.disjoint_filter.mpr
      fun r _ hr hr' => hmm' (Outcome.ask.inj (hr.symm.trans hr'))),
      ← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun r hr hr' => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hr'
        obtain ⟨m, _, hm⟩ := hr'
        rw [hr] at hm
        cases hm)]
    refine Finset.card_le_card fun r hr => ?_
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion] at hr ⊢
    rcases hr with hr | ⟨m, _, hr⟩ <;> rw [hr] <;> exact nofun

/-! ### No prover beats the value -/

/-- One round of a prover against a program: if the program has finished, it accepts or not; if
it sends a message of length at most `L`, the prover answers and what remains continues. -/
private theorem acceptFrom_after_eq (P : Prover Unit) (s : P.State) (p : WordQueryComp Unit Bool)
    (h : History) (hp : ∀ m, outcome p h = .ask m → m.length ≤ L) :
    acceptFrom P s (after p h) = (if outcome p h = .done true then 1 else 0) +
      ∑ m ∈ BitString.shortWords L, ∑' ys : List Bool × P.State,
        (P.respond ((), m)).run s ys * acceptFrom P ys.2 (after p (h ++ [(m, ys.1)])) := by
  simp only [after_append]
  unfold outcome at hp ⊢
  rcases hah : after p h with _ | ⟨b⟩ | ⟨q, next⟩
  · simp
  · change acceptFrom P s (some (pure b)) = _
    rw [acceptFrom_pure]
    cases b <;> simp
  · simp only [hah] at hp
    simp only [reduceCtorEq, ite_false, zero_add, Option.bind_some, after]
    obtain ⟨⟨⟩, m⟩ := q
    have hm : m ∈ BitString.shortWords L := BitString.mem_shortWords.mpr (hp m rfl)
    rw [Finset.sum_eq_single_of_mem m hm fun m' _ hm' => by simp [hm']]
    simp only [ite_true]
    exact acceptFrom_query_bind P s m next

/-- **No prover beats the value**, from any history it is in and any of its states: the
probabilities that `P` makes what remains of the programs accept sum to at most the value, when
the programs have at most `n` rounds to go. -/
private theorem sum_acceptFrom_after_le (hF : IsBounded F D L) (P : Prover Unit) (n : ℕ)
    (h : History)
    (hn : D ≤ h.length + n) (s : P.State) :
    ∑ r, acceptFrom P s (after (F r) h) ≤ value F L n h := by
  induction n generalizing h s with
  | zero =>
    simp only [value, accepted]
    rw [Finset.card_filter, Nat.cast_sum]
    refine (Finset.sum_le_sum fun r _ => ?_)
    rw [acceptFrom_after_eq P s (F r) h (fun m hm => hF.message r h m hm)]
    have hnil : ∀ m, outcome (F r) h ≠ .ask m := fun m hm => by
      have := hF.rounds r h m hm
      lia
    rw [Finset.sum_eq_zero fun m _ => ?_, add_zero]
    · split_ifs <;> simp
    · refine tsum_eq_zero_iff.mpr fun ys => ?_
      rw [after_append]
      unfold outcome at hnil
      rcases hah : after (F r) h with _ | ⟨b⟩ | ⟨q, next⟩
      · simp
      · simp
      · exact (hnil q.2 (by rw [hah])).elim
  | succ n ih =>
    simp only [Finset.sum_congr rfl fun r _ => acceptFrom_after_eq P s (F r) h
      (fun m hm => hF.message r h m hm), Finset.sum_add_distrib]
    simp only [value, Nat.cast_add, Nat.cast_sum]
    refine add_le_add ?_ ?_
    · rw [accepted, Finset.card_filter, Nat.cast_sum]
      exact (Finset.sum_congr rfl fun r _ => by split_ifs <;> simp).le
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [← Summable.tsum_finsetSum fun r _ => CompleteLattice.summable]
    calc ∑' ys : List Bool × P.State, ∑ r, (P.respond ((), m)).run s ys *
          acceptFrom P ys.2 (after (F r) (h ++ [(m, ys.1)]))
        ≤ ∑' ys : List Bool × P.State, (P.respond ((), m)).run s ys *
          ((BitString.shortWords L).sup fun y => value F L n (h ++ [(m, y)]) : ℕ) := by
          refine tsum_le_tsum fun ys => ?_
          rw [← Finset.mul_sum]
          refine mul_le_mul_right ?_ _
          refine (ih (h ++ [(m, ys.1)]) (by
            simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
            lia) ys.2).trans ?_
          rw [value_take hF]
          exact Nat.cast_le.mpr (Finset.le_sup (f := fun y => value F L n (h ++ [(m, y)]))
            (BitString.mem_shortWords.mpr (List.length_take_le _ _)))
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **No prover beats the value**: for a bounded family, every prover makes the programs accept
with probabilities summing to at most the value of the empty history. -/
theorem sum_acceptFrom_le_value (hF : IsBounded F D L) (P : Prover Unit) :
    ∑ r, acceptFrom P P.init (some (F r)) ≤ value F L D [] := by
  simpa using sum_acceptFrom_after_le hF P D [] (by simp) P.init

/-! ### The optimal prover -/

section Optimal

variable (F L)

/-- A reply of length at most `L` that is best for the message `m` after the history `h`, with `n`
rounds to go after it. -/
noncomputable def bestReply (n : ℕ) (h : History) (m : List Bool) : List Bool :=
  ((BitString.shortWords L).exists_max_image (fun y => value F L n (h ++ [(m, y)]))
    ⟨[], BitString.nil_mem_shortWords L⟩).choose

private theorem bestReply_mem (n : ℕ) (h : History) (m : List Bool) :
    bestReply F L n h m ∈ BitString.shortWords L :=
  ((BitString.shortWords L).exists_max_image (fun y => value F L n (h ++ [(m, y)]))
    ⟨[], BitString.nil_mem_shortWords L⟩).choose_spec.1

/-- The best reply attains the best value. -/
private theorem value_bestReply (n : ℕ) (h : History) (m : List Bool) :
    value F L n (h ++ [(m, bestReply F L n h m)]) =
      (BitString.shortWords L).sup fun y => value F L n (h ++ [(m, y)]) :=
  le_antisymm (Finset.le_sup (f := fun y => value F L n (h ++ [(m, y)]))
      (bestReply_mem F L n h m))
    (Finset.sup_le fun y hy =>
      ((BitString.shortWords L).exists_max_image (fun y => value F L n (h ++ [(m, y)]))
        ⟨[], BitString.nil_mem_shortWords L⟩).choose_spec.2 y hy)

/-- The optimal prover: its state is the history so far, and it answers every message with a best
reply for the rounds left of `D`. -/
noncomputable def optimalProver (D : ℕ) : Prover Unit where
  State := History
  init := []
  respond q h :=
    let y := bestReply F L (D - h.length - 1) h q.2
    PMF.pure (y, h ++ [(q.2, y)])

variable {F L}

/-- **The optimal prover attains the value** from every history it is in. -/
private theorem sum_acceptFrom_optimalProver_after (hF : IsBounded F D L) (n : ℕ) (h : History)
    (hn : h.length + n = D) :
    ∑ r, acceptFrom (optimalProver F L D) h (after (F r) h) = value F L n h := by
  induction n generalizing h with
  | zero =>
    simp only [value, accepted]
    rw [Finset.card_filter, Nat.cast_sum]
    refine (Finset.sum_congr rfl fun r _ => ?_)
    rw [acceptFrom_after_eq (optimalProver F L D) h (F r) h (fun m hm => hF.message r h m hm)]
    have hnil : ∀ m, outcome (F r) h ≠ .ask m := fun m hm => by
      have := hF.rounds r h m hm
      lia
    rw [Finset.sum_eq_zero fun m _ => ?_, add_zero]
    · split_ifs <;> simp
    · refine tsum_eq_zero_iff.mpr fun ys => ?_
      rw [after_append]
      unfold outcome at hnil
      rcases hah : after (F r) h with _ | ⟨b⟩ | ⟨q, next⟩
      · simp
      · simp
      · exact (hnil q.2 (by rw [hah])).elim
  | succ n ih =>
    classical
    simp only [Finset.sum_congr rfl fun r _ => acceptFrom_after_eq (optimalProver F L D) h (F r) h
      (fun m hm => hF.message r h m hm), Finset.sum_add_distrib]
    simp only [value, Nat.cast_add, Nat.cast_sum]
    congr 1
    · rw [accepted, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hD : D - h.length - 1 = n := by lia
    have hrespond : (optimalProver F L D).respond ((), m) h =
        (PMF.pure (bestReply F L n h m, h ++ [(m, bestReply F L n h m)]) :
          PMF (List Bool × (optimalProver F L D).State)) := by
      simp only [optimalProver, hD]
    simp only [StateT.run, hrespond, PMF.pure_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl fun r _ => tsum_ite_eq _ _, ← value_bestReply]
    exact_mod_cast ih _ (by
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
      lia)

/-- **The optimal prover attains the value**: for a bounded family, it makes the programs accept
with probabilities summing to the value of the empty history. -/
theorem sum_acceptFrom_optimalProver (hF : IsBounded F D L) :
    ∑ r, acceptFrom (optimalProver F L D) (optimalProver F L D).init (some (F r)) =
      value F L D [] := by
  have := sum_acceptFrom_optimalProver_after hF D [] (by simp)
  simp only [after_nil] at this
  exact this

end Optimal

/-! ### Replays -/

/-- The replay monad: a history to answer from, and failure with the message sent when the
history is exhausted, or with `none` when a message does not match the history. -/
abbrev ReplayM := StateT History (Except (Option (List Bool)))

/-- Answer a message from the history. -/
def replayAnswer (q : Unit × List Bool) : ReplayM (List Bool) := fun h =>
  match h with
  | [] => .error (some q.2)
  | (m, y) :: h => if m = q.2 then .ok (y, h) else .error none

/-- Run a program against a history. -/
def replay (p : WordQueryComp Unit α) : ReplayM α := OracleComp.interpret replayAnswer p

/-- The outcome of a replay: the result when it consumed the whole history, the pending message
when it ran out of history, and `invalid` otherwise. -/
def replayOutcome : Except (Option (List Bool)) (Bool × History) → Outcome
  | .ok (b, []) => .done b
  | .ok (_, _ :: _) => .invalid
  | .error (some m) => .ask m
  | .error none => .invalid

/-- **Outcomes are replays.** -/
theorem outcome_eq_replay (p : WordQueryComp Unit Bool) (h : History) :
    outcome p h = replayOutcome ((replay p).run h) := by
  induction p generalizing h with
  | pure b => cases h <;> rfl
  | liftBind q next ih =>
    obtain ⟨⟨⟩, m⟩ := q
    cases h with
    | nil => rfl
    | cons x h =>
      obtain ⟨m', y⟩ := x
      have hout : outcome (.liftBind ((), m) next) ((m', y) :: h) =
          if m' = m then outcome (next y) h else .invalid := by
        unfold outcome
        change (match (if m' = m then after (next y) h else none) with
          | none => Outcome.invalid
          | some (.pure b) => .done b
          | some (.liftBind q _) => .ask q.2) = _
        split_ifs <;> rfl
      have hrun : (replay (.liftBind ((), m) next)).run ((m', y) :: h) =
          if m' = m then (replay (next y)).run h else .error none := by
        change (replayAnswer ((), m) >>= fun u => replay (next u)).run ((m', y) :: h) = _
        rw [StateT.run_bind]
        change (if m' = m then (Except.ok (y, h) : Except (Option (List Bool)) _)
          else .error none) >>= _ = _
        split_ifs <;> rfl
      rw [hout, hrun]
      split_ifs
      · exact ih y h
      · rfl

end Cslib.Complexity.Interaction
