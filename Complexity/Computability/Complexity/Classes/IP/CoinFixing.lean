/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.OptimalProver
public import Complexity.Computability.Machines.Turing.MultiTape.FiniteConfiguration
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Probability.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
import Complexity.Foundations.Control.Monad.IsMonadHom.StateT
import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Fixing the coins of a verifier machine

An `IP` verifier is realized by the clocked run of a finite fair-coin oracle machine `M`
(`Cslib.Probability.IsOraclePPTOn`). Every live instruction of the run draws one fresh coin, so a
run of `t` instructions is determined by `t` coins and the replies. Fixing the coins `r` and
truncating every reply to its first `t` bits, which the run cannot read beyond, leaves the program
`Cslib.Complexity.Interaction.coinProgram M t x r` making word requests. Against every stateful
prover the run is the average of these programs over uniform coins
(`Cslib.Complexity.Interaction.run_interpret_runOracle_eq_coins`), so the acceptance probability of
the verifier is the average of the acceptance probabilities of the programs
(`Cslib.Complexity.Interaction.acceptProb_eq_sum`).

A deterministic replay of a program against a history executes one instruction per coin, answering
the messages from the history (`Cslib.Complexity.Interaction.replayStep`,
`Cslib.Complexity.Interaction.simulate`); it computes the outcome of the program
(`Cslib.Complexity.Interaction.outcome_coinProgram`). Along the replay the machine sends at most one
message per instruction, of length at most the number of instructions so far, and reads replies only
through their first `t` bits. So the programs of `t` coins form a bounded family, with at most `t`
messages, each of length less than `t` (`Cslib.Complexity.Interaction.isBounded_coinFamily`).

## Main definitions

* `Cslib.Complexity.Interaction.coinStep`, `Cslib.Complexity.Interaction.coinProgram`: the program
  of fixed coins.
* `Cslib.Complexity.Interaction.replayStep`, `Cslib.Complexity.Interaction.simulate`: the
  deterministic replay.

## Main results

* `Cslib.Complexity.Interaction.run_interpret_runOracle_eq_coins`: the run averages the programs of
  fixed coins.
* `Cslib.Complexity.Interaction.acceptProb_eq_sum`: acceptance averages over the coins.
* `Cslib.Complexity.Interaction.outcome_coinProgram`: outcomes are replays.
* `Cslib.Complexity.Interaction.isBounded_coinFamily`: the programs form a bounded family.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.Interaction

open Cslib.Probability _root_.Turing _root_.Turing.MultiTapeMachine

section CoinFixing

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (M : MultiTapePTM k Bool Control Operation)

/-! ### Programs of fixed coins -/

/-- One instruction of `M` with the coin `b`, its replies truncated to their first `t` bits. -/
def coinStep (t : ℕ) (cfg : FiniteConfig k Bool Control Operation) (b : Bool) :
    WordQueryComp Operation (FiniteConfig k Bool Control Operation) :=
  M.finiteStep (fun choices => choices <$> pure b)
    (fun op w => List.take t <$> OracleComp.query (op, w)) cfg

/-- The verifier `M` on the input `x` with the coins `r`, one per instruction, its replies truncated
to their first `t` bits; it accepts when its output is `[true]`. -/
def coinProgram (t : ℕ) (x r : List Bool) : WordQueryComp Operation Bool :=
  (fun cfg => decide (cfg.tapes.output = [true])) <$>
    r.foldlM (coinStep M t) (FiniteConfig.init M.initial x)

/-- The family of the programs of `t` coins. -/
def coinFamily (t : ℕ) (x : List Bool) (r : Fin t → Bool) : WordQueryComp Operation Bool :=
  coinProgram M t x (List.ofFn r)

variable {S : Type} (oracle : Operation × List Bool → StateT S PMF (List Bool))

/-- The handler of the private coins and of the prover `o`. -/
local notation "handler" o =>
  ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) o

/-- An instruction with a fixed coin makes the requests of `coinStep`. -/
private theorem run_interpret_finiteStep_pure (t : ℕ)
    (cfg : FiniteConfig k Bool Control Operation) (b : Bool) (s : S) :
    (OracleComp.interpret (handler oracle) (M.finiteStep (fun choices => choices <$> pure b)
      (fun op w => List.take t <$> ProbOracleComp.query (op, w)) cfg)).run s =
      (OracleComp.interpret oracle (coinStep M t cfg b)).run s := by
  unfold coinStep MultiTapeMachine.finiteStep
  cases cfg.tapes.state with
  | none => rfl
  | some c =>
    simp only [map_pure, pure_bind]
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step => rfl
    | query op next =>
      simp only [bind_map_left, OracleComp.interpret_bind, ProbOracleComp.interpret_query,
        OracleComp.interpret_query, OracleComp.interpret_pure]

/-- Instructions with fixed coins make the requests of `coinStep`. -/
private theorem run_interpret_foldlM_pure (t : ℕ) (r : List Bool)
    (cfg : FiniteConfig k Bool Control Operation) (s : S) :
    (OracleComp.interpret (handler oracle) (r.foldlM (fun cfg b => M.finiteStep
      (fun choices => choices <$> pure b)
      (fun op w => List.take t <$> ProbOracleComp.query (op, w)) cfg) cfg)).run s =
      (OracleComp.interpret oracle (r.foldlM (coinStep M t) cfg)).run s := by
  induction r generalizing cfg s with
  | nil => rfl
  | cons b r ih =>
    simp only [List.foldlM_cons, OracleComp.interpret_bind, StateT.run_bind,
      run_interpret_finiteStep_pure, ih]

/-- An instruction drawing a fair coin averages the instructions with fixed coins. -/
private theorem run_interpret_finiteStep_sample
    (query : Operation → List Bool →
      ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool))
    (cfg : FiniteConfig k Bool Control Operation) (s : S) :
    (OracleComp.interpret (handler oracle) (M.finiteStep
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool)) query cfg)).run s =
      (PMF.uniformOfFintype Bool).bind fun b =>
        (OracleComp.interpret (handler oracle) (M.finiteStep (fun choices => choices <$> pure b)
          query cfg)).run s := by
  unfold MultiTapeMachine.finiteStep
  cases cfg.tapes.state with
  | none =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.bind_const]
  | some c =>
    simp only [map_pure, pure_bind, bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      MultiTapePTM.run_interpret_sample_uniform_bool, Probability.PMF.monad_bind_eq_bind,
      PMF.bind_map]
    rfl

/-- A clocked loop drawing fair coins averages the loops with fixed coins. -/
private theorem run_interpret_iterate_eq_coins
    (query : Operation → List Bool →
      ProbOracleComp (fun _ : Operation × List Bool => List Bool) (List Bool))
    (n : ℕ) (cfg : FiniteConfig k Bool Control Operation) (s : S) :
    (OracleComp.interpret (handler oracle) (OracleComp.iterate n (M.finiteStep
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool)) query)
        cfg)).run s =
      (BitString.uniformList n).bind fun r =>
        (OracleComp.interpret (handler oracle) (r.foldlM (fun cfg b => M.finiteStep
          (fun choices => choices <$> pure b) query cfg) cfg)).run s := by
  induction n generalizing cfg s with
  | zero => simp
  | succ n ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, run_interpret_finiteStep_sample,
      BitString.uniformList_succ, PMF.bind_bind, PMF.bind_bind]
    congr 1
    funext b
    simp only [ih, PMF.bind_map, Function.comp_def, List.foldlM_cons, OracleComp.interpret_bind,
      StateT.run_bind, Probability.PMF.monad_bind_eq_bind]
    exact PMF.bind_comm _ _ _

/-- **The run averages the programs of fixed coins**, against every stateful prover, retaining its
final state. -/
theorem run_interpret_runOracle_eq_coins (t : ℕ) (x : List Bool) (s : S) :
    (OracleComp.interpret (handler oracle) (M.runOracle t x)).run s =
      (BitString.uniformList t).bind fun r =>
        (OracleComp.interpret oracle ((fun cfg => cfg.tapes.output) <$>
          r.foldlM (coinStep M t) (FiniteConfig.init M.initial x))).run s := by
  rw [← MultiTapePTM.finiteRunFrom_take_runOracle, MultiTapeMachine.finiteRunFrom,
    OracleComp.interpret_map, StateT.run_map, run_interpret_iterate_eq_coins,
    _root_.PMF.monad_map_eq_map, PMF.map_bind]
  congr 1
  funext r
  rw [OracleComp.interpret_map, StateT.run_map, run_interpret_foldlM_pure,
    _root_.PMF.monad_map_eq_map]

/-- **Acceptance averages over the coins.** If the verifier `V` is realized by the run of `M` under
the clock `t`, then its acceptance probability against `P` averages the acceptance probabilities of
the programs of fixed coins. -/
theorem acceptProb_eq_sum {V : WordOracleComp Operation Bool} {t : ℕ} {x : List Bool}
    (hV : ∀ (S : Type) (oracle : Operation × List Bool → StateT S PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (Turing.MultiTapeTM.encBool <$> V)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (M.runOracle t x)).run s)
    (P : Prover Operation) :
    acceptProb V P =
      (2 ^ t)⁻¹ * ∑ r : Fin t → Bool,
        acceptFrom P P.init (some (coinProgram M t x (List.ofFn r))) := by
  have h := congrArg (fun μ => μ.map (fun z => decide (z.1 = [true])) true)
    (hV P.State P.respond P.init)
  rw [OracleComp.interpret_map, StateT.run_map, run_interpret_runOracle_eq_coins,
    _root_.PMF.monad_map_eq_map, PMF.map_comp] at h
  have hl : acceptProb V P = ((OracleComp.interpret (ProbOracleComp.handler
      (fun n => StateT.lift (ProbComp.unifOracle n)) P.respond) V).run P.init).map
        ((fun z => decide (z.1 = [true])) ∘ fun p => (Turing.MultiTapeTM.encBool p.1, p.2))
          true := by
    rw [acceptProb]
    congr 2
    funext z
    obtain ⟨_ | _, _⟩ := z <;> rfl
  rw [hl, h, PMF.map_bind, BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Function.comp_apply, coinProgram, acceptFrom, OracleComp.interpret_map, StateT.run_map,
    _root_.PMF.monad_map_eq_map, PMF.map_comp, OracleComp.interpret_map, StateT.run_map,
    _root_.PMF.monad_map_eq_map, PMF.map_comp, Nat.cast_pow, Nat.cast_ofNat]
  rfl

end CoinFixing

variable {k : ℕ} {Control : Type} (M : MultiTapePTM k Bool Control Unit)

/-! ### The replay -/

/-- One instruction of `M` with the coin `b`, answering a message from the history, if any;
failing with the message when the history is exhausted, and with `none` when the message differs
from the history. -/
def replayStep (t : ℕ) (p : FiniteConfig k Bool Control Unit × History) (b : Bool) :
    Except (Option (List Bool)) (FiniteConfig k Bool Control Unit × History) :=
  match p.1.tapes.state with
  | none => .ok p
  | some c =>
    match M.tr c p.1.tapes.inputSymbol p.1.tapes.workTapeSymbols p.1.answerSymbols b with
    | .step action symbol move => .ok (p.1.step action symbol move, p.2)
    | .query op next =>
      match p.2 with
      | [] => .error (some (p.1.channels op).1)
      | (m, y) :: h =>
        if m = (p.1.channels op).1 then .ok (p.1.receive op next (y.take t), h) else .error none

/-- The replay of `M` on the input `x` with the coins `r` against the history `h`. -/
def simulate (t : ℕ) (x r : List Bool) (h : History) :
    Except (Option (List Bool)) (FiniteConfig k Bool Control Unit × History) :=
  r.foldl (fun acc b => do
    let p ← acc
    replayStep M t p b)
    (.ok (FiniteConfig.init M.initial x, h))

/-- The replay of an instruction is `replayStep`. -/
private theorem replay_coinStep (t : ℕ) (cfg : FiniteConfig k Bool Control Unit) (b : Bool)
    (h : History) :
    (replay (coinStep M t cfg b)).run h = replayStep M t (cfg, h) b := by
  unfold coinStep MultiTapeMachine.finiteStep replayStep
  simp only
  cases cfg.tapes.state with
  | none => rfl
  | some c =>
    simp only [map_pure, pure_bind]
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step => rfl
    | query op next =>
      simp only [replay, bind_map_left, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure, StateT.run_bind]
      cases h with
      | nil => rfl
      | cons x h =>
        obtain ⟨m, y⟩ := x
        change (if m = (cfg.channels op).1 then (Except.ok (y, h) : Except (Option (List Bool)) _)
          else .error none) >>= _ = _
        split_ifs with hm <;> simp [hm]

/-- A replay of a fold is a fold of replays. -/
private theorem replay_foldlM {β γ : Type} (f : β → γ → WordQueryComp Unit β) (l : List γ)
    (b : β) :
    replay (l.foldlM f b) = l.foldlM (fun b c => replay (f b c)) b :=
  (PFunctor.FreeM.isMonadHom_liftM (P := ⟨Unit × List Bool, fun _ => List Bool⟩)
    replayAnswer).map_listFoldlM _ _ _

/-- **Outcomes are replays**: the outcome of the program of the coins `r` after the history `h` is
read off the replay. -/
theorem outcome_coinProgram (t : ℕ) (x r : List Bool) (h : History) :
    outcome (coinProgram M t x r) h = replayOutcome ((simulate M t x r h).map fun p =>
      (decide (p.1.tapes.output = [true]), p.2)) := by
  rw [outcome_eq_replay]
  congr 1
  rw [coinProgram, replay, OracleComp.interpret_map, StateT.run_map, ← replay, replay_foldlM,
    StateT.foldlM_run_except]
  simp only [replay_coinStep, simulate]
  rfl

/-! ### Bounds on the replay -/

/-- The invariant of the replay after `i` instructions against `h`: a live replay has consumed at
most `i` entries of `h` and its storage is bounded; a replay out of history has consumed all of `h`
within fewer than `i` instructions and its message is shorter than `i`. -/
def ReplayInv (t : ℕ) (x : List Bool) (h : History) (i : ℕ) :
    Except (Option (List Bool)) (FiniteConfig k Bool Control Unit × History) → Prop
  | .ok (cfg, rest) => (∃ pre, h = pre ++ rest ∧ pre.length ≤ i) ∧
      FiniteConfig.SpaceBound x.length i t cfg
  | .error (some m) => h.length < i ∧ m.length < i
  | .error none => True

/-- An instruction of the replay preserves the invariant. -/
private theorem replayInv_step {t : ℕ} {x : List Bool} {h : History} {i : ℕ}
    {acc : Except (Option (List Bool)) (FiniteConfig k Bool Control Unit × History)}
    (hacc : ReplayInv t x h i acc) (b : Bool) :
    ReplayInv t x h (i + 1) (acc.bind fun p => replayStep M t p b) := by
  rcases acc with (_ | ⟨m⟩) | ⟨cfg, rest⟩
  · trivial
  · exact ⟨by have := hacc.1; lia, by have := hacc.2; lia⟩
  · obtain ⟨⟨pre, hpre, hlen⟩, hspace⟩ := hacc
    change ReplayInv t x h (i + 1) (replayStep M t (cfg, rest) b)
    unfold replayStep
    simp only
    cases hs : cfg.tapes.state with
    | none => exact ⟨⟨pre, hpre, by lia⟩, hspace.mono le_rfl (by lia) le_rfl⟩
    | some c =>
      simp only
      cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
      | step action symbol move =>
        exact ⟨⟨pre, hpre, by lia⟩, hspace.step action symbol move⟩
      | query op next =>
        simp only
        cases rest with
        | nil =>
          refine ⟨by rw [hpre, List.append_nil]; lia, ?_⟩
          have := hspace.query op
          lia
        | cons e rest =>
          obtain ⟨m, y⟩ := e
          simp only
          split_ifs
          · refine ⟨⟨pre ++ [(m, y)], by simp [hpre], by
              simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
              lia⟩, ?_⟩
            exact hspace.receive op next _ (List.length_take_le _ _)
          · trivial

/-- The replay satisfies the invariant after all its coins. -/
private theorem replayInv_simulate (t : ℕ) (x : List Bool) (h : History) (r : List Bool) :
    ReplayInv t x h r.length (simulate M t x r h) := by
  suffices ∀ (l : List Bool) (acc) (i : ℕ), ReplayInv t x h i acc →
      ReplayInv t x h (i + l.length)
        (l.foldl (fun acc b => acc.bind fun p => replayStep M t p b) acc) by
    simpa [simulate, bind] using this r (.ok (FiniteConfig.init M.initial x, h)) 0
      ⟨⟨[], rfl, le_rfl⟩, FiniteConfig.spaceBound_init _ _ _⟩
  intro l
  induction l with
  | nil => intro acc i hacc; simpa using hacc
  | cons b l ih =>
    intro acc i hacc
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih _ _ (replayInv_step M hacc b)

/-- Truncate every reply of a history to its first `t` bits. -/
private def truncate (t : ℕ) (h : History) : History := h.map fun e => (e.1, e.2.take t)

/-- An instruction of the replay reads replies only through their first `t` bits. -/
private theorem replayStep_truncate (t : ℕ) (cfg : FiniteConfig k Bool Control Unit) (h : History)
    (b : Bool) :
    (replayStep M t (cfg, h) b).map (fun p => (p.1, truncate t p.2)) =
      (replayStep M t (cfg, truncate t h) b).map (fun p => (p.1, truncate t p.2)) := by
  unfold replayStep
  simp only
  cases cfg.tapes.state with
  | none => simp [Except.map, truncate, List.map_map, Function.comp_def, List.take_take]
  | some c =>
    simp only
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step => simp [Except.map, truncate, List.map_map, Function.comp_def, List.take_take]
    | query op next =>
      simp only
      cases h with
      | nil => rfl
      | cons e h =>
        obtain ⟨m, y⟩ := e
        simp only [truncate, List.map_cons, List.take_take, min_self]
        split_ifs <;> simp [Except.map, List.map_map, Function.comp_def, List.take_take]

/-- The replay reads replies only through their first `t` bits. -/
private theorem simulate_truncate (t : ℕ) (x r : List Bool) {h h' : History}
    (hh : truncate t h = truncate t h') :
    (simulate M t x r h).map (fun p => (p.1, truncate t p.2)) =
      (simulate M t x r h').map (fun p => (p.1, truncate t p.2)) := by
  suffices ∀ (l : List Bool) (acc acc' : Except (Option (List Bool)) _),
      acc.map (fun p => (p.1, truncate t p.2)) = acc'.map (fun p => (p.1, truncate t p.2)) →
      (l.foldl (fun acc b => acc.bind fun p => replayStep M t p b) acc).map
          (fun p => (p.1, truncate t p.2)) =
        (l.foldl (fun acc b => acc.bind fun p => replayStep M t p b) acc').map
          (fun p => (p.1, truncate t p.2)) from
    this r _ _ (by simp [Except.map, hh])
  intro l
  induction l with
  | nil => exact fun _ _ h => h
  | cons b l ih =>
    intro acc acc' hacc
    refine ih _ _ ?_
    rcases acc with e | ⟨cfg, rest⟩ <;> rcases acc' with e' | ⟨cfg', rest'⟩ <;>
      simp only [Except.map, Except.error.injEq, Except.ok.injEq, reduceCtorEq,
        Prod.mk.injEq] at hacc
    · subst hacc
      rfl
    · obtain ⟨rfl, hrest⟩ := hacc
      change (replayStep M t (cfg, rest) b).map _ = (replayStep M t (cfg, rest') b).map _
      rw [replayStep_truncate, hrest, ← replayStep_truncate]

/-- **The programs of `t` coins form a bounded family**: at most `t` messages, each of length at
most `t`, and only the first `t` bits of each reply matter. -/
theorem isBounded_coinFamily (t : ℕ) (x : List Bool) :
    IsBounded (coinFamily M t x) t t where
  rounds r h m hm := by
    have hinv := replayInv_simulate M t x h (List.ofFn r)
    rw [coinFamily, outcome_coinProgram] at hm
    rcases hs : simulate M t x (List.ofFn r) h with (_ | ⟨m'⟩) | ⟨cfg, _ | ⟨_, _⟩⟩ <;>
      simp only [hs, Except.map, replayOutcome, reduceCtorEq] at hm
    rw [hs, List.length_ofFn] at hinv
    exact hinv.1
  message r h m hm := by
    have hinv := replayInv_simulate M t x h (List.ofFn r)
    rw [coinFamily, outcome_coinProgram] at hm
    rcases hs : simulate M t x (List.ofFn r) h with (_ | ⟨m'⟩) | ⟨cfg, _ | ⟨_, _⟩⟩ <;>
      simp only [hs, Except.map, replayOutcome, reduceCtorEq, Outcome.ask.injEq] at hm
    subst hm
    rw [hs, List.length_ofFn] at hinv
    exact hinv.2.le
  reply r h m y e := by
    simp only [coinFamily, outcome_coinProgram]
    have hsim := simulate_truncate M t x (List.ofFn r)
      (h := h ++ (m, y) :: e) (h' := h ++ (m, y.take t) :: e)
      (by simp [truncate, List.take_take])
    have key (z : Except (Option (List Bool)) (FiniteConfig k Bool Control Unit × History)) :
        replayOutcome (z.map fun p => (decide (p.1.tapes.output = [true]), p.2)) =
          replayOutcome ((z.map fun p => (p.1, truncate t p.2)).map fun p =>
            (decide (p.1.tapes.output = [true]), p.2)) := by
      rcases z with (_ | _) | ⟨cfg, _ | ⟨_, _⟩⟩ <;> rfl
    rw [key, hsim, ← key]

end Cslib.Complexity.Interaction
