/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Forking
public import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Bind

/-!
# The forking reduction for Fiat–Shamir in the random-oracle model

Fiat–Shamir signatures and Fiat–Shamir non-interactive proofs are proved secure by the same
reduction ([BonehShoup2023], Theorems 19.16 and 20.3.4, with the general forking lemma of
[BellareNeven2006], Lemma 1). The adversary makes signing (or proving) calls and hash calls and
outputs a candidate `(m, (t, z))`: a message or statement `m` and a transcript commitment `t` and
response `z`. The reduction runs it as a program over its own hash oracle alone:

* signing calls are answered without a secret, from one presampled value per call, and may
  program the oracle table at a point and log an entry (`Signer`);
* hash calls are answered from the table, or by the reduction's own oracle, recording the
  position of each such query;
* the candidate wins when its transcript at `point m t` is accepting and it was not produced by
  a logged signing call (`Check`); the reduction then names the position of the query for that
  point.

This module states the reduction once (`ForkingReduction.program`) and proves the facts every
security proof needs: with its oracle answered uniformly, it has the winning law of the adversary
against the presampled game signer (`map_run_program`); it names a valid query whenever it wins,
so the forking lemma bounds the winning probability (`toReal_le_add_sqrt_fork_of_le`); and a
successful fork yields two accepting candidates at the same point with different challenges
(`exists_of_mem_support_fork`). The only assumption linking signer and check is
`RejectsProgrammed`: a candidate at a programmed point whose log entry is logged is not fresh.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.Signer`,
  `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.Check`: the scheme-specific parts.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.handler`: the reduction's answers to the
  adversary's calls.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.program`: the adversary with simulated
  signing, as a program over the hash oracle naming the query of its candidate.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.gameHandler`,
  `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.finishGame`: the corresponding game, with
  the lazy random oracle.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.map_run_program`: the reduction simulates
  the game.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.runWithAnswers_program`: the reduction's
  runs on fixed answers.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.toReal_le_add_sqrt_fork_of_le`: the
  forking lemma for the reduction.
* `Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction.exists_of_mem_support_fork`: extraction
  data from a successful fork.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.6.1 and 20.3.4.
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction

open Probability OracleComp ROMSignature
open scoped ENNReal

variable {Req Reply M T C Z Point Log S : Type}

/-- The state of the reduction while it runs the adversary: the oracle table, each point with its
challenge and, when the reduction asked its own oracle for the point, the position of that query;
the entries logged by signing calls; the number of queries asked so far; and the presampled values
not used yet. -/
structure State (Point C Log S : Type) where
  /-- The oracle table. -/
  table : List (Point × C × Option ℕ)
  /-- The entries logged by signing calls. -/
  log : List Log
  /-- The number of queries asked so far. -/
  count : ℕ
  /-- The presampled values not used yet. -/
  samples : List S

/-- How the reduction answers a signing call `q` without a secret, from one presampled value `s`:
it returns `(step s q).1` and, when `(step s q).2 = some (x, c, l)`, programs the oracle at `x` with
`c` and logs `l`. -/
structure Signer (Req Reply Point C Log S : Type) where
  /-- The value used once the presampled values run out. -/
  fallback : S
  /-- The reply to a call and what it programs and logs. -/
  step : S → Req → Reply × Option (Point × C × Log)

/-- The final check on a candidate `(m, (t, z))`: its challenge is the oracle's value at
`point m t`, and it wins when `accepts m t c z` and `fresh m t log`. -/
structure Check (M T C Z Point Log : Type) where
  /-- The oracle point of a candidate. -/
  point : M → T → Point
  /-- Whether the candidate's transcript is accepting. -/
  accepts : M → T → C → Z → Bool
  /-- Whether the candidate was not produced by a logged signing call. -/
  fresh : M → T → List Log → Bool

/-- Program the table at `x` with `c` and log `l`, when a signing call asks to. -/
def State.record (st : State Point C Log S) : Option (Point × C × Log) → State Point C Log S
  | none => st
  | some (x, c, l) => { st with table := (x, c, none) :: st.table, log := l :: st.log }

/-- The game's version of `State.record`, on the lazy oracle's table and the log. -/
def recordGame (st : List (Point × C) × List Log) :
    Option (Point × C × Log) → List (Point × C) × List Log
  | none => st
  | some (x, c, l) => ((x, c) :: st.1, l :: st.2)

/-- No candidate at a point the signer programmed is fresh once that call's log entry is logged.
This is what makes a winning candidate name its own hash query. -/
def RejectsProgrammed (σ : Signer Req Reply Point C Log S) (κ : Check M T C Z Point Log) : Prop :=
  ∀ s q x c l, (σ.step s q).2 = some (x, c, l) →
    ∀ m t log, κ.point m t = x → l ∈ log → κ.fresh m t log = false

variable [DecidableEq Point]

/-- Answer the adversary's calls without a secret, consuming one presampled value per call. A
signing call follows the signer. A hash call returns the table's challenge, or asks the
reduction's own oracle and records the answer with the position of the query. -/
def handler (σ : Signer Req Reply Point C Log S) :
    (q : Req ⊕ Point) → StateT (State Point C Log S) (OracleComp (fun _ : Point => C))
      (ForgerSpec Req Point Reply C q)
  | .inl q => fun st =>
    pure ((σ.step (st.samples.headD σ.fallback) q).1,
      { st.record (σ.step (st.samples.headD σ.fallback) q).2 with samples := st.samples.tail })
  | .inr x => fun st =>
    match st.table.lookup x with
    | some entry => pure (entry.1, { st with samples := st.samples.tail })
    | none => (fun c => (c, ⟨(x, c, some st.count) :: st.table, st.log, st.count + 1,
        st.samples.tail⟩)) <$> OracleComp.query x

/-- The outcome of the final check: whether the candidate won, the candidate and its
challenge. -/
structure Outcome (M T C Z : Type) where
  /-- Whether the candidate won. -/
  won : Bool
  /-- The candidate's message or statement. -/
  message : M
  /-- The candidate's commitment. -/
  commitment : T
  /-- The challenge at the candidate's point. -/
  challenge : C
  /-- The candidate's response. -/
  response : Z

/-- The verdict on a candidate whose point has challenge `c`: when it wins, the reduction names
`position`, the position of the query for its point. -/
def verdict (κ : Check M T C Z Point Log) (cand : (M × (T × Z)) × State Point C Log S) (c : C)
    (position : Option ℕ) : Option ℕ × Outcome M T C Z :=
  let ((m, t, z), st) := cand
  let won := κ.accepts m t c z && κ.fresh m t st.log
  (if won then position else none, ⟨won, m, t, c, z⟩)

/-- Check a candidate, querying its point when the table lacks it. -/
def finish (κ : Check M T C Z Point Log) (cand : (M × (T × Z)) × State Point C Log S) :
    OracleComp (fun _ : Point => C) (Option ℕ × Outcome M T C Z) :=
  let ((m, t, _), st) := cand
  match st.table.lookup (κ.point m t) with
  | some entry => pure (verdict κ cand entry.1 entry.2)
  | none => (fun c => verdict κ cand c (some st.count)) <$> OracleComp.query (κ.point m t)

/-- **The reduction.** The adversary `A`, with signing calls answered by `σ` from `samples`, as a
program over the hash oracle alone. It names the query of the candidate's point when the
candidate wins. -/
def program (σ : Signer Req Reply Point C Log S) (κ : Check M T C Z Point Log)
    (A : OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z))) (samples : List S) :
    OracleComp (fun _ : Point => C) (Option ℕ × Outcome M T C Z) :=
  (interpret (handler σ) A).run ⟨[], [], 0, samples⟩ >>= finish κ

/-- The game's view of the reduction's state: the table without positions, the log, and the unused
values. -/
private def State.toGame (st : State Point C Log S) : (List (Point × C) × List Log) × List S :=
  ((st.table.map fun e => (e.1, e.2.1), st.log), st.samples)

private theorem run_handler_inl (σ : Signer Req Reply Point C Log S) (q : Req)
    (st : State Point C Log S) :
    (handler σ (.inl q)).run st =
      pure ((σ.step (st.samples.headD σ.fallback) q).1,
        { st.record (σ.step (st.samples.headD σ.fallback) q).2 with
          samples := st.samples.tail }) := rfl

private theorem run_handler_inr_some (σ : Signer Req Reply Point C Log S) {x : Point}
    {st : State Point C Log S} {e : C × Option ℕ} (h : st.table.lookup x = some e) :
    (handler σ (.inr x)).run st = pure (e.1, { st with samples := st.samples.tail }) := by
  simp only [handler, StateT.run, h]

private theorem run_handler_inr_none (σ : Signer Req Reply Point C Log S) {x : Point}
    {st : State Point C Log S} (h : st.table.lookup x = none) :
    (handler σ (.inr x)).run st =
      (fun c => (c, ⟨(x, c, some st.count) :: st.table, st.log, st.count + 1,
        st.samples.tail⟩)) <$> OracleComp.query x := by
  simp only [handler, StateT.run, h]

section Game

variable [Fintype C] [Nonempty C]

/-- The game's signer from one value `s`: signing calls follow the signer, programming the lazy
oracle's table, and hash calls are answered by the lazy random oracle. -/
noncomputable def gameHandler (σ : Signer Req Reply Point C Log S) (s : S) :
    (q : Req ⊕ Point) → StateT (List (Point × C) × List Log) PMF (ForgerSpec Req Point Reply C q)
  | .inl q => fun st => PMF.pure ((σ.step s q).1, recordGame st (σ.step s q).2)
  | .inr x => fun st => (oracle C x st.1).map fun r => (r.1, (r.2, st.2))

/-- The game's final check: query the candidate's point on the lazy oracle and test it. -/
noncomputable def finishGame (κ : Check M T C Z Point Log)
    (cand : (M × (T × Z)) × (List (Point × C) × List Log)) : PMF Bool :=
  let ((m, t, z), table, log) := cand
  (oracle C (κ.point m t) table).map fun r => κ.accepts m t r.1 z && κ.fresh m t log

/-! ### The reduction simulates the game -/

omit [DecidableEq Point] in
private theorem run_interpret_countingUniform_pure {β : Type} (b : β) (n : ℕ) :
    (interpret countingUniform (pure b : OracleComp (fun _ : Point => C) β)).run n =
      PMF.pure (b, n) := rfl

omit [DecidableEq Point] in
private theorem run_countingUniform (x : Point) (n : ℕ) :
    (countingUniform (H := C) x).run n = (PMF.uniformOfFintype C).map (·, n + 1) := rfl

/-- One call of the reduction's handler, with its oracle answered uniformly and counted, is a call
of the game's signer in the game's view. -/
private theorem combined_step (σ : Signer Req Reply Point C Log S) (q : Req ⊕ Point)
    (s : State Point C Log S × ℕ) :
    ((fun result => (result.1.1, result.1.2, result.2)) <$>
      (interpret countingUniform ((handler σ q).run s.1)).run s.2).map
        (fun x => (x.1, x.2.1.toGame)) =
      withSampleList σ.fallback (gameHandler σ) q s.1.toGame := by
  cases q with
  | inl q =>
    obtain ⟨st, n⟩ := s
    rw [run_handler_inl, run_interpret_countingUniform_pure]
    simp only [PMF.monad_map_eq_map, PMF.pure_map, withSampleList, gameHandler, State.toGame]
    cases (σ.step (st.samples.headD σ.fallback) q).2 <;> rfl
  | inr x =>
    cases h : s.1.table.lookup x with
    | some e =>
      have hcache : s.1.toGame.1.1.lookup x = some e.1 := by
        rw [State.toGame, List.lookup_map_snd, h]
        rfl
      rw [run_handler_inr_some σ h]
      simp only [run_interpret_countingUniform_pure, PMF.monad_map_eq_map, PMF.pure_map,
        withSampleList, gameHandler]
      rw [oracle, memoize_of_some _ _ _ _ hcache]
      simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
      rfl
    | none =>
      have hcache : s.1.toGame.1.1.lookup x = none := by
        rw [State.toGame, List.lookup_map_snd, h]
        rfl
      rw [run_handler_inr_none σ h]
      simp only [interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
        withSampleList, gameHandler]
      rw [oracle, memoize_of_none _ _ _ hcache]
      simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
      rfl

/-- The reduction's final check, with its oracle answered uniformly, wins exactly when the game's
final check does. -/
private theorem map_run_finish (κ : Check M T C Z Point Log) (cand : M × (T × Z))
    (st : State Point C Log S) (n : ℕ) :
    ((interpret countingUniform (finish κ (cand, st))).run n).map (fun run => run.1.2.won) =
      finishGame κ (cand, st.toGame.1) := by
  obtain ⟨m, t, z⟩ := cand
  cases h : st.table.lookup (κ.point m t) with
  | some e =>
    have hcache : st.toGame.1.1.lookup (κ.point m t) = some e.1 := by
      rw [State.toGame, List.lookup_map_snd, h]
      rfl
    simp only [finish, h, run_interpret_countingUniform_pure, PMF.pure_map, finishGame, verdict]
    rw [oracle, memoize_of_some _ _ _ _ hcache]
    simp only [PMF.monad_pure_eq_pure, PMF.pure_map]
    rfl
  | none =>
    have hcache : st.toGame.1.1.lookup (κ.point m t) = none := by
      rw [State.toGame, List.lookup_map_snd, h]
      rfl
    simp only [finish, h, interpret_map, interpret_query, StateT.run_map, PMF.monad_map_eq_map,
      finishGame, verdict]
    rw [oracle, memoize_of_none _ _ _ hcache]
    simp only [run_countingUniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_apply]
    rfl

/-- **The reduction simulates the game.** With its oracle answered uniformly, the reduction wins
exactly when the adversary wins against the game's signer with the same presampled values. -/
theorem map_run_program (σ : Signer Req Reply Point C Log S) (κ : Check M T C Z Point Log)
    (A : OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z))) (samples : List S) :
    ((interpret countingUniform (program σ κ A samples)).run 0).map
        (fun ((_, outcome), _) => outcome.won) =
      ((interpret (withSampleList σ.fallback (gameHandler σ)) A).run (([], []), samples)).bind
        fun (cand, game, _) => finishGame κ (cand, game) := by
  have hsim := run_interpret_map_state _ (withSampleList σ.fallback (gameHandler σ))
    (fun s : State Point C Log S × ℕ => s.1.toGame) (combined_step σ) A (⟨[], [], 0, samples⟩, 0)
  rw [show (⟨[], [], 0, samples⟩ : State Point C Log S).toGame = (([], []), samples) from rfl]
    at hsim
  rw [program, interpret_bind, StateT.run_bind, run_interpret_run_interpret, ← hsim]
  simp only [pmf_norm]
  exact congrArg (PMF.bind _) (funext fun r => map_run_finish κ r.1 r.2.1 r.2.2)

end Game

/-! ### The reduction's runs on fixed answers -/

/-- The invariant of the reduction's run on a list of answers, given the queries asked so far: the
count is their number; an entry with a position records the query at that position and its
answer; an entry without one was programmed by a signing call whose entry is logged. -/
private def Consistent (default : C) (answers : List C) (σ : Signer Req Reply Point C Log S)
    (st : State Point C Log S) (queries : List Point) : Prop :=
  st.count = queries.length ∧
    (∀ x c i, (x, c, some i) ∈ st.table →
      queries[i]? = some x ∧ answers.getD i default = c) ∧
    ∀ x c, (x, c, none) ∈ st.table → ∃ s q l, (σ.step s q).2 = some (x, c, l) ∧ l ∈ st.log

/-- Every call of the reduction's handler preserves the invariant. -/
private theorem consistent_step (default : C) (answers : List C)
    (σ : Signer Req Reply Point C Log S) (q : Req ⊕ Point) (st : State Point C Log S)
    (queries : List Point) (h : Consistent default answers σ st queries) :
    Consistent default answers σ
      (runWithAnswers default ((handler σ q).run st) (answers.drop queries.length)).1.2
      (queries ++ (runWithAnswers default ((handler σ q).run st)
        (answers.drop queries.length)).2) := by
  obtain ⟨hcount, hpos, hprog⟩ := h
  cases q with
  | inl q =>
    rw [run_handler_inl, runWithAnswers_pure, List.append_nil]
    cases hr : (σ.step (st.samples.headD σ.fallback) q).2 with
    | none => exact ⟨hcount, hpos, hprog⟩
    | some r =>
      obtain ⟨x, c, l⟩ := r
      refine ⟨hcount, fun x' c' i hx => ?_, fun x' c' hx => ?_⟩
      · simp only [State.record, List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false,
          false_or] at hx
        exact hpos x' c' i hx
      · simp only [State.record, List.mem_cons, Prod.mk.injEq] at hx
        rcases hx with ⟨rfl, rfl, -⟩ | hx
        · exact ⟨_, q, l, hr, List.mem_cons_self⟩
        · obtain ⟨s', q', l', hr', hl'⟩ := hprog x' c' hx
          exact ⟨s', q', l', hr', List.mem_cons_of_mem _ hl'⟩
  | inr x =>
    cases hl : st.table.lookup x with
    | some e =>
      rw [run_handler_inr_some σ hl, runWithAnswers_pure, List.append_nil]
      exact ⟨hcount, hpos, hprog⟩
    | none =>
      rw [run_handler_inr_none σ hl, runWithAnswers_map_query]
      refine ⟨by simp [hcount], fun x' c i hx => ?_, fun x' c hx => ?_⟩
      · simp only [List.mem_cons, Prod.mk.injEq, Option.some.injEq] at hx
        rcases hx with ⟨rfl, rfl, rfl⟩ | hx
        · rw [hcount, List.getElem?_concat_length, List.getD_eq_getElem?_getD,
            List.headD_eq_head?_getD, List.head?_drop]
          exact ⟨rfl, rfl⟩
        · obtain ⟨hq, hc⟩ := hpos x' c i hx
          have hi : i < queries.length := (List.getElem?_eq_some_iff.mp hq).1
          exact ⟨by rw [List.getElem?_append_left hi, hq], hc⟩
      · simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hx
        exact hprog x' c hx

/-- **The reduction's runs on fixed answers.** On any list of answers, a winning candidate names a
position, and a named position is that of the query for the candidate's point, answered there with
the candidate's challenge, and the candidate's transcript is accepting. -/
theorem runWithAnswers_program (default : C) (σ : Signer Req Reply Point C Log S)
    (κ : Check M T C Z Point Log) (hκ : RejectsProgrammed σ κ)
    (A : OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z))) (samples : List S)
    (answers : List C) {position : Option ℕ} {outcome : Outcome M T C Z} {queries : List Point}
    (hout : runWithAnswers default (program σ κ A samples) answers =
      ((position, outcome), queries)) :
    (outcome.won = true → position.isSome) ∧
      ∀ j, position = some j →
        queries[j]? = some (κ.point outcome.message outcome.commitment) ∧
        answers.getD j default = outcome.challenge ∧
        κ.accepts outcome.message outcome.commitment outcome.challenge outcome.response = true := by
  have hinv := runWithAnswers_run_interpret_invariant default (handler σ) answers
    (Consistent default answers σ) (consistent_step default answers σ) A ⟨[], [], 0, samples⟩ []
    ⟨rfl, by simp, by simp⟩
  simp only [List.length_nil, List.drop_zero, List.nil_append] at hinv
  rw [program, runWithAnswers_bind] at hout
  generalize runWithAnswers default ((interpret (handler σ) A).run ⟨[], [], 0, samples⟩) answers =
    r at hinv hout
  obtain ⟨⟨⟨m, t, z⟩, st⟩, qs⟩ := r
  obtain ⟨hcount, hpos, hprog⟩ := hinv
  cases hl : st.table.lookup (κ.point m t) with
  | some e =>
    obtain ⟨l₁, l₂, htable, -⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : (κ.point m t, e.1, e.2) ∈ st.table := by
      rw [htable]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨c, i⟩ := e
    simp only [finish, hl, runWithAnswers_pure, List.append_nil, verdict, Prod.mk.injEq] at hout
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
    cases i with
    | none =>
      obtain ⟨s, q, l, hr, hlog⟩ := hprog _ _ hmem
      have hfresh := hκ s q _ c l hr m t st.log rfl hlog
      simp [hfresh]
    | some i =>
      obtain ⟨hq, hc⟩ := hpos _ _ _ hmem
      refine ⟨fun hwin => by simpa using hwin, fun j hj => ?_⟩
      split_ifs at hj with hwin
      cases hj
      exact ⟨hq, hc, ((Bool.and_eq_true _ _).mp hwin).1⟩
  | none =>
    simp only [finish, hl, runWithAnswers_map_query, verdict, Prod.mk.injEq] at hout
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
    refine ⟨fun hwin => by simpa using hwin, fun j hj => ?_⟩
    split_ifs at hj with hwin
    cases hj
    refine ⟨by rw [hcount, List.getElem?_concat_length], ?_, ((Bool.and_eq_true _ _).mp hwin).1⟩
    rw [hcount, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

/-- The reduction asks at most one query per hash call of the adversary, and one more to check
the candidate. -/
theorem isQueryBounded_program (σ : Signer Req Reply Point C Log S) (κ : Check M T C Z Point Log)
    {A : OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z))} {Qro : ℕ}
    (hA : IsCostBounded hashCost A Qro) (samples : List S) :
    IsQueryBounded (program σ κ A samples) (Qro + 1) := by
  have hhandler (q : Req ⊕ Point) (st : State Point C Log S) :
      IsQueryBounded ((handler σ q).run st) (hashCost q) := by
    cases q with
    | inl q =>
      rw [run_handler_inl]
      exact .pure _ _
    | inr x =>
      cases hl : st.table.lookup x with
      | some e =>
        rw [run_handler_inr_some σ hl]
        exact .pure _ _
      | none =>
        rw [run_handler_inr_none σ hl]
        exact .liftBind _ _ 0 fun _ => .pure _ 0
  refine (hA.run_interpret hhandler ⟨[], [], 0, samples⟩).bind fun ⟨⟨m, t, _⟩, st⟩ => ?_
  cases hl : st.table.lookup (κ.point m t) with
  | some e =>
    simp only [finish, hl]
    exact .pure _ _
  | none =>
    simp only [finish, hl]
    exact .liftBind _ _ 0 fun _ => .pure _ 0

/-! ### Forking the reduction -/

section Fork

variable [Fintype C] [Nonempty C]

/-- With its oracle answered uniformly, the reduction wins at most as often as it validly names a
query. -/
private theorem map_run_le_validIndex (σ : Signer Req Reply Point C Log S)
    (κ : Check M T C Z Point Log) (hκ : RejectsProgrammed σ κ)
    {A : OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z))} {Qro : ℕ}
    (hA : IsCostBounded hashCost A Qro) (samples : List S) :
    ((interpret countingUniform (program σ κ A samples)).run 0).map
        (fun ((_, outcome), _) => outcome.won) true ≤
      ((interpret countingUniform (program σ κ A samples)).run 0).bind
        (fun run => PMF.pure (validIndex (Qro + 1) run.2 run.1.1).isSome) true := by
  have hbound := isQueryBounded_program σ κ hA samples
  let defC := Classical.arbitrary C
  rw [run_interpret_countingUniform_eq defC _ hbound]
  simp only [pmf_norm, ← PMF.bind_pure_comp]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun h _ => ?_
  have hle := hbound.length_runWithAnswers_le defC (List.ofFn h)
  generalize hrun : runWithAnswers defC (program σ κ A samples) (List.ofFn h) = run at hle ⊢
  obtain ⟨⟨position, outcome⟩, queries⟩ := run
  obtain ⟨hwin, hnamed⟩ := runWithAnswers_program defC σ κ hκ A samples (List.ofFn h) hrun
  dsimp only at hle ⊢
  by_cases hw : outcome.won = true
  · obtain ⟨j, rfl⟩ := Option.isSome_iff_exists.mp (hwin hw)
    have hlt : j < queries.length := (List.getElem?_eq_some_iff.mp (hnamed j rfl).1).1
    have hvalid : (validIndex (Qro + 1) (0 + queries.length) (some j)).isSome = true := by
      rw [zero_add]
      simp only [validIndex, Option.bind_some]
      split_ifs with hc
      · rfl
      · exact absurd ⟨by omega, hlt⟩ hc
    rw [hw, hvalid]
  · rw [Bool.eq_false_iff.mpr hw]
    simp

/-- **The forking lemma for the reduction** ([BellareNeven2006], Lemma 1). If an event has
probability at most `ε` more than the reduction's winning probability, over coins `first` that
fix the check, the adversary and the presampled values, and the adversary makes at most `Qro` hash
calls, then the event has real probability at most `(Qro + 1) / |C| + √((Qro + 1) · succ) + ε`,
where forking the reduction succeeds with probability at most `succ`. -/
theorem toReal_le_add_sqrt_fork_of_le [DecidableEq C] {Coins : Type} (first : PMF Coins)
    (σ : Signer Req Reply Point C Log S) (κ : Coins → Check M T C Z Point Log)
    (hκ : ∀ s, RejectsProgrammed σ (κ s))
    (A : Coins → OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z)))
    (samples : Coins → List S) {Qro : ℕ} (hA : ∀ s, IsCostBounded hashCost (A s) Qro)
    {p ε succ : ℝ≥0∞} (hε : ε ≠ ⊤)
    (hp : p ≤ first.bind (fun s =>
      ((interpret countingUniform (program σ (κ s) (A s) (samples s))).run 0).map
        fun ((_, outcome), _) => outcome.won) true + ε)
    (hfork : (Forking.fork first (forkingAlgorithm (Classical.arbitrary C) (Qro + 1)
      fun s => program σ (κ s) (A s) (samples s))).map Option.isSome true ≤ succ)
    (hsucc : succ ≠ ⊤) :
    p.toReal ≤ (Qro + 1 : ℕ) / Fintype.card C + √((Qro + 1 : ℕ) * succ.toReal) + ε.toReal :=
  OracleComp.toReal_le_add_sqrt_fork_of_le first _ (Classical.arbitrary C)
    (fun s => isQueryBounded_program σ (κ s) (hA s) (samples s)) hε
    (hp.trans (add_le_add (Probability.PMF.bind_apply_mono_on_support _ _ fun s _ =>
      map_run_le_validIndex σ (κ s) (hκ s) (hA s) (samples s)) le_rfl)) hfork hsucc

/-- **Extraction data from a successful fork.** Both runs of a successful fork of the reduction
start from the same coins `s` and name the same query: their candidates `outcome` and `outcome'`
have the same point, different challenges, and accepting transcripts. -/
theorem exists_of_mem_support_fork [DecidableEq C] {Coins : Type}
    {first : PMF Coins} (σ : Signer Req Reply Point C Log S)
    (κ : Coins → Check M T C Z Point Log) (hκ : ∀ s, RejectsProgrammed σ (κ s))
    (A : Coins → OracleComp (ForgerSpec Req Point Reply C) (M × (T × Z)))
    (samples : Coins → List S) {default : C} {q : ℕ} {j : Fin q}
    {position position' : Option ℕ} {outcome outcome' : Outcome M T C Z}
    {queries queries' : List Point}
    (hfork : some (j, ((position, outcome), queries), ((position', outcome'), queries')) ∈
      (Forking.fork first (forkingAlgorithm default q
        fun s => program σ (κ s) (A s) (samples s))).support) :
    ∃ s ∈ first.support,
      (κ s).point outcome.message outcome.commitment =
        (κ s).point outcome'.message outcome'.commitment ∧
      outcome.challenge ≠ outcome'.challenge ∧
      (κ s).accepts outcome.message outcome.commitment outcome.challenge outcome.response =
        true ∧
      (κ s).accepts outcome'.message outcome'.commitment outcome'.challenge outcome'.response =
        true := by
  obtain ⟨s, hs, h, h', -, hne, hout, hout', hj, hj', -, query, hq, hq'⟩ := mem_support_fork hfork
  obtain ⟨-, hnamed⟩ :=
    runWithAnswers_program default σ (κ s) (hκ s) (A s) (samples s) (List.ofFn h) hout.symm
  obtain ⟨-, hnamed'⟩ :=
    runWithAnswers_program default σ (κ s) (hκ s) (A s) (samples s) (List.ofFn h') hout'.symm
  obtain ⟨hp, hc, hv⟩ := hnamed j hj
  obtain ⟨hp', hc', hv'⟩ := hnamed' j hj'
  rw [List.getD_ofFn] at hc hc'
  exact ⟨s, hs, Option.some.inj (hp.symm.trans (hq.trans (hq'.symm.trans hp'))),
    by rw [← hc, ← hc']; exact hne, hv, hv'⟩

end Fork

end Cslib.Crypto.Protocols.SigmaProtocol.ForkingReduction
