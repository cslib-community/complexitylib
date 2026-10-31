/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Probability.Forking
import Complexity.Languages.Probabilistic.Presample
import Complexity.Languages.Probabilistic.Repeat
import Complexity.Probability.PMF
import Complexity.Probability.Product

/-!
# Forking oracle programs

An oracle program `P s : OracleComp (fun _ : Query => H) (Option ℕ × β)`, with explicit coins
`s`, asks queries whose answers lie in a finite set `H` and finally names one of its queries by
its position, or none. A name counts only if the program actually asked a query at that position
(`validIndex`). Forking runs the program with uniform answers and, if it validly names position
`j`, runs it again on the same coins with the same answers before `j` and fresh answers from `j`
on; it succeeds when the rerun validly names `j` too and the answers at `j` differ. Both runs then
ask the same first `j + 1` queries, so the named query exists in both and is the same, while its
two answers differ (`mem_support_fork`).

`runWithAnswers` runs a program on a list of answers, deterministically, recording its queries.
Sequencing splits the answers (`runWithAnswers_bind`), so properties of a program run through a
stateful handler follow from properties of single calls
(`runWithAnswers_run_interpret_invariant`).
Answering queries from `q` presampled uniform answers has the law of answering them uniformly as
they come, when the program asks at most `q` queries: this is the presampling theorem
`OracleComp.IsQueryBounded.run_interpret_presample` (`interpret_uniform_eq`, and
`run_interpret_countingUniform_eq` when the queries are also counted). Hence the general forking
lemma (`Probability.Forking.le_add_sqrt_fork`) bounds the probability that the program, with
uniform answers, validly names a query by `q / |H| + √(q · frk)` (`le_add_sqrt_fork`).

The coins are explicit: the second run replays them. A program with private randomness is put in
this form by drawing its coins in advance. The statements are exact; no efficiency is involved.

## Main definitions

* `Cslib.OracleComp.runWithAnswers`: run on a list of answers, recording the queries.
* `Cslib.OracleComp.validIndex`: the named position, if it is below `q` and was queried.
* `Cslib.OracleComp.countingUniform`: uniform answers as queries come, counting them.
* `Cslib.OracleComp.forkingAlgorithm`: a program on coins and an answer vector, for forking.

## Main results

* `Cslib.OracleComp.interpret_uniform_eq`, `Cslib.OracleComp.run_interpret_countingUniform_eq`:
  uniform answers as they come, or presampled.
* `Cslib.OracleComp.le_add_sqrt_fork`: the forking lemma for oracle programs.
* `Cslib.OracleComp.mem_support_fork`: both runs of a successful fork ask the same queries up to
  the named one, and answer it differently.
* `Cslib.OracleComp.take_runWithAnswers`: a program's first `n + 1` queries depend only on its
  first `n` answers.
* `Cslib.OracleComp.runWithAnswers_run_interpret_invariant`: an invariant of a handler's state
  and the queries asked so far holds after running a program through the handler on fixed
  answers.

## References

* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.8.
-/

@[expose] public section

namespace Cslib.OracleComp

open Probability

variable {Query H α : Type}

/-- Run a program on a list of answers, in order, answering `default` once the list is exhausted;
return its result and its queries, in order. -/
def runWithAnswers (default : H) : OracleComp (fun _ : Query => H) α → List H → α × List Query
  | .pure a, _ => (a, [])
  | .liftBind q cont, answers =>
    ((runWithAnswers default (cont (answers.headD default)) answers.tail).1,
      q :: (runWithAnswers default (cont (answers.headD default)) answers.tail).2)

/-- Returning a value asks no query. -/
@[simp] theorem runWithAnswers_pure (default : H) (a : α) (answers : List H) :
    runWithAnswers default (pure a : OracleComp (fun _ : Query => H) α) answers = (a, []) := rfl

/-- A query is answered by the head of the list, and the rest goes to the continuation. -/
@[simp] theorem runWithAnswers_query_bind (default : H) (q : Query)
    (cont : H → OracleComp (fun _ : Query => H) α) (answers : List H) :
    runWithAnswers default (OracleComp.query (spec := fun _ : Query => H) q >>= cont) answers =
      ((runWithAnswers default (cont (answers.headD default)) answers.tail).1,
        q :: (runWithAnswers default (cont (answers.headD default)) answers.tail).2) := rfl

/-- A mapped query is answered by the head of the list. -/
@[simp] theorem runWithAnswers_map_query (default : H) (f : H → α) (q : Query)
    (answers : List H) :
    runWithAnswers default (f <$> OracleComp.query (spec := fun _ : Query => H) q) answers =
      (f (answers.headD default), [q]) := rfl

/-- A program's first `n + 1` queries depend only on the first `n` answers. -/
theorem take_runWithAnswers (default : H) (program : OracleComp (fun _ : Query => H) α) :
    ∀ {answers answers' : List H} {n : ℕ}, answers.take n = answers'.take n →
      (runWithAnswers default program answers).2.take (n + 1) =
        (runWithAnswers default program answers').2.take (n + 1) := by
  induction program with
  | pure a => intros; rfl
  | liftBind q cont ih =>
    intro answers answers' n h
    cases n with
    | zero => rfl
    | succ n =>
      have hsplit : answers.headD default = answers'.headD default ∧
          answers.tail.take n = answers'.tail.take n := by
        cases answers <;> cases answers' <;> simp_all
      simp only [runWithAnswers, List.take_succ_cons, hsplit.1, ih _ hsplit.2]

/-- Running a sequenced program on a list of answers runs the first part on the list and the
second part on the answers the first part left unused. -/
theorem runWithAnswers_bind {β : Type} (default : H) (program : OracleComp (fun _ : Query => H) α)
    (next : α → OracleComp (fun _ : Query => H) β) (answers : List H) :
    runWithAnswers default (program >>= next) answers =
      ((runWithAnswers default (next (runWithAnswers default program answers).1)
          (answers.drop (runWithAnswers default program answers).2.length)).1,
        (runWithAnswers default program answers).2 ++
          (runWithAnswers default (next (runWithAnswers default program answers).1)
            (answers.drop (runWithAnswers default program answers).2.length)).2) := by
  induction program using OracleComp.induction generalizing answers with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [bind_assoc, runWithAnswers_query_bind, ih]
    cases answers with
    | nil => simp
    | cons a rest => rfl

/-- A program making at most `n` calls asks at most `n` queries on every list of answers. -/
theorem IsQueryBounded.length_runWithAnswers_le (default : H)
    {program : OracleComp (fun _ : Query => H) α} {n : ℕ} (h : IsQueryBounded program n)
    (answers : List H) : (runWithAnswers default program answers).2.length ≤ n := by
  induction h generalizing answers with
  | pure a n => exact Nat.zero_le n
  | liftBind q cont n _ ih =>
    rw [runWithAnswers_query_bind, List.length_cons]
    exact Nat.succ_le_succ (ih _ _)

/-- The result component of a `runWithAnswers` output pair `(result, queries)`. -/
abbrev runWithAnswersOutput {α γ : Type} (out : α × γ) : α := out.1

/-- The final handler state produced by `runWithAnswers` on a stateful handler execution. -/
abbrev runWithAnswersState {σ β : Type} (out : (β × σ) × List Query) : σ :=
  (runWithAnswersOutput out).2

/-- **An invariant of a handler's run on a list of answers.** A program runs through a stateful
handler whose calls are oracle programs, and the resulting program runs on a list of answers. A
property of the handler's state and of the queries asked so far that every handler call
preserves, when run on the answers not yet used, holds at the end. -/
theorem runWithAnswers_run_interpret_invariant {ι σ β : Type} {spec : ι → Type} (default : H)
    (handler : (q : ι) → StateT σ (OracleComp (fun _ : Query => H)) (spec q))
    (answers : List H) (invariant : σ → List Query → Prop)
    (step : ∀ q s queries, invariant s queries →
      invariant
        (runWithAnswersState (runWithAnswers default ((handler q).run s)
          (answers.drop queries.length)))
        (queries ++ (runWithAnswers default ((handler q).run s)
          (answers.drop queries.length)).2))
    (program : OracleComp spec β) (s : σ) (queries : List Query) (hs : invariant s queries) :
    invariant (runWithAnswersState (runWithAnswers default ((interpret handler program).run s)
        (answers.drop queries.length)))
      (queries ++ (runWithAnswers default ((interpret handler program).run s)
        (answers.drop queries.length)).2) := by
  induction program using OracleComp.induction generalizing s queries with
  | pure b => simpa using hs
  | query_bind q cont ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind, runWithAnswers_bind,
      List.drop_drop]
    have hstep := step q s queries hs
    have hnext := ih (runWithAnswers default ((handler q).run s)
      (answers.drop queries.length)).1.1 _ _ hstep
    simp only [List.length_append, List.append_assoc] at hnext
    exact hnext

/-! ### Presampled answers -/

/-- Answering the lifted program from a saved list is running it on that list. -/
private theorem eval_run_withSampleList (default : H)
    (program : OracleComp (fun _ : Query => H) α) (answers : List H) :
    ProbComp.eval ((fun (result, next, _) => (result, next)) <$>
      (interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (withSampleList default fun v _ s => (pure (v, s) : ProbComp (H × Unit))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run ((), answers)) =
      PMF.pure ((runWithAnswers default program answers).1, ()) := by
  induction program using OracleComp.induction generalizing answers with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [runWithAnswers_query_bind, ← ih (answers.headD default) answers.tail]
    rfl

/-- Answering lifted queries uniformly as they come is answering them uniformly. -/
private theorem eval_run_uniform [Fintype H] [Nonempty H]
    (program : OracleComp (fun _ : Query => H) α) :
    ProbComp.eval ((interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun _ s => do
          let value ← ProbComp.uniform H
          (pure (value, s) : ProbComp (H × Unit))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run ()) =
      (interpret (fun _ => PMF.uniformOfFintype H) program).map (·, ()) := by
  have hstate : (fun (_ : Query) (s : Unit) => do
      let value ← ProbComp.uniform H
      (pure (value, s) : ProbComp (H × Unit))) =
      fun _ s => (fun a => (a, s)) <$> ProbComp.uniform H := by
    funext _ s
    rw [map_eq_bind_pure_comp]
    rfl
  have heval : ProbComp.eval (interpret (fun _ => ProbComp.uniform H) program) =
      interpret (fun _ => PMF.uniformOfFintype H) program := by
    simp only [ProbComp.eval_interpret, ProbComp.eval_uniform]
  rw [interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  rw [hstate, run_interpret_stateless, ProbComp.eval_map, heval]

/-- `q` uniform samples, collected in a list, are the entries of a uniform vector. -/
private theorem eval_replicate_uniform [Fintype H] [Nonempty H] (q : ℕ) :
    ProbComp.eval (replicate q (ProbComp.uniform H)) =
      (PMF.uniformOfFintype (Fin q → H)).map List.ofFn := by
  induction q with
  | zero =>
    have hconst : (List.ofFn : (Fin 0 → H) → List H) = Function.const _ [] :=
      funext fun _ => List.ofFn_zero
    rw [replicate_zero, ProbComp.eval_pure, hconst, PMF.map_const]
  | succ q ih =>
    rw [replicate_succ, ← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_fin_succ,
      Probability.PMF.pi_uniformOfFintype]
    simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_uniform, ih, PMF.map_bind,
      PMF.map_comp, Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- The lazy law of uniform answers is the law of `q` presampled uniform answers, for a program
asking at most `q` queries: an instance of the presampling theorem
`ProbOracleComp.IsQueryBounded.eval_presample`. -/
theorem interpret_uniform_eq [Fintype H] [Nonempty H] (default : H)
    (program : OracleComp (fun _ : Query => H) α) {q : ℕ} (hq : program.IsQueryBounded q) :
    interpret (fun _ => PMF.uniformOfFintype H) program =
      (PMF.uniformOfFintype (Fin q → H)).map fun h =>
        (runWithAnswers default program (List.ofFn h)).1 := by
  have hp := hq.probOracleComp.eval_presample (ProbComp.uniform H) default
    (fun v _ s => (pure (v, s) : ProbComp (H × Unit))) ()
  rw [eval_run_uniform, ProbComp.eval_bind, eval_replicate_uniform] at hp
  simp only [eval_run_withSampleList, PMF.bind_map, Function.comp_def] at hp
  have hfst := congrArg (PMF.map Prod.fst) hp
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show PMF.map (fun x => x) (interpret (fun _ => PMF.uniformOfFintype H) program) =
    interpret (fun _ => PMF.uniformOfFintype H) program from PMF.map_id _] at hfst
  rw [← hfst, PMF.map_bind]
  simp only [PMF.pure_map]
  rfl

/-- Answer queries uniformly as they come, counting them in the state. -/
noncomputable def countingUniform [Fintype H] [Nonempty H] (_ : Query) : StateT ℕ PMF H :=
  fun count => (PMF.uniformOfFintype H).map (·, count + 1)

/-- Answering the lifted program from a saved list, counting the calls, is running it on that
list. -/
private theorem eval_run_withSampleList_count (default : H)
    (program : OracleComp (fun _ : Query => H) α) (count : ℕ) (answers : List H) :
    ProbComp.eval ((fun (result, next, _) => (result, next)) <$>
      (interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (withSampleList default fun v _ n => (pure (v, n + 1) : ProbComp (H × ℕ))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run (count, answers)) =
      PMF.pure ((runWithAnswers default program answers).1,
        count + (runWithAnswers default program answers).2.length) := by
  induction program using OracleComp.induction generalizing count answers with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [runWithAnswers_query_bind, List.length_cons,
      show count + ((runWithAnswers default (cont (answers.headD default)) answers.tail).2.length
        + 1) = (count + 1) +
          (runWithAnswers default (cont (answers.headD default)) answers.tail).2.length by omega,
      ← ih (answers.headD default) (count + 1) answers.tail]
    rfl

/-- Answering lifted queries uniformly as they come, counting them, is `countingUniform`. -/
private theorem eval_run_counting [Fintype H] [Nonempty H]
    (program : OracleComp (fun _ : Query => H) α) (count : ℕ) :
    ProbComp.eval ((interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun _ n => do
          let value ← ProbComp.uniform H
          (pure (value, n + 1) : ProbComp (H × ℕ))))
          (interpret (fun q => ProbOracleComp.query (spec := fun _ : Query => H) q)
            program)).run count) =
      (interpret countingUniform program).run count := by
  rw [ProbOracleComp.eval_run_interpret, interpret_interpret]
  congr 1
  congr 1
  funext q n
  simp only [ProbOracleComp.interpret_query, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  rfl

/-- Counting variant of `interpret_uniform_eq`: answering uniformly as queries come, and counting
them, has the law of running on `q` presampled uniform answers and counting the queries made. -/
theorem run_interpret_countingUniform_eq [Fintype H] [Nonempty H] (default : H)
    (program : OracleComp (fun _ : Query => H) α) {q : ℕ} (hq : program.IsQueryBounded q)
    (count : ℕ) :
    (interpret countingUniform program).run count =
      (PMF.uniformOfFintype (Fin q → H)).map fun h =>
        ((runWithAnswers default program (List.ofFn h)).1,
          count + (runWithAnswers default program (List.ofFn h)).2.length) := by
  have hp := hq.probOracleComp.eval_presample (ProbComp.uniform H) default
    (fun v _ n => (pure (v, n + 1) : ProbComp (H × ℕ))) count
  rw [eval_run_counting, ProbComp.eval_bind, eval_replicate_uniform] at hp
  simp only [eval_run_withSampleList_count, PMF.bind_map, Function.comp_def] at hp
  rw [← hp]
  rfl

/-! ### Forking -/

/-- The named position, if it is below `q` and names one of the `count` queries made. A program
naming a position it never queried does not count as naming one. -/
def validIndex (q count : ℕ) (position : Option ℕ) : Option (Fin q) :=
  position.bind fun j => if h : j < q ∧ j < count then some ⟨j, h.1⟩ else none

/-- A valid index is a named position below `q` and below the number of queries made. -/
theorem validIndex_eq_some {q count : ℕ} {position : Option ℕ} {j : Fin q}
    (h : validIndex q count position = some j) : position = some j.val ∧ j.val < count := by
  cases position with
  | none => simp [validIndex] at h
  | some p =>
    simp only [validIndex, Option.bind_some] at h
    split_ifs at h with hp
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, hp.2⟩

/-- The named query position returned by a forking-lemma program execution. -/
abbrev forkNamedPosition {β γ : Type} (out : (Option ℕ × β) × γ) : Option ℕ :=
  (runWithAnswersOutput out).1

/-- A program with explicit coins as an algorithm on coins and `q` answers, for the general
forking lemma: the validly named position, and the result with the queries. -/
def forkingAlgorithm {S β : Type} (default : H) (q : ℕ)
    (program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)) (s : S) (h : Fin q → H) :
    Option (Fin q) × ((Option ℕ × β) × List Query) :=
  let run := runWithAnswers default (program s) (List.ofFn h)
  (validIndex q run.2.length (forkNamedPosition run), run)

variable {S β : Type} [Fintype H] [Nonempty H] [DecidableEq H]

/-- **The forking lemma for oracle programs** ([BellareNeven2006], Lemma 1): if a program with
explicit coins asks at most `q` queries, and with probability `acc` names one of the queries it
made when they are answered uniformly as they come, then forking it succeeds with probability
`frk` such that `acc ≤ q / |H| + √(q · frk)`. -/
theorem le_add_sqrt_fork (first : PMF S)
    (program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)) (default : H)
    {q : ℕ} (hq : ∀ s, (program s).IsQueryBounded q) :
    ((do
      let s ← first
      let run ← (interpret countingUniform (program s)).run 0
      return (validIndex q run.2 (forkNamedPosition run)).isSome : PMF Bool) true).toReal ≤
      q / Fintype.card H + √(q * ((Forking.fork first (forkingAlgorithm default q program)).map
        Option.isSome true).toReal) := by
  have hacc : (do
      let s ← first
      let run ← (interpret countingUniform (program s)).run 0
      return (validIndex q run.2 run.1.1).isSome : PMF Bool) =
      Forking.accept first (forkingAlgorithm default q program) := by
    simp only [Forking.accept, forkingAlgorithm, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure]
    refine congrArg _ (funext fun s => ?_)
    rw [run_interpret_countingUniform_eq default (program s) (hq s), PMF.bind_map]
    simp only [zero_add]
    rfl
  rw [hacc]
  exact Forking.le_add_sqrt_fork first _

/-- A successful fork of a program reruns it on the same coins with answers that agree before the
named position `j` and differ at it. Both runs name `j`, ask the same first `j + 1` queries, and
have actually asked a query at position `j`, the same one. -/
theorem mem_support_fork {first : PMF S}
    {program : S → OracleComp (fun _ : Query => H) (Option ℕ × β)} {default : H} {q : ℕ}
    {j : Fin q} {out out' : (Option ℕ × β) × List Query}
    (hfork : some (j, out, out') ∈
      (Forking.fork first (forkingAlgorithm default q program)).support) :
    ∃ s ∈ first.support, ∃ h h' : Fin q → H, (∀ i < j, h i = h' i) ∧ h j ≠ h' j ∧
      out = runWithAnswers default (program s) (List.ofFn h) ∧
      out' = runWithAnswers default (program s) (List.ofFn h') ∧
      forkNamedPosition out = some j.val ∧ forkNamedPosition out' = some j.val ∧
      out.2.take (j + 1) = out'.2.take (j + 1) ∧
      ∃ query, out.2[j.val]? = some query ∧ out'.2[j.val]? = some query := by
  obtain ⟨s, hs, h, h', hagree, hne, hrun, hrun'⟩ := Forking.mem_support_fork hfork
  simp only [forkingAlgorithm, Prod.mk.injEq] at hrun hrun'
  obtain ⟨hidx, rfl⟩ := hrun
  obtain ⟨hidx', rfl⟩ := hrun'
  obtain ⟨hpos, hlt⟩ := validIndex_eq_some hidx
  obtain ⟨hpos', hlt'⟩ := validIndex_eq_some hidx'
  have htake : (runWithAnswers default (program s) (List.ofFn h)).2.take (j + 1) =
      (runWithAnswers default (program s) (List.ofFn h')).2.take (j + 1) := by
    refine take_runWithAnswers default (program s) ?_
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_take, List.length_ofFn] at hi
    simp only [List.getElem_take, List.getElem_ofFn]
    exact hagree ⟨i, by omega⟩ (Fin.mk_lt_of_lt_val (by omega))
  refine ⟨s, hs, h, h', hagree, hne, rfl, rfl, hpos, hpos', htake,
    (runWithAnswers default (program s) (List.ofFn h)).2[j.val], List.getElem?_eq_getElem hlt, ?_⟩
  have hget := congrArg (fun l : List Query => l[j.val]?) htake
  simp only [List.getElem?_take, Nat.lt_succ_self, ite_true] at hget
  rw [← hget, List.getElem?_eq_getElem hlt]

end Cslib.OracleComp
