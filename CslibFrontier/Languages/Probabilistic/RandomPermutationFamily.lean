/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.Product

/-!
# Independent bidirectional permutation oracles

A finite indexed family of independent permutations, with one lazy partial-bijection cache
per index. Each query updates only its selected cache using `RandomPermutation.answer`.
The simulation retains the completed family jointly with the adaptive program's result;
consequently a continuation may inspect previously unqueried entries as well as the transcript.
This generalizes the two-cache construction used by the Even–Mansour ideal game.

## Main definitions

* `Cslib.RandomPermutation.Family.Spec`: indexed bidirectional queries.
* `Cslib.RandomPermutation.Family.answer`, `complete`: lazy answers and independent completion.

## Main results

* `Cslib.RandomPermutation.Family.answer_complete`: exact joint one-query completion law.
* `Cslib.RandomPermutation.Family.run_interpret_answer_complete`: adaptive joint completion law.
* `Cslib.RandomPermutation.Family.uniform_interpret_eq_lazy`,
  `uniform_prob_interpret_eq_lazy`: eager/lazy output laws, including private-coin programs.
* `Cslib.RandomPermutation.Family.run_prob_valid`: validity after every supported program prefix.
-/

public section

namespace Cslib.RandomPermutation.Family

open Probability OracleComp

/-- A query names an independent permutation and a forward or inverse argument. -/
abbrev Spec (Index Word : Type) : OracleSpec (Index × PermQuery Word) := fun _ => Word

/-- One partial permutation table per index. -/
abbrev Tables (Index Word : Type) := Index → RandomPermutation.Cache Word

/-- Read a selected permutation in the requested direction. -/
@[expose] def eval {Index Word : Type} (perms : Index → Equiv.Perm Word)
    (query : Index × PermQuery Word) : Word := evalPerm (perms query.1) query.2

variable {Index Word : Type} [Fintype Index] [DecidableEq Index]
  [Fintype Word] [DecidableEq Word] [Nonempty Word]

/-- Answer using exactly one table, preserving every other table. -/
@[expose] noncomputable def answer (query : Index × PermQuery Word) :
    StateT (Tables Index Word) PMF (Spec Index Word query) := fun tables =>
  (RandomPermutation.answer query.2 (tables query.1)).map fun (value, table) =>
    (value, Function.update tables query.1 table)

/-- Complete the individual tables independently and uniformly among their extensions. -/
@[expose] noncomputable def complete (tables : Tables Index Word) :
    PMF (Index → Equiv.Perm Word) := PMF.pi fun i => RandomPermutation.complete (tables i)

/-- The invariant required for every coordinate's exact completion law. -/
def Valid (tables : Tables Index Word) : Prop :=
  ∀ i, IsPartialBijection (tables i)

omit [Fintype Index] [DecidableEq Index] [Fintype Word] [DecidableEq Word]
  [Nonempty Word] in
/-- Empty family tables are valid, including an empty index type. -/
theorem valid_empty : Valid (fun _ : Index => ([] : Cache Word)) :=
  fun _ => isPartialBijection_nil

omit [Fintype Index] in
/-- Supported answers preserve every coordinate's partial-bijection invariant. -/
theorem answer_valid (query : Index × PermQuery Word) (tables : Tables Index Word)
    (h : Valid tables) (value : Word) (tables' : Tables Index Word)
    (hout : (value, tables') ∈ (answer query tables).support) : Valid tables' := by
  simp only [answer, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨value, table⟩, htable, heq⟩ := hout
  cases heq
  intro i
  by_cases hi : i = query.1
  · subst i
    simp only [Function.update_self]
    exact RandomPermutation.answer_preserve_isPartialBijection _ _ (h _) _ _ htable
  · simpa only [Function.update_of_ne hi] using h i

omit [Nonempty Word] in
private theorem complete_update (tables : Tables Index Word) (i : Index) (table : Cache Word) :
    complete (Function.update tables i table) =
      (RandomPermutation.complete table).bind fun perm =>
        PMF.pi (Function.update (fun j => RandomPermutation.complete (tables j))
          i (PMF.pure perm)) := by
  have heq : (fun j => RandomPermutation.complete (Function.update tables i table j)) =
      Function.update (fun j => RandomPermutation.complete (tables j))
        i (RandomPermutation.complete table) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  rw [complete, heq, ← PMF.pi_bind_update _ i]
  simp only [Function.update_self, Function.update_idem]

/-- Answering one selected oracle and then completing all tables has the same joint law as
completing first and reading the selected permutation. No independence of adaptive queries
is assumed. -/
theorem answer_complete (query : Index × PermQuery Word) (tables : Tables Index Word)
    (h : Valid tables) :
    (answer query tables).bind (fun (value, tables') => (complete tables').map (value, ·)) =
      (complete tables).map (fun perms => (eval perms query, perms)) := by
  simp only [answer, PMF.bind_map, Function.comp_def, complete_update, PMF.map_bind]
  have hone := congrArg (fun law : PMF (Word × Equiv.Perm Word) =>
    law.bind fun (value, perm) =>
      (PMF.pi (Function.update (fun j => RandomPermutation.complete (tables j))
        query.1 (PMF.pure perm))).map (value, ·))
    (RandomPermutation.answer_complete query.2 (tables query.1) (h query.1))
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at hone
  rw [hone]
  simpa only [complete, eval, PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using
    (PMF.bind_pi_update (fun j => RandomPermutation.complete (tables j)) query.1
      (fun perm perms => PMF.pure (evalPerm perm query.2, perms)))

/-- The exact eager/lazy equivalence retains the entire completed family, not just answers.
This permits subsequent output verification using entries the adversary did not query. -/
theorem run_interpret_answer_complete {Output : Type}
    (program : OracleComp (Spec Index Word) Output) (tables : Tables Index Word)
    (h : Valid tables) :
    ((interpret answer program).run tables).bind
        (fun (value, tables') => (complete tables').map (value, ·)) =
      (complete tables).bind fun perms =>
        (interpret (fun query => PMF.pure (eval perms query)) program).map (·, perms) := by
  have hsim := run_interpret_simulation_of_invariant answer
    (fun query perms => (·, perms) <$> PMF.pure (eval perms query)) complete Valid
    answer_valid (fun query tables h => by
      simpa only [pmf_norm, PMF.map] using answer_complete query tables h) program tables h
  refine hsim.trans (congrArg ((complete tables).bind) (funext fun perms => ?_))
  simpa only [pmf_norm] using
    run_interpret_readOnly (fun query perms => PMF.pure (eval perms query)) program perms

omit [Nonempty Word] in
/-- Empty caches complete to the independent uniform family. -/
theorem complete_empty :
    complete (fun _ : Index => ([] : Cache Word)) =
      PMF.uniformOfFintype (Index → Equiv.Perm Word) := by
  simp only [complete, RandomPermutation.complete_nil, PMF.pi_uniformOfFintype]

/-- Arbitrary adaptive bidirectional programs see exactly the uniform independent family. -/
theorem uniform_interpret_eq_lazy {Output : Type}
    (program : OracleComp (Spec Index Word) Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      interpret (fun query => PMF.pure (eval perms query)) program) =
        ((interpret answer program).run (fun _ => [])).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_answer_complete program (fun _ => []) valid_empty)
  simpa only [complete_empty, pmf_norm, PMF.map_id, PMF.map_const, PMF.map,
    Function.comp_def, PMF.bind_pure, PMF.bind_const] using h.symm

/-- Private uniform samples leave all permutation tables unchanged; external calls use `answer`.
The two effects remain distinct, so a query budget can count only external calls. -/
@[expose] noncomputable def probAnswer :
    (query : ℕ ⊕ (Index × PermQuery Word)) →
      StateT (Tables Index Word) PMF (probOracleSpec (Spec Index Word) query) :=
  sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) answer

/-- Eager family handler with independent private uniform samples. -/
@[expose] noncomputable def probEval (perms : Index → Equiv.Perm Word) :
    (query : ℕ ⊕ (Index × PermQuery Word)) → PMF (probOracleSpec (Spec Index Word) query) :=
  sumHandler ProbComp.unifOracle (fun query => PMF.pure (eval perms query))

omit [Fintype Index] in
/-- Private sampling and external permutation queries both preserve table validity. -/
theorem probAnswer_valid (query : ℕ ⊕ (Index × PermQuery Word))
    (tables : Tables Index Word) (h : Valid tables)
    (value : probOracleSpec (Spec Index Word) query) (tables' : Tables Index Word)
    (hout : (value, tables') ∈ (probAnswer query tables).support) : Valid tables' := by
  cases query with
  | inl n =>
    change (value, tables') ∈ ((ProbComp.unifOracle n).map (·, tables)).support at hout
    simp only [PMF.mem_support_map_iff] at hout
    obtain ⟨_, _, heq⟩ := hout
    cases heq
    exact h
  | inr query => exact answer_valid query tables h value tables' hout

omit [Fintype Index] in
/-- Every supported final table family after any private-coin adaptive program is valid.
Applied to a prefix program, this gives validity at that prefix as well. -/
theorem run_prob_valid {Output : Type} (program : ProbOracleComp (Spec Index Word) Output)
    (tables : Tables Index Word) (h : Valid tables) (value : Output) (tables' : Tables Index Word)
    (hout : (value, tables') ∈ ((interpret probAnswer program).run tables).support) :
    Valid tables' :=
  run_interpret_invariant probAnswer Valid probAnswer_valid program tables h value tables' hout

/-- Exact joint completion for adaptive programs with private randomness. Sampling is independent
of the hidden family and does not require a bound on the number of internal random draws. -/
theorem run_prob_interpret_answer_complete {Output : Type}
    (program : ProbOracleComp (Spec Index Word) Output) (tables : Tables Index Word)
    (h : Valid tables) :
    ((interpret probAnswer program).run tables).bind
        (fun (value, tables') => (complete tables').map (value, ·)) =
      (complete tables).bind fun perms => (interpret (probEval perms) program).map (·, perms) := by
  have hstep : ∀ query (tables : Tables Index Word), Valid tables →
      (probAnswer query tables).bind (fun (value, tables') =>
        (complete tables').map (value, ·)) =
      (complete tables).bind fun perms =>
        (probEval perms query).map (·, perms) := by
    rintro (n | query) tables h
    · simp only [probAnswer, probEval, sumHandler, StateT.lift, pmf_norm, PMF.map]
      rw [PMF.bind_comm]
    · simpa only [probAnswer, probEval, sumHandler, pmf_norm, PMF.map] using
        answer_complete query tables h
  have hsim := run_interpret_simulation_of_invariant probAnswer
    (fun query perms => (·, perms) <$> probEval perms query) complete Valid
    probAnswer_valid hstep program tables h
  refine hsim.trans (congrArg ((complete tables).bind) (funext fun perms => ?_))
  simpa only [pmf_norm] using
    run_interpret_readOnly (fun query perms => probEval perms query) program perms

/-- Arbitrary private-coin adaptive programs see exactly independent uniform permutations. -/
theorem uniform_prob_interpret_eq_lazy {Output : Type}
    (program : ProbOracleComp (Spec Index Word) Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      interpret (probEval perms) program) =
        ((interpret probAnswer program).run (fun _ => [])).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_prob_interpret_answer_complete program (fun _ => []) valid_empty)
  simpa only [complete_empty, pmf_norm, PMF.map_id, PMF.map_const, PMF.map,
    Function.comp_def, PMF.bind_pure, PMF.bind_const] using h.symm

end Cslib.RandomPermutation.Family
