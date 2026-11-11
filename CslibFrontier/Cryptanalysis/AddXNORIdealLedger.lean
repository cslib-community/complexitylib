/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealForest
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Fresh ledgers of the actual indexed permutation oracle

`answer` executes the existing exact family sampler, recording precisely cache misses.
`project_run` identifies its complete cache state with that sampler, starting from empty
valid tables. Hits do not create entries, so their repeated answers are not fresh collisions.
This connects the deterministic forest ledger to actual adaptive private-coin execution.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Ledger.tables`: caches reconstructed from fresh entries.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Ledger.answer`: exact sampling with a fresh ledger.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Ledger.project_run`: actual sampler cache correspondence.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Ledger

open Probability OracleComp RandomPermutation

variable {Index Word : Type} [DecidableEq Index]

/-- Reconstruct each indexed permutation cache from the actual fresh entries, newest first. -/
@[expose] def tables (records : List (Forest.Record Index Word)) : Family.Tables Index Word :=
  fun label => (records.filter fun r => r.label = label).map Forest.Record.entry

/-- Prepending one fresh entry changes exactly its selected cache. -/
theorem tables_cons (record : Forest.Record Index Word)
    (records : List (Forest.Record Index Word)) :
    tables (record :: records) =
      Function.update (tables records) record.label
        (record.entry :: tables records record.label) := by
  funext label
  by_cases heq : label = record.label
  · subst label
    simp [tables]
  · simp [tables, Function.update_of_ne heq, Ne.symm heq]

variable [Fintype Word] [DecidableEq Word] [Nonempty Word]

/-- Append an actual answer only when the original request missed its selected cache. -/
@[expose] def update (query : Index × PermQuery Word) (value : Word)
    (records : List (Forest.Record Index Word)) : List (Forest.Record Index Word) :=
  if cachedAnswer (tables records query.1) query.2 = none then
    ⟨query.1, query.2, value⟩ :: records else records

/-- Execute the real family sampler and retain exactly its new entries. -/
@[expose] noncomputable def answer (query : Index × PermQuery Word) :
    StateT (List (Forest.Record Index Word)) PMF Word := fun records =>
  (Family.answer query (tables records)).map fun (value, _) => (value, update query value records)

/-- The ledger's reconstructed caches are precisely the returned sampler caches. -/
theorem tables_update_of_support (query : Index × PermQuery Word)
    (records : List (Forest.Record Index Word)) (hvalid : Family.Valid (tables records))
    (value : Word) (next : Family.Tables Index Word)
    (hout : (value, next) ∈ (Family.answer query (tables records)).support) :
    tables (update query value records) = next := by
  simp only [Family.answer, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨value, cache⟩, hcache, heq⟩ := hout
  cases heq
  cases hm : cachedAnswer (tables records query.1) query.2 with
  | some old =>
    rw [answer_of_cachedAnswer_eq_some hm, PMF.mem_support_pure_iff] at hcache
    cases hcache
    simp only [update, hm, reduceCtorEq, ↓reduceIte, Function.update_eq_self]
  | none =>
    rw [answer_of_cachedAnswer_eq_none hm ((hvalid _).freshAnswers_nonempty hm),
      PMF.mem_support_map_iff] at hcache
    obtain ⟨fresh, _, heq⟩ := hcache
    cases heq
    simp only [update, hm, ↓reduceIte, tables_cons]

/-- One instrumented call has the exact original sampler marginal, including complete caches. -/
theorem project_answer (query : Index × PermQuery Word) (records : List (Forest.Record Index Word))
    (hvalid : Family.Valid (tables records)) :
    (answer query records).map (fun (value, records') => (value, tables records')) =
      Family.answer query (tables records) := by
  rw [answer, PMF.map_comp]
  have h := PMF.map_congr_on_support (Family.answer query (tables records))
    (fun (value, next) => (value, tables (update query value records))) id
    (fun ⟨value, next⟩ hm => by
      simp only [id_eq]
      rw [tables_update_of_support query records hvalid value next hm])
  exact h.trans (PMF.map_id _)

/-- Every supported ledger transition preserves validity of all its reconstructed caches. -/
theorem answer_valid (query : Index × PermQuery Word) (records : List (Forest.Record Index Word))
    (hvalid : Family.Valid (tables records)) (value : Word)
    (records' : List (Forest.Record Index Word))
    (hout : (value, records') ∈ (answer query records).support) :
    Family.Valid (tables records') := by
  have hm : (value, tables records') ∈ ((answer query records).map
      (fun (value, records') => (value, tables records'))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨(value, records'), hout, rfl⟩
  rw [project_answer query records hvalid] at hm
  exact Family.answer_valid query (tables records) hvalid value (tables records') hm

/-- Projecting a whole adaptive private-coin run recovers the real family sampler's caches.
Initial validity is constructed from empty caches, not assumed as an endpoint premise. -/
theorem project_run {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (ProbOracleComp.runWith answer program []).map
        (fun (out, records) => (out, tables records)) =
      ProbOracleComp.runWith Family.answer program (fun _ => []) := by
  exact ProbOracleComp.runWith_map_state_of_invariant answer Family.answer tables
    (fun records => Family.Valid (tables records)) answer_valid
    (fun query records hvalid => project_answer query records hvalid)
    program [] Family.valid_empty

/-- One actual call records at most one fresh entry. -/
theorem answer_length (query : Index × PermQuery Word) (records : List (Forest.Record Index Word))
    (value : Word) (records' : List (Forest.Record Index Word))
    (hout : (value, records') ∈ (answer query records).support) :
    records'.length ≤ records.length + 1 := by
  simp only [answer, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨value, next⟩, _, heq⟩ := hout
  cases heq
  simp only [update]
  split <;> simp

/-- Recording a new miss never removes earlier ledger entries. -/
theorem answer_retains (query : Index × PermQuery Word) (records : List (Forest.Record Index Word))
    (value : Word) (records' : List (Forest.Record Index Word))
    (hout : (value, records') ∈ (answer query records).support) : records ⊆ records' := by
  simp only [answer, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨value, next⟩, _, heq⟩ := hout
  cases heq
  intro record hr
  simp only [update]
  split
  · exact List.mem_cons_of_mem _ hr
  · exact hr

/-- Every actual supported run has at most as many fresh entries as external calls. The query
budget supplies only the adversary's syntactic call bound; ledger size is derived from execution. -/
theorem run_length {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output)
    (Q : ℕ) (hQ : ProbOracleComp.IsQueryBounded program Q)
    (out : Output) (records : List (Forest.Record Index Word))
    (hout : (out, records) ∈ (ProbOracleComp.runWith answer program []).support) :
    records.length ≤ Q := by
  have hp := ProbOracleComp.run_interpret_withTranscript answer program [] []
  rw [← hp, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨out, records, trace⟩, hfull, heq⟩ := hout
  cases heq
  have hsize := ProbOracleComp.runWith_invariant (withTranscript answer)
    (fun state : List (Forest.Record Index Word) × Transcript (Family.Spec Index Word) =>
      state.1.length ≤ state.2.length) (fun query state hs value next hn => by
        obtain ⟨rows, log⟩ := state
        simp only [withTranscript, PMF.mem_support_map_iff] at hn
        obtain ⟨⟨value, rows'⟩, hrows, heq⟩ := hn
        cases heq
        have hg := answer_length query rows value rows' hrows
        simp only [List.length_cons]
        exact hg.trans (Nat.add_le_add_right hs 1))
    program ([], []) (by simp)
    out (records, trace) hfull
  exact hsize.trans (hQ.length_transcript_le answer hfull)

/-- The actual ledger instrument preserves the independent uniform family's output law. -/
theorem uniform_output [Fintype Index] {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      interpret (Family.probEval perms) program) =
        (ProbOracleComp.runWith answer program []).map Prod.fst := by
  rw [Family.uniform_prob_interpret_eq_lazy]
  have hp := congrArg (PMF.map Prod.fst) (project_run program)
  simpa only [ProbOracleComp.runWith, OracleComp.runWith, Family.probAnswer,
    PMF.map_comp, Function.comp_def] using hp.symm

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Ledger
