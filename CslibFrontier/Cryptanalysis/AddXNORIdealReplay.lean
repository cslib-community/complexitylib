/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealLedger
public import CslibFrontier.Cryptanalysis.AddXNORIdealCoupling
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Joint replay of the visible transcript, fresh ledger and hidden family

The cut-hit event depends on unqueried permutation entries. An output marginal cannot justify
its probability. `run_completion` retains both the complete hidden family and every visible
request while replaying the actual indexed sampler. Its local completion identity is derived
from `RandomPermutation.Family.answer_complete`; no simulation law is assumed.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.State`: fresh entries, visible log and family.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.answer`: concrete eager instrument.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.run_completion`: joint eager/lazy replay law.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.erase_records`: the actual original reader's
  visible transcript is unchanged.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.fresh_law`: joint result/ledger law after
  erasing the hidden family and visible log.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay.run_recorded`: every visible request,
  including cache hits, has a representative in the actual fresh ledger.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay

open Probability OracleComp RandomPermutation

/-- Replay retains the hidden permutation family without putting it in the visible log. -/
structure State (Index Word : Type) where
  /-- Only actual cache misses, newest first. -/
  records : List (Forest.Record Index Word)
  /-- All external requests and replies, newest first. -/
  trace : Transcript (Family.Spec Index Word)
  /-- The private complete family used by the eager experiment. -/
  perms : Index → Equiv.Perm Word

variable {Index Word : Type} [DecidableEq Index] [Fintype Word] [DecidableEq Word]
  [Nonempty Word]

/-- Read the original hidden family and update the actual fresh ledger and visible transcript. -/
@[expose] noncomputable def answer (query : Index × PermQuery Word) :
    StateT (State Index Word) PMF Word := fun state =>
  let value := Family.eval state.perms query
  PMF.pure (value,
    { records := Ledger.update query value state.records
      trace := ⟨query, value⟩ :: state.trace
      perms := state.perms })

variable [Fintype Index]

/-- Complete the actual fresh caches, retaining the entire visible log. -/
@[expose] noncomputable def completion
    (state : List (Forest.Record Index Word) × Transcript (Family.Spec Index Word)) :
    PMF (State Index Word) :=
  (Family.complete (Ledger.tables state.1)).map fun perms => ⟨state.1, state.2, perms⟩

private theorem answer_completion (query : Index × PermQuery Word)
    (state : List (Forest.Record Index Word) × Transcript (Family.Spec Index Word))
    (hv : Family.Valid (Ledger.tables state.1)) :
    ((withTranscript Ledger.answer) query state).bind
        (fun (value, next) => (completion next).map (value, ·)) =
      (completion state).bind (answer query) := by
  obtain ⟨records, trace⟩ := state
  simp only [withTranscript, Ledger.answer, PMF.bind_map, Function.comp_def,
    completion, PMF.map_comp]
  have h := congrArg (PMF.map (fun (value, perms) =>
      (value, State.mk (Ledger.update query value records) (⟨query, value⟩ :: trace) perms)))
    (Family.answer_complete query (Ledger.tables records) hv)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  calc
    _ = (Family.answer query (Ledger.tables records)).bind
        (fun (value, next) => (Family.complete next).map fun perms =>
          (value, State.mk (Ledger.update query value records)
            (⟨query, value⟩ :: trace) perms)) := by
      apply PMF.bind_congr_on_support
      rintro ⟨value, next⟩ hout
      rw [Ledger.tables_update_of_support query records hv value next hout]
    _ = _ := by
      rw [h]
      simp only [answer, Function.comp_def, PMF.map]

/-- Exact joint law for adaptive private-coin execution: complete only after the actual lazy
run, or complete first and replay while retaining the hidden family, fresh entries and log.
Initial table validity is the sampler's structural invariant, not a security premise. -/
theorem run_completion {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (state : List (Forest.Record Index Word) × Transcript (Family.Spec Index Word))
    (hv : Family.Valid (Ledger.tables state.1)) :
    (ProbOracleComp.runWith (withTranscript Ledger.answer) program state).bind
        (fun (value, next) => (completion next).map (value, ·)) =
      (completion state).bind (ProbOracleComp.runWith answer program) := by
  let handler : (query : ℕ ⊕ (Index × PermQuery Word)) →
      StateT (List (Forest.Record Index Word) ×
        Transcript (Family.Spec Index Word)) PMF
        (probOracleSpec (Family.Spec Index Word) query) :=
    sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript Ledger.answer)
  let handler' : (query : ℕ ⊕ (Index × PermQuery Word)) →
      StateT (State Index Word) PMF (probOracleSpec (Family.Spec Index Word) query) :=
    sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) answer
  apply OracleComp.run_interpret_simulation_of_invariant handler handler' completion
    (fun state => Family.Valid (Ledger.tables state.1)) ?_ ?_ program state hv
  · rintro (n | query) ⟨records, trace⟩ hvalid value next hout
    · have hm : (value, next) ∈
          ((ProbComp.unifOracle n).map (·, (records, trace))).support := by
        simpa only [handler, StateT.lift, pmf_norm, PMF.map] using hout
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨coin, _, heq⟩ := hm
      cases heq
      exact hvalid
    · simp only [handler, withTranscript, PMF.mem_support_map_iff] at hout
      obtain ⟨⟨value, records'⟩, hrecords, heq⟩ := hout
      cases heq
      exact Ledger.answer_valid query records hvalid value records' hrecords
  · rintro (n | query) state hvalid
    · simp only [handler, handler', sumHandler, StateT.lift, pmf_norm, PMF.map]
      exact PMF.bind_comm _ _ _
    · exact answer_completion query state hvalid

/-- Starting from empty caches, replay samples precisely the independent uniform family. -/
theorem uniform_run {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      ProbOracleComp.runWith answer program ⟨[], [], perms⟩) =
      (ProbOracleComp.runWith (withTranscript Ledger.answer) program ([], [])).bind
        (fun (value, next) => (completion next).map (value, ·)) := by
  have h := run_completion program ([], []) Family.valid_empty
  have he : completion ([], []) =
      (PMF.uniformOfFintype (Index → Equiv.Perm Word)).map (fun perms =>
        State.mk [] [] perms) := by
    have ht : Ledger.tables ([] : List (Forest.Record Index Word)) = (fun _ => []) := rfl
    rw [completion, ht, Family.complete_empty]
  rw [he, PMF.bind_map] at h
  exact h.symm

/-- Erasing only the completed hidden family gives the actual lazy joint output, fresh ledger
and complete transcript. Thus collision predicates retain their exact probability as well. -/
theorem lazy_law {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      ProbOracleComp.runWith answer program ⟨[], [], perms⟩).map
        (fun (out, state) => (out, (state.records, state.trace)))) =
      ProbOracleComp.runWith (withTranscript Ledger.answer) program ([], []) := by
  rw [uniform_run, PMF.map_bind]
  calc
    _ = (ProbOracleComp.runWith (withTranscript Ledger.answer) program ([], [])).bind
        PMF.pure := by
      congr 1
      funext ⟨out, records, trace⟩
      simp only [completion, PMF.map_comp, Function.comp_def]
      exact PMF.map_const _ _
    _ = _ := PMF.bind_pure _

/-- Erasing both the complete log and the hidden family preserves the joint result/fresh-ledger
law of the original indexed sampler. -/
theorem fresh_law {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      ProbOracleComp.runWith answer program ⟨[], [], perms⟩).map
        (fun (out, state) => (out, state.records))) =
      ProbOracleComp.runWith Ledger.answer program [] := by
  have h := congrArg (PMF.map (fun (out, records, _) => (out, records))) (lazy_law program)
  have ht := ProbOracleComp.run_interpret_withTranscript Ledger.answer program [] []
  simpa only [PMF.map_comp, Function.comp_def] using h.trans ht

omit [Fintype Word] [Nonempty Word] [Fintype Index] in
/-- The eager transcript is the ordinary original-reader transcript, erasing only the fresh
ledger and the private family. The family remains fixed throughout supported execution. -/
theorem erase_records {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) (initial : State Index Word) :
    (ProbOracleComp.runWith answer program initial).map
        (fun (out, next) => (out, ((), next.trace))) =
      ProbOracleComp.runWith (withTranscript (Visible.reader initial.perms)) program
        ((), initial.trace) := by
  apply ProbOracleComp.runWith_map_state_of_invariant answer
    (withTranscript (Visible.reader initial.perms)) (fun state => ((), state.trace))
    (fun state => state.perms = initial.perms) ?_ ?_ program initial rfl
  · intro query state hs value next hn
    simp only [answer, PMF.mem_support_pure_iff] at hn
    cases hn
    exact hs
  · intro query state hs
    simp [answer, Visible.reader, withTranscript, hs]

omit [Fintype Word] [Fintype Index] in
/-- Every supported eager transcript entry has an actual representative in its fresh ledger.
This is transported through the proved full joint law, not assumed about the eager state. -/
theorem run_recorded [Finite Index] [Finite Word] {Output : Type} (perms : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (out : Output) (state : State Index Word)
    (hout : (out, state) ∈ (ProbOracleComp.runWith answer program ⟨[], [], perms⟩).support) :
    ∀ entry ∈ state.trace, Ledger.Recorded state.records entry.1 entry.2 := by
  let : Fintype Index := Fintype.ofFinite Index
  let : Fintype Word := Fintype.ofFinite Word
  have hu : (out, state) ∈ ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind
      fun perms => ProbOracleComp.runWith answer program ⟨[], [], perms⟩).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨perms, by simp, hout⟩
  rw [uniform_run, PMF.mem_support_bind_iff] at hu
  obtain ⟨⟨out', records, trace⟩, hrun, hstate⟩ := hu
  simp only [completion, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hstate
  obtain ⟨perms', _, he⟩ := hstate
  cases he
  exact Ledger.run_recorded program out records trace hrun

omit [Fintype Word] [Nonempty Word] [Fintype Index] in
/-- The stored visible replies are actual evaluations of the original fixed hidden family. -/
theorem run_trace_eval {Output : Type} (perms : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (out : Output) (state : State Index Word)
    (hout : (out, state) ∈ (ProbOracleComp.runWith answer program ⟨[], [], perms⟩).support) :
    state.perms = perms ∧ ∀ entry ∈ state.trace, entry.2 = Family.eval perms entry.1 := by
  apply ProbOracleComp.runWith_invariant answer
    (fun state => state.perms = perms ∧
      ∀ entry ∈ state.trace, entry.2 = Family.eval perms entry.1) ?_
    program ⟨[], [], perms⟩ ⟨rfl, by simp⟩ out state hout
  intro query state hs value next hn
  simp only [answer, PMF.mem_support_pure_iff] at hn
  cases hn
  refine ⟨hs.1, ?_⟩
  intro entry hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact congrArg (fun perms => Family.eval perms query) hs.1
  · exact hs.2 entry hm

omit [Fintype Word] [Nonempty Word] [Fintype Index] in
/-- Only prepending visible entries is possible during a replay. -/
theorem run_trace_suffix {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) (initial : State Index Word)
    (out : Output) (state : State Index Word)
    (hout : (out, state) ∈ (ProbOracleComp.runWith answer program initial).support) :
    initial.trace <:+ state.trace := by
  apply ProbOracleComp.runWith_invariant answer (fun state => initial.trace <:+ state.trace)
    (fun query state hs value next hn => ?_) program initial (List.suffix_refl _) out state hout
  simp only [answer, PMF.mem_support_pure_iff] at hn
  cases hn
  exact hs.trans (List.suffix_cons _ _)

omit [Fintype Word] [Nonempty Word] [Fintype Index] in
/-- The replay never removes or reorders old fresh entries. -/
theorem run_records_suffix {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) (initial : State Index Word)
    (out : Output) (state : State Index Word)
    (hout : (out, state) ∈ (ProbOracleComp.runWith answer program initial).support) :
    initial.records <:+ state.records := by
  apply ProbOracleComp.runWith_invariant answer (fun state => initial.records <:+ state.records)
    (fun query state hs value next hn => ?_) program initial (List.suffix_refl _) out state hout
  simp only [answer, PMF.mem_support_pure_iff] at hn
  cases hn
  simp only [Ledger.update]
  split
  · exact hs.trans (List.suffix_cons _ _)
  · exact hs

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Replay
