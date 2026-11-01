/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# Lazy random functions with independent private randomness

The eager/lazy completion law also holds for clients interleaving external queries with fresh
private finite-uniform samples. Only external replies are cached. The joint law retains the
client's result and the completed table, including when a private sample or an earlier reply
determines a later query.

## Main results

* `Cslib.RandomOracle.run_interpret_answer_complete_prob`: the full joint completion law.
* `Cslib.RandomOracle.interpret_prob_eq_lazy`: the marginal eager/lazy equivalence.
* `Cslib.RandomOracle.uniform_interpret_prob_eq_lazy`: specialization to a uniform random function.
* `Cslib.RandomOracle.run_interpret_memoize_prob`: the list cache implements the partial table.
* `Cslib.RandomOracle.memoize_cache_bounds_prob`: external budgets control the list cache.
* `Cslib.RandomOracle.eval_run_interpret_memoize_prob`: closed samplers realize the list cache.
* `Cslib.RandomOracle.interpret_prob_eq_memoize_map`: injective representations preserve the game.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3.

Extends the crypto-branch lazy-sampling proof at `5ff69ca93402e7c947208dc56396d6d86203ccd8`
to the disjoint-sum interface of `ProbOracleComp`, reusing the general state simulation rule.
-/

@[expose] public section

namespace Cslib.RandomOracle

open Probability ProbOracleComp
open OracleComp (sumHandler)

section List

variable {Query Value α : Type} [BEq Query]

/-- Each new cache entry comes from an external request and its sampled answer. Private samples
do not add entries or enter the external transcript. Arbitrary initial lists are allowed. -/
private theorem run_interpret_memoize_transcript_prob (distribution : Query → PMF Value)
    (program : ProbOracleComp (fun _ : Query => Value) α) (cache cache' : List (Query × Value))
    (result : α) (transcript : OracleComp.Transcript (fun _ : Query => Value))
    (h : (result, cache', transcript) ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript (memoize distribution))) program).run (cache, [])).support) :
    cache'.length ≤ cache.length + transcript.length ∧
      ∀ entry ∈ cache', entry ∈ cache ∨
        (⟨entry.1, entry.2⟩ ∈ transcript ∧ entry.2 ∈ (distribution entry.1).support) := by
  refine ProbOracleComp.run_interpret_invariant (OracleComp.withTranscript (memoize distribution))
    (fun (current, seen) => current.length ≤ cache.length + seen.length ∧
      ∀ entry ∈ current, entry ∈ cache ∨
        (⟨entry.1, entry.2⟩ ∈ seen ∧ entry.2 ∈ (distribution entry.1).support))
    ?_ program (cache, []) (by simp) result (cache', transcript) h
  rintro q ⟨current, seen⟩ ⟨hcount, hentries⟩ answer next hnext
  simp only [OracleComp.withTranscript, PMF.mem_support_map_iff, mem_support_memoize_iff] at hnext
  obtain ⟨⟨value, current'⟩, hvalue, heq⟩ := hnext
  cases heq
  dsimp only at hvalue
  rcases hvalue with ⟨_, rfl⟩ | ⟨_, hfresh, rfl⟩ <;> grind

/-- External query budgets control cache growth and new-entry provenance for randomized clients.
Preassigned entries are retained regardless of the sampling distribution's support. -/
theorem memoize_cache_bounds_prob (distribution : Query → PMF Value)
    (program : ProbOracleComp (fun _ : Query => Value) α) (size : Query → ℕ) (calls maxSize : ℕ)
    (hcalls : program.IsQueryBounded calls) (hsize : program.QueriesSatisfy (size · ≤ maxSize))
    (cache cache' : List (Query × Value)) (result : α)
    (h : (result, cache') ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (memoize distribution))
        program).run cache).support) :
    cache'.length ≤ cache.length + calls ∧
      ∀ entry ∈ cache', entry ∈ cache ∨
        (size entry.1 ≤ maxSize ∧ entry.2 ∈ (distribution entry.1).support) := by
  rw [← ProbOracleComp.run_interpret_withTranscript (memoize distribution) program cache [],
    PMF.mem_support_map_iff] at h
  obtain ⟨⟨value, state⟩, hstate, heq⟩ := h
  cases heq
  obtain ⟨hcount, hentries⟩ := run_interpret_memoize_transcript_prob distribution program cache
    state.1 result state.2 hstate
  refine ⟨hcount.trans (Nat.add_le_add_left
    (hcalls.length_transcript_le (memoize distribution) hstate) _), ?_⟩
  intro entry hentry
  rcases hentries entry hentry with h | ⟨hseen, hsupport⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsize.forall_mem_transcript (memoize distribution) hstate _ hseen, hsupport⟩

/-- List memoization implements the mathematical random oracle for clients with private samples,
retaining the result and represented final cache even over infinite query domains. -/
theorem run_interpret_memoize_prob [LawfulBEq Query] [DecidableEq Query]
    (distribution : Query → PMF Value) (program : ProbOracleComp (fun _ : Query => Value) α)
    (cache : List (Query × Value)) :
    ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (memoize distribution))
        program).run cache).map (fun (result, cache') => (result, ofList cache')) =
      (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
          program).run (ofList cache) := by
  apply ProbOracleComp.run_interpret_map_state
  intro q current
  simpa only [OracleComp.interpret_query, StateT.run] using
    run_interpret_memoize distribution (OracleComp.query q) current

/-- Closed samplers and the client's private randomness implement the same joint result/cache
law as the mathematical lazy oracle. Only external requests are memoized. -/
theorem eval_run_interpret_memoize_prob [LawfulBEq Query] [DecidableEq Query]
    (compute : Query → ProbComp Value) (program : ProbOracleComp (fun _ : Query => Value) α)
    (cache : List (Query × Value)) :
    (ProbComp.eval ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (memoize compute)) program).run
        cache)).map (fun (result, cache') => (result, ofList cache')) =
      (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (answer (fun q => ProbComp.eval (compute q)))) program).run (ofList cache) := by
  rw [ProbOracleComp.eval_run_interpret]
  simpa only [ProbComp.eval_memoize] using
    run_interpret_memoize_prob (fun q => ProbComp.eval (compute q)) program cache

end List

variable {Query α : Type} {Response : Query → Type} [Fintype Query]
  [∀ q, Finite (Response q)]

/-- Complete the cache before or after a client with fresh private randomness: the joint result
and complete-table distributions agree, even for arbitrary preassigned cache entries. -/
theorem run_interpret_answer_complete_prob [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q))
    (program : ProbOracleComp Response α) (cache : Cache Response) :
    (do
      let (result, cache') ← (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
          program).run cache
      (complete distribution cache').map (result, ·)) =
      (do
        let table ← complete distribution cache
        (OracleComp.interpret
          (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program).map
            (·, table)) := by
  simp only [PMF.monad_bind_eq_bind]
  have h := ProbOracleComp.run_interpret_simulation (answer distribution)
    (fun q table => (PMF.pure (table q)).map (·, table)) (complete distribution)
    (fun q cache => by
      simpa only [PMF.monad_bind_eq_bind, PMF.map, Function.comp_def, PMF.pure_bind] using
        answer_complete distribution cache q) program cache
  refine h.trans (congrArg ((complete distribution cache).bind) (funext fun table => ?_))
  exact ProbOracleComp.run_interpret_readOnly
    (fun q (table : (q : Query) → Response q) => PMF.pure (table q)) program table

/-- Lazy sampling from an empty cache implements the eager table experiment for randomized,
adaptive clients, with private randomness independent of the table. -/
theorem interpret_prob_eq_lazy [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q)) (program : ProbOracleComp Response α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret
        (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (answer distribution))
          program).run (fun _ => none)).map Prod.fst :=
  pi_bind_eq_map_fst_of_complete_eq distribution
    (run_interpret_answer_complete_prob distribution program (fun _ => none))

/-- A uniform random function can be implemented by consistent lazy uniform replies even when
the client uses private randomness between its adaptive queries. -/
theorem uniform_interpret_prob_eq_lazy [DecidableEq Query] [∀ q, Fintype (Response q)]
    [∀ q, Nonempty (Response q)] (program : ProbOracleComp Response α) :
    (do
      let table ← PMF.uniformOfFintype ((q : Query) → Response q)
      OracleComp.interpret
        (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (answer (fun q => PMF.uniformOfFintype (Response q))))
            program).run (fun _ => none)).map Prod.fst := by
  simpa only [PMF.pi_uniformOfFintype] using
    interpret_prob_eq_lazy (fun q => PMF.uniformOfFintype (Response q)) program

/-- A list cache implements eager independent sampling for clients with private randomness. -/
theorem interpret_prob_eq_memoize {Value : Type} [Finite Value] [BEq Query] [LawfulBEq Query]
    (distribution : Query → PMF Value) (program : ProbOracleComp (fun _ : Query => Value) α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (memoize distribution))
          program).run []).map Prod.fst := by
  classical
  rw [interpret_prob_eq_lazy]
  have h := congrArg (PMF.map Prod.fst) (run_interpret_memoize_prob distribution program [])
  simpa only [PMF.map_comp, Function.comp_def, ofList_nil] using h.symm

/-- Injective keys and mapped values implement the same finite random function, including
independent private samples and adaptive external queries in the client. -/
theorem interpret_prob_eq_memoize_map {Value Key' Value' : Type} [Finite Value]
    [BEq Query] [LawfulBEq Query] [BEq Key'] [LawfulBEq Key']
    (keyMap : Query ↪ Key') (valueMap : Value → Value')
    (distribution : Query → PMF Value) (sample' : Key' → PMF Value')
    (hsample : ∀ key, sample' (keyMap key) = (distribution key).map valueMap)
    (program : ProbOracleComp (fun _ : Query => Value') α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret
        (sumHandler ProbComp.unifOracle (fun key => PMF.pure (valueMap (table key)))) program) =
      ((OracleComp.interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun key => memoize sample' (keyMap key))) program).run []).map Prod.fst := by
  let represent := fun cache : List (Query × Value) =>
    cache.map (fun entry => (keyMap entry.1, valueMap entry.2))
  have hrun := ProbOracleComp.run_interpret_map_response_state (fun _ => valueMap)
    (memoize distribution) (fun key => memoize sample' (keyMap key)) represent
    (fun key cache => by
      simpa only [represent, PMF.monad_map_eq_map] using
        memoize_map keyMap valueMap distribution sample' hsample key cache) program []
  have houtput := congrArg (PMF.map Prod.fst) hrun
  simp only [PMF.map_comp, Function.comp_def, represent, List.map_nil] at houtput
  rw [← houtput]
  simpa only [OracleComp.interpret_interpret, OracleComp.interpret_sumHandler, interpret_sample,
    ProbComp.unifFin, OracleComp.interpret_query, OracleComp.interpret_map, interpret_query,
    PMF.monad_map_eq_map, PMF.pure_map] using interpret_prob_eq_memoize distribution
      (OracleComp.interpret (sumHandler (fun n => sample (ProbComp.unifFin n))
        (fun key => valueMap <$> ProbOracleComp.query key)) program)

/-- Executable closed samplers with a list cache implement the eager independent-table experiment,
including the adversary's private samples and adaptive external calls. -/
theorem eval_run_interpret_memoize_prob_eq_eager {Key Value Result : Type}
    [Fintype Key] [Finite Value] [BEq Key] [LawfulBEq Key]
    (compute : Key → ProbComp Value) (program : ProbOracleComp (fun _ : Key => Value) Result) :
    ProbComp.eval (Prod.fst <$> (OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (memoize compute)) program).run []) =
        (do
          let table ← PMF.pi (fun q => ProbComp.eval (compute q))
          OracleComp.interpret (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q)))
            program) := by
  rw [interpret_prob_eq_memoize]
  simp only [ProbComp.eval_map, ProbOracleComp.eval_run_interpret, ProbComp.eval_memoize]

end Cslib.RandomOracle
