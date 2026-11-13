/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

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
* `Cslib.RandomOracle.eval_zoom_memoize_map`, `Cslib.RandomOracle.eval_zoom_memoize_bind`:
  component-cache `zoomStateT`/`memoize` representation bridges to `RandomOracle.answer`.
* `Cslib.RandomOracle.answer_bind_complete`, `Cslib.RandomOracle.answer_bind_complete₁`,
  `Cslib.RandomOracle.answer_bind_complete₂`: continuation-form table completion laws past
  independent samples.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3.

Extends the crypto-branch lazy-sampling proof at `5ff69ca93402e7c947208dc56396d6d86203ccd8`
to the disjoint-sum interface of `ProbOracleComp`, reusing the general state simulation rule.
-/

public section

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
    (h : (result, cache', transcript) ∈ (ProbOracleComp.runWith
        (OracleComp.withTranscript (memoize distribution)) program (cache, [])).support) :
    cache'.length ≤ cache.length + transcript.length ∧
      ∀ entry ∈ cache', entry ∈ cache ∨
        (⟨entry.1, entry.2⟩ ∈ transcript ∧ entry.2 ∈ (distribution entry.1).support) := by
  refine ProbOracleComp.runWith_invariant (OracleComp.withTranscript (memoize distribution))
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
    (h : (result, cache') ∈ (ProbOracleComp.runWith (memoize distribution) program cache).support) :
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
    (ProbOracleComp.runWith (memoize distribution) program cache).map
        (fun (result, cache') => (result, ofList cache')) =
      ProbOracleComp.runWith (answer distribution) program (ofList cache) := by
  apply ProbOracleComp.runWith_map_state
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
      ProbOracleComp.runWith (answer (fun q => ProbComp.eval (compute q))) program
        (ofList cache) := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  simpa only [ProbComp.eval_memoize] using
    run_interpret_memoize_prob (fun q => ProbComp.eval (compute q)) program cache

omit [BEq Query] in
/-- One lazy call on a component cache, with its result and represented state, is
`RandomOracle.answer` on the represented component. -/
theorem eval_zoom_memoize_map {Key Value St T β : Type} [DecidableEq Key]
    (get : St → List (Key × Value)) (set : St → List (Key × Value) → St) (d : ProbComp Value)
    (q : Key) (s : St) (g : Value → β) (rep : St → T)
    (F : Cache (fun _ : Key => Value) → T)
    (hrep : ∀ c, rep (set s c) = F (ofList c)) :
    (ProbComp.eval (zoomStateT get set (memoize (fun _ => d) q) s)).map
        (fun z => (g z.1, rep z.2)) =
      (answer (fun _ => ProbComp.eval d) q (ofList (get s))).map
        (fun z => (g z.1, F z.2)) := by
  rw [eval_zoomStateT_memoize, ← memoize_map_ofList]
  simp only [PMF.map_comp, Function.comp_def, hrep]

omit [BEq Query] in
/-- One lazy call on a component cache followed by a continuation, on represented states. -/
theorem eval_zoom_memoize_bind {Key Value St T β : Type} [DecidableEq Key]
    (get : St → List (Key × Value)) (set : St → List (Key × Value) → St) (d : ProbComp Value)
    (q : Key) (s : St) (f : Value → St → ProbComp (β × St)) (rep : St → T)
    (Φ : Value × Cache (fun _ : Key => Value) → PMF (β × T))
    (hf : ∀ v c, (ProbComp.eval (f v (set s c))).map (fun z => (z.1, rep z.2)) =
      Φ (v, ofList c)) :
    (ProbComp.eval (zoomStateT get set (memoize (fun _ => d) q) s >>=
        fun vs => f vs.1 vs.2)).map (fun z => (z.1, rep z.2)) =
      (answer (fun _ => ProbComp.eval d) q (ofList (get s))).bind Φ := by
  rw [ProbComp.eval_bind, eval_zoomStateT_memoize, ← memoize_map_ofList, PMF.map_bind,
    PMF.bind_map, PMF.bind_map]
  congr 1 with ⟨v, c⟩ : 1
  exact hf v c

end List

variable {Query α : Type} {Response : Query → Type} [Fintype Query]
  [∀ q, Finite (Response q)]

/-- Complete the cache before or after a client with fresh private randomness: the joint result
and complete-table distributions agree, even for arbitrary preassigned cache entries. -/
theorem run_interpret_answer_complete_prob [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q))
    (program : ProbOracleComp Response α) (cache : Cache Response) :
    (do
      let (result, cache') ← ProbOracleComp.runWith (answer distribution) program cache
      (complete distribution cache').map (result, ·)) =
      (do
        let table ← complete distribution cache
        (OracleComp.interpret
          (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program).map
            (·, table)) := by
  simp only [PMF.monad_bind_eq_bind]
  have h := ProbOracleComp.runWith_simulation (answer distribution)
    (fun q table => (PMF.pure (table q)).map (·, table)) (complete distribution)
    (fun q cache => by
      simpa only [PMF.monad_bind_eq_bind, PMF.map, Function.comp_def, PMF.pure_bind] using
        answer_complete distribution cache q) program cache
  refine h.trans (congrArg ((complete distribution cache).bind) (funext fun table => ?_))
  exact ProbOracleComp.runWith_readOnly
    (fun q (table : (q : Query) → Response q) => PMF.pure (table q)) program table

/-- Lazy sampling from an empty cache implements the eager table experiment for randomized,
adaptive clients, with private randomness independent of the table. -/
theorem interpret_prob_eq_lazy [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q)) (program : ProbOracleComp Response α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret
        (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      (ProbOracleComp.runWith (answer distribution) program (fun _ => none)).map Prod.fst :=
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
      (ProbOracleComp.runWith (answer (fun q => PMF.uniformOfFintype (Response q))) program
        (fun _ => none)).map Prod.fst := by
  simpa only [PMF.pi_uniformOfFintype] using
    interpret_prob_eq_lazy (fun q => PMF.uniformOfFintype (Response q)) program

/-- A list cache implements eager independent sampling for clients with private randomness. -/
theorem interpret_prob_eq_memoize {Value : Type} [Finite Value] [BEq Query] [LawfulBEq Query]
    (distribution : Query → PMF Value) (program : ProbOracleComp (fun _ : Query => Value) α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret (sumHandler ProbComp.unifOracle (fun q => PMF.pure (table q))) program) =
      (ProbOracleComp.runWith (memoize distribution) program []).map Prod.fst := by
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
  simpa only [ProbOracleComp.runWith, OracleComp.runWith, OracleComp.interpret_interpret,
    OracleComp.interpret_sumHandler, interpret_sample, ProbComp.unifFin,
    OracleComp.interpret_query, OracleComp.interpret_map, interpret_query, PMF.monad_map_eq_map,
    PMF.pure_map] using interpret_prob_eq_memoize distribution
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
  simp only [ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith, ProbComp.eval_memoize]

section AnswerComplete

variable {Q V α α' β : Type} [Fintype Q] [Finite V] [DecidableEq Q]

/-- Answering one query and completing its table is completing the table and reading it,
followed by any continuation `F` that ignores the intermediate cache. -/
theorem answer_bind_complete (d : Q → PMF V) (c : Cache (fun _ : Q => V))
    (q : Q) (F : V × Cache (fun _ : Q => V) → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (answer d q c).bind (fun x => (complete d x.2).bind (F x)) =
      (complete d c).bind (fun T => F (T q, c) T) := by
  have h := congrArg (fun p => p.bind (fun x => F (x.1, c) x.2)) (answer_complete d c q)
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map,
    Function.comp_def] at h
  rw [← h]
  congr 1 with ⟨v, c'⟩ : 1
  rw [hF v c' c]

/-- `answer_bind_complete` past one independent sample `p`. -/
theorem answer_bind_complete₁ (d : Q → PMF V) (c : Cache (fun _ : Q => V))
    (q : Q) (p : PMF α) (F : V × Cache (fun _ : Q => V) → α → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (answer d q c).bind (fun x => p.bind fun a =>
        (complete d x.2).bind (F x a)) =
      (complete d c).bind (fun T => p.bind fun a => F (T q, c) a T) := by
  simp only [PMF.bind_comm p]
  exact answer_bind_complete d c q (fun x T => p.bind fun a => F x a T)
    (fun v c₁ c₂ => by rw [hF v c₁ c₂])

/-- `answer_bind_complete` past two independent samples `p` and `p'`. -/
theorem answer_bind_complete₂ (d : Q → PMF V) (c : Cache (fun _ : Q => V))
    (q : Q) (p : PMF α) (p' : PMF α')
    (F : V × Cache (fun _ : Q => V) → α → α' → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (answer d q c).bind (fun x => p.bind fun a => p'.bind fun b =>
        (complete d x.2).bind (F x a b)) =
      (complete d c).bind (fun T => p.bind fun a => p'.bind fun b =>
        F (T q, c) a b T) := by
  simp only [PMF.bind_comm p]
  exact answer_bind_complete₁ d c q p' (fun x b T => p.bind fun a => F x a b T)
    (fun v c₁ c₂ => by rw [hF v c₁ c₂])

end AnswerComplete

end Cslib.RandomOracle
