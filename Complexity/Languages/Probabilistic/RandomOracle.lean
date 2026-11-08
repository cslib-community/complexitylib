/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.Memoize
public import Complexity.Probability.Product

import Complexity.Languages.Probabilistic.Semantics

/-!
# Lazy sampling of random functions

`RandomOracle.answer` samples a response on the first occurrence of a query and reuses it on
later calls. It supports arbitrary query domains, dependent response types, and a separate
distribution for each query. A cache may also contain answers fixed in advance.

On finite domains and finite response types, `run_interpret_answer_complete` proves the stronger
form of eager/lazy equivalence: completing the cache after an adaptive program has the same
joint law as completing it before the program. `interpret_eq_lazy` discards the final table, and
`uniform_interpret_eq_lazy` specializes to a uniformly random function.

`memoize` supplies an ordinary association-list implementation. `run_interpret_memoize` relates its
complete executions to the mathematical cache, including on infinite query domains. Its closed
efficiency certificate is in `Computability.Probabilistic.Memoize`.
`memoize_cache_bounds` derives cache cardinality and entry provenance from the program's query
bounds; a computational certificate must also account for the encoded sizes of keys and replies.

## Main definitions

* `RandomOracle.Cache`, `.answer`, `.complete`: partial tables, consistent replies and completion.
* `RandomOracle.ofList`: represent a list cache by its first occurrence at each key.

## Main results

* `RandomOracle.run_interpret_answer_complete`: eager/lazy equivalence of the result and table.
* `RandomOracle.uniform_interpret_eq_lazy`: replace a uniformly sampled function by a lazy oracle.
* `RandomOracle.run_interpret_memoize`: association-list implementation with joint state semantics.
* `RandomOracle.memoize_cache_bounds`: query bounds control cache growth and entry provenance.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3, uses consistent lazy sampling in the adaptive hybrid argument.

Adapted from Languages/Probabilistic/RandomOracle.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using `OracleComp.interpret` and generic
monad morphisms.
-/

@[expose] public section

namespace Cslib.RandomOracle

open Probability

universe u

variable {Query : Type u} {Response : Query → Type u} {α : Type u}

/-- Previously assigned responses, indexed by their typed queries. -/
abbrev Cache (Response : Query → Type u) := (q : Query) → Option (Response q)

/-- Return a cached answer, or sample and store one fresh answer. -/
noncomputable def answer [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (q : Query) : StateT (Cache Response) PMF (Response q) := fun cache =>
  match cache q with
  | some value => PMF.pure (value, cache)
  | none => (distribution q).map (fun value => (value, Function.update cache q (some value)))

/-- A cache hit does not change the cache or draw fresh randomness. -/
theorem answer_of_some [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) (q : Query) (value : Response q) (h : cache q = some value) :
    answer distribution q cache = PMF.pure (value, cache) := by
  simp [answer, h]

/-- A previously unseen query draws exactly one response from its designated distribution. -/
theorem answer_of_none [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) (q : Query) (h : cache q = none) :
    answer distribution q cache =
      (distribution q).map (fun value => (value, Function.update cache q (some value))) := by
  simp [answer, h]

section List

variable {Value : Type u} [BEq Query]

/-- A supported memoized call either returns the first cached value unchanged, or samples and
prepends exactly one new entry. Initial cached values need not belong to the sampling support. -/
theorem mem_support_memoize_iff (distribution : Query → PMF Value)
    (key : Query) (cache : List (Query × Value)) (result : Value × List (Query × Value)) :
    result ∈ (memoize distribution key cache).support ↔
      (cache.lookup key = some result.1 ∧ result.2 = cache) ∨
      (cache.lookup key = none ∧ result.1 ∈ (distribution key).support ∧
        result.2 = (key, result.1) :: cache) := by
  rcases result with ⟨value, next⟩
  cases h : cache.lookup key <;>
    simp [memoize, h, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, Prod.ext_iff, eq_comm]

/-- A memoized sampler preserves any property of its key-value entries and returns a value with
that property at the requested key. Cache keys need not be unique. -/
theorem memoize_invariant [LawfulBEq Query] (distribution : Query → PMF Value)
    (property : Query → Value → Prop) (key : Query) (cache : List (Query × Value))
    (hcache : ∀ entry ∈ cache, property entry.1 entry.2)
    (hsample : ∀ value ∈ (distribution key).support, property key value)
    (result : Value × List (Query × Value))
    (hresult : result ∈ (memoize distribution key cache).support) :
    property key result.1 ∧ ∀ entry ∈ result.2, property entry.1 entry.2 := by
  rcases (mem_support_memoize_iff _ _ _ _).mp hresult with
    ⟨hlookup, hnext⟩ | ⟨_, hvalue, hnext⟩
  · rw [hnext]
    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hlookup
    exact ⟨hcache (key, result.1) (by simp [hlist]), hcache⟩
  · rw [hnext]
    exact ⟨hsample result.1 hvalue, by simpa using And.intro (hsample result.1 hvalue) hcache⟩

/-- Each memoized call adds at most one entry. Every new entry records an actual query and an
answer in its sampling distribution's support. Repeated calls still appear in the transcript. -/
private theorem run_interpret_memoize_transcript (distribution : Query → PMF Value)
    (program : OracleComp (fun _ : Query => Value) α) (cache cache' : List (Query × Value))
    (result : α) (transcript : OracleComp.Transcript (fun _ : Query => Value))
    (h : (result, cache', transcript) ∈ ((OracleComp.interpret
      (OracleComp.withTranscript (memoize distribution)) program).run (cache, [])).support) :
    cache'.length ≤ cache.length + transcript.length ∧
      ∀ entry ∈ cache', entry ∈ cache ∨
        (⟨entry.1, entry.2⟩ ∈ transcript ∧ entry.2 ∈ (distribution entry.1).support) := by
  refine OracleComp.run_interpret_invariant (OracleComp.withTranscript (memoize distribution))
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

/-- Query bounds control the number and provenance of all new cache entries. The sampler's own
support bound can then bound stored replies, without assuming that each call grows by a constant. -/
theorem memoize_cache_bounds (distribution : Query → PMF Value)
    (program : OracleComp (fun _ : Query => Value) α) (size : Query → ℕ) (calls maxSize : ℕ)
    (hcalls : program.IsQueryBounded calls) (hsize : program.QueriesSatisfy (size · ≤ maxSize))
    (cache cache' : List (Query × Value)) (result : α)
    (h : (result, cache') ∈
      ((OracleComp.interpret (memoize distribution) program).run cache).support) :
    cache'.length ≤ cache.length + calls ∧
      ∀ entry ∈ cache', entry ∈ cache ∨
        (size entry.1 ≤ maxSize ∧ entry.2 ∈ (distribution entry.1).support) := by
  rw [← OracleComp.run_interpret_withTranscript (memoize distribution) program cache [],
    PMF.mem_support_map_iff] at h
  obtain ⟨⟨value, state⟩, hstate, heq⟩ := h
  cases heq
  obtain ⟨hcount, hentries⟩ := run_interpret_memoize_transcript distribution program cache state.1
    result state.2 hstate
  refine ⟨hcount.trans (Nat.add_le_add_left
    (hcalls.length_transcript_le (memoize distribution) hstate) _), ?_⟩
  intro entry hentry
  rcases hentries entry hentry with h | ⟨hseen, hsupport⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsize.forall_mem_transcript (memoize distribution) hstate _ hseen, hsupport⟩

/-- Interpret a finite association list as a partial function. The first occurrence of a key
determines its value, so arbitrary initial lists are supported without a uniqueness invariant. -/
def ofList (cache : List (Query × Value)) : Cache (fun _ : Query => Value) :=
  fun q => cache.lookup q

/-- The empty list represents the empty cache. -/
@[simp] theorem ofList_nil : ofList ([] : List (Query × Value)) = fun _ => none := rfl

variable [LawfulBEq Query]

/-- At most `cache.length` keys have a value recorded in `cache`. -/
theorem card_filter_lookup_isSome_le [Fintype Query] (cache : List (Query × Value)) :
    (Finset.univ.filter fun q : Query => (cache.lookup q).isSome = true).card ≤ cache.length := by
  classical
  calc (Finset.univ.filter fun q : Query => (cache.lookup q).isSome = true).card
      ≤ (cache.map Prod.fst).toFinset.card := by
        refine Finset.card_le_card fun q hq => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hq
        obtain ⟨v, hv⟩ := hq
        obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hv
        have hmem : (q, v) ∈ cache := by simp [hlist]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hmem)
    _ ≤ (cache.map Prod.fst).length := List.toFinset_card_le _
    _ = cache.length := List.length_map Prod.fst

variable [DecidableEq Query]

/-- Prepending a cache entry updates exactly its key in the represented partial function. -/
theorem ofList_cons (cache : List (Query × Value)) (q : Query) (value : Value) :
    ofList ((q, value) :: cache) = Function.update (ofList cache) q (some value) := by
  funext query
  by_cases h : query = q
  · subst query
    simp [ofList]
  · simp [ofList, List.lookup_cons, h, beq_eq_false_iff_ne.mpr h]

/-- Mapping the list cache by `ofList` turns one `memoize` call into `answer`. -/
theorem memoize_map_ofList (distribution : Query → PMF Value) (q : Query)
    (cache : List (Query × Value)) :
    (memoize distribution q cache).map (fun (result, cache') => (result, ofList cache')) =
      answer distribution q (ofList cache) := by
  cases h : cache.lookup q with
  | none =>
    rw [memoize_of_none _ _ _ h, answer_of_none distribution (ofList cache) q h]
    change ((distribution q).map (fun value => (value, (q, value) :: cache))).map _ = _
    simp only [PMF.map_comp, Function.comp_def, ofList_cons]
  | some value =>
    rw [memoize_of_some _ _ _ _ h, answer_of_some distribution (ofList cache) q value h]
    exact PMF.pure_map _ _

/-- The ordinary list-based memoizer implements the mathematical random oracle, preserving the
result and represented final cache for every adaptive program, even on an infinite query domain. -/
theorem run_interpret_memoize (distribution : Query → PMF Value)
    (program : OracleComp (fun _ : Query => Value) α) (cache : List (Query × Value)) :
    ((OracleComp.interpret (memoize distribution) program).run cache).map
        (fun (result, cache') => (result, ofList cache')) =
      (OracleComp.interpret (answer distribution) program).run (ofList cache) :=
  OracleComp.run_interpret_map_state _ _ _ (memoize_map_ofList distribution) program cache

end List

section Finite

variable [Fintype Query] [∀ q, Finite (Response q)]

/-- Independently fill all missing entries while retaining the previously assigned answers. -/
noncomputable def complete (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) : PMF ((q : Query) → Response q) :=
  PMF.pi (fun q => (cache q).elim (distribution q) PMF.pure)

/-- Completing the empty cache samples all coordinates independently. -/
@[simp] theorem complete_empty (distribution : (q : Query) → PMF (Response q)) :
    complete distribution (fun _ => none) = PMF.pi distribution := rfl

/-- A completion agrees with every answer already in the cache. -/
theorem complete_agrees (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) (table : (q : Query) → Response q)
    (htable : table ∈ (complete distribution cache).support)
    (q : Query) (value : Response q) (h : cache q = some value) : table q = value := by
  have hq := (PMF.mem_support_pi_iff _ _).mp htable q
  simpa only [h, Option.elim_some, PMF.mem_support_pure_iff] using hq

/-- Fixing one cache entry fixes the corresponding coordinate of its completion. -/
theorem complete_update [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) (q : Query) (value : Response q) :
    complete distribution (Function.update cache q (some value)) =
      PMF.pi (Function.update (fun q => (cache q).elim (distribution q) PMF.pure)
        q (PMF.pure value)) := by
  unfold complete
  congr 1
  funext query
  by_cases h : query = q
  · subst query
    simp
  · simp [Function.update_of_ne h]

/-- Answering one query and completing the cache gives the same joint answer and table as
completing first and reading the table. -/
theorem answer_complete [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (cache : Cache Response) (q : Query) :
    (do
      let (value, cache') ← answer distribution q cache
      (complete distribution cache').map (value, ·)) =
        (complete distribution cache).map (fun table => (table q, table)) := by
  simp only [PMF.monad_bind_eq_bind]
  cases h : cache q with
  | none =>
    simp only [answer, h, PMF.bind_map, Function.comp_def, complete_update]
    simpa only [h, Option.elim_none, complete] using
      PMF.pi_bind_update_pair (fun q => (cache q).elim (distribution q) PMF.pure) q
  | some value =>
    simp only [answer, h, PMF.pure_bind]
    symm
    exact PMF.map_congr_on_support _ _ _ (fun table htable => by
      rw [complete_agrees distribution cache table htable q value h])

/-- Eager/lazy equivalence including the final complete table, for every adaptive program and
every initial cache. Later continuations can inspect both the result and that table. -/
theorem run_interpret_answer_complete [DecidableEq Query]
    (distribution : (q : Query) → PMF (Response q))
    (program : OracleComp Response α) (cache : Cache Response) :
    (do
      let (result, cache') ← (OracleComp.interpret (answer distribution) program).run cache
      (complete distribution cache').map (result, ·)) =
        (do
          let table ← complete distribution cache
          (OracleComp.interpret (fun q => PMF.pure (table q)) program).map (·, table)) := by
  simp only [PMF.monad_bind_eq_bind]
  have h := OracleComp.run_interpret_simulation (answer distribution)
    (fun q table => (·, table) <$> PMF.pure (table q)) (complete distribution)
    (fun q cache => by
      simpa only [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.pure_map, PMF.map,
        Function.comp_def, PMF.pure_bind] using
        answer_complete distribution cache q) program cache
  refine h.trans (congrArg ((complete distribution cache).bind) (funext fun table => ?_))
  simpa only [PMF.monad_map_eq_map] using OracleComp.run_interpret_readOnly
    (fun q (table : (q : Query) → Response q) => PMF.pure (table q)) program table

/-- Marginalizing a joint result-and-table completion identity over the completed table gives
equality of the eager and lazy result distributions. -/
theorem pi_bind_eq_map_fst_of_complete_eq (distribution : (q : Query) → PMF (Response q))
    {lazy : PMF (α × Cache Response)} {eager : ((q : Query) → Response q) → PMF α}
    (h : (do
      let (result, cache') ← lazy
      (complete distribution cache').map (result, ·)) =
        (do
          let table ← complete distribution (fun _ => none)
          (eager table).map (·, table))) :
    (do
      let table ← PMF.pi distribution
      eager table) = lazy.map Prod.fst := by
  have hfst := congrArg (PMF.map Prod.fst) h.symm
  simp only [PMF.monad_bind_eq_bind, complete_empty, PMF.map_bind, PMF.map_comp,
    Function.comp_def] at hfst
  change ((PMF.pi distribution).bind fun a => (eager a).map id) =
    lazy.bind fun a => (complete distribution a.2).map (Function.const _ a.1) at hfst
  simp only [PMF.map_id, PMF.map_const] at hfst
  exact hfst

/-- Lazy evaluation from an empty cache agrees with sampling the entire independent function
in advance, even for adaptive programs with repeated queries. -/
theorem interpret_eq_lazy [DecidableEq Query] (distribution : (q : Query) → PMF (Response q))
    (program : OracleComp Response α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret (fun q => PMF.pure (table q)) program) =
        ((OracleComp.interpret (answer distribution) program).run (fun _ => none)).map
          Prod.fst :=
  pi_bind_eq_map_fst_of_complete_eq distribution
    (run_interpret_answer_complete distribution program (fun _ => none))

/-- A uniformly sampled function can be replaced by a consistent lazy uniform oracle. -/
theorem uniform_interpret_eq_lazy [DecidableEq Query] [∀ q, Fintype (Response q)]
    [∀ q, Nonempty (Response q)] (program : OracleComp Response α) :
    (do
      let table ← PMF.uniformOfFintype ((q : Query) → Response q)
      OracleComp.interpret (fun q => PMF.pure (table q)) program) =
        ((OracleComp.interpret (answer (fun q => PMF.uniformOfFintype (Response q)))
          program).run (fun _ => none)).map Prod.fst := by
  simpa only [PMF.pi_uniformOfFintype] using
    interpret_eq_lazy (fun q => PMF.uniformOfFintype (Response q)) program

end Finite

section ListFinite

variable {Value : Type u} [Fintype Query] [Finite Value]
  [BEq Query] [LawfulBEq Query]

/-- Completing a singleton list cache `[(q₀, v₀)]` fixes coordinate `q₀` to `v₀`. -/
theorem complete_ofList_singleton [DecidableEq Query] (distribution : Query → PMF Value)
    (q₀ : Query) (v₀ : Value) :
    complete distribution (ofList [(q₀, v₀)]) =
      PMF.pi (Function.update distribution q₀ (PMF.pure v₀)) := by
  rw [ofList_cons, ofList_nil, complete_update]
  rfl

/-- An ordinary list-based cache implements eager independent function sampling. -/
theorem interpret_eq_memoize (distribution : Query → PMF Value)
    (program : OracleComp (fun _ : Query => Value) α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret (fun q => PMF.pure (table q)) program) =
        ((OracleComp.interpret (memoize distribution) program).run []).map Prod.fst := by
  classical
  rw [interpret_eq_lazy]
  have h := congrArg (PMF.map Prod.fst) (run_interpret_memoize distribution program [])
  simpa only [PMF.map_comp, Function.comp_def, ofList_nil] using h.symm

/-- Implement a finite random function using arbitrary injective key representations and mapped
values. The client sees the represented values; it need not know the finite sampling type. -/
theorem interpret_eq_memoize_map {Key' Value' : Type u} [BEq Key'] [LawfulBEq Key']
    (keyMap : Query ↪ Key') (valueMap : Value → Value')
    (distribution : Query → PMF Value) (sample' : Key' → PMF Value')
    (hsample : ∀ key, sample' (keyMap key) = (distribution key).map valueMap)
    (program : OracleComp (fun _ : Query => Value') α) :
    (do
      let table ← PMF.pi distribution
      OracleComp.interpret (fun key => PMF.pure (valueMap (table key))) program) =
      ((OracleComp.interpret (fun key => memoize sample' (keyMap key)) program).run []).map
        Prod.fst := by
  let represent := fun cache : List (Query × Value) =>
    cache.map (fun entry => (keyMap entry.1, valueMap entry.2))
  have hrun := OracleComp.run_interpret_map_response_state (fun _ => valueMap)
    (memoize distribution) (fun key => memoize sample' (keyMap key)) represent
    (fun key cache => by
      simpa only [represent, PMF.monad_map_eq_map] using
        memoize_map keyMap valueMap distribution sample' hsample key cache) program []
  have houtput := congrArg (PMF.map Prod.fst) hrun
  simp only [PMF.map_comp, Function.comp_def, represent, List.map_nil] at houtput
  rw [← houtput]
  simpa only [OracleComp.interpret_interpret, OracleComp.interpret_map, OracleComp.interpret_query,
    PMF.monad_map_eq_map, PMF.pure_map] using interpret_eq_memoize distribution
      (OracleComp.interpret (fun key => valueMap <$> OracleComp.query key) program)

end ListFinite

section Closed

variable {Key Value Result : Type} [BEq Key] [LawfulBEq Key]

/-- Evaluate memoized closed samplers while retaining the represented final cache. -/
theorem eval_run_interpret_memoize [DecidableEq Key] (sample : Key → ProbComp Value)
    (program : OracleComp (fun _ : Key => Value) Result) (cache : List (Key × Value)) :
    (ProbComp.eval ((OracleComp.interpret (memoize sample) program).run cache)).map
        (fun (result, cache') => (result, ofList cache')) =
      (OracleComp.interpret (answer (fun q => ProbComp.eval (sample q))) program).run
        (ofList cache) := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  simpa only [ProbComp.isMonadHom_eval.map_memoize] using
    run_interpret_memoize (fun q => ProbComp.eval (sample q)) program cache

/-- Memoized closed samplers implement the eager independent random-function experiment. -/
theorem eval_run_interpret_memoize_eq_eager [Fintype Key] [Finite Value]
    (sample : Key → ProbComp Value) (program : OracleComp (fun _ : Key => Value) Result) :
    ProbComp.eval (Prod.fst <$> (OracleComp.interpret (memoize sample) program).run []) =
      (do
        let table ← PMF.pi (fun q => ProbComp.eval (sample q))
        OracleComp.interpret (fun q => PMF.pure (table q)) program) := by
  classical
  rw [interpret_eq_lazy]
  have h := congrArg (PMF.map Prod.fst) (eval_run_interpret_memoize sample program [])
  simpa only [ProbComp.eval_map, PMF.map_comp, Function.comp_def, ofList_nil] using h

/-- Lift a stateful computation on a component cache `C` into a composite state `S`. -/
def zoomStateT {S C α : Type} {m : Type → Type} [Monad m]
    (get : S → C) (set : S → C → S) (act : StateT C m α) : StateT S m α := fun s => do
  let (a, c') ← act (get s)
  return (a, set s c')

omit [LawfulBEq Key] in
/-- Evaluating `zoomStateT get set (memoize (fun _ => dist) q)` commutes with `ProbComp.eval`. -/
theorem eval_zoomStateT_memoize {S : Type}
    (get : S → List (Key × Value)) (set : S → List (Key × Value) → S)
    (dist : ProbComp Value) (q : Key) (s : S) :
    ProbComp.eval (zoomStateT get set (memoize (fun _ => dist) q) s) =
      (memoize (fun _ => ProbComp.eval dist) q (get s)).map
        (fun (v, c') => (v, set s c')) := by
  simp [zoomStateT, ProbComp.eval_memoize, PMF.map]

end Closed

end Cslib.RandomOracle
