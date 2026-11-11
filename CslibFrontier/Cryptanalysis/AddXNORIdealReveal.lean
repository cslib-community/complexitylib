/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealReplay
public import CslibFrontier.Cryptanalysis.AddXNORIdealCollisions
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Actual auxiliary walks for the hidden-cut bridge

Forward and inverse walks use the same concrete replay handler as the adversary. Requests
are charged individually. The recorded-entry invariant and collision-free witness persistence
recover paths that were already present before the hidden walks, rather than assuming covering.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.pathProgram`: actual directional oracle walk.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.cutHit_bridge`: every actual cut hit is
  charged to a reveal collision or a side covered by the old ledger.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.cutProgram_queryBound`: auxiliary calls
  are counted explicitly.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.verification_collision`: independent-target
  acceptance forces a fresh collision, including coincident public roots.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.source_independent_verification`: the
  averaged numerical bound for the actual independent verification game.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal.source_search_le_visibleBad`: numerical
  independent verification composed with the original planted-search comparison.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal

open Probability OracleComp RandomPermutation

/-- Flip a request's direction, retaining the selected independent permutation. -/
@[expose] def inverseRequest {Index Word : Type} (query : Index × PermQuery Word) :
    Index × PermQuery Word :=
  (query.1, match query.2 with
    | .forward point => .inverse point
    | .inverse point => .forward point)

/-- Reuse the original forward walker, interpreting its calls inversely for a backward walk. -/
@[expose] def pathProgram {Index Word : Type} (backward : Bool) (path : List Index) (seed : Word) :
    OracleComp (Family.Spec Index Word) Word :=
  if backward then interpret (fun query => OracleComp.query (inverseRequest query)) (walk path seed)
  else walk path seed

private theorem pathProgram_nil {Index Word : Type} (backward : Bool) (seed : Word) :
    pathProgram (Index := Index) backward [] seed = pure seed := by
  cases backward <;> simp [pathProgram, walk, interpret_pure]

private theorem pathProgram_cons {Index Word : Type} (backward : Bool) (label : Index)
    (path : List Index) (seed : Word) :
    pathProgram backward (label :: path) seed = (do
      let next ← OracleComp.query (label, if backward then .inverse seed else .forward seed)
      pathProgram backward path next) := by
  cases backward <;> simp [pathProgram, walk, interpret_bind, interpret_query, inverseRequest]

/-- Reverse the same ledger when interpreting inverse requests. -/
@[expose] def directionRecords {Index Word : Type} (backward : Bool)
    (records : List (Forest.Record Index Word)) : List (Forest.Record Index Word) :=
  if backward then records.map Forest.Record.reverse else records

variable {Index Word : Type} [DecidableEq Index] [DecidableEq Word]

omit [DecidableEq Word] in
private theorem recorded_edge (backward : Bool) (records : List (Forest.Record Index Word))
    (label : Index) (point value : Word)
    (h : Ledger.Recorded records
      (label, if backward then .inverse point else .forward point) value) :
    Forest.Follows (directionRecords backward records) point [label] value := by
  obtain ⟨r, hr, hl, he⟩ := Ledger.recorded_entry _ _ _ h
  cases backward with
  | false =>
    have hs : r.source = point := congrArg Prod.fst he
    have ht : r.target = value := congrArg Prod.snd he
    simpa only [directionRecords, Bool.false_eq_true, ↓reduceIte, hs, ht, hl] using
      (Forest.Follows.cons r hr (Forest.Follows.nil r.target))
  | true =>
    have hm : r.reverse ∈ directionRecords true records := by
      simp only [directionRecords, ↓reduceIte, List.mem_map]
      exact ⟨r, hr, rfl⟩
    have he' := congrArg Prod.swap he
    rw [← Forest.Record.reverse_entry] at he'
    have hs : r.reverse.source = point := congrArg Prod.fst he'
    have ht : r.reverse.target = value := congrArg Prod.snd he'
    have hl' : r.reverse.label = label := hl
    simpa only [hs, ht, hl'] using
      (Forest.Follows.cons r.reverse hm (Forest.Follows.nil r.reverse.target))

/-- The actual walk has a path in the final fresh ledger. The transcript-to-ledger fact is
supplied by `Replay.run_recorded` for the whole executed program, including these walks. -/
theorem path_follows (backward : Bool) (path : List Index) (seed : Word)
    (initial : Replay.State Index Word) (endpoint : Word) (state : Replay.State Index Word)
    (hout : (endpoint, state) ∈ (ProbOracleComp.runWith Replay.answer
      (liftRight (spec₁ := unifSpec) (pathProgram backward path seed)) initial).support)
    (hr : ∀ entry ∈ state.trace, Ledger.Recorded state.records entry.1 entry.2) :
    Forest.Follows (directionRecords backward state.records) seed path endpoint := by
  induction path generalizing seed initial with
  | nil =>
    rw [pathProgram_nil, liftRight_pure, ProbOracleComp.runWith_pure,
      PMF.mem_support_pure_iff] at hout
    cases hout
    exact .nil _
  | cons label rest ih =>
    rw [pathProgram_cons, liftRight_bind, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_liftRight, OracleComp.runWith_query,
      PMF.mem_support_bind_iff] at hout
    obtain ⟨⟨reply, next⟩, hstep, htail⟩ := hout
    have hs := Replay.run_trace_suffix _ next endpoint state htail
    have hhead : ⟨(label, if backward then .inverse seed else .forward seed), reply⟩ ∈
        state.trace := by
      simp only [Replay.answer, PMF.mem_support_pure_iff] at hstep
      cases hstep
      exact hs.subset (List.mem_cons_self ..)
    have hedge := recorded_edge backward state.records label seed reply (hr _ hhead)
    simpa only [List.singleton_append] using hedge.append (ih reply next htail)

omit [DecidableEq Index] [DecidableEq Word] in
/-- Directional auxiliary walks make exactly one external call per path label. -/
theorem path_queryBound (backward : Bool) (path : List Index) (seed : Word) :
    ProbOracleComp.IsQueryBounded
      (liftRight (spec₁ := unifSpec) (pathProgram backward path seed)) path.length := by
  have hraw := (walk_correct (fun _ : Index => Equiv.refl Word) path seed).1
  cases backward with
  | false =>
    simpa only [pathProgram, Bool.false_eq_true, ↓reduceIte, liftRight,
      ProbOracleComp.query] using hraw.probOracleComp
  | true =>
    have hi : IsQueryBounded (interpret (fun query =>
        OracleComp.query (inverseRequest query)) (walk path seed)) path.length :=
      IsCostBounded.interpret (spec := Family.Spec Index Word)
        (target := Family.Spec Index Word) (cost := fun _ => 1) (cost' := fun _ => 1)
        (fun query => IsCostBounded.query (inverseRequest query)) hraw
    simpa only [pathProgram, ↓reduceIte, liftRight, ProbOracleComp.query] using hi.probOracleComp

/-- Supported auxiliary execution returns the actual forward or inverse-permutation path value. -/
theorem path_endpoint (backward : Bool) (path : List Index) (seed : Word)
    (initial : Replay.State Index Word) (endpoint : Word) (state : Replay.State Index Word)
    (hout : (endpoint, state) ∈ (ProbOracleComp.runWith Replay.answer
      (liftRight (spec₁ := unifSpec) (pathProgram backward path seed)) initial).support) :
    endpoint = pathEquiv (fun label =>
      if backward then (initial.perms label).symm else initial.perms label) path seed := by
  induction path generalizing seed initial with
  | nil =>
    rw [pathProgram_nil, liftRight_pure, ProbOracleComp.runWith_pure,
      PMF.mem_support_pure_iff] at hout
    cases hout
    rfl
  | cons label rest ih =>
    rw [pathProgram_cons, liftRight_bind, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_liftRight, OracleComp.runWith_query,
      PMF.mem_support_bind_iff] at hout
    obtain ⟨⟨reply, next⟩, hstep, htail⟩ := hout
    simp only [Replay.answer, PMF.mem_support_pure_iff] at hstep
    cases hstep
    have he := ih _ _ htail
    cases backward <;> simpa only [Bool.false_eq_true, ↓reduceIte, Family.eval,
      evalPerm_forward, evalPerm_inverse, pathEquiv, Equiv.trans_apply] using he

/-- Reveal the two hidden sides in the original family. These internal observations are not
adversary-visible calls, but all their fresh draws must enter the collision budget. -/
@[expose] def cutProgram (cut : Cut Index) (seed target : Word) :
    ProbOracleComp (Family.Spec Index Word) (Word × Word) := do
  let forward ← liftRight (pathProgram false (cut.left ++ [cut.edge]) seed)
  let backward ← liftRight (pathProgram true cut.right.reverse target)
  return (forward, backward)

omit [DecidableEq Index] [DecidableEq Word] in
/-- The auxiliary reveal charges the prefix including the cut edge and the entire suffix. -/
theorem cutProgram_queryBound (cut : Cut Index) (seed target : Word) :
    ProbOracleComp.IsQueryBounded (cutProgram cut seed target)
      (cut.left.length + 1 + cut.right.length) := by
  have hf := path_queryBound false (cut.left ++ [cut.edge]) seed
  have hb := path_queryBound true cut.right.reverse target
  simpa only [cutProgram, List.length_append, List.length_singleton, List.length_reverse,
    Nat.add_zero] using hf.bind fun forward => hb.bind fun backward =>
      IsCostBounded.pure (forward, backward) 0

open scoped Classical in
/-- The original visible cut-hit game has exactly the full replay law. Only the private state
representation changes; the adversary and every one of its visible calls are preserved. -/
theorem cutHitGame_replay (cut : Cut Index)
    (perms : Index → Equiv.Perm Word) (seed target : Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    Visible.cutHitGame cut perms seed target program =
      (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).map
        (fun (_, state) => decide (∃ entry ∈ state.trace,
          cut.affected perms seed target entry.1)) := by
  rw [Visible.cutHitGame, ← Replay.erase_records program ⟨[], [], perms⟩, PMF.map_comp]
  rfl

/-- An actual visible cut hit exposes either the original cut output or the inverse-suffix
endpoint among the old seen words. Cache hits are covered by the derived recorded-entry law;
no hidden-path covering conclusion is assumed. -/
theorem cutHit_seen [Finite Index] [Finite Word] [Nonempty Word] (cut : Cut Index)
    (perms : Index → Equiv.Perm Word) (seed target : Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (out : Output) (state : Replay.State Index Word)
    (hout : (out, state) ∈ (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).support)
    (hhit : ∃ entry ∈ state.trace, cut.affected perms seed target entry.1) :
    perms cut.edge (cut.input perms seed) ∈ Forest.seen {seed, target} state.records ∨
      (cut.suffix perms).symm target ∈ Forest.seen {seed, target} state.records := by
  obtain ⟨⟨⟨label, query⟩, reply⟩, hm, hh⟩ := hhit
  have hs := Ledger.recorded_seen {seed, target} state.records (label, query) reply
    (Replay.run_recorded perms program out state hout _ hm)
  have he := (Replay.run_trace_eval perms program out state hout).2 _ hm
  obtain ⟨hl, hh⟩ := hh
  change label = cut.edge at hl
  subst label
  cases query with
  | forward point =>
    change reply = perms cut.edge point at he
    rcases hh with hi | ht
    · exact Or.inl (by simpa only [he, hi] using hs.2)
    · exact Or.inr (by simpa only [he, ht] using hs.2)
  | inverse point =>
    rcases hh with hi | ht
    · exact Or.inl (by simpa only [PermQuery.argument, hi] using hs.1)
    · exact Or.inr (by simpa only [PermQuery.argument, ht] using hs.1)

/-- Actual cut hits are charged to a collision during the executed auxiliary reveal, or a
hidden side already covered by the adversary's original fresh ledger. The reveal has the
explicit query budget `cutProgram_queryBound`; its draws are not counted for free. -/
theorem cutHit_bridge [Finite Index] [Finite Word] [Nonempty Word] (cut : Cut Index)
    (perms : Index → Equiv.Perm Word) (seed target : Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (out : Output) (old : Replay.State Index Word)
    (hold : (out, old) ∈ (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).support)
    (result : Word × Word) (last : Replay.State Index Word)
    (hreveal : (result, last) ∈
      (ProbOracleComp.runWith Replay.answer (cutProgram cut seed target) old).support)
    (hhit : ∃ entry ∈ old.trace, cut.affected perms seed target entry.1) :
    ¬Forest.NoCollision {seed, target} last.records ∨
      (Forest.NoCollision {seed, target} old.records ∧
        ((∃ endpoint, Forest.Follows old.records seed (cut.left ++ [cut.edge]) endpoint) ∨
          ∃ endpoint, Forest.Follows (old.records.map Forest.Record.reverse) target
            cut.right.reverse endpoint)) := by
  classical
  by_cases hc : Forest.NoCollision {seed, target} last.records
  · right
    have hsub := Replay.run_records_suffix _ old result last hreveal
    obtain ⟨extra, he⟩ := hsub
    refine ⟨Forest.noCollision_append_right {seed, target} extra old.records
      (by simpa only [he] using hc), ?_⟩
    rw [cutProgram, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hreveal
    obtain ⟨⟨forward, middle⟩, hf, hb⟩ := hreveal
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hb
    obtain ⟨⟨backward, final⟩, hb, hpure⟩ := hb
    rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hpure
    cases hpure
    have hforward : (forward, middle) ∈ (ProbOracleComp.runWith Replay.answer
        (program >>= fun _ => liftRight (pathProgram false (cut.left ++ [cut.edge]) seed))
        ⟨[], [], perms⟩).support := by
      rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff]
      exact ⟨(out, old), hold, hf⟩
    have hlast : ((forward, backward), final) ∈ (ProbOracleComp.runWith Replay.answer
        (program >>= fun _ => cutProgram cut seed target) ⟨[], [], perms⟩).support := by
      rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff]
      refine ⟨(out, old), hold, ?_⟩
      rw [cutProgram, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff]
      refine ⟨(forward, middle), hf, ?_⟩
      rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff]
      exact ⟨(backward, final), hb, by simp⟩
    have hfm := Replay.run_recorded perms _ forward middle hforward
    have hbm := Replay.run_recorded perms _ (forward, backward) final hlast
    have hfp := path_follows false _ seed old forward middle hf hfm
    have hbp := path_follows true _ target middle backward final hb hbm
    simp only [directionRecords, Bool.false_eq_true, ↓reduceIte] at hfp hbp
    have hs₁ := Replay.run_records_suffix _ old forward middle hf
    have hs₂ := Replay.run_records_suffix _ middle backward final hb
    have hs := hs₁.trans hs₂
    have hπold := (Replay.run_trace_eval perms program out old hold).1
    have hπmiddle := (Replay.run_trace_eval perms _ forward middle hforward).1
    have hvf := path_endpoint false _ seed old forward middle hf
    have hvb := path_endpoint true _ target middle backward final hb
    simp only [Bool.false_eq_true, ↓reduceIte, hπold, pathEquiv_append, pathEquiv,
      Equiv.trans_apply, Equiv.refl_apply] at hvf
    simp only [↓reduceIte, hπmiddle, pathEquiv_reverse_symm] at hvb
    rcases cutHit_seen cut perms seed target program out old hold hhit with hseen | hseen
    · left
      refine ⟨forward, Forest.follows_of_suffix_of_seen {seed, target} seed
        (Finset.mem_insert_self ..) old.records final.records hs hc ?_ (hfp.mono hs₂.subset)⟩
      simpa only [hvf, Cut.input] using hseen
    · right
      refine ⟨backward, Forest.follows_of_suffix_of_seen {seed, target} target
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (old.records.map Forest.Record.reverse) (final.records.map Forest.Record.reverse)
        (hs.map Forest.Record.reverse) ((Forest.noCollision_reverse _ _).mpr hc) ?_ hbp⟩
      simpa only [Forest.seen_reverse, hvb, Cut.suffix] using hseen
  · exact Or.inl hc

omit [DecidableEq Index] in
/-- In the actual independent-target verification run, a nonempty accepted chain forces a
fresh collision. The final path is derived from execution, including the candidate-dependent
walk and all cache hits; no witness soundness or traversal conclusion is a premise. -/
theorem verification_collision {q : ℕ} [Finite Word] [Nonempty Word] (hq : 0 < q)
    (perms : Label q → Equiv.Perm Word) (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (state : Replay.State (Label q) Word)
    (hout : (true, state) ∈ (ProbOracleComp.runWith Replay.answer
      (verifiedAdversary adversary seed target) ⟨[], [], perms⟩).support) :
    ¬Forest.NoCollision {seed, target} state.records := by
  have hrecorded := Replay.run_recorded perms _ true state hout
  rw [verifiedAdversary, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨⟨candidate, middle⟩, _, hw⟩ := hout
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hw
  obtain ⟨⟨endpoint, last⟩, hwalk, hpure⟩ := hw
  rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hpure
  obtain ⟨he, hs⟩ := Prod.mk.inj hpure
  have ht : endpoint = target := of_decide_eq_true he.symm
  change state = last at hs
  subst last
  subst endpoint
  have hpath := path_follows false (List.ofFn fun i => (i, candidate i)) seed middle target
    state (by simpa only [pathProgram, Bool.false_eq_true, ↓reduceIte] using hwalk) hrecorded
  simp only [directionRecords, Bool.false_eq_true, ↓reduceIte] at hpath
  intro hc
  exact Forest.no_nonempty_initial_path {seed, target} seed (Finset.mem_insert_self ..)
    state.records hc (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (by intro he; have hlen := congrArg List.length he; simp only [List.length_ofFn,
          List.length_nil] at hlen; omega) hpath

omit [DecidableEq Index] in
/-- Independent verification success also forces a collision in the actual lazy sampler,
transporting the full supported run rather than assuming a simulation or witness contract. -/
theorem verification_collision_lazy {q : ℕ} [Fintype Word] [Nonempty Word] (hq : 0 < q)
    (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (records : List (Forest.Record (Label q) Word))
    (hout : (true, records) ∈ (ProbOracleComp.runWith Ledger.answer
      (verifiedAdversary adversary seed target) []).support) :
    ¬Forest.NoCollision {seed, target} records := by
  let program := verifiedAdversary adversary seed target
  have hp := ProbOracleComp.run_interpret_withTranscript Ledger.answer program [] []
  rw [← hp, PMF.mem_support_map_iff] at hout
  obtain ⟨⟨accepted, rows, trace⟩, htrace, he⟩ := hout
  cases he
  have hj : (true, (rows, trace)) ∈
      (((PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
        ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).map
          (fun (out, state) => (out, (state.records, state.trace)))).support := by
    rw [Replay.lazy_law]
    exact htrace
  rw [PMF.mem_support_map_iff] at hj
  obtain ⟨⟨accepted, rows, log, family⟩, hj, he⟩ := hj
  cases he
  rw [PMF.mem_support_bind_iff] at hj
  obtain ⟨perms, _, hrun⟩ := hj
  exact verification_collision hq perms seed target adversary _ hrun

omit [DecidableEq Index] in
/-- A fixed public seed/target independent-family verification probability is bounded by the
collision event of the actual `T+q` sampler program. -/
theorem verification_probability_le {q : ℕ} [Fintype Word] [Nonempty Word] (hq : 0 < q)
    (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    (((PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
      interpret (Family.probEval perms) (verifiedAdversary adversary seed target)) true) ≤
      (ProbOracleComp.runWith Ledger.answer
        (verifiedAdversary adversary seed target) []).toOuterMeasure
          {out | ¬Forest.NoCollision {seed, target} out.2} := by
  classical
  rw [Ledger.uniform_output]
  have h := PMF.map_true_mono
    (ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) [])
    (E := Prod.fst) (F := fun (_, records) => decide (¬Forest.NoCollision {seed, target} records))
    (fun (out, records) hout htrue => by
      change out = true at htrue
      subst out
      exact decide_eq_true (verification_collision_lazy hq seed target adversary records hout))
  simpa only [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using h

omit [DecidableEq Index] [DecidableEq Word] in
/-- Numerical independent-target verification bound under the source's visible-call and
word-width restrictions. The candidate-dependent `q`-call walk is explicitly charged. -/
theorem source_verification_le_eight {q : ℕ} (hq : 0 < q) (m T : ℕ)
    (seed target : Fin (2 ^ m))
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hqueries : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((((PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
      interpret (Family.probEval perms) (verifiedAdversary adversary seed target)) true)).toReal ≤
        8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hp := verification_probability_le hq seed target adversary
  have hr := ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _) hp
  exact hr.trans (Collisions.source_collision_le_eight m q T seed target hqT hT hlimit
    (verifiedAdversary adversary seed target)
    (verifiedAdversary_queryBound adversary T hqueries seed target))

omit [DecidableEq Index] [DecidableEq Word] in
/-- The actual independent-target decision game with search verification, averaging the public
seed and target, has the same explicit numerical bound. -/
theorem source_independent_verification {q : ℕ} (hq : 0 < q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hqueries : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((decision false (verifiedAdversary adversary)) true).toReal ≤
      8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hn : 0 ≤ 8 * (T : ℝ) ^ 2 / 2 ^ m := by positivity
  have hp : (decision false (verifiedAdversary adversary)) true ≤
      ENNReal.ofReal (8 * (T : ℝ) ^ 2 / 2 ^ m) := by
    simp only [decision, Bool.false_eq_true, ↓reduceIte, pmf_norm, PMF.bind_const]
    apply Probability.PMF.bind_apply_le_on_support
    intro seed _
    apply Probability.PMF.bind_apply_le_on_support
    intro target _
    exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) hn).mpr
      (source_verification_le_eight hq m T seed target adversary hqueries hqT hT hlimit)
  simpa only [ENNReal.toReal_ofReal hn] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hp

omit [DecidableEq Index] [DecidableEq Word] in
/-- The actual planted search comparison now has a proved numerical independent-verification
term. `AddXNORIdealSecurity` bounds its visible stopping term with a charged reveal;
no bound on that game is a premise of this theorem. -/
theorem source_search_le_visibleBad {q : ℕ} (hq : 0 < q) (k : Fin q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hqueries : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      ((visibleBadGame k (verifiedAdversary adversary)) true).toReal +
        8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hs := search_comparison k adversary
  have hr := NNReal.coe_le_coe.mpr hs
  rw [Crypto.Game.coe_advantage] at hr
  change |((plantedSearch adversary) true).toReal -
    ((decision false (verifiedAdversary adversary)) true).toReal| ≤
      ((visibleBadGame k (verifiedAdversary adversary)) true).toReal at hr
  have hi := source_independent_verification hq m T adversary hqueries hqT hT hlimit
  have hd := le_abs_self (((plantedSearch adversary) true).toReal -
    ((decision false (verifiedAdversary adversary)) true).toReal)
  linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Reveal
