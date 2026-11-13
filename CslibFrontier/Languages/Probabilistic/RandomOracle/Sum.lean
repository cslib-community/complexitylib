/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Semantics
public import CslibFrontier.Languages.Probabilistic.Sum
import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Random-oracle caches on a sum of interfaces

Several independent lazy random oracles are one lazy random oracle on the sum of their interfaces,
answered by `OracleComp.sumHandler`. `RandomOracle.Cache.sum` joins one cache per side into a cache
of the joined interface, and a lazy call on one side of a joined cache is a lazy call on that side's
cache (`answer_sum_inl`, `answer_sum_inr`). A game that keeps one cache per oracle can therefore be
read as one represented lazy oracle.

A protocol in the random-oracle model often queries two independent oracles, such as a Merkle
hash and a Fiat–Shamir challenge oracle. `RandomOracle.memoizeSum` answers the calls of
`spec₁ ⊕ₒ spec₂` by memoizing each side in its own association list, so that a soundness proof
can reason about the two lists separately. It implements the lazy random oracle
`answer (sumHandler dist₁ dist₂)` on the joined cache of the two lists
(`run_interpret_memoizeSum`). A program over one side touches only that side's list
(`run_interpret_memoizeSum_liftLeft`), and properties of each list preserved by single memoized
calls hold after every run (`mem_support_run_interpret_memoizeSum`).

## Main definitions

* `Cslib.RandomOracle.Cache.sum`: the cache of `spec₁ ⊕ₒ spec₂` built from one cache for each side.
* `Cslib.RandomOracle.memoizeSum`: memoize the two sides of a sum interface in two lists.

## Main results

* `Cslib.RandomOracle.answer_sum_inl`, `Cslib.RandomOracle.answer_sum_inr`: a lazy call on one side
  of a joined cache is a lazy call on that side's cache.
* `Cslib.RandomOracle.Cache.update_sum_inl`, `Cslib.RandomOracle.Cache.update_sum_inr`: recording
  an answer in a joined cache records it on its side.
* `Cslib.RandomOracle.mem_support_memoizeSum_inl`, `Cslib.RandomOracle.mem_support_memoizeSum_inr`:
  a memoized call on one side updates only that side's list.
* `Cslib.RandomOracle.run_interpret_memoizeSum`: the two lists implement the lazy random oracle.
* `Cslib.RandomOracle.run_interpret_memoizeSum_liftLeft`,
  `Cslib.RandomOracle.run_interpret_memoizeSum_liftRight`: a program over one side uses only its
  own list.
* `Cslib.RandomOracle.mem_support_run_interpret_memoizeSum`: per-list invariants of supported runs.
-/

public section

namespace Cslib.RandomOracle

open scoped Cslib

section Cache

universe u

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, u} ι₁} {spec₂ : OracleSpec.{u, u} ι₂}

/-- The cache of the joined interface `spec₁ ⊕ₒ spec₂`: left queries read `c₁`, right queries read
`c₂`. -/
@[expose] def Cache.sum (c₁ : Cache spec₁) (c₂ : Cache spec₂) : Cache (spec₁ ⊕ₒ spec₂)
  | .inl q => c₁ q
  | .inr q => c₂ q

@[simp] theorem Cache.sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    Cache.sum c₁ c₂ (.inl q) = c₁ q := rfl

@[simp] theorem Cache.sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    Cache.sum c₁ c₂ (.inr q) = c₂ q := rfl

/-- The responses of a joined interface are finite when both sides' responses are. -/
instance [∀ q, Finite (spec₁ q)] [∀ q, Finite (spec₂ q)] : ∀ q, Finite ((spec₁ ⊕ₒ spec₂) q)
  | .inl q => inferInstanceAs (Finite (spec₁ q))
  | .inr q => inferInstanceAs (Finite (spec₂ q))

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- Recording a left answer in a joined cache records it in the left cache. -/
theorem Cache.update_sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) (v : spec₁ q) :
    Function.update (Cache.sum c₁ c₂) (.inl q) (some v) =
      Cache.sum (Function.update c₁ q (some v)) c₂ := by
  funext q'
  rcases q' with q' | q'
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inl_injective.ne h)]
  · simp

/-- Recording a right answer in a joined cache records it in the right cache. -/
theorem Cache.update_sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) (v : spec₂ q) :
    Function.update (Cache.sum c₁ c₂) (.inr q) (some v) =
      Cache.sum c₁ (Function.update c₂ q (some v)) := by
  funext q'
  rcases q' with q' | q'
  · simp
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inr_injective.ne h)]

/-- A lazy call on the left side of a joined cache is a lazy call on the left cache. -/
theorem answer_sum_inl (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    answer (OracleComp.sumHandler d₁ d₂) (.inl q) (Cache.sum c₁ c₂) =
      (answer d₁ q c₁).map fun z => (z.1, Cache.sum z.2 c₂) := by
  cases h : c₁ q with
  | none =>
    rw [answer_of_none d₁ c₁ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₁ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inl c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₁ c₁ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) v h, PMF.pure_map]

/-- A lazy call on the right side of a joined cache is a lazy call on the right cache. -/
theorem answer_sum_inr (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    answer (OracleComp.sumHandler d₁ d₂) (.inr q) (Cache.sum c₁ c₂) =
      (answer d₂ q c₂).map fun z => (z.1, Cache.sum c₁ z.2) := by
  cases h : c₂ q with
  | none =>
    rw [answer_of_none d₂ c₂ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₂ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inr c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₂ c₂ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) v h, PMF.pure_map]

end Cache

/-! ### Two lazy random oracles memoized in two lists -/

section MemoizeSum

open OracleComp Probability

variable {ι₁ ι₂ R₁ R₂ : Type} [BEq ι₁] [BEq ι₂]

/-- Answer the calls of `(fun _ => R₁) ⊕ₒ (fun _ => R₂)` by memoizing the left calls in the first
list, sampling from `dist₁`, and the right calls in the second, sampling from `dist₂`. -/
noncomputable def memoizeSum (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) :
    (q : ι₁ ⊕ ι₂) → StateT (List (ι₁ × R₁) × List (ι₂ × R₂)) PMF
      (((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) q) :=
  sumHandler (fun q => zoomStateT Prod.fst (fun st tr₁ => (tr₁, st.2)) (memoize dist₁ q))
    (fun q => zoomStateT Prod.snd (fun st tr₂ => (st.1, tr₂)) (memoize dist₂ q))

/-- A left call memoizes on the first list and leaves the second unchanged. -/
theorem memoizeSum_inl (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) (q : ι₁)
    (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) :
    memoizeSum dist₁ dist₂ (.inl q) (tr₁, tr₂) =
      (memoize dist₁ q tr₁).map fun (ans, tr₁') => (ans, (tr₁', tr₂)) := by
  rfl

/-- A right call memoizes on the second list and leaves the first unchanged. -/
theorem memoizeSum_inr (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) (q : ι₂)
    (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) :
    memoizeSum dist₁ dist₂ (.inr q) (tr₁, tr₂) =
      (memoize dist₂ q tr₂).map fun (ans, tr₂') => (ans, (tr₁, tr₂')) := by
  rfl

/-- The supported outcomes of a left call are those of `memoize dist₁` on the first list, with the
second list unchanged. -/
theorem mem_support_memoizeSum_inl {dist₁ : ι₁ → PMF R₁} {dist₂ : ι₂ → PMF R₂} {q : ι₁}
    {tr₁ : List (ι₁ × R₁)} {tr₂ : List (ι₂ × R₂)} {ans : R₁}
    {st' : List (ι₁ × R₁) × List (ι₂ × R₂)} :
    (ans, st') ∈ (memoizeSum dist₁ dist₂ (.inl q) (tr₁, tr₂)).support ↔
      ∃ tr₁', (ans, tr₁') ∈ (memoize dist₁ q tr₁).support ∧ st' = (tr₁', tr₂) := by
  rw [memoizeSum_inl, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨⟨ans', tr₁'⟩, hmem, heq⟩
    cases heq
    exact ⟨tr₁', hmem, rfl⟩
  · rintro ⟨tr₁', hmem, rfl⟩
    exact ⟨(ans, tr₁'), hmem, rfl⟩

/-- The supported outcomes of a right call are those of `memoize dist₂` on the second list, with
the first list unchanged. -/
theorem mem_support_memoizeSum_inr {dist₁ : ι₁ → PMF R₁} {dist₂ : ι₂ → PMF R₂} {q : ι₂}
    {tr₁ : List (ι₁ × R₁)} {tr₂ : List (ι₂ × R₂)} {ans : R₂}
    {st' : List (ι₁ × R₁) × List (ι₂ × R₂)} :
    (ans, st') ∈ (memoizeSum dist₁ dist₂ (.inr q) (tr₁, tr₂)).support ↔
      ∃ tr₂', (ans, tr₂') ∈ (memoize dist₂ q tr₂).support ∧ st' = (tr₁, tr₂') := by
  rw [memoizeSum_inr, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨⟨ans', tr₂'⟩, hmem, heq⟩
    cases heq
    exact ⟨tr₂', hmem, rfl⟩
  · rintro ⟨tr₂', hmem, rfl⟩
    exact ⟨(ans, tr₂'), hmem, rfl⟩

/-- Running a left program under `memoizeSum` runs it under `memoize dist₁` on the first list and
leaves the second list unchanged. -/
theorem run_interpret_memoizeSum_liftLeft (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) {β : Type}
    (prog : OracleComp (fun _ : ι₁ => R₁) β) (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) :
    (interpret (memoizeSum dist₁ dist₂) (liftLeft (spec₂ := fun _ : ι₂ => R₂) prog)).run
        (tr₁, tr₂) =
      ((interpret (memoize dist₁) prog).run tr₁).map fun (res, tr₁') => (res, (tr₁', tr₂)) := by
  induction prog using OracleComp.induction generalizing tr₁ with
  | pure a => simp [PMF.monad_pure_eq_pure]
  | query_bind q cont ih =>
    simp only [liftLeft_bind, liftLeft_query, run_interpret_bind, run_interpret_query,
      memoizeSum_inl, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    exact congrArg (PMF.bind _) (funext fun ⟨ans, tr₁'⟩ => ih ans tr₁')

/-- Running a right program under `memoizeSum` runs it under `memoize dist₂` on the second list
and leaves the first list unchanged. -/
theorem run_interpret_memoizeSum_liftRight (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) {β : Type}
    (prog : OracleComp (fun _ : ι₂ => R₂) β) (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) :
    (interpret (memoizeSum dist₁ dist₂) (liftRight (spec₁ := fun _ : ι₁ => R₁) prog)).run
        (tr₁, tr₂) =
      ((interpret (memoize dist₂) prog).run tr₂).map fun (res, tr₂') => (res, (tr₁, tr₂')) := by
  induction prog using OracleComp.induction generalizing tr₂ with
  | pure a => simp [PMF.monad_pure_eq_pure]
  | query_bind q cont ih =>
    simp only [liftRight_bind, liftRight_query, run_interpret_bind, run_interpret_query,
      memoizeSum_inr, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    exact congrArg (PMF.bind _) (funext fun ⟨ans, tr₂'⟩ => ih ans tr₂')

/-- If single memoized calls preserve a property `P₁` of the first list and a property `P₂` of the
second, then every supported run of `memoizeSum` preserves both. -/
theorem mem_support_run_interpret_memoizeSum (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂)
    (P₁ : List (ι₁ × R₁) → Prop) (P₂ : List (ι₂ × R₂) → Prop)
    (h₁ : ∀ q tr tr' ans, P₁ tr → (ans, tr') ∈ (memoize dist₁ q tr).support → P₁ tr')
    (h₂ : ∀ q tr tr' ans, P₂ tr → (ans, tr') ∈ (memoize dist₂ q tr).support → P₂ tr')
    {β : Type} (prog : OracleComp ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) β)
    {st st' : List (ι₁ × R₁) × List (ι₂ × R₂)} {res : β} (hst : P₁ st.1 ∧ P₂ st.2)
    (hmem : (res, st') ∈ ((interpret (memoizeSum dist₁ dist₂) prog).run st).support) :
    P₁ st'.1 ∧ P₂ st'.2 := by
  refine run_interpret_invariant _ (fun st => P₁ st.1 ∧ P₂ st.2) ?_ prog st hst res st' hmem
  rintro (q | q) ⟨tr₁, tr₂⟩ ⟨hP₁, hP₂⟩ ans st'' hstep
  · obtain ⟨tr₁', hmemo, rfl⟩ := mem_support_memoizeSum_inl.mp hstep
    exact ⟨h₁ q tr₁ _ _ hP₁ hmemo, hP₂⟩
  · obtain ⟨tr₂', hmemo, rfl⟩ := mem_support_memoizeSum_inr.mp hstep
    exact ⟨hP₁, h₂ q tr₂ _ _ hP₂ hmemo⟩

variable [LawfulBEq ι₁] [LawfulBEq ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- `memoizeSum dist₁ dist₂` implements the lazy random oracle `answer (sumHandler dist₁ dist₂)`
on the joined cache of its two lists, preserving the result and represented final cache of every
adaptive program. -/
theorem run_interpret_memoizeSum (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) {β : Type}
    (prog : OracleComp ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) β)
    (st : List (ι₁ × R₁) × List (ι₂ × R₂)) :
    ((interpret (memoizeSum dist₁ dist₂) prog).run st).map
        (fun (res, st') => (res, Cache.sum (ofList st'.1) (ofList st'.2))) =
      runWith (answer (sumHandler (spec₁ := fun _ : ι₁ => R₁) (spec₂ := fun _ : ι₂ => R₂)
        dist₁ dist₂)) prog (Cache.sum (ofList st.1) (ofList st.2)) := by
  refine run_interpret_map_state _ _ (fun st => Cache.sum (ofList st.1) (ofList st.2)) ?_ prog st
  rintro (q | q) ⟨tr₁, tr₂⟩
  · rw [memoizeSum_inl, PMF.map_comp, answer_sum_inl, ← memoize_map_ofList, PMF.map_comp]
    rfl
  · rw [memoizeSum_inr, PMF.map_comp, answer_sum_inr, ← memoize_map_ofList, PMF.map_comp]
    rfl

/-- From two empty lists, `memoizeSum dist₁ dist₂` has the output distribution of the lazy random
oracle `answer (sumHandler dist₁ dist₂)` started from the empty cache. -/
theorem map_fst_run_interpret_memoizeSum_nil (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂)
    {β : Type} (prog : OracleComp ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) β) :
    ((interpret (memoizeSum dist₁ dist₂) prog).run ([], [])).map Prod.fst =
      (runWith (answer (sumHandler (spec₁ := fun _ : ι₁ => R₁) (spec₂ := fun _ : ι₂ => R₂)
        dist₁ dist₂)) prog (fun _ => none)).map Prod.fst := by
  have hnil : Cache.sum (ofList ([] : List (ι₁ × R₁))) (ofList ([] : List (ι₂ × R₂))) =
      fun _ => none := by
    funext q
    cases q <;> rfl
  have h := congrArg (PMF.map Prod.fst) (run_interpret_memoizeSum dist₁ dist₂ prog ([], []))
  simpa only [PMF.map_comp, Function.comp_def, hnil] using h

end MemoizeSum

end Cslib.RandomOracle
