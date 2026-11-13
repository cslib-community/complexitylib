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
# Two independent lazy random oracles

A protocol in the random-oracle model often queries two independent oracles, such as a Merkle
hash and a Fiat–Shamir challenge oracle. `RandomOracle.memoizeSum` answers the calls of
`spec₁ ⊕ₒ spec₂` by memoizing each side in its own association list, so that a soundness proof
can reason about the two traces separately.

`run_interpret_memoizeSum` shows that this implements the lazy random oracle
`RandomOracle.answer (sumHandler dist₁ dist₂)` on the cache represented by the two lists
(`RandomOracle.ofSumTrace`). A program over one side touches only that side's list
(`run_interpret_memoizeSum_liftLeft`), and properties of each list preserved by single memoized
calls hold after every run (`mem_support_run_interpret_memoizeSum`).

## Main definitions

* `Cslib.RandomOracle.memoizeSum`: memoize the two sides of a sum interface in two lists.
* `Cslib.RandomOracle.ofSumTrace`: the cache represented by the two lists.

## Main results

* `Cslib.RandomOracle.run_interpret_memoizeSum`: the two lists implement the lazy random oracle.
* `Cslib.RandomOracle.run_interpret_memoizeSum_liftLeft`,
  `Cslib.RandomOracle.run_interpret_memoizeSum_liftRight`: a program over one side uses only its
  own list.
* `Cslib.RandomOracle.mem_support_run_interpret_memoizeSum`: per-list invariants of supported runs.
-/

@[expose] public section

namespace Cslib.RandomOracle

open OracleComp Probability

variable {ι₁ ι₂ R₁ R₂ : Type} [BEq ι₁] [BEq ι₂]

/-- Answer the calls of `(fun _ => R₁) ⊕ₒ (fun _ => R₂)` by memoizing the left calls in the first
list, sampling from `dist₁`, and the right calls in the second, sampling from `dist₂`. -/
noncomputable def memoizeSum (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) :
    (q : ι₁ ⊕ ι₂) → StateT (List (ι₁ × R₁) × List (ι₂ × R₂)) PMF
      (((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) q)
  | .inl q => fun (tr₁, tr₂) =>
    (memoize dist₁ q tr₁).map fun (ans, tr₁') => (ans, (tr₁', tr₂))
  | .inr q => fun (tr₁, tr₂) =>
    (memoize dist₂ q tr₂).map fun (ans, tr₂') => (ans, (tr₁, tr₂'))

/-- The cache represented by a pair of association lists: the first occurrence of a key in the
list for its side determines its value. -/
def ofSumTrace (st : List (ι₁ × R₁) × List (ι₂ × R₂)) :
    Cache ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂))
  | .inl q => ofList st.1 q
  | .inr q => ofList st.2 q

/-- Two empty lists represent the empty cache. -/
@[simp] theorem ofSumTrace_nil :
    ofSumTrace (([], []) : List (ι₁ × R₁) × List (ι₂ × R₂)) = fun _ => none := by
  funext q
  cases q <;> rfl

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
      memoizeSum, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
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
      memoizeSum, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
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
  rintro (q | q) ⟨tr₁, tr₂⟩ ⟨hP₁, hP₂⟩ ans ⟨tr₁', tr₂'⟩ hstep
  · obtain ⟨⟨ans', tr₁''⟩, hmemo, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨h₁ q tr₁ _ _ hP₁ hmemo, hP₂⟩
  · obtain ⟨⟨ans', tr₂''⟩, hmemo, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hP₁, h₂ q tr₂ _ _ hP₂ hmemo⟩

variable [LawfulBEq ι₁] [LawfulBEq ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

omit [LawfulBEq ι₂] in
/-- Recording a left answer updates exactly its key in the represented cache. -/
theorem ofSumTrace_cons_left (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) (q : ι₁) (ans : R₁) :
    ofSumTrace ((q, ans) :: tr₁, tr₂) =
      Function.update (ofSumTrace (tr₁, tr₂)) (.inl q) (some ans) := by
  funext q'
  cases q' with
  | inl q' => simpa [ofSumTrace] using congrFun (ofList_cons tr₁ q ans) q'
  | inr q' => simp [ofSumTrace]

omit [LawfulBEq ι₁] in
/-- Recording a right answer updates exactly its key in the represented cache. -/
theorem ofSumTrace_cons_right (tr₁ : List (ι₁ × R₁)) (tr₂ : List (ι₂ × R₂)) (q : ι₂) (ans : R₂) :
    ofSumTrace (tr₁, (q, ans) :: tr₂) =
      Function.update (ofSumTrace (tr₁, tr₂)) (.inr q) (some ans) := by
  funext q'
  cases q' with
  | inl q' => simp [ofSumTrace]
  | inr q' => simpa [ofSumTrace] using congrFun (ofList_cons tr₂ q ans) q'

/-- `memoizeSum dist₁ dist₂` implements the lazy random oracle
`answer (sumHandler dist₁ dist₂)`, preserving the result and represented final cache of every
adaptive program. -/
theorem run_interpret_memoizeSum (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂) {β : Type}
    (prog : OracleComp ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) β)
    (st : List (ι₁ × R₁) × List (ι₂ × R₂)) :
    ((interpret (memoizeSum dist₁ dist₂) prog).run st).map
        (fun (res, st') => (res, ofSumTrace st')) =
      runWith (answer (sumHandler (spec₁ := fun _ : ι₁ => R₁) (spec₂ := fun _ : ι₂ => R₂)
        dist₁ dist₂)) prog (ofSumTrace st) := by
  apply run_interpret_map_state
  rintro (q | q) ⟨tr₁, tr₂⟩
  · dsimp only [memoizeSum]
    cases h : tr₁.lookup q with
    | none =>
      rw [memoize_of_none _ _ _ h, answer_of_none _ (ofSumTrace (tr₁, tr₂)) (.inl q) h]
      change (((dist₁ q).map (fun v => (v, (q, v) :: tr₁))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, ofSumTrace_cons_left]
    | some val =>
      rw [memoize_of_some _ _ _ _ h, answer_of_some _ (ofSumTrace (tr₁, tr₂)) (.inl q) val h]
      simp [PMF.monad_pure_eq_pure]
  · dsimp only [memoizeSum]
    cases h : tr₂.lookup q with
    | none =>
      rw [memoize_of_none _ _ _ h, answer_of_none _ (ofSumTrace (tr₁, tr₂)) (.inr q) h]
      change (((dist₂ q).map (fun v => (v, (q, v) :: tr₂))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, ofSumTrace_cons_right]
    | some val =>
      rw [memoize_of_some _ _ _ _ h, answer_of_some _ (ofSumTrace (tr₁, tr₂)) (.inr q) val h]
      simp [PMF.monad_pure_eq_pure]

/-- From two empty lists, `memoizeSum dist₁ dist₂` has the output distribution of the lazy random
oracle `answer (sumHandler dist₁ dist₂)` started from the empty cache. -/
theorem map_fst_run_interpret_memoizeSum_nil (dist₁ : ι₁ → PMF R₁) (dist₂ : ι₂ → PMF R₂)
    {β : Type} (prog : OracleComp ((fun _ : ι₁ => R₁) ⊕ₒ (fun _ : ι₂ => R₂)) β) :
    ((interpret (memoizeSum dist₁ dist₂) prog).run ([], [])).map Prod.fst =
      (runWith (answer (sumHandler (spec₁ := fun _ : ι₁ => R₁) (spec₂ := fun _ : ι₂ => R₂)
        dist₁ dist₂)) prog (fun _ => none)).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (run_interpret_memoizeSum dist₁ dist₂ prog ([], []))
  simpa only [PMF.map_comp, Function.comp_def, ofSumTrace_nil] using h

end Cslib.RandomOracle
