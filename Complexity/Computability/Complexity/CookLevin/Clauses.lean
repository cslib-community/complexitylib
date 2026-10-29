/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Encoding

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Polynomial-time construction of tableau clauses

All clause families of the existing Cook–Levin tableau are polynomial-time functions of their
input word and unary time/window bounds. Variables use `encVar`, so the certificates compose with
`Cslib.Complexity.CookLevin.computableInPolyTime_relabel` to produce binary SAT instances.

The machine, its tape count and its finite state type are fixed. Traversals of tapes and
situations therefore use fixed lists; the tape-cell window is enumerated from the input bound.
The step certificate enumerates the original constructor templates, preserving their order and
multiplicity. These certificates assemble into the complete reduction in
`Complexity/Computability/Complexity/CookLevin/PolyTime.lean`.

## Main results

* `Cslib.Complexity.CookLevin.computableInPolyTime_initClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_acceptClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_sitClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_uniqueClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_oneHotClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_inputClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_readClauses`.
* `Cslib.Complexity.CookLevin.computableInPolyTime_stepClauses`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM ComputableInPolyTime Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State]

@[local fun_prop]
private theorem mapConst_plain {ι : Type*} {α β : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} (l : List ι) {f : α → ι → β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn encB) :
    ComputableInPolyTime (fun x => l.map (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact (hf a (List.mem_cons_self ..)).cons'
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

@[local fun_prop]
private theorem flatMapConst_plain {ι : Type*} {α β : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} (l : List ι) {f : α → ι → List β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn (encList encB)) :
    ComputableInPolyTime (fun x => l.flatMap (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact (hf a (List.mem_cons_self ..)).listAppend'
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

@[local fun_prop]
private theorem mapFilterConst_plain {ι : Type*} {α β : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} (list : List ι) {test : α → ι → Bool} {f : α → ι → β}
    (htest : ∀ i ∈ list, ComputableInPolyTime (fun x => test x i) encIn encBool)
    (hf : ∀ i ∈ list, ComputableInPolyTime (fun x => f x i) encIn encB) :
    ComputableInPolyTime (fun x => (list.filter (test x)).map (f x)) encIn (encList encB) := by
  induction list with
  | nil => exact const []
  | cons a list ih =>
    have htail := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    have h := (htest a (List.mem_cons_self ..)).ite'
      ((hf a (List.mem_cons_self ..)).cons' htail) htail
    refine h.of_enc_eq fun x => ?_
    cases hta : test x a <;> simp [hta]

@[local fun_prop]
private theorem int_abs_le_nat'_plain {α : Type} {input : α ↪ List Bool}
    {position : α → ℤ} {bound : α → ℕ}
    (hposition : ComputableInPolyTime position input encInt)
    (hbound : ComputableInPolyTime bound input encUnary) :
    ComputableInPolyTime (fun a => decide (|position a| ≤ (bound a : ℤ))) input encBool := by
  simp only [← Int.natCast_natAbs, Int.ofNat_le]
  fun_prop

/-- Enumerate the feature groups in polynomial time in the unary input and window bounds. -/
@[fun_prop]
theorem computableInPolyTime_groups :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => Feature.groups (k := k) (State := State) p.1 p.2)
      (encPair encUnary encUnary) (encList (encList encFeature)) := by
  unfold Feature.groups
  simp only [SProd.sprod, List.product, List.map_flatMap, List.map_map, Function.comp_def]
  fun_prop

/-- Build all exactly-one clauses for one tableau row, including the input-dependent windows. -/
@[fun_prop]
theorem computableInPolyTime_oneHotClauses [DecidableEq State]
    {α : Type} {enc : α ↪ List Bool} {u : α → List Bool} {L T t : α → ℕ}
    (hu : ComputableInPolyTime u enc encBits)
    (hL : ComputableInPolyTime L enc encUnary)
    (hT : ComputableInPolyTime T enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime
      (fun a => oneHotClauses (k := k) (State := State) (u a) (L a) (T a) (t a)) enc
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [oneHotClauses]

/-- Build the existing initial-configuration clauses from a unary window bound. -/
@[fun_prop]
theorem computableInPolyTime_initClauses (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (initClauses tm) encUnary
      (encList (encList (encPair encVar encBool))) := by
  unfold initClauses
  refine (const _).listAppend' (flatMapConst_plain _ fun i _ => (const _).cons' ?_)
  fun_prop

/-- Build the two accepting-configuration clauses from a unary time. -/
@[fun_prop]
theorem computableInPolyTime_acceptClauses :
    ComputableInPolyTime (acceptClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [acceptClauses]

/-- Build the situation clauses at a unary time, with the finite machine data fixed. -/
@[fun_prop]
theorem computableInPolyTime_sitClauses :
    ComputableInPolyTime (sitClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [sitClauses]

/-- Build the uniqueness clauses at a unary time, with the finite machine data fixed. -/
@[fun_prop]
theorem computableInPolyTime_uniqueClauses [DecidableEq State] :
    ComputableInPolyTime (uniqueClauses (k := k) (State := State)) encUnary
      (encList (encList (encPair encVar encBool))) := by
  fun_prop [uniqueClauses]

/-- Build input-symbol clauses from computed input, certificate length, time and position. -/
@[fun_prop]
theorem computableInPolyTime_inputClauses {α : Type} {enc : α ↪ List Bool}
    {u : α → List Bool} {L t j : α → ℕ}
    (hu : ComputableInPolyTime u enc encBits)
    (hL : ComputableInPolyTime L enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime
      (fun a => inputClauses (k := k) (State := State) (u a) (L a) (t a) (j a))
      enc (encList (encList (encPair encVar encBool))) := by
  fun_prop [inputClauses]

/-- Enumerate work-tape and input-symbol clauses, charging the complete input-dependent lists. -/
@[fun_prop]
theorem computableInPolyTime_readClauses
    {α : Type} {enc : α ↪ List Bool} {u : α → List Bool} {L T t : α → ℕ}
    (hu : ComputableInPolyTime u enc encBits)
    (hL : ComputableInPolyTime L enc encUnary)
    (hT : ComputableInPolyTime T enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime
      (fun a => readClauses (k := k) (State := State) (u a) (L a) (T a) (t a)) enc
      (encList (encList (encPair encVar encBool))) := by
  unfold readClauses
  apply listAppend' <;> fun_prop

section Step

variable [DecidableEq State] (tm : MultiTapeTM k Bool State)
  {α : Type} {enc : α ↪ List Bool} {n T : α → ℕ}

private theorem stepTerms_state (q : Option State) :
    ComputableInPolyTime (fun a => Feature.stepTerms tm (n a) (T a) (.state q))
      enc (encList (encList (encPair encFeature encBool))) := const _

private theorem stepTerms_out (o : OutView) :
    ComputableInPolyTime (fun a => Feature.stepTerms tm (n a) (T a) (.out o))
      enc (encList (encList (encPair encFeature encBool))) := const _

private theorem stepTerms_cell (i : Fin k) (s : Option Bool) {z : α → ℤ}
    (hz : ComputableInPolyTime z enc encInt) :
    ComputableInPolyTime (fun a => Feature.stepTerms tm (n a) (T a) (.cell i (z a) s))
      enc (encList (encList (encPair encFeature encBool))) := by
  fun_prop [Feature.stepTerms]

private theorem stepTerms_head (i : Fin k) {z : α → ℤ}
    (hT : ComputableInPolyTime T enc encUnary)
    (hz : ComputableInPolyTime z enc encInt) :
    ComputableInPolyTime (fun a => Feature.stepTerms tm (n a) (T a) (.head i (z a)))
      enc (encList (encList (encPair encFeature encBool))) := by
  unfold Feature.stepTerms
  apply cons'
  · fun_prop
  · apply mapFilterConst_plain
    · intro y _
      fun_prop
    · intro y _
      fun_prop

private theorem stepTerms_inPos {j : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => Feature.stepTerms tm (n a) (T a) (.inPos (j a)))
      enc (encList (encList (encPair encFeature encBool))) := by
  unfold Feature.stepTerms
  apply cons'
  · fun_prop
  · simp only [SProd.sprod, List.product, List.filter_flatMap, List.filter_map,
      List.map_flatMap, List.map_map, Function.comp_def]
    apply flatMapConst_plain
    intro y _
    apply mapWithInput (encA := encUnary)
    · fun_prop
    · fun_prop

omit [DecidableEq State] in
private theorem stepImpClauses {t : α → ℕ} {feature : α → Feature k State}
    {terms : α → List (Feature.Term k State)}
    (ht : ComputableInPolyTime t enc encUnary)
    (hfeature : ComputableInPolyTime feature enc encFeature)
    (hterms : ComputableInPolyTime terms enc
      (encList (encList (encPair encFeature encBool)))) :
    ComputableInPolyTime (fun a => (terms a).map fun c =>
      Clause.impLits (c.map fun l => (.holds (t a) l.1, l.2))
        (.holds (t a + 1) (feature a))) enc (encList (encList (encPair encVar encBool))) := by
  apply mapWithInput (encA := encList (encPair encFeature encBool))
  · exact hterms
  · fun_prop

end Step

/-- Build the step constraints by enumerating the fixed constructor templates in their original
order. Positions and bounds are unary; the machine's finite transition table is fixed. -/
@[fun_prop]
theorem computableInPolyTime_stepClauses [DecidableEq State]
    (tm : MultiTapeTM k Bool State)
    {α : Type} {enc : α ↪ List Bool} {u : α → List Bool} {L T t : α → ℕ}
    (hu : ComputableInPolyTime u enc encBits)
    (hL : ComputableInPolyTime L enc encUnary)
    (hT : ComputableInPolyTime T enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime
      (fun a => stepClauses tm (u a) (L a) (T a) (t a)) enc
      (encList (encList (encPair encVar encBool))) := by
  unfold stepClauses
  simp only [Feature.basic, Feature.groups, List.flatten_eq_flatMap, List.flatMap_assoc,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_map, List.flatMap_append,
    SProd.sprod, List.product, List.append_nil, List.append_assoc, id_eq]
  refine listAppend' ?_ (listAppend' ?_ (listAppend' ?_ (listAppend' ?_ ?_)))
  · apply flatMapConst_plain
    intro q _
    exact stepImpClauses (by fun_prop) (by fun_prop) (stepTerms_state tm q)
  · apply flatMapWithInput (encA := encUnary) (by fun_prop)
    exact stepImpClauses (by fun_prop) (by fun_prop)
      (stepTerms_inPos tm (by fun_prop) (by fun_prop))
  · apply flatMapConst_plain
    intro i _
    apply flatMapWithInput (encA := encInt) (by fun_prop)
    exact stepImpClauses (by fun_prop) (by fun_prop)
      (stepTerms_head tm i (by fun_prop) (by fun_prop))
  · apply flatMapConst_plain
    intro i _
    apply flatMapWithInput (encA := encInt) (by fun_prop)
    apply flatMapConst_plain
    intro s _
    exact stepImpClauses (by fun_prop) (by fun_prop) (stepTerms_cell tm i s (by fun_prop))
  · apply flatMapConst_plain
    intro o _
    exact stepImpClauses (by fun_prop) (by fun_prop) (stepTerms_out tm o)

end Cslib.Complexity.CookLevin
