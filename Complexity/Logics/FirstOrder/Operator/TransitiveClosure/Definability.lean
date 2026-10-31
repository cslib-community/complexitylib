/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.TransitiveClosure
public import Complexity.Logics.FirstOrder.Operator.Definability
public import Complexity.Tactic.FOOperator.Init

/-!
# Certified synthesis of tuple transitive closure

`definable_tc` constructs a well-formed closure formula from a certificate for its body. The
same formula works across the whole family of structures, including empty structures. Its rule
is registered in `FODefinable`, so `fo_definable` can compose closure with the ordinary logical
connectives and quantifiers.

## Main results

* `definable_tc`: synthesize closure from a uniformly definable body predicate.
* `definable_tc_pair`: the same certificate with separate source and target term tuples.
* `definable_tc_relation`: synthesize a semantic relation's closure directly.
-/

public section

universe u v w z t

open FirstOrder Language Cslib.Logic.FO.Operator

namespace Cslib.Logic.FO.TC

variable {L : Language.{u, v}} {ι : Type t} {M : ι → Type z}
  [∀ i, L.Structure (M i)] {Γ : List ℕ} {ρ : ∀ i, RelEnv Γ (M i)}
  {α : Type w} {k : ℕ} {P : ∀ i, (α ⊕ Fin (2 * k) → M i) → Prop}

/-- A uniformly definable body has a uniformly definable tuple transitive closure. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_tc (args : Fin (2 * k) → L.Term α)
    (hP : Operator.Definable (L := L) policy M (fun _ => interpretation) ρ P) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => Relation.ReflTransGen (fun xs ys => P i (Sum.elim v (pair xs ys)))
        (fun j => (left args j).realize v) (fun j => (right args j).realize v)) := by
  obtain ⟨body, hbody, hP⟩ := hP
  refine ⟨tc body args, by simpa only [wellFormed_tc] using hbody, ?_⟩
  intro i v
  rw [realize_tc]
  constructor
  · exact Relation.ReflTransGen.mono (fun xs ys h => (hP i (Sum.elim v (pair xs ys))).1 h) _ _
  · exact Relation.ReflTransGen.mono (fun xs ys h => (hP i (Sum.elim v (pair xs ys))).2 h) _ _

/-- Synthesize tuple closure with separately supplied source and target terms. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_tc_pair (xs ys : Fin k → L.Term α)
    (hP : Operator.Definable (L := L) policy M (fun _ => interpretation) ρ P) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => Relation.ReflTransGen (fun us vs => P i (Sum.elim v (pair us vs)))
        (fun j => (xs j).realize v) (fun j => (ys j).realize v)) := by
  simpa only [left_pair, right_pair] using definable_tc (pair xs ys) hP

/-- Synthesize a relation's closure directly. The body premise places the free parameters in
`Sum.inl` and the two endpoint tuples in `Sum.inr`. This formulation lets synthesis infer the
semantic relation without solving for a predicate applied to a composed assignment. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_tc_relation (xs ys : Fin k → L.Term α)
    {R : ∀ i, (α → M i) → (Fin k → M i) → (Fin k → M i) → Prop}
    (hR : Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i (v : α ⊕ Fin (2 * k) → M i) =>
        R i (v ∘ Sum.inl) (left (v ∘ Sum.inr)) (right (v ∘ Sum.inr)))) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => Relation.ReflTransGen (R i v)
        (fun j => (xs j).realize v) (fun j => (ys j).realize v)) := by
  apply (definable_tc_pair xs ys hR).congr
  intro i v
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, left_pair, right_pair]

end Cslib.Logic.FO.TC
