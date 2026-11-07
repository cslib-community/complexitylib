/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Polymorphisms of relations

An operation preserves a relation when its coordinatewise application to tuples in that relation
again belongs to the relation. Relations are ordinary sets of functions, so the coordinate and
operation index types need not be finite. Empty index types include nullary relations and
operations. For finite nonempty index types this is [Chen2006CSP], Definition 3.10; allowing
arbitrary index types also includes infinitary and nullary operations and relations.

Preservation passes to conjunctions, variable substitutions and existential projections. These
are the elementary preservation rules underlying primitive-positive definitions; no converse
definability or complexity theorem is asserted here.

## Main definitions

* `Cslib.Logic.IsPolymorphism`: coordinatewise preservation of a relation by an operation.

## Main results

* `Cslib.Logic.IsPolymorphism.iInter`: preservation of conjunctions.
* `Cslib.Logic.IsPolymorphism.substitute`: preservation after variable substitution.
* `Cslib.Logic.IsPolymorphism.project`: preservation after existential projection.

## References

* [H. Chen, *A Rendezvous of Logic, Complexity, and Algebra*][Chen2006CSP], Definition 3.10
  and the preservation direction of Theorem 3.13 (arXiv version 1, pp. 8–10).
-/

public section

namespace Cslib.Logic

variable {D I J K : Type*}

/-- An operation `f` is a polymorphism of `R` when it preserves membership in `R` under
coordinatewise application. The index type `J` may be empty (a nullary operation). -/
@[expose] def IsPolymorphism (f : (J → D) → D) (R : Set (I → D)) : Prop :=
  ∀ a : J → I → D, (∀ j, a j ∈ R) → (fun i => f (fun j => a j i)) ∈ R

/-- Every projection operation preserves every relation. -/
theorem isPolymorphism_projection (j : J) (R : Set (I → D)) :
    IsPolymorphism (fun a : J → D => a j) R :=
  fun _ ha => ha j

/-- Composing polymorphisms yields another polymorphism of the same relation. -/
theorem IsPolymorphism.comp {f : (K → D) → D} {g : K → (J → D) → D}
    {R : Set (I → D)} (hf : IsPolymorphism f R) (hg : ∀ k, IsPolymorphism (g k) R) :
    IsPolymorphism (fun a => f (fun k => g k a)) R :=
  fun a ha => hf (fun k i => g k (fun j => a j i)) (fun k => hg k a ha)

/-- An operation preserves a conjunction of relations if it preserves every conjunct. -/
theorem IsPolymorphism.iInter {f : (J → D) → D} {R : K → Set (I → D)}
    (h : ∀ k, IsPolymorphism f (R k)) : IsPolymorphism f (⋂ k, R k) :=
  fun a ha => Set.mem_iInter.mpr fun k => h k a fun j => Set.mem_iInter.mp (ha j) k

/-- Substituting variables, including repeated variables, preserves polymorphisms. -/
theorem IsPolymorphism.substitute {f : (J → D) → D} {R : Set (I → D)}
    (h : IsPolymorphism f R) (p : I → K) :
    IsPolymorphism f {a : K → D | a ∘ p ∈ R} :=
  fun a ha => h (fun j => a j ∘ p) ha

/-- Existentially projecting coordinates preserves polymorphisms. The map `p` may also repeat
coordinates; equality constraints are thereby included. -/
theorem IsPolymorphism.project {f : (J → D) → D} {R : Set (I → D)}
    (h : IsPolymorphism f R) (p : K → I) :
    IsPolymorphism f {a : K → D | ∃ b ∈ R, b ∘ p = a} := by
  classical
  intro a ha
  choose b hb heq using ha
  refine ⟨fun i => f (fun j => b j i), h b hb, ?_⟩
  funext k
  exact congrArg f (funext fun j => congrFun (heq j) k)

/-- A nullary constant operation preserves exactly the relations containing its constant tuple.
In particular an empty relation is not preserved by a nullary operation. -/
theorem isPolymorphism_const_iff (b : D) (R : Set (I → D)) :
    IsPolymorphism (fun _ : Empty → D => b) R ↔ (fun _ => b) ∈ R := by
  constructor
  · intro h
    exact h (fun j => j.elim) (fun j => j.elim)
  · intro h _ _
    exact h

end Cslib.Logic
