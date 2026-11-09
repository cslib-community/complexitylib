/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.BooleanClone.Classification
public import CslibFrontier.Logics.Propositional.CSP.Boolean

/-!
# Clones of positive-arity Boolean operations

A clone contains the coordinate projections and is closed under superposition. Only positive
arities participate; the set of nullary operations is explicitly empty. This convention permits
empty relations and agrees with the unary constants in the Boolean CSP criterion.

The classification is [Chen2006CSP], Theorem 5.1 (arXiv version 1, printed pp. 17–18): a Boolean
clone consists of essentially unary operations or contains AND, OR, majority or minority.
The arbitrary-arity proof in the shared classification is original: ternary partition minors
detect a singleton coordinate, avoiding a minimum-essential-arity argument. There is no bound
on operation arity. This is an algebraic classification, not a complexity dichotomy.

## Main definitions

* `Cslib.Logic.BooleanClone`: positive-arity Boolean clones.
* `Cslib.Logic.EssentiallyUnary`: dependence on at most one coordinate.
* `Cslib.Logic.PL.CSP.polymorphismClone`: the clone of a fixed Boolean language.

## Main results

* `Cslib.Logic.BooleanClone.classification`: the four-generator classification at all arities.
* `Cslib.Logic.PL.CSP.projection_or_negation_of_not_hasSchaeferPolymorphism`:
  the six-case corollary.
* `Cslib.Logic.PL.CSP.isPolymorphism_selfDual_of_not_hasSchaeferPolymorphism`: preservation of
  every self-dual relation in the negative six-case branch.

## References

* [H. Chen, *A Rendezvous of Logic, Complexity, and Algebra*][Chen2006CSP], Theorem 5.1,
  arXiv version 1, printed pp. 17–18.
-/

public section

namespace Cslib.Logic
namespace BooleanClone

/-- The common positive-arity polymorphisms of any fixed family of finite Boolean relations
form a clone. No finiteness or nonemptiness of the family, or of its relations, is required. -/
@[expose] def ofRelations {Rel : Type*} (arity : Rel → ℕ)
    (R : ∀ r, Set (Fin (arity r) → Bool)) : BooleanClone where
  operations n := {f | 0 < n ∧ ∀ r, IsPolymorphism f (R r)}
  nullary := by ext f; simp
  projection i := ⟨lt_of_le_of_lt (Nat.zero_le _) i.isLt,
    fun r => isPolymorphism_projection i (R r)⟩
  comp _ hn _ _ hf hg := ⟨hn, fun r => (hf.2 r).comp (fun i => (hg i).2 r)⟩

end BooleanClone

namespace PL.CSP

/-- The positive-arity polymorphism clone of a fixed Boolean CSP language. -/
@[expose] def polymorphismClone {Rel : Type*} (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) : BooleanClone :=
  BooleanClone.ofRelations arity (booleanRelation arity sem)

/-- Membership includes the positive-arity convention explicitly. -/
theorem mem_polymorphismClone_iff {Rel : Type*} (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) {n : ℕ} (f : (Fin n → Bool) → Bool) :
    f ∈ (polymorphismClone arity sem).operations n ↔ 0 < n ∧ HasPolymorphism arity sem f :=
  Iff.rfl

/-- If all six Schaefer polymorphisms are absent, each positive-arity polymorphism is a
coordinate projection or its Boolean negation. Constants here are unary, so empty relations
are handled by precisely the shared Schaefer criterion. -/
theorem projection_or_negation_of_not_hasSchaeferPolymorphism {Rel : Type*}
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ HasSchaeferPolymorphism arity sem)
    {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : HasPolymorphism arity sem f) :
    ∃ i : Fin n, f = (fun a => a i) ∨ f = (fun a => !(a i)) := by
  let C := polymorphismClone arity sem
  have hand : BooleanClone.andOp ∉ C.operations 2 := fun he =>
    h (Or.inr (Or.inr (Or.inl he.2)))
  have hor : BooleanClone.orOp ∉ C.operations 2 := fun he =>
    h (Or.inr (Or.inr (Or.inr (Or.inl he.2))))
  have hmaj : (Cslib.majority 3) ∉ C.operations 3 := fun he =>
    h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he.2)))))
  have hmin : (Cslib.parity 3) ∉ C.operations 3 := fun he =>
    h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he.2)))))
  obtain ⟨i, u, hu⟩ := C.essentiallyUnary_of_missing_generators hand hor hmaj hmin hn ⟨hn, hf⟩
  have hc (b : Bool) (hb : ∀ c, u c = b) :
      HasPolymorphism arity sem (fun _ : Fin 1 → Bool => b) := by
    have hd := (C.diagonal hn ⟨hn, hf⟩).2
    simpa only [hu, hb, HasPolymorphism] using hd
  cases h₀ : u false <;> cases h₁ : u true
  · exact False.elim (h (Or.inl (hc false (fun c => by cases c <;> assumption))))
  · refine ⟨i, Or.inl (funext fun a => ?_)⟩
    rw [hu]
    cases ha : a i <;> assumption
  · refine ⟨i, Or.inr (funext fun a => ?_)⟩
    rw [hu]
    cases ha : a i <;> assumption
  · exact False.elim (h (Or.inr (Or.inl (hc true (fun c => by cases c <;> assumption)))))

/-- Every polymorphism of a language missing the six operations preserves every relation
closed under simultaneous Boolean negation. This includes empty and nullary relations. -/
theorem isPolymorphism_selfDual_of_not_hasSchaeferPolymorphism {Rel I : Type*}
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ HasSchaeferPolymorphism arity sem)
    {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : HasPolymorphism arity sem f) (R : Set (I → Bool))
    (hR : ∀ a ∈ R, (fun i => !(a i)) ∈ R) : IsPolymorphism f R := by
  obtain ⟨i, hi | hi⟩ := projection_or_negation_of_not_hasSchaeferPolymorphism arity sem h hn hf
  · rw [hi]
    exact isPolymorphism_projection i R
  · rw [hi]
    exact fun a ha => hR (a i) (ha i)

end PL.CSP
end Cslib.Logic
