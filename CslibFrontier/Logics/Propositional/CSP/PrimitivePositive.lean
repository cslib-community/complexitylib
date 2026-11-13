/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.EquivFin

/-!
# Equality-free primitive-positive gadgets

The canonical table-of-tuples construction in [Chen2006CSP], Theorem 3.13, arXiv v1,
pp. 9–10, gives a finite gadget for a nonempty Boolean relation whose coordinate columns
are distinct, whenever its polymorphisms include all positive-arity polymorphisms of the
language. The variables of the canonical conjunction are all Boolean columns indexed by
the tuples of the target relation. Its constraints enumerate every scope that belongs
pointwise to a language relation. Satisfying assignments are exactly polymorphisms.

Distinct columns are necessary here to give separate free ports without equality symbols.
We do not implement the source's equality-based removal of repeated columns. Empty target
relations are excluded so that only positive-arity polymorphisms are needed. Empty and
nullary language relations are allowed, as are nullary target relations.

## Main definitions

* `Cslib.Logic.PL.CSP.PPGadget`: an equality-free conjunction with free and auxiliary ports.
* `Cslib.Logic.PL.CSP.SeparatesCoordinates`: distinct columns in the target tuple table.

## Main results

* `Cslib.Logic.PL.CSP.exists_ppGadget_of_polymorphisms`: the restricted finite Inv–Pol
  construction, using all positive finite arities.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel : Type} {n : ℕ}

/-- A finite equality-free conjunction with free coordinate ports and existential auxiliaries. -/
structure PPGadget (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (R : Set (Fin n → Bool)) where
  /-- Number of local auxiliary variables. -/
  numAux : ℕ
  /-- Conjunction over separate free and auxiliary ports. -/
  body : CSP Rel (Fin n ⊕ Fin numAux)
  /-- Every constraint has its declared arity. -/
  wellFormed : WellFormed arity body
  /-- The conjunction existentially defines the target relation. -/
  correct : ∀ a, a ∈ R ↔ ∃ b, body.eval sem (Sum.elim a b) = true

/-- A relation separates its coordinates if its tuple table has distinct columns. -/
@[expose] def SeparatesCoordinates (R : Set (Fin n → Bool)) : Prop :=
  ∀ i j, i ≠ j → ∃ a ∈ R, a i ≠ a j

namespace CanonicalPP

variable (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (R : Set (Fin n → Bool))

/-- The columns in the target's table of tuples. -/
private abbrev Column := R → Bool

/-- All scopes that satisfy a language relation in every row of the target table. -/
private def Scope := {c : (r : Rel) × (Fin (arity r) → Column R) //
  ∀ t : R, sem c.1 (List.ofFn fun i => c.2 i t) = true}

/-- The finite canonical conjunction, with columns as variables. -/
private noncomputable def body [Fintype Rel] : CSP Rel (Column R) := by
  classical
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype (Scope arity sem R) :=
    inferInstanceAs (Fintype {c : (r : Rel) × (Fin (arity r) → Column R) //
      ∀ t : R, sem c.1 (List.ofFn fun i => c.2 i t) = true})
  exact (Finset.univ.toList : List (Scope arity sem R)).map fun c =>
    ⟨c.val.1, List.ofFn c.val.2⟩

/-- All scopes of the canonical conjunction have exact declared arity. -/
private theorem wellFormed_body [Fintype Rel] : WellFormed arity (body arity sem R) := by
  classical
  intro c hc
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  simp

/-- Satisfying assignments of the canonical conjunction are precisely common polymorphisms
whose argument positions are the tuples of the target relation. -/
private theorem eval_body_iff [Fintype Rel] (f : Column R → Bool) :
    (body arity sem R).eval sem f = true ↔ HasPolymorphism arity sem f := by
  classical
  simp only [body, eval, List.all_map, List.all_eq_true, Finset.mem_toList,
    Finset.mem_univ, forall_true_left, Function.comp_def, Constraint.eval, List.map_ofFn]
  constructor
  · intro h r a ha
    exact h ⟨⟨r, fun i t => a t i⟩, ha⟩
  · intro h c
    exact h c.val.1 (fun t i => c.val.2 i t) c.property

/-- Evaluation at a row is a satisfying assignment of the canonical conjunction. -/
private theorem eval_body_projection [Fintype Rel] (t : R) :
    (body arity sem R).eval sem (fun c => c t) = true :=
  (eval_body_iff arity sem R _).mpr fun _ => isPolymorphism_projection t _

end CanonicalPP

/-- Finite positive-arity invariance suffices for an equality-free gadget when the target is
nonempty and has distinct columns. This is the corresponding restricted converse direction
of [Chen2006CSP], Theorem 3.13; no solver or pp-definability theorem is assumed. -/
theorem exists_ppGadget_of_polymorphisms [Finite Rel]
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (R : Set (Fin n → Bool))
    (hne : R.Nonempty) (hsep : SeparatesCoordinates R)
    (hinv : ∀ k, 0 < k → ∀ f : (Fin k → Bool) → Bool,
      HasPolymorphism arity sem f → IsPolymorphism f R) :
    Nonempty (PPGadget arity sem R) := by
  classical
  let _ : Fintype Rel := Fintype.ofFinite Rel
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Nonempty R := hne.to_subtype
  let C := CanonicalPP.Column R
  let _ : Fintype C := Fintype.ofFinite C
  let col : Fin n → C := fun i t => t.val i
  have hcol : Function.Injective col := by
    intro i j hij
    by_contra h
    obtain ⟨a, ha, hneq⟩ := hsep i j h
    exact hneq (congrFun hij ⟨a, ha⟩)
  let e := Fintype.equivFin C
  let port : C → Fin n ⊕ Fin (Fintype.card C) := fun c =>
    if h : ∃ i, col i = c then Sum.inl h.choose else Sum.inr (e c)
  have port_col (i : Fin n) : port (col i) = Sum.inl i := by
    dsimp [port]
    split
    · congr 1
      rename_i h
      exact hcol h.choose_spec
    · simp_all
  let F := CanonicalPP.body arity sem R
  refine ⟨⟨Fintype.card C, F.relabel port, ?_, ?_⟩⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa [Constraint.relabel] using CanonicalPP.wellFormed_body arity sem R d hd
  · intro a
    constructor
    · intro ha
      refine ⟨fun i => (e.symm i) ⟨a, ha⟩, ?_⟩
      rw [eval_relabel]
      have heq : (Sum.elim a (fun i => (e.symm i) ⟨a, ha⟩)) ∘ port =
          fun c : C => c ⟨a, ha⟩ := by
        funext c
        dsimp [port]
        split
        · rename_i h
          have hc := h.choose_spec
          simp only [Sum.elim_inl]
          exact congrArg (fun c : C => c ⟨a, ha⟩) hc
        · simp
      rw [heq]
      exact CanonicalPP.eval_body_projection arity sem R ⟨a, ha⟩
    · rintro ⟨b, hb⟩
      rw [eval_relabel] at hb
      let f : C → Bool := (Sum.elim a b) ∘ port
      have hf := (CanonicalPP.eval_body_iff arity sem R f).mp hb
      let er := Fintype.equivFin R
      let g : (Fin (Fintype.card R) → Bool) → Bool := fun v => f (v ∘ er)
      have hg : HasPolymorphism arity sem g := by
        intro r t ht
        exact hf r (fun j => t (er j)) (fun j => ht (er j))
      have hr := hinv (Fintype.card R) Fintype.card_pos g hg
        (fun j => (er.symm j).val) (fun j => (er.symm j).property)
      have heq : (fun i => g (fun j => (er.symm j).val i)) = a := by
        funext i
        change f ((fun j => (er.symm j).val i) ∘ er) = a i
        have harg : ((fun j => (er.symm j).val i) ∘ er) = col i := by
          funext t
          simp [col]
        rw [harg]
        change Sum.elim a b (port (col i)) = a i
        rw [port_col]
        rfl
      rwa [heq] at hr

end Cslib.Logic.PL.CSP
