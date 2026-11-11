/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Declared CSPs
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL
open Turing.MultiTapeTM

/-- A Constraint Satisfaction Problem equipped with an explicit number of declared variables. -/
structure DeclaredCSP (Rel : Type) where
  numVars : ℕ
  formula : CSP Rel ℕ
  deriving Repr

/-- Canonical bit encoding of `DeclaredCSP`. -/
@[expose]
def encDeclaredCSP {Rel : Type} (encRel : Rel ↪ List Bool) : DeclaredCSP Rel ↪ List Bool :=
  ⟨fun x => encPair encUnary (encCSP encRel encNat) (x.numVars, x.formula), fun x y h => by
    have h' := (encPair encUnary (encCSP encRel encNat)).injective h
    cases x; cases y; simp_all⟩

@[simp] theorem encDeclaredCSP_apply {Rel : Type} {encRel : Rel ↪ List Bool} (x : DeclaredCSP Rel) :
    encDeclaredCSP encRel x = encPair encUnary (encCSP encRel encNat) (x.numVars, x.formula) :=
  rfl

private theorem computableInDegree_fields {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInDegree (fun x : DeclaredCSP Rel => (x.numVars, x.formula))
      (encDeclaredCSP encRel) (encPair encUnary (encCSP encRel encNat)) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

@[scoped fun_prop]
theorem encDeclaredCSP_numVars_polyTime {Rel : Type} {γ : Type}
    {encIn : γ ↪ List Bool} {encRel : Rel ↪ List Bool} {g : γ → DeclaredCSP Rel}
    (hg : ComputableInPolyTime g encIn (encDeclaredCSP encRel)) :
    ComputableInPolyTime (fun x => (g x).numVars) encIn encUnary :=
  ComputableInPolyTime.fst encUnary (encCSP encRel encNat) |>.comp <|
    (computableInDegree_fields encRel).computableInPolyTime |>.comp hg

@[scoped fun_prop]
theorem encDeclaredCSP_formula_polyTime {Rel : Type} {γ : Type}
    {encIn : γ ↪ List Bool} {encRel : Rel ↪ List Bool} {g : γ → DeclaredCSP Rel}
    (hg : ComputableInPolyTime g encIn (encDeclaredCSP encRel)) :
    ComputableInPolyTime (fun x => (g x).formula) encIn (encCSP encRel encNat) :=
  ComputableInPolyTime.snd encUnary (encCSP encRel encNat) |>.comp <|
    (computableInDegree_fields encRel).computableInPolyTime |>.comp hg

@[scoped fun_prop]
theorem encDeclaredCSP_mk_polyTime {Rel : Type} {γ : Type}
    {encIn : γ ↪ List Bool} {encRel : Rel ↪ List Bool}
    {numVars : γ → ℕ} {formula : γ → CSP Rel ℕ}
    (hnumVars : ComputableInPolyTime numVars encIn encUnary)
    (hformula : ComputableInPolyTime formula encIn (encCSP encRel encNat)) :
    ComputableInPolyTime (fun x => DeclaredCSP.mk (numVars x) (formula x)) encIn (encDeclaredCSP encRel) := by
  have hd : ComputableInDegree (fun p : ℕ × CSP Rel ℕ => DeclaredCSP.mk p.1 p.2) (encPair encUnary (encCSP encRel encNat)) (encDeclaredCSP encRel) 1 1 := ComputableInDegree.of_eq fun _ => rfl
  exact hd.computableInPolyTime.comp (hnumVars.prod hformula)

namespace DeclaredCSP

variable {Rel : Type}

@[expose] def WellFormed (x : DeclaredCSP Rel) : Prop :=
  ∀ v ∈ x.formula.vars, v < x.numVars

@[expose] def wellFormed (x : DeclaredCSP Rel) : Bool :=
  x.formula.vars.all fun v => decide (v < x.numVars)

end DeclaredCSP
end Cslib.Complexity
