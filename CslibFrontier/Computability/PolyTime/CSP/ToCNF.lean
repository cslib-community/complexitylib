/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.ToCNF
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time forbidden-pattern compilation of Boolean CSPs

The existing width-guarded compiler `Cslib.Logic.PL.CSP.toCNFBounded` is polynomial-time for
fixed width when its finite relation tables can be evaluated in polynomial time. These
certificates serve both exact counting and approximation-preserving reductions.

## Main definitions

* `Cslib.Complexity.encConstraint`, `Cslib.Complexity.encCSP`: framed binary encodings of
  constraints and their lists.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_of_forall`: compilation from
  polynomial-time evaluations of the finitely many relevant local patterns.
* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded`: compilation from a polynomial-time
  relation evaluator.
* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_of_finite`: compilation for a finite
  relation alphabet.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Binary encoding of a constraint `⟨R, vs⟩ : Constraint Rel V`: the encoded pair of its relation
symbol and its scope. -/
def encConstraint {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    Constraint Rel V ↪ List Bool :=
  encOfEquiv Constraint.equivProd (encPair encRel (encList encV))

@[simp]
theorem encConstraint_apply {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool)
    (c : Constraint Rel V) :
    encConstraint encRel encV c = encPair encRel (encList encV) (c.rel, c.scope) :=
  rfl

/-- Binary encoding of a CSP instance `F : CSP Rel V`. -/
abbrev encCSP {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    CSP Rel V ↪ List Bool :=
  encList (encConstraint encRel encV)

section encConstraintRules

variable {Rel V γ : Type} {encRel : Rel ↪ List Bool} {encV : V ↪ List Bool}
  {encIn : γ ↪ List Bool}

/-- Reading the relation symbol of a polynomial-time constraint is polynomial-time. -/
@[fun_prop]
theorem encConstraint_rel_polyTime {g : γ → Constraint Rel V}
    (h : ComputableInPolyTime g encIn (encConstraint encRel encV)) :
    ComputableInPolyTime (fun a => (g a).rel) encIn encRel :=
  (ComputableInPolyTime.fst encRel (encList encV)).comp
    ((ComputableInPolyTime.of_eq fun _ => rfl).comp h)

/-- Reading the scope of a polynomial-time constraint is polynomial-time. -/
@[fun_prop]
theorem encConstraint_scope_polyTime {g : γ → Constraint Rel V}
    (h : ComputableInPolyTime g encIn (encConstraint encRel encV)) :
    ComputableInPolyTime (fun a => (g a).scope) encIn (encList encV) :=
  (ComputableInPolyTime.snd encRel (encList encV)).comp
    ((ComputableInPolyTime.of_eq fun _ => rfl).comp h)

/-- Building a constraint from a polynomial-time relation symbol and scope is polynomial-time. -/
@[fun_prop]
theorem encConstraint_mk_polyTime {r : γ → Rel} {vs : γ → List V}
    (hr : ComputableInPolyTime r encIn encRel)
    (hvs : ComputableInPolyTime vs encIn (encList encV)) :
    ComputableInPolyTime (fun a => (⟨r a, vs a⟩ : Constraint Rel V)) encIn
      (encConstraint encRel encV) :=
  (hr.prod hvs).of_enc_eq fun _ => rfl

end encConstraintRules

namespace CSP

variable {Rel V : Type}

open Cslib.Logic.PL.CSP ComputableInPolyTime


private theorem computableInPolyTime_mapFilterConst {α ι γ : Type} {encIn : α ↪ List Bool}
    {encC : γ ↪ List Bool} (items : List ι) {test : α → ι → Bool} {f : α → ι → γ}
    (htest : ∀ i ∈ items, ComputableInPolyTime (fun a => test a i) encIn encBool)
    (hf : ∀ i ∈ items, ComputableInPolyTime (fun a => f a i) encIn encC) :
    ComputableInPolyTime (fun a => (items.filter (test a)).map (f a)) encIn (encList encC) := by
  induction items with
  | nil => exact const []
  | cons item rest ih =>
    have hrest := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    have hhead := hf item List.mem_cons_self
    have hkeep := htest item List.mem_cons_self
    refine (hkeep.ite (cons' hhead hrest) hrest).of_enc_eq fun a => ?_
    simp only [List.filter_cons]
    cases test a item <;> simp

private theorem computableInPolyTime_forbidClause (encV : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : List V × List Bool => Constraint.forbidClause p.1 p.2)
      (encPair (encList encV) (encList encBool))
      (encList (encPair encV encBool)) := by
  unfold Constraint.forbidClause
  fun_prop

private theorem computableInPolyTime_toCNFAt (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (sem : Rel → List Bool → Bool) (r : ℕ)
    (hsem : ∀ w ∈ BitString.enumList r,
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime
      (fun c : Constraint Rel V =>
        ((BitString.enumList r).filter fun w => !sem c.rel w).map (Constraint.forbidClause c.scope))
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  refine computableInPolyTime_mapFilterConst (BitString.enumList r)
    (test := fun (c : Constraint Rel V) (w : List Bool) => !sem c.rel w)
    (f := fun (c : Constraint Rel V) (w : List Bool) => Constraint.forbidClause c.scope w)
    (fun w hw => ?_) (fun w _ => ?_)
  · have hsemw := hsem w hw
    fun_prop
  · exact (computableInPolyTime_forbidClause encV).comp
      ((encConstraint_scope_polyTime id').prod (const w))

private theorem computableInPolyTime_constraintToCNFBounded
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime (Constraint.toCNFBounded k sem)
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  induction k with
  | zero =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel V => decide (c.scope.length = 0))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem 0
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (const [])).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF, Nat.le_zero]
    by_cases h : c.scope.length = 0 <;> simp [h]
  | succ k ih =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel V => decide (c.scope.length = k + 1))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem (k + 1)
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (ih fun w hw => hsem w (hw.trans (Nat.le_succ k)))).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF]
    by_cases h1 : c.scope.length = k + 1
    · simp [h1]
    · have hle : (c.scope.length ≤ k + 1) ↔ (c.scope.length ≤ k) := by omega
      simp [h1, hle]

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time whenever `fun R => sem R w` is computable in polynomial time for each bit pattern
`w` of length at most `k`. -/
theorem computableInPolyTime_toCNFBounded_of_forall (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV) (encCNFOver encV) := by
  have hc := computableInPolyTime_constraintToCNFBounded encRel encV k sem hsem
  exact flatMapWithInput (id' (encIn := encCSP encRel encV))
    (hc.comp (snd (encCSP encRel encV) (encConstraint encRel encV)))

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time whenever `sem` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toCNFBounded (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ComputableInPolyTime (fun p : Rel × List Bool => sem p.1 p.2)
      (encPair encRel encBits) encBool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV) (encCNFOver encV) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time for any finite relation alphabet `Rel`. -/
theorem computableInPolyTime_toCNFBounded_of_finite [Finite Rel] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV) (encCNFOver encV) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun _ _ => of_finite _

end CSP

end Cslib.Complexity
