/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.ToCNF
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

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

/-- Binary encoding of a constraint `(R, vs) : Constraint Rel V`. -/
abbrev encConstraint {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    Constraint Rel V ↪ List Bool :=
  encPair encRel (encList encV)

/-- Binary encoding of a CSP instance `F : CSP Rel V`. -/
abbrev encCSP {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    CSP Rel V ↪ List Bool :=
  encList (encConstraint encRel encV)

namespace CSP

variable {Rel V : Type}

open Cslib.Logic.PL.CSP ComputableInPolyTime

/-- Zip framed lists in polynomial time. -/
@[local fun_prop]
theorem computableInPolyTime_zip {α β : Type}
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by
  rcases isEmpty_or_nonempty α with h | h
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.1 with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    rw [heq]
    exact const []
  rcases isEmpty_or_nonempty β with h' | h'
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.2 with
      | nil => simp
      | cons b _ => exact isEmptyElim b
    rw [heq]
    exact const []
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := h'
  have heq (p : List α × List β) : p.1.zip p.2 =
      (List.range (p.1.length - (p.1.length - p.2.length))).map
        (fun i => (p.1.getD i a, p.2.getD i b)) := by
    have hmin : p.1.length - (p.1.length - p.2.length) = min p.1.length p.2.length := by omega
    rw [hmin]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hleft : i < p.1.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).1
    have hright : i < p.2.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hleft,
      List.getElem?_eq_getElem hright, Option.getD_some]
  simp_rw [heq]
  fun_prop

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
        ((BitString.enumList r).filter fun w => !sem c.1 w).map (Constraint.forbidClause c.2))
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  refine computableInPolyTime_mapFilterConst (BitString.enumList r)
    (test := fun (c : Constraint Rel V) (w : List Bool) => !sem c.1 w)
    (f := fun (c : Constraint Rel V) (w : List Bool) => Constraint.forbidClause c.2 w)
    (fun w hw => ?_) (fun w _ => ?_)
  · have hsemw := hsem w hw
    fun_prop
  · exact (computableInPolyTime_forbidClause encV).comp
      ((snd encRel (encList encV)).prod (const w))

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
        (fun c : Constraint Rel V => decide (c.2.length = 0))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem 0
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (const [])).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF, Nat.le_zero]
    by_cases h : c.2.length = 0 <;> simp [h]
  | succ k ih =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel V => decide (c.2.length = k + 1))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem (k + 1)
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (ih fun w hw => hsem w (hw.trans (Nat.le_succ k)))).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF]
    by_cases h1 : c.2.length = k + 1
    · simp [h1]
    · have hle : (c.2.length ≤ k + 1) ↔ (c.2.length ≤ k) := by omega
      simp [h1, hle]

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time whenever `fun R => sem R w` is computable in polynomial time for each bit pattern
`w` of length at most `k`. -/
theorem computableInPolyTime_toCNFBounded_of_forall (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) := by
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
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time for any finite relation alphabet `Rel`. -/
theorem computableInPolyTime_toCNFBounded_of_finite [Finite Rel] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun _ _ => of_finite _

end CSP

end Cslib.Complexity
