/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.USTCON
import Complexity.Computability.Complexity.Parameterized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Complexity.Classes.Promise.Reduction

/-! Many-one reductions by a class of maps: polynomial-time and logspace reducibility, hardness and
completeness still unfold to their `∃` and `∀` forms, uses of the generic hardness lemmas, and axiom
guards for the core. -/

namespace ComplexityTests.ManyOne

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
  {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}

/-! ### Polynomial-time reductions keep their `∃` form -/

example (f : α → β) (hf : ComputableInPolyTime f encA encB) (h : ∀ a, a ∈ A ↔ f a ∈ B) :
    PolyTimeReducible encA encB A B :=
  ⟨f, hf, h⟩

example (h : PolyTimeReducible encA encB A B) :
    ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B := by
  obtain ⟨f, hf, hAB⟩ := h
  exact ⟨f, hf, hAB⟩

example : PolyTimeReducible encA encB A B ↔
    ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B :=
  Iff.rfl

example : PolyTimeHard 𝒞 encB B ↔
    ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒞 enc → PolyTimeReducible enc encB A B :=
  Iff.rfl

example : PolyTimeComplete 𝒞 encB B ↔ B ∈ 𝒞 encB ∧ PolyTimeHard 𝒞 encB B :=
  Iff.rfl

/-- The hardness conjunct of a completeness hypothesis is a `PolyTimeHard`, so dot notation on it
finds the `PolyTimeHard` API once it is named. (On `hB.2` itself, Lean first instantiates the
leading implicit binder of the unfolded `∀ {α : Type}`, as it did before `HardUnder`.) -/
example {γ : Type} {encC : γ ↪ List Bool} {C : Set γ} (hB : PolyTimeComplete 𝒞 encB B)
    (hBC : PolyTimeReducible encB encC B C) : PolyTimeHard 𝒞 encC C := by
  obtain ⟨-, hhard⟩ := hB
  exact hhard.trans hBC

example (hB : LogSpaceComplete 𝒞 encB B) : LogSpaceHard 𝒞 encB B :=
  hB.2

/-- Applying a hardness hypothesis gives a `PolyTimeReducible`, so dot notation still finds the
`PolyTimeReducible` API. -/
example (hB : PolyTimeHard 𝒞 encB B) (hA : A ∈ 𝒞 encA) (hBP : B ∈ P encB) : A ∈ P encA :=
  (hB encA A hA).mem_P hBP

/-- A hardness proof by introduction and an anonymous constructor. -/
example (h : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒞 enc →
    ∃ f : α → β, ComputableInPolyTime f enc encB ∧ ∀ a, a ∈ A ↔ f a ∈ B) :
    PolyTimeHard 𝒞 encB B := by
  intro α enc A hA
  obtain ⟨f, hf, hAB⟩ := h enc A hA
  exact ⟨f, hf, hAB⟩

/-- Regression test: the admissibility goal of an anonymous constructor is
`ComputableInPolyTime f encA encB` itself, not a beta-redex, so `fun_prop` proves it with no
`beta_reduce`. -/
example : PolyTimeReducible encBits encBits {w : List Bool | w.tail.headD false = true}
    {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

example : PolyTimeReducible encBits encBits {w : List Bool | w.tail.headD false = true}
    {w | w.headD false = true} :=
  ⟨List.tail, by guard_target =ₛ ComputableInPolyTime List.tail encBits encBits; fun_prop,
    fun _ => Iff.rfl⟩

/-! ### Logspace reductions keep their `∃` form -/

/-- Regression test: the admissibility goal of an anonymous constructor is
`ComputableInLogSpace f encA encA` itself, not a beta-redex. -/
example : LogSpaceReducible encA encA A A :=
  ⟨fun a => a, by guard_target =ₛ ComputableInLogSpace (fun a => a) encA encA; exact .id,
    fun _ => Iff.rfl⟩

example (f : α → β) (hf : ComputableInLogSpace f encA encB) (h : ∀ a, a ∈ A ↔ f a ∈ B) :
    LogSpaceReducible encA encB A B :=
  ⟨f, hf, h⟩

example (h : LogSpaceReducible encA encB A B) :
    ∃ f : α → β, ComputableInLogSpace f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B := by
  obtain ⟨f, hf, hAB⟩ := h
  exact ⟨f, hf, hAB⟩

example : LogSpaceReducible encA encB A B ↔
    ∃ f : α → β, ComputableInLogSpace f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B :=
  Iff.rfl

example : LogSpaceHard 𝒞 encB B ↔
    ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒞 enc → LogSpaceReducible enc encB A B :=
  Iff.rfl

example : LogSpaceComplete 𝒞 encB B ↔ B ∈ 𝒞 encB ∧ LogSpaceHard 𝒞 encB B :=
  Iff.rfl

/-- Both reducibilities are many-one reducibility by their class of maps: concrete reductions,
core `refl` witnesses, and `USTCON`'s logspace completeness transport across the bridges. -/
example :
    ManyOneReducibleBy (ComputableInPolyTime · encBits encBits)
      {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} ∧
    LogSpaceReducible encA encA A A ∧
    PolyTimeReducible encA encA A A ∧
    CompleteUnder (fun enc => LogSpaceReducible enc encUSTCON) L encUSTCON USTCON :=
  ⟨polyTimeReducible_iff_manyOneReducibleBy.mp ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩,
   logSpaceReducible_iff_manyOneReducibleBy.mpr (ManyOneReducibleBy.refl ComputableInLogSpace.id A),
   polyTimeReducible_iff_manyOneReducibleBy.mpr
     (ManyOneReducibleBy.refl ComputableInPolyTime.id' A),
   logSpaceComplete_iff_completeUnder.mp USTCON_logSpaceComplete_L⟩

/-! ### Mapping reductions and fpt-reductions -/

/-- The identity, computable in polynomial time, bounds the parameter by itself, and both
`MappingReducible` and `FPTReducible` transport `ManyOneReducibleBy.refl` across their bridges. -/
example {κA : α → ℕ} :
    ComputableInFPTWithParam encA encA κA κA id ∧
    MappingReducible encA encA A A ∧
    FPTReducible encA encA κA κA A A := by
  have hid : ComputableInFPTWithParam encA encA κA κA id :=
    ⟨ComputableInPolyTime.id'.computableInFPTTime κA, id, fun _ => le_rfl⟩
  exact ⟨hid,
    mappingReducible_iff_manyOneReducibleBy.mpr
      (ManyOneReducibleBy.refl (isComputable_id encA) A),
    fptReducible_iff_manyOneReducibleBy.mpr (ManyOneReducibleBy.refl hid A)⟩

/-! ### Promise reductions -/

/-- `PromiseProblem.ofSet SAT` is `HardUnder` promise polynomial-time reductions for `NP`. -/
example :
    HardUnder (fun enc A Y => PromiseProblem.PolyTimeReducible enc encCNF (.ofSet A) Y)
      @NP (.ofSet SAT) :=
  PromiseProblem.npHard_iff_hardUnder.mp
    (PromiseProblem.npHard_of_polyTimeReducible_SAT (.refl encCNF (.ofSet SAT)))

universe u in
example {α : Type u} (enc : α ↪ List Bool) (X : PromiseProblem α) :
    PromiseProblem.PolyTimeReducible enc enc X X :=
  .refl enc X

/-! ### The generic hardness lemmas -/

/-- `USTCON` is complete for `L` under polynomial-time reductions, by weakening the reducibility
of its logspace completeness. -/
example : PolyTimeComplete L encUSTCON USTCON :=
  CompleteUnder.mono (fun _ _ h => h.polyTimeReducible) USTCON_logSpaceComplete_L

/-- Hardness under polynomial-time reductions weakens to hardness under reductions by arbitrary
maps, a reducibility of the core with no admissibility condition. -/
example (hB : PolyTimeHard 𝒞 encB B) :
    HardUnder (fun _ => ManyOneReducibleBy fun _ => True) 𝒞 B :=
  HardUnder.mono (fun _ _ h => ManyOneReducibleBy.mono (fun _ _ => trivial) h) hB

/-- The complement of an `NP`-complete problem is `coNP`-complete, through the generic lemma. -/
example (hB : NPComplete encB B) : coNPComplete encB Bᶜ :=
  CompleteUnder.compl (fun _ _ h => h.compl) (fun _ _ => Iff.rfl) hB

/-- Logspace hardness for `SL` transfers along the identity reduction. -/
example : LogSpaceHard SL encUSTCON USTCON :=
  HardUnder.trans (fun _ _ h h' => h.trans h') USTCON_logSpaceHard_SL
    (LogSpaceReducible.refl encUSTCON USTCON)

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.ManyOneReducibleBy.refl' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ManyOneReducibleBy.refl

/--
info: 'Cslib.Complexity.ManyOneReducibleBy.trans' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ManyOneReducibleBy.trans

/--
info: 'Cslib.Complexity.ManyOneReducibleBy.mono' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ManyOneReducibleBy.mono

/--
info: 'Cslib.Complexity.ManyOneReducibleBy.compl' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ManyOneReducibleBy.compl

/--
info: 'Cslib.Complexity.ManyOneReducibleBy.lift' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ManyOneReducibleBy.lift

/--
info: 'Cslib.Complexity.HardUnder.mono' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HardUnder.mono

/--
info: 'Cslib.Complexity.HardUnder.trans' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HardUnder.trans

/--
info: 'Cslib.Complexity.CompleteUnder.mono' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CompleteUnder.mono

end ComplexityTests.ManyOne
