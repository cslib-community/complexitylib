/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.USTCON
import Complexity.Computability.Complexity.Classes.SharpP.Completeness
import Complexity.Computability.Complexity.Classes.TFNP
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

/-- Both reducibilities are many-one reducibility by their class of maps. -/
example : PolyTimeReducible encA encB A B ↔
    ManyOneReducibleBy (ComputableInPolyTime · encA encB) A B :=
  polyTimeReducible_iff_manyOneReducibleBy

example : LogSpaceReducible encA encB A B ↔
    ManyOneReducibleBy (ComputableInLogSpace · encA encB) A B :=
  logSpaceReducible_iff_manyOneReducibleBy

/-- A core reduction by logspace maps, built from the core's `refl`, is a logspace reduction
through the bridge. -/
example : LogSpaceReducible encA encA A A :=
  logSpaceReducible_iff_manyOneReducibleBy.mpr (ManyOneReducibleBy.refl ComputableInLogSpace.id A)

/-- A core reduction by polynomial-time maps is a polynomial-time reduction through the bridge. -/
example : PolyTimeReducible encA encA A A :=
  polyTimeReducible_iff_manyOneReducibleBy.mpr
    (ManyOneReducibleBy.refl ComputableInPolyTime.id' A)

/-- Completeness under logspace reductions is `CompleteUnder` for `LogSpaceReducible`. -/
example (h : LogSpaceComplete 𝒞 encB B) :
    CompleteUnder (fun enc => LogSpaceReducible enc encB) 𝒞 encB B :=
  logSpaceComplete_iff_completeUnder.mp h

/-! ### Mapping reductions and fpt-reductions -/

example : MappingReducible encA encB A B ↔
    ∃ f : α → β, IsComputable f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B :=
  Iff.rfl

example : MappingReducible encA encB A B ↔
    ManyOneReducibleBy (IsComputable · encA encB) A B :=
  mappingReducible_iff_manyOneReducibleBy

example {κA : α → ℕ} {κB : β → ℕ} : FPTReducible encA encB κA κB A B ↔
    ∃ f : α → β, (ComputableInFPTTime f encA encB κA ∧
      ∃ h : ℕ → ℕ, ∀ a, κB (f a) ≤ h (κA a)) ∧ ∀ a, a ∈ A ↔ f a ∈ B :=
  Iff.rfl

example {κA : α → ℕ} {κB : β → ℕ} : FPTReducible encA encB κA κB A B ↔
    ManyOneReducibleBy (ComputableInFPTWithParam encA encB κA κB) A B :=
  fptReducible_iff_manyOneReducibleBy

/-- The identity, computable in polynomial time, bounds the parameter by itself. -/
example {κA : α → ℕ} : ComputableInFPTWithParam encA encA κA κA id :=
  ⟨(ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.id').computableInFPTTime κA, id,
    fun _ => le_rfl⟩

/-! ### Non-`Set` hardness and completeness instances -/

example {g : β → ℕ} : SharpPHard encB g ↔
    ∀ {α : Type} (enc : α ↪ List Bool) (f : α → ℕ), f ∈ SharpP enc →
      ParsimoniousReducible enc encB f g :=
  Iff.rfl

example {g : β → ℕ} : SharpPHard encB g ↔
    HardUnder (fun enc => ParsimoniousReducible enc encB) @SharpP g :=
  sharpPHard_iff_hardUnder

example {g : β → ℕ} : SharpPComplete encB g ↔
    CompleteUnder (fun enc => ParsimoniousReducible enc encB) @SharpP encB g :=
  sharpPComplete_iff_completeUnder

example {𝒮 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}
    {S : β → List Bool → Prop} : SearchHard 𝒮 encB S ↔
    ∀ {α : Type} (enc : α ↪ List Bool) (R : α → List Bool → Prop), R ∈ 𝒮 enc →
      SearchReducible enc encB R S :=
  Iff.rfl

example {𝒮 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}
    {S : β → List Bool → Prop} : SearchHard 𝒮 encB S ↔
    HardUnder (fun enc => SearchReducible enc encB) @𝒮 S :=
  searchHard_iff_hardUnder

example {𝒮 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}
    {S : β → List Bool → Prop} : SearchComplete 𝒮 encB S ↔
    CompleteUnder (fun enc => SearchReducible enc encB) @𝒮 encB S :=
  searchComplete_iff_completeUnder

example {Y : PromiseProblem β} : PromiseProblem.NPHard encB Y ↔
    ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ NP enc →
      PromiseProblem.PolyTimeReducible enc encB (.ofSet A) Y :=
  Iff.rfl

example {Y : PromiseProblem β} : PromiseProblem.NPHard encB Y ↔
    HardUnder (fun enc A Y => PromiseProblem.PolyTimeReducible enc encB (.ofSet A) Y) @NP Y :=
  PromiseProblem.npHard_iff_hardUnder

/-! ### Randomized reductions on promise problems -/

universe u in
example {α : Type u} (enc : α ↪ List Bool) (X : PromiseProblem α) :
    PromiseProblem.PolyTimeReducible enc enc X X :=
  .refl enc X

example {X : PromiseProblem α} {Y : PromiseProblem β} :
    PromiseProblem.RPReducible encA encB X Y ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ∀ b ∈ (Cslib.ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.no).toReal :=
  Iff.rfl

example {X : PromiseProblem α} {Y : PromiseProblem β} :
    PromiseProblem.RPReducible encA encB X Y ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.no).toReal :=
  PromiseProblem.rpReducible_iff_toOuterMeasure_eq_one

example {X : PromiseProblem α} {Y : PromiseProblem β} {s : α → ℝ} :
    PromiseProblem.RPReducibleWithError encA encB s Xᶜ Yᶜ ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.no, ∀ b ∈ (Cslib.ProbComp.eval (R a)).support, b ∈ Y.no) ∧
        ∀ a ∈ X.yes, s a ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal :=
  PromiseProblem.rpReducibleWithError_compl_iff

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.PolyTimeReducible encA encB X Y) :
    PromiseProblem.RPReducible encA encB X Y :=
  h.rpReducible

example {X : PromiseProblem α} : PromiseProblem.RPReducible encA encA X X :=
  PromiseProblem.RPReducible.refl encA X

example {γ : Type} {encC : γ ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    {s₁ : α → ℝ} {s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (hXY : PromiseProblem.RPReducibleWithError encA encB s₁ X Y)
    (hYZ : PromiseProblem.RPReducibleWithError encB encC (fun _ => s₂) Y Z) :
    PromiseProblem.RPReducibleWithError encA encC (fun a => s₁ a * s₂) X Z :=
  hXY.trans hYZ hs₂

example {γ : Type} {encC : γ ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    {s₁ : α → ℝ} {s₂ : ℝ} (hs₂ : s₂ ≤ 1)
    (hXY : PromiseProblem.RPReducibleWithError encA encB s₁ X Y)
    (hYZ : PromiseProblem.RPReducibleWithError encB encC (fun _ => s₂) Y Z) :
    PromiseProblem.RPReducibleWithError encA encC (fun a => s₁ a + s₂ - 1) X Z :=
  hXY.trans_add hYZ hs₂

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA :=
  hXY.mem_PromiseCoRP hY

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA :=
  hXY.mem_PromiseBPP hY

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB Xᶜ Yᶜ)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA :=
  hXY.mem_PromiseRP_of_compl hY

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
info: 'Cslib.Complexity.HardUnder.compl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HardUnder.compl

/--
info: 'Cslib.Complexity.CompleteUnder.mono' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CompleteUnder.mono

/--
info: 'Cslib.Complexity.CompleteUnder.compl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CompleteUnder.compl

end ComplexityTests.ManyOne
