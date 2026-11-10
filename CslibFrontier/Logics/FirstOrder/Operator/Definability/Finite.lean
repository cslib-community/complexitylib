/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.Definability.Polarity

/-!
# Formula synthesis for fixed finite choices

A fixed finite family of defining formulas can be conjoined or disjoined without changing
the relational polarity. The indexing type is independent of the structure, so these rules
construct one finite formula uniformly across all domain sizes. They support, for example,
finite machine transition tables in descriptive-complexity proofs.

## Main results

* `PolarityDefinable.constant`: structure-independent truth values are definable.
* `PolarityDefinable.exists_mem`, `PolarityDefinable.forall_mem`: disjunctions and conjunctions
  over a fixed list, with definability required only of its members.
* `PolarityDefinable.iEx`, `PolarityDefinable.iAll`: fixed finite choices and conjunctions.

`constant`, `iEx` and `iAll` participate in the extensible `FODefinable` synthesis rule set.
-/

public section

universe u v w z s t r

open FirstOrder Language

namespace Cslib.Logic.FO.Operator.PolarityDefinable

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape} {policy : Policy shape}
  {ι : Type t} {M : ι → Type z} [∀ i, L.Structure (M i)]
  {I : ∀ i, Interpretation shape (M i)} {Γ : List ℕ} {ρ : ∀ i, RelEnv Γ (M i)}
  {mark : Marking Γ} {sign : Bool} {α : Type w}

/-- A proposition independent of the structure and assignment has a constant formula. -/
theorem constant (p : Prop) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun _ (_ : α → _) => p) := by
  classical
  by_cases hp : p
  · exact truth.congr fun _ _ => iff_of_true trivial hp
  · exact falsity.congr fun _ _ => iff_of_false not_false hp

/-- A disjunction over a fixed list preserves a certified polarity. -/
theorem exists_mem {β : Type r} (l : List β) {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b ∈ l, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∃ b ∈ l, P b i v) := by
  induction l with
  | nil => exact falsity.congr fun _ _ => by simp
  | cons b l ih =>
    exact ((hP b (by simp)).disj (ih fun c hc => hP c (by simp [hc]))).congr fun _ _ => by simp

/-- A conjunction over a fixed list preserves a certified polarity. -/
theorem forall_mem {β : Type r} (l : List β) {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b ∈ l, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∀ b ∈ l, P b i v) := by
  induction l with
  | nil => exact truth.congr fun _ _ => by simp
  | cons b l ih =>
    exact ((hP b (by simp)).conj (ih fun c hc => hP c (by simp [hc]))).congr fun _ _ => by simp

/-- A fixed finite disjunction preserves a certified polarity. -/
theorem iEx {β : Type r} [Finite β] {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∃ b, P b i v) := by
  classical
  let _ := Fintype.ofFinite β
  exact (exists_mem (Finset.univ : Finset β).toList fun b _ => hP b).congr fun _ _ => by simp

/-- A fixed finite conjunction preserves a certified polarity. -/
theorem iAll {β : Type r} [Finite β] {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∀ b, P b i v) := by
  classical
  let _ := Fintype.ofFinite β
  exact (forall_mem (Finset.univ : Finset β).toList fun b _ => hP b).congr fun _ _ => by simp

attribute [aesop safe apply (rule_sets := [FODefinable])] constant iEx iAll

end Cslib.Logic.FO.Operator.PolarityDefinable
