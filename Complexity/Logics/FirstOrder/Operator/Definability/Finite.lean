/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Definability.Polarity

/-!
# Formula synthesis for fixed finite choices

A fixed finite family of defining formulas can be conjoined or disjoined without changing
the relational polarity. The indexing type is independent of the structure, so these rules
construct one finite formula uniformly across all domain sizes. They support, for example,
finite machine transition tables in descriptive-complexity proofs.

## Main results

* `PolarityDefinable.constant`: structure-independent truth values are definable.
* `PolarityDefinable.iEx`, `PolarityDefinable.iAll`: fixed finite choices and conjunctions.

All three rules participate in the extensible `FODefinable` synthesis rule set.
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

/-- A fixed finite disjunction preserves a certified polarity. -/
theorem iEx {β : Type r} [Finite β] {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∃ b, P b i v) := by
  classical
  let _ := Fintype.ofFinite β
  have hlist (l : List β) : PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => ∃ b ∈ l, P b i v) := by
    induction l with
    | nil => exact falsity.congr fun _ _ => by simp
    | cons b l ih => exact ((hP b).disj ih).congr fun _ _ => by simp
  exact (hlist (Finset.univ : Finset β).toList).congr fun _ _ => by simp

/-- A fixed finite conjunction preserves a certified polarity. -/
theorem iAll {β : Type r} [Finite β] {P : β → ∀ i, (α → M i) → Prop}
    (hP : ∀ b, PolarityDefinable (L := L) policy mark sign M I ρ (P b)) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∀ b, P b i v) := by
  classical
  let _ := Fintype.ofFinite β
  have hlist (l : List β) : PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => ∀ b ∈ l, P b i v) := by
    induction l with
    | nil => exact truth.congr fun _ _ => by simp
    | cons b l ih => exact ((hP b).conj ih).congr fun _ _ => by simp
  exact (hlist (Finset.univ : Finset β).toList).congr fun _ _ => by simp

attribute [aesop safe apply (rule_sets := [FODefinable])] constant iEx iAll

end Cslib.Logic.FO.Operator.PolarityDefinable
