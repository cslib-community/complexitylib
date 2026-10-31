/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Basic

/-!
# Satisfiability of clause sets

A clause set is *satisfiable* when some assignment satisfies all of its clauses
(`ClauseSet.Satisfiable`). Over a finite type of variables this is decidable, and it agrees with
satisfiability of a formula listing the clauses, and a formula with satisfiability of its clause set
(`ClauseSet.satisfiable_toCNF_iff`, `CNF.satisfiable_toClauseSet_iff`). Satisfaction of unions,
insertions, images and indexed unions of clause sets is characterized clause by clause, and renaming
the variables along an injective map preserves satisfiability (`ClauseSet.satisfiable_relabel`), as
for formulas (`CNF.satisfiable_relabel`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Satisfiable`: some assignment satisfies every clause.
* `Cslib.Logic.PL.ClauseSet.relabel`: rename the variables of a clause set.

## Main results

* `Cslib.Logic.PL.ClauseSet.satisfiable_toCNF_iff`,
  `Cslib.Logic.PL.CNF.satisfiable_toClauseSet_iff`: agreement with `CNF.Satisfiable`, in both
  directions.
* `Cslib.Logic.PL.ClauseSet.sat_union_iff`, `Cslib.Logic.PL.ClauseSet.sat_insert_iff`,
  `Cslib.Logic.PL.ClauseSet.sat_singleton_iff`, `Cslib.Logic.PL.ClauseSet.sat_empty`,
  `Cslib.Logic.PL.ClauseSet.sat_image_iff`, `Cslib.Logic.PL.ClauseSet.sat_biUnion_iff`:
  satisfaction of combined clause sets.
* `Cslib.Logic.PL.ClauseSet.sat_relabel_iff`, `Cslib.Logic.PL.ClauseSet.satisfiable_relabel`:
  relabelling.
* `Cslib.Logic.PL.ClauseSet.relabel_union`, `Cslib.Logic.PL.ClauseSet.mem_relabel`: the clauses of
  a relabelled clause set.
* `Cslib.Logic.PL.ClauseSet.card_relabel_le`, `Cslib.Logic.PL.ClauseSet.card_le_of_mem_relabel`:
  relabelling adds neither clauses nor literals.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

namespace ClauseSet

variable {V W ι : Type*}

/-- Some assignment satisfies every clause of `ψ`. -/
def Satisfiable (ψ : ClauseSet V) : Prop :=
  ∃ x : V → Bool, ψ.Sat x

instance [Fintype V] [DecidableEq V] (ψ : ClauseSet V) : Decidable ψ.Satisfiable :=
  inferInstanceAs (Decidable (∃ x : V → Bool, ψ.Sat x))

/-- A clause set is satisfiable exactly when a formula listing its clauses is. -/
theorem satisfiable_toCNF_iff (ψ : ClauseSet V) : ψ.toCNF.Satisfiable ↔ ψ.Satisfiable := by
  simp only [CNF.Satisfiable, ClauseSet.eval_toCNF_eq_true_iff, Satisfiable]

/-- A formula is satisfiable exactly when its clause set is. -/
theorem _root_.Cslib.Logic.PL.CNF.satisfiable_toClauseSet_iff [DecidableEq V] (φ : CNF V) :
    φ.toClauseSet.Satisfiable ↔ φ.Satisfiable :=
  exists_congr fun x => CNF.sat_toClauseSet_iff φ x

/-! ### Satisfaction of combined clause sets -/

section Sat

variable {x : V → Bool}

/-- An assignment satisfies a union exactly when it satisfies both parts. -/
@[simp] theorem sat_union_iff [DecidableEq V] {ψ φ : ClauseSet V} :
    (ψ ∪ φ).Sat x ↔ ψ.Sat x ∧ φ.Sat x := by
  simp only [Sat, mem_union]
  exact ⟨fun h => ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩,
    fun ⟨h₁, h₂⟩ C hC => hC.elim (h₁ C) (h₂ C)⟩

/-- An assignment satisfies `insert C ψ` exactly when it satisfies the clause `C` and `ψ`. -/
@[simp] theorem sat_insert_iff [DecidableEq V] {C : Finset (Literal V)} {ψ : ClauseSet V} :
    (insert C ψ).Sat x ↔ (∃ l ∈ C, x l.1 = l.2) ∧ ψ.Sat x := by
  simp [Sat]

/-- An assignment satisfies a single clause exactly when it makes one of its literals true. -/
@[simp] theorem sat_singleton_iff {C : Finset (Literal V)} :
    ({C} : ClauseSet V).Sat x ↔ ∃ l ∈ C, x l.1 = l.2 := by
  simp [Sat]

/-- Every assignment satisfies the empty clause set. -/
@[simp] theorem sat_empty : (∅ : ClauseSet V).Sat x := by
  simp [Sat]

/-- An assignment satisfies the clauses `f i` for `i ∈ s` exactly when it satisfies each. -/
theorem sat_image_iff [DecidableEq V] {s : Finset ι} {f : ι → Finset (Literal V)} :
    ClauseSet.Sat (s.image f) x ↔ ∀ i ∈ s, ∃ l ∈ f i, x l.1 = l.2 := by
  simp [Sat]

/-- An assignment satisfies an indexed union exactly when it satisfies each part. -/
theorem sat_biUnion_iff [DecidableEq V] {s : Finset ι} {f : ι → ClauseSet V} :
    ClauseSet.Sat (s.biUnion f) x ↔ ∀ i ∈ s, (f i).Sat x := by
  simp only [Sat, mem_biUnion]
  exact ⟨fun h i hi C hC => h C ⟨i, hi, hC⟩, fun h C ⟨i, hi, hC⟩ => h i hi C hC⟩

end Sat

/-! ### Relabelling -/

section Relabel

variable [DecidableEq W]

/-- Rename the variables of a clause set along `f`. -/
def relabel (f : V → W) (ψ : ClauseSet V) : ClauseSet W :=
  ψ.image fun C => C.image (Prod.map f id)

/-- `σ` satisfies `ψ.relabel f` exactly when `σ ∘ f` satisfies `ψ`. -/
@[simp] theorem sat_relabel_iff (f : V → W) (ψ : ClauseSet V) (σ : W → Bool) :
    (ψ.relabel f).Sat σ ↔ ψ.Sat (σ ∘ f) := by
  simp [relabel, Sat]

/-- Relabelling along an injective map preserves satisfiability. An assignment of the new
variables restricts to the old ones, and an assignment of the old variables extends along `f`. -/
theorem satisfiable_relabel {f : V → W} (hf : Function.Injective f) (ψ : ClauseSet V) :
    (ψ.relabel f).Satisfiable ↔ ψ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ f, (sat_relabel_iff f ψ σ).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨Function.extend f σ fun _ => false, (sat_relabel_iff f ψ _).mpr ?_⟩
    rwa [Function.extend_comp hf]

/-- Relabelling commutes with unions. -/
theorem relabel_union [DecidableEq V] (f : V → W) (ψ φ : ClauseSet V) :
    (ψ ∪ φ).relabel f = ψ.relabel f ∪ φ.relabel f :=
  image_union _ _

/-- Relabelling does not add clauses; it may merge some. -/
theorem card_relabel_le (f : V → W) (ψ : ClauseSet V) : (ψ.relabel f).card ≤ ψ.card :=
  card_image_le

/-- The clauses of `ψ.relabel f` are the images of the clauses of `ψ`. -/
@[simp] theorem mem_relabel {f : V → W} {ψ : ClauseSet V} {C : Finset (Literal W)} :
    C ∈ ψ.relabel f ↔ ∃ C' ∈ ψ, C'.image (Prod.map f id) = C :=
  mem_image

/-- Relabelling does not widen clauses: if every clause of `ψ` has at most `k` literals, so does
every clause of `ψ.relabel f`. -/
theorem card_le_of_mem_relabel {f : V → W} {ψ : ClauseSet V} {k : ℕ}
    (hψ : ∀ C ∈ ψ, C.card ≤ k) {C : Finset (Literal W)} (hC : C ∈ ψ.relabel f) : C.card ≤ k := by
  obtain ⟨C', hC', rfl⟩ := mem_relabel.mp hC
  exact card_image_le.trans (hψ C' hC')

end Relabel

end ClauseSet

end Cslib.Logic.PL
