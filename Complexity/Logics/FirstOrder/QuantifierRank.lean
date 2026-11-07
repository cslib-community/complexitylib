/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.ModelTheory.Syntax

/-!
# Quantifier rank

The quantifier rank of a first-order formula is the maximal nesting depth of its quantifiers. It is
the syntactic measure matched by the number of rounds of Ehrenfeucht–Fraïssé games
(`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka`). The notion is stated for Mathlib's
bounded formulas over an arbitrary language; no finiteness assumption is involved.

## Main definitions

* `Cslib.Logic.FO.quantifierRank`: the quantifier rank of a bounded formula.

## Main results

* `Cslib.Logic.FO.quantifierRank_bdEqual`, `Cslib.Logic.FO.quantifierRank_relations_boundedFormula`:
  atomic formulas have rank `0`.
* `Cslib.Logic.FO.quantifierRank_not`, `Cslib.Logic.FO.quantifierRank_ex`,
  `Cslib.Logic.FO.quantifierRank_inf`, `Cslib.Logic.FO.quantifierRank_sup`,
  `Cslib.Logic.FO.quantifierRank_iff`: the rank of the derived connectives.
* `Cslib.Logic.FO.quantifierRank_iInf_le`, `Cslib.Logic.FO.quantifierRank_iSup_le`: finite
  conjunctions and disjunctions do not increase the rank.
* `Cslib.Logic.FO.quantifierRank_castLE`, `Cslib.Logic.FO.quantifierRank_relabel`,
  `Cslib.Logic.FO.quantifierRank_formula_relabel`, `Cslib.Logic.FO.quantifierRank_toFormula`:
  Mathlib's maps between formulas with different variables preserve the rank.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3.
-/

public section

universe u v

open FirstOrder Language

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {α : Type*} {n : ℕ}

/-- The quantifier rank of a bounded formula: the maximal nesting depth of quantifiers. -/
def quantifierRank : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (quantifierRank φ) (quantifierRank ψ)
  | _, .all φ => quantifierRank φ + 1

@[simp] theorem quantifierRank_falsum : quantifierRank (.falsum : L.BoundedFormula α n) = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_bot : quantifierRank (⊥ : L.BoundedFormula α n) = 0 :=
  quantifierRank_falsum

@[simp] theorem quantifierRank_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    quantifierRank (.equal t₁ t₂ : L.BoundedFormula α n) = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    quantifierRank (.rel R ts : L.BoundedFormula α n) = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    quantifierRank (t₁.bdEqual t₂) = 0 :=
  quantifierRank_equal t₁ t₂

@[simp] theorem quantifierRank_relations_boundedFormula {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) : quantifierRank (R.boundedFormula ts) = 0 :=
  quantifierRank_rel R ts

@[simp] theorem quantifierRank_relations_boundedFormula₁ (R : L.Relations 1)
    (t : L.Term (α ⊕ Fin n)) : quantifierRank (R.boundedFormula₁ t) = 0 :=
  quantifierRank_rel R _

@[simp] theorem quantifierRank_relations_boundedFormula₂ (R : L.Relations 2)
    (t₁ t₂ : L.Term (α ⊕ Fin n)) : quantifierRank (R.boundedFormula₂ t₁ t₂) = 0 :=
  quantifierRank_rel R _

@[simp] theorem quantifierRank_imp (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ.imp ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_all (φ : L.BoundedFormula α (n + 1)) :
    quantifierRank φ.all = quantifierRank φ + 1 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_not (φ : L.BoundedFormula α n) :
    quantifierRank φ.not = quantifierRank φ := by
  simp [BoundedFormula.not]

@[simp] theorem quantifierRank_ex (φ : L.BoundedFormula α (n + 1)) :
    quantifierRank φ.ex = quantifierRank φ + 1 := by
  simp [BoundedFormula.ex]

@[simp] theorem quantifierRank_top : quantifierRank (⊤ : L.BoundedFormula α n) = 0 := by
  simp [Top.top]

@[simp] theorem quantifierRank_inf (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊓ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  simp [Min.min]

@[simp] theorem quantifierRank_sup (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊔ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  simp [Max.max]

@[simp] theorem quantifierRank_iff (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ.iff ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  simp [BoundedFormula.iff, max_comm]

private theorem quantifierRank_foldr_inf_le {l : List (L.BoundedFormula α n)} {m : ℕ}
    (h : ∀ φ ∈ l, quantifierRank φ ≤ m) : quantifierRank (l.foldr (· ⊓ ·) ⊤) ≤ m := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    rw [List.foldr_cons, quantifierRank_inf, max_le_iff]
    exact ⟨h φ List.mem_cons_self, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

private theorem quantifierRank_foldr_sup_le {l : List (L.BoundedFormula α n)} {m : ℕ}
    (h : ∀ φ ∈ l, quantifierRank φ ≤ m) : quantifierRank (l.foldr (· ⊔ ·) ⊥) ≤ m := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    rw [List.foldr_cons, quantifierRank_sup, max_le_iff]
    exact ⟨h φ List.mem_cons_self, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

/-- A finite conjunction has quantifier rank at most `m` when each conjunct does. -/
theorem quantifierRank_iInf_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n} {m : ℕ}
    (h : ∀ b, quantifierRank (f b) ≤ m) : quantifierRank (BoundedFormula.iInf f) ≤ m := by
  unfold BoundedFormula.iInf
  refine quantifierRank_foldr_inf_le fun φ hφ => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ
  exact h b

/-- A finite disjunction has quantifier rank at most `m` when each disjunct does. -/
theorem quantifierRank_iSup_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n} {m : ℕ}
    (h : ∀ b, quantifierRank (f b) ≤ m) : quantifierRank (BoundedFormula.iSup f) ≤ m := by
  unfold BoundedFormula.iSup
  refine quantifierRank_foldr_sup_le fun φ hφ => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ
  exact h b

/-! ### Invariance under Mathlib's syntactic maps -/

/-- Raising the number of bound variables in scope does not change the rank. -/
@[simp] theorem quantifierRank_castLE {m m' : ℕ} (h : m ≤ m') (φ : L.BoundedFormula α m) :
    quantifierRank (φ.castLE h) = quantifierRank φ := by
  induction φ generalizing m' with
  | falsum => simp only [BoundedFormula.castLE, quantifierRank_falsum]
  | equal => simp only [BoundedFormula.castLE, quantifierRank_equal]
  | rel => simp only [BoundedFormula.castLE, quantifierRank_rel]
  | imp _ _ ih₁ ih₂ => simp only [BoundedFormula.castLE, quantifierRank_imp, ih₁, ih₂]
  | all _ ih => simp only [BoundedFormula.castLE, quantifierRank_all, ih]

/-- Relabeling variables does not change the rank. -/
@[simp] theorem quantifierRank_relabel {β : Type*} (g : α → β ⊕ Fin n) {k : ℕ}
    (φ : L.BoundedFormula α k) : quantifierRank (φ.relabel g) = quantifierRank φ := by
  induction φ with
  | falsum => rfl
  | equal => exact quantifierRank_equal _ _
  | rel => exact quantifierRank_rel _ _
  | imp _ _ ih₁ ih₂ =>
    rw [BoundedFormula.relabel_imp, quantifierRank_imp, quantifierRank_imp, ih₁, ih₂]
  | all _ ih => rw [BoundedFormula.relabel_all, quantifierRank_all, quantifierRank_all, ih]

/-- Relabeling the free variables of a formula does not change the rank. -/
@[simp] theorem quantifierRank_formula_relabel {β : Type*} (g : α → β) (φ : L.Formula α) :
    quantifierRank (φ.relabel g) = quantifierRank φ :=
  quantifierRank_relabel _ φ

/-- Turning the bound variables in scope into free variables does not change the rank. -/
@[simp] theorem quantifierRank_toFormula {k : ℕ} (φ : L.BoundedFormula α k) :
    quantifierRank φ.toFormula = quantifierRank φ := by
  induction φ with
  | falsum => rfl
  | equal => exact quantifierRank_equal _ _
  | rel => exact quantifierRank_rel _ _
  | imp _ _ ih₁ ih₂ =>
    rw [BoundedFormula.toFormula, quantifierRank_imp, quantifierRank_imp, ih₁, ih₂]
  | all _ ih =>
    rw [BoundedFormula.toFormula, quantifierRank_all, quantifierRank_all, quantifierRank_relabel,
      ih]

end Cslib.Logic.FO
