/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
public import CslibFrontier.Logics.Propositional.Resolution.Restrict
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum

/-!
# General CNF variable restriction and branching model counts

This module develops the semantic, satisfiability, size, occurrence, and model-counting properties
of single-variable restriction (`Cslib.Logic.PL.CNF.restrict` from `Resolution.lean`),
list-ordered partial-assignment restriction (`Cslib.Logic.PL.CNF.restrictList`), and partial-map
restriction (`Cslib.Logic.PL.CNF.restrictBy`).

## Main definitions

* `Cslib.Logic.PL.CNF.restrictModelsEquiv`: explicit bijection between satisfying assignments of
  a restricted formula `φ.restrict v b` over `declared.erase v` and satisfying assignments of `φ`
  over `declared` fixing `v ↦ b`.
* `Cslib.Logic.PL.CNF.modelsSplitEquiv`: disjoint sum splitting declared models of `φ` across
  `φ.restrict v false` and `φ.restrict v true`.
* `Cslib.Logic.PL.CNF.restrictList`: iterated restriction along a list of literals.

## Main results

* `Cslib.Logic.PL.CNF.eval_restrict`: exact evaluation identity
  `(φ.restrict v b).eval σ = φ.eval (Function.update σ v b)`.
* `Cslib.Logic.PL.CNF.satisfiable_restrict_iff`, `Cslib.Logic.PL.CNF.satisfiable_iff_restrict`:
  satisfiability characterization and binary branching split.
* `Cslib.Logic.PL.CNF.modelCountOn_eq_add_restrict`,
  `Cslib.Logic.PL.CNF.modelCount_eq_add_restrict_of_mem_vars`: additive branching laws for both
  declared-universe and occurring-variable model counts.
* `Cslib.Logic.PL.CNF.length_restrict_le`, `Cslib.Logic.PL.CNF.numVars_restrict_lt`,
  `Cslib.Logic.PL.CNF.occurrences_restrict_self`, `Cslib.Logic.PL.CNF.occurrences_restrict_le`:
  formula length, variable count, and literal-occurrence bounds under restriction.
* `Cslib.Logic.PL.CNF.eval_restrictList`, `Cslib.Logic.PL.CNF.satisfiable_restrictBy_iff`:
  iterated and partial-map restriction properties.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### Single-variable clause and formula restriction -/

/-- Filtering `(v, !b)` out of a clause that does not contain `(v, b)` computes evaluation under
`Function.update σ v b`. -/
theorem Clause.eval_filter_ne_neg (σ : V → Bool) {c : Clause V} {v : V} {b : Bool}
    (hc : (v, b) ∉ c) :
    Clause.eval σ (c.filter (· ≠ (v, !b))) = c.eval (Function.update σ v b) := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨l, hl, hσ⟩
    obtain ⟨hlc, hne⟩ := List.mem_filter.mp hl
    have hlv : l.1 ≠ v := by
      intro heq
      rcases l with ⟨u, p⟩
      simp only at heq
      subst heq
      cases p <;> cases b <;> simp_all
    refine ⟨l, hlc, ?_⟩
    simpa [Function.update, hlv] using hσ
  · rintro ⟨l, hlc, hσ⟩
    have hlv : l.1 ≠ v := by
      intro heq
      rcases l with ⟨u, p⟩
      simp only at heq
      subst heq
      simp only [Function.update_self] at hσ
      subst hσ
      exact hc hlc
    refine ⟨l, List.mem_filter.mpr ⟨hlc, ?_⟩, ?_⟩
    · simp only [decide_eq_true_iff, ne_eq, Prod.ext_iff, not_and]
      exact fun h => absurd h hlv
    · simpa [Function.update, hlv] using hσ

namespace CNF

/-- Evaluating a single-variable restriction `φ.restrict v b` at `σ` equals evaluating `φ` at
`Function.update σ v b`. -/
@[simp] theorem eval_restrict (φ : CNF V) (v : V) (b : Bool) (σ : V → Bool) :
    (φ.restrict v b).eval σ = φ.eval (Function.update σ v b) := by
  rw [Bool.eq_iff_iff]
  constructor
  · exact CNF.eval_update_of_eval_restrict
  · rw [CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
    intro h c' hc'
    obtain ⟨c, hc, hmem, rfl⟩ := CNF.mem_restrict.mp hc'
    rw [Clause.eval_filter_ne_neg σ hmem]
    exact h c hc

/-- When `σ v = b`, evaluating `φ.restrict v b` at `σ` agrees with evaluating `φ` at `σ`. -/
theorem eval_restrict_of_eq {φ : CNF V} {v : V} {b : Bool} {σ : V → Bool} (hσ : σ v = b) :
    (φ.restrict v b).eval σ = φ.eval σ := by
  rw [eval_restrict, Function.update_eq_self_iff.mpr hσ.symm]

/-- Restricting on a variable that does not occur in `φ` leaves `φ` unchanged. -/
theorem restrict_eq_self_of_notMem_vars {φ : CNF V} {v : V} {b : Bool} (hv : v ∉ φ.vars) :
    φ.restrict v b = φ := by
  have hcl : ∀ c ∈ φ, (v, b) ∉ c ∧ c.filter (· ≠ (v, !b)) = c := by
    intro c hc
    refine ⟨fun hmem => hv (mem_vars.mpr ⟨c, hc, b, hmem⟩), ?_⟩
    exact List.filter_eq_self.mpr fun l hl => by
      simp only [decide_eq_true_iff, ne_eq]
      rintro rfl
      exact hv (mem_vars.mpr ⟨c, hc, !b, hl⟩)
  unfold CNF.restrict
  have hf : φ.filter (fun c => decide ((v, b) ∉ c)) = φ :=
    List.filter_eq_self.mpr fun c hc => decide_eq_true (hcl c hc).1
  rw [hf]
  have hmap : φ.map (List.filter fun x => decide (x ≠ (v, !b))) = φ.map id :=
    List.map_congr_left fun c hc => (hcl c hc).2
  simpa using hmap

/-- The restricted variable does not occur in `φ.restrict v b`. -/
theorem notMem_vars_restrict (φ : CNF V) (v : V) (b : Bool) :
    v ∉ (φ.restrict v b).vars := by
  intro hv
  obtain ⟨c, hc, p, hp⟩ := mem_vars.mp hv
  exact fst_ne_of_mem_restrict hc hp rfl

/-- Restricting a variable never increases the number of distinct occurring variables. -/
theorem numVars_restrict_le (φ : CNF V) (v : V) (b : Bool) :
    (φ.restrict v b).numVars ≤ φ.numVars := by
  exact Finset.card_le_card fun u hu =>
    Finset.mem_of_mem_erase (vars_restrict_subset hu)

/-- Restricting an occurring variable strictly reduces `CNF.numVars`. -/
theorem numVars_restrict_lt {φ : CNF V} {v : V} {b : Bool} (hv : v ∈ φ.vars) :
    (φ.restrict v b).numVars < φ.numVars := by
  have hsub : (φ.restrict v b).vars.toFinset ⊆ φ.vars.toFinset.erase v := vars_restrict_subset
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem (List.mem_toFinset.mpr hv))

/-- Every clause of `φ.restrict v b` is a sublist-literal subset of some clause of `φ` of at most
the same length. -/
theorem exists_clause_subset_of_mem_restrict {φ : CNF V} {v : V} {b : Bool} {c' : Clause V}
    (hc' : c' ∈ φ.restrict v b) :
    ∃ c ∈ φ, (∀ l ∈ c', l ∈ c) ∧ c'.toFinset ⊆ c.toFinset ∧ c'.length ≤ c.length := by
  obtain ⟨c, hc, -, rfl⟩ := mem_restrict.mp hc'
  refine ⟨c, hc, fun l hl => (List.mem_filter.mp hl).1, ?_, List.length_filter_le _ _⟩
  intro l hl
  exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hl)).1

/-- Restricting never increases the number of clauses. -/
theorem length_restrict_le (φ : CNF V) (v : V) (b : Bool) :
    (φ.restrict v b).length ≤ φ.length := by
  unfold CNF.restrict
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- If some clause of `φ` contains `(v, b)`, restricting `v` to `b` strictly decreases the number
of clauses. -/
theorem length_restrict_lt {φ : CNF V} {v : V} {b : Bool} {c : Clause V}
    (hc : c ∈ φ) (hl : (v, b) ∈ c) :
    (φ.restrict v b).length < φ.length := by
  unfold CNF.restrict
  rw [List.length_map, List.length_filter_lt_length_iff_exists]
  exact ⟨c, hc, fun h => (of_decide_eq_true h) hl⟩

/-- Restricting on `v` removes all occurrences of `v`. -/
@[simp] theorem occurrences_restrict_self (φ : CNF V) (v : V) (b : Bool) :
    (φ.restrict v b).occurrences v = 0 := by
  unfold CNF.occurrences
  rw [List.countP_eq_zero]
  intro c hc
  simp only [decide_eq_true_eq, not_exists, not_and]
  intro l hl
  exact fst_ne_of_mem_restrict hc hl

/-- Restricting on `v` does not increase the number of clauses mentioning any variable `u`. -/
theorem occurrences_restrict_le (φ : CNF V) (v u : V) (b : Bool) :
    (φ.restrict v b).occurrences u ≤ φ.occurrences u := by
  induction φ with
  | nil => simp [CNF.restrict]
  | cons c ψ ih =>
    unfold CNF.restrict at ih ⊢
    by_cases hmem : (v, b) ∈ c
    · have hf : decide ((v, b) ∉ c) = false := decide_eq_false (by simp [hmem])
      rw [List.filter_cons_of_neg (by simp [hf])]
      exact ih.trans (by
        unfold CNF.occurrences
        rw [List.countP_cons]
        omega)
    · have hf : decide ((v, b) ∉ c) = true := decide_eq_true hmem
      rw [List.filter_cons_of_pos (by simp [hf]), List.map_cons]
      unfold CNF.occurrences at ih ⊢
      rw [List.countP_cons, List.countP_cons]
      split_ifs with h₁ h₂
      · exact Nat.succ_le_succ ih
      · exfalso
        obtain ⟨l, hl, hlu⟩ := decide_eq_true_iff.mp h₁
        exact (decide_eq_true_iff.not.mp h₂) ⟨l, (List.mem_filter.mp hl).1, hlu⟩
      · exact ih.trans (Nat.le_succ _)
      · exact ih

/-! ### Satisfiability and assignment bijections -/

/-- `φ.restrict v b` is satisfiable iff `φ` has a satisfying assignment mapping `v` to `b`. -/
theorem satisfiable_restrict_iff (φ : CNF V) (v : V) (b : Bool) :
    (φ.restrict v b).Satisfiable ↔ ∃ σ : V → Bool, σ v = b ∧ φ.eval σ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [eval_restrict] at hσ
    exact ⟨Function.update σ v b, Function.update_self v b σ, hσ⟩
  · rintro ⟨σ, hσv, hσ⟩
    refine ⟨σ, ?_⟩
    rw [eval_restrict_of_eq hσv]
    exact hσ

/-- Binary branching characterization of CNF satisfiability. -/
theorem satisfiable_iff_restrict (φ : CNF V) (v : V) :
    φ.Satisfiable ↔ (φ.restrict v false).Satisfiable ∨ (φ.restrict v true).Satisfiable := by
  rw [satisfiable_restrict_iff, satisfiable_restrict_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    cases hb : σ v
    · exact Or.inl ⟨σ, hb, hσ⟩
    · exact Or.inr ⟨σ, hb, hσ⟩
  · rintro (⟨σ, -, hσ⟩ | ⟨σ, -, hσ⟩) <;> exact ⟨σ, hσ⟩

/-- Extend a restricted assignment on `declared.erase v` to `declared` by fixing `v ↦ b`. -/
private def extendAt (declared : Finset V) (v : V) (b : Bool)
    (σ : ↥(declared.erase v) → Bool) : ↥declared → Bool :=
  fun u => if h : u.1 = v then b else σ ⟨u.1, Finset.mem_erase.mpr ⟨h, u.2⟩⟩

private theorem extendAt_self {declared : Finset V} (v : V) (hv : v ∈ declared) (b : Bool)
    (σ : ↥(declared.erase v) → Bool) : extendAt declared v b σ ⟨v, hv⟩ = b := by
  simp [extendAt]

private theorem eval_restrict_eq_eval_extendAt (φ : CNF V) (declared : Finset V) (v : V)
    (hv : v ∈ declared) (b : Bool) (σ : ↥(declared.erase v) → Bool) :
    (φ.restrict v b).eval (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) =
      φ.eval (fun u => if h : u ∈ declared then extendAt declared v b σ ⟨u, h⟩ else false) := by
  rw [eval_restrict]
  congr 1
  funext u
  by_cases huv : u = v
  · subst huv
    simp [Function.update, extendAt, hv]
  · simp only [Function.update, huv, ↓reduceDIte]
    by_cases hu : u ∈ declared
    · have hue : u ∈ declared.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
      simp [hu, hue, extendAt, huv]
    · have hue : u ∉ declared.erase v := fun h => hu (Finset.mem_of_mem_erase h)
      simp [hu, hue]

/-- Explicit bijection between satisfying assignments of `φ.restrict v b` on `declared.erase v` and
satisfying assignments of `φ` on `declared` that map `v` to `b`. -/
def restrictModelsEquiv (φ : CNF V) (declared : Finset V) {v : V} (hv : v ∈ declared)
    (b : Bool) :
    {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v b).eval (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) =
        true} ≃
    {τ : ↥declared → Bool //
      φ.eval (fun u => if h : u ∈ declared then τ ⟨u, h⟩ else false) = true ∧
        τ ⟨v, hv⟩ = b} where
  toFun σ :=
    ⟨extendAt declared v b σ.1,
      ⟨by rw [← eval_restrict_eq_eval_extendAt φ declared v hv b σ.1]; exact σ.2,
       extendAt_self v hv b σ.1⟩⟩
  invFun τ :=
    ⟨fun u => τ.1 ⟨u.1, Finset.mem_of_mem_erase u.2⟩, by
      have heval := eval_restrict_eq_eval_extendAt φ declared v hv b
        (fun u => τ.1 ⟨u.1, Finset.mem_of_mem_erase u.2⟩)
      have hext : extendAt declared v b (fun u => τ.1 ⟨u.1, Finset.mem_of_mem_erase u.2⟩) =
          τ.1 := by
        funext u
        by_cases huv : u.1 = v
        · have hu : u = ⟨v, hv⟩ := Subtype.ext huv
          subst hu
          simp [extendAt, τ.2.2]
        · simp [extendAt, huv]
      rw [hext] at heval
      rw [heval]
      exact τ.2.1⟩
  left_inv σ := by
    ext ⟨u, hu⟩
    have huv : u ≠ v := (Finset.mem_erase.mp hu).1
    simp [extendAt, huv]
  right_inv τ := by
    ext ⟨u, hu⟩
    by_cases huv : u = v
    · have heq : (⟨u, hu⟩ : ↥declared) = ⟨v, hv⟩ := Subtype.ext huv
      rw [heq]
      simpa [extendAt] using τ.2.2.symm
    · simp [extendAt, huv]

/-- Explicit disjoint sum equivalence splitting declared models of `φ` into those extending
`φ.restrict v false` and those extending `φ.restrict v true`. -/
def modelsSplitEquiv (φ : CNF V) (declared : Finset V) {v : V} (hv : v ∈ declared) :
    {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v false).eval
        (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) = true} ⊕
    {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v true).eval
        (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) = true} ≃
    {τ : ↥declared → Bool //
      φ.eval (fun u => if h : u ∈ declared then τ ⟨u, h⟩ else false) = true} where
  toFun
    | Sum.inl σ =>
      match restrictModelsEquiv φ declared hv false σ with
      | ⟨val, hval, _⟩ => ⟨val, hval⟩
    | Sum.inr σ =>
      match restrictModelsEquiv φ declared hv true σ with
      | ⟨val, hval, _⟩ => ⟨val, hval⟩
  invFun τ :=
    if h : τ.1 ⟨v, hv⟩ = false then
      Sum.inl ((restrictModelsEquiv φ declared hv false).symm ⟨τ.1, τ.2, h⟩)
    else
      Sum.inr ((restrictModelsEquiv φ declared hv true).symm ⟨τ.1, τ.2, by
        cases hτ : τ.1 ⟨v, hv⟩
        · exact absurd hτ h
        · rfl⟩)
  left_inv s := by
    rcases s with σ | σ
    · have hself : (restrictModelsEquiv φ declared hv false σ).1 ⟨v, hv⟩ = false :=
        (restrictModelsEquiv φ declared hv false σ).2.2
      dsimp only
      rw [dite_eq_left hself]
      congr 1
      exact (restrictModelsEquiv φ declared hv false).left_inv σ
    · have hself : (restrictModelsEquiv φ declared hv true σ).1 ⟨v, hv⟩ = true :=
        (restrictModelsEquiv φ declared hv true σ).2.2
      have hne : ¬ (restrictModelsEquiv φ declared hv true σ).1 ⟨v, hv⟩ = false := by
        simp [hself]
      dsimp only
      rw [dite_eq_right hne]
      congr 1
      exact (restrictModelsEquiv φ declared hv true).left_inv σ
  right_inv τ := by
    by_cases h : τ.1 ⟨v, hv⟩ = false
    · dsimp only
      rw [dite_eq_left h]
      dsimp only
      exact Subtype.ext (congrArg (fun x => x.1)
        ((restrictModelsEquiv φ declared hv false).right_inv ⟨τ.1, τ.2, h⟩))
    · have ht : τ.1 ⟨v, hv⟩ = true := by
        cases hv0 : τ.1 ⟨v, hv⟩
        · exact absurd hv0 h
        · rfl
      dsimp only
      rw [dite_eq_right h]
      dsimp only
      exact Subtype.ext (congrArg (fun x => x.1)
        ((restrictModelsEquiv φ declared hv true).right_inv ⟨τ.1, τ.2, ht⟩))

/-- Forward action of `restrictModelsEquiv` extends `σ` at `v` by `b`. -/
theorem restrictModelsEquiv_apply_val (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared) (b : Bool)
    (σ : {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v b).eval (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) =
        true})
    (u : ↥declared) :
    (restrictModelsEquiv φ declared hv b σ).1 u =
      if h : u.1 = v then b else σ.1 ⟨u.1, Finset.mem_erase.mpr ⟨h, u.2⟩⟩ := by
  rfl

/-- At the restricted variable `v`, `restrictModelsEquiv` yields `b`. -/
@[simp] theorem restrictModelsEquiv_apply_self (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared) (b : Bool)
    (σ : {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v b).eval (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) =
        true}) :
    (restrictModelsEquiv φ declared hv b σ).1 ⟨v, hv⟩ = b := by
  rw [restrictModelsEquiv_apply_val]
  exact dite_eq_left rfl

/-- Off the restricted variable `v`, `restrictModelsEquiv` agrees with `σ`. -/
@[simp] theorem restrictModelsEquiv_apply_ne (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared) (b : Bool)
    (σ : {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v b).eval (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) =
        true})
    {u : ↥declared} (hu : u.1 ≠ v) :
    (restrictModelsEquiv φ declared hv b σ).1 u = σ.1 ⟨u.1, Finset.mem_erase.mpr ⟨hu, u.2⟩⟩ := by
  rw [restrictModelsEquiv_apply_val]
  exact dite_eq_right hu

/-- Inverse of `restrictModelsEquiv` restricts `τ` to `declared.erase v`. -/
@[simp] theorem restrictModelsEquiv_symm_apply_val (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared) (b : Bool)
    (τ : {τ : ↥declared → Bool //
      φ.eval (fun u => if h : u ∈ declared then τ ⟨u, h⟩ else false) = true ∧ τ ⟨v, hv⟩ = b})
    (u : ↥(declared.erase v)) :
    ((restrictModelsEquiv φ declared hv b).symm τ).1 u =
      τ.1 ⟨u.1, Finset.mem_of_mem_erase u.2⟩ := by
  rfl

/-- Left branch of `modelsSplitEquiv` agrees with `restrictModelsEquiv ... false`. -/
@[simp] theorem modelsSplitEquiv_inl_val (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared)
    (σ : {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v false).eval
        (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) = true}) :
    (modelsSplitEquiv φ declared hv (Sum.inl σ)).1 =
      (restrictModelsEquiv φ declared hv false σ).1 := by
  rfl

/-- Right branch of `modelsSplitEquiv` agrees with `restrictModelsEquiv ... true`. -/
@[simp] theorem modelsSplitEquiv_inr_val (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared)
    (σ : {σ : ↥(declared.erase v) → Bool //
      (φ.restrict v true).eval
        (fun u => if h : u ∈ declared.erase v then σ ⟨u, h⟩ else false) = true}) :
    (modelsSplitEquiv φ declared hv (Sum.inr σ)).1 =
      (restrictModelsEquiv φ declared hv true σ).1 := by
  rfl

/-- Inverse of `modelsSplitEquiv` on an assignment setting `v ↦ false`. -/
theorem modelsSplitEquiv_symm_of_eq_false (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared)
    (τ : {τ : ↥declared → Bool //
      φ.eval (fun u => if h : u ∈ declared then τ ⟨u, h⟩ else false) = true})
    (h : τ.1 ⟨v, hv⟩ = false) :
    (modelsSplitEquiv φ declared hv).symm τ =
      Sum.inl ((restrictModelsEquiv φ declared hv false).symm ⟨τ.1, τ.2, h⟩) := by
  exact dite_eq_left h

/-- Inverse of `modelsSplitEquiv` on an assignment setting `v ↦ true`. -/
theorem modelsSplitEquiv_symm_of_eq_true (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∈ declared)
    (τ : {τ : ↥declared → Bool //
      φ.eval (fun u => if h : u ∈ declared then τ ⟨u, h⟩ else false) = true})
    (h : τ.1 ⟨v, hv⟩ = true) :
    (modelsSplitEquiv φ declared hv).symm τ =
      Sum.inr ((restrictModelsEquiv φ declared hv true).symm ⟨τ.1, τ.2, h⟩) := by
  have hne : τ.1 ⟨v, hv⟩ ≠ false := by simp [h]
  exact dite_eq_right hne

/-! ### Branching additivity for model counts -/

/-- Branching additivity for declared-universe model counting: restricting `v ∈ declared` splits
`modelCountOn` into the sum of `false` and `true` branches over `declared.erase v`. -/
theorem modelCountOn_eq_add_restrict (φ : CNF V) (declared : Finset V) {v : V} (hv : v ∈ declared) :
    φ.modelCountOn declared =
      (φ.restrict v false).modelCountOn (declared.erase v) +
        (φ.restrict v true).modelCountOn (declared.erase v) := by
  have hcard := Fintype.card_congr (modelsSplitEquiv φ declared hv)
  rw [Fintype.card_sum] at hcard
  simp only [Fintype.card_subtype] at hcard
  simpa [modelCountOn] using hcard.symm

/-- When every satisfying assignment of `φ` maps `v ∈ declared` to `b`, restricting `v ↦ b`
conserves `modelCountOn` onto `declared.erase v`. -/
theorem modelCountOn_eq_restrict_of_forall {φ : CNF V} {declared : Finset V} {v : V}
    (hv : v ∈ declared) {b : Bool} (hforce : ∀ σ : V → Bool, φ.eval σ = true → σ v = b) :
    φ.modelCountOn declared = (φ.restrict v b).modelCountOn (declared.erase v) := by
  have hzero : (φ.restrict v (!b)).modelCountOn (declared.erase v) = 0 := by
    rw [modelCountOn, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro σ hσ
    have heval := (Finset.mem_filter.mp hσ).2
    rw [eval_restrict] at heval
    have hbv := hforce _ heval
    rw [Function.update_self] at hbv
    cases b <;> simp at hbv
  rw [modelCountOn_eq_add_restrict φ declared hv]
  cases b
  · rw [Bool.not_false] at hzero
    simp [hzero]
  · rw [Bool.not_true] at hzero
    simp [hzero]

/-- When `v ∉ declared`, `modelCountOn` fixes `v ↦ false`, so restricting `v ↦ false` leaves
`modelCountOn` unchanged. -/
theorem modelCountOn_restrict_of_notMem (φ : CNF V) (declared : Finset V) {v : V}
    (hv : v ∉ declared) :
    (φ.restrict v false).modelCountOn declared = φ.modelCountOn declared := by
  simp only [modelCountOn]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_restrict]
  have hupd : Function.update (fun u => if h : u ∈ declared then σ ⟨u, h⟩ else false) v false =
      fun u => if h : u ∈ declared then σ ⟨u, h⟩ else false := by
    apply Function.update_eq_self_iff.mpr
    simp [hv]
  rw [hupd]

/-- Branching additivity for occurring-variable `CNF.modelCount` on an occurring variable `v`,
explicitly accounting for any other variables eliminated along each branch. -/
theorem modelCount_eq_add_restrict_of_mem_vars (φ : CNF V) {v : V} (hv : v ∈ φ.vars) :
    φ.modelCount =
      2 ^ ((φ.vars.toFinset.erase v).card - (φ.restrict v false).numVars) *
          (φ.restrict v false).modelCount +
        2 ^ ((φ.vars.toFinset.erase v).card - (φ.restrict v true).numVars) *
          (φ.restrict v true).modelCount := by
  rw [← modelCountOn_vars,
    modelCountOn_eq_add_restrict φ φ.vars.toFinset (List.mem_toFinset.mpr hv),
    modelCountOn_eq_mul_modelCount (φ.restrict v false) (φ.vars.toFinset.erase v)
      vars_restrict_subset,
    modelCountOn_eq_mul_modelCount (φ.restrict v true) (φ.vars.toFinset.erase v)
      vars_restrict_subset]

/-- Restricting a non-occurring variable leaves `CNF.modelCount` unchanged. -/
theorem modelCount_restrict_of_notMem_vars (φ : CNF V) {v : V} (hv : v ∉ φ.vars) (b : Bool) :
    (φ.restrict v b).modelCount = φ.modelCount := by
  rw [restrict_eq_self_of_notMem_vars hv]

/-! ### Iterated list restriction and partial-map restriction -/

/-- Restrict a formula sequentially along a list of literals `(v, b)`. -/
@[expose] def restrictList (φ : CNF V) (assign : List (Literal V)) : CNF V :=
  assign.foldl (fun ψ l => ψ.restrict l.1 l.2) φ

@[simp] theorem restrictList_nil (φ : CNF V) :
    φ.restrictList [] = φ := rfl

@[simp] theorem restrictList_cons (φ : CNF V) (l : Literal V) (ls : List (Literal V)) :
    φ.restrictList (l :: ls) = (φ.restrict l.1 l.2).restrictList ls := rfl

/-- Update an assignment by applying a list of literals in list order (earlier entries override
later ones, matching `CNF.restrictList`). -/
@[expose] def applyAssignList (assign : List (Literal V)) (σ : V → Bool) : V → Bool :=
  assign.foldr (fun l τ => Function.update τ l.1 l.2) σ

@[simp] theorem applyAssignList_nil (σ : V → Bool) :
    applyAssignList [] σ = σ := rfl

@[simp] theorem applyAssignList_cons (l : Literal V) (ls : List (Literal V)) (σ : V → Bool) :
    applyAssignList (l :: ls) σ = Function.update (applyAssignList ls σ) l.1 l.2 := rfl

/-- Evaluation of `φ.restrictList assign` at `σ` equals evaluation of `φ` at `applyAssignList
assign σ`. -/
theorem eval_restrictList (φ : CNF V) (assign : List (Literal V)) (σ : V → Bool) :
    (φ.restrictList assign).eval σ = φ.eval (applyAssignList assign σ) := by
  induction assign generalizing φ with
  | nil => rfl
  | cons l ls ih =>
    rw [restrictList_cons, ih, eval_restrict, applyAssignList_cons]

/-- Variables remaining in `φ.restrictList assign` occur in `φ` and not in `assign`. -/
theorem vars_restrictList_subset (φ : CNF V) (assign : List (Literal V)) :
    (φ.restrictList assign).vars.toFinset ⊆
      φ.vars.toFinset \ (assign.map Prod.fst).toFinset := by
  induction assign generalizing φ with
  | nil => simp
  | cons l ls ih =>
    intro u hu
    have hu1 := ih (φ.restrict l.1 l.2) hu
    rw [Finset.mem_sdiff] at hu1 ⊢
    have hu2 := vars_restrict_subset hu1.1
    rw [Finset.mem_erase] at hu2
    refine ⟨hu2.2, ?_⟩
    simp only [List.map_cons, List.mem_toFinset, List.mem_cons, not_or]
    exact ⟨hu2.1, by simpa using hu1.2⟩

/-- Iterated restriction does not increase the number of clauses. -/
theorem length_restrictList_le (φ : CNF V) (assign : List (Literal V)) :
    (φ.restrictList assign).length ≤ φ.length := by
  induction assign generalizing φ with
  | nil => exact le_rfl
  | cons l ls ih =>
    exact (ih (φ.restrict l.1 l.2)).trans (length_restrict_le φ l.1 l.2)

/-- Iterated restriction does not increase occurrences of any variable. -/
theorem occurrences_restrictList_le (φ : CNF V) (assign : List (Literal V)) (u : V) :
    (φ.restrictList assign).occurrences u ≤ φ.occurrences u := by
  induction assign generalizing φ with
  | nil => exact le_rfl
  | cons l ls ih =>
    exact (ih (φ.restrict l.1 l.2)).trans (occurrences_restrict_le φ l.1 u l.2)

/-- Any variable mentioned in `assign` has zero occurrences in `φ.restrictList assign`. -/
theorem occurrences_restrictList_eq_zero (φ : CNF V) (assign : List (Literal V)) {u : V}
    (hu : u ∈ assign.map Prod.fst) :
    (φ.restrictList assign).occurrences u = 0 := by
  have hnot : u ∉ (φ.restrictList assign).vars := by
    intro hmem
    have hsub := vars_restrictList_subset φ assign (List.mem_toFinset.mpr hmem)
    rw [Finset.mem_sdiff] at hsub
    exact hsub.2 (List.mem_toFinset.mpr hu)
  unfold CNF.occurrences
  rw [List.countP_eq_zero]
  intro c hc
  simp only [decide_eq_true_eq, not_exists, not_and]
  intro l hl hlu
  exact hnot (hlu ▸ mem_vars.mpr ⟨c, hc, l.2, hl⟩)

/-- If every assigned literal holds in `assign` (no conflicting assignments to the same variable),
`applyAssignList` fixes each variable to its assigned Boolean value. -/
theorem applyAssignList_eq_of_nodup {assign : List (Literal V)}
    (hnd : (assign.map Prod.fst).Nodup) (σ : V → Bool) {l : Literal V} (hl : l ∈ assign) :
    applyAssignList assign σ l.1 = l.2 := by
  induction assign with
  | nil => simp at hl
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hl with rfl | hxs
    · simp
    · have hne : l.1 ≠ x.1 := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨l, hxs, rfl⟩)
      simp [hne, ih hnd.2 hxs]

/-- Under a variable-disjoint literal list `assign`, satisfiability of `φ.restrictList assign` is
equivalent to satisfiability of `φ` extending `assign`. -/
theorem satisfiable_restrictList_iff (φ : CNF V) {assign : List (Literal V)}
    (hnd : (assign.map Prod.fst).Nodup) :
    (φ.restrictList assign).Satisfiable ↔
      ∃ σ : V → Bool, (∀ l ∈ assign, σ l.1 = l.2) ∧ φ.eval σ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [eval_restrictList] at hσ
    exact ⟨applyAssignList assign σ, fun l hl => applyAssignList_eq_of_nodup hnd σ hl, hσ⟩
  · rintro ⟨σ, hassign, hσ⟩
    refine ⟨σ, ?_⟩
    rw [eval_restrictList]
    refine (eval_congr fun v _ => ?_).trans hσ
    clear hσ
    induction assign with
    | nil => rfl
    | cons l ls ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [applyAssignList_cons]
      by_cases hv : v = l.1
      · subst hv
        simpa using (hassign l List.mem_cons_self).symm
      · rw [Function.update_of_ne hv]
        exact ih hnd.2 fun m hm => hassign m (List.mem_cons_of_mem _ hm)

omit [DecidableEq V] in
/-- Variables remaining after `CNF.restrictBy ρ` belong to `φ` and are not fixed by `ρ`. -/
theorem vars_restrictBy_subset (φ : CNF V) (ρ : V → Option Bool) :
    ∀ v ∈ (φ.restrictBy ρ).vars, v ∈ φ.vars ∧ ρ v = none := by
  intro v hv
  obtain ⟨c', hc', b, hb⟩ := mem_vars.mp hv
  obtain ⟨c, hc, -, rfl⟩ := mem_restrictBy.mp hc'
  obtain ⟨hmem, hnone⟩ := List.mem_filter.mp hb
  exact ⟨mem_vars.mpr ⟨c, hc, b, hmem⟩, decide_eq_true_eq.mp hnone⟩

omit [DecidableEq V] in
/-- Partial-map restriction `CNF.restrictBy` does not increase clause count. -/
theorem length_restrictBy_le (φ : CNF V) (ρ : V → Option Bool) :
    (φ.restrictBy ρ).length ≤ φ.length := by
  unfold CNF.restrictBy
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- `CNF.restrictBy ρ` eliminates all occurrences of variables fixed by `ρ`. -/
theorem occurrences_restrictBy_eq_zero (φ : CNF V) (ρ : V → Option Bool) {v : V}
    (hv : ρ v ≠ none) :
    (φ.restrictBy ρ).occurrences v = 0 := by
  unfold CNF.occurrences
  rw [List.countP_eq_zero]
  intro c hc
  simp only [decide_eq_true_eq, not_exists, not_and]
  intro l hl hlv
  have hmem := (vars_restrictBy_subset φ ρ v (mem_vars.mpr ⟨c, hc, l.2, hlv ▸ hl⟩)).2
  exact hv hmem

omit [DecidableEq V] in
/-- `CNF.restrictBy ρ` is satisfiable iff `φ` has a satisfying assignment extending `ρ`. -/
theorem satisfiable_restrictBy_iff (φ : CNF V) (ρ : V → Option Bool) :
    (φ.restrictBy ρ).Satisfiable ↔
      ∃ σ : V → Bool, (∀ v b, ρ v = some b → σ v = b) ∧ φ.eval σ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    let τ : V → Bool := fun v => match ρ v with | some b => b | none => σ v
    have hτ : ∀ v b, ρ v = some b → τ v = b := fun v b hb => by simp [τ, hb]
    refine ⟨τ, hτ, ?_⟩
    rw [← eval_restrictBy (φ := φ) (ρ := ρ) hτ]
    refine (eval_congr fun v hv => ?_).trans hσ
    have hnone := (vars_restrictBy_subset φ ρ v hv).2
    simp [τ, hnone]
  · rintro ⟨σ, hσρ, hσ⟩
    refine ⟨σ, ?_⟩
    rw [eval_restrictBy hσρ]
    exact hσ

end CNF

end Cslib.Logic.PL
