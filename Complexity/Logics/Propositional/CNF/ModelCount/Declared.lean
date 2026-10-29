/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount.Relabel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

/-!
# Counting assignments on a declared set of variables

`CNF.modelCountOn` counts assignments of a supplied finite set, extending them by `false` outside
that set. When the set contains all occurring variables, each unused variable contributes a free
Boolean choice. The original occurring-variable `CNF.modelCount` is unchanged and is recovered by
declaring exactly the occurring variables.

Renaming by positions in `distinctVars` gives dense natural labels below `numVars`. This differs
from the existing `compact`, whose first literal-occurrence positions can have gaps. The dense
renaming preserves literal order, clause lengths and the occurring-variable count.

These are elementary semantic transport facts for the declared-variable convention of the native
counting development in #1226. They do not implement a counting algorithm or assert a runtime bound.

## Main definitions

* `Cslib.Logic.PL.CNF.modelCountOn`: count assignments on a declared finite set.
* `Cslib.Logic.PL.CNF.validDeclaredInput`: guard for clause widths `≤ k` and variables `< N`.
* `Cslib.Logic.PL.CNF.normalizeDeclaredLeaf`: right-shift a declared count by unused variables.

## Main results

* `Cslib.Logic.PL.CNF.modelCountOn_vars`: recover the original occurring-variable count.
* `Cslib.Logic.PL.CNF.modelCountOn_eq_mul_modelCount`: unused variables give independent choices.
* `Cslib.Logic.PL.CNF.vars_dense_relabel`: dense renaming has exactly the expected variable range.
* `Cslib.Logic.PL.CNF.modelCountOn_dense_relabel`: dense renaming preserves the declared count.
* `Cslib.Logic.PL.CNF.validDeclaredInput_eq_true_iff`: width and `Finset.range N` equivalence.
* `Cslib.Logic.PL.CNF.normalizeDeclaredLeaf_eq_div`, `normalizeDeclaredLeaf_eq_modelCount`,
  `normalizeDeclaredLeaf_le_two_pow_numVars`: division form, `modelCount`, and `2 ^ numVars` bound.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

/-- Count assignments of `declared` that satisfy the existing CNF evaluation, extending by `false`
outside `declared`. To interpret this as a declared-variable formula, require that every occurring
variable belongs to `declared`. No inhabitedness of the variable type is needed. -/
def modelCountOn (φ : CNF V) (declared : Finset V) : ℕ :=
  (Finset.univ.filter fun σ : declared → Bool =>
    φ.eval (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false) = true).card

/-- Declaring exactly the occurring variables recovers the existing model count. -/
@[simp]
theorem modelCountOn_vars (φ : CNF V) :
    φ.modelCountOn φ.vars.toFinset = φ.modelCount := rfl

/-- Every declared variable is free in an empty formula, including when the declared set is empty.
-/
@[simp]
theorem modelCountOn_nil (declared : Finset V) :
    modelCountOn ([] : CNF V) declared = 2 ^ declared.card := by
  simp [modelCountOn]

/-- An empty clause rules out every assignment, regardless of the declared variables. -/
theorem modelCountOn_eq_zero_of_nil_mem {φ : CNF V} (h : [] ∈ φ) (declared : Finset V) :
    φ.modelCountOn declared = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have hsat := (Finset.mem_filter.mp hσ).2
  have := (CNF.eval_eq_true_iff _ _).mp hsat [] h
  simp at this

/-- If the declared set contains all occurring variables, its unused variables independently
contribute two choices each. The containment premise is essential because assignments outside the
declared set are extended by `false`. -/
theorem modelCountOn_eq_mul_modelCount (φ : CNF V) (declared : Finset V)
    (hvars : φ.vars.toFinset ⊆ declared) :
    φ.modelCountOn declared = 2 ^ (declared.card - φ.numVars) * φ.modelCount := by
  classical
  let used := φ.vars.toFinset
  let p : declared → Prop := fun v => v.1 ∈ used
  let usedEquiv : {v : declared // p v} ≃ used :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun v => ⟨⟨v.1, hvars v.2⟩, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let split : (declared → Bool) ≃ (used → Bool) × ({v : declared // ¬p v} → Bool) :=
    (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).trans
      (Equiv.prodCongr (Equiv.arrowCongr usedEquiv (Equiv.refl Bool)) (Equiv.refl _))
  let good : (used → Bool) → Prop := fun τ => φ.eval (φ.extendAssignment τ) = true
  have heval (σ : declared → Bool) :
      φ.eval (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false) =
        φ.eval (φ.extendAssignment (split σ).1) := by
    apply CNF.eval_congr
    intro v hv
    have hu : v ∈ used := List.mem_toFinset.mpr hv
    simp only [dite_eq_left (hvars hu), extendAssignment_of_mem _ hv]
    rfl
  let e : {σ : declared → Bool //
      φ.eval (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false) = true} ≃
      {τ : used → Bool // good τ} × ({v : declared // ¬p v} → Bool) :=
    { toFun := fun σ => (⟨(split σ.1).1, by
        change φ.eval (φ.extendAssignment (split σ.1).1) = true
        rw [← heval]
        exact σ.2⟩, (split σ.1).2)
      invFun := fun τ => ⟨split.symm (τ.1.1, τ.2), by
        rw [heval]
        simpa only [Equiv.apply_symm_apply] using τ.1.2⟩
      left_inv := fun σ => Subtype.ext (split.symm_apply_apply σ.1)
      right_inv := fun τ => by
        simp only [Equiv.apply_symm_apply] }
  have hused : Fintype.card {v : declared // p v} = used.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr usedEquiv
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, hused] at hcard
  simpa only [Fintype.card_subtype, good, modelCountOn, modelCount,
    Fintype.card_coe, used, numVars, Nat.mul_comm] using hcard

/-- Renaming by the duplicate-free variable list uses every index below `numVars`, without gaps.
The original clause and literal order is retained. -/
theorem vars_dense_relabel (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).vars.toFinset = Finset.range φ.numVars := by
  rw [vars_relabel]
  have hmap : (φ.vars.map φ.distinctVars.idxOf).toFinset =
      φ.vars.toFinset.image φ.distinctVars.idxOf := by
    ext i
    simp
  rw [hmap]
  have hinj : Set.InjOn φ.distinctVars.idxOf {v | v ∈ φ.vars.toFinset} := by
    intro v hv w hw h
    exact (List.idxOf_inj (mem_distinctVars.mpr (List.mem_toFinset.mp hv))).mp h
  have hsub : φ.vars.toFinset.image φ.distinctVars.idxOf ⊆ Finset.range φ.numVars := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_range.mpr
    rw [← length_distinctVars]
    exact List.idxOf_lt_length_iff.mpr (mem_distinctVars.mpr (List.mem_toFinset.mp hv))
  apply Finset.eq_of_subset_of_card_le hsub
  simpa only [Finset.card_range, numVars] using
    (Finset.card_image_of_injOn (s := φ.vars.toFinset) (f := φ.distinctVars.idxOf) hinj).ge

/-- Dense natural relabeling preserves the occurring-variable model count. -/
theorem modelCount_dense_relabel (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).modelCount = φ.modelCount :=
  modelCount_relabel_of_injOn φ fun _ hv _ _ h =>
    (List.idxOf_inj (mem_distinctVars.mpr hv)).mp h

/-- Dense natural relabeling gives the original count on exactly `numVars` declared variables.
This includes the empty formula without requiring a total map from `V` into `Fin 0`. -/
theorem modelCountOn_dense_relabel (φ : CNF V) :
    (φ.relabel φ.distinctVars.idxOf).modelCountOn (Finset.range φ.numVars) = φ.modelCount := by
  rw [← vars_dense_relabel φ, modelCountOn_vars, modelCount_dense_relabel]

/-- Guard checking that every clause of `φ` has width `≤ k` and every variable lies in `< N`. -/
def validDeclaredInput (k N : ℕ) (φ : CNF ℕ) : Bool :=
  (φ.all fun c => decide (c.length ≤ k)) && (φ.vars.all fun v => decide (v < N))

theorem validDeclaredInput_eq_true_iff {k N : ℕ} {φ : CNF ℕ} :
    validDeclaredInput k N φ = true ↔
      (∀ c ∈ φ, c.length ≤ k) ∧ φ.vars.toFinset ⊆ Finset.range N := by
  simp only [validDeclaredInput, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact and_congr_right' ⟨fun h _ hv => Finset.mem_range.mpr (h _ (List.mem_toFinset.mp hv)),
    fun h _ hv => Finset.mem_range.mp (h (List.mem_toFinset.mpr hv))⟩

/-- Right-shift normalization converting a declared-range count `ψ.modelCountOn (Finset.range N)`
into `ψ.modelCount` (`= h (p, ψ) >>> (NOf p - ψ.distinctVars.length)`). -/
def normalizeDeclaredLeaf {P : Type*} (NOf : P → ℕ) (h : P × CNF ℕ → ℕ) (x : P × CNF ℕ) : ℕ :=
  h x >>> (NOf x.1 - x.2.distinctVars.length)

theorem normalizeDeclaredLeaf_eq_div {P : Type*} (NOf : P → ℕ) (h : P × CNF ℕ → ℕ) (x : P × CNF ℕ) :
    normalizeDeclaredLeaf NOf h x = h x / 2 ^ (NOf x.1 - x.2.numVars) := by
  rw [normalizeDeclaredLeaf, Nat.shiftRight_eq_div_pow, length_distinctVars]

/-- When `ψ`'s variables lie in `Finset.range (NOf p)` and `h (p, ψ)` equals the declared-range
count `ψ.modelCountOn (Finset.range (NOf p))`, `normalizeDeclaredLeaf` recovers `ψ.modelCount`. -/
theorem normalizeDeclaredLeaf_eq_modelCount {P : Type*} {NOf : P → ℕ} {h : P × CNF ℕ → ℕ} {p : P}
    {ψ : CNF ℕ} (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hh : h (p, ψ) = ψ.modelCountOn (Finset.range (NOf p))) :
    normalizeDeclaredLeaf NOf h (p, ψ) = ψ.modelCount := by
  rw [normalizeDeclaredLeaf_eq_div, hh, modelCountOn_eq_mul_modelCount ψ _ hsub, Finset.card_range,
    Nat.mul_div_right _ (Nat.two_pow_pos _)]

/-- When `ψ`'s variables lie in `Finset.range (NOf p)` and `h (p, ψ) ≤ 2 ^ NOf p`,
`normalizeDeclaredLeaf NOf h (p, ψ)` is at most `2 ^ ψ.numVars`. -/
theorem normalizeDeclaredLeaf_le_two_pow_numVars {P : Type*} {NOf : P → ℕ} {h : P × CNF ℕ → ℕ}
    {p : P} {ψ : CNF ℕ} (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hh : h (p, ψ) ≤ 2 ^ NOf p) :
    normalizeDeclaredLeaf NOf h (p, ψ) ≤ 2 ^ ψ.numVars := by
  rw [normalizeDeclaredLeaf_eq_div]
  have hle : ψ.numVars ≤ NOf p := by
    simpa only [numVars, Finset.card_range] using Finset.card_le_card hsub
  exact Nat.div_le_of_le_mul (hh.trans (by rw [← pow_add, Nat.sub_add_cancel hle]))

end Cslib.Logic.PL.CNF
