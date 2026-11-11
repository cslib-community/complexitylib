/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
public import Std.Sat.CNF
import Mathlib.Data.Fintype.Card

/-!
# Bridge to `Std.Sat.CNF`

This module connects cslib's list-based conjunctive normal form (`Cslib.Logic.PL.CNF`) to Lean's
array-backed `Std.Sat.CNF`, `Std.Sat.CNF.relabelFin`, `Std.Sat.CNF.dimacs`, and finite-variable
`Std.Sat.CNF (Fin n)` formulas.

Because `Std.Sat.CNF.Clause` wraps its literal list cleanly via `ofLiterals` and `literals`, the
clause and formula conversions `toStdSat` and `ofStdSat` form exact bijections preserving
evaluation, satisfiability, unsatisfiability, variable occurrences, relabeling, and finite model
counts (`CNF.modelCountOn` and `CNF.modelCount`).

## Main definitions

* `Cslib.Logic.PL.Clause.toStdSat`, `Cslib.Logic.PL.Clause.ofStdSat`,
  `Cslib.Logic.PL.Clause.equivStdSat`: bijection between list clauses and `Std.Sat.CNF.Clause`.
* `Cslib.Logic.PL.CNF.toStdSat`, `Cslib.Logic.PL.CNF.ofStdSat`,
  `Cslib.Logic.PL.CNF.equivStdSat`: exact equivalence between `CNF` formulas and `Std.Sat.CNF`.

## Main results

* `Cslib.Logic.PL.CNF.eval_toStdSat`, `Cslib.Logic.PL.CNF.eval_ofStdSat`: evaluation agreement.
* `Cslib.Logic.PL.CNF.unsat_toStdSat_iff`, `Cslib.Logic.PL.CNF.satisfiable_ofStdSat_iff`:
  satisfiability and unsatisfiability correspondence, including `Std.Sat.CNF.relabelFin`.
* `Cslib.Logic.PL.CNF.relabel_toStdSat`, `Cslib.Logic.PL.CNF.relabel_ofStdSat`: compatibility with
  variable relabeling.
* `Cslib.Logic.PL.CNF.modelCountOn_ofStdSat_univ`,
  `Cslib.Logic.PL.CNF.card_sat_eq_two_pow_mul_modelCount`: model-count correspondence for
  `Std.Sat.CNF (Fin n)` with both declared-universe counting (`Finset.univ`, `Finset.range n`)
  and occurring-variable counting (`CNF.modelCount`).
-/

public section

namespace Cslib.Logic.PL

variable {α β : Type*}

/-! ### Conversions between list clauses/formulas and `Std.Sat.CNF` -/

/-- Convert a list clause to a `Std.Sat.CNF.Clause`. -/
@[expose] def Clause.toStdSat (c : Clause α) : Std.Sat.CNF.Clause α :=
  Std.Sat.CNF.Clause.ofLiterals c

/-- Convert a `Std.Sat.CNF.Clause` to a list clause by extracting its literals. -/
@[expose] def Clause.ofStdSat (c : Std.Sat.CNF.Clause α) : Clause α :=
  c.literals

@[simp] theorem Clause.ofStdSat_toStdSat (c : Clause α) :
    Clause.ofStdSat (Clause.toStdSat c) = c := by
  simp [Clause.ofStdSat, Clause.toStdSat]

@[simp] theorem Clause.toStdSat_ofStdSat (c : Std.Sat.CNF.Clause α) :
    Clause.toStdSat (Clause.ofStdSat c) = c := by
  simp [Clause.toStdSat, Clause.ofStdSat]

/-- List clauses and `Std.Sat.CNF.Clause` are in exact bijection. -/
@[expose] def Clause.equivStdSat : Clause α ≃ Std.Sat.CNF.Clause α where
  toFun := Clause.toStdSat
  invFun := Clause.ofStdSat
  left_inv := Clause.ofStdSat_toStdSat
  right_inv := Clause.toStdSat_ofStdSat

@[simp] theorem Clause.equivStdSat_apply (c : Clause α) :
    Clause.equivStdSat c = c.toStdSat := rfl

@[simp] theorem Clause.equivStdSat_symm_apply (c : Std.Sat.CNF.Clause α) :
    Clause.equivStdSat.symm c = Clause.ofStdSat c := rfl

@[simp] theorem Clause.mem_toStdSat {c : Clause α} {l : Literal α} :
    l ∈ c.toStdSat ↔ l ∈ c := by
  rw [← Std.Sat.CNF.Clause.mem_literals_iff, Clause.toStdSat,
    Std.Sat.CNF.Clause.literals_ofLiterals]

@[simp] theorem Clause.mem_ofStdSat {c : Std.Sat.CNF.Clause α} {l : Literal α} :
    l ∈ Clause.ofStdSat c ↔ l ∈ c :=
  Std.Sat.CNF.Clause.mem_literals_iff

/-- Convert a list-based CNF formula to a `Std.Sat.CNF`. -/
@[expose] def CNF.toStdSat (φ : CNF α) : Std.Sat.CNF α :=
  ⟨(φ.map Clause.toStdSat).toArray⟩

/-- Convert a `Std.Sat.CNF` formula to a list-based `CNF`. -/
@[expose] def CNF.ofStdSat (f : Std.Sat.CNF α) : CNF α :=
  f.clauses.toList.map Clause.ofStdSat

@[simp] theorem CNF.ofStdSat_toStdSat (φ : CNF α) :
    CNF.ofStdSat (CNF.toStdSat φ) = φ := by
  change ((φ.map Clause.toStdSat).map Clause.ofStdSat) = φ
  simp [List.map_map, Function.comp_def]

@[simp] theorem CNF.toStdSat_ofStdSat (f : Std.Sat.CNF α) :
    CNF.toStdSat (CNF.ofStdSat f) = f := by
  rcases f with ⟨clauses⟩
  simp only [CNF.toStdSat, CNF.ofStdSat, List.map_map, Function.comp_def,
    Clause.toStdSat_ofStdSat, List.map_id', Array.toArray_toList]

/-- List CNF formulas and `Std.Sat.CNF` are in exact bijection. -/
@[expose] def CNF.equivStdSat : CNF α ≃ Std.Sat.CNF α where
  toFun := CNF.toStdSat
  invFun := CNF.ofStdSat
  left_inv := CNF.ofStdSat_toStdSat
  right_inv := CNF.toStdSat_ofStdSat

@[simp] theorem CNF.equivStdSat_apply (φ : CNF α) :
    CNF.equivStdSat φ = φ.toStdSat := rfl

@[simp] theorem CNF.equivStdSat_symm_apply (f : Std.Sat.CNF α) :
    CNF.equivStdSat.symm f = CNF.ofStdSat f := rfl

@[simp] theorem CNF.mem_toStdSat {φ : CNF α} {c : Std.Sat.CNF.Clause α} :
    c ∈ φ.toStdSat ↔ Clause.ofStdSat c ∈ φ := by
  simp only [Std.Sat.CNF.Internal.mem_iff, CNF.toStdSat, List.mem_toArray, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa using hd
  · intro h
    exact ⟨Clause.ofStdSat c, h, Clause.toStdSat_ofStdSat c⟩

@[simp] theorem CNF.mem_ofStdSat {f : Std.Sat.CNF α} {c : Clause α} :
    c ∈ CNF.ofStdSat f ↔ Clause.toStdSat c ∈ f := by
  simp only [CNF.ofStdSat, List.mem_map, Array.mem_toList_iff,
    Std.Sat.CNF.Internal.mem_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa using hd
  · intro h
    exact ⟨Clause.toStdSat c, h, Clause.ofStdSat_toStdSat c⟩

/-! ### Evaluation, satisfiability, and variable occurrences -/

/-- Evaluation of `Clause.toStdSat` agrees with `Clause.eval`. -/
@[simp] theorem Clause.eval_toStdSat (σ : α → Bool) (c : Clause α) :
    (Clause.toStdSat c).eval σ = c.eval σ := by
  rw [Bool.eq_iff_iff, ← Std.Sat.CNF.Clause.sat_def, Std.Sat.CNF.Clause.sat_iff_exists_mem_eq,
    Clause.eval_eq_true_iff]
  simp

/-- Evaluation of `Clause.ofStdSat` agrees with `Std.Sat.CNF.Clause.eval`. -/
@[simp] theorem Clause.eval_ofStdSat (σ : α → Bool) (c : Std.Sat.CNF.Clause α) :
    (Clause.ofStdSat c).eval σ = c.eval σ := by
  rw [← Clause.eval_toStdSat, Clause.toStdSat_ofStdSat]

/-- A `Clause` is satisfied in `Std.Sat.CNF` iff it evaluates to `true`. -/
theorem Clause.sat_toStdSat_iff (σ : α → Bool) (c : Clause α) :
    Std.Sat.CNF.Clause.Sat σ c.toStdSat ↔ c.eval σ = true := by
  simp [Std.Sat.CNF.Clause.sat_def]

/-- Evaluation of `CNF.toStdSat` agrees with `CNF.eval`. -/
@[simp] theorem CNF.eval_toStdSat (σ : α → Bool) (φ : CNF α) :
    φ.toStdSat.eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, ← Std.Sat.CNF.sat_def, Std.Sat.CNF.sat_iff_all_mem_sat,
    CNF.eval_eq_true_iff]
  constructor
  · intro h c hc
    have hsat := h (Clause.toStdSat c) (CNF.mem_toStdSat.mpr (by simpa using hc))
    simpa [Clause.sat_toStdSat_iff] using hsat
  · intro h c hc
    have hc' : Clause.ofStdSat c ∈ φ := CNF.mem_toStdSat.mp hc
    simpa [Std.Sat.CNF.Clause.sat_def] using h _ hc'

/-- Evaluation of `CNF.ofStdSat` agrees with `Std.Sat.CNF.eval`. -/
@[simp] theorem CNF.eval_ofStdSat (σ : α → Bool) (f : Std.Sat.CNF α) :
    (CNF.ofStdSat f).eval σ = f.eval σ := by
  rw [← CNF.eval_toStdSat, CNF.toStdSat_ofStdSat]

/-- `CNF.toStdSat` is `Std.Sat.CNF.Sat` iff `CNF.eval` is `true`. -/
theorem CNF.sat_toStdSat_iff (σ : α → Bool) (φ : CNF α) :
    φ.toStdSat.Sat σ ↔ φ.eval σ = true := by
  simp [Std.Sat.CNF.sat_def]

/-- `CNF.Satisfiable` holds iff `φ.toStdSat` has a satisfying assignment. -/
theorem CNF.satisfiable_iff_exists_sat_toStdSat (φ : CNF α) :
    φ.Satisfiable ↔ ∃ σ : α → Bool, φ.toStdSat.Sat σ := by
  simp [CNF.Satisfiable, CNF.sat_toStdSat_iff]

/-- `CNF.toStdSat` is `Std.Sat.CNF.Unsat` iff `¬ φ.Satisfiable`. -/
theorem CNF.unsat_toStdSat_iff (φ : CNF α) :
    φ.toStdSat.Unsat ↔ ¬φ.Satisfiable := by
  rw [Std.Sat.CNF.unsat_iff_not_sat, CNF.Satisfiable]
  simp [CNF.sat_toStdSat_iff]

/-- A `Std.Sat.CNF` is unsatisfiable iff its `ofStdSat` conversion is not satisfiable. -/
theorem CNF.unsat_iff_not_satisfiable_ofStdSat (f : Std.Sat.CNF α) :
    f.Unsat ↔ ¬(CNF.ofStdSat f).Satisfiable := by
  rw [← CNF.unsat_toStdSat_iff, CNF.toStdSat_ofStdSat]

/-- A `Std.Sat.CNF` is not `Unsat` iff `ofStdSat f` is satisfiable. -/
theorem CNF.satisfiable_ofStdSat_iff (f : Std.Sat.CNF α) :
    (CNF.ofStdSat f).Satisfiable ↔ ¬f.Unsat := by
  rw [CNF.unsat_iff_not_satisfiable_ofStdSat, not_not]

/-- A `Std.Sat.CNF` has a `Sat` assignment iff `ofStdSat f` is satisfiable. -/
theorem CNF.satisfiable_ofStdSat_iff_exists_sat (f : Std.Sat.CNF α) :
    (CNF.ofStdSat f).Satisfiable ↔ ∃ σ : α → Bool, f.Sat σ := by
  simp [CNF.Satisfiable, Std.Sat.CNF.sat_def]

/-- Variable membership in `Clause.toStdSat` matches `Clause` literal membership. -/
theorem Clause.varMem_toStdSat_iff (c : Clause α) (v : α) :
    Std.Sat.CNF.Clause.VarMem v c.toStdSat ↔ ∃ b, (v, b) ∈ c := by
  rw [Std.Sat.CNF.Clause.VarMem_iff_exists_mem_literals, Clause.toStdSat,
    Std.Sat.CNF.Clause.literals_ofLiterals]

/-- Variable membership in `CNF.toStdSat` matches `CNF.mem_vars`. -/
theorem CNF.varMem_toStdSat_iff (φ : CNF α) (v : α) :
    Std.Sat.CNF.VarMem v φ.toStdSat ↔ v ∈ φ.vars := by
  rw [CNF.mem_vars]
  constructor
  · rintro ⟨c, hc, hv⟩
    have hc' : Clause.ofStdSat c ∈ φ := CNF.mem_toStdSat.mp (Std.Sat.CNF.Internal.mem_iff.mpr hc)
    obtain ⟨b, hb⟩ :=
      (Clause.varMem_toStdSat_iff (Clause.ofStdSat c) v).mp (by simpa using hv)
    exact ⟨Clause.ofStdSat c, hc', b, hb⟩
  · rintro ⟨c, hc, b, hb⟩
    refine ⟨c.toStdSat, ?_, (Clause.varMem_toStdSat_iff c v).mpr ⟨b, hb⟩⟩
    exact Std.Sat.CNF.Internal.mem_iff.mp (CNF.mem_toStdSat.mpr (by simpa using hc))

/-! ### Relabeling, `relabelFin`, and finite `Fin n` model counting -/

/-- `Clause.toStdSat` commutes with variable relabeling. -/
@[simp] theorem Clause.relabel_toStdSat (r : α → β) (c : Clause α) :
    (c.relabel r).toStdSat = c.toStdSat.relabel r := by
  apply Std.Sat.CNF.Clause.ext
  simp [Clause.toStdSat, Clause.relabel]

/-- `Clause.ofStdSat` commutes with variable relabeling. -/
@[simp] theorem Clause.relabel_ofStdSat (r : α → β) (c : Std.Sat.CNF.Clause α) :
    Clause.ofStdSat (c.relabel r) = (Clause.ofStdSat c).relabel r := by
  simp [Clause.ofStdSat, Clause.relabel]

/-- `CNF.toStdSat` commutes with variable relabeling. -/
@[simp] theorem CNF.relabel_toStdSat (r : α → β) (φ : CNF α) :
    (φ.relabel r).toStdSat = φ.toStdSat.relabel r := by
  rw [← CNF.toStdSat_ofStdSat (φ.toStdSat.relabel r)]
  congr 1
  simp [CNF.toStdSat, CNF.ofStdSat, Std.Sat.CNF.relabel, CNF.relabel,
    Function.comp_def, List.map_map]

/-- `CNF.ofStdSat` commutes with variable relabeling. -/
@[simp] theorem CNF.relabel_ofStdSat (r : α → β) (f : Std.Sat.CNF α) :
    CNF.ofStdSat (f.relabel r) = (CNF.ofStdSat f).relabel r := by
  simp [Std.Sat.CNF.relabel, CNF.ofStdSat, CNF.relabel, List.map_map, Function.comp_def]

/-- `Std.Sat.CNF.relabelFin` preserves satisfiability under `CNF.ofStdSat`. -/
theorem CNF.satisfiable_ofStdSat_relabelFin_iff (f : Std.Sat.CNF ℕ) :
    (CNF.ofStdSat f.relabelFin).Satisfiable ↔ (CNF.ofStdSat f).Satisfiable := by
  rw [CNF.satisfiable_ofStdSat_iff, CNF.satisfiable_ofStdSat_iff, Std.Sat.CNF.unsat_relabelFin]

/-- Every variable occurring in `CNF.ofStdSat f` is strictly below `f.numLiterals`. -/
theorem CNF.lt_numLiterals_of_mem_vars_ofStdSat (f : Std.Sat.CNF ℕ) {v : ℕ}
    (hv : v ∈ (CNF.ofStdSat f).vars) : v < f.numLiterals := by
  apply Std.Sat.CNF.lt_numLiterals
  rw [← CNF.varMem_toStdSat_iff, CNF.toStdSat_ofStdSat] at hv
  exact hv

/-- Every variable occurring in `CNF.ofStdSat (f.relabel Fin.val)` for `f : Std.Sat.CNF (Fin n)` is
strictly below `n`. -/
theorem CNF.lt_of_mem_vars_ofStdSat_relabel_val {n : ℕ} (f : Std.Sat.CNF (Fin n)) {v : ℕ}
    (hv : v ∈ (CNF.ofStdSat (f.relabel Fin.val)).vars) : v < n := by
  rw [CNF.relabel_ofStdSat, CNF.mem_vars] at hv
  obtain ⟨c, hc, b, hb⟩ := hv
  rw [CNF.relabel, List.mem_map] at hc
  obtain ⟨d, _, rfl⟩ := hc
  rw [Clause.relabel, List.mem_map] at hb
  obtain ⟨⟨i, bi⟩, _, hEq⟩ := hb
  have hi : i.val = v := congrArg Prod.fst hEq
  exact hi ▸ i.isLt

/-- For `f : Std.Sat.CNF (Fin n)`, `CNF.modelCountOn Finset.univ` of `CNF.ofStdSat f` equals the
number of assignments `a : Fin n → Bool` with `f.eval a = true`. -/
theorem CNF.modelCountOn_ofStdSat_univ {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    (CNF.ofStdSat f).modelCountOn Finset.univ =
      (Finset.univ.filter fun a : Fin n → Bool => f.eval a = true).card := by
  rw [CNF.modelCountOn]
  let U : Finset (Fin n) := Finset.univ
  let e : (↥U → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun σ i => σ ⟨i, Finset.mem_univ i⟩
      invFun := fun a i => a i.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Finset.card_bij (fun σ _ => e σ) (fun σ hσ => ?_) (fun _ _ _ _ h => e.injective h)
    (fun a ha => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_ofStdSat] at hσ ⊢
    convert hσ using 2
    ext i
    simp [e]
  · refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_ofStdSat] at ha ⊢
    convert ha using 2
    ext i
    simp [e]

/-- For `f : Std.Sat.CNF (Fin n)`, the cardinality of `{a : Fin n → Bool // f.eval a = true}`
equals `(CNF.ofStdSat f).modelCountOn Finset.univ`. -/
theorem CNF.card_eval_ofStdSat_eq_modelCountOn {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    Fintype.card {a : Fin n → Bool // f.eval a = true} =
      (CNF.ofStdSat f).modelCountOn Finset.univ := by
  rw [CNF.modelCountOn_ofStdSat_univ, Fintype.card_subtype]

/-- Embedding `Fin n` into `ℕ` via `Fin.val` equates `Std.Sat.CNF (Fin n)` model counting with
`CNF.modelCountOn (Finset.range n)`. -/
theorem CNF.card_eval_eq_modelCountOn_relabel_val {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    Fintype.card {a : Fin n → Bool // f.eval a = true} =
      (CNF.ofStdSat (f.relabel Fin.val)).modelCountOn (Finset.range n) := by
  rw [CNF.card_eval_ofStdSat_eq_modelCountOn, CNF.relabel_ofStdSat]
  let R : Finset ℕ := Finset.range n
  let g : (Fin n → Bool) ≃ (↥R → Bool) :=
    { toFun := fun σ i => σ ⟨i.1, Finset.mem_range.mp i.2⟩
      invFun := fun τ i => τ ⟨i.1, Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hL : (CNF.ofStdSat f).modelCountOn Finset.univ =
      (Finset.univ.filter fun a : Fin n → Bool => (CNF.ofStdSat f).eval a = true).card := by
    rw [CNF.modelCountOn_ofStdSat_univ]
    simp [CNF.eval_ofStdSat]
  rw [hL, CNF.modelCountOn]
  refine Finset.card_bij (fun a _ => g a) (fun a ha => ?_) (fun _ _ _ _ h => g.injective h)
    (fun τ hτ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_relabel] at ha ⊢
    refine (CNF.eval_congr ?_).trans ha
    intro i _
    simp [g]
  · refine ⟨g.symm τ, ?_, g.apply_symm_apply τ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_relabel] at hτ ⊢
    refine (CNF.eval_congr ?_).trans hτ
    intro i _
    simp [g]

/-- Express the exact `Std.Sat.CNF (Fin n)` model count using the occurring-variable
`CNF.modelCount` of `CNF.ofStdSat f`. -/
theorem CNF.card_eval_eq_two_pow_mul_modelCount {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    Fintype.card {a : Fin n → Bool // f.eval a = true} =
      2 ^ (n - (CNF.ofStdSat f).numVars) * (CNF.ofStdSat f).modelCount := by
  rw [CNF.card_eval_ofStdSat_eq_modelCountOn,
    CNF.modelCountOn_eq_mul_modelCount _ _ (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin]

/-- Classical `Std.Sat.CNF.Sat` version of `CNF.card_eval_eq_two_pow_mul_modelCount`. -/
theorem CNF.card_sat_eq_two_pow_mul_modelCount {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    letI := Classical.decPred fun a : Fin n → Bool => f.Sat a
    Fintype.card {a : Fin n → Bool // f.Sat a} =
      2 ^ (n - (CNF.ofStdSat f).numVars) * (CNF.ofStdSat f).modelCount := by
  classical
  have h : (fun a : Fin n → Bool => f.Sat a) = (fun a : Fin n → Bool => f.eval a = true) := rfl
  simp only [h]
  convert CNF.card_eval_eq_two_pow_mul_modelCount f

/-- A `Std.Sat.CNF (Fin n)` formula has a positive number of models iff it is satisfiable. -/
theorem CNF.card_eval_pos_iff {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    0 < Fintype.card {a : Fin n → Bool // f.eval a = true} ↔
      ∃ a : Fin n → Bool, f.Sat a := by
  rw [Fintype.card_pos_iff]
  exact ⟨fun ⟨⟨a, ha⟩⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨⟨a, ha⟩⟩⟩

/-- For `f : Std.Sat.CNF ℕ`, declared-universe model counting on `Finset.range f.numLiterals`
agrees with occurring-variable `CNF.modelCount`. -/
theorem CNF.modelCountOn_ofStdSat_range_numLiterals (f : Std.Sat.CNF ℕ) :
    (CNF.ofStdSat f).modelCountOn (Finset.range f.numLiterals) =
      2 ^ (f.numLiterals - (CNF.ofStdSat f).numVars) * (CNF.ofStdSat f).modelCount := by
  have hsub : (CNF.ofStdSat f).vars.toFinset ⊆ Finset.range f.numLiterals := by
    intro v hv
    exact Finset.mem_range.mpr (CNF.lt_numLiterals_of_mem_vars_ofStdSat f (List.mem_toFinset.mp hv))
  simpa using CNF.modelCountOn_eq_mul_modelCount (CNF.ofStdSat f) (Finset.range f.numLiterals) hsub

/-- Every `Clause` converts to a `Std.Sat.CNF.Clause` of the same length. -/
@[simp] theorem Clause.size_toStdSat (c : Clause α) :
    c.toStdSat.size = c.length := by
  rw [← Std.Sat.CNF.Clause.length_literals, Clause.toStdSat,
    Std.Sat.CNF.Clause.literals_ofLiterals]

/-- Every `Std.Sat.CNF.Clause` converts to a list clause of the same length. -/
@[simp] theorem Clause.length_ofStdSat (c : Std.Sat.CNF.Clause α) :
    (Clause.ofStdSat c).length = c.size :=
  Std.Sat.CNF.Clause.length_literals

/-- Every `CNF` converts to a `Std.Sat.CNF` with the same number of clauses. -/
@[simp] theorem CNF.size_toStdSat (φ : CNF α) :
    φ.toStdSat.clauses.size = φ.length := by
  simp [CNF.toStdSat]

/-- Every `Std.Sat.CNF` converts to a `CNF` with the same number of clauses. -/
@[simp] theorem CNF.length_ofStdSat (f : Std.Sat.CNF α) :
    (CNF.ofStdSat f).length = f.clauses.size := by
  simp [CNF.ofStdSat]

end Cslib.Logic.PL
