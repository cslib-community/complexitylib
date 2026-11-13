/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Restrict
import Mathlib.Data.Finset.Card

/-!
# Unit propagation for CNF formulas

This module formalizes unit-clause detection and unit propagation over `Cslib.Logic.PL.CNF`, built
on `Cslib.Logic.PL.CNF.restrict` and `Cslib.Logic.PL.CNF.restrictList`.

Iterated propagation uses structural recursion on a clause-count fuel bound `φ.length`
(`unitPropagateWithTrailAux`), ensuring kernel reducibility while terminating cleanly on every
formula because each unit step removes at least the unit clause `[l]`.

Because propagating `[l]` drops `[l]` itself from `φ.restrict l.1 l.2`, evaluation equivalence
carries an explicit side condition that every propagated unit literal holds under `σ`
(`CNF.eval_unitPropagate_iff`). Satisfiability (`CNF.satisfiable_unitPropagate_iff`) and model
counts (`CNF.modelCountOn_unitPropagate`, `CNF.modelCount_unitPropagate`) are conserved exactly.

## Main definitions

* `Cslib.Logic.PL.Clause.unit?`, `Cslib.Logic.PL.CNF.findUnit?`: syntactic unit-clause
  detection.
* `Cslib.Logic.PL.CNF.unitPropagateStep`: one step of unit propagation.
* `Cslib.Logic.PL.CNF.unitPropagateWithTrail`, `Cslib.Logic.PL.CNF.unitPropagate`,
  `Cslib.Logic.PL.CNF.unitTrail`: iterated unit propagation to a unit-free normal form.

## Main results

* `Cslib.Logic.PL.CNF.eval_eq_of_mem_singleton`,
  `Cslib.Logic.PL.CNF.modelCountOn_restrict_of_mem_singleton`: single-unit forcing and declared
  model-count conservation.
* `Cslib.Logic.PL.CNF.unitPropagate_eq_restrictList`: propagated formula equals sequential
  restriction along the trail.
* `Cslib.Logic.PL.CNF.eval_unitPropagate_iff`, `Cslib.Logic.PL.CNF.satisfiable_unitPropagate_iff`,
  `Cslib.Logic.PL.CNF.modelCountOn_unitPropagate`, `Cslib.Logic.PL.CNF.modelCount_unitPropagate`:
  soundness, completeness, and model-count conservation of iterated unit propagation.
* `Cslib.Logic.PL.CNF.findUnit?_unitPropagate`, `Cslib.Logic.PL.CNF.unitPropagate_idem`: normal
  form (no unit clauses remain) and idempotence.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-! ### Unit-clause recognition -/

/-- Extract the literal of a singleton clause `[l]`, returning `none` otherwise. -/
@[expose] def Clause.unit? (c : Clause V) : Option (Literal V) :=
  match c with
  | [l] => some l
  | _ => none

@[simp] theorem Clause.unit?_nil : Clause.unit? ([] : Clause V) = none := rfl

@[simp] theorem Clause.unit?_singleton (l : Literal V) : Clause.unit? [l] = some l := rfl

/-- `c.unit? = some l` holds if and only if `c = [l]`. -/
theorem Clause.unit?_eq_some_iff {c : Clause V} {l : Literal V} :
    c.unit? = some l ↔ c = [l] := by
  cases c with
  | nil => simp
  | cons a t =>
    cases t with
    | nil => simp [Clause.unit?]
    | cons b u => simp [Clause.unit?]

/-- `c.unit? = none` holds if and only if `c.length ≠ 1`. -/
theorem Clause.unit?_eq_none_iff {c : Clause V} :
    c.unit? = none ↔ c.length ≠ 1 := by
  cases c with
  | nil => simp
  | cons a t =>
    cases t with
    | nil => simp [Clause.unit?]
    | cons b u => simp [Clause.unit?]

namespace CNF

variable [DecidableEq V]

/-- Find the literal of the first unit clause in `φ`, if any. -/
@[expose] def findUnit? (φ : CNF V) : Option (Literal V) :=
  φ.findSome? Clause.unit?

omit [DecidableEq V] in
/-- If `φ.findUnit? = some l`, then the unit clause `[l]` belongs to `φ`. -/
theorem mem_of_findUnit?_eq_some {φ : CNF V} {l : Literal V} (h : φ.findUnit? = some l) :
    [l] ∈ φ := by
  rw [findUnit?, List.findSome?_eq_some_iff] at h
  obtain ⟨_, c, _, rfl, hc, -⟩ := h
  obtain rfl := Clause.unit?_eq_some_iff.mp hc
  simp

omit [DecidableEq V] in
/-- If `φ.findUnit? = some l`, then `l.1` occurs in `φ`. -/
theorem mem_vars_of_findUnit?_eq_some {φ : CNF V} {l : Literal V} (h : φ.findUnit? = some l) :
    l.1 ∈ φ.vars :=
  mem_vars.mpr ⟨[l], mem_of_findUnit?_eq_some h, l.2, List.mem_cons_self⟩

omit [DecidableEq V] in
/-- `φ.findUnit? = none` holds iff `φ` contains no unit clauses. -/
theorem findUnit?_eq_none_iff {φ : CNF V} :
    φ.findUnit? = none ↔ ∀ c ∈ φ, c.length ≠ 1 := by
  rw [findUnit?, List.findSome?_eq_none_iff]
  simp [Clause.unit?_eq_none_iff]

/-! ### Single-unit forcing and model-count conservation -/

omit [DecidableEq V] in
/-- Any model of a formula containing the unit clause `[l]` sets `l.1` to `l.2`. -/
theorem eval_eq_of_mem_singleton {φ : CNF V} {l : Literal V} (hl : [l] ∈ φ)
    {σ : V → Bool} (hσ : φ.eval σ = true) : σ l.1 = l.2 := by
  have hc := (CNF.eval_eq_true_iff σ φ).mp hσ [l] hl
  simpa [Clause.eval, Literal.eval] using hc

/-- For a unit clause `[l] ∈ φ`, `φ` holds under `σ` iff `σ l.1 = l.2` and `φ.restrict l.1 l.2`
holds under `σ`. -/
theorem eval_restrict_of_mem_singleton {φ : CNF V} {l : Literal V} (hl : [l] ∈ φ) (σ : V → Bool) :
    φ.eval σ = true ↔ σ l.1 = l.2 ∧ (φ.restrict l.1 l.2).eval σ = true := by
  constructor
  · intro hσ
    have hval := eval_eq_of_mem_singleton hl hσ
    exact ⟨hval, (eval_restrict_of_eq hval).symm ▸ hσ⟩
  · rintro ⟨hval, hres⟩
    rwa [eval_restrict_of_eq hval] at hres

/-- Propagating a unit clause `[l] ∈ φ` preserves satisfiability. -/
theorem satisfiable_restrict_of_mem_singleton {φ : CNF V} {l : Literal V} (hl : [l] ∈ φ) :
    (φ.restrict l.1 l.2).Satisfiable ↔ φ.Satisfiable := by
  rw [satisfiable_restrict_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, eval_eq_of_mem_singleton hl hσ, hσ⟩

/-- Propagating a unit clause `[l] ∈ φ` on `l.1 ∈ declared` preserves `CNF.modelCountOn` on
`declared.erase l.1`. -/
theorem modelCountOn_restrict_of_mem_singleton {φ : CNF V} {l : Literal V} (hl : [l] ∈ φ)
    {declared : Finset V} (hv : l.1 ∈ declared) :
    φ.modelCountOn declared = (φ.restrict l.1 l.2).modelCountOn (declared.erase l.1) :=
  modelCountOn_eq_restrict_of_forall hv fun _ hσ => eval_eq_of_mem_singleton hl hσ

/-- Propagating a unit clause `[l] ∈ φ` preserves occurring-variable `CNF.modelCount` up to the
factor `2` for each variable other than `l.1` dropped alongside `[l]`. -/
theorem modelCount_restrict_of_mem_singleton {φ : CNF V} {l : Literal V} (hl : [l] ∈ φ) :
    φ.modelCount =
      2 ^ (φ.numVars - 1 - (φ.restrict l.1 l.2).numVars) * (φ.restrict l.1 l.2).modelCount := by
  have hlvars : l.1 ∈ φ.vars.toFinset :=
    List.mem_toFinset.mpr (mem_vars.mpr ⟨[l], hl, l.2, List.mem_cons_self⟩)
  rw [← modelCountOn_vars φ, modelCountOn_restrict_of_mem_singleton hl hlvars,
    modelCountOn_eq_mul_modelCount (φ.restrict l.1 l.2) (φ.vars.toFinset.erase l.1)
      vars_restrict_subset,
    Finset.card_erase_of_mem hlvars]
  rfl

/-! ### Single-step and iterated unit propagation -/

/-- Perform a single unit-propagation step on `φ`, returning `φ` unchanged if no unit clause
exists. -/
@[expose] def unitPropagateStep (φ : CNF V) : CNF V :=
  match φ.findUnit? with
  | none => φ
  | some l => φ.restrict l.1 l.2

theorem unitPropagateStep_of_none {φ : CNF V} (h : φ.findUnit? = none) :
    φ.unitPropagateStep = φ := by
  simp [unitPropagateStep, h]

theorem unitPropagateStep_of_some {φ : CNF V} {l : Literal V} (h : φ.findUnit? = some l) :
    φ.unitPropagateStep = φ.restrict l.1 l.2 := by
  simp [unitPropagateStep, h]

/-- One step of unit propagation preserves satisfiability. -/
theorem satisfiable_unitPropagateStep_iff (φ : CNF V) :
    φ.unitPropagateStep.Satisfiable ↔ φ.Satisfiable := by
  cases h : φ.findUnit? with
  | none => simp [unitPropagateStep_of_none h]
  | some l =>
    rw [unitPropagateStep_of_some h]
    exact satisfiable_restrict_of_mem_singleton (mem_of_findUnit?_eq_some h)

/-- One step of unit propagation does not increase clause count. -/
theorem length_unitPropagateStep_le (φ : CNF V) :
    φ.unitPropagateStep.length ≤ φ.length := by
  cases h : φ.findUnit? with
  | none => simp [unitPropagateStep_of_none h]
  | some l =>
    rw [unitPropagateStep_of_some h]
    exact length_restrict_le φ l.1 l.2

/-- Structural fuel helper for iterated unit propagation. -/
@[expose] def unitPropagateWithTrailAux : ℕ → CNF V → List (Literal V) × CNF V
  | 0, φ => ([], φ)
  | n + 1, φ =>
    match φ.findUnit? with
    | none => ([], φ)
    | some l =>
      let res := unitPropagateWithTrailAux n (φ.restrict l.1 l.2)
      (l :: res.1, res.2)

/-- Repeatedly propagate unit clauses to a unit-free formula, returning `(trail, reduced)` with
the list of propagated unit literals and the resulting unit-free CNF. -/
@[expose] def unitPropagateWithTrail (φ : CNF V) : List (Literal V) × CNF V :=
  unitPropagateWithTrailAux φ.length φ

/-- The unit-free CNF produced by iterated unit propagation on `φ`. -/
@[expose] def unitPropagate (φ : CNF V) : CNF V :=
  (φ.unitPropagateWithTrail).2

/-- The list of unit literals forced during iterated unit propagation on `φ`. -/
@[expose] def unitTrail (φ : CNF V) : List (Literal V) :=
  (φ.unitPropagateWithTrail).1

private theorem unitPropagateWithTrailAux_of_none {n : ℕ} {φ : CNF V} (h : φ.findUnit? = none) :
    unitPropagateWithTrailAux n φ = ([], φ) := by
  cases n with
  | zero => rfl
  | succ k => simp [unitPropagateWithTrailAux, h]

private theorem unitPropagateWithTrailAux_eq_of_le {n m : ℕ} {φ : CNF V}
    (hn : φ.length ≤ n) (hm : φ.length ≤ m) :
    unitPropagateWithTrailAux n φ = unitPropagateWithTrailAux m φ := by
  induction n generalizing m φ with
  | zero =>
    obtain rfl : φ = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hn)
    exact (unitPropagateWithTrailAux_of_none (φ := []) rfl).trans
      (unitPropagateWithTrailAux_of_none (φ := []) rfl).symm
  | succ k ih =>
    cases h : φ.findUnit? with
    | none =>
      exact (unitPropagateWithTrailAux_of_none h).trans
        (unitPropagateWithTrailAux_of_none h).symm
    | some l =>
      have hpos : 0 < φ.length := List.length_pos_of_mem (mem_of_findUnit?_eq_some h)
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hlt : (φ.restrict l.1 l.2).length < φ.length :=
        length_restrict_lt (mem_of_findUnit?_eq_some h) List.mem_cons_self
      have ihstep := ih (by omega : (φ.restrict l.1 l.2).length ≤ k)
        (by omega : (φ.restrict l.1 l.2).length ≤ m')
      simp [unitPropagateWithTrailAux, h, ihstep]

private theorem unitPropagateWithTrail_of_none {φ : CNF V} (h : φ.findUnit? = none) :
    φ.unitPropagateWithTrail = ([], φ) :=
  unitPropagateWithTrailAux_of_none h

private theorem unitPropagateWithTrail_of_some {φ : CNF V} {l : Literal V}
    (h : φ.findUnit? = some l) :
    φ.unitPropagateWithTrail =
      (l :: (φ.restrict l.1 l.2).unitTrail, (φ.restrict l.1 l.2).unitPropagate) := by
  have hpos : 0 < φ.length := List.length_pos_of_mem (mem_of_findUnit?_eq_some h)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hlt : (φ.restrict l.1 l.2).length < φ.length :=
    length_restrict_lt (mem_of_findUnit?_eq_some h) List.mem_cons_self
  have hfuel : unitPropagateWithTrailAux k (φ.restrict l.1 l.2) =
      (φ.restrict l.1 l.2).unitPropagateWithTrail :=
    unitPropagateWithTrailAux_eq_of_le (by omega) le_rfl
  rw [unitPropagateWithTrail, hk]
  simp only [unitPropagateWithTrailAux, h, hfuel, unitTrail, unitPropagate]

/-- Induction principle matching iterated unit propagation: either `φ` has no unit clauses, or
some unit literal `l` is propagated via `φ.restrict l.1 l.2` with strictly fewer variables. -/
theorem unitPropagate_ind {motive : CNF V → Prop}
    (base : ∀ φ, φ.findUnit? = none → motive φ)
    (step : ∀ φ l, φ.findUnit? = some l → motive (φ.restrict l.1 l.2) → motive φ)
    (φ : CNF V) : motive φ := by
  induction hn : φ.numVars using Nat.strong_induction_on generalizing φ with
  | ind n ih =>
    cases h : φ.findUnit? with
    | none => exact base φ h
    | some l =>
      have hlt : (φ.restrict l.1 l.2).numVars < n :=
        hn ▸ numVars_restrict_lt (mem_vars_of_findUnit?_eq_some h)
      exact step φ l h (ih _ hlt (φ.restrict l.1 l.2) rfl)

/-- Iterated unit propagation equals sequential restriction along `φ.unitTrail`. -/
theorem unitPropagate_eq_restrictList (φ : CNF V) :
    φ.unitPropagate = φ.restrictList φ.unitTrail := by
  induction φ using unitPropagate_ind with
  | base φ h =>
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitPropagate, unitTrail, hwt]
  | step φ l h ih =>
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitPropagate, unitTrail, hwt]
    dsimp only
    rw [restrictList_cons]
    exact ih

/-- Exact evaluation equivalence for iterated unit propagation together with the forced unit
trail. -/
theorem eval_unitPropagate_iff (φ : CNF V) (σ : V → Bool) :
    ((∀ l ∈ φ.unitTrail, σ l.1 = l.2) ∧ φ.unitPropagate.eval σ = true) ↔ φ.eval σ = true := by
  induction φ using unitPropagate_ind with
  | base φ h =>
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitPropagate, unitTrail, hwt]
  | step φ l h ih =>
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitPropagate, unitTrail, hwt]
    dsimp only
    rw [eval_restrict_of_mem_singleton (mem_of_findUnit?_eq_some h)]
    constructor
    · rintro ⟨htrail, heval⟩
      refine ⟨htrail l List.mem_cons_self, ih.mp ⟨fun m hm => ?_, heval⟩⟩
      exact htrail m (List.mem_cons_of_mem _ hm)
    · rintro ⟨hl, hres⟩
      obtain ⟨htrail, heval⟩ := ih.mpr hres
      refine ⟨fun m hm => ?_, heval⟩
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hl
      · exact htrail m hm'

/-- Iterated unit propagation preserves satisfiability. -/
theorem satisfiable_unitPropagate_iff (φ : CNF V) :
    φ.unitPropagate.Satisfiable ↔ φ.Satisfiable := by
  induction φ using unitPropagate_ind with
  | base φ h =>
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitPropagate, hwt]
  | step φ l h ih =>
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitPropagate, hwt]
    dsimp only
    exact ih.trans (satisfiable_restrict_of_mem_singleton (mem_of_findUnit?_eq_some h))

/-- A unit-propagation conflict (deriving the empty clause) certifies unsatisfiability. -/
theorem not_satisfiable_of_nil_mem_unitPropagate {φ : CNF V} (h : [] ∈ φ.unitPropagate) :
    ¬φ.Satisfiable := by
  rw [← satisfiable_unitPropagate_iff]
  rintro ⟨σ, hσ⟩
  have hc := (CNF.eval_eq_true_iff σ φ.unitPropagate).mp hσ [] h
  simp at hc

/-- Every variable in `φ.unitTrail` occurs in `φ`. -/
theorem mem_vars_of_mem_unitTrail (φ : CNF V) {l : Literal V} (hl : l ∈ φ.unitTrail) :
    l.1 ∈ φ.vars := by
  revert hl
  induction φ using unitPropagate_ind with
  | base φ h =>
    intro hl
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitTrail, hwt] at hl
  | step φ u h ih =>
    intro hl
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitTrail, hwt] at hl
    dsimp only at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact mem_vars_of_findUnit?_eq_some h
    · exact Finset.mem_of_mem_erase
        (vars_restrict_subset (List.mem_toFinset.mpr (ih hl')))
        |> List.mem_toFinset.mp

/-- `φ.unitTrail` never repeats a variable. -/
theorem unitTrail_nodup_vars (φ : CNF V) :
    (φ.unitTrail.map Prod.fst).Nodup := by
  induction φ using unitPropagate_ind with
  | base φ h =>
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitTrail, hwt]
  | step φ u h ih =>
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitTrail, hwt]
    dsimp only
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hu
    obtain ⟨m, hm, hmu⟩ := List.mem_map.mp hu
    have hmvars := mem_vars_of_mem_unitTrail (φ.restrict u.1 u.2) hm
    rw [hmu] at hmvars
    exact notMem_vars_restrict φ u.1 u.2 hmvars

/-- No unit clauses remain after `CNF.unitPropagate`. -/
theorem findUnit?_unitPropagate (φ : CNF V) :
    φ.unitPropagate.findUnit? = none := by
  induction φ using unitPropagate_ind with
  | base φ h =>
    have hwt := unitPropagateWithTrail_of_none h
    simpa [unitPropagate, hwt] using h
  | step φ u h ih =>
    have hwt := unitPropagateWithTrail_of_some h
    rw [unitPropagate, hwt]
    exact ih

/-- Every clause remaining in `φ.unitPropagate` has length distinct from `1`. -/
theorem length_ne_one_of_mem_unitPropagate {φ : CNF V} {c : Clause V}
    (hc : c ∈ φ.unitPropagate) : c.length ≠ 1 :=
  findUnit?_eq_none_iff.mp (findUnit?_unitPropagate φ) c hc

/-- `CNF.unitPropagate` is idempotent. -/
@[simp] theorem unitPropagate_idem (φ : CNF V) :
    φ.unitPropagate.unitPropagate = φ.unitPropagate := by
  have hwt := unitPropagateWithTrail_of_none (findUnit?_unitPropagate φ)
  rw [unitPropagate, hwt]

/-- Declared-universe model counting is conserved across iterated unit propagation, removing the
forced trail variables from `declared`. -/
theorem modelCountOn_unitPropagate (φ : CNF V) (declared : Finset V)
    (htrail : ∀ l ∈ φ.unitTrail, l.1 ∈ declared) :
    φ.modelCountOn declared =
      φ.unitPropagate.modelCountOn (declared \ (φ.unitTrail.map Prod.fst).toFinset) := by
  revert declared htrail
  induction φ using unitPropagate_ind with
  | base φ h =>
    intro declared _
    have hwt := unitPropagateWithTrail_of_none h
    simp [unitPropagate, unitTrail, hwt]
  | step φ u h ih =>
    intro declared htrail
    have hwt := unitPropagateWithTrail_of_some h
    have hu : u ∈ φ.unitTrail := by
      rw [unitTrail, hwt]
      exact List.mem_cons_self
    have hudec : u.1 ∈ declared := htrail u hu
    have hsub : ∀ m ∈ (φ.restrict u.1 u.2).unitTrail, m.1 ∈ declared.erase u.1 := by
      intro m hm
      have hm' : m ∈ φ.unitTrail := by
        rw [unitTrail, hwt]
        exact List.mem_cons_of_mem _ hm
      have hnd := unitTrail_nodup_vars φ
      rw [unitTrail, hwt] at hnd
      dsimp only at hnd
      rw [List.map_cons, List.nodup_cons] at hnd
      have hne : m.1 ≠ u.1 := fun heq =>
        hnd.1 (List.mem_map.mpr ⟨m, hm, heq⟩)
      exact Finset.mem_erase.mpr ⟨hne, htrail m hm'⟩
    have ihstep := ih (declared.erase u.1) hsub
    rw [modelCountOn_restrict_of_mem_singleton (mem_of_findUnit?_eq_some h) hudec, ihstep]
    conv_rhs => rw [unitPropagate, unitTrail, hwt]
    dsimp only
    congr 1
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.map_cons, List.mem_toFinset,
      List.mem_cons, not_or]
    tauto

/-- When `declared` contains all occurring variables of `φ`, `φ.modelCountOn declared` equals
`φ.unitPropagate.modelCountOn` on the unpropagated declared variables. -/
theorem modelCountOn_unitPropagate_of_vars_subset (φ : CNF V) {declared : Finset V}
    (hvars : φ.vars.toFinset ⊆ declared) :
    φ.modelCountOn declared =
      φ.unitPropagate.modelCountOn (declared \ (φ.unitTrail.map Prod.fst).toFinset) :=
  modelCountOn_unitPropagate φ declared fun _ hl =>
    hvars (List.mem_toFinset.mpr (mem_vars_of_mem_unitTrail φ hl))

/-- Occurring-variable `CNF.modelCount` under iterated unit propagation, accounting for any
variables eliminated alongside forced unit clauses. -/
theorem modelCount_unitPropagate (φ : CNF V) :
    φ.modelCount =
      2 ^ (φ.numVars - φ.unitTrail.length - φ.unitPropagate.numVars) *
        φ.unitPropagate.modelCount := by
  have hcount := modelCountOn_unitPropagate_of_vars_subset φ (Finset.Subset.refl _)
  rw [modelCountOn_vars] at hcount
  have hsubTrail : (φ.unitTrail.map Prod.fst).toFinset ⊆ φ.vars.toFinset := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact List.mem_toFinset.mpr (mem_vars_of_mem_unitTrail φ hl)
  have hvarsProp : φ.unitPropagate.vars.toFinset ⊆
      φ.vars.toFinset \ (φ.unitTrail.map Prod.fst).toFinset := by
    rw [unitPropagate_eq_restrictList]
    exact vars_restrictList_subset φ φ.unitTrail
  rw [hcount, modelCountOn_eq_mul_modelCount _ _ hvarsProp,
    Finset.card_sdiff_of_subset hsubTrail,
    List.toFinset_card_of_nodup (unitTrail_nodup_vars φ), List.length_map]
  rfl

/-- Iterated unit propagation does not increase clause count. -/
theorem length_unitPropagate_le (φ : CNF V) :
    φ.unitPropagate.length ≤ φ.length := by
  rw [unitPropagate_eq_restrictList]
  exact length_restrictList_le φ φ.unitTrail

/-- Remaining variables after iterated unit propagation belong to `φ` outside the trail. -/
theorem vars_unitPropagate_subset (φ : CNF V) :
    φ.unitPropagate.vars.toFinset ⊆
      φ.vars.toFinset \ (φ.unitTrail.map Prod.fst).toFinset := by
  rw [unitPropagate_eq_restrictList]
  exact vars_restrictList_subset φ φ.unitTrail

/-- Iterated unit propagation does not increase variable occurrences. -/
theorem occurrences_unitPropagate_le (φ : CNF V) (u : V) :
    φ.unitPropagate.occurrences u ≤ φ.occurrences u := by
  rw [unitPropagate_eq_restrictList]
  exact occurrences_restrictList_le φ φ.unitTrail u

/-- Any variable forced in `φ.unitTrail` has zero remaining occurrences in `φ.unitPropagate`. -/
theorem occurrences_unitPropagate_eq_zero (φ : CNF V) {l : Literal V} (hl : l ∈ φ.unitTrail) :
    φ.unitPropagate.occurrences l.1 = 0 := by
  rw [unitPropagate_eq_restrictList]
  exact occurrences_restrictList_eq_zero φ φ.unitTrail (List.mem_map.mpr ⟨l, hl, rfl⟩)

end CNF

end Cslib.Logic.PL
