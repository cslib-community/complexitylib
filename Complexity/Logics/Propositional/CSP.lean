/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
public import Complexity.Foundations.Data.List.SelectDistinct
import Mathlib.Data.List.Zip

/-!
# Boolean constraint satisfaction problems

A Boolean constraint on variables `V` specifies a list of scoped variables `c.vars` and a list
`c.forbidden` of forbidden local assignments (`List Bool`). An assignment `σ : V → Bool` satisfies
the constraint when its restriction `c.vars.map σ` is not among the forbidden assignments
(`Constraint.eval`). A constraint satisfaction problem instance `φ : CSP V` is a list of
constraints, and is satisfied when all of its constraints are satisfied (`CSP.eval`).

This module implements the canonical count-preserving reduction from Boolean CSPs of bounded arity
to conjunctive normal form formulas: each forbidden local assignment `α` to `c.vars` becomes a
clause `forbiddenClause c.vars α`, which contains the literal `(v, !b)` for each variable `v` and
forbidden bit `b`. The clause is falsified if and only if `c.vars.map σ = α`
(`forbiddenClause_eval_eq_false_iff`).

Compiling a CSP instance `φ` to CNF via `CSP.toCNF` preserves:
- clause widths: each clause has length at most `c.vars.length` (`CSP.all_length_le_toCNF`);
- satisfying assignments: `φ.toCNF.eval σ = φ.eval σ` on every valid instance (`CSP.eval_toCNF`);
- model counts on any declared finite set: `(φ.toCNF).modelCountOn S = φ.modelCountOn S`
  (`CSP.modelCountOn_toCNF`);
- dense relabeling: `(φ.denseRelabel).toCNF = (φ.toCNF).relabel φ.distinctVars.idxOf`
  (`CSP.toCNF_denseRelabel`).

This formalizes the reduction described in Appendix C.2 (Corollary C.2) of [OpenAI2026ETH] and
answers Milestone 1 of #1326.

## Main definitions

* `Cslib.Logic.PL.Constraint`: a Boolean constraint with a variable scope and forbidden assignments.
* `Cslib.Logic.PL.CSP`: a Boolean constraint satisfaction problem instance (`List (Constraint V)`).
* `Cslib.Logic.PL.Constraint.eval`, `Cslib.Logic.PL.CSP.eval`, `Cslib.Logic.PL.CSP.Satisfiable`:
  truth evaluation and satisfiability.
* `Cslib.Logic.PL.Constraint.Valid`, `Cslib.Logic.PL.CSP.Valid`: constraints whose forbidden tuples
  match the scope length.
* `Cslib.Logic.PL.Constraint.HasWidth`, `Cslib.Logic.PL.CSP.HasWidth`: scope length bounded by `k`.
* `Cslib.Logic.PL.forbiddenClause`: the clause forbidding one local assignment.
* `Cslib.Logic.PL.Constraint.toCNF`, `Cslib.Logic.PL.CSP.toCNF`: compilation to CNF.
* `Cslib.Logic.PL.CSP.modelCountOn`, `Cslib.Logic.PL.CSP.modelCount`: declared and
  occurring-variable model counts.
* `Cslib.Logic.PL.Constraint.relabel`, `Cslib.Logic.PL.CSP.relabel`,
  `Cslib.Logic.PL.CSP.denseRelabel`: variable relabeling.
* `Cslib.Logic.PL.Relation`, `Cslib.Logic.PL.Language`, `Cslib.Logic.PL.CSP.InLanguage`:
  signatures and constraint languages of bounded arity.

## Main results

* `Cslib.Logic.PL.forbiddenClause_eval_eq_false_iff`: `forbiddenClause` is falsified iff the local
  assignment matches.
* `Cslib.Logic.PL.Constraint.eval_toCNF`, `Cslib.Logic.PL.CSP.eval_toCNF`: semantics preservation.
* `Cslib.Logic.PL.CSP.all_length_le_toCNF`: clause width bounded by maximum arity.
* `Cslib.Logic.PL.CSP.modelCountOn_toCNF`: declared-variable model counts are preserved.
* `Cslib.Logic.PL.CSP.modelCount_eq_mul_toCNF_modelCount`: exact model count relation with CNF.
* `Cslib.Logic.PL.CSP.vars_toCNF_subset`, `Cslib.Logic.PL.CSP.numVars_toCNF_le`: variable
  occurrences and counts are bounded by the CSP instance.
* `Cslib.Logic.PL.CSP.toCNF_relabel`: compilation commutes with variable relabeling.
* `Cslib.Logic.PL.CSP.InLanguage.valid`, `Cslib.Logic.PL.CSP.InLanguage.hasWidth`: instances in a
  bounded-arity language are valid and have bounded width.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Complexity

variable {V W : Type*}

/-- A Boolean constraint over a variable type `V`. It specifies an ordered list of scoped
variables `vars` and a list of forbidden local truth assignments `forbidden`. Each assignment
in `forbidden` that matches the scope's length is rejected by the constraint. -/
structure Constraint (V : Type*) where
  /-- The ordered list of scoped variables of the constraint. -/
  vars : List V
  /-- The list of forbidden local truth assignments to `vars`. -/
  forbidden : List (List Bool)
  deriving DecidableEq

/-- A Boolean constraint satisfaction problem (CSP) instance is a list of constraints. -/
abbrev CSP (V : Type*) : Type _ := List (Constraint V)

/-- The arity of a constraint: the number of scoped variables. -/
def Constraint.arity (c : Constraint V) : ℕ := c.vars.length

/-- A constraint has width at most `k` when its arity is at most `k`. -/
def Constraint.HasWidth (k : ℕ) (c : Constraint V) : Prop := c.vars.length ≤ k

/-- A CSP instance has width at most `k` when all of its constraints have width at most `k`. -/
def CSP.HasWidth (k : ℕ) (φ : CSP V) : Prop := ∀ c ∈ φ, c.HasWidth k

/-- A constraint is valid when every forbidden assignment has the same length as its variable
scope. -/
def Constraint.Valid (c : Constraint V) : Prop := ∀ α ∈ c.forbidden, α.length = c.vars.length

/-- A CSP instance is valid when all of its constraints are valid. -/
def CSP.Valid (φ : CSP V) : Prop := ∀ c ∈ φ, c.Valid

/-- An assignment `σ` satisfies a constraint `c` when `c.vars.map σ` is not among `c.forbidden`. -/
def Constraint.eval (σ : V → Bool) (c : Constraint V) : Bool :=
  c.forbidden.all fun α => decide (c.vars.map σ ≠ α)

/-- An assignment `σ` satisfies a CSP instance `φ` when it satisfies every constraint. -/
def CSP.eval (σ : V → Bool) (φ : CSP V) : Bool :=
  φ.all (Constraint.eval σ)

/-- A CSP instance is satisfiable when some assignment satisfies all its constraints. -/
def CSP.Satisfiable (φ : CSP V) : Prop := ∃ σ : V → Bool, φ.eval σ = true

/-! ### Compilation to CNF -/

/-- The clause forbidding a specific local truth assignment `α` on variables `vars`.
It is satisfied under `σ` iff `vars.map σ ≠ α`. -/
def forbiddenClause (vars : List V) (α : List Bool) : Clause V :=
  List.zipWith (fun v b => (v, !b)) vars α

private theorem beq_not_eq_false (x y : Bool) : (x == !y) = false ↔ x = y := by
  cases x <;> cases y <;> decide

/-- The clause forbidding `α` is falsified under `σ` if and only if the assignment to `vars`
equals `α` exactly. -/
theorem forbiddenClause_eval_eq_false_iff (σ : V → Bool) :
    ∀ (vars : List V) (α : List Bool) (_ : vars.length = α.length),
      Clause.eval σ (forbiddenClause vars α) = false ↔ vars.map σ = α
  | [], [], _ => by
    simp [forbiddenClause, Clause.eval]
  | v :: vars, b :: α, hlen => by
    have hlen' : vars.length = α.length := Nat.succ.inj hlen
    simp only [forbiddenClause, List.zipWith_cons_cons, Clause.eval, List.any_cons,
      Bool.or_eq_false_iff, Literal.eval_mk, beq_not_eq_false, List.map_cons, List.cons.injEq]
    change (σ v = b ∧ Clause.eval σ (forbiddenClause vars α) = false) ↔ (σ v = b ∧ vars.map σ = α)
    rw [forbiddenClause_eval_eq_false_iff σ vars α hlen']

/-- The truth value of `forbiddenClause vars α` under `σ` is `decide (vars.map σ ≠ α)`. -/
theorem forbiddenClause_eval_eq_decide (σ : V → Bool) (vars : List V) (α : List Bool)
    (hlen : vars.length = α.length) :
    Clause.eval σ (forbiddenClause vars α) = decide (vars.map σ ≠ α) := by
  cases h : Clause.eval σ (forbiddenClause vars α)
  · rw [forbiddenClause_eval_eq_false_iff σ vars α hlen] at h
    simp [h]
  · have hne : vars.map σ ≠ α := by
      intro heq
      have := (forbiddenClause_eval_eq_false_iff σ vars α hlen).2 heq
      rw [h] at this
      contradiction
    simp [hne]

/-- Any variable appearing in a literal of `forbiddenClause vars α` belongs to `vars`. -/
theorem mem_vars_forbiddenClause {vars : List V} {α : List Bool} {v : V} {b : Bool}
    (hv : (v, b) ∈ forbiddenClause vars α) : v ∈ vars := by
  induction vars generalizing α with
  | nil =>
    simp [forbiddenClause] at hv
  | cons v' vars ih =>
    cases α with
    | nil =>
      simp [forbiddenClause] at hv
    | cons b' α =>
      simp only [forbiddenClause, List.zipWith_cons_cons, List.mem_cons] at hv
      rcases hv with heq | htail
      · injection heq with heq1 _
        subst heq1
        exact .head _
      · exact List.mem_cons_of_mem _ (ih htail)

/-- Compile a constraint to a list of clauses, one for each forbidden local assignment. -/
def Constraint.toCNF (c : Constraint V) : CNF V :=
  c.forbidden.map (forbiddenClause c.vars)

/-- Compile a CSP instance to a CNF formula by collecting the clauses of all constraints. -/
def CSP.toCNF (φ : CSP V) : CNF V :=
  φ.flatMap Constraint.toCNF

/-- Compiling a valid constraint to CNF preserves its truth evaluation. -/
theorem Constraint.eval_toCNF (σ : V → Bool) (c : Constraint V) (h : c.Valid) :
    c.toCNF.eval σ = c.eval σ := by
  rw [Bool.eq_iff_iff]
  simp only [CNF.eval, toCNF, List.all_map, Constraint.eval, List.all_eq_true, Function.comp_apply]
  refine forall₂_congr fun α hα => ?_
  rw [forbiddenClause_eval_eq_decide σ c.vars α (h α hα).symm]

/-- Compiling a valid CSP instance to CNF preserves its truth evaluation under every assignment. -/
theorem CSP.eval_toCNF (σ : V → Bool) (φ : CSP V) (h : φ.Valid) :
    φ.toCNF.eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff]
  simp only [CNF.eval, toCNF, List.all_flatMap, CSP.eval, List.all_eq_true]
  refine forall₂_congr fun c hc => ?_
  have he := Constraint.eval_toCNF σ c (h c hc)
  rw [← he, CNF.eval, List.all_eq_true]

/-- Compiling a valid CSP instance to CNF preserves satisfiability. -/
theorem CSP.satisfiable_toCNF (φ : CSP V) (h : φ.Valid) :
    φ.toCNF.Satisfiable ↔ φ.Satisfiable := by
  simp only [CNF.Satisfiable, CSP.Satisfiable, CSP.eval_toCNF _ _ h]

/-- Every clause generated from a constraint has length bounded by the constraint's arity. -/
theorem Constraint.all_length_le_toCNF {k : ℕ} (c : Constraint V) (h : c.HasWidth k) :
    ∀ cl ∈ c.toCNF, cl.length ≤ k := by
  intro cl hcl
  obtain ⟨α, _, rfl⟩ := List.mem_map.1 hcl
  dsimp [forbiddenClause]
  rw [List.length_zipWith]
  exact (Nat.min_le_left _ _).trans h

/-- Every clause generated from a bounded-width CSP has length bounded by `k`. -/
theorem CSP.all_length_le_toCNF {k : ℕ} (φ : CSP V) (h : φ.HasWidth k) :
    ∀ cl ∈ φ.toCNF, cl.length ≤ k := by
  intro cl hcl
  obtain ⟨c, hc, hcl'⟩ := List.mem_flatMap.1 hcl
  exact Constraint.all_length_le_toCNF c (h c hc) cl hcl'

/-! ### Model counting -/

/-- The list of all scoped variable occurrences in a CSP instance. -/
def CSP.vars (φ : CSP V) : List V := φ.flatMap (·.vars)

/-- Count the satisfying assignments of `φ` restricted to a declared finite set of variables,
extending by `false` outside `declared`. -/
def CSP.modelCountOn [DecidableEq V] (φ : CSP V) (declared : Finset V) : ℕ :=
  (Finset.univ.filter fun σ : declared → Bool =>
    φ.eval (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false) = true).card

/-- Declared-variable model counting is preserved by compilation to CNF. -/
theorem CSP.modelCountOn_toCNF [DecidableEq V] (φ : CSP V) (h : φ.Valid) (declared : Finset V) :
    CNF.modelCountOn φ.toCNF declared = φ.modelCountOn declared := by
  simp only [CNF.modelCountOn, modelCountOn]
  refine congrArg Finset.card (Finset.filter_congr fun σ _ => ?_)
  rw [CSP.eval_toCNF _ _ h]

/-- The number of distinct variables occurring in a CSP instance. -/
def CSP.numVars [DecidableEq V] (φ : CSP V) : ℕ := φ.vars.toFinset.card

/-- The distinct variables of a CSP instance in order of first occurrence. -/
def CSP.distinctVars [DecidableEq V] (φ : CSP V) : List V :=
  selectDistinct φ.vars (List.replicate φ.vars.length true)

/-- The total number of satisfying assignments of `φ` on its occurring variables. -/
def CSP.modelCount [DecidableEq V] (φ : CSP V) : ℕ := φ.modelCountOn φ.vars.toFinset

/-- Every variable occurring in `φ.toCNF` occurs in `φ`. -/
theorem CSP.vars_toCNF_subset [DecidableEq V] (φ : CSP V) :
    (φ.toCNF).vars.toFinset ⊆ φ.vars.toFinset := by
  intro v hv
  rw [List.mem_toFinset] at hv ⊢
  rw [CNF.mem_vars] at hv
  obtain ⟨cl, hcl, b, hlit⟩ := hv
  simp only [CSP.toCNF, List.mem_flatMap] at hcl
  obtain ⟨c, hc, hclc⟩ := hcl
  simp only [Constraint.toCNF, List.mem_map] at hclc
  obtain ⟨α, _, rfl⟩ := hclc
  simp only [CSP.vars, List.mem_flatMap]
  refine ⟨c, hc, ?_⟩
  exact mem_vars_forbiddenClause hlit

/-- Compilation to CNF does not increase the number of distinct variables. -/
theorem CSP.numVars_toCNF_le [DecidableEq V] (φ : CSP V) : (φ.toCNF).numVars ≤ φ.numVars := by
  simp only [CNF.numVars, CSP.numVars]
  exact Finset.card_le_card (CSP.vars_toCNF_subset φ)

/-- The model count of a valid CSP instance equals the model count of its compiled CNF formula
scaled by `2 ^ (φ.numVars - φ.toCNF.numVars)` to account for unconstrained variables. -/
theorem CSP.modelCount_eq_mul_toCNF_modelCount [DecidableEq V] (φ : CSP V) (h : φ.Valid) :
    φ.modelCount = 2 ^ (φ.numVars - (φ.toCNF).numVars) * (φ.toCNF).modelCount := by
  have h1 : φ.modelCount = (φ.toCNF).modelCountOn φ.vars.toFinset := by
    rw [CSP.modelCountOn_toCNF φ h, CSP.modelCount]
  rw [h1]
  exact CNF.modelCountOn_eq_mul_modelCount (φ.toCNF) φ.vars.toFinset (CSP.vars_toCNF_subset φ)

/-! ### Variable relabeling -/

/-- Relabel the variables of a constraint by a map `f`. -/
def Constraint.relabel (f : V → W) (c : Constraint V) : Constraint W :=
  ⟨c.vars.map f, c.forbidden⟩

/-- Relabel the variables of a CSP instance by a map `f`. -/
def CSP.relabel (f : V → W) (φ : CSP V) : CSP W :=
  φ.map (Constraint.relabel f)

@[simp]
theorem Constraint.vars_relabel (f : V → W) (c : Constraint V) :
    (c.relabel f).vars = c.vars.map f := rfl

@[simp]
theorem Constraint.forbidden_relabel (f : V → W) (c : Constraint V) :
    (c.relabel f).forbidden = c.forbidden := rfl

@[simp]
theorem CSP.vars_relabel (f : V → W) (φ : CSP V) :
    (CSP.relabel f φ).vars = φ.vars.map f := by
  simp only [CSP.vars, CSP.relabel, List.flatMap_map, Constraint.vars_relabel, List.map_flatMap]

@[simp]
theorem Constraint.valid_relabel (f : V → W) (c : Constraint V) :
    (c.relabel f).Valid ↔ c.Valid := by
  simp only [Constraint.Valid, Constraint.forbidden_relabel, Constraint.vars_relabel,
    List.length_map]

@[simp]
theorem CSP.valid_relabel (f : V → W) (φ : CSP V) :
    (CSP.relabel f φ).Valid ↔ φ.Valid := by
  simp only [CSP.Valid, CSP.relabel, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Constraint.valid_relabel]

@[simp]
theorem Constraint.hasWidth_relabel (f : V → W) {k : ℕ} (c : Constraint V) :
    (c.relabel f).HasWidth k ↔ c.HasWidth k := by
  simp only [Constraint.HasWidth, Constraint.vars_relabel, List.length_map]

@[simp]
theorem CSP.hasWidth_relabel (f : V → W) {k : ℕ} (φ : CSP V) :
    (CSP.relabel f φ).HasWidth k ↔ φ.HasWidth k := by
  simp only [CSP.HasWidth, CSP.relabel, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Constraint.hasWidth_relabel]

theorem forbiddenClause_relabel (f : V → W) (vars : List V) (α : List Bool) :
    (forbiddenClause vars α).relabel f = forbiddenClause (vars.map f) α := by
  simp only [forbiddenClause, Clause.relabel, List.map_zipWith, List.zipWith_map_left]
  rfl

theorem Constraint.toCNF_relabel (f : V → W) (c : Constraint V) :
    (c.relabel f).toCNF = (c.toCNF).relabel f := by
  simp only [toCNF, relabel, CNF.relabel, List.map_map, Function.comp_def, forbiddenClause_relabel]

theorem CSP.toCNF_relabel (f : V → W) :
    ∀ φ : CSP V, (CSP.relabel f φ).toCNF = (CSP.toCNF φ).relabel f
  | [] => rfl
  | c :: φ => by
    simp only [relabel, List.map_cons, toCNF, List.flatMap_cons, CNF.relabel, List.map_append]
    change (Constraint.toCNF (c.relabel f)) ++ (CSP.relabel f φ).toCNF =
      (Constraint.toCNF c).relabel f ++ (CSP.toCNF φ).relabel f
    rw [Constraint.toCNF_relabel, toCNF_relabel f φ]

/-- Rename variables of `φ` to dense indices `0, …, φ.numVars - 1`. -/
def CSP.denseRelabel [DecidableEq V] (φ : CSP V) : CSP ℕ :=
  CSP.relabel φ.distinctVars.idxOf φ

theorem CSP.toCNF_denseRelabel [DecidableEq V] (φ : CSP V) :
    φ.denseRelabel.toCNF = (φ.toCNF).relabel φ.distinctVars.idxOf :=
  CSP.toCNF_relabel _ _

/-! ### Constraint languages -/

/-- A Boolean relation of arity `a`: a list of forbidden bit vectors of length `arity`. -/
structure Relation where
  /-- The arity of the relation. -/
  arity : ℕ
  /-- The list of forbidden assignments of length `arity`. -/
  forbidden : List (List Bool)
  /-- Every forbidden assignment has length matching the relation's arity. -/
  valid : ∀ α ∈ forbidden, α.length = arity
  deriving DecidableEq

/-- A Boolean constraint language is a collection of relations. -/
abbrev Language : Type _ := List Relation

/-- A constraint language has width at most `k` when every relation in it has arity `≤ k`. -/
def Language.HasWidth (k : ℕ) (Γ : Language) : Prop :=
  ∀ R ∈ Γ, R.arity ≤ k

/-- A constraint `c` is an instance of a relation `R` when its scope has length `R.arity` and
its forbidden assignments match `R.forbidden`. -/
def Constraint.OfRelation (c : Constraint V) (R : Relation) : Prop :=
  c.vars.length = R.arity ∧ c.forbidden = R.forbidden

/-- A CSP instance `φ` is over the constraint language `Γ` when every constraint in `φ`
is an instance of some relation in `Γ`. -/
def CSP.InLanguage (Γ : Language) (φ : CSP V) : Prop :=
  ∀ c ∈ φ, ∃ R ∈ Γ, c.OfRelation R

theorem CSP.InLanguage.valid {Γ : Language} {φ : CSP V} (h : φ.InLanguage Γ) : φ.Valid := by
  intro c hc α hα
  obtain ⟨R, _, hR⟩ := h c hc
  have hα' : α ∈ R.forbidden := by rwa [← hR.2]
  rw [hR.1]
  exact R.valid α hα'

theorem CSP.InLanguage.hasWidth {Γ : Language} {k : ℕ} (hΓ : Γ.HasWidth k) {φ : CSP V}
    (h : φ.InLanguage Γ) : φ.HasWidth k := by
  intro c hc
  obtain ⟨R, hRmem, hR⟩ := h c hc
  dsimp [Constraint.HasWidth]
  rw [hR.1]
  exact hΓ R hRmem

end Cslib.Logic.PL
