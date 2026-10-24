/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Std.Sat.CNF.Literal

/-!
# Conjunctive normal form

Propositional formulas in conjunctive normal form over an arbitrary type of variables `V`, with
their Boolean semantics. A literal (`Std.Sat.Literal`) is a variable together with the polarity
under which it is read, a clause is a list of literals read disjunctively, and a formula is a list
of clauses read conjunctively.

Formulas are plain lists so that reductions can build them with list operations and their sizes
can be read off directly. This is why `Std.Sat.CNF`, an array-based structure built for efficient
SAT solving in `bv_decide`, is not reused; neither is `Cslib.Logic.PL.Proposition`, whose
connectives are binary and whose formulas are not in normal form. The names follow `Std.Sat.CNF`
where they overlap (`relabel`, `eval`).

Reductions to satisfiability usually build formulas over structured variables (indexed by time
steps, tape cells, and so on) and relabel them injectively at the end; `CNF.satisfiable_relabel`
says that this preserves satisfiability.

## Main definitions

* `Cslib.Logic.PL.Literal`, `Cslib.Logic.PL.Clause`, `Cslib.Logic.PL.CNF`.
* `Cslib.Logic.PL.CNF.eval`, `Cslib.Logic.PL.CNF.Satisfiable`.
* `Cslib.Logic.PL.CNF.vars`, `Cslib.Logic.PL.CNF.occurrences`: the variables of a formula in order
  of occurrence, and the number of clauses mentioning a variable.
* `Cslib.Logic.PL.CNF.relabel`: rename the variables of a formula.
* `Cslib.Logic.PL.CNF.countUnsat`: the number of clauses an assignment falsifies.
* `Cslib.Logic.PL.Clause.imp`, `Cslib.Logic.PL.Clause.impLits`: the clause `h₁ ∧ ⋯ ∧ hₙ → c`, for
  variables or literals `hᵢ`.

## Main results

* `Cslib.Logic.PL.CNF.eval_eq_true_iff`, `Cslib.Logic.PL.Clause.eval_eq_true_iff`: the semantics
  as quantifiers over clauses and literals.
* `Cslib.Logic.PL.CNF.eval_congr`: a formula only depends on its variables.
* `Cslib.Logic.PL.CNF.mem_vars`, `Cslib.Logic.PL.CNF.vars_relabel`,
  `Cslib.Logic.PL.Clause.fst_mem_of_mem_imp`: the variables of formulas and implications.
* `Cslib.Logic.PL.CNF.satisfiable_relabel`: injective relabelling preserves satisfiability.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- A literal: a variable and the polarity under which it is read. -/
abbrev Literal (V : Type*) : Type _ := Std.Sat.Literal V

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type*) : Type _ := List (Literal V)

/-- A formula in conjunctive normal form is a conjunction of clauses. -/
abbrev CNF (V : Type*) : Type _ := List (Clause V)

variable {V W : Type*}

/-- A literal `(v, b)` holds under `σ` when `σ v = b`. -/
def Literal.eval (σ : V → Bool) (l : Literal V) : Bool := σ l.1 == l.2

/-- A clause holds when one of its literals does. -/
def Clause.eval (σ : V → Bool) (c : Clause V) : Bool := c.any (Literal.eval σ)

/-- A formula holds when all of its clauses do. -/
def CNF.eval (σ : V → Bool) (φ : CNF V) : Bool := φ.all (Clause.eval σ)

/-- A formula is satisfiable when some assignment makes it true. -/
def CNF.Satisfiable (φ : CNF V) : Prop := ∃ σ : V → Bool, φ.eval σ = true

/-! ### Semantics -/

/-- The value of a literal `(v, b)`: whether `v` has the value `b`. -/
@[simp] theorem Literal.eval_mk (σ : V → Bool) (v : V) (b : Bool) :
    Literal.eval σ (v, b) = (σ v == b) := rfl

/-- A literal holds when its variable has its polarity. -/
@[simp] theorem Literal.eval_eq_true_iff (σ : V → Bool) (l : Literal V) :
    Literal.eval σ l = true ↔ σ l.1 = l.2 := by
  simp [Literal.eval]

/-- Negating a literal negates its value. -/
@[simp] theorem Literal.eval_negate (σ : V → Bool) (l : Literal V) :
    Literal.eval σ (Std.Sat.Literal.negate l) = !Literal.eval σ l := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [Std.Sat.Literal.negate]

/-- A clause holds when some literal does. -/
theorem Clause.eval_eq_true_iff (σ : V → Bool) (c : Clause V) :
    c.eval σ = true ↔ ∃ l ∈ c, σ l.1 = l.2 := by
  simp [Clause.eval, Literal.eval]

/-- The empty clause evaluates to `false`. -/
@[simp] theorem Clause.eval_nil (σ : V → Bool) : Clause.eval σ [] = false := rfl

/-- A clause `l :: c` evaluates to the disjunction of `l` and `c`. -/
@[simp] theorem Clause.eval_cons (σ : V → Bool) (l : Literal V) (c : Clause V) :
    Clause.eval σ (l :: c) = (Literal.eval σ l || Clause.eval σ c) := rfl

/-- A formula holds when every clause does. -/
theorem CNF.eval_eq_true_iff (σ : V → Bool) (φ : CNF V) :
    φ.eval σ = true ↔ ∀ c ∈ φ, c.eval σ = true := by
  simp [CNF.eval]

/-- The empty CNF formula evaluates to `true`. -/
@[simp] theorem CNF.eval_nil (σ : V → Bool) : CNF.eval σ [] = true := rfl

/-- Appending two CNF formulas evaluates to the conjunction of their evaluations. -/
@[simp] theorem CNF.eval_append (σ : V → Bool) (φ ψ : CNF V) :
    CNF.eval σ (φ ++ ψ) = (CNF.eval σ φ && CNF.eval σ ψ) := by
  simp [CNF.eval, List.all_append]

/-- A CNF formula `c :: φ` evaluates to the conjunction of `c` and `φ`. -/
@[simp] theorem CNF.eval_cons (σ : V → Bool) (c : Clause V) (φ : CNF V) :
    CNF.eval σ (c :: φ) = (Clause.eval σ c && CNF.eval σ φ) := rfl

/-- A formula made of one clause per element of a list holds when each of those clauses does. -/
theorem CNF.eval_map_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι) (f : ι → Clause V) :
    CNF.eval σ (l.map f) = true ↔ ∀ i ∈ l, (f i).eval σ = true := by
  simp [CNF.eval_eq_true_iff]

/-- A formula made of one block of clauses per element of a list holds when each block does. -/
theorem CNF.eval_flatMap_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι) (f : ι → CNF V) :
    CNF.eval σ (l.flatMap f) = true ↔ ∀ i ∈ l, CNF.eval σ (f i) = true := by
  simp only [CNF.eval_eq_true_iff, List.mem_flatMap, forall_exists_index, and_imp]
  exact ⟨fun h i hi c hc => h c i hi hc, fun h c i hi hc => h i hi c hc⟩

/-! ### Variables -/

/-- The variables of a formula, in order of occurrence and with repetitions. -/
def CNF.vars (φ : CNF V) : List V := φ.flatten.map Prod.fst

/-- The length of `φ.vars` is the sum of the lengths of the clauses of `φ`. -/
theorem CNF.length_vars (φ : CNF V) : φ.vars.length = (φ.map List.length).sum := by
  simp [CNF.vars, List.length_flatten, Function.comp_def]

/-- A formula with `m` clauses of at most `k` literals has at most `k m` occurrences of
variables. -/
theorem CNF.length_vars_le_mul_length {k : ℕ} {φ : CNF V} (h : ∀ c ∈ φ, c.length ≤ k) :
    φ.vars.length ≤ k * φ.length := by
  rw [CNF.length_vars]
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc := h c List.mem_cons_self
    have hφ := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- A variable of a formula is the variable of a literal of one of its clauses. -/
theorem CNF.mem_vars {φ : CNF V} {v : V} : v ∈ φ.vars ↔ ∃ c ∈ φ, ∃ b, (v, b) ∈ c := by
  simp only [CNF.vars, List.mem_map, List.mem_flatten, Prod.exists]
  constructor
  · rintro ⟨_, b, ⟨c, hc, hl⟩, rfl⟩
    exact ⟨c, hc, b, hl⟩
  · rintro ⟨c, hc, b, hl⟩
    exact ⟨v, b, ⟨c, hc, hl⟩, rfl⟩

/-- A formula only depends on the values of its variables. -/
theorem CNF.eval_congr {σ τ : V → Bool} {φ : CNF V} (h : ∀ v ∈ φ.vars, σ v = τ v) :
    φ.eval σ = φ.eval τ := by
  have key : ∀ c ∈ φ, ∀ l ∈ c, σ l.1 = τ l.1 := fun c hc l hl =>
    h l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩)
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  refine forall₂_congr fun c hc => ?_
  rw [Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  exact exists_congr fun l => and_congr_right fun hl => by rw [key c hc l hl]

/-- The number of clauses of a formula, counted with repetition, mentioning the variable `v`. -/
def CNF.occurrences [DecidableEq V] (φ : CNF V) (v : V) : ℕ :=
  φ.countP fun c => decide (∃ l ∈ c, l.1 = v)

/-! ### Implications -/

/-- The clause `l₁ ∧ ⋯ ∧ lₙ → c` for literals `lᵢ`, that is `¬l₁ ∨ ⋯ ∨ ¬lₙ ∨ c`. -/
def Clause.impLits (hyps : List (Literal V)) (concl : V) : Clause V :=
  hyps.map Std.Sat.Literal.negate ++ [(concl, true)]

/-- `Clause.impLits hyps concl` holds under `σ` if and only if `σ concl = true` whenever every
literal in `hyps` holds. -/
@[simp] theorem Clause.eval_impLits (σ : V → Bool) (hyps : List (Literal V)) (concl : V) :
    (Clause.impLits hyps concl).eval σ = true ↔
      ((∀ l ∈ hyps, σ l.1 = l.2) → σ concl = true) := by
  simp only [Clause.impLits, Clause.eval_eq_true_iff, List.mem_append, List.mem_map,
    List.mem_singleton]
  constructor
  · rintro ⟨l, hl | rfl, hσ⟩ hh
    · obtain ⟨h, hmem, rfl⟩ := hl
      simp [Std.Sat.Literal.negate, hh h hmem] at hσ
    · exact hσ
  · intro himp
    by_cases hall : ∀ l ∈ hyps, σ l.1 = l.2
    · exact ⟨_, Or.inr rfl, himp hall⟩
    · push Not at hall
      obtain ⟨⟨v, b⟩, hmem, hf⟩ := hall
      refine ⟨(v, !b), Or.inl ⟨(v, b), hmem, rfl⟩, ?_⟩
      cases b <;> simpa using hf

/-- The clause `h₁ ∧ ⋯ ∧ hₙ → c`, that is `¬h₁ ∨ ⋯ ∨ ¬hₙ ∨ c`. -/
def Clause.imp (hyps : List V) (concl : V) : Clause V :=
  Clause.impLits (hyps.map (·, true)) concl

/-- `Clause.imp hyps concl` holds under `σ` if and only if `σ concl = true` whenever every variable
in `hyps` is true. -/
@[simp] theorem Clause.eval_imp (σ : V → Bool) (hyps : List V) (concl : V) :
    (Clause.imp hyps concl).eval σ = true ↔ ((∀ h ∈ hyps, σ h = true) → σ concl = true) := by
  simp [Clause.imp]

/-- The variables of an implication are its hypotheses and its conclusion. -/
theorem Clause.fst_mem_of_mem_impLits {hyps : List (Literal V)} {concl : V} {l : Literal V}
    (hl : l ∈ Clause.impLits hyps concl) : (∃ h ∈ hyps, l.1 = h.1) ∨ l.1 = concl := by
  simp only [Clause.impLits, List.mem_append, List.mem_map, List.mem_singleton] at hl
  rcases hl with ⟨h, hh, rfl⟩ | rfl
  · exact Or.inl ⟨h, hh, rfl⟩
  · exact Or.inr rfl

/-- The variables of an implication are its hypotheses and its conclusion. -/
theorem Clause.fst_mem_of_mem_imp {hyps : List V} {concl : V} {l : Literal V}
    (hl : l ∈ Clause.imp hyps concl) : l.1 ∈ hyps ∨ l.1 = concl := by
  rcases Clause.fst_mem_of_mem_impLits hl with ⟨h, hh, he⟩ | he
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact Or.inl (he ▸ hv)
  · exact Or.inr he

/-! ### Relabelling -/

/-- Rename the variables of a clause along `f`. -/
def Clause.relabel (f : V → W) (c : Clause V) : Clause W := c.map (Prod.map f id)

/-- Rename the variables of a formula along `f`. -/
def CNF.relabel (f : V → W) (φ : CNF V) : CNF W := φ.map (Clause.relabel f)

/-- Relabeling a clause by `id` leaves it unchanged. -/
@[simp] theorem Clause.relabel_id (c : Clause V) : c.relabel id = c := List.map_id c

/-- Relabeling a CNF formula by `id` leaves it unchanged. -/
@[simp] theorem CNF.relabel_id (φ : CNF V) : φ.relabel id = φ :=
  List.map_id'' Clause.relabel_id φ

/-- Evaluating a relabeled clause `c.relabel f` under `σ` evaluates `c` under `σ ∘ f`. -/
@[simp] theorem Clause.eval_relabel (f : V → W) (σ : W → Bool) (c : Clause V) :
    (c.relabel f).eval σ = c.eval (σ ∘ f) := by
  induction c with
  | nil => rfl
  | cons l c ih => simp_all [Clause.relabel, Literal.eval]

/-- Evaluating a relabeled CNF formula `φ.relabel f` under `σ` evaluates `φ` under `σ ∘ f`. -/
@[simp] theorem CNF.eval_relabel (f : V → W) (σ : W → Bool) (φ : CNF V) :
    (φ.relabel f).eval σ = φ.eval (σ ∘ f) := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp_all [CNF.relabel]

/-- Relabeling a clause preserves its length. -/
@[simp] theorem Clause.length_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).length = c.length := List.length_map _

/-- Relabelling renames the variables, occurrence by occurrence. -/
theorem CNF.vars_relabel (f : V → W) (φ : CNF V) : (φ.relabel f).vars = φ.vars.map f := by
  simp [CNF.vars, CNF.relabel, Clause.relabel, List.map_flatten, Function.comp_def]

/-- Relabelling along an injective map preserves satisfiability. An assignment of the new
variables restricts to the old ones, and an assignment of the old variables extends along `f`. -/
theorem CNF.satisfiable_relabel {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ f, by simpa using hσ⟩
  · rintro ⟨σ, hσ⟩
    classical
    refine ⟨Function.extend f σ (fun _ => false), ?_⟩
    rwa [CNF.eval_relabel, Function.extend_comp hf]

/-- The number of clauses of `φ`, counted with multiplicity, that the assignment `σ` falsifies. -/
def CNF.countUnsat (σ : V → Bool) (φ : CNF V) : ℕ :=
  φ.countP fun c ↦ !c.eval σ

/-- An assignment falsifies no clause exactly when it satisfies the formula. -/
theorem CNF.countUnsat_eq_zero_iff {σ : V → Bool} {φ : CNF V} :
    φ.countUnsat σ = 0 ↔ φ.eval σ = true := by
  simp [countUnsat, List.countP_eq_zero, CNF.eval_eq_true_iff]

/-- An assignment falsifies at most all the clauses. -/
theorem CNF.countUnsat_le_length (σ : V → Bool) (φ : CNF V) : φ.countUnsat σ ≤ φ.length :=
  List.countP_le_length

end Cslib.Logic.PL
