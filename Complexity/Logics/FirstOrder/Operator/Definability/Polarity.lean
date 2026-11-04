/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Definability
public import Complexity.Tactic.FOOperator.Init

/-!
# Formula synthesis with certified polarity

`PolarityDefinable` strengthens uniform definability by requiring a syntactic polarity
certificate for the same defining formula. This lets a fixed-point synthesis rule construct
its body from a Lean predicate while checking that recursive relation occurrences are positive.
Monotonicity is never assumed in place of this syntactic check.

The compositional rules are registered in `FODefinable`, so `fo_definable` handles these goals
as well as ordinary `Definable` goals. Negation reverses the requested polarity; marked relation
atoms are available only positively. Unmarked relation atoms are available with either sign.

## Main definitions

* `PolarityDefinable`: one well-formed, polarity-checked formula for a family of predicates.

## Main results

* `PolarityDefinable.toDefinable`: forget the additional polarity certificate.
* `PolarityDefinable.neg`, `PolarityDefinable.conj`, `PolarityDefinable.disj`,
  `PolarityDefinable.ex`, `PolarityDefinable.all`: compositional synthesis rules.
* `PolarityDefinable.head_vars`: a positive recursive atom in the nearest relation binder.
-/

public section

universe u v w z s t

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- Uniform definability with a syntactic polarity check on the defining formula itself. -/
@[expose] def PolarityDefinable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
    (policy : Policy shape) {Γ : List ℕ} (mark : Marking Γ) (sign : Bool)
    {ι : Type t} (M : ι → Type z) [∀ i, L.Structure (M i)]
    (I : ∀ i, Interpretation shape (M i)) (ρ : ∀ i, RelEnv Γ (M i))
    {α : Type w} (P : ∀ i, (α → M i) → Prop) : Prop :=
  ∃ φ : Formula L shape Γ α, φ.wellFormed policy = true ∧
    φ.checkPolarity policy.variance sign mark = true ∧
    ∀ i v, φ.Realize (I i) (ρ i) v ↔ P i v

namespace PolarityDefinable

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape} {policy : Policy shape}
  {ι : Type t} {M : ι → Type z} [∀ i, L.Structure (M i)]
  {I : ∀ i, Interpretation shape (M i)} {Γ : List ℕ} {ρ : ∀ i, RelEnv Γ (M i)}
  {mark : Marking Γ} {sign : Bool} {α : Type w} {P Q : ∀ i, (α → M i) → Prop}

/-- Forget the polarity requirement while retaining the well-formed defining formula. -/
theorem toDefinable (h : PolarityDefinable (L := L) policy mark sign M I ρ P) :
    Definable (L := L) policy M I ρ P := by
  obtain ⟨φ, hφ, _, hP⟩ := h
  exact ⟨φ, hφ, hP⟩

/-- Equivalent semantic presentations use the same syntax and polarity certificate. -/
theorem congr (hP : PolarityDefinable (L := L) policy mark sign M I ρ P)
    (h : ∀ i v, P i v ↔ Q i v) : PolarityDefinable (L := L) policy mark sign M I ρ Q := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  exact ⟨φ, hφ, hp, fun i v => (hP i v).trans (h i v)⟩

/-- Native first-order formulas are independent of all scoped relation variables. -/
theorem ofFO (φ : L.Formula α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => φ.Realize (M := M i) v) :=
  ⟨.ofFO φ, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- Negation reverses the required polarity of its body. -/
theorem neg (hP : PolarityDefinable (L := L) policy mark (!sign) M I ρ P) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ¬ P i v) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  exact ⟨.neg φ, hφ, hp, fun i v => not_congr (hP i v)⟩

/-- Conjunction preserves the polarity of both bodies. -/
theorem conj (hP : PolarityDefinable (L := L) policy mark sign M I ρ P)
    (hQ : PolarityDefinable (L := L) policy mark sign M I ρ Q) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => P i v ∧ Q i v) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  obtain ⟨ψ, hψ, hq, hQ⟩ := hQ
  exact ⟨.conj φ ψ, by simp [Formula.wellFormed, hφ, hψ],
    by simp [Formula.checkPolarity, hp, hq], fun i v => and_congr (hP i v) (hQ i v)⟩

/-- Derived disjunction preserves the polarity of both bodies. -/
theorem disj (hP : PolarityDefinable (L := L) policy mark sign M I ρ P)
    (hQ : PolarityDefinable (L := L) policy mark sign M I ρ Q) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => P i v ∨ Q i v) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  obtain ⟨ψ, hψ, hq, hQ⟩ := hQ
  refine ⟨φ.disj ψ, by simp [Formula.disj, Formula.wellFormed, hφ, hψ],
    by simp [Formula.disj, Formula.checkPolarity, hp, hq], ?_⟩
  exact fun i v => (Formula.realize_disj _ _ _ _ _).trans (or_congr (hP i v) (hQ i v))

/-- Implication reverses polarity in its antecedent and preserves it in its consequent. -/
theorem imp (hP : PolarityDefinable (L := L) policy mark (!sign) M I ρ P)
    (hQ : PolarityDefinable (L := L) policy mark sign M I ρ Q) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => P i v → Q i v) :=
  (hP.neg.disj hQ).congr fun _ _ => by simp only [or_iff_not_imp_left, not_not]

/-- Existential quantification preserves polarity while binding a fresh first-order variable. -/
theorem ex {P : ∀ i, M i → (α → M i) → Prop}
    (hP : PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => P i (v none) (fun a => v (some a)))) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∃ x, P i x v) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  exact ⟨.ex φ, hφ, hp, fun i v => exists_congr fun x => hP i (Option.elim · x v)⟩

/-- Universal quantification preserves polarity while binding a fresh first-order variable. -/
theorem all {P : ∀ i, M i → (α → M i) → Prop}
    (hP : PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => P i (v none) (fun a => v (some a)))) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => ∀ x, P i x v) := by
  obtain ⟨φ, hφ, hp, hP⟩ := hP
  refine ⟨φ.all, hφ, by simpa only [Formula.all, Formula.checkPolarity, Bool.not_not]
    using hp, ?_⟩
  exact fun i v => (Formula.realize_all _ _ _ _).trans
    (forall_congr' fun x => hP i (Option.elim · x v))

/-- The constant true predicate has either polarity. -/
theorem truth :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun _ (_ : α → _) => True) :=
  (ofFO (⊤ : L.Formula α)).congr fun _ _ => FirstOrder.Language.Formula.realize_top

/-- The constant false predicate has either polarity. -/
theorem falsity :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun _ (_ : α → _) => False) :=
  (ofFO (⊥ : L.Formula α)).congr fun _ _ => FirstOrder.Language.Formula.realize_bot

/-- Equality of native terms has either polarity. -/
theorem equal (a b : L.Term α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => a.realize (M := M i) v = b.realize v) :=
  (ofFO (a.equal b)).congr fun _ _ => by simp

/-- Equality of variables is an atomic polarity-aware synthesis rule. -/
theorem var_eq (a b : α) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun _ v => v a = v b) :=
  equal (.var a) (.var b)

/-- Native vocabulary relations have either polarity in scoped relation variables. -/
theorem relation {k : ℕ} (r : L.Relations k) (args : Fin k → L.Term α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => Structure.RelMap (M := M i) r (fun j => (args j).realize v)) :=
  (ofFO (r.formula args)).congr fun _ _ => by simp

/-- Native vocabulary relations applied to variable tuples have either polarity. -/
theorem relation_vars {k : ℕ} (r : L.Relations k) (args : Fin k → α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => Structure.RelMap (M := M i) r (v ∘ args)) :=
  relation r (fun j => .var (args j))

/-- Binary vocabulary relations in vector notation are atomic synthesis rules. -/
theorem relation₂ (r : L.Relations 2) (a b : α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => Structure.RelMap (M := M i) r ![v a, v b]) :=
  (ofFO (FO.rel₂ r a b)).congr fun _ v => FO.realize_rel₂ v r a b

/-- A scoped relation atom is positive in every marked relation. -/
theorem rel {k : ℕ} (r : RelVar Γ k) (args : Fin k → L.Term α) :
    PolarityDefinable (L := L) policy mark true M I ρ
      (fun i v => (fun j => (args j).realize v) ∈ ρ i r) :=
  ⟨.rel r args, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- An unmarked relation atom has either polarity. -/
theorem rel_unmarked {k : ℕ} (r : RelVar Γ k) (hm : mark r = false)
    (args : Fin k → L.Term α) :
    PolarityDefinable (L := L) policy mark sign M I ρ
      (fun i v => (fun j => (args j).realize v) ∈ ρ i r) :=
  ⟨.rel r args, rfl, by simp [Formula.checkPolarity, hm], fun _ _ => Iff.rfl⟩

/-- Variable arguments give the usual positive relation application. -/
theorem rel_vars {k : ℕ} (r : RelVar Γ k) (args : Fin k → α) :
    PolarityDefinable (L := L) policy mark true M I ρ (fun i v => (v ∘ args) ∈ ρ i r) :=
  rel r (fun j => .var (args j))

/-- Unmarked relation variables can be applied to variables at either polarity. -/
theorem rel_vars_unmarked {k : ℕ} (r : RelVar Γ k) (hm : mark r = false)
    (args : Fin k → α) :
    PolarityDefinable (L := L) policy mark sign M I ρ (fun i v => (v ∘ args) ∈ ρ i r) :=
  rel_unmarked r hm (fun j => .var (args j))

/-- Direct membership in the nearest bound relation is a positive atom. This form lets
synthesis start from the ordinary relation predicate, without reconstructing a relation index. -/
theorem head_vars {k : ℕ} (mark : Marking (k :: Γ)) (R : ∀ i, Set (Fin k → M i))
    (args : Fin k → α) :
    PolarityDefinable (L := L) policy mark true M I
      (fun i => RelEnv.cons (R i) (ρ i)) (fun i v => (v ∘ args) ∈ R i) :=
  rel .here (fun j => .var (args j))

attribute [aesop safe apply (rule_sets := [FODefinable])]
  ofFO neg conj disj imp ex all truth falsity equal var_eq relation relation_vars relation₂
  rel rel_unmarked rel_vars rel_vars_unmarked head_vars

end PolarityDefinable

end Cslib.Logic.FO.Operator
