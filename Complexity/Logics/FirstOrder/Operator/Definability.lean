/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Polarity

/-!
# Uniform definability by first-order formulas with operators

`Definable` certifies that one well-formed formula defines a Lean predicate across a family of
structures. The formula is independent of the family index, structure size, and assignment.
This is the semantic interface for formula synthesis: compositional rules construct syntax and
prove its formation conditions and meaning together.

The family supplies the interpretations of the operators and free relation variables. Particular
logics can therefore register rules about their own semantic operations without extending this
interface. A registered rule must produce a well-formed witness, rather than raw syntax alone.

## Main definitions

* `Definable`: uniform definability across an indexed family of structures.
* `Definable.of_formula`: use a checked formula as a definability certificate.

## Main results

* `Definable.neg`, `Definable.conj`, `Definable.disj`, `Definable.ex`, `Definable.all`:
  compositional construction of well-formed formulas.
* `Definable.ofFO`, `Definable.equal`, `Definable.rel`: atomic certificates.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

public section

universe u v w z s t

open FirstOrder Language

namespace Cslib.Logic.FO.Operator

/-- A single well-formed formula defines the predicate in every member of a family of structures.
The existential witness is outside the quantification over structures and assignments. -/
@[expose] def Definable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
    (policy : Policy shape) {ι : Type t} (M : ι → Type z) [∀ i, L.Structure (M i)]
    (I : ∀ i, Interpretation shape (M i)) {Γ : List ℕ} (ρ : ∀ i, RelEnv Γ (M i))
    {α : Type w} (P : ∀ i, (α → M i) → Prop) : Prop :=
  ∃ φ : Formula L shape Γ α, φ.wellFormed policy = true ∧
    ∀ i v, φ.Realize (I i) (ρ i) v ↔ P i v

namespace Definable

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape} {policy : Policy shape}
  {ι : Type t} {M : ι → Type z} [∀ i, L.Structure (M i)]
  {I : ∀ i, Interpretation shape (M i)} {Γ : List ℕ} {ρ : ∀ i, RelEnv Γ (M i)}
  {α β : Type w} {P Q : ∀ i, (α → M i) → Prop}

/-- Register an explicit well-formed formula through its semantics. -/
theorem of_formula (φ : Formula L shape Γ α) (hφ : φ.wellFormed policy = true) :
    Definable (L := L) policy M I ρ (fun i v => φ.Realize (I i) (ρ i) v) :=
  ⟨φ, hφ, fun _ _ => Iff.rfl⟩

/-- Replace a predicate by an equivalent one without changing its formula. -/
theorem congr (hP : Definable (L := L) policy M I ρ P) (h : ∀ i v, P i v ↔ Q i v) :
    Definable (L := L) policy M I ρ Q := by
  obtain ⟨φ, hφ, hP⟩ := hP
  exact ⟨φ, hφ, fun i v => (hP i v).trans (h i v)⟩

/-- Relabeling free variables composes the predicate with the assignment map. -/
theorem relabel (hP : Definable (L := L) policy M I ρ P) (f : α → β) :
    Definable (L := L) policy M I ρ (fun i v => P i (v ∘ f)) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  refine ⟨φ.relabel f, by simpa only [Formula.wellFormed_relabel] using hφ, ?_⟩
  intro i v
  exact (Formula.realize_relabel _ _ _ _ _).trans (hP i (v ∘ f))

/-- A native first-order formula has the same meaning in the extended logic. -/
theorem ofFO (φ : L.Formula α) :
    Definable (L := L) policy M I ρ (fun i v => φ.Realize (M := M i) v) :=
  ⟨.ofFO φ, rfl, fun _ _ => Iff.rfl⟩

/-- Negation preserves uniform definability. -/
theorem neg (hP : Definable (L := L) policy M I ρ P) :
    Definable (L := L) policy M I ρ (fun i v => ¬ P i v) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  exact ⟨.neg φ, hφ, fun i v => not_congr (hP i v)⟩

/-- Conjunction combines the two defining formulas. -/
theorem conj (hP : Definable (L := L) policy M I ρ P) (hQ : Definable (L := L) policy M I ρ Q) :
    Definable (L := L) policy M I ρ (fun i v => P i v ∧ Q i v) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  obtain ⟨ψ, hψ, hQ⟩ := hQ
  exact ⟨.conj φ ψ, by simp [Formula.wellFormed, hφ, hψ],
    fun i v => and_congr (hP i v) (hQ i v)⟩

/-- Disjunction combines the two defining formulas. -/
theorem disj (hP : Definable (L := L) policy M I ρ P) (hQ : Definable (L := L) policy M I ρ Q) :
    Definable (L := L) policy M I ρ (fun i v => P i v ∨ Q i v) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  obtain ⟨ψ, hψ, hQ⟩ := hQ
  refine ⟨φ.disj ψ, by simp [Formula.disj, Formula.wellFormed, hφ, hψ], ?_⟩
  intro i v
  exact (Formula.realize_disj _ _ _ _ _).trans (or_congr (hP i v) (hQ i v))

/-- Implication is a derived first-order connective. -/
theorem imp (hP : Definable (L := L) policy M I ρ P) (hQ : Definable (L := L) policy M I ρ Q) :
    Definable (L := L) policy M I ρ (fun i v => P i v → Q i v) :=
  (hP.neg.disj hQ).congr fun _ _ => by simp only [or_iff_not_imp_left, not_not]

/-- Existential quantification is synthesized by adding one scoped first-order variable. -/
theorem ex {P : ∀ i, M i → (α → M i) → Prop}
    (hP : Definable (L := L) policy M I ρ
      (fun i v => P i (v none) (fun a => v (some a)))) :
    Definable (L := L) policy M I ρ (fun i v => ∃ x, P i x v) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  refine ⟨.ex φ, hφ, ?_⟩
  intro i v
  exact exists_congr fun x => hP i (Option.elim · x v)

/-- Universal quantification is synthesized from a defining formula with one extra variable. -/
theorem all {P : ∀ i, M i → (α → M i) → Prop}
    (hP : Definable (L := L) policy M I ρ
      (fun i v => P i (v none) (fun a => v (some a)))) :
    Definable (L := L) policy M I ρ (fun i v => ∀ x, P i x v) := by
  obtain ⟨φ, hφ, hP⟩ := hP
  refine ⟨φ.all, hφ, ?_⟩
  intro i v
  exact (Formula.realize_all _ _ _ _).trans (forall_congr' fun x =>
    hP i (Option.elim · x v))

/-- The constant true predicate is uniformly definable, including on empty structures. -/
theorem truth : Definable (L := L) policy M I ρ (fun _ (_ : α → _) => True) :=
  (ofFO (⊤ : L.Formula α)).congr fun _ _ => FirstOrder.Language.Formula.realize_top

/-- The constant false predicate is uniformly definable. -/
theorem falsity : Definable (L := L) policy M I ρ (fun _ (_ : α → _) => False) :=
  (ofFO (⊥ : L.Formula α)).congr fun _ _ => FirstOrder.Language.Formula.realize_bot

/-- Equality of two native first-order terms is uniformly definable. -/
theorem equal (a b : L.Term α) :
    Definable (L := L) policy M I ρ (fun i v => a.realize (M := M i) v = b.realize v) := by
  apply (ofFO (a.equal b)).congr
  intro i v
  simp

/-- Equality of two free variables is an atomic synthesis rule. -/
theorem var_eq (a b : α) : Definable (L := L) policy M I ρ (fun _ v => v a = v b) :=
  equal (.var a) (.var b)

/-- A base-language relation applied to native terms is uniformly definable. -/
theorem relation {k : ℕ} (r : L.Relations k) (args : Fin k → L.Term α) :
    Definable (L := L) policy M I ρ
      (fun i v => Structure.RelMap (M := M i) r (fun j => (args j).realize v)) := by
  apply (ofFO (r.formula args)).congr
  intro i v
  simp

/-- A base-language relation applied to free variables is an atomic synthesis rule. -/
theorem relation_vars {k : ℕ} (r : L.Relations k) (args : Fin k → α) :
    Definable (L := L) policy M I ρ (fun i v => Structure.RelMap (M := M i) r (v ∘ args)) :=
  relation r (fun j => .var (args j))

/-- Unary relation application in the usual vector notation is an atomic synthesis rule. -/
theorem relation₁ (r : L.Relations 1) (a : α) :
    Definable (L := L) policy M I ρ (fun i v => Structure.RelMap (M := M i) r ![v a]) :=
  ⟨.ofFO (FO.rel₁ r a), rfl, fun _ v => FO.realize_rel₁ v r a⟩

/-- Binary relation application in the usual vector notation is an atomic synthesis rule. -/
theorem relation₂ (r : L.Relations 2) (a b : α) :
    Definable (L := L) policy M I ρ (fun i v => Structure.RelMap (M := M i) r ![v a, v b]) :=
  ⟨.ofFO (FO.rel₂ r a b), rfl, fun _ v => FO.realize_rel₂ v r a b⟩

/-- Free relation variables are also available to formula synthesis. -/
theorem rel {k : ℕ} (r : RelVar Γ k) (args : Fin k → L.Term α) :
    Definable (L := L) policy M I ρ (fun i v => (fun j => (args j).realize v) ∈ ρ i r) :=
  ⟨.rel r args, rfl, fun _ _ => Iff.rfl⟩

/-- A free relation variable applied to a tuple of free variables is uniformly definable. -/
theorem rel_vars {k : ℕ} (r : RelVar Γ k) (args : Fin k → α) :
    Definable (L := L) policy M I ρ (fun i v => (v ∘ args) ∈ ρ i r) :=
  rel r (fun j => .var (args j))

/-- Unary free-relation application in vector notation is an atomic synthesis rule. -/
theorem rel₁ (r : RelVar Γ 1) (a : α) :
    Definable (L := L) policy M I ρ (fun i v => ![v a] ∈ ρ i r) := by
  apply (rel_vars r ![a]).congr
  intro i v
  have h : v ∘ ![a] = ![v a] := by
    funext j
    exact Fin.cases rfl (fun k => k.elim0) j
  rw [h]

/-- Binary free-relation application in vector notation is an atomic synthesis rule. -/
theorem rel₂ (r : RelVar Γ 2) (a b : α) :
    Definable (L := L) policy M I ρ (fun i v => ![v a, v b] ∈ ρ i r) := by
  apply (rel_vars r ![a, b]).congr
  intro i v
  have h : v ∘ ![a, b] = ![v a, v b] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => l.elim0) k) j
  rw [h]

end Definable

end Cslib.Logic.FO.Operator
