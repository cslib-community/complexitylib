/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Basic
public import Complexity.Logics.FirstOrder.Interpretation
public import Complexity.Tactic.FirstOrder.Init
public import Mathlib.ModelTheory.Complexity

/-!
# Quantifier-free interpretations

An interpretation is quantifier-free when its domain and relation formulas are quantifier-free.
Such interpretations preserve quantifier-free formulas under pullback and compose. This is a
syntactic property, distinct from the single-input-literal restriction of a projection.

The lemmas closing quantifier-freeness goals for the formula constructors of Mathlib, the
combinators of `Complexity.Logics.FirstOrder.Basic` and interpretations are registered in the
Aesop rule set `FirstOrder`, used by the tactic `fo_qf`.

## Main definitions

* `Cslib.Logic.FO.Interpretation.IsQF`: quantifier-free domain and relation definitions.

## Main results

* `Cslib.Logic.FO.Interpretation.IsQF.onFormula`: pullback preserves quantifier-freeness.
* `Cslib.Logic.FO.Interpretation.IsQF.comp`: quantifier-free interpretations compose.
* `Cslib.Logic.FO.isAtomic_varEq`, `Cslib.Logic.FO.isAtomic_rel₁`, `Cslib.Logic.FO.isAtomic_rel₂`,
  `Cslib.Logic.FO.isQF_atVar`: the atomic combinators are atomic or quantifier-free.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

namespace FirstOrder.Language

variable {L L' : Language} {α β : Type*} {n : ℕ}

namespace BoundedFormula.IsQF

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem iInf [Finite β] (f : β → L.BoundedFormula α n) (h : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  suffices ∀ s : List β, ((s.map f).foldr (· ⊓ ·) ⊤).IsQF from this _
  intro s
  induction s with
  | nil => exact .top
  | cons b _ ih => exact (h b).inf ih

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem iSup [Finite β] (f : β → L.BoundedFormula α n) (h : ∀ b, (f b).IsQF) :
    (BoundedFormula.iSup f).IsQF := by
  suffices ∀ s : List β, ((s.map f).foldr (· ⊔ ·) ⊥).IsQF from this _
  intro s
  induction s with
  | nil => exact isQF_bot
  | cons b _ ih => exact (h b).sup ih

/-- A biimplication of quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem iff {φ ψ : L.BoundedFormula α n} (hφ : φ.IsQF) (hψ : ψ.IsQF) : (φ.iff ψ).IsQF :=
  (hφ.imp hψ).inf (hψ.imp hφ)

/-- A conditional between quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem ite {P : Prop} [Decidable P] {φ ψ : L.BoundedFormula α n}
    (hφ : φ.IsQF) (hψ : ψ.IsQF) : (if P then φ else ψ).IsQF := by
  split_ifs <;> assumption

/-- Mapping relation and function symbols preserves quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem onBoundedFormula {φ : L.BoundedFormula α n} (h : φ.IsQF) (f : L →ᴸ L') :
    (f.onBoundedFormula φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (IsAtomic.equal _ _).isQF
    | rel => exact (IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- Mapping relation and function symbols of a formula preserves quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem onFormula {φ : L.Formula α} (h : φ.IsQF) (f : L →ᴸ L') : (f.onFormula φ).IsQF :=
  h.onBoundedFormula f

end BoundedFormula.IsQF

namespace BoundedFormula

/-- A unary relation applied to a term is an atomic bounded formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₁ (r : L.Relations 1) (t : L.Term (α ⊕ Fin n)) :
    (r.boundedFormula₁ t).IsAtomic :=
  .rel _ _

/-- A binary relation applied to two terms is an atomic bounded formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (r.boundedFormula₂ t₁ t₂).IsAtomic :=
  .rel _ _

end BoundedFormula

namespace Formula

/-- Equality of two terms is an atomic formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_equal (t₁ t₂ : L.Term α) : (t₁.equal t₂).IsAtomic :=
  .equal _ _

/-- A relation symbol applied to a tuple of terms is an atomic formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel (R : L.Relations n) (ts : Fin n → L.Term α) : (R.formula ts).IsAtomic :=
  .rel _ _

/-- A unary relation applied to a term is an atomic formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₁ (r : L.Relations 1) (t : L.Term α) : (r.formula₁ t).IsAtomic :=
  .rel _ _

/-- A binary relation applied to two terms is an atomic formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : (r.formula₂ t₁ t₂).IsAtomic :=
  .rel _ _

/-- Relabeling the variables of a quantifier-free formula gives a quantifier-free formula. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_relabel {φ : L.Formula α} (h : φ.IsQF) (g : α → β) : (φ.relabel g).IsQF :=
  BoundedFormula.IsQF.relabel h _

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_iInf [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iInf f).IsQF :=
  BoundedFormula.IsQF.iInf f h

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_iSup [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iSup f).IsQF :=
  BoundedFormula.IsQF.iSup f h

end Formula

end FirstOrder.Language

namespace Cslib.Logic.FO

open FirstOrder Language

/-! ### Quantifier-free combinators -/

section Combinators

variable {L : Language} {V : Type*}

/-- Equality of two variables is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_varEq (u w : V) : (varEq (L := L) u w).IsAtomic :=
  Formula.isAtomic_equal _ _

/-- A unary relation symbol applied to a variable is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₁ (r : L.Relations 1) (u : V) : (rel₁ r u).IsAtomic :=
  Formula.isAtomic_rel₁ _ _

/-- A binary relation symbol applied to two variables is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_rel₂ (r : L.Relations 2) (u w : V) : (rel₂ r u w).IsAtomic :=
  Formula.isAtomic_rel₂ _ _ _

/-- The strict order combinator `lt r u w` is atomic. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isAtomic_lt (r : L.Relations 2) (u w : V) : (lt r u w).IsAtomic :=
  isAtomic_rel₂ r u w

/-- The weak order combinator `le r u w` is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_le (r : L.Relations 2) (u w : V) : (le r u w).IsQF :=
  (isAtomic_lt r w u).isQF.not

/-- Relabeling a quantifier-free formula to a variable keeps it quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_atVar {φ : L.Formula (Fin 1)} (h : φ.IsQF) (u : V) : (atVar φ u).IsQF :=
  Formula.isQF_relabel h _

end Combinators

namespace Interpretation

variable {L L' L'' : Language} {ι κ α : Type*}

/-- Quantifier-free interpretations have both a quantifier-free domain and quantifier-free
relation definitions. This permits arbitrary Boolean combinations of input relations. -/
structure IsQF (I : Interpretation L L' ι) : Prop where
  /-- The domain introduces no quantifiers. -/
  domain : I.domain.IsQF
  /-- No relation definition introduces quantifiers. -/
  rel : ∀ {n} (R : L'.Relations n), (I.rel R).IsQF

-- A concrete interpretation is split into its domain and relation definitions only when no
-- lemma about its construction applies. A hypothesis is split into its fields.
attribute [aesop safe 10 apply (rule_sets := [FirstOrder])] IsQF.mk
attribute [aesop safe forward (rule_sets := [FirstOrder])] IsQF.domain IsQF.rel

/-- Pulling a quantifier-free bounded formula back along a quantifier-free interpretation preserves
quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.onBoundedFormula [Finite ι] [L'.IsRelational] {I : Interpretation L L' ι}
    (hI : I.IsQF) {n : ℕ} {φ : L'.BoundedFormula α n} (hφ : φ.IsQF) :
    (I.onBoundedFormula φ).IsQF := by
  induction hφ with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact BoundedFormula.IsQF.iInf _ fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (hI.rel R).relabel _
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- Quantifier-free interpretations preserve quantifier-free formulas under pullback. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.onFormula [Finite ι] [L'.IsRelational] {I : Interpretation L L' ι}
    (hI : I.IsQF) {φ : L'.Formula α} (hφ : φ.IsQF) : (I.onFormula φ).IsQF :=
  (hI.onBoundedFormula hφ).relabel _

/-- The identity interpretation is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_id (L : Language) : (Interpretation.id L).IsQF :=
  ⟨.top, fun _ => (BoundedFormula.IsAtomic.rel _ _).isQF⟩

/-- Quantifier-free interpretations compose, including their relativized domains. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.comp [Finite ι] [Finite κ] [L'.IsRelational]
    {J : Interpretation L' L'' κ} {I : Interpretation L L' ι} (hJ : J.IsQF) (hI : I.IsQF) :
    (J.comp I).IsQF :=
  ⟨(BoundedFormula.IsQF.iInf _ fun _ => hI.domain.relabel _).inf (hI.onFormula hJ.domain),
    fun R => (hI.onFormula (hJ.rel R)).relabel _⟩

end Interpretation

end Cslib.Logic.FO
