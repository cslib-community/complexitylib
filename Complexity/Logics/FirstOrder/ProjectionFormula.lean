/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.QuantifierFree

/-!
# First-order projection formulas

A projection chooses a constant or one signed input-relation bit using only numeric information.
`ProjectionFormula N L α` separates the numeric language `N` from the input language `L`.
Its internal nodes test formulas of `N`; its leaves are constants or input literals. Consequently
neither the choice of input bit nor its polarity can depend on input-relation values.

The syntax is a decision-tree presentation of the mutually exclusive numeric cases in the
definition of first-order projections [Immerman and Landau, Definition 3.6][ImmermanLandau1995].
Numeric guards may contain quantifiers;
quantifier-free interpretations with arbitrary Boolean combinations of input relations are not
projections. The numeric vocabulary is a parameter: no interpretation of order or BIT, or
machine resource bound, is implicit in this definition.

## Main definitions

* `Cslib.Logic.FO.InputLiteral`, `Cslib.Logic.FO.InputLiteral.Realize`,
  `Cslib.Logic.FO.InputLiteral.not`, `Cslib.Logic.FO.InputLiteral.relabel`,
  `Cslib.Logic.FO.InputLiteral.toFormula`: a constant or a signed relation applied to free
  variables, its semantics, negation, variable renaming, and formula view.
* `Cslib.Logic.FO.ProjectionFormula`, `Cslib.Logic.FO.ProjectionFormula.not`,
  `Cslib.Logic.FO.ProjectionFormula.relabel`, `Cslib.Logic.FO.ProjectionFormula.subst`,
  `Cslib.Logic.FO.ProjectionFormula.IsQF`: numeric tests with input literals at the leaves,
  negation, variable renaming, substitution, and quantifier-freeness.
* `Cslib.Logic.FO.ProjectionFormula.toFormula`: the ordinary formula over the sum of the two
  languages.
* `Cslib.Logic.FO.ProjectionFormula.select`: the literal selected by the numeric structure alone.
* `Cslib.Logic.FO.ProjectionFormula.Case`, `Cslib.Logic.FO.ProjectionFormula.caseGuard`,
  `Cslib.Logic.FO.ProjectionFormula.caseLiteral`: the leaf cases of a projection formula, their
  guard formulas, and their output literals.

## Main results

* `Cslib.Logic.FO.ProjectionFormula.realize_toFormula`: realization is that of the selected literal.
* `Cslib.Logic.FO.ProjectionFormula.exists_literal`: one selected literal works for all input
  structures.
* `Cslib.Logic.FO.ProjectionFormula.existsUnique_case`: the numeric cases partition assignments.
* `Cslib.Logic.FO.ProjectionFormula.realize_iff_exists_case`: disjoint-case normal form.
* `Cslib.Logic.FO.ProjectionFormula.realize_subst`: truth-preserving substitution.
* `Cslib.Logic.FO.ProjectionFormula.realize_relabel`: variable renaming preserves realization.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995]
-/

@[expose] public section

universe u v u' v' w

namespace Cslib.Logic.FO

open FirstOrder Language Structure

/-- A projection output is a constant or a single input-relation literal. Arguments are
variables, so even the address of the input bit is independent of input relations. -/
inductive InputLiteral (L : Language.{u, v}) (α : Type*) where
  /-- A constant truth value. -/
  | const (value : Bool)
  /-- A relation on the given variables, negated exactly when `negative` is true. -/
  | rel {n : ℕ} (symbol : L.Relations n) (args : Fin n → α) (negative : Bool)

namespace InputLiteral

variable {L : Language.{u, v}} {α β M : Type*} [L.Structure M]

/-- The truth value of a constant or input literal. -/
def Realize : InputLiteral L α → (α → M) → Prop
  | .const b, _ => b = true
  | .rel R args neg, x => if neg then ¬ RelMap R (x ∘ args) else RelMap R (x ∘ args)

/-- A constant input literal `.const b` holds if and only if `b = true`. -/
@[fo_realize]
theorem realize_const (b : Bool) (x : α → M) : (const b : InputLiteral L α).Realize x ↔ b = true :=
  Iff.rfl

/-- A positive relation literal `.rel R args false` holds when `R` holds on `x ∘ args`. -/
@[fo_realize]
theorem realize_rel_false {n : ℕ} (R : L.Relations n) (args : Fin n → α) (x : α → M) :
    (rel R args false).Realize x ↔ RelMap R fun i => x (args i) :=
  Iff.rfl

/-- A negated relation literal `.rel R args true` holds when `R` does not hold on `x ∘ args`. -/
@[fo_realize]
theorem realize_rel_true {n : ℕ} (R : L.Relations n) (args : Fin n → α) (x : α → M) :
    (rel R args true).Realize x ↔ ¬ RelMap R fun i => x (args i) :=
  Iff.rfl

/-- Negate a literal, keeping its input address unchanged. -/
def not : InputLiteral L α → InputLiteral L α
  | .const b => .const (!b)
  | .rel R args neg => .rel R args (!neg)

/-- The negated literal `l.not` holds if and only if `l` does not hold. -/
@[simp, fo_realize]
theorem realize_not (l : InputLiteral L α) (x : α → M) :
    l.not.Realize x ↔ ¬ l.Realize x := by
  cases l with
  | const b => cases b <;> simp [not, Realize]
  | rel R args neg => cases neg <;> simp [not, Realize]

/-- Rename the variables of an input literal. -/
def relabel (f : α → β) : InputLiteral L α → InputLiteral L β
  | .const b => .const b
  | .rel R args neg => .rel R (f ∘ args) neg

/-- Relabeling a literal by `f` evaluates it under the assignment `x ∘ f`. -/
@[simp, fo_realize]
theorem realize_relabel (f : α → β) (l : InputLiteral L α) (x : β → M) :
    (l.relabel f).Realize x ↔ l.Realize (x ∘ f) := by
  cases l <;> rfl

/-- View an input literal as a formula. -/
def toFormula : InputLiteral L α → L.Formula α
  | .const b => if b then ⊤ else ⊥
  | .rel R args neg =>
    if neg then (R.formula fun i => .var (args i)).not else R.formula fun i => .var (args i)

/-- The formula `l.toFormula` is realized if and only if `l` is realized. -/
@[simp, fo_realize]
theorem realize_toFormula (l : InputLiteral L α) (x : α → M) :
    l.toFormula.Realize x ↔ l.Realize x := by
  cases l with
  | const b => cases b <;> simp [toFormula, Realize]
  | rel R args neg => cases neg <;> simp [toFormula, Realize, Function.comp_def]

/-- Every input literal is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_toFormula (l : InputLiteral L α) : l.toFormula.IsQF := by
  cases l with
  | const b =>
    cases b with
    | false => exact BoundedFormula.isQF_bot
    | true => exact BoundedFormula.IsQF.top
  | rel R args neg =>
    cases neg
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not

end InputLiteral

/-- A first-order projection formula: numeric tests may choose between input literals, but
input values cannot occur in the tests. `N` and `L` are separate vocabularies. -/
inductive ProjectionFormula (N : Language.{u, v}) (L : Language.{u', v'}) (α : Type*) where
  /-- A constant or a single signed input bit. -/
  | leaf (literal : InputLiteral L α)
  /-- Test a numeric formula, independently of the input relations. -/
  | branch (guard : N.Formula α) (yes no : ProjectionFormula N L α)

namespace ProjectionFormula

variable {N : Language.{u, v}} {L : Language.{u', v'}} {α β M : Type*}

/-- Translate numeric tests and input literals to the sum language. -/
def toFormula : ProjectionFormula N L α → (N.sum L).Formula α
  | .leaf l => LHom.sumInr.onFormula l.toFormula
  | .branch guard yes no =>
    let φ := LHom.sumInl.onFormula guard
    (φ ⊓ yes.toFormula) ⊔ (φ.not ⊓ no.toFormula)

open Classical in
/-- Choose the output literal using only the numeric structure and the variable assignment.
There is deliberately no `L.Structure M` parameter. -/
noncomputable def select [N.Structure M] (x : α → M) :
    ProjectionFormula N L α → InputLiteral L α
  | .leaf l => l
  | .branch guard yes no => if guard.Realize x then yes.select x else no.select x

/-- The output of a projection is exactly one literal selected without inspecting the input
relations. This statement holds for every interpretation of the input vocabulary. -/
theorem realize_toFormula [N.Structure M] [L.Structure M] (p : ProjectionFormula N L α)
    (x : α → M) : p.toFormula.Realize x ↔ (p.select x).Realize x := by
  induction p with
  | leaf l => simp [toFormula, select]
  | branch guard yes no ihy ihn =>
    simp only [toFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      LHom.realize_onFormula, ihy, ihn, select]
    split_ifs <;> tauto

/-- A leaf is realized as its literal. -/
@[fo_realize]
theorem realize_toFormula_leaf [N.Structure M] [L.Structure M] (l : InputLiteral L α)
    (x : α → M) : (leaf l : ProjectionFormula N L α).toFormula.Realize x ↔ l.Realize x := by
  simp [toFormula]

/-- A branch is realized as its first or second subtree, as its numeric guard holds or not. -/
@[fo_realize]
theorem realize_toFormula_branch [N.Structure M] [L.Structure M] (guard : N.Formula α)
    (yes no : ProjectionFormula N L α) (x : α → M) :
    (branch guard yes no).toFormula.Realize x ↔
      guard.Realize x ∧ yes.toFormula.Realize x ∨ ¬ guard.Realize x ∧ no.toFormula.Realize x := by
  simp only [toFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    LHom.realize_onFormula]

/-- A single literal works for every interpretation of the input relations. The existential
choice precedes the input structure: the selected literal cannot depend on input bits. -/
theorem exists_literal [N.Structure M] (p : ProjectionFormula N L α) (x : α → M) :
    ∃ l : InputLiteral L α, ∀ (_ : L.Structure M),
      p.toFormula.Realize x ↔ l.Realize x :=
  ⟨p.select x, fun _ => p.realize_toFormula x⟩

/-- Negate the output, leaving all numeric tests unchanged. -/
def not : ProjectionFormula N L α → ProjectionFormula N L α
  | .leaf l => .leaf l.not
  | .branch guard yes no => .branch guard yes.not no.not

/-- Selecting a literal from `p.not` negates the literal selected from `p`. -/
@[simp]
theorem select_not [N.Structure M] (p : ProjectionFormula N L α) (x : α → M) :
    p.not.select x = (p.select x).not := by
  induction p with
  | leaf => rfl
  | branch guard yes no ihy ihn => simp only [not, select, ihy, ihn]; split_ifs <;> rfl

/-- Rename every free variable in numeric tests and input literals. -/
def relabel (f : α → β) : ProjectionFormula N L α → ProjectionFormula N L β
  | .leaf l => .leaf (l.relabel f)
  | .branch guard yes no => .branch (guard.relabel f) (yes.relabel f) (no.relabel f)

/-- Selecting a literal from `p.relabel f` relabels the literal selected under `x ∘ f`. -/
@[simp]
theorem select_relabel [N.Structure M] (f : α → β) (p : ProjectionFormula N L α) (x : β → M) :
    (p.relabel f).select x = (p.select (x ∘ f)).relabel f := by
  classical
  induction p with
  | leaf => rfl
  | branch guard yes no ihy ihn =>
    simp only [relabel, select, Formula.realize_relabel, ihy, ihn]
    split_ifs <;> rfl

/-- Relabeling a projection formula by `f` evaluates its formula under `x ∘ f`. -/
@[fo_realize]
theorem realize_relabel [N.Structure M] [L.Structure M]
    (f : α → β) (p : ProjectionFormula N L α) (x : β → M) :
    (p.relabel f).toFormula.Realize x ↔ p.toFormula.Realize (x ∘ f) := by
  simp only [realize_toFormula, select_relabel, InputLiteral.realize_relabel]

/-- The formula of `p.not` holds if and only if the formula of `p` does not hold. -/
@[simp, fo_realize]
theorem realize_not [N.Structure M] [L.Structure M] (p : ProjectionFormula N L α)
    (x : α → M) : p.not.toFormula.Realize x ↔ ¬ p.toFormula.Realize x := by
  simp only [realize_toFormula, select_not, InputLiteral.realize_not]

/-- Substitute numeric tests and input literals independently. In particular, replacing each
input literal by a projection preserves the one-input-bit restriction. -/
def subst {N' L' : Language} (guard : N.Formula α → N'.Formula β)
    (literal : InputLiteral L α → ProjectionFormula N' L' β) :
    ProjectionFormula N L α → ProjectionFormula N' L' β
  | .leaf l => literal l
  | .branch g yes no => .branch (guard g) (yes.subst guard literal) (no.subst guard literal)

/-- Correct substitutions of numeric tests and input literals preserve truth. The source and
target structures need not have the same universe or vocabulary. -/
theorem realize_subst {N' L' : Language} {M' : Type*}
    [N.Structure M] [L.Structure M] [N'.Structure M'] [L'.Structure M']
    (guard : N.Formula α → N'.Formula β)
    (literal : InputLiteral L α → ProjectionFormula N' L' β)
    (x : α → M) (y : β → M')
    (hguard : ∀ g, (guard g).Realize y ↔ g.Realize x)
    (hliteral : ∀ l, (literal l).toFormula.Realize y ↔ l.Realize x)
    (p : ProjectionFormula N L α) :
    (p.subst guard literal).toFormula.Realize y ↔ p.toFormula.Realize x := by
  induction p with
  | leaf l => simpa [subst, toFormula] using hliteral l
  | branch g yes no ihy ihn =>
    simp only [subst, toFormula, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_not, LHom.realize_onFormula, hguard, ihy, ihn]

/-- All numeric tests are quantifier-free. The vocabulary is still a parameter; this property
alone does not select the classical numeric vocabulary or exclude BIT. -/
def IsQF : ProjectionFormula N L α → Prop
  | .leaf _ => True
  | .branch guard yes no => guard.IsQF ∧ yes.IsQF ∧ no.IsQF

/-- Every leaf projection formula is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isQF_leaf (l : InputLiteral L α) : (leaf l : ProjectionFormula N L α).IsQF :=
  trivial

/-- A branch of quantifier-free subformulas with a quantifier-free guard is quantifier-free. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.branch {guard : N.Formula α} {yes no : ProjectionFormula N L α} (hguard : guard.IsQF)
    (hyes : yes.IsQF) (hno : no.IsQF) : (branch guard yes no).IsQF :=
  ⟨hguard, hyes, hno⟩

/-- Quantifier-free numeric tests give a quantifier-free ordinary formula. Quantifier-freeness
of an arbitrary ordinary formula does not ensure it is a projection: it can mix input bits. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.toFormula {p : ProjectionFormula N L α} (h : p.IsQF) : p.toFormula.IsQF := by
  induction p with
  | leaf l => exact l.isQF_toFormula.onBoundedFormula _
  | branch guard yes no ihy ihn =>
    have hg := h.1.onBoundedFormula (LHom.sumInl (L' := L))
    exact (hg.inf (ihy h.2.1)).sup (hg.not.inf (ihn h.2.2))

/-- Negating a quantifier-free projection formula preserves quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.not {p : ProjectionFormula N L α} (h : p.IsQF) : p.not.IsQF := by
  induction p with
  | leaf => trivial
  | branch _ _ _ ihy ihn => exact ⟨h.1, ihy h.2.1, ihn h.2.2⟩

/-- Relabeling a quantifier-free projection formula preserves quantifier-freeness. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem IsQF.relabel {p : ProjectionFormula N L α} (h : p.IsQF) (f : α → β) :
    (p.relabel f).IsQF := by
  induction p with
  | leaf => trivial
  | branch _ _ _ ihy ihn => exact ⟨h.1.relabel _, ihy h.2.1, ihn h.2.2⟩

/-- Substituting quantifier-free guards and quantifier-free projections into a quantifier-free
projection formula preserves quantifier-freeness. -/
theorem IsQF.subst {N' L' : Language} {p : ProjectionFormula N L α} (h : p.IsQF)
    (guard : N.Formula α → N'.Formula β)
    (literal : InputLiteral L α → ProjectionFormula N' L' β)
    (hguard : ∀ g, g.IsQF → (guard g).IsQF) (hliteral : ∀ l, (literal l).IsQF) :
    (p.subst guard literal).IsQF := by
  induction p with
  | leaf l => exact hliteral l
  | branch g _ _ ihy ihn => exact ⟨hguard g h.1, ihy h.2.1, ihn h.2.2⟩

/-- The finitely many leaf occurrences of a projection formula. Distinct occurrences remain
distinct even when they carry the same literal. -/
def Case : ProjectionFormula N L α → Type
  | .leaf _ => Unit
  | .branch _ yes no => yes.Case ⊕ no.Case

/-- A projection formula has finitely many leaf cases. -/
noncomputable instance (p : ProjectionFormula N L α) : Fintype p.Case := by
  induction p with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | branch _ _ _ ihy ihn => exact inferInstanceAs (Fintype (_ ⊕ _))

/-- The conjunction of numeric tests on the path to a leaf. -/
def caseGuard : (p : ProjectionFormula N L α) → p.Case → N.Formula α
  | .leaf _, _ => ⊤
  | .branch guard yes _, .inl c => guard ⊓ yes.caseGuard c
  | .branch guard _ no, .inr c => guard.not ⊓ no.caseGuard c

/-- The literal at a leaf occurrence. -/
def caseLiteral : (p : ProjectionFormula N L α) → p.Case → InputLiteral L α
  | .leaf l, _ => l
  | .branch _ yes _, .inl c => yes.caseLiteral c
  | .branch _ _ no, .inr c => no.caseLiteral c

/-- The numeric cases form a partition, including on empty structures whenever an assignment
of the free variables exists. -/
theorem existsUnique_case [N.Structure M] (p : ProjectionFormula N L α) (x : α → M) :
    ∃! c : p.Case, (p.caseGuard c).Realize x := by
  induction p with
  | leaf l => exact ⟨(), by simp [caseGuard], fun c _ => Unit.ext c ()⟩
  | branch guard yes no ihy ihn =>
    classical
    by_cases h : guard.Realize x
    · obtain ⟨c, hc, unique⟩ := ihy
      refine ⟨Sum.inl c, by simpa [caseGuard, h] using hc, ?_⟩
      intro d hd
      cases d with
      | inl d => exact congrArg Sum.inl (unique d (by simpa [caseGuard, h] using hd))
      | inr d => simp [caseGuard, h] at hd
    · obtain ⟨c, hc, unique⟩ := ihn
      refine ⟨Sum.inr c, by simpa [caseGuard, h] using hc, ?_⟩
      intro d hd
      cases d with
      | inl d => simp [caseGuard, h] at hd
      | inr d => exact congrArg Sum.inr (unique d (by simpa [caseGuard, h] using hd))

/-- A projection is the disjunction of its mutually exclusive numeric cases, each conjoined
with one constant or signed input literal. -/
theorem realize_iff_exists_case [N.Structure M] [L.Structure M]
    (p : ProjectionFormula N L α) (x : α → M) :
    p.toFormula.Realize x ↔
      ∃ c : p.Case, (p.caseGuard c).Realize x ∧ (p.caseLiteral c).Realize x := by
  induction p with
  | leaf l => simp [Case, toFormula, caseGuard, caseLiteral]
  | branch guard yes no ihy ihn =>
    simp only [toFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      LHom.realize_onFormula, ihy, ihn, Case, Sum.exists, caseGuard, caseLiteral,
      Formula.realize_inf, Formula.realize_not]
    aesop

end ProjectionFormula

end Cslib.Logic.FO
