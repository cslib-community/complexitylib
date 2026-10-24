/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation

/-!
# Formula-defined constants in interpreted structures

A relational interpretation can be expanded by target constants whose values are uniquely
specified by source formulas on its domain. Validity requires existence and uniqueness inside
the interpreted domain; it is a hypothesis on the source structure, not an implicit choice of
default values. For finitely many constants, the pullback existentially quantifies their tuples,
asserts their definitions and domain membership, and uses Mathlib's native constants-to-variables
equivalence followed by the existing relational pullback. Free variables and selected constants
occupy disjoint summands, so bound variables cannot capture either.

The canonical full-tuple instance and its numeric-preserving composition are supplied separately
in `Ordered.FullTuple` and `Ordered.FullTuple.Composition`. This generic extension retains explicit
validity hypotheses for arbitrary interpreted domains.

## Main definitions

* `Cslib.Logic.FO.Interpretation.WithConstants`: formulas defining additional target constants.
* `Cslib.Logic.FO.Interpretation.WithConstants.Valid`,
  `Cslib.Logic.FO.Interpretation.WithConstants.value`: unique existence and selection of the
  interpreted-domain tuple for each constant.
* `Cslib.Logic.FO.Interpretation.WithConstants.modelStructure`: the expanded interpreted structure.
* `Cslib.Logic.FO.Interpretation.WithConstants.onFormula`,
  `Cslib.Logic.FO.Interpretation.WithConstants.onSentence`: formula and sentence pullbacks.

## Main results

* `Cslib.Logic.FO.Interpretation.WithConstants.realize_onFormula`: formula truth preservation.
* `Cslib.Logic.FO.Interpretation.WithConstants.realize_onSentence`: sentence truth preservation.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definitions 1.26 and 3.3,
  and Proposition 3.5. The explicit validity predicate supplies the well-definedness of constants.
-/

@[expose] public section

universe u v u' v' w

namespace Cslib.Logic.FO.Interpretation

open FirstOrder Language Structure

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {ι γ : Type*}

/-- Additional target constants specified by formulas on the interpreted domain. -/
structure WithConstants (I : Interpretation L L' ι) (γ : Type*) where
  /-- The defining formula for each constant; domain membership is imposed separately. -/
  constant : γ → L.Formula ι

namespace WithConstants

variable {I : Interpretation L L' ι} (D : I.WithConstants γ)
  (M : Type w) [L.Structure M]

/-- Every target constant has exactly one value inside the interpreted domain. -/
def Valid : Prop := ∀ c, ∃! x : I.Model M, (D.constant c).Realize x.val

variable {M}

/-- The unique interpreted-domain tuple selected by a valid constant definition. -/
noncomputable def value (h : D.Valid M) (c : γ) : I.Model M := (h c).exists.choose

/-- The selected tuple `D.value h c` satisfies its defining formula `D.constant c`. -/
theorem value_spec (h : D.Valid M) (c : γ) :
    (D.constant c).Realize (D.value h c).val := (h c).exists.choose_spec

/-- A tuple satisfying a constant definition is its selected value. -/
theorem eq_value (h : D.Valid M) (c : γ) (x : I.Model M)
    (hx : (D.constant c).Realize x.val) : x = D.value h c :=
  (h c).unique hx (D.value_spec h c)

/-- Validity depends only on the domain formula and the constant definitions. -/
theorem Valid.of_eq {L'' : Language} {I' : Interpretation L L'' ι} {D' : I'.WithConstants γ}
    {D : I.WithConstants γ} (h : D.Valid M) (hdom : I'.domain = I.domain)
    (hcon : D'.constant = D.constant) : D'.Valid M := by
  intro c
  obtain ⟨x, hx, huniq⟩ := h c
  refine ⟨⟨x.val, by rw [hdom]; exact x.property⟩, by rw [hcon]; exact hx, fun y hy => ?_⟩
  exact Model.ext (congrArg (fun z => z.val)
    (huniq ⟨y.val, by rw [← hdom]; exact y.property⟩ (by rw [← hcon]; exact hy)))

/-- Two constant extensions with the same domain and constant formulas select the same underlying
tuples. -/
theorem val_value_eq {L'' : Language} {I' : Interpretation L L'' ι} {D' : I'.WithConstants γ}
    {D : I.WithConstants γ} (hdom : I'.domain = I.domain) (hcon : D'.constant = D.constant)
    (h : D.Valid M) (h' : D'.Valid M) (c : γ) :
    (D'.value h' c).val = (D.value h c).val :=
  congrArg (fun z => z.val)
    (D.eq_value h c ⟨(D'.value h' c).val, by rw [← hdom]; exact (D'.value h' c).property⟩
      (by rw [← hcon]; exact D'.value_spec h' c))

variable [L'.IsRelational]

/-- The interpreted relational structure expanded by its uniquely defined constants. -/
@[instance_reducible]
noncomputable def modelStructure (h : D.Valid M) : L'[[γ]].Structure (I.Model M) :=
  letI := constantsOn.structure (D.value h)
  inferInstance

/-- A target constant denotes the uniquely selected interpreted-domain tuple. -/
theorem modelStructure_coe_constant (h : D.Valid M) (c : γ) :
    letI := D.modelStructure h
    (L'.con c : I.Model M) = D.value h c := rfl

variable [Finite ι] [Finite γ] {α : Type*}

/-- Pull back a formula with target constants by quantifying their uniquely defined tuples. -/
noncomputable def onFormula (φ : L'[[γ]].Formula α) : L.Formula (α × ι) :=
  Formula.iExs (γ × ι)
    ((Formula.iInf fun c => (I.domain ⊓ D.constant c).relabel fun i => Sum.inr (c, i)) ⊓
      (I.onFormula (BoundedFormula.constantsVarsEquiv φ)).relabel
        (fun p => p.1.elim (fun c => Sum.inr (c, p.2)) (fun a => Sum.inl (a, p.2))))

/-- The pullback preserves every assignment of the original free variables. -/
theorem realize_onFormula (h : D.Valid M) (φ : L'[[γ]].Formula α) (v : α → I.Model M) :
    (D.onFormula φ).Realize (fun p => (v p.1).val p.2) ↔
      letI := D.modelStructure h
      φ.Realize v := by
  let := constantsOn.structure (D.value h)
  change _ ↔ φ.Realize v
  have hsem : (I.onFormula (BoundedFormula.constantsVarsEquiv φ)).Realize
      (fun p => (Sum.elim (D.value h) v p.1).val p.2) ↔ φ.Realize v := by
    rw [I.realize_onFormula]
    exact BoundedFormula.realize_constantsVarsEquiv
  simp only [onFormula, Formula.realize_iExs, Formula.realize_inf, Formula.realize_iInf,
    Formula.realize_relabel]
  constructor
  · rintro ⟨xs, hxs, hφ⟩
    have heq : xs = fun p => (D.value h p.1).val p.2 := by
      funext p
      have hc := D.eq_value h p.1 ⟨fun i => xs (p.1, i), (hxs p.1).1⟩ (hxs p.1).2
      exact congrArg (fun x : I.Model M => x.val p.2) hc
    apply hsem.mp
    subst xs
    convert hφ using 1
    funext p
    rcases p with ⟨c | a, i⟩ <;> rfl
  · intro hφ
    refine ⟨fun p => (D.value h p.1).val p.2, ?_, ?_⟩
    · exact fun c => ⟨(D.value h c).property, D.value_spec h c⟩
    · convert hsem.mpr hφ using 1
      funext p
      rcases p with ⟨c | a, i⟩ <;> rfl

/-- Pull back a sentence containing the defined target constants. -/
noncomputable def onSentence (φ : L'[[γ]].Sentence) : L.Sentence :=
  (D.onFormula φ).relabel Prod.fst

/-- Truth of a sentence is preserved by the constant-aware interpretation. -/
theorem realize_onSentence (h : D.Valid M) (φ : L'[[γ]].Sentence) :
    M ⊨ D.onSentence φ ↔ letI := D.modelStructure h; I.Model M ⊨ φ := by
  let := D.modelStructure h
  rw [onSentence, Sentence.Realize, Formula.realize_relabel]
  convert D.realize_onFormula h φ (fun x => x.elim) using 1
  · exact iff_of_eq (congrArg (D.onFormula φ).Realize (Subsingleton.elim _ _))
  · rw [Sentence.Realize]
    exact iff_of_eq (congrArg (Formula.Realize (M := I.Model M) φ) (Subsingleton.elim _ _))

end WithConstants
end Cslib.Logic.FO.Interpretation
