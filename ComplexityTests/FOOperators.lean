import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint.Definability
import Complexity.Logics.FirstOrder.Operator.Relabel
import Complexity.Logics.FirstOrder.Operator.TransitiveClosure.Definability
import Complexity.Tactic.FOOperator

/-! Regression clients for scoped operators, exact least fixed points, and certified synthesis. -/

open FirstOrder Language Cslib.Logic.FO

local instance {M : Type*} : Language.empty.Structure M := Language.emptyStructure

namespace Formation

private def selfBody : LFP.RawFormula Language.empty [1] (Unit ⊕ Fin 1) :=
  .rel .here ![.var (.inr 0)]

private def self : LFP.RawFormula Language.empty [] Unit :=
  LFP.lfp selfBody ![.var ()]

example : self.wellFormed LFP.policy = true := by
  fo_wf [self, selfBody, LFP.lfp, LFP.policy, LFP.shape]

-- Negating a completed fixed point is allowed; negating its recursive relation is not.
example : (Operator.Formula.neg self).wellFormed LFP.policy = true := by
  fo_wf [self, selfBody, LFP.lfp, LFP.policy, LFP.shape]

example : (LFP.lfp (.neg selfBody) ![.var ()]).wellFormed LFP.policy = false := by
  fo_wf [selfBody, LFP.lfp, LFP.policy, LFP.shape]

example : True := by
  fail_if_success
    have : (LFP.lfp (.neg selfBody) ![.var ()]).wellFormed LFP.policy = true := by
      fo_wf [selfBody, LFP.lfp, LFP.policy, LFP.shape]
  trivial

-- The inner fixed point may depend negatively on a free outer relation. Binding that outer
-- relation as a least fixed point must reject the resulting negative recursion.
private def nestedNegative : LFP.RawFormula Language.empty [1] (Unit ⊕ Fin 1) :=
  LFP.lfp (.neg (.rel (.there .here) ![.var (.inr 0)])) ![.var (.inr 0)]

example : nestedNegative.wellFormed LFP.policy = true := by
  fo_wf [nestedNegative, LFP.lfp, LFP.policy, LFP.shape]

example : (LFP.lfp nestedNegative ![.var ()]).wellFormed LFP.policy = false := by
  fo_wf [nestedNegative, LFP.lfp, LFP.policy, LFP.shape]

private def nestedPositive : LFP.RawFormula Language.empty [1] (Unit ⊕ Fin 1) :=
  LFP.lfp
    (.disj (.rel (.there .here) ![.var (.inr 0)]) (.rel .here ![.var (.inr 0)]))
    ![.var (.inr 0)]

example : (LFP.lfp nestedPositive ![.var ()]).wellFormed LFP.policy = true := by
  fo_wf [nestedPositive, LFP.lfp, LFP.policy, LFP.shape]

-- μR.R is empty, even though every relation is a fixed point of its body.
example (b : Bool) : ¬ self.Realize LFP.interpretation Operator.RelEnv.empty (fun _ => b) := by
  have hp : LFP.Positive selfBody := by decide
  rw [self, LFP.realize_lfp selfBody hp]
  have hle := LFP.lfp_le selfBody hp Operator.RelEnv.empty (fun _ => b) (R := ∅)
    (by intro xs hx; exact hx)
  exact fun h => hle h

end Formation

namespace Weakening

private def unaryAtom : LFP.RawFormula Language.empty [1] Bool :=
  .rel .here (fun _ => .var true)

-- Reusing an outer formula under a new binary binder does not capture its unary relation.
example : (unaryAtom.weakenRel [2]).relabel (Sum.inl : Bool → Bool ⊕ Fin 2) =
    (.rel (.there .here) (fun _ => .var (.inl true)) :
      LFP.RawFormula Language.empty [2, 1] (Bool ⊕ Fin 2)) := rfl

example {L : Language} {Γ : List ℕ} {α : Type} (φ : LFP.RawFormula L Γ α) (k : ℕ) :
    LFP.Positive ((φ.weakenRel [k]).relabel (Sum.inl : α → α ⊕ Fin k)) := by
  unfold LFP.Positive
  rw [Operator.Formula.checkPolarity_relabel]
  change (φ.relabelRel (Operator.RelVar.lift [k])).checkPolarity _ _ _ = true
  rw [Operator.Formula.checkPolarity_relabelRel]
  exact Operator.Formula.checkPolarity_false _ φ true

end Weakening

namespace Parameters

private def body : LFP.RawFormula Language.empty [1] (Bool ⊕ Fin 1) :=
  .ofFO (Term.equal (.var (.inr 0)) (.var (.inl false)))

private theorem positive : LFP.Positive body := by decide

-- One formula defines equality to the captured source parameter for every assignment.
private theorem parameter_iff (v : Bool → Bool) :
    (LFP.lfp body ![.var true]).Realize LFP.interpretation Operator.RelEnv.empty v ↔
      v true = v false := by
  rw [LFP.realize_lfp body positive]
  rw [← LFP.step_lfp body positive Operator.RelEnv.empty v]
  simp [LFP.step, body]

example : ¬ (LFP.lfp body ![.var true]).Realize LFP.interpretation Operator.RelEnv.empty id := by
  simp [parameter_iff]

example : (LFP.lfp body ![.var true]).Realize LFP.interpretation Operator.RelEnv.empty
    (fun _ => false) := (parameter_iff _).2 rfl

-- The checked constructor also participates in the existing fo_realize simplification set.
example (v : Bool → Bool) :
    (LFP.Formula.lfp ⟨body, rfl⟩ positive ![.var true]).Realize
      Operator.RelEnv.empty v ↔
      ![v true] ∈ (LFP.stepHom body positive Operator.RelEnv.empty v).lfp := by
  simp only [fo_realize]
  apply iff_of_eq
  congr 1
  funext i
  simp only [Matrix.cons_val_fin_one, Term.realize_var]

end Parameters

namespace FiniteStages

private def grow : Set Bool →o Set Bool where
  toFun s := {b | b = false ∨ false ∈ s}
  monotone' := fun _ _ h _ hb => hb.imp_right (fun hs => h hs)

private theorem grow_lfp : grow.lfp = Set.univ := by
  rw [← grow.iterate_card_bot_eq_lfp]
  change (grow^[2]) ⊥ = Set.univ
  ext b
  change (b = false ∨ false = false ∨ false ∈ (∅ : Set Bool)) ↔ True
  simp

example : (grow^[1]) ∅ ≠ grow.lfp := by
  intro h
  have ht : true ∈ grow.lfp := by rw [grow_lfp]; trivial
  rw [← h] at ht
  change true = false ∨ false ∈ (∅ : Set Bool) at ht
  simp at ht

example : (grow^[9]) ∅ = Set.univ :=
  (grow.iterate_bot_eq_lfp_of_card_le (by decide)).trans grow_lfp

example (f : Set (Fin 0) →o Set (Fin 0)) : f.lfp = ∅ := by
  simpa using f.iterate_card_bot_eq_lfp.symm

-- An empty domain still has one nullary tuple, so a true nullary body needs one stage.
private def nullary : LFP.RawFormula Language.empty [0] (Empty ⊕ Fin 0) := .ofFO ⊤

example : ((LFP.step nullary (Operator.RelEnv.empty (M := Empty)) Empty.elim)^[1]) ∅ =
    (LFP.stepHom nullary (by decide) Operator.RelEnv.empty Empty.elim).lfp := by
  simpa using LFP.iterate_card_pow_eq_lfp nullary (by decide)
    (Operator.RelEnv.empty (M := Empty)) Empty.elim

example : (Fin.elim0 : Fin 0 → Empty) ∈
    (LFP.stepHom nullary (by decide) Operator.RelEnv.empty Empty.elim).lfp := by
  rw [← LFP.step_lfp nullary (by decide) Operator.RelEnv.empty Empty.elim]
  simp [LFP.step, nullary]

end FiniteStages

namespace Closure

private def falseBody : Operator.Formula Language.empty TC.shape [] (Bool ⊕ Fin 2) := .ofFO ⊥
private def vertex (b : Bool) : Fin 1 → Language.empty.Term Bool := fun _ => .var b

example : (TC.tc falseBody (TC.pair (vertex false) (vertex false))).Realize
    TC.interpretation Operator.RelEnv.empty id :=
  TC.realize_tc_refl falseBody (vertex false) Operator.RelEnv.empty id

example : ¬ (TC.tc falseBody (TC.pair (vertex false) (vertex true))).Realize
    TC.interpretation Operator.RelEnv.empty id := by
  rw [TC.realize_tc_pair]
  intro h
  rcases h.cases_head with heq | ⟨c, hc, _⟩
  · have := congrFun heq 0
    simp [vertex] at this
  · simp [falseBody] at hc

example : (TC.tc (k := 0) (.ofFO (⊥ : Language.empty.Formula (Empty ⊕ Fin 0)))
    (TC.pair (k := 0) (Fin.elim0 : Fin 0 → Language.empty.Term Empty) Fin.elim0)).Realize
    TC.interpretation (Operator.RelEnv.empty (M := Empty)) Empty.elim :=
  TC.realize_tc_refl _ _ _ _

end Closure

namespace Synthesis

variable {L : Language} {ι : Type} {M : ι → Type} [∀ i, L.Structure (M i)] {α : Type}

example (a b c : α) : Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
    (fun _ => Operator.RelEnv.empty) (fun _ v => v a = v b ∧ v b ≠ v c) := by
  fo_definable

example (a : α) : Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
    (fun _ => Operator.RelEnv.empty) (fun _ v => ∃ x, x = v a) := by
  fo_definable

example (r : L.Relations 2) (xs ys : Fin 1 → L.Term α) :
    Operator.Definable (L := L) TC.policy M (fun _ => TC.interpretation)
      (fun _ => Operator.RelEnv.empty)
      (fun i v => Relation.ReflTransGen
        (fun us vs : Fin 1 → M i => Structure.RelMap r ![us 0, vs 0])
        (fun j => (xs j).realize v) (fun j => (ys j).realize v)) := by
  fo_definable

private def seeded {A : Type} (a : A) : Set (Fin 1 → A) →o Set (Fin 1 → A) where
  toFun R := {xs | xs 0 = a ∨ xs ∈ R}
  monotone' := fun _ _ h _ hx => hx.imp_right (fun hr => h hr)

-- An ordinary Lean monotone operator is compiled to an LFP formula, including its positive body.
example (a b : α) : Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
    (fun _ => Operator.RelEnv.empty) (fun _ v => ![v b] ∈ (seeded (v a)).lfp) := by
  fo_definable

private def reachStep {A : Type} [L.Structure A] (edge : L.Relations 2) (start : A) :
    Set (Fin 1 → A) →o Set (Fin 1 → A) where
  toFun R := {ys | ys 0 = start ∨ ∃ x,
    (fun _ : Fin 1 => x) ∈ R ∧ Structure.RelMap edge ![x, ys 0]}
  monotone' := by
    intro R S h ys hy
    rcases hy with hstart | ⟨x, hx, hedge⟩
    · exact Or.inl hstart
    · exact Or.inr ⟨x, h hx, hedge⟩

-- The tactic also synthesizes the positive existential body of graph reachability.
example (edge : L.Relations 2) (a b : α) :
    Operator.Definable (L := L) LFP.policy M (fun _ => LFP.interpretation)
      (fun _ => Operator.RelEnv.empty)
      (fun _ v => ![v b] ∈ (reachStep edge (v a)).lfp) := by
  fo_definable

example : True := by
  fail_if_success
    have : Operator.PolarityDefinable (L := Language.empty) LFP.policy
        (LFP.headMark (Γ := []) (k := 1)) true
        (fun _ : Set (Fin 1 → Bool) => Bool) (fun _ => LFP.interpretation)
        (fun R => Operator.RelEnv.cons R Operator.RelEnv.empty)
        (fun R v => ¬ v ∈ R) := by
      fo_definable
  trivial

end Synthesis

namespace MixedSignature

-- This is a binding-shape/variance regression, not an implementation of regular languages.
-- A REG-style operator can have several bodies and arbitrary variance in each letter predicate.
private abbrev shape : ℕ ⊕ Unit → Operator.Shape :=
  Sum.elim LFP.shape (fun _ => ⟨0, 2, fun _ => ⟨[], 1⟩⟩)

private def policy : Operator.Policy shape where
  variance o _ := match o with | .inl _ => .positive | .inr _ => .arbitrary
  positive o _ {_} _ := match o with | .inl _ => true | .inr _ => false

private def bad : Operator.Formula Language.empty shape [] Unit :=
  .op (.inl 1)
    (fun _ => .op (.inr ()) (fun _ => .rel .here ![.var (.inr (0 : Fin 1))]) Fin.elim0)
    ![.var ()]

private def good : Operator.Formula Language.empty shape [] Unit :=
  .op (.inl 1) (fun _ => .op (.inr ()) (fun _ => .ofFO ⊤) Fin.elim0) ![.var ()]

example : bad.wellFormed policy = false := by decide
example : good.wellFormed policy = true := by decide

end MixedSignature
