/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.TransitiveClosure
public import Mathlib.ModelTheory.Graph

/-!
# Tests for pulling FO(TC) sentences back along full-tuple interpretations

The client is a two-dimensional interpretation of directed graphs. Pulling back preserves closure
polarity in both directions: a positive closure stays positive and a negated one stays negated.
Truth is preserved on both sides: a reflexive closure query holds and a closure query between
distinct numeric constants with an empty edge relation fails, before and after pullback.
-/

@[expose] public section

namespace CslibFrontierTests.FullTupleTransitiveClosure

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

/-- Pairs of vertices, with an edge between pairs whose first coordinates are adjacent. -/
noncomputable def pairs : FullTupleInterpretation Language.graph Language.graph 2 where
  rel
    | graphRel.adj => (LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
        (Relations.formula₂ adj (.var (0, 0)) (.var (1, 0)))

/-- The width-one closure body given by the edge relation. -/
noncomputable def edgeBody :
    Operator.Formula (language Language.graph) TC.shape [] (Empty ⊕ Fin (2 * 1)) :=
  .ofFO (Relations.formula₂ (Sum.inl adj : (language Language.graph).Relations 2)
    (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- The width-one closure body with no edges. -/
def emptyBody : Operator.Formula (language Language.graph) TC.shape [] (Empty ⊕ Fin (2 * 1)) :=
  .ofFO ⊥

/-- Reachability from `0` to `max`. -/
noncomputable def reach : Operator.Formula (language Language.graph) TC.shape [] Empty :=
  TC.tc edgeBody (TC.pair ![zero _] ![max _])

/-! ### Polarity is preserved in both directions -/

example : TC.Positive (pairs.onTCSentence reach) true :=
  (pairs.positive_onTCSentence reach true).2 ⟨rfl, trivial⟩

example : ¬ TC.Positive (pairs.onTCSentence reach.neg) true := fun h =>
  Bool.false_ne_true ((pairs.positive_onTCSentence reach.neg true).1 h).1

/-! ### Truth is preserved on both sides -/

/-- A reflexive closure query holds on every canonical structure after pullback. -/
example {n : ℕ} [Fact (2 ≤ n)] [Language.graph.Structure (Fin n)] :
    (pairs.onTCSentence (TC.tc emptyBody (TC.pair ![max _] ![max _]))).Realize
      (M := Fin n) TC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [pairs.realize_onTCSentence (by decide)]
  let := pairs.inputStructure (n := n)
  let : Fact (2 ≤ n ^ 2) := ⟨FullTupleInterpretation.two_le_pow (n := n) (by decide)⟩
  exact TC.realize_tc_refl _ _ _ _

/-- Without edges, `max` is not reachable from `0`, before or after pullback. -/
example {n : ℕ} [Fact (2 ≤ n)] [Language.graph.Structure (Fin n)] :
    ¬ (pairs.onTCSentence (TC.tc emptyBody (TC.pair ![zero _] ![max _]))).Realize
      (M := Fin n) TC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [pairs.realize_onTCSentence (by decide)]
  let := pairs.inputStructure (n := n)
  let : Fact (2 ≤ n ^ 2) := ⟨FullTupleInterpretation.two_le_pow (n := n) (by decide)⟩
  rw [TC.realize_tc_pair, Relation.reflTransGen_iff_eq (fun _ h => h)]
  intro h
  have h4 : 4 ≤ n ^ 2 := by
    have := (Fact.out : 2 ≤ n)
    nlinarith
  have := congrArg Fin.val (congrFun h 0)
  simp only [Matrix.cons_val_fin_one, realize_zero_val, realize_max_val] at this
  omega

end CslibFrontierTests.FullTupleTransitiveClosure
