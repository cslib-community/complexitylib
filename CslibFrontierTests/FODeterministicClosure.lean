import CslibFrontier.Logics.FirstOrder.Ordered.DeterministicTransitiveClosure

/-! Regression clients for deterministic transitive closure and its embedding into FO(TC). -/

open FirstOrder Language Cslib.Logic.FO

local instance {M : Type*} : Language.empty.Structure M := Language.emptyStructure

namespace DeterministicClosure

/-- Every pair of vertices is an edge. -/
private def fullBody : Operator.Formula Language.empty TC.shape [] (Bool ⊕ Fin 2) := .ofFO ⊤

/-- The single edge `false → true`. -/
private def stepBody : Operator.Formula Language.empty TC.shape [] (Bool ⊕ Fin 2) :=
  .ofFO ((Term.var (.inr 0)).equal (.var (.inl false)) ⊓
    (Term.var (.inr 1)).equal (.var (.inl true)))

private def vertex (b : Bool) : Fin 1 → Language.empty.Term Bool := fun _ => .var b

private theorem pair_zero (us ws : Fin 1 → Bool) : TC.pair us ws 0 = us 0 := rfl

private theorem pair_one (us ws : Fin 1 → Bool) : TC.pair us ws 1 = ws 0 := rfl

private theorem realize_stepBody (I : Operator.Interpretation TC.shape Bool)
    (us ws : Fin 1 → Bool) :
    stepBody.Realize I Operator.RelEnv.empty (Sum.elim id (TC.pair us ws)) ↔
      us 0 = false ∧ ws 0 = true := by
  simp [stepBody, pair_zero, pair_one]

-- Closure follows the edge `false → true` of the complete graph on `Bool`.
example : (TC.tc fullBody (TC.pair (vertex false) (vertex true))).Realize
    TC.interpretation Operator.RelEnv.empty id :=
  TC.realize_tc_of_body _ _ _ _ _ (by simp [fullBody])

-- Deterministic closure does not: `false` has two successors, so it has no unique one.
private theorem not_dtc_full : ¬ (TC.tc fullBody (TC.pair (vertex false) (vertex true))).Realize
    DTC.interpretation Operator.RelEnv.empty id := by
  rw [DTC.realize_tc_pair]
  intro h
  rcases h.cases_head with heq | ⟨c, hc, _⟩
  · have := congrFun heq 0
    simp [vertex] at this
  · have h₁ := hc.2 (fun _ => false) (by simp [fullBody])
    have h₂ := hc.2 (fun _ => true) (by simp [fullBody])
    have := congrFun (h₁.trans h₂.symm) 0
    simp at this

-- On the subgraph with the single edge `false → true`, the successor is unique: deterministic
-- closure is not monotone in its body.
example : (TC.tc stepBody (TC.pair (vertex false) (vertex true))).Realize
    DTC.interpretation Operator.RelEnv.empty id := by
  rw [DTC.realize_tc_pair]
  refine .single ⟨(realize_stepBody _ _ _).2 ⟨rfl, rfl⟩, fun zs hz => ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  exact ((realize_stepBody _ _ _).1 hz).2

-- Negated deterministic closure: `true` has no successor, so `false` is unreachable from it.
example : (Operator.Formula.neg (TC.tc stepBody (TC.pair (vertex true) (vertex false)))).Realize
    DTC.interpretation Operator.RelEnv.empty id := by
  rw [Operator.Formula.realize_neg, DTC.realize_tc_pair]
  intro h
  rcases h.cases_head with heq | ⟨c, hc, _⟩
  · have := congrFun heq 0
    simp [vertex] at this
  · have := ((realize_stepBody _ _ _).1 hc.1).1
    simp [vertex] at this

-- Width zero: the empty tuple reaches itself, even on an empty domain.
example : (TC.tc (k := 0) (.ofFO (⊥ : Language.empty.Formula (Empty ⊕ Fin 0)))
    (TC.pair (k := 0) (Fin.elim0 : Fin 0 → Language.empty.Term Empty) Fin.elim0)).Realize
    DTC.interpretation (Operator.RelEnv.empty (M := Empty)) Empty.elim :=
  DTC.realize_tc_refl _ _ _ _

-- The FO(TC) translation agrees with deterministic closure on the separating example.
example : ¬ (DTC.toTC (TC.tc fullBody (TC.pair (vertex false) (vertex true)))).Realize
    TC.interpretation Operator.RelEnv.empty id := by
  rw [DTC.realize_toTC]
  exact not_dtc_full

-- Definability chain FO ⊆ FO(DTC) ⊆ FO(TC).
example {L : Language} {K : Ordered.Query L} (h : Ordered.Definable K) :
    Ordered.TCDefinable K :=
  h.dtcDefinable.tcDefinable

end DeterministicClosure
