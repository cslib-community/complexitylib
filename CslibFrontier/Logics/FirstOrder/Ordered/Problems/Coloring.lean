/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Reachability
public import CslibFrontier.Logics.FirstOrder.Problems.Coloring
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Tagged
import Mathlib.Tactic.FinCases

/-!
# Canonical ordered 3-colorability and the `SAT ≤_qfp 3COL` projection

Over Mathlib's language of graphs `FirstOrder.Language.graph`, `Ordered.ThreeColorable` and
`Ordered.SimpleThreeColorable` are the canonical ordered queries corresponding to
`FO.graph.ThreeColorable` (3-colorable directed graphs, loops forbidden by proper coloring) and
`FO.graph.SimpleThreeColorable` (3-colorable simple loopless undirected graphs) on universes `Fin n`
with `2 ≤ n`, sharing `Ordered.graphVocabulary` with `Ordered.Reach`.

On canonically ordered structures, `Ordered.SAT` reduces directly to **both**
`Ordered.SimpleThreeColorable` and `Ordered.ThreeColorable` by one dimension-6 **quantifier-free
projection** (`satToColoringInterpretation`, without `BIT`):
* Using `4` binary `{0, max}` tag coordinates and `2` payload coordinates `(c, x)` (`4 + 2 = 6`),
  `13` vertex roles encode a palette triangle `(pT, pF, pB)`, variable literal switches
  `(vPos x, vNeg x)`, active-literal gates `(actPos c x, actNeg c x)`, and two successor-linked
  chains of 3-vertex OR-gates `(posG0, posG1, posOut)` and `(negG0, negG1, negOut)` scanning
  positive and negative literals `0 .. max` of each clause `c`.
* Input literals appear **only** on the edges `pT(0, 0) ~ actPos(c, x)` (guarded by `¬ pos(c, x)`)
  and `pT(0, 0) ~ actNeg(c, x)` (guarded by `¬ neg(c, x)`), so every output edge inspects at most
  one input bit; all other edges are quantifier-free numeric formulas in `qfNumericLanguage`.
* `symmPairBinaryTag` symmetrizes a strictly upper-triangular edge table, so the output graph models
  `Theory.simpleGraph` unconditionally on every input structure `M`.

For existential second-order definability and native `NP` membership at `encStructure`, see
`CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems`.

## Main definitions

* `Cslib.Logic.FO.Ordered.ThreeColorable`, `Cslib.Logic.FO.Ordered.SimpleThreeColorable`: canonical
  ordered 3-colorability queries over `FirstOrder.Language.graph`.
* `Cslib.Logic.FO.Ordered.satToColoringFormula`,
  `Cslib.Logic.FO.Ordered.satToColoringInterpretation`: dimension-6 `BIT`-free quantifier-free
  projection from `Ordered.SAT` to simple 3-colorable graphs.

## Main results

* `Cslib.Logic.FO.Ordered.isQFProjection_satToColoringInterpretation`:
  `satToColoringInterpretation` is a quantifier-free projection (`IsQFProjection`).
* `Cslib.Logic.FO.Ordered.simpleGraph_satToColoring`: every image of `satToColoringInterpretation`
  is a simple loopless undirected graph (`⊨ Theory.simpleGraph`).
* `Cslib.Logic.FO.Ordered.mem_SimpleThreeColorable_satToColoringInterpretation`,
  `Cslib.Logic.FO.Ordered.mem_ThreeColorable_satToColoringInterpretation`: exact reduction
  equivalence on all ordered `FO.cnf` structures.
* `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_SimpleThreeColorable`,
  `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeColorable`: `Ordered.SAT` quantifier-free
  projection reduces to `Ordered.SimpleThreeColorable` and `Ordered.ThreeColorable`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure CategoryTheory

/-- **Canonical ordered 3-colorability** (general graph structures, loops allowed in the input
signature): an ordered `Language.graph` structure belongs to `ThreeColorable` when its vertices
admit a proper 3-coloring. -/
@[expose] def ThreeColorable : Query Language.graph :=
  {M | FO.graph.Colorable 3 M}

/-- **Canonical ordered simple 3-colorability**: an ordered `Language.graph` structure belongs to
`SimpleThreeColorable` when it is symmetric and irreflexive (`⊨ Theory.simpleGraph`) and admits a
proper 3-coloring. -/
@[expose] def SimpleThreeColorable : Query Language.graph :=
  {M | M ⊨ Theory.simpleGraph ∧ FO.graph.Colorable 3 M}

theorem mem_ThreeColorable {M : Structure Language.graph} :
    M ∈ ThreeColorable ↔ FO.graph.Colorable 3 M :=
  Iff.rfl

theorem mem_SimpleThreeColorable {M : Structure Language.graph} :
    M ∈ SimpleThreeColorable ↔ M ⊨ Theory.simpleGraph ∧ FO.graph.Colorable 3 M :=
  Iff.rfl

/-! ### Successor OR-gate `SAT ≤_qfp SimpleThreeColorable` gadget (`k = 6`) -/

section SatToColoring

private inductive ColorTag : Type
  | pT
  | pF
  | pB
  | vPos
  | vNeg
  | actPos
  | actNeg
  | posG0
  | posG1
  | posOut
  | negG0
  | negG1
  | negOut
  deriving DecidableEq

private def colorTagRank : ColorTag → ℕ
  | .pT => 0
  | .pF => 1
  | .pB => 2
  | .vPos => 3
  | .vNeg => 4
  | .actPos => 5
  | .actNeg => 6
  | .posG0 => 7
  | .posG1 => 8
  | .posOut => 9
  | .negG0 => 10
  | .negG1 => 11
  | .negOut => 12

private def colorCode : ColorTag → Fin 4 → Bool
  | .pT => ![false, false, false, false]
  | .pF => ![false, false, false, true]
  | .pB => ![false, false, true, false]
  | .vPos => ![false, false, true, true]
  | .vNeg => ![false, true, false, false]
  | .actPos => ![false, true, false, true]
  | .actNeg => ![false, true, true, false]
  | .posG0 => ![false, true, true, true]
  | .posG1 => ![true, false, false, false]
  | .posOut => ![true, false, false, true]
  | .negG0 => ![true, false, true, false]
  | .negG1 => ![true, false, true, true]
  | .negOut => ![true, true, false, false]

private theorem colorCode_injective : Function.Injective colorCode := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  cases a <;> cases b <;> simp_all [colorCode]

private def allColorTags : List ColorTag :=
  [.pT, .pF, .pB, .vPos, .vNeg, .actPos, .actNeg,
   .posG0, .posG1, .posOut, .negG0, .negG1, .negOut]

private theorem mem_allColorTags (t : ColorTag) : t ∈ allColorTags := by
  cases t <;> simp [allColorTags]

private abbrev cPay0 : Fin (4 + 2) := Fin.natAdd 4 0
private abbrev cPay1 : Fin (4 + 2) := Fin.natAdd 4 1

private def guardOrigin0 : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  QFNumeric.isZero (0, cPay0) ⊓ QFNumeric.isZero (0, cPay1)

private def guardOriginBoth : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  guardOrigin0 ⊓ (QFNumeric.isZero (1, cPay0) ⊓ QFNumeric.isZero (1, cPay1))

private def guardOriginToVar : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  guardOrigin0 ⊓ QFNumeric.isZero (1, cPay0)

private def guardOriginToZero1 : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  guardOrigin0 ⊓ QFNumeric.isZero (1, cPay1)

private def guardOriginToMax1 : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  guardOrigin0 ⊓ QFNumeric.isMax (1, cPay1)

private def guardSameVar0 : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  QFNumeric.isZero (0, cPay0) ⊓
    (QFNumeric.isZero (1, cPay0) ⊓ QFNumeric.varEq (0, cPay1) (1, cPay1))

private def guardVarToAct : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  QFNumeric.isZero (0, cPay0) ⊓ QFNumeric.varEq (0, cPay1) (1, cPay1)

private def guardSameCell : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  QFNumeric.varEq (0, cPay0) (1, cPay0) ⊓ QFNumeric.varEq (0, cPay1) (1, cPay1)

private def guardBridgeLink : qfNumericLanguage.Formula (Fin 2 × Fin (4 + 2)) :=
  QFNumeric.varEq (0, cPay0) (1, cPay0) ⊓
    (QFNumeric.isMax (0, cPay1) ⊓ QFNumeric.isZero (1, cPay1))

private theorem isQF_guardOrigin0 : guardOrigin0.IsQF :=
  (QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _)

private theorem isQF_guardOriginBoth : guardOriginBoth.IsQF :=
  isQF_guardOrigin0.inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _))

private theorem isQF_guardOriginToVar : guardOriginToVar.IsQF :=
  isQF_guardOrigin0.inf (QFNumeric.isQF_isZero _)

private theorem isQF_guardOriginToZero1 : guardOriginToZero1.IsQF :=
  isQF_guardOrigin0.inf (QFNumeric.isQF_isZero _)

private theorem isQF_guardOriginToMax1 : guardOriginToMax1.IsQF :=
  isQF_guardOrigin0.inf (QFNumeric.isQF_isMax _)

private theorem isQF_guardSameVar0 : guardSameVar0.IsQF :=
  (QFNumeric.isQF_isZero _).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_varEq _ _))

private theorem isQF_guardVarToAct : guardVarToAct.IsQF :=
  (QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_varEq _ _)

private theorem isQF_guardSameCell : guardSameCell.IsQF :=
  (QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_varEq _ _)

private theorem isQF_guardBridgeLink : guardBridgeLink.IsQF :=
  (QFNumeric.isQF_varEq _ _).inf ((QFNumeric.isQF_isMax _).inf (QFNumeric.isQF_isZero _))

/-- Combined intra-gate triangle edge `(c, x) ~ (c, x)` and successor step link
`g0(c, x + 1) ~ out(c, x)`. -/
private def gateG0OutFormula :
    ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2)) :=
  .guardAnd (QFNumeric.varEq (0, cPay0) (1, cPay0))
    (.branch (QFNumeric.varEq (0, cPay1) (1, cPay1))
      (.const true)
      (.guardAnd (QFNumeric.varSucc (1, cPay1) (0, cPay1)) (.const true)))

private theorem isQF_gateG0OutFormula : gateG0OutFormula.IsQF :=
  ProjectionFormula.IsQF.guardAnd (QFNumeric.isQF_varEq _ _)
    ⟨QFNumeric.isQF_varEq _ _, ProjectionFormula.isQF_const true,
      ProjectionFormula.IsQF.guardAnd (QFNumeric.isQF_varSucc _ _)
        (ProjectionFormula.isQF_const true)⟩

/-- Strictly upper-triangular edge specification (`colorTagRank t₁ < colorTagRank t₂`). -/
private def upperColorEdge : ColorTag → ColorTag →
    Option (ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2)))
  | .pT, .pF => some (.guardAnd guardOriginBoth (.const true))
  | .pT, .pB => some (.guardAnd guardOriginBoth (.const true))
  | .pT, .actPos =>
    some (.guardAnd guardOrigin0 (.negLit FO.cnf.pos ![(1, cPay0), (1, cPay1)]))
  | .pT, .actNeg =>
    some (.guardAnd guardOrigin0 (.negLit FO.cnf.neg ![(1, cPay0), (1, cPay1)]))
  | .pF, .pB => some (.guardAnd guardOriginBoth (.const true))
  | .pF, .vPos => some (.guardAnd guardOriginToVar (.const true))
  | .pF, .vNeg => some (.guardAnd guardOriginToVar (.const true))
  | .pF, .posG0 => some (.guardAnd guardOriginToZero1 (.const true))
  | .pF, .negOut => some (.guardAnd guardOriginToMax1 (.const true))
  | .pB, .actPos => some (.guardAnd guardOrigin0 (.const true))
  | .pB, .actNeg => some (.guardAnd guardOrigin0 (.const true))
  | .pB, .posOut => some (.guardAnd guardOrigin0 (.const true))
  | .pB, .negOut => some (.guardAnd guardOrigin0 (.const true))
  | .vPos, .vNeg => some (.guardAnd guardSameVar0 (.const true))
  | .vPos, .actPos => some (.guardAnd guardVarToAct (.const true))
  | .vNeg, .actNeg => some (.guardAnd guardVarToAct (.const true))
  | .actPos, .posG1 => some (.guardAnd guardSameCell (.const true))
  | .actNeg, .negG1 => some (.guardAnd guardSameCell (.const true))
  | .posG0, .posG1 => some (.guardAnd guardSameCell (.const true))
  | .posG0, .posOut => some gateG0OutFormula
  | .posG1, .posOut => some (.guardAnd guardSameCell (.const true))
  | .posOut, .negG0 => some (.guardAnd guardBridgeLink (.const true))
  | .negG0, .negG1 => some (.guardAnd guardSameCell (.const true))
  | .negG0, .negOut => some gateG0OutFormula
  | .negG1, .negOut => some (.guardAnd guardSameCell (.const true))
  | _, _ => none

private theorem rank_lt_of_upperColorEdge {t₁ t₂ : ColorTag}
    {p : ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2))}
    (h : upperColorEdge t₁ t₂ = some p) : colorTagRank t₁ < colorTagRank t₂ := by
  cases t₁ <;> cases t₂ <;> simp [upperColorEdge, colorTagRank] at h ⊢

private theorem asym_upperColorEdge (t₁ t₂ : ColorTag)
    (p : ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2)))
    (h : upperColorEdge t₁ t₂ = some p) : upperColorEdge t₂ t₁ = none := by
  have h12 := rank_lt_of_upperColorEdge h
  cases h21 : upperColorEdge t₂ t₁ with
  | none => rfl
  | some q => exact False.elim (Nat.lt_asymm h12 (rank_lt_of_upperColorEdge h21))

private theorem isQF_upperColorEdge (t₁ t₂ : ColorTag)
    (p : ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2)))
    (h : upperColorEdge t₁ t₂ = some p) : p.IsQF := by
  have htrue := ProjectionFormula.isQF_const (N := qfNumericLanguage) (L := FO.cnf)
    (α := Fin 2 × Fin (4 + 2)) true
  cases t₁ <;> cases t₂ <;> simp only [upperColorEdge, Option.some.injEq] at h
  all_goals try cases h
  all_goals first
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOriginBoth htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOrigin0 (ProjectionFormula.isQF_negLit _ _)
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOrigin0 htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOriginToVar htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOriginToZero1 htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardOriginToMax1 htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardSameVar0 htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardVarToAct htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardSameCell htrue
    | exact ProjectionFormula.IsQF.guardAnd isQF_guardBridgeLink htrue
    | exact isQF_gateG0OutFormula

/-- Quantifier-free projection formulas for the dimension-6 `SAT → SimpleThreeColorable`
reduction. -/
noncomputable def satToColoringFormula :
    ∀ {r : ℕ}, Language.graph.Relations r →
      ProjectionFormula qfNumericLanguage FO.cnf (Fin r × Fin 6)
  | _, .adj => symmPairBinaryTag (m := 2) colorCode allColorTags upperColorEdge

/-- Dimension-6 full-tuple interpretation reducing `Ordered.SAT` to `Ordered.SimpleThreeColorable`
and `Ordered.ThreeColorable` without `BIT`. -/
noncomputable def satToColoringInterpretation :
    FullTupleInterpretation FO.cnf Language.graph 6 :=
  FullTupleInterpretation.ofQFProjection satToColoringFormula

theorem isQFProjection_satToColoringInterpretation :
    satToColoringInterpretation.IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection satToColoringFormula fun R => ?_
  cases R
  exact isQF_symmPairBinaryTag (m := 2) colorCode allColorTags isQF_upperColorEdge

/-! ### Simple-graph property and 3-coloring equivalence -/

private def mkVertex {n : ℕ} [Fact (2 ≤ n)] (t : ColorTag) (c x : Fin n) :
    Fin (4 + 2) → Fin n :=
  mkTagged (colorCode t) ![c, x]

private theorem pair_arg1_pay {n : ℕ} (u v : Fin (4 + 2) → Fin n) :
    (fun i : Fin 2 =>
      (![u, v] (![((1 : Fin 2), cPay0), (1, cPay1)] i).1)
        (![((1 : Fin 2), cPay0), (1, cPay1)] i).2) = ![v cPay0, v cPay1] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i' => have hi : i' = 0 := Subsingleton.elim _ _; subst hi; rfl

private theorem simpleGraph_tupleStructure (M : Structure FO.cnf) :
    letI := satToColoringInterpretation.tupleStructure M
    (Fin (4 + 2) → Fin M.size) ⊨ Theory.simpleGraph := by
  let _ := satToColoringInterpretation.tupleStructure M
  rw [Theory.simpleGraph_model_iff]
  refine ⟨⟨fun u hu => ?_⟩, ⟨fun u v huv => ?_⟩⟩
  · rw [satToColoringInterpretation,
      FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToColoringFormula] at hu
    exact irrefl_symmPairBinaryTag (m := 2) colorCode_injective allColorTags asym_upperColorEdge
      u hu
  · rw [satToColoringInterpretation,
      FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToColoringFormula] at huv ⊢
    exact symm_symmPairBinaryTag (m := 2) colorCode_injective allColorTags asym_upperColorEdge huv

private theorem directed_edge_to_adj (M : Structure FO.cnf) {t₁ t₂ : ColorTag}
    {p : ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2))}
    (h12 : upperColorEdge t₁ t₂ = some p) (c₁ x₁ c₂ x₂ : Fin M.size)
    (hp : p.toFormula.Realize
      (fun q : Fin 2 × Fin (4 + 2) => (![mkVertex t₁ c₁ x₁, mkVertex t₂ c₂ x₂] q.1) q.2)) :
    (satToColoringInterpretation.tupleStructure M).RelMap Language.adj
      ![mkVertex t₁ c₁ x₁, mkVertex t₂ c₂ x₂] := by
  rw [satToColoringInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToColoringFormula,
    realize_symmPairBinaryTag (m := 2) colorCode_injective allColorTags asym_upperColorEdge]
  exact .inl ⟨t₁, mem_allColorTags t₁, t₂, mem_allColorTags t₂,
    (matchBinaryTag_mkTagged _ _ _).mpr rfl, (matchBinaryTag_mkTagged _ _ _).mpr rfl,
    p, h12, hp⟩

/-! ### OR-gate arithmetic on `Fin 3` -/

private def orGate0 (u v : Fin 3) : Fin 3 :=
  if u = 0 then 1 else if v = 0 then 2 else 0

private def orGate1 (u v : Fin 3) : Fin 3 :=
  if u = 0 then 2 else if v = 0 then 1 else 2

private def orGateOut (u v : Fin 3) : Fin 3 :=
  if u = 0 then 0 else if v = 0 then 0 else 1

private theorem orGate_in0_ne : ∀ u v : Fin 3, u ≠ 2 → v ≠ 2 → u ≠ orGate0 u v := by decide
private theorem orGate_in1_ne : ∀ u v : Fin 3, u ≠ 2 → v ≠ 2 → v ≠ orGate1 u v := by decide
private theorem orGate_g0_ne_g1 : ∀ u v : Fin 3, u ≠ 2 → v ≠ 2 → orGate0 u v ≠ orGate1 u v := by
  decide
private theorem orGate_g0_ne_out : ∀ u v : Fin 3, u ≠ 2 → v ≠ 2 → orGate0 u v ≠ orGateOut u v := by
  decide
private theorem orGate_g1_ne_out : ∀ u v : Fin 3, u ≠ 2 → v ≠ 2 → orGate1 u v ≠ orGateOut u v := by
  decide

private theorem fin_three_eq_of_ne :
    ∀ x y z w : Fin 3, x ≠ w → y ≠ w → x ≠ y → z ≠ x → z ≠ y → z = w := by
  intro x y z w
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;> decide

private theorem color_or_of_ne {t f b z : Fin 3}
    (htf : t ≠ f) (htb : t ≠ b) (hfb : f ≠ b) (hz : z ≠ b) : z = t ∨ z = f := by
  by_cases hzt : z = t
  · exact .inl hzt
  · exact .inr (fin_three_eq_of_ne t b z f htf hfb.symm htb hzt hz)

private theorem orGate_forces {t f in0 in1 g0 g1 gOut : Fin 3} (htf : t ≠ f)
    (hin0 : in0 = t ∨ in0 = f) (hin1 : in1 = t ∨ in1 = f)
    (he0 : in0 ≠ g0) (he1 : in1 ≠ g1)
    (hg01 : g0 ≠ g1) (hg0o : g0 ≠ gOut) (hg1o : g1 ≠ gOut)
    (hout : gOut = t) : in0 = t ∨ in1 = t := by
  by_contra hneither
  push Not at hneither
  have hf0 : in0 = f := hin0.resolve_left hneither.1
  have hf1 : in1 = f := hin1.resolve_left hneither.2
  rw [hf0] at he0
  rw [hf1] at he1
  have hgo_f : gOut = f :=
    fin_three_eq_of_ne g0 g1 gOut f he0.symm he1.symm hg01 hg0o.symm hg1o.symm
  exact htf (hout.symm.trans hgo_f)

/-! ### Completeness: `Satisfiable M → Colorable 3` -/

open Classical in
private theorem colorable_of_satisfiable (M : Structure FO.cnf) (hM : FO.cnf.Satisfiable M) :
    letI := satToColoringInterpretation.tupleStructure M
    FO.graph.Colorable 3 (Fin (4 + 2) → Fin M.size) := by
  let _ := satToColoringInterpretation.tupleStructure M
  obtain ⟨A, hA⟩ := hM
  let actPosVal (c x : Fin M.size) : Fin 3 :=
    if RelMap (M := M) FO.cnf.pos ![c, x] ∧ A x then 0 else 1
  let actNegVal (c x : Fin M.size) : Fin 3 :=
    if RelMap (M := M) FO.cnf.neg ![c, x] ∧ ¬ A x then 0 else 1
  let posPref (c x : Fin M.size) : Fin 3 :=
    if ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y then 0 else 1
  let negPref (c x : Fin M.size) : Fin 3 :=
    if (∃ y : Fin M.size, RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y) ∨
        (∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.neg ![c, y] ∧ ¬ A y) then 0 else 1
  let inPos0 (c x : Fin M.size) : Fin 3 :=
    if hx : x.val = 0 then 1 else posPref c ⟨x.val - 1, by omega⟩
  let inNeg0 (c x : Fin M.size) : Fin 3 :=
    if hx : x.val = 0 then posPref c (QFNumeric.maxFin M.size)
    else negPref c ⟨x.val - 1, by omega⟩
  have hinPos0_ne2 (c x : Fin M.size) : inPos0 c x ≠ 2 := by
    dsimp only [inPos0, posPref]
    split_ifs <;> decide
  have hinNeg0_ne2 (c x : Fin M.size) : inNeg0 c x ≠ 2 := by
    dsimp only [inNeg0, posPref, negPref]
    split_ifs <;> decide
  have hactPos_ne2 (c x : Fin M.size) : actPosVal c x ≠ 2 := by
    dsimp only [actPosVal]; split_ifs <;> decide
  have hactNeg_ne2 (c x : Fin M.size) : actNegVal c x ≠ 2 := by
    dsimp only [actNegVal]; split_ifs <;> decide
  have horPos_eq (c x : Fin M.size) : orGateOut (inPos0 c x) (actPosVal c x) = posPref c x := by
    have hiff : (inPos0 c x = 0 ∨ actPosVal c x = 0) ↔
        ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y := by
      by_cases hx0 : x.val = 0
      · have hx_eq : x = 0 := Fin.ext hx0
        subst hx_eq
        simp only [inPos0, Fin.val_zero, ↓reduceDIte, actPosVal]
        constructor
        · rintro (hbad | h0)
          · exact False.elim (by revert hbad; decide)
          · split_ifs at h0 with hp
            · exact ⟨0, le_rfl, hp.1, hp.2⟩
            · exact False.elim (by revert h0; decide)
        · rintro ⟨y, hy0, hp, hAy⟩
          have hy : y = 0 := Fin.ext (Nat.eq_zero_of_le_zero hy0)
          subst hy
          exact .inr (by simp [hp, hAy])
      · simp only [inPos0, hx0, ↓reduceDIte, posPref, actPosVal]
        constructor
        · rintro (hprev | hcur)
          · split_ifs at hprev with hex
            · obtain ⟨y, hyle, hp, hAy⟩ := hex
              exact ⟨y, le_trans hyle (by change x.val - 1 ≤ x.val; omega), hp, hAy⟩
            · exact False.elim (by revert hprev; decide)
          · split_ifs at hcur with hp
            · exact ⟨x, le_rfl, hp.1, hp.2⟩
            · exact False.elim (by revert hcur; decide)
        · rintro ⟨y, hyle, hp, hAy⟩
          by_cases hyx : y = x
          · subst hyx
            exact .inr (by simp [hp, hAy])
          · have hylt : y ≤ ⟨x.val - 1, by omega⟩ := by
              have hne_val : y.val ≠ x.val := fun h => hyx (Fin.ext h)
              change y.val ≤ x.val - 1
              change y.val ≤ x.val at hyle
              omega
            have hex : ∃ z : Fin M.size, z ≤ ⟨x.val - 1, by omega⟩ ∧
                RelMap (M := M) FO.cnf.pos ![c, z] ∧ A z := ⟨y, hylt, hp, hAy⟩
            exact .inl (by simp [hex])
    dsimp only [orGateOut, posPref]
    by_cases h : ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y
    · simp only [h, ↓reduceIte]
      rcases hiff.mpr h with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp only [h, ↓reduceIte]
      have hn : ¬ (inPos0 c x = 0 ∨ actPosVal c x = 0) := fun ho => h (hiff.mp ho)
      push Not at hn
      simp [hn.1, hn.2]
  have hle_max (y : Fin M.size) : y ≤ QFNumeric.maxFin M.size := by
    change y.val ≤ M.size - 1
    have := y.isLt
    omega
  have horNeg_eq (c x : Fin M.size) : orGateOut (inNeg0 c x) (actNegVal c x) = negPref c x := by
    have hiff : (inNeg0 c x = 0 ∨ actNegVal c x = 0) ↔
        ((∃ y : Fin M.size, RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y) ∨
          ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.neg ![c, y] ∧ ¬ A y) := by
      by_cases hx0 : x.val = 0
      · have hx_eq : x = 0 := Fin.ext hx0
        subst hx_eq
        simp only [inNeg0, Fin.val_zero, ↓reduceDIte, posPref, actNegVal]
        constructor
        · rintro (hpos | hneg0)
          · split_ifs at hpos with hex
            · obtain ⟨y, _, hp, hAy⟩ := hex
              exact .inl ⟨y, hp, hAy⟩
            · exact False.elim (by revert hpos; decide)
          · split_ifs at hneg0 with hn
            · exact .inr ⟨0, le_rfl, hn.1, hn.2⟩
            · exact False.elim (by revert hneg0; decide)
        · rintro (⟨y, hp, hAy⟩ | ⟨y, hy0, hn, hnAy⟩)
          · have hex : ∃ z : Fin M.size, z ≤ QFNumeric.maxFin M.size ∧
                RelMap (M := M) FO.cnf.pos ![c, z] ∧ A z := ⟨y, hle_max y, hp, hAy⟩
            exact .inl (by simp [hex])
          · have hy : y = 0 := Fin.ext (Nat.eq_zero_of_le_zero hy0)
            subst hy
            exact .inr (by simp [hn, hnAy])
      · simp only [inNeg0, hx0, ↓reduceDIte, negPref, actNegVal]
        constructor
        · rintro (hprev | hcur)
          · split_ifs at hprev with hex
            · rcases hex with hp | ⟨y, hyle, hn, hnAy⟩
              · exact .inl hp
              · exact .inr ⟨y, le_trans hyle (by change x.val - 1 ≤ x.val; omega), hn, hnAy⟩
            · exact False.elim (by revert hprev; decide)
          · split_ifs at hcur with hn
            · exact .inr ⟨x, le_rfl, hn.1, hn.2⟩
            · exact False.elim (by revert hcur; decide)
        · rintro (hp | ⟨y, hyle, hn, hnAy⟩)
          · exact .inl (by simp [hp])
          · by_cases hyx : y = x
            · subst hyx
              exact .inr (by simp [hn, hnAy])
            · have hylt : y ≤ ⟨x.val - 1, by omega⟩ := by
                have hne_val : y.val ≠ x.val := fun h => hyx (Fin.ext h)
                change y.val ≤ x.val - 1
                change y.val ≤ x.val at hyle
                omega
              have hex : ∃ z : Fin M.size, z ≤ ⟨x.val - 1, by omega⟩ ∧
                  RelMap (M := M) FO.cnf.neg ![c, z] ∧ ¬ A z := ⟨y, hylt, hn, hnAy⟩
              exact .inl (by simp [hex])
    dsimp only [orGateOut, negPref]
    by_cases h : (∃ y : Fin M.size, RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y) ∨
        ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.neg ![c, y] ∧ ¬ A y
    · simp only [h, ↓reduceIte]
      rcases hiff.mpr h with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp only [h, ↓reduceIte]
      have hn : ¬ (inNeg0 c x = 0 ∨ actNegVal c x = 0) := fun ho => h (hiff.mp ho)
      push Not at hn
      simp [hn.1, hn.2]
  let tagCol (t : ColorTag) (c x : Fin M.size) : Fin 3 :=
    match t with
    | .pT => 0
    | .pF => if c = 0 ∧ x = 0 then 1 else 0
    | .pB => if c = 0 ∧ x = 0 then 2 else 0
    | .vPos => if c = 0 then (if A x then 2 else 0) else 0
    | .vNeg => if c = 0 then (if A x then 0 else 2) else 0
    | .actPos => actPosVal c x
    | .actNeg => actNegVal c x
    | .posG0 => orGate0 (inPos0 c x) (actPosVal c x)
    | .posG1 => orGate1 (inPos0 c x) (actPosVal c x)
    | .posOut => posPref c x
    | .negG0 => orGate0 (inNeg0 c x) (actNegVal c x)
    | .negG1 => orGate1 (inNeg0 c x) (actNegVal c x)
    | .negOut => negPref c x
  let col (u : Fin (4 + 2) → Fin M.size) : Fin 3 :=
    if h : ∃ t : ColorTag, MatchBinaryTag (colorCode t) u then
      tagCol (Classical.choose h) (u cPay0) (u cPay1)
    else 0
  have hcol_tag {t : ColorTag} {u : Fin (4 + 2) → Fin M.size}
      (hm : MatchBinaryTag (colorCode t) u) :
      col u = tagCol t (u cPay0) (u cPay1) := by
    have hex : ∃ t' : ColorTag, MatchBinaryTag (colorCode t') u := ⟨t, hm⟩
    simp only [col, hex, ↓reduceDIte]
    have heq : Classical.choose hex = t :=
      colorCode_injective (matchBinaryTag_unique (Classical.choose_spec hex) hm)
    rw [heq]
  have hupper_proper : ∀ {u v : Fin (4 + 2) → Fin M.size},
      UpperTagEdge colorCode allColorTags upperColorEdge u v → col u ≠ col v := by
    rintro u v ⟨t₁, _, t₂, _, hm₁, hm₂, p, h12, hp⟩
    rw [hcol_tag hm₁, hcol_tag hm₂]
    cases t₁ <;> cases t₂ <;> simp only [upperColorEdge, Option.some.injEq] at h12
    all_goals try cases h12
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginBoth, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv0, hv1⟩, -⟩
      simp [tagCol, hu0, hu1, hv0, hv1]
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginBoth, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv0, hv1⟩, -⟩
      simp [tagCol, hu0, hu1, hv0, hv1]
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, ProjectionFormula.realize_negLit, pair_arg1_pay,
        Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, hnpos⟩
      simp [tagCol, actPosVal, hnpos]
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, ProjectionFormula.realize_negLit, pair_arg1_pay,
        Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, hnneg⟩
      simp [tagCol, actNegVal, hnneg]
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginBoth, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv0, hv1⟩, -⟩
      simp [tagCol, hu0, hu1, hv0, hv1]
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginToVar, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv0⟩, -⟩
      simp only [tagCol, hu0, hu1, hv0, and_self, ↓reduceIte]
      split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginToVar, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv0⟩, -⟩
      simp only [tagCol, hu0, hu1, hv0, and_self, ↓reduceIte]
      split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginToZero1, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv1⟩, -⟩
      have hin0 : inPos0 (v cPay0) (v cPay1) = 1 := by simp [inPos0, hv1]
      have hv := orGate_in0_ne (inPos0 (v cPay0) (v cPay1)) (actPosVal (v cPay0) (v cPay1))
        (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
      rw [hin0] at hv
      simpa [tagCol, hu0, hu1, hin0] using hv
    · simp only [ProjectionFormula.realize_guardAnd, guardOriginToMax1, guardOrigin0,
        Formula.realize_inf, QFNumeric.realize_isZero, QFNumeric.realize_isMax,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨⟨hu0, hu1⟩, hv1⟩, -⟩
      have hgoal : negPref (v cPay0) (QFNumeric.maxFin M.size) = 0 := by
        dsimp only [negPref]
        rcases hA (v cPay0) with ⟨y, ⟨hpos, hAy⟩ | ⟨hneg, hnAy⟩⟩
        · have hex : ∃ z, RelMap (M := M) FO.cnf.pos ![v cPay0, z] ∧ A z := ⟨y, hpos, hAy⟩
          simp [hex]
        · have hex : ∃ z ≤ QFNumeric.maxFin M.size,
              RelMap (M := M) FO.cnf.neg ![v cPay0, z] ∧ ¬ A z := ⟨y, hle_max y, hneg, hnAy⟩
          simp [hex]
      simp [tagCol, hu0, hu1, hv1, hgoal]
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, -⟩
      simpa [tagCol, hu0, hu1] using (hactPos_ne2 (v cPay0) (v cPay1)).symm
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, -⟩
      simpa [tagCol, hu0, hu1] using (hactNeg_ne2 (v cPay0) (v cPay1)).symm
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, -⟩
      simp only [tagCol, hu0, hu1, and_self, ↓reduceIte, posPref]
      split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardOrigin0, Formula.realize_inf,
        QFNumeric.realize_isZero, Matrix.cons_val_zero] at hp
      rcases hp with ⟨⟨hu0, hu1⟩, -⟩
      simp only [tagCol, hu0, hu1, and_self, ↓reduceIte, negPref]
      split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardSameVar0, Formula.realize_inf,
        QFNumeric.realize_isZero, QFNumeric.realize_varEq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hu0, hv0, h1⟩, -⟩
      simp only [tagCol, hu0, hv0, h1, ↓reduceIte]
      split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardVarToAct, Formula.realize_inf,
        QFNumeric.realize_isZero, QFNumeric.realize_varEq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hu0, h1⟩, -⟩
      simp only [tagCol, hu0, h1, ↓reduceIte, actPosVal]
      by_cases hAv : A (v cPay1)
      · simp only [hAv, ↓reduceIte, and_true]; split_ifs <;> decide
      · simp [hAv]
    · simp only [ProjectionFormula.realize_guardAnd, guardVarToAct, Formula.realize_inf,
        QFNumeric.realize_isZero, QFNumeric.realize_varEq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hu0, h1⟩, -⟩
      simp only [tagCol, hu0, h1, ↓reduceIte, actNegVal]
      by_cases hAv : A (v cPay1)
      · simp [hAv]
      · simp only [hAv, ↓reduceIte, not_false_eq_true, and_true]; split_ifs <;> decide
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      simpa [tagCol, hc, hx] using
        orGate_in1_ne (inPos0 (v cPay0) (v cPay1)) (actPosVal (v cPay0) (v cPay1))
          (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      simpa [tagCol, hc, hx] using
        orGate_in1_ne (inNeg0 (v cPay0) (v cPay1)) (actNegVal (v cPay0) (v cPay1))
          (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      simpa [tagCol, hc, hx] using
        orGate_g0_ne_g1 (inPos0 (v cPay0) (v cPay1)) (actPosVal (v cPay0) (v cPay1))
          (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
    · simp only [gateG0OutFormula, ProjectionFormula.realize_guardAnd,
        ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_varEq,
        QFNumeric.realize_varSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, ProjectionFormula.realize_const_true, and_true] at hp
      rcases hp with ⟨hc, hsame | ⟨_, hsucc⟩⟩
      · have hv := orGate_g0_ne_out (inPos0 (v cPay0) (v cPay1)) (actPosVal (v cPay0) (v cPay1))
          (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
        rw [horPos_eq] at hv
        simpa [tagCol, hc, hsame] using hv
      · have hnz : u cPay1 ≠ 0 := by
          intro h
          have hv0 : (u cPay1).val = 0 := congrArg Fin.val h
          omega
        have hpred : (⟨(u cPay1).val - 1, by omega⟩ : Fin M.size) = v cPay1 := by
          apply Fin.ext; change (u cPay1).val - 1 = (v cPay1).val; omega
        have hin0 : inPos0 (u cPay0) (u cPay1) = posPref (v cPay0) (v cPay1) := by
          simp [inPos0, hnz, hpred, hc]
        have hv := orGate_in0_ne (inPos0 (u cPay0) (u cPay1)) (actPosVal (u cPay0) (u cPay1))
          (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
        rw [hin0] at hv
        simpa [tagCol, hin0] using hv.symm
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      have hv := orGate_g1_ne_out (inPos0 (v cPay0) (v cPay1)) (actPosVal (v cPay0) (v cPay1))
        (hinPos0_ne2 _ _) (hactPos_ne2 _ _)
      rw [horPos_eq] at hv
      simpa [tagCol, hc, hx] using hv
    · simp only [ProjectionFormula.realize_guardAnd, guardBridgeLink, Formula.realize_inf,
        QFNumeric.realize_varEq, QFNumeric.realize_isMax, QFNumeric.realize_isZero,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hu1, hv1⟩, -⟩
      have hin0 : inNeg0 (v cPay0) (v cPay1) = posPref (v cPay0) (QFNumeric.maxFin M.size) := by
        simp [inNeg0, hv1]
      have hv := orGate_in0_ne (inNeg0 (v cPay0) (v cPay1)) (actNegVal (v cPay0) (v cPay1))
        (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
      rw [hin0] at hv
      simpa [tagCol, hc, hu1, hin0] using hv
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      simpa [tagCol, hc, hx] using
        orGate_g0_ne_g1 (inNeg0 (v cPay0) (v cPay1)) (actNegVal (v cPay0) (v cPay1))
          (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
    · simp only [gateG0OutFormula, ProjectionFormula.realize_guardAnd,
        ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_varEq,
        QFNumeric.realize_varSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, ProjectionFormula.realize_const_true, and_true] at hp
      rcases hp with ⟨hc, hsame | ⟨_, hsucc⟩⟩
      · have hv := orGate_g0_ne_out (inNeg0 (v cPay0) (v cPay1)) (actNegVal (v cPay0) (v cPay1))
          (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
        rw [horNeg_eq] at hv
        simpa [tagCol, hc, hsame] using hv
      · have hnz : u cPay1 ≠ 0 := by
          intro h
          have hv0 : (u cPay1).val = 0 := congrArg Fin.val h
          omega
        have hpred : (⟨(u cPay1).val - 1, by omega⟩ : Fin M.size) = v cPay1 := by
          apply Fin.ext; change (u cPay1).val - 1 = (v cPay1).val; omega
        have hin0 : inNeg0 (u cPay0) (u cPay1) = negPref (v cPay0) (v cPay1) := by
          simp [inNeg0, hnz, hpred, hc]
        have hv := orGate_in0_ne (inNeg0 (u cPay0) (u cPay1)) (actNegVal (u cPay0) (u cPay1))
          (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
        rw [hin0] at hv
        simpa [tagCol, hin0] using hv.symm
    · simp only [ProjectionFormula.realize_guardAnd, guardSameCell, Formula.realize_inf,
        QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hp
      rcases hp with ⟨⟨hc, hx⟩, -⟩
      have hv := orGate_g1_ne_out (inNeg0 (v cPay0) (v cPay1)) (actNegVal (v cPay0) (v cPay1))
        (hinNeg0_ne2 _ _) (hactNeg_ne2 _ _)
      rw [horNeg_eq] at hv
      simpa [tagCol, hc, hx] using hv
  refine ⟨col, fun u v hadj => ?_⟩
  rw [satToColoringInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToColoringFormula,
    realize_symmPairBinaryTag (m := 2) colorCode_injective allColorTags asym_upperColorEdge] at hadj
  rcases hadj with huv | hvu
  · exact hupper_proper huv
  · exact (hupper_proper hvu).symm

/-! ### Soundness: `Colorable 3 → Satisfiable M` -/

private theorem satisfiable_of_colorable (M : Structure FO.cnf)
    (hcol : letI := satToColoringInterpretation.tupleStructure M;
      FO.graph.Colorable 3 (Fin (4 + 2) → Fin M.size)) :
    FO.cnf.Satisfiable M := by
  let _ := satToColoringInterpretation.tupleStructure M
  obtain ⟨col, hproper⟩ := hcol
  let tCol := col (mkVertex .pT 0 0)
  let fCol := col (mkVertex .pF 0 0)
  let bCol := col (mkVertex .pB 0 0)
  have hedge {t₁ t₂ : ColorTag}
      {p : ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (4 + 2))}
      (h12 : upperColorEdge t₁ t₂ = some p) (c₁ x₁ c₂ x₂ : Fin M.size)
      (hp : p.toFormula.Realize
        (fun q : Fin 2 × Fin (4 + 2) => (![mkVertex t₁ c₁ x₁, mkVertex t₂ c₂ x₂] q.1) q.2)) :
      col (mkVertex t₁ c₁ x₁) ≠ col (mkVertex t₂ c₂ x₂) :=
    hproper _ _ (directed_edge_to_adj M h12 c₁ x₁ c₂ x₂ hp)
  have htf : tCol ≠ fCol := hedge (t₁ := .pT) (t₂ := .pF) rfl 0 0 0 0
    (by simp [guardOriginBoth, guardOrigin0, mkVertex])
  have htb : tCol ≠ bCol := hedge (t₁ := .pT) (t₂ := .pB) rfl 0 0 0 0
    (by simp [guardOriginBoth, guardOrigin0, mkVertex])
  have hfb : fCol ≠ bCol := hedge (t₁ := .pF) (t₂ := .pB) rfl 0 0 0 0
    (by simp [guardOriginBoth, guardOrigin0, mkVertex])
  let A (x : Fin M.size) : Prop := col (mkVertex .vPos 0 x) = bCol
  have hvPos_t_of_not_A (x : Fin M.size) (hnA : ¬ A x) : col (mkVertex .vPos 0 x) = tCol := by
    have hnf : col (mkVertex .vPos 0 x) ≠ fCol :=
      (hedge (t₁ := .pF) (t₂ := .vPos) rfl 0 0 0 x
        (by simp [guardOriginToVar, guardOrigin0, mkVertex])).symm
    exact fin_three_eq_of_ne fCol bCol (col (mkVertex .vPos 0 x)) tCol
      htf.symm htb.symm hfb hnf hnA
  have hvNeg_t_of_A (x : Fin M.size) (hAx : A x) : col (mkVertex .vNeg 0 x) = tCol := by
    have hnf : col (mkVertex .vNeg 0 x) ≠ fCol :=
      (hedge (t₁ := .pF) (t₂ := .vNeg) rfl 0 0 0 x
        (by simp [guardOriginToVar, guardOrigin0, mkVertex])).symm
    have hnv : col (mkVertex .vPos 0 x) ≠ col (mkVertex .vNeg 0 x) :=
      hedge (t₁ := .vPos) (t₂ := .vNeg) rfl 0 x 0 x
        (by simp [guardSameVar0, mkVertex])
    have hnb : col (mkVertex .vNeg 0 x) ≠ bCol := fun h => hnv (hAx.trans h.symm)
    exact fin_three_eq_of_ne fCol bCol (col (mkVertex .vNeg 0 x)) tCol
      htf.symm htb.symm hfb hnf hnb
  have hactPos_or (c x : Fin M.size) :
      col (mkVertex .actPos c x) = tCol ∨ col (mkVertex .actPos c x) = fCol :=
    color_or_of_ne htf htb hfb
      (hedge (t₁ := .pB) (t₂ := .actPos) rfl 0 0 c x (by simp [guardOrigin0, mkVertex])).symm
  have hactNeg_or (c x : Fin M.size) :
      col (mkVertex .actNeg c x) = tCol ∨ col (mkVertex .actNeg c x) = fCol :=
    color_or_of_ne htf htb hfb
      (hedge (t₁ := .pB) (t₂ := .actNeg) rfl 0 0 c x (by simp [guardOrigin0, mkVertex])).symm
  have hposOut_or (c x : Fin M.size) :
      col (mkVertex .posOut c x) = tCol ∨ col (mkVertex .posOut c x) = fCol :=
    color_or_of_ne htf htb hfb
      (hedge (t₁ := .pB) (t₂ := .posOut) rfl 0 0 c x (by simp [guardOrigin0, mkVertex])).symm
  have hnegOut_or (c x : Fin M.size) :
      col (mkVertex .negOut c x) = tCol ∨ col (mkVertex .negOut c x) = fCol :=
    color_or_of_ne htf htb hfb
      (hedge (t₁ := .pB) (t₂ := .negOut) rfl 0 0 c x (by simp [guardOrigin0, mkVertex])).symm
  have hactPos_sound (c x : Fin M.size) (ht : col (mkVertex .actPos c x) = tCol) :
      RelMap (M := M) FO.cnf.pos ![c, x] ∧ A x := by
    constructor
    · by_contra hnpos
      have hne := hedge (t₁ := .pT) (t₂ := .actPos) rfl 0 0 c x (by
        simp [guardOrigin0, pair_arg1_pay, mkVertex, hnpos])
      exact hne ht.symm
    · by_contra hnA
      have hvt := hvPos_t_of_not_A x hnA
      have hne := hedge (t₁ := .vPos) (t₂ := .actPos) rfl 0 x c x
        (by simp [guardVarToAct, mkVertex])
      exact hne (hvt.trans ht.symm)
  have hactNeg_sound (c x : Fin M.size) (ht : col (mkVertex .actNeg c x) = tCol) :
      RelMap (M := M) FO.cnf.neg ![c, x] ∧ ¬ A x := by
    constructor
    · by_contra hnneg
      have hne := hedge (t₁ := .pT) (t₂ := .actNeg) rfl 0 0 c x (by
        simp [guardOrigin0, pair_arg1_pay, mkVertex, hnneg])
      exact hne ht.symm
    · intro hAx
      have hvt := hvNeg_t_of_A x hAx
      have hne := hedge (t₁ := .vNeg) (t₂ := .actNeg) rfl 0 x c x
        (by simp [guardVarToAct, mkVertex])
      exact hne (hvt.trans ht.symm)
  refine ⟨A, fun c => ?_⟩
  have hpos_chain : ∀ k : ℕ, (hk : k < M.size) → col (mkVertex .posOut c ⟨k, hk⟩) = tCol →
      FO.cnf.ClauseSatisfied A c := by
    intro k
    induction k with
    | zero =>
      intro hk hout
      have h0_eq : (⟨0, hk⟩ : Fin M.size) = 0 := Fin.ext rfl
      rw [h0_eq] at hout
      have he0 : fCol ≠ col (mkVertex .posG0 c 0) :=
        hedge (t₁ := .pF) (t₂ := .posG0) rfl 0 0 c 0
          (by simp [guardOriginToZero1, guardOrigin0, mkVertex])
      have he1 : col (mkVertex .actPos c 0) ≠ col (mkVertex .posG1 c 0) :=
        hedge (t₁ := .actPos) (t₂ := .posG1) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      have hg01 : col (mkVertex .posG0 c 0) ≠ col (mkVertex .posG1 c 0) :=
        hedge (t₁ := .posG0) (t₂ := .posG1) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      have hg0o : col (mkVertex .posG0 c 0) ≠ col (mkVertex .posOut c 0) :=
        hedge (t₁ := .posG0) (t₂ := .posOut) rfl c 0 c 0
          (by simp [gateG0OutFormula, ProjectionFormula.realize_toFormula_branch, mkVertex])
      have hg1o : col (mkVertex .posG1 c 0) ≠ col (mkVertex .posOut c 0) :=
        hedge (t₁ := .posG1) (t₂ := .posOut) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      rcases orGate_forces htf (.inr rfl) (hactPos_or c 0) he0 he1 hg01 hg0o hg1o hout with
          hbad | hact
      · exact False.elim (htf hbad.symm)
      · exact ⟨0, .inl (hactPos_sound c 0 hact)⟩
    | succ k ih =>
      intro hk hout
      let x : Fin M.size := ⟨k, by omega⟩
      let x' : Fin M.size := ⟨k + 1, hk⟩
      have he0 : col (mkVertex .posOut c x) ≠ col (mkVertex .posG0 c x') :=
        (hedge (t₁ := .posG0) (t₂ := .posOut) rfl c x' c x (by
          simp only [gateG0OutFormula, ProjectionFormula.realize_guardAnd,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_varEq,
            QFNumeric.realize_varSucc, ProjectionFormula.realize_const_true, and_true, mkVertex,
            mkTagged_payload, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          refine ⟨trivial, .inr ⟨fun h => ?_, rfl⟩⟩
          have hv := congrArg Fin.val h
          change k + 1 = k at hv
          omega)).symm
      have he1 : col (mkVertex .actPos c x') ≠ col (mkVertex .posG1 c x') :=
        hedge (t₁ := .actPos) (t₂ := .posG1) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      have hg01 : col (mkVertex .posG0 c x') ≠ col (mkVertex .posG1 c x') :=
        hedge (t₁ := .posG0) (t₂ := .posG1) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      have hg0o : col (mkVertex .posG0 c x') ≠ col (mkVertex .posOut c x') :=
        hedge (t₁ := .posG0) (t₂ := .posOut) rfl c x' c x'
          (by simp [gateG0OutFormula, ProjectionFormula.realize_toFormula_branch, mkVertex])
      have hg1o : col (mkVertex .posG1 c x') ≠ col (mkVertex .posOut c x') :=
        hedge (t₁ := .posG1) (t₂ := .posOut) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      rcases orGate_forces htf (hposOut_or c x) (hactPos_or c x') he0 he1 hg01 hg0o hg1o hout with
          hprev | hact
      · exact ih (by omega) hprev
      · exact ⟨x', .inl (hactPos_sound c x' hact)⟩
  have hneg_chain : ∀ k : ℕ, (hk : k < M.size) → col (mkVertex .negOut c ⟨k, hk⟩) = tCol →
      FO.cnf.ClauseSatisfied A c := by
    intro k
    induction k with
    | zero =>
      intro hk hout
      have h0_eq : (⟨0, hk⟩ : Fin M.size) = 0 := Fin.ext rfl
      rw [h0_eq] at hout
      let mx := QFNumeric.maxFin M.size
      have he0 : col (mkVertex .posOut c mx) ≠ col (mkVertex .negG0 c 0) :=
        hedge (t₁ := .posOut) (t₂ := .negG0) rfl c mx c 0
          (by simp [guardBridgeLink, mkVertex, mx])
      have he1 : col (mkVertex .actNeg c 0) ≠ col (mkVertex .negG1 c 0) :=
        hedge (t₁ := .actNeg) (t₂ := .negG1) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      have hg01 : col (mkVertex .negG0 c 0) ≠ col (mkVertex .negG1 c 0) :=
        hedge (t₁ := .negG0) (t₂ := .negG1) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      have hg0o : col (mkVertex .negG0 c 0) ≠ col (mkVertex .negOut c 0) :=
        hedge (t₁ := .negG0) (t₂ := .negOut) rfl c 0 c 0
          (by simp [gateG0OutFormula, ProjectionFormula.realize_toFormula_branch, mkVertex])
      have hg1o : col (mkVertex .negG1 c 0) ≠ col (mkVertex .negOut c 0) :=
        hedge (t₁ := .negG1) (t₂ := .negOut) rfl c 0 c 0 (by simp [guardSameCell, mkVertex])
      rcases orGate_forces htf (hposOut_or c mx) (hactNeg_or c 0) he0 he1 hg01 hg0o hg1o hout with
          hposMax | hact
      · exact hpos_chain (M.size - 1) (NumericFunction.index_lt M.size_ge_two .max) hposMax
      · exact ⟨0, .inr (hactNeg_sound c 0 hact)⟩
    | succ k ih =>
      intro hk hout
      let x : Fin M.size := ⟨k, by omega⟩
      let x' : Fin M.size := ⟨k + 1, hk⟩
      have he0 : col (mkVertex .negOut c x) ≠ col (mkVertex .negG0 c x') :=
        (hedge (t₁ := .negG0) (t₂ := .negOut) rfl c x' c x (by
          simp only [gateG0OutFormula, ProjectionFormula.realize_guardAnd,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_varEq,
            QFNumeric.realize_varSucc, ProjectionFormula.realize_const_true, and_true, mkVertex,
            mkTagged_payload, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          refine ⟨trivial, .inr ⟨fun h => ?_, rfl⟩⟩
          have hv := congrArg Fin.val h
          change k + 1 = k at hv
          omega)).symm
      have he1 : col (mkVertex .actNeg c x') ≠ col (mkVertex .negG1 c x') :=
        hedge (t₁ := .actNeg) (t₂ := .negG1) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      have hg01 : col (mkVertex .negG0 c x') ≠ col (mkVertex .negG1 c x') :=
        hedge (t₁ := .negG0) (t₂ := .negG1) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      have hg0o : col (mkVertex .negG0 c x') ≠ col (mkVertex .negOut c x') :=
        hedge (t₁ := .negG0) (t₂ := .negOut) rfl c x' c x'
          (by simp [gateG0OutFormula, ProjectionFormula.realize_toFormula_branch, mkVertex])
      have hg1o : col (mkVertex .negG1 c x') ≠ col (mkVertex .negOut c x') :=
        hedge (t₁ := .negG1) (t₂ := .negOut) rfl c x' c x' (by simp [guardSameCell, mkVertex])
      rcases orGate_forces htf (hnegOut_or c x) (hactNeg_or c x') he0 he1 hg01 hg0o hg1o hout with
          hprev | hact
      · exact ih (by omega) hprev
      · exact ⟨x', .inr (hactNeg_sound c x' hact)⟩
  let mx := QFNumeric.maxFin M.size
  have hgoal_nf : col (mkVertex .negOut c mx) ≠ fCol :=
    (hedge (t₁ := .pF) (t₂ := .negOut) rfl 0 0 c mx
      (by simp [guardOriginToMax1, guardOrigin0, mkVertex, mx])).symm
  have hgoal_t : col (mkVertex .negOut c mx) = tCol :=
    (hnegOut_or c mx).resolve_right hgoal_nf
  exact hneg_chain (M.size - 1) (NumericFunction.index_lt M.size_ge_two .max) hgoal_t

end SatToColoring

/-- **Every image of `satToColoringInterpretation` is a simple loopless undirected graph** on all
ordered input structures `M`. -/
theorem simpleGraph_satToColoring
    {hI : satToColoringInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    satToColoringInterpretation.toDomainInterpretation.map hI M ⊨ Theory.simpleGraph := by
  let _ := satToColoringInterpretation.tupleStructure M
  have h := simpleGraph_tupleStructure M
  exact StrongHomClass.theory_model (T := Theory.simpleGraph)
    (satToColoringInterpretation.tupleEquiv (by decide) (hI := hI) M)

/-- **Exact `SimpleThreeColorable` preservation of `satToColoringInterpretation`**: on every ordered
`FO.cnf` structure `M`, the dimension-6 image belongs to `Ordered.SimpleThreeColorable` if and only
if `M ∈ Ordered.SAT`. -/
theorem mem_SimpleThreeColorable_satToColoringInterpretation
    {hI : satToColoringInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    satToColoringInterpretation.toDomainInterpretation.map hI M ∈ SimpleThreeColorable ↔
      M ∈ SAT := by
  have hiso := satToColoringInterpretation.mem_of_isoClosed
    FO.graph.isoClosed_SimpleThreeColorable (by decide) (hI := hI) M
  change satToColoringInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure Language.graph | Bundled.of (c := Language.graph.Structure) N ∈
      FO.graph.SimpleThreeColorable} ↔ _
  rw [← hiso, mem_SAT]
  let _ := satToColoringInterpretation.tupleStructure M
  change ((Fin (4 + 2) → Fin M.size) ⊨ Theory.simpleGraph ∧
    FO.graph.Colorable 3 (Fin (4 + 2) → Fin M.size)) ↔ FO.cnf.Satisfiable M
  exact ⟨fun ⟨_, h⟩ => satisfiable_of_colorable M h,
    fun h => ⟨simpleGraph_tupleStructure M, colorable_of_satisfiable M h⟩⟩

/-- **Exact `ThreeColorable` preservation of `satToColoringInterpretation`**: on every ordered
`FO.cnf` structure `M`, the dimension-6 image belongs to `Ordered.ThreeColorable` if and only if
`M ∈ Ordered.SAT`. -/
theorem mem_ThreeColorable_satToColoringInterpretation
    {hI : satToColoringInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    satToColoringInterpretation.toDomainInterpretation.map hI M ∈ ThreeColorable ↔
      M ∈ SAT := by
  have hiso := satToColoringInterpretation.mem_of_isoClosed
    FO.graph.isoClosed_ThreeColorable (by decide) (hI := hI) M
  change satToColoringInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure Language.graph | Bundled.of (c := Language.graph.Structure) N ∈
      FO.graph.ThreeColorable} ↔ _
  rw [← hiso, mem_SAT]
  let _ := satToColoringInterpretation.tupleStructure M
  change FO.graph.Colorable 3 (Fin (4 + 2) → Fin M.size) ↔ FO.cnf.Satisfiable M
  exact ⟨satisfiable_of_colorable M, colorable_of_satisfiable M⟩

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.SimpleThreeColorable`**
(without `BIT`). -/
theorem sat_qfProjectionReduces_SimpleThreeColorable :
    QFProjectionReduces SAT SimpleThreeColorable :=
  QFProjectionReduces.of_qfProjection isQFProjection_satToColoringInterpretation (by decide)
    fun M => (mem_SimpleThreeColorable_satToColoringInterpretation M).symm

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.ThreeColorable`**
(without `BIT`). -/
theorem sat_qfProjectionReduces_ThreeColorable :
    QFProjectionReduces SAT ThreeColorable :=
  QFProjectionReduces.of_qfProjection isQFProjection_satToColoringInterpretation (by decide)
    fun M => (mem_ThreeColorable_satToColoringInterpretation M).symm

end Cslib.Logic.FO.Ordered
