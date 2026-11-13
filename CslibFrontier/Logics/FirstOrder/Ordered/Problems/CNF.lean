/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction
public import CslibFrontier.Logics.FirstOrder.Problems.CNF
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Tagged

/-!
# Canonical ordered CNF satisfiability and the `SAT ≤_qfp 3SAT` projection

Over `Cslib.Logic.FO.cnf` (binary relation symbols `pos(c, x)` and `neg(c, x)`), `Ordered.SAT` and
`Ordered.ThreeSAT` are the canonical ordered queries corresponding to `FO.cnf.SAT` and
`FO.cnf.ThreeSAT` on universes `Fin n` with `2 ≤ n`.

Unlike unordered structures — where splitting a clause of arbitrary width requires ordering its
literals — a canonically ordered CNF structure has `0`, `max`, and non-wrapping `succ` available in
`qfNumericLanguage` (without `BIT`). Using dimension `5` (`3` binary `{0, max}` tag coordinates
plus `2` payload coordinates `(c, x)`), `satToThreeSATInterpretation` chains two successor scans of
relay variables (`varPos c x` across positive literals `0 .. max` and `varNeg c x` across negative
literals `0 .. max`) into clauses of at most `3` literals, with inactive tuples padded by the
2-literal tautology `varX 0 ∨ ¬ varX 0`. Every output entry inspects at most one input literal, so
`Ordered.SAT` reduces to `Ordered.ThreeSAT` by a **quantifier-free projection**
(`sat_qfProjectionReduces_ThreeSAT`).

For existential second-order definability and native `NP` membership at `encStructure`, see
`CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems`.

## Main definitions

* `Cslib.Logic.FO.Ordered.SAT`, `Cslib.Logic.FO.Ordered.ThreeSAT`: canonical ordered CNF and 3-CNF
  satisfiability queries over `FO.cnf`.
* `Cslib.Logic.FO.Ordered.satToThreeSATFormula`,
  `Cslib.Logic.FO.Ordered.satToThreeSATInterpretation`: dimension-5 `BIT`-free quantifier-free
  projection reducing `Ordered.SAT` to `Ordered.ThreeSAT`.

## Main results

* `Cslib.Logic.FO.Ordered.isQFProjection_satToThreeSATInterpretation`:
  `satToThreeSATInterpretation` is a quantifier-free projection (`IsQFProjection`).
* `Cslib.Logic.FO.Ordered.isThreeCNF_satToThreeSAT`: every image tuple names a clause of at most
  three literals on all inputs.
* `Cslib.Logic.FO.Ordered.mem_ThreeSAT_satToThreeSATInterpretation`,
  `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeSAT`: `Ordered.SAT` quantifier-free
  projection reduces to `Ordered.ThreeSAT`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 7.
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure CategoryTheory

/-- **Canonical ordered SAT**: an ordered `FO.cnf` structure belongs to `SAT` when some truth
assignment to `Fin M.size` satisfies every clause. -/
@[expose] def SAT : Query FO.cnf :=
  {M | FO.cnf.Satisfiable M}

/-- **Canonical ordered 3SAT**: an ordered `FO.cnf` structure belongs to `ThreeSAT` when every
clause has at most three literals and the structure is satisfiable. -/
@[expose] def ThreeSAT : Query FO.cnf :=
  {M | FO.cnf.IsThreeCNF M ∧ FO.cnf.Satisfiable M}

theorem mem_SAT {M : Structure FO.cnf} : M ∈ SAT ↔ FO.cnf.Satisfiable M :=
  Iff.rfl

theorem mem_ThreeSAT {M : Structure FO.cnf} :
    M ∈ ThreeSAT ↔ FO.cnf.IsThreeCNF M ∧ FO.cnf.Satisfiable M :=
  Iff.rfl

/-! ### Successor-relay `SAT ≤_qfp ThreeSAT` gadget (`k = 5`) -/

section SatToThreeSAT

private inductive ThreeSATTag : Type
  | posStart
  | posStep
  | bridge
  | negStep
  | goal
  deriving DecidableEq

private def tagCode : ThreeSATTag → Fin 3 → Bool
  | .posStart => ![false, false, false]
  | .posStep => ![false, false, true]
  | .bridge => ![false, true, false]
  | .negStep => ![false, true, true]
  | .goal => ![true, false, false]

private theorem tagCode_injective : Function.Injective tagCode := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases a <;> cases b <;> simp_all [tagCode]

private def allThreeSATTags : List ThreeSATTag :=
  [.posStart, .posStep, .bridge, .negStep, .goal]

private abbrev pay0 : Fin (3 + 2) := Fin.natAdd 3 0
private abbrev pay1 : Fin (3 + 2) := Fin.natAdd 3 1

private noncomputable def isVarXZero : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStart) 1 ⊓
    (QFNumeric.isZero (1, pay0) ⊓ QFNumeric.isZero (1, pay1))

private noncomputable def isVarXSucc : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStart) 1 ⊓
    (QFNumeric.isZero (1, pay0) ⊓ QFNumeric.varSucc (0, pay1) (1, pay1))

private noncomputable def isVarPosZero : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStep) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.isZero (1, pay1))

private noncomputable def isVarPosSame : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStep) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.varEq (0, pay1) (1, pay1))

private noncomputable def isVarPosSucc : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStep) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.varSucc (0, pay1) (1, pay1))

private noncomputable def isVarPosMax : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .posStep) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.isMax (1, pay1))

private noncomputable def isVarNegZero : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .bridge) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.isZero (1, pay1))

private noncomputable def isVarNegSame : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .bridge) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.varEq (0, pay1) (1, pay1))

private noncomputable def isVarNegSucc : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .bridge) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.varSucc (0, pay1) (1, pay1))

private noncomputable def isVarNegMax : qfNumericLanguage.Formula (Fin 2 × Fin (3 + 2)) :=
  hasBinaryTag 2 (tagCode .bridge) 1 ⊓
    (QFNumeric.varEq (0, pay0) (1, pay0) ⊓ QFNumeric.isMax (1, pay1))

private theorem isQF_isVarXZero : isVarXZero.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _))

private theorem isQF_isVarXSucc : isVarXSucc.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_varSucc _ _))

private theorem isQF_isVarPosZero : isVarPosZero.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_isZero _))

private theorem isQF_isVarPosSame : isVarPosSame.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_varEq _ _))

private theorem isQF_isVarPosSucc : isVarPosSucc.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_varSucc _ _))

private theorem isQF_isVarPosMax : isVarPosMax.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_isMax _))

private theorem isQF_isVarNegZero : isVarNegZero.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_isZero _))

private theorem isQF_isVarNegSame : isVarNegSame.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_varEq _ _))

private theorem isQF_isVarNegSucc : isVarNegSucc.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_varSucc _ _))

private theorem isQF_isVarNegMax : isVarNegMax.IsQF :=
  (isQF_hasBinaryTag 2 _ 1).inf ((QFNumeric.isQF_varEq _ _).inf (QFNumeric.isQF_isMax _))

private noncomputable def tautHalf :
    ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (3 + 2)) :=
  .guardAnd isVarXZero (.const true)

private theorem isQF_tautHalf : tautHalf.IsQF :=
  ProjectionFormula.IsQF.guardAnd isQF_isVarXZero (ProjectionFormula.isQF_const true)

private noncomputable def posBranch : ThreeSATTag →
    ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (3 + 2))
  | .posStart =>
    .branch (QFNumeric.isZero (0, pay1))
      (.guardAnd isVarXZero (.posLit FO.cnf.pos ![(0, pay0), (0, pay1)]))
      tautHalf
  | .posStep =>
    .branch (QFNumeric.isMax (0, pay1)).not
      (.branch isVarPosSame (.const true)
        (.guardAnd isVarXSucc (.posLit FO.cnf.pos ![(0, pay0), (1, pay1)])))
      tautHalf
  | .bridge =>
    .branch (QFNumeric.isZero (0, pay1))
      (.guardAnd isVarPosMax (.const true))
      tautHalf
  | .negStep =>
    .branch (QFNumeric.isMax (0, pay1)).not
      (.guardAnd isVarNegSame (.const true))
      tautHalf
  | .goal =>
    .branch (QFNumeric.isZero (0, pay1))
      (.guardAnd isVarNegMax (.const true))
      tautHalf

private noncomputable def negBranch : ThreeSATTag →
    ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin (3 + 2))
  | .posStart =>
    .branch (QFNumeric.isZero (0, pay1))
      (.guardAnd isVarPosZero (.const true))
      tautHalf
  | .posStep =>
    .branch (QFNumeric.isMax (0, pay1)).not
      (.guardAnd isVarPosSucc (.const true))
      tautHalf
  | .bridge =>
    .branch (QFNumeric.isZero (0, pay1))
      (.branch isVarNegZero (.const true)
        (.guardAnd isVarXZero (.posLit FO.cnf.neg ![(0, pay0), (0, pay1)])))
      tautHalf
  | .negStep =>
    .branch (QFNumeric.isMax (0, pay1)).not
      (.branch isVarNegSucc (.const true)
        (.guardAnd isVarXSucc (.posLit FO.cnf.neg ![(0, pay0), (1, pay1)])))
      tautHalf
  | .goal =>
    .branch (QFNumeric.isZero (0, pay1))
      (.const false)
      tautHalf

/-- Quantifier-free projection formulas for the dimension-5 `SAT → ThreeSAT` successor-relay
construction. -/
noncomputable def satToThreeSATFormula :
    ∀ {r : ℕ}, FO.cnf.Relations r →
      ProjectionFormula qfNumericLanguage FO.cnf (Fin r × Fin 5)
  | _, .pos => dispatchBinaryTag (m := 2) 0 tagCode allThreeSATTags posBranch tautHalf
  | _, .neg => dispatchBinaryTag (m := 2) 0 tagCode allThreeSATTags negBranch tautHalf

/-- Dimension-5 full-tuple interpretation reducing `Ordered.SAT` to `Ordered.ThreeSAT` without
`BIT`. -/
noncomputable def satToThreeSATInterpretation : FullTupleInterpretation FO.cnf FO.cnf 5 :=
  FullTupleInterpretation.ofQFProjection satToThreeSATFormula

theorem isQFProjection_satToThreeSATInterpretation :
    satToThreeSATInterpretation.IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection satToThreeSATFormula fun R => ?_
  cases R
  · refine isQF_dispatchBinaryTag (m := 2) 0 tagCode allThreeSATTags (fun t _ => ?_) isQF_tautHalf
    cases t
    · exact ⟨QFNumeric.isQF_isZero _,
        ProjectionFormula.IsQF.guardAnd isQF_isVarXZero (ProjectionFormula.isQF_posLit _ _),
        isQF_tautHalf⟩
    · exact ⟨(QFNumeric.isQF_isMax _).not,
        ⟨isQF_isVarPosSame, ProjectionFormula.isQF_const true,
          ProjectionFormula.IsQF.guardAnd isQF_isVarXSucc (ProjectionFormula.isQF_posLit _ _)⟩,
        isQF_tautHalf⟩
    · exact ⟨QFNumeric.isQF_isZero _,
        ProjectionFormula.IsQF.guardAnd isQF_isVarPosMax (ProjectionFormula.isQF_const true),
        isQF_tautHalf⟩
    · exact ⟨(QFNumeric.isQF_isMax _).not,
        ProjectionFormula.IsQF.guardAnd isQF_isVarNegSame (ProjectionFormula.isQF_const true),
        isQF_tautHalf⟩
    · exact ⟨QFNumeric.isQF_isZero _,
        ProjectionFormula.IsQF.guardAnd isQF_isVarNegMax (ProjectionFormula.isQF_const true),
        isQF_tautHalf⟩
  · refine isQF_dispatchBinaryTag (m := 2) 0 tagCode allThreeSATTags (fun t _ => ?_) isQF_tautHalf
    cases t
    · exact ⟨QFNumeric.isQF_isZero _,
        ProjectionFormula.IsQF.guardAnd isQF_isVarPosZero (ProjectionFormula.isQF_const true),
        isQF_tautHalf⟩
    · exact ⟨(QFNumeric.isQF_isMax _).not,
        ProjectionFormula.IsQF.guardAnd isQF_isVarPosSucc (ProjectionFormula.isQF_const true),
        isQF_tautHalf⟩
    · exact ⟨QFNumeric.isQF_isZero _,
        ⟨isQF_isVarNegZero, ProjectionFormula.isQF_const true,
          ProjectionFormula.IsQF.guardAnd isQF_isVarXZero (ProjectionFormula.isQF_posLit _ _)⟩,
        isQF_tautHalf⟩
    · exact ⟨(QFNumeric.isQF_isMax _).not,
        ⟨isQF_isVarNegSucc, ProjectionFormula.isQF_const true,
          ProjectionFormula.IsQF.guardAnd isQF_isVarXSucc (ProjectionFormula.isQF_posLit _ _)⟩,
        isQF_tautHalf⟩
    · exact ⟨QFNumeric.isQF_isZero _, ProjectionFormula.isQF_const false, isQF_tautHalf⟩

/-! ### Tuple-level variable and clause semantics -/

private def varX {n : ℕ} [Fact (2 ≤ n)] (x : Fin n) : Fin (3 + 2) → Fin n :=
  mkTagged (tagCode .posStart) ![0, x]

private def varPos {n : ℕ} [Fact (2 ≤ n)] (c x : Fin n) : Fin (3 + 2) → Fin n :=
  mkTagged (tagCode .posStep) ![c, x]

private def varNeg {n : ℕ} [Fact (2 ≤ n)] (c x : Fin n) : Fin (3 + 2) → Fin n :=
  mkTagged (tagCode .bridge) ![c, x]

private theorem eq_mkTagged_two {n : ℕ} [Fact (2 ≤ n)] {bs : Fin 3 → Bool}
    {v : Fin (3 + 2) → Fin n} {a b : Fin n} :
    (MatchBinaryTag bs v ∧ (v pay0 = a ∧ v pay1 = b)) ↔ v = mkTagged bs ![a, b] := by
  constructor
  · rintro ⟨hm, h0, h1⟩
    rw [eq_mkTagged_of_matchBinaryTag hm, mkTagged_inj]
    refine ⟨rfl, funext fun j => ?_⟩
    cases j using Fin.cases with
    | zero => exact h0
    | succ j' =>
      have hj : j' = 0 := Subsingleton.elim _ _
      subst hj
      exact h1
  · rintro rfl
    exact ⟨(matchBinaryTag_mkTagged bs bs ![a, b]).mpr rfl,
      mkTagged_payload bs ![a, b] 0, mkTagged_payload bs ![a, b] 1⟩

private theorem succ_fin_of_ne_max {n : ℕ} [Fact (2 ≤ n)] {x : Fin n}
    (hx : x ≠ QFNumeric.maxFin n) : x.val + 1 < n := by
  have hlt := x.isLt
  have hne : x.val ≠ n - 1 := fun hv => hx (Fin.ext hv)
  omega

private def nextFin {n : ℕ} [Fact (2 ≤ n)] (x : Fin n) (hx : x ≠ QFNumeric.maxFin n) : Fin n :=
  ⟨x.val + 1, succ_fin_of_ne_max hx⟩

private theorem val_eq_succ_iff_eq_nextFin {n : ℕ} [Fact (2 ≤ n)] {x y : Fin n}
    (hx : x ≠ QFNumeric.maxFin n) : x.val + 1 = y.val ↔ y = nextFin x hx :=
  ⟨fun h => Fin.ext h.symm, fun h => h ▸ rfl⟩

private theorem realize_pair_arg00 {n : ℕ} (u v : Fin (3 + 2) → Fin n) :
    (fun i : Fin 2 =>
      (![u, v] (![((0 : Fin 2), pay0), (0, pay1)] i).1)
        (![((0 : Fin 2), pay0), (0, pay1)] i).2) = ![u pay0, u pay1] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i' => have hi : i' = 0 := Subsingleton.elim _ _; subst hi; rfl

private theorem realize_pair_arg01 {n : ℕ} (u v : Fin (3 + 2) → Fin n) :
    (fun i : Fin 2 =>
      (![u, v] (![((0 : Fin 2), pay0), (1, pay1)] i).1)
        (![((0 : Fin 2), pay0), (1, pay1)] i).2) = ![u pay0, v pay1] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i' => have hi : i' = 0 := Subsingleton.elim _ _; subst hi; rfl

private theorem mem_allThreeSATTags (t : ThreeSATTag) : t ∈ allThreeSATTags := by
  cases t <;> simp [allThreeSATTags]

private theorem realize_tautHalf {n : ℕ} [Fact (2 ≤ n)] [FO.cnf.Structure (Fin n)]
    (u v : Fin (3 + 2) → Fin n) :
    tautHalf.toFormula.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔ v = varX 0 := by
  simp only [tautHalf, ProjectionFormula.realize_guardAnd, isVarXZero, Formula.realize_inf,
    realize_hasBinaryTag, QFNumeric.realize_isZero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ProjectionFormula.realize_const_true, and_true]
  exact eq_mkTagged_two

private theorem realize_isVarXZero {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarXZero.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔ v = varX 0 := by
  simp only [isVarXZero, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_isZero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact eq_mkTagged_two

private theorem realize_isVarXSucc {n : ℕ} [Fact (2 ≤ n)] {u v : Fin (3 + 2) → Fin n}
    (hx : u pay1 ≠ QFNumeric.maxFin n) :
    isVarXSucc.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varX (nextFin (u pay1) hx) := by
  simp only [isVarXSucc, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_isZero,
    QFNumeric.realize_varSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    val_eq_succ_iff_eq_nextFin hx]
  exact eq_mkTagged_two

private theorem realize_isVarPosZero {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarPosZero.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varPos (u pay0) 0 := by
  simp only [isVarPosZero, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0)]
  exact eq_mkTagged_two

private theorem realize_isVarPosSame {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarPosSame.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varPos (u pay0) (u pay1) := by
  simp only [isVarPosSame, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0), eq_comm (a := u pay1)]
  exact eq_mkTagged_two

private theorem realize_isVarPosSucc {n : ℕ} [Fact (2 ≤ n)] {u v : Fin (3 + 2) → Fin n}
    (hx : u pay1 ≠ QFNumeric.maxFin n) :
    isVarPosSucc.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varPos (u pay0) (nextFin (u pay1) hx) := by
  simp only [isVarPosSucc, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_varSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0), val_eq_succ_iff_eq_nextFin hx]
  exact eq_mkTagged_two

private theorem realize_isVarPosMax {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarPosMax.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varPos (u pay0) (QFNumeric.maxFin n) := by
  simp only [isVarPosMax, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_isMax, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0)]
  exact eq_mkTagged_two

private theorem realize_isVarNegZero {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarNegZero.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varNeg (u pay0) 0 := by
  simp only [isVarNegZero, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_isZero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0)]
  exact eq_mkTagged_two

private theorem realize_isVarNegSame {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarNegSame.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varNeg (u pay0) (u pay1) := by
  simp only [isVarNegSame, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0), eq_comm (a := u pay1)]
  exact eq_mkTagged_two

private theorem realize_isVarNegSucc {n : ℕ} [Fact (2 ≤ n)] {u v : Fin (3 + 2) → Fin n}
    (hx : u pay1 ≠ QFNumeric.maxFin n) :
    isVarNegSucc.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varNeg (u pay0) (nextFin (u pay1) hx) := by
  simp only [isVarNegSucc, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_varSucc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0), val_eq_succ_iff_eq_nextFin hx]
  exact eq_mkTagged_two

private theorem realize_isVarNegMax {n : ℕ} [Fact (2 ≤ n)] (u v : Fin (3 + 2) → Fin n) :
    isVarNegMax.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ↔
      v = varNeg (u pay0) (QFNumeric.maxFin n) := by
  simp only [isVarNegMax, Formula.realize_inf, realize_hasBinaryTag, QFNumeric.realize_varEq,
    QFNumeric.realize_isMax, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eq_comm (a := u pay0)]
  exact eq_mkTagged_two

private theorem varPos_ne_varX {n : ℕ} [Fact (2 ≤ n)] (c x y : Fin n) :
    varPos c x ≠ varX y := by
  intro h
  have ht := (mkTagged_inj.mp h).1
  exact ThreeSATTag.noConfusion (tagCode_injective ht)

private theorem varNeg_ne_varX {n : ℕ} [Fact (2 ≤ n)] (c x y : Fin n) :
    varNeg c x ≠ varX y := by
  intro h
  have ht := (mkTagged_inj.mp h).1
  exact ThreeSATTag.noConfusion (tagCode_injective ht)

/-- The image's literal relation of polarity `b` dispatches on the clause tag to that polarity's
branch formulas, with `tautHalf` on untagged clauses. -/
private theorem relMap_lit (M : Structure FO.cnf) (b : Bool) (u v : Fin (3 + 2) → Fin M.size) :
    (satToThreeSATInterpretation.tupleStructure M).RelMap (FO.cnf.lit b) ![u, v] ↔
      (∃ t ∈ allThreeSATTags, MatchBinaryTag (tagCode t) u ∧
          ((if b then posBranch t else negBranch t)).toFormula.Realize
            (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2)) ∨
        ((∀ t ∈ allThreeSATTags, ¬ MatchBinaryTag (tagCode t) u) ∧ v = varX 0) := by
  rw [← realize_tautHalf u v, satToThreeSATInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection]
  cases b
  · exact realize_dispatchBinaryTag 0 tagCode_injective allThreeSATTags negBranch tautHalf _
  · exact realize_dispatchBinaryTag 0 tagCode_injective allThreeSATTags posBranch tautHalf _

/-- On a tagged clause `u = mkTagged (tagCode t) p`, `dispatchBinaryTag 0` selects `branchFn t`. -/
private theorem relMap_on_tagged (M : Structure FO.cnf) (b : Bool) (t : ThreeSATTag)
    (u v : Fin (3 + 2) → Fin M.size) (hm : MatchBinaryTag (tagCode t) u) :
    (satToThreeSATInterpretation.tupleStructure M).RelMap (FO.cnf.lit b) ![u, v] ↔
      ((if b then posBranch t else negBranch t)).toFormula.Realize
        (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) := by
  rw [relMap_lit]
  constructor
  · rintro (⟨t', _, hm', hb⟩ | ⟨hall, -⟩)
    · have heq := tagCode_injective (matchBinaryTag_unique hm hm')
      subst heq
      exact hb
    · exact False.elim (hall t (mem_allThreeSATTags t) hm)
  · intro hb
    exact Or.inl ⟨t, mem_allThreeSATTags t, hm, hb⟩

private theorem relMap_on_untagged (M : Structure FO.cnf) (b : Bool)
    (u v : Fin (3 + 2) → Fin M.size) (hun : ∀ t, ¬ MatchBinaryTag (tagCode t) u) :
    (satToThreeSATInterpretation.tupleStructure M).RelMap (FO.cnf.lit b) ![u, v] ↔ v = varX 0 := by
  rw [relMap_lit]
  exact ⟨fun | .inl ⟨t, _, hm, _⟩ => False.elim (hun t hm) | .inr ⟨_, hv⟩ => hv,
    fun hv => .inr ⟨fun t _ => hun t, hv⟩⟩

private theorem encard_le_three_of_subset_triple {α : Type*} {s : Set α} (a b d : α)
    (hs : s ⊆ {a, b, d}) : s.encard ≤ 3 := by
  calc
    s.encard ≤ ({a, b, d} : Set α).encard := Set.encard_mono hs
    _ ≤ ({b, d} : Set α).encard + 1 := Set.encard_insert_le {b, d} a
    _ ≤ ({d} : Set α).encard + 1 + 1 := add_le_add (Set.encard_insert_le {d} b) le_rfl
    _ = 3 := by rw [Set.encard_singleton]; rfl

private theorem isThreeCNF_tupleStructure (M : Structure FO.cnf) :
    letI := satToThreeSATInterpretation.tupleStructure M
    FO.cnf.IsThreeCNF (Fin (3 + 2) → Fin M.size) := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  intro u
  by_cases htag : ∃ t : ThreeSATTag, MatchBinaryTag (tagCode t) u
  · obtain ⟨t, hm⟩ := htag
    cases t
    · by_cases hz : u pay1 = 0
      · refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varPos (u pay0) 0) (false, varPos (u pay0) 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .posStart u v hm] at hbv
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
            ProjectionFormula.realize_guardAnd, realize_isVarPosZero,
            ProjectionFormula.realize_const_true, and_true] at hbv
          simp [hbv]
        · simp only [↓reduceIte, posBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
            ProjectionFormula.realize_guardAnd, realize_isVarXZero] at hbv
          simp [hbv.1]
      · refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varX 0) (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .posStart u v hm] at hbv
        cases b <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, posBranch, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, false_and, not_false_eq_true, true_and, false_or,
            realize_tautHalf] at hbv
          simp [hbv]
    · by_cases hx : u pay1 ≠ QFNumeric.maxFin M.size
      · refine encard_le_three_of_subset_triple
          (true, varPos (u pay0) (u pay1))
          (true, varX (nextFin (u pay1) hx))
          (false, varPos (u pay0) (nextFin (u pay1) hx)) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .posStep u v hm] at hbv
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_false_eq_true, true_and,
            not_true_eq_false, false_and, or_false, ProjectionFormula.realize_guardAnd,
            realize_isVarPosSucc hx, ProjectionFormula.realize_const_true, and_true] at hbv
          simp [hbv]
        · simp only [↓reduceIte, posBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_false_eq_true, true_and,
            not_true_eq_false, false_and, or_false, realize_isVarPosSame,
            ProjectionFormula.realize_const_true, and_true,
            ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx] at hbv
          rcases hbv with rfl | ⟨_, rfl, -⟩ <;> simp
      · push Not at hx
        refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varX 0) (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .posStep u v hm] at hbv
        cases b <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, posBranch, negBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_true_eq_false, false_and,
            not_false_eq_true, true_and, false_or, realize_tautHalf] at hbv
          simp [hbv]
    · by_cases hz : u pay1 = 0
      · refine encard_le_three_of_subset_triple
          (true, varPos (u pay0) (QFNumeric.maxFin M.size))
          (false, varNeg (u pay0) 0)
          (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .bridge u v hm] at hbv
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
            realize_isVarNegZero, ProjectionFormula.realize_const_true, and_true,
            ProjectionFormula.realize_guardAnd, realize_isVarXZero] at hbv
          rcases hbv with rfl | ⟨_, rfl, -⟩ <;> simp
        · simp only [↓reduceIte, posBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
            ProjectionFormula.realize_guardAnd, realize_isVarPosMax,
            ProjectionFormula.realize_const_true, and_true] at hbv
          simp [hbv]
      · refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varX 0) (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .bridge u v hm] at hbv
        cases b <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, posBranch, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, false_and, not_false_eq_true, true_and, false_or,
            realize_tautHalf] at hbv
          simp [hbv]
    · by_cases hx : u pay1 ≠ QFNumeric.maxFin M.size
      · refine encard_le_three_of_subset_triple
          (true, varNeg (u pay0) (u pay1))
          (false, varNeg (u pay0) (nextFin (u pay1) hx))
          (false, varX (nextFin (u pay1) hx)) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .negStep u v hm] at hbv
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_false_eq_true, true_and,
            not_true_eq_false, false_and, or_false, realize_isVarNegSucc hx,
            ProjectionFormula.realize_const_true, and_true,
            ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx] at hbv
          rcases hbv with rfl | ⟨_, rfl, -⟩ <;> simp
        · simp only [↓reduceIte, posBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_false_eq_true, true_and,
            not_true_eq_false, false_and, or_false, ProjectionFormula.realize_guardAnd,
            realize_isVarNegSame, ProjectionFormula.realize_const_true, and_true] at hbv
          simp [hbv]
      · push Not at hx
        refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varX 0) (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .negStep u v hm] at hbv
        cases b <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, posBranch, negBranch,
            ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
            QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_true_eq_false, false_and,
            not_false_eq_true, true_and, false_or, realize_tautHalf] at hbv
          simp [hbv]
    · by_cases hz : u pay1 = 0
      · refine encard_le_three_of_subset_triple
          (true, varNeg (u pay0) (QFNumeric.maxFin M.size))
          (true, varNeg (u pay0) (QFNumeric.maxFin M.size))
          (true, varNeg (u pay0) (QFNumeric.maxFin M.size)) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .goal u v hm] at hbv
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, ProjectionFormula.realize_const_false,
            not_true_eq_false, false_and, or_self] at hbv
        · simp only [↓reduceIte, posBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
            ProjectionFormula.realize_guardAnd, realize_isVarNegMax,
            ProjectionFormula.realize_const_true, and_true] at hbv
          simp [hbv]
      · refine encard_le_three_of_subset_triple
          (true, varX 0) (false, varX 0) (false, varX 0) ?_
        rintro ⟨b, v⟩ hbv
        rw [FO.cnf.mem_literals, relMap_on_tagged M b .goal u v hm] at hbv
        cases b <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, posBranch, negBranch,
            ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
            Matrix.cons_val_zero, hz, false_and, not_false_eq_true, true_and, false_or,
            realize_tautHalf] at hbv
          simp [hbv]
  · push Not at htag
    refine encard_le_three_of_subset_triple
      (true, varX 0) (false, varX 0) (false, varX 0) ?_
    rintro ⟨b, v⟩ hbv
    rw [FO.cnf.mem_literals, relMap_on_untagged M b u v htag] at hbv
    cases b <;> simp [hbv]

private theorem tautology_clauseSatisfied (M : Structure FO.cnf)
    (B : (Fin (3 + 2) → Fin M.size) → Prop) (u : Fin (3 + 2) → Fin M.size)
    (hp : (satToThreeSATInterpretation.tupleStructure M).RelMap FO.cnf.pos ![u, varX 0])
    (hn : (satToThreeSATInterpretation.tupleStructure M).RelMap FO.cnf.neg ![u, varX 0]) :
    letI := satToThreeSATInterpretation.tupleStructure M
    FO.cnf.ClauseSatisfied B u := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  by_cases hB : B (varX 0)
  · exact ⟨varX 0, .inl ⟨hp, hB⟩⟩
  · exact ⟨varX 0, .inr ⟨hn, hB⟩⟩

private theorem satisfiable_satToThreeSAT_of_satisfiable (M : Structure FO.cnf)
    (hM : FO.cnf.Satisfiable M) :
    letI := satToThreeSATInterpretation.tupleStructure M
    FO.cnf.Satisfiable (Fin (3 + 2) → Fin M.size) := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  obtain ⟨A, hA⟩ := hM
  let PosUpTo (c x : Fin M.size) : Prop :=
    ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y
  let NegUpTo (c x : Fin M.size) : Prop :=
    (∃ y : Fin M.size, RelMap (M := M) FO.cnf.pos ![c, y] ∧ A y) ∨
      ∃ y : Fin M.size, y ≤ x ∧ RelMap (M := M) FO.cnf.neg ![c, y] ∧ ¬ A y
  let B (v : Fin (3 + 2) → Fin M.size) : Prop :=
    (MatchBinaryTag (tagCode .posStart) v ∧ v pay0 = 0 ∧ A (v pay1)) ∨
      (MatchBinaryTag (tagCode .posStep) v ∧ PosUpTo (v pay0) (v pay1)) ∨
      (MatchBinaryTag (tagCode .bridge) v ∧ NegUpTo (v pay0) (v pay1))
  have hB_varX (x : Fin M.size) : B (varX x) ↔ A x := by
    simp only [B, varX, matchBinaryTag_mkTagged, mkTagged_payload, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, tagCode_injective.eq_iff]
    simp
  have hB_varPos (c x : Fin M.size) : B (varPos c x) ↔ PosUpTo c x := by
    simp only [B, varPos, matchBinaryTag_mkTagged, mkTagged_payload, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, tagCode_injective.eq_iff]
    simp
  have hB_varNeg (c x : Fin M.size) : B (varNeg c x) ↔ NegUpTo c x := by
    simp only [B, varNeg, matchBinaryTag_mkTagged, mkTagged_payload, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, tagCode_injective.eq_iff]
    simp
  have hle_max (y : Fin M.size) : y ≤ QFNumeric.maxFin M.size := by
    change y.val ≤ M.size - 1
    have := y.isLt
    omega
  refine ⟨B, fun u => ?_⟩
  by_cases htag : ∃ t : ThreeSATTag, MatchBinaryTag (tagCode t) u
  · obtain ⟨t, hm⟩ := htag
    cases t
    · by_cases hz : u pay1 = 0
      · by_cases hp0 : B (varPos (u pay0) 0)
        · obtain ⟨y, hy0, hpos, hAy⟩ := (hB_varPos (u pay0) 0).mp hp0
          have hy : y = 0 := Fin.ext (Nat.eq_zero_of_le_zero hy0)
          subst hy
          refine ⟨varX 0, .inl ⟨?_, (hB_varX 0).mpr hAy⟩⟩
          rw [← FO.cnf.lit_true, relMap_on_tagged M true .posStart u (varX 0) hm]
          simp only [↓reduceIte, posBranch, ProjectionFormula.realize_toFormula_branch,
            QFNumeric.realize_isZero, Matrix.cons_val_zero, hz,
            ProjectionFormula.realize_guardAnd, realize_isVarXZero,
            ProjectionFormula.realize_posLit, realize_pair_arg00, hpos, and_self, true_or]
        · refine ⟨varPos (u pay0) 0, .inr ⟨?_, hp0⟩⟩
          rw [← FO.cnf.lit_false, relMap_on_tagged M false .posStart u (varPos (u pay0) 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_isVarPosZero]
      · refine tautology_clauseSatisfied M B u ?_ ?_
        · rw [← FO.cnf.lit_true, relMap_on_tagged M true .posStart u (varX 0) hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
        · rw [← FO.cnf.lit_false, relMap_on_tagged M false .posStart u (varX 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
    · by_cases hx : u pay1 ≠ QFNumeric.maxFin M.size
      · let x' := nextFin (u pay1) hx
        by_cases hnext : B (varPos (u pay0) x')
        · obtain ⟨y, hy_le, hpos, hAy⟩ := (hB_varPos (u pay0) x').mp hnext
          by_cases hyle : y ≤ u pay1
          · refine ⟨varPos (u pay0) (u pay1), .inl ⟨?_,
              (hB_varPos (u pay0) (u pay1)).mpr ⟨y, hyle, hpos, hAy⟩⟩⟩
            rw [← FO.cnf.lit_true,
              relMap_on_tagged M true .posStep u (varPos (u pay0) (u pay1)) hm]
            simp [posBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_isVarPosSame]
          · have hy_eq : y = x' := by
              apply Fin.ext
              change y.val ≤ (u pay1).val + 1 at hy_le
              change ¬ y.val ≤ (u pay1).val at hyle
              change y.val = (u pay1).val + 1
              omega
            subst hy_eq
            refine ⟨varX x', .inl ⟨?_, (hB_varX x').mpr hAy⟩⟩
            rw [← FO.cnf.lit_true, relMap_on_tagged M true .posStep u (varX x') hm]
            have hne : varX x' ≠ varPos (u pay0) (u pay1) := (varPos_ne_varX _ _ _).symm
            have hpay : (varX x') pay1 = x' := mkTagged_payload (tagCode .posStart) ![0, x'] 1
            dsimp only [x'] at hne hpay ⊢
            simp only [↓reduceIte, posBranch, ProjectionFormula.realize_toFormula_branch,
              Formula.realize_not, QFNumeric.realize_isMax, Matrix.cons_val_zero, hx,
              not_false_eq_true, true_and, not_true_eq_false, false_and, or_false,
              realize_isVarPosSame, hne, false_or,
              ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx,
              ProjectionFormula.realize_posLit, realize_pair_arg01, hpay]
            exact hpos
        · refine ⟨varPos (u pay0) x', .inr ⟨?_, hnext⟩⟩
          rw [← FO.cnf.lit_false, relMap_on_tagged M false .posStep u (varPos (u pay0) x') hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hx,
            realize_isVarPosSucc hx, x']
      · push Not at hx
        refine tautology_clauseSatisfied M B u ?_ ?_
        · rw [← FO.cnf.lit_true, relMap_on_tagged M true .posStep u (varX 0) hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_tautHalf]
        · rw [← FO.cnf.lit_false, relMap_on_tagged M false .posStep u (varX 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_tautHalf]
    · by_cases hz : u pay1 = 0
      · by_cases hn0 : B (varNeg (u pay0) 0)
        · rcases (hB_varNeg (u pay0) 0).mp hn0 with ⟨y, hpos, hAy⟩ | ⟨y, hy0, hneg, hnAy⟩
          · refine ⟨varPos (u pay0) (QFNumeric.maxFin M.size), .inl ⟨?_,
              (hB_varPos _ _).mpr ⟨y, hle_max y, hpos, hAy⟩⟩⟩
            rw [← FO.cnf.lit_true, relMap_on_tagged M true .bridge u _ hm]
            simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_isVarPosMax]
          · have hy : y = 0 := Fin.ext (Nat.eq_zero_of_le_zero hy0)
            subst hy
            refine ⟨varX 0, .inr ⟨?_, fun hA0 => hnAy ((hB_varX 0).mp hA0)⟩⟩
            rw [← FO.cnf.lit_false, relMap_on_tagged M false .bridge u (varX 0) hm]
            have hne : varX 0 ≠ varNeg (u pay0) 0 := (varNeg_ne_varX _ _ _).symm
            simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
              ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
              Matrix.cons_val_zero, hz, true_and, not_true_eq_false, false_and, or_false,
              not_false_eq_true, realize_isVarNegZero, hne, false_or,
              ProjectionFormula.realize_guardAnd, realize_isVarXZero,
              ProjectionFormula.realize_posLit, realize_pair_arg00]
            exact hneg
        · refine ⟨varNeg (u pay0) 0, .inr ⟨?_, hn0⟩⟩
          rw [← FO.cnf.lit_false, relMap_on_tagged M false .bridge u (varNeg (u pay0) 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_isVarNegZero]
      · refine tautology_clauseSatisfied M B u ?_ ?_
        · rw [← FO.cnf.lit_true, relMap_on_tagged M true .bridge u (varX 0) hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
        · rw [← FO.cnf.lit_false, relMap_on_tagged M false .bridge u (varX 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
    · by_cases hx : u pay1 ≠ QFNumeric.maxFin M.size
      · let x' := nextFin (u pay1) hx
        by_cases hnext : B (varNeg (u pay0) x')
        · rcases (hB_varNeg (u pay0) x').mp hnext with ⟨y, hpos, hAy⟩ | ⟨y, hy_le, hneg, hnAy⟩
          · refine ⟨varNeg (u pay0) (u pay1), .inl ⟨?_,
              (hB_varNeg _ _).mpr (.inl ⟨y, hpos, hAy⟩)⟩⟩
            rw [← FO.cnf.lit_true,
              relMap_on_tagged M true .negStep u (varNeg (u pay0) (u pay1)) hm]
            simp [posBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_isVarNegSame]
          · by_cases hyle : y ≤ u pay1
            · refine ⟨varNeg (u pay0) (u pay1), .inl ⟨?_,
                (hB_varNeg _ _).mpr (.inr ⟨y, hyle, hneg, hnAy⟩)⟩⟩
              rw [← FO.cnf.lit_true,
                relMap_on_tagged M true .negStep u (varNeg (u pay0) (u pay1)) hm]
              simp [posBranch, ProjectionFormula.realize_toFormula_branch, hx,
                realize_isVarNegSame]
            · have hy_eq : y = x' := by
                apply Fin.ext
                change y.val ≤ (u pay1).val + 1 at hy_le
                change ¬ y.val ≤ (u pay1).val at hyle
                change y.val = (u pay1).val + 1
                omega
              subst hy_eq
              refine ⟨varX x', .inr ⟨?_, fun hAx' => hnAy ((hB_varX x').mp hAx')⟩⟩
              rw [← FO.cnf.lit_false, relMap_on_tagged M false .negStep u (varX x') hm]
              have hne : varX x' ≠ varNeg (u pay0) x' := (varNeg_ne_varX _ _ _).symm
              have hpay : (varX x') pay1 = x' := mkTagged_payload (tagCode .posStart) ![0, x'] 1
              dsimp only [x'] at hne hpay ⊢
              simp only [Bool.false_eq_true, ↓reduceIte, negBranch,
                ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
                QFNumeric.realize_isMax, Matrix.cons_val_zero, hx, not_false_eq_true, true_and,
                not_true_eq_false, false_and, or_false,
                realize_isVarNegSucc hx, hne, false_or,
                ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx,
                ProjectionFormula.realize_posLit, realize_pair_arg01, hpay]
              exact hneg
        · refine ⟨varNeg (u pay0) x', .inr ⟨?_, hnext⟩⟩
          rw [← FO.cnf.lit_false, relMap_on_tagged M false .negStep u (varNeg (u pay0) x') hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hx,
            realize_isVarNegSucc hx, x']
      · push Not at hx
        refine tautology_clauseSatisfied M B u ?_ ?_
        · rw [← FO.cnf.lit_true, relMap_on_tagged M true .negStep u (varX 0) hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_tautHalf]
        · rw [← FO.cnf.lit_false, relMap_on_tagged M false .negStep u (varX 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hx, realize_tautHalf]
    · by_cases hz : u pay1 = 0
      · obtain ⟨y, ⟨hpos, hAy⟩ | ⟨hneg, hnAy⟩⟩ := hA (u pay0)
        · refine ⟨varNeg (u pay0) (QFNumeric.maxFin M.size), .inl ⟨?_,
            (hB_varNeg _ _).mpr (.inl ⟨y, hpos, hAy⟩)⟩⟩
          rw [← FO.cnf.lit_true, relMap_on_tagged M true .goal u _ hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_isVarNegMax]
        · refine ⟨varNeg (u pay0) (QFNumeric.maxFin M.size), .inl ⟨?_,
            (hB_varNeg _ _).mpr (.inr ⟨y, hle_max y, hneg, hnAy⟩)⟩⟩
          rw [← FO.cnf.lit_true, relMap_on_tagged M true .goal u _ hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_isVarNegMax]
      · refine tautology_clauseSatisfied M B u ?_ ?_
        · rw [← FO.cnf.lit_true, relMap_on_tagged M true .goal u (varX 0) hm]
          simp [posBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
        · rw [← FO.cnf.lit_false, relMap_on_tagged M false .goal u (varX 0) hm]
          simp [negBranch, ProjectionFormula.realize_toFormula_branch, hz, realize_tautHalf]
  · push Not at htag
    exact tautology_clauseSatisfied M B u
      ((relMap_on_untagged M true u (varX 0) htag).mpr rfl)
      ((relMap_on_untagged M false u (varX 0) htag).mpr rfl)

/-- A satisfying assignment of the image satisfies a literal of the clause with tag `t` at payload
`(c, x)`, read through that tag's branch formulas. -/
private theorem exists_branch_of_satisfies (M : Structure FO.cnf)
    {B : (Fin (3 + 2) → Fin M.size) → Prop}
    (hB : letI := satToThreeSATInterpretation.tupleStructure M; FO.cnf.Satisfies B)
    (t : ThreeSATTag) (c x : Fin M.size) :
    ∃ u : Fin (3 + 2) → Fin M.size, u pay0 = c ∧ u pay1 = x ∧ ∃ v,
      ((posBranch t).toFormula.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ∧
          B v) ∨
        ((negBranch t).toFormula.Realize (fun p : Fin 2 × Fin (3 + 2) => (![u, v] p.1) p.2) ∧
          ¬ B v) := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  let u := mkTagged (tagCode t) ![c, x]
  have hm : MatchBinaryTag (tagCode t) u := (matchBinaryTag_mkTagged _ _ _).mpr rfl
  refine ⟨u, mkTagged_payload _ ![c, x] 0, mkTagged_payload _ ![c, x] 1, ?_⟩
  obtain ⟨v, ⟨hp, hBv⟩ | ⟨hn, hnBv⟩⟩ := hB u
  · rw [← FO.cnf.lit_true, relMap_on_tagged M true t u v hm] at hp
    exact ⟨v, .inl ⟨hp, hBv⟩⟩
  · rw [← FO.cnf.lit_false, relMap_on_tagged M false t u v hm] at hn
    exact ⟨v, .inr ⟨hn, hnBv⟩⟩

/-- Position `k` of a chain is not the last one when `k + 1` is a position. -/
private theorem exists_nextFin_eq {n : ℕ} [Fact (2 ≤ n)] {k : ℕ} (hk : k + 1 < n) {x : Fin n}
    (hx : x.val = k) : ∃ hmax : x ≠ QFNumeric.maxFin n, nextFin x hmax = ⟨k + 1, hk⟩ := by
  have hmax : x ≠ QFNumeric.maxFin n := fun h => by
    have hv := congrArg Fin.val h
    change x.val = n - 1 at hv
    omega
  exact ⟨hmax, Fin.ext (congrArg (· + 1) hx)⟩

private theorem satisfiable_of_satisfiable_satToThreeSAT (M : Structure FO.cnf)
    (h : letI := satToThreeSATInterpretation.tupleStructure M;
      FO.cnf.Satisfiable (Fin (3 + 2) → Fin M.size)) :
    FO.cnf.Satisfiable M := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  obtain ⟨B, hB⟩ := h
  let A (x : Fin M.size) : Prop := B (varX x)
  refine ⟨A, fun c => ?_⟩
  have hpos_chain : ∀ k : ℕ, (hk : k < M.size) → B (varPos c ⟨k, hk⟩) →
      FO.cnf.ClauseSatisfied A c := by
    intro k
    induction k with
    | zero =>
      intro hk hBp
      obtain ⟨u, hu0, hu1, v, ⟨hp, hBv⟩ | ⟨hn, hnBv⟩⟩ :=
        exists_branch_of_satisfies M hB .posStart c 0
      · simp only [posBranch, ProjectionFormula.realize_toFormula_branch,
          QFNumeric.realize_isZero, Matrix.cons_val_zero, hu1, true_and, not_true_eq_false,
          false_and, or_false, ProjectionFormula.realize_guardAnd, realize_isVarXZero,
          ProjectionFormula.realize_posLit, realize_pair_arg00, hu0] at hp
        obtain ⟨rfl, hrel⟩ := hp
        exact ⟨0, .inl ⟨hrel, hBv⟩⟩
      · simp only [negBranch, ProjectionFormula.realize_toFormula_branch,
          QFNumeric.realize_isZero, Matrix.cons_val_zero, hu1, true_and, not_true_eq_false,
          false_and, or_false, ProjectionFormula.realize_guardAnd, realize_isVarPosZero, hu0,
          ProjectionFormula.realize_const_true, and_true] at hn
        subst hn
        exact False.elim (hnBv hBp)
    | succ k ih =>
      intro hk hBp
      obtain ⟨u, hu0, hu1, v, hlit⟩ := exists_branch_of_satisfies M hB .posStep c ⟨k, by omega⟩
      obtain ⟨hx_u, hnext_eq⟩ := exists_nextFin_eq hk (congrArg Fin.val hu1)
      rcases hlit with ⟨hp, hBv⟩ | ⟨hn, hnBv⟩
      · simp only [posBranch, ProjectionFormula.realize_toFormula_branch,
          Formula.realize_not, QFNumeric.realize_isMax, Matrix.cons_val_zero, hx_u,
          not_false_eq_true, true_and, not_true_eq_false, false_and, or_false,
          realize_isVarPosSame, ProjectionFormula.realize_const_true, and_true,
          ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx_u,
          ProjectionFormula.realize_posLit, realize_pair_arg01, hu0] at hp
        rcases hp with rfl | ⟨_, rfl, hrel⟩
        · rw [hu1] at hBv
          exact ih (by omega) hBv
        · rw [hnext_eq] at hBv hrel
          have hpay : (varX (⟨k + 1, hk⟩ : Fin M.size)) pay1 = ⟨k + 1, hk⟩ :=
            mkTagged_payload (tagCode .posStart) ![0, ⟨k + 1, hk⟩] 1
          rw [hpay] at hrel
          exact ⟨⟨k + 1, hk⟩, .inl ⟨hrel, hBv⟩⟩
      · simp only [negBranch, ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
          QFNumeric.realize_isMax, Matrix.cons_val_zero, hx_u, not_false_eq_true, true_and,
          not_true_eq_false, false_and, or_false, ProjectionFormula.realize_guardAnd,
          realize_isVarPosSucc hx_u, hu0, hnext_eq,
          ProjectionFormula.realize_const_true, and_true] at hn
        subst hn
        exact False.elim (hnBv hBp)
  have hneg_chain : ∀ k : ℕ, (hk : k < M.size) → B (varNeg c ⟨k, hk⟩) →
      FO.cnf.ClauseSatisfied A c := by
    intro k
    induction k with
    | zero =>
      intro hk hBn
      obtain ⟨u, hu0, hu1, v, ⟨hp, hBv⟩ | ⟨hn, hnBv⟩⟩ :=
        exists_branch_of_satisfies M hB .bridge c 0
      · simp only [posBranch, ProjectionFormula.realize_toFormula_branch,
          QFNumeric.realize_isZero, Matrix.cons_val_zero, hu1, true_and, not_true_eq_false,
          false_and, or_false, ProjectionFormula.realize_guardAnd, realize_isVarPosMax, hu0,
          ProjectionFormula.realize_const_true, and_true] at hp
        subst hp
        exact hpos_chain (M.size - 1) (NumericFunction.index_lt M.size_ge_two .max) hBv
      · simp only [negBranch, ProjectionFormula.realize_toFormula_branch,
          QFNumeric.realize_isZero, Matrix.cons_val_zero, hu1, true_and, not_true_eq_false,
          false_and, or_false, realize_isVarNegZero, ProjectionFormula.realize_const_true,
          and_true, ProjectionFormula.realize_guardAnd, realize_isVarXZero,
          ProjectionFormula.realize_posLit, realize_pair_arg00, hu0] at hn
        rcases hn with rfl | ⟨_, rfl, hrel⟩
        · exact False.elim (hnBv hBn)
        · exact ⟨0, .inr ⟨hrel, hnBv⟩⟩
    | succ k ih =>
      intro hk hBn
      obtain ⟨u, hu0, hu1, v, hlit⟩ := exists_branch_of_satisfies M hB .negStep c ⟨k, by omega⟩
      obtain ⟨hx_u, hnext_eq⟩ := exists_nextFin_eq hk (congrArg Fin.val hu1)
      rcases hlit with ⟨hp, hBv⟩ | ⟨hn, hnBv⟩
      · simp only [posBranch, ProjectionFormula.realize_toFormula_branch,
          Formula.realize_not, QFNumeric.realize_isMax, Matrix.cons_val_zero, hx_u,
          not_false_eq_true, true_and, not_true_eq_false, false_and, or_false,
          ProjectionFormula.realize_guardAnd, realize_isVarNegSame, hu0,
          ProjectionFormula.realize_const_true, and_true] at hp
        subst hp
        rw [hu1] at hBv
        exact ih (by omega) hBv
      · simp only [negBranch, ProjectionFormula.realize_toFormula_branch, Formula.realize_not,
          QFNumeric.realize_isMax, Matrix.cons_val_zero, hx_u, not_false_eq_true, true_and,
          not_true_eq_false, false_and, or_false, realize_isVarNegSucc hx_u,
          ProjectionFormula.realize_const_true, and_true,
          ProjectionFormula.realize_guardAnd, realize_isVarXSucc hx_u,
          ProjectionFormula.realize_posLit, realize_pair_arg01, hu0, hnext_eq] at hn
        rcases hn with rfl | ⟨_, rfl, hrel⟩
        · exact False.elim (hnBv hBn)
        · have hpay : (varX (⟨k + 1, hk⟩ : Fin M.size)) pay1 = ⟨k + 1, hk⟩ :=
            mkTagged_payload (tagCode .posStart) ![0, ⟨k + 1, hk⟩] 1
          rw [hpay] at hrel
          exact ⟨⟨k + 1, hk⟩, .inr ⟨hrel, hnBv⟩⟩
  obtain ⟨u, hu0, hu1, v, ⟨hp, hBv⟩ | ⟨hn, -⟩⟩ := exists_branch_of_satisfies M hB .goal c 0
  · simp only [posBranch, ProjectionFormula.realize_toFormula_branch,
      QFNumeric.realize_isZero, Matrix.cons_val_zero, hu1, true_and, not_true_eq_false,
      false_and, or_false, ProjectionFormula.realize_guardAnd, realize_isVarNegMax, hu0,
      ProjectionFormula.realize_const_true, and_true] at hp
    subst hp
    exact hneg_chain (M.size - 1) (NumericFunction.index_lt M.size_ge_two .max) hBv
  · simp only [negBranch, ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
      Matrix.cons_val_zero, hu1, true_and, ProjectionFormula.realize_const_false,
      not_true_eq_false, false_and, or_self] at hn

end SatToThreeSAT

/-- **Every clause of the `satToThreeSATInterpretation` image has at most three literals** on every
input structure `M`. -/
theorem isThreeCNF_satToThreeSAT
    {hI : satToThreeSATInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    FO.cnf.IsThreeCNF (satToThreeSATInterpretation.toDomainInterpretation.map hI M) := by
  let _ := satToThreeSATInterpretation.tupleStructure M
  exact (FO.cnf.isThreeCNF_iff_of_equiv
    (satToThreeSATInterpretation.tupleEquiv (by decide) M)).mp (isThreeCNF_tupleStructure M)

/-- **Exact `ThreeSAT` preservation of `satToThreeSATInterpretation`**: on every ordered `FO.cnf`
structure `M`, the dimension-5 image belongs to `Ordered.ThreeSAT` if and only if `M ∈ Ordered.SAT`.
-/
theorem mem_ThreeSAT_satToThreeSATInterpretation
    {hI : satToThreeSATInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    satToThreeSATInterpretation.toDomainInterpretation.map hI M ∈ ThreeSAT ↔ M ∈ SAT := by
  have hiso := satToThreeSATInterpretation.mem_of_isoClosed FO.cnf.isoClosed_ThreeSAT
    (by decide) (hI := hI) M
  change satToThreeSATInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.cnf | Bundled.of (c := FO.cnf.Structure) N ∈ FO.cnf.ThreeSAT} ↔ _
  rw [← hiso, mem_SAT]
  let _ := satToThreeSATInterpretation.tupleStructure M
  change (FO.cnf.IsThreeCNF (Fin (3 + 2) → Fin M.size) ∧
    FO.cnf.Satisfiable (Fin (3 + 2) → Fin M.size)) ↔ FO.cnf.Satisfiable M
  exact ⟨fun ⟨_, h⟩ => satisfiable_of_satisfiable_satToThreeSAT M h,
    fun h => ⟨isThreeCNF_tupleStructure M, satisfiable_satToThreeSAT_of_satisfiable M h⟩⟩

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.ThreeSAT`** (without `BIT`). -/
theorem sat_qfProjectionReduces_ThreeSAT : QFProjectionReduces SAT ThreeSAT :=
  QFProjectionReduces.of_qfProjection isQFProjection_satToThreeSATInterpretation (by decide)
    fun M => (mem_ThreeSAT_satToThreeSATInterpretation M).symm

end Cslib.Logic.FO.Ordered
