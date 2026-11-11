/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Tagged
public import CslibFrontier.Logics.SecondOrder.Grounding
public import CslibFrontier.Logics.SecondOrder.Projection

/-!
# Grounding ordered existential second-order sentences by quantifier-free projections

Over a relational input language `L`, an existential second-order sentence
`Φ : ESO.Sentence (L.sum ESO.orderLanguage)` inspecting the canonical strict linear order `<` on
`Fin n` (`2 ≤ n`) reduces directly to `Ordered.SAT` by a **quantifier-free projection**
(`QFProjectionReduces`, over `≤`, successor, `0`, and `max`, without `BIT`)
[Immerman, Chapter 7][Immerman1999],
[Immerman and Landau, Definition 3.6][ImmermanLandau1995].

Rather than repeating Tseitin subformula induction, `groundQFInterpretation` embeds the tagged
grounding `Φ.groundInterpretation` (`CslibFrontier.Logics.SecondOrder.Grounding`) into full tuples
`Fin Φ.groundDim → Fin M.size`:
* The first `Φ.groundTagCard` coordinates carry a binary `{0, max}` one-hot code for
  `t : Φ.GroundTag` (`0 ≠ max` because `2 ≤ M.size`), and the remaining `Φ.groundPayloadDim`
  coordinates hold `t.Coord`, padded with `0`.
* Inactive tuples receive the self-tautology `u ∨ ¬u` (`pos(u, u)` and `neg(u, u)`), which mentions
  no input relations and is satisfied under every truth assignment.
* Active tuples realize `Φ.groundTemplates`: equality guards translate to `QFNumeric.varEq`, strict
  order guards `ltSym` on `Fin M.size` translate to `∼(y ≤ x)` / `y ≤ x` via `QFNumeric.le`,
  structural Tseitin clauses have purely numeric coordinate-copy guards, and input-relation clauses
  inspect a single signed literal of `L` (`posLit` / `negLit`).

## Main definitions

* `Cslib.Logic.ESO.Sentence.groundTagCard`, `Cslib.Logic.ESO.Sentence.groundPayloadDim`,
  `Cslib.Logic.ESO.Sentence.groundDim`: tag count, maximum coordinate arity, and full-tuple
  dimension of the ordered projection grounding.
* `Cslib.Logic.ESO.Sentence.groundQFFormula`,
  `Cslib.Logic.ESO.Sentence.groundQFInterpretation`: `BIT`-free quantifier-free projection formulas
  and full-tuple interpretation grounding `Φ : ESO.Sentence (L.sum ESO.orderLanguage)` into
  `FO.cnf`.

## Main results

* `Cslib.Logic.ESO.Sentence.groundDim_pos`: the grounding tuple dimension is positive.
* `Cslib.Logic.ESO.Sentence.isQFProjection_groundQFInterpretation`:
  `Φ.groundQFInterpretation` is a `BIT`-free quantifier-free projection (`IsQFProjection`).
* `Cslib.Logic.ESO.Sentence.satisfiable_tupleStructure_groundQFInterpretation_iff`,
  `Cslib.Logic.ESO.Sentence.mem_SAT_groundQFInterpretation`: on every ordered `L`-structure `M`,
  the image of `M` under `Φ.groundQFInterpretation` belongs to `Ordered.SAT` iff `Φ` holds on `M`
  with its canonical strict linear order.
* `Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_orderSentence`: any ordered query defined on
  canonical orders by an `ESO.Sentence (L.sum ESO.orderLanguage)` reduces to `Ordered.SAT` via
  `QFProjectionReduces`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 7.
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6.
-/

public section

namespace Cslib.Logic

open FirstOrder Language Structure CategoryTheory
open FO FO.Ordered FO.TaggedInterpretation

namespace ESO.Sentence

section GroundQF

variable {L : Language} (Φ : ESO.Sentence (L.sum ESO.orderLanguage))

/-- Number of variable and clause tags in `Φ.GroundTag`. -/
noncomputable def groundTagCard : ℕ :=
  Nat.card Φ.GroundTag

theorem groundTagCard_pos : 0 < Φ.groundTagCard := by
  have : Nonempty Φ.GroundTag := ⟨.top⟩
  exact Nat.card_pos

private noncomputable def groundTagEquiv : Φ.GroundTag ≃ Fin Φ.groundTagCard :=
  Finite.equivFin Φ.GroundTag

private noncomputable def allGroundTags : List Φ.GroundTag :=
  (List.finRange Φ.groundTagCard).map (groundTagEquiv Φ).symm

private theorem mem_allGroundTags (t : Φ.GroundTag) : t ∈ allGroundTags Φ :=
  List.mem_map.mpr ⟨groundTagEquiv Φ t, List.mem_finRange _, (groundTagEquiv Φ).symm_apply_apply t⟩

private noncomputable def groundTagCode (t : Φ.GroundTag) (i : Fin Φ.groundTagCard) : Bool :=
  decide (i = groundTagEquiv Φ t)

private theorem groundTagCode_injective : Function.Injective (groundTagCode Φ) := by
  intro t₁ t₂ h
  have hi := congrFun h (groundTagEquiv Φ t₁)
  simp only [groundTagCode, decide_true, true_eq_decide_iff] at hi
  exact (groundTagEquiv Φ).injective hi

/-- Arity of the coordinate tuple `t.Coord` of `t : Φ.GroundTag`. -/
def groundCoordArity : Φ.GroundTag → ℕ
  | .var ⟨⟨k, _⟩, _⟩ => k
  | .relVar r => Φ.arity r
  | .top => 0
  | .clause ⟨⟨k, _⟩, _⟩ _ => k + 1

private def groundCoordEquiv : (t : Φ.GroundTag) → t.Coord ≃ Fin (Φ.groundCoordArity t)
  | .var ⟨⟨_, _⟩, _⟩ => Equiv.refl _
  | .relVar _ => Equiv.refl _
  | .top => Equiv.refl _
  | .clause ⟨⟨_, _⟩, _⟩ _ => Equiv.refl _

/-- Maximum coordinate arity across all tags of `Φ.GroundTag`. -/
noncomputable def groundPayloadDim : ℕ :=
  ((allGroundTags Φ).map Φ.groundCoordArity).foldr max 0

private theorem le_foldr_max_of_mem : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0
  | _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (le_foldr_max_of_mem h) (Nat.le_max_right _ _)

theorem groundCoordArity_le (t : Φ.GroundTag) : Φ.groundCoordArity t ≤ Φ.groundPayloadDim :=
  le_foldr_max_of_mem (List.mem_map_of_mem (mem_allGroundTags Φ t))

/-- Full-tuple dimension `groundTagCard Φ + groundPayloadDim Φ` of `Φ.groundQFInterpretation`. -/
noncomputable abbrev groundDim : ℕ :=
  Φ.groundTagCard + Φ.groundPayloadDim

/-- The tuple dimension `Φ.groundDim` is strictly positive. -/
theorem groundDim_pos : 0 < Φ.groundDim :=
  Nat.add_pos_left Φ.groundTagCard_pos _

private noncomputable def coordPayloadIdx (t : Φ.GroundTag) (c : t.Coord) :
    Fin Φ.groundPayloadDim :=
  Fin.castLE (Φ.groundCoordArity_le t) (groundCoordEquiv Φ t c)

private noncomputable def coordIdx (t : Φ.GroundTag) (c : t.Coord) : Fin Φ.groundDim :=
  Fin.natAdd Φ.groundTagCard (coordPayloadIdx Φ t c)

private noncomputable def padZeroGuard (t : Φ.GroundTag) (a : Fin 2) :
    qfNumericLanguage.Formula (Fin 2 × Fin Φ.groundDim) :=
  Formula.iInf fun j : Fin Φ.groundPayloadDim =>
    if Φ.groundCoordArity t ≤ j.val then
      QFNumeric.isZero (a, Fin.natAdd Φ.groundTagCard j)
    else
      ⊤

private theorem isQF_padZeroGuard (t : Φ.GroundTag) (a : Fin 2) :
    (padZeroGuard Φ t a).IsQF := by
  refine Formula.isQF_iInf _ fun j => ?_
  split_ifs
  · exact QFNumeric.isQF_isZero _
  · exact BoundedFormula.IsQF.top

private theorem realize_padZeroGuard {n : ℕ} [Fact (2 ≤ n)] (t : Φ.GroundTag) (a : Fin 2)
    (x : Fin 2 × Fin Φ.groundDim → Fin n) :
    (padZeroGuard Φ t a).Realize x ↔
      ∀ j : Fin Φ.groundPayloadDim, Φ.groundCoordArity t ≤ j.val →
        x (a, Fin.natAdd Φ.groundTagCard j) = 0 := by
  rw [padZeroGuard, Formula.realize_iInf]
  refine forall_congr' fun j => ?_
  by_cases hj : Φ.groundCoordArity t ≤ j.val
  · simp only [hj, ↓reduceIte, QFNumeric.realize_isZero, true_implies]
  · simp only [hj, ↓reduceIte, false_implies]
    exact iff_of_true FO.formula_realize_top trivial

private noncomputable def selfEqGuard :
    qfNumericLanguage.Formula (Fin 2 × Fin Φ.groundDim) :=
  Formula.iInf fun idx : Fin Φ.groundDim => QFNumeric.varEq (0, idx) (1, idx)

private theorem isQF_selfEqGuard : (selfEqGuard Φ).IsQF :=
  Formula.isQF_iInf _ fun _ => QFNumeric.isQF_varEq _ _

private theorem realize_selfEqGuard {n : ℕ} [Fact (2 ≤ n)]
    (u v : Fin Φ.groundDim → Fin n) :
    (selfEqGuard Φ).Realize (fun p => (![u, v] p.1) p.2) ↔ u = v := by
  rw [selfEqGuard, Formula.realize_iInf]
  simp only [QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact funext_iff.symm

private noncomputable def selfTautology :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin Φ.groundDim) :=
  .guardAnd (selfEqGuard Φ) (.const true)

private theorem isQF_selfTautology : (selfTautology Φ).IsQF :=
  ProjectionFormula.IsQF.guardAnd (isQF_selfEqGuard Φ) (ProjectionFormula.isQF_const true)

private theorem realize_selfTautology {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (u v : Fin Φ.groundDim → Fin n) :
    (selfTautology Φ).toFormula.Realize (fun p => (![u, v] p.1) p.2) ↔ u = v := by
  rw [selfTautology, ProjectionFormula.realize_guardAnd, realize_selfEqGuard]
  simp only [ProjectionFormula.realize_const_true, and_true]

variable [L.IsRelational]

/-- Boolean characterization of the tag-level domain of `Φ.groundInterpretation`. -/
private def inGroundDomain : Φ.GroundTag → Bool
  | .clause s i => !((clauseTemplates s i true).isEmpty && (clauseTemplates s i false).isEmpty)
  | .var _ => true
  | .relVar _ => true
  | .top => true

private theorem realize_domain_iff_inGroundDomain {N : Type*}
    [(L.sum ESO.orderLanguage).Structure N] (t : Φ.GroundTag) (x : t.Coord → N) :
    (Φ.groundInterpretation.domain t).Realize x ↔ inGroundDomain Φ t = true := by
  cases t with
  | clause s i =>
    simp only [groundInterpretation, inGroundDomain]
    cases (clauseTemplates s i true).isEmpty && (clauseTemplates s i false).isEmpty
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact iff_of_true FO.formula_realize_top trivial
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, Formula.realize_bot]
  | var _ | relVar _ | top =>
    simp only [groundInterpretation, inGroundDomain]
    exact iff_of_true FO.formula_realize_top trivial

private noncomputable def targetCompatGuard (t tgt : Φ.GroundTag)
    (mp : tgt.Coord → Option t.Coord) :
    qfNumericLanguage.Formula (Fin 2 × Fin Φ.groundDim) :=
  if inGroundDomain Φ tgt then
    hasBinaryTag Φ.groundPayloadDim (groundTagCode Φ tgt) 1 ⊓
      (padZeroGuard Φ tgt 1 ⊓
        Formula.iInf fun j : tgt.Coord =>
          match mp j with
          | none => ⊤
          | some i => QFNumeric.varEq (1, coordIdx Φ tgt j) (0, coordIdx Φ t i))
  else
    ⊥

private theorem isQF_targetCompatGuard (t tgt : Φ.GroundTag)
    (mp : tgt.Coord → Option t.Coord) :
    (targetCompatGuard Φ t tgt mp).IsQF := by
  rw [targetCompatGuard]
  split_ifs
  · refine (isQF_hasBinaryTag _ _ 1).inf ((isQF_padZeroGuard Φ tgt 1).inf ?_)
    refine Formula.isQF_iInf _ fun j => ?_
    cases mp j with
    | none => exact BoundedFormula.IsQF.top
    | some i => exact QFNumeric.isQF_varEq _ _
  · exact BoundedFormula.isQF_bot

private noncomputable def templateListGuard (t : Φ.GroundTag)
    (l : List (Template (L.sum ESO.orderLanguage) GroundTag.Coord t)) :
    qfNumericLanguage.Formula (Fin 2 × Fin Φ.groundDim) :=
  l.foldr (fun τ acc => targetCompatGuard Φ t τ.target τ.map ⊔ acc) ⊥

private theorem isQF_templateListGuard (t : Φ.GroundTag)
    (l : List (Template (L.sum ESO.orderLanguage) GroundTag.Coord t)) :
    (templateListGuard Φ t l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons τ τs ih => exact (isQF_targetCompatGuard Φ t τ.target τ.map).sup ih

private theorem realize_templateListGuard {n : ℕ} [Fact (2 ≤ n)] (t : Φ.GroundTag)
    (l : List (Template (L.sum ESO.orderLanguage) GroundTag.Coord t))
    (x : Fin 2 × Fin Φ.groundDim → Fin n) :
    (templateListGuard Φ t l).Realize x ↔
      ∃ τ ∈ l, (targetCompatGuard Φ t τ.target τ.map).Realize x := by
  induction l with
  | nil =>
    simp only [templateListGuard, List.foldr_nil, Formula.realize_bot, List.not_mem_nil,
      false_and, exists_false]
  | cons τ τs ih =>
    simp only [templateListGuard, List.foldr_cons, Formula.realize_sup]
    change ((targetCompatGuard Φ t τ.target τ.map).Realize x ∨
        (templateListGuard Φ t τs).Realize x) ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

private noncomputable def uncondTemplatesFormula (t : Φ.GroundTag) (b : Bool) :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin Φ.groundDim) :=
  .guardAnd (templateListGuard Φ t (Φ.groundTemplates t b)) (.const true)

private theorem isQF_uncondTemplatesFormula (t : Φ.GroundTag) (b : Bool) :
    (uncondTemplatesFormula Φ t b).IsQF :=
  ProjectionFormula.IsQF.guardAnd (isQF_templateListGuard Φ t _)
    (ProjectionFormula.isQF_const true)

private noncomputable def clauseZeroFormula (s : Φ.Subformula) (b : Bool) :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin Φ.groundDim) :=
  match s with
  | ⟨⟨k, .equal t₁ t₂⟩, hs⟩ =>
    let sEq : Φ.Subformula := ⟨⟨k, .equal t₁ t₂⟩, hs⟩
    let t : Φ.GroundTag := .clause sEq 0
    let eqG := QFNumeric.varEq (0, coordIdx Φ t (termCoord t₁)) (0, coordIdx Φ t (termCoord t₂))
    .guardAnd
      (targetCompatGuard Φ t (.var sEq) (fun j => some j.castSucc) ⊓
        (if b then eqG else eqG.not))
      (.const true)
  | ⟨⟨k, .rel (.inl (.inl R_in)) ts⟩, hs⟩ =>
    let sRel : Φ.Subformula := ⟨⟨k, .rel (.inl (.inl R_in)) ts⟩, hs⟩
    let t : Φ.GroundTag := .clause sRel 0
    let args := fun j => (0, coordIdx Φ t (termCoord (ts j)))
    .guardAnd
      (targetCompatGuard Φ t (.var sRel) (fun j => some j.castSucc))
      (if b then .posLit R_in args else .negLit R_in args)
  | ⟨⟨k, .rel (.inl (.inr ⟨(), hr⟩)) ts⟩, hs⟩ =>
    let sOrd : Φ.Subformula := ⟨⟨k, .rel (.inl (.inr ⟨(), hr⟩)) ts⟩, hs⟩
    let t : Φ.GroundTag := .clause sOrd 0
    let c₀ : t.Coord := termCoord (ts (Fin.cast hr 0))
    let c₁ : t.Coord := termCoord (ts (Fin.cast hr 1))
    let leG := QFNumeric.le (.var (0, coordIdx Φ t c₁)) (.var (0, coordIdx Φ t c₀))
    .guardAnd
      (targetCompatGuard Φ t (.var sOrd) (fun j => some j.castSucc) ⊓
        (if b then leG.not else leG))
      (.const true)
  | ⟨⟨k, .falsum⟩, hs⟩ =>
    uncondTemplatesFormula Φ (.clause ⟨⟨k, .falsum⟩, hs⟩ 0) b
  | ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ =>
    uncondTemplatesFormula Φ (.clause ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ 0) b
  | ⟨⟨k, .imp ψ χ⟩, hs⟩ =>
    uncondTemplatesFormula Φ (.clause ⟨⟨k, .imp ψ χ⟩, hs⟩ 0) b
  | ⟨⟨k, .all ψ⟩, hs⟩ =>
    uncondTemplatesFormula Φ (.clause ⟨⟨k, .all ψ⟩, hs⟩ 0) b

private theorem isQF_clauseZeroFormula (s : Φ.Subformula) (b : Bool) :
    (clauseZeroFormula Φ s b).IsQF := by
  rcases s with ⟨⟨k, ψ⟩, hs⟩
  cases ψ with
  | equal t₁ t₂ =>
    refine ProjectionFormula.IsQF.guardAnd ((isQF_targetCompatGuard Φ _ _ _).inf ?_)
      (ProjectionFormula.isQF_const true)
    cases b
    · exact (QFNumeric.isQF_varEq _ _).not
    · exact QFNumeric.isQF_varEq _ _
  | rel R ts =>
    rcases R with (R_in | ⟨⟨⟩, hr⟩) | r_var
    · refine ProjectionFormula.IsQF.guardAnd (isQF_targetCompatGuard Φ _ _ _) ?_
      cases b
      · exact ProjectionFormula.isQF_negLit _ _
      · exact ProjectionFormula.isQF_posLit _ _
    · refine ProjectionFormula.IsQF.guardAnd ((isQF_targetCompatGuard Φ _ _ _).inf ?_)
        (ProjectionFormula.isQF_const true)
      cases b
      · exact (QFNumeric.isAtomic_le _ _).isQF
      · exact (QFNumeric.isAtomic_le _ _).isQF.not
    · exact isQF_uncondTemplatesFormula Φ _ b
  | falsum => exact isQF_uncondTemplatesFormula Φ _ b
  | imp _ _ => exact isQF_uncondTemplatesFormula Φ _ b
  | all _ => exact isQF_uncondTemplatesFormula Φ _ b

private noncomputable def activeTagFormula (t : Φ.GroundTag) (b : Bool) :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin Φ.groundDim) :=
  match t with
  | .clause s i =>
    if i = 0 then clauseZeroFormula Φ s b else uncondTemplatesFormula Φ (.clause s i) b
  | .var s => uncondTemplatesFormula Φ (.var s) b
  | .relVar r => uncondTemplatesFormula Φ (.relVar r) b
  | .top => uncondTemplatesFormula Φ .top b

private theorem isQF_activeTagFormula (t : Φ.GroundTag) (b : Bool) :
    (activeTagFormula Φ t b).IsQF := by
  cases t with
  | clause s i =>
    dsimp only [activeTagFormula]
    split_ifs
    · exact isQF_clauseZeroFormula Φ s b
    · exact isQF_uncondTemplatesFormula Φ _ b
  | var _ | relVar _ | top =>
    exact isQF_uncondTemplatesFormula Φ _ b

private noncomputable def tagBranch (t : Φ.GroundTag) (b : Bool) :
    ProjectionFormula qfNumericLanguage L (Fin 2 × Fin Φ.groundDim) :=
  if inGroundDomain Φ t then
    .branch (padZeroGuard Φ t 0) (activeTagFormula Φ t b) (selfTautology Φ)
  else
    selfTautology Φ

private theorem isQF_tagBranch (t : Φ.GroundTag) (b : Bool) :
    (tagBranch Φ t b).IsQF := by
  rw [tagBranch]
  split_ifs
  · exact ⟨isQF_padZeroGuard Φ t 0, isQF_activeTagFormula Φ t b, isQF_selfTautology Φ⟩
  · exact isQF_selfTautology Φ

/-- `BIT`-free quantifier-free projection formulas defining `FO.cnf.pos` and `FO.cnf.neg` for the
ordered grounding of `Φ : ESO.Sentence (L.sum ESO.orderLanguage)`. -/
noncomputable def groundQFFormula :
    ∀ {r : ℕ}, FO.cnf.Relations r →
      ProjectionFormula qfNumericLanguage L (Fin r × Fin Φ.groundDim)
  | _, .pos =>
    dispatchBinaryTag (m := Φ.groundPayloadDim) 0 (groundTagCode Φ) (allGroundTags Φ)
      (fun t => tagBranch Φ t true) (selfTautology Φ)
  | _, .neg =>
    dispatchBinaryTag (m := Φ.groundPayloadDim) 0 (groundTagCode Φ) (allGroundTags Φ)
      (fun t => tagBranch Φ t false) (selfTautology Φ)

/-- Full-tuple interpretation grounding `Φ : ESO.Sentence (L.sum ESO.orderLanguage)` into `FO.cnf`
by a quantifier-free projection without `BIT`. -/
noncomputable def groundQFInterpretation :
    FullTupleInterpretation L FO.cnf Φ.groundDim :=
  FullTupleInterpretation.ofQFProjection (groundQFFormula Φ)

/-- **`Φ.groundQFInterpretation` is a `BIT`-free quantifier-free projection.** -/
theorem isQFProjection_groundQFInterpretation :
    Φ.groundQFInterpretation.IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection _ fun R => ?_
  cases R with
  | pos =>
    exact isQF_dispatchBinaryTag 0 (groundTagCode Φ) (allGroundTags Φ)
      (fun t _ => isQF_tagBranch Φ t true) (isQF_selfTautology Φ)
  | neg =>
    exact isQF_dispatchBinaryTag 0 (groundTagCode Φ) (allGroundTags Φ)
      (fun t _ => isQF_tagBranch Φ t false) (isQF_selfTautology Φ)

/-! ### Active-tuple embedding and clause semantics -/

section Semantics

variable {Φ} (M : Ordered.Structure L)

private noncomputable def padPayload (t : Φ.GroundTag) (coords : t.Coord → Fin M.size)
    (j : Fin Φ.groundPayloadDim) : Fin M.size :=
  if h : j.val < Φ.groundCoordArity t then
    coords ((groundCoordEquiv Φ t).symm ⟨j.val, h⟩)
  else
    0

private noncomputable def extractCoords (t : Φ.GroundTag)
    (u : Fin Φ.groundDim → Fin M.size) : t.Coord → Fin M.size :=
  fun c => u (coordIdx Φ t c)

private noncomputable def embedGroundSigma (t : Φ.GroundTag) (coords : t.Coord → Fin M.size) :
    Fin Φ.groundDim → Fin M.size :=
  mkTagged (groundTagCode Φ t) (padPayload M t coords)

omit [L.IsRelational] in
private theorem matchBinaryTag_embedGroundSigma (t : Φ.GroundTag)
    (coords : t.Coord → Fin M.size) :
    MatchBinaryTag (groundTagCode Φ t) (embedGroundSigma M t coords) := by
  rw [embedGroundSigma, matchBinaryTag_mkTagged]

omit [L.IsRelational] in
private theorem padZero_embedGroundSigma (t : Φ.GroundTag) (coords : t.Coord → Fin M.size)
    (j : Fin Φ.groundPayloadDim) (hj : Φ.groundCoordArity t ≤ j.val) :
    embedGroundSigma M t coords (Fin.natAdd Φ.groundTagCard j) = 0 := by
  have hnot : ¬ j.val < Φ.groundCoordArity t := Nat.not_lt.mpr hj
  simp only [embedGroundSigma, mkTagged_payload, padPayload, hnot, dite_false]

omit [L.IsRelational] in
private theorem extractCoords_embedGroundSigma (t : Φ.GroundTag)
    (coords : t.Coord → Fin M.size) :
    extractCoords M t (embedGroundSigma M t coords) = coords := by
  funext c
  let idx := groundCoordEquiv Φ t c
  have hlt : (Fin.castLE (Φ.groundCoordArity_le t) idx).val < Φ.groundCoordArity t := idx.isLt
  simp only [extractCoords, coordIdx, coordPayloadIdx, embedGroundSigma, mkTagged_payload,
    padPayload, idx, hlt, dite_true]
  have hfin : (⟨(Fin.castLE (Φ.groundCoordArity_le t) (groundCoordEquiv Φ t c)).val, hlt⟩ :
      Fin (Φ.groundCoordArity t)) = groundCoordEquiv Φ t c := Fin.ext rfl
  rw [hfin, Equiv.symm_apply_apply]

omit [L.IsRelational] in
private theorem embedGroundSigma_extractCoords {t : Φ.GroundTag}
    {u : Fin Φ.groundDim → Fin M.size}
    (htag : MatchBinaryTag (groundTagCode Φ t) u)
    (hpad : ∀ j : Fin Φ.groundPayloadDim, Φ.groundCoordArity t ≤ j.val →
      u (Fin.natAdd Φ.groundTagCard j) = 0) :
    embedGroundSigma M t (extractCoords M t u) = u := by
  conv_rhs => rw [eq_mkTagged_of_matchBinaryTag htag]
  rw [embedGroundSigma, mkTagged_inj]
  refine ⟨rfl, funext fun j => ?_⟩
  by_cases hj : j.val < Φ.groundCoordArity t
  · simp only [padPayload, hj, dite_true, extractCoords, coordIdx, coordPayloadIdx]
    have hfin : Fin.castLE (Φ.groundCoordArity_le t)
        (groundCoordEquiv Φ t ((groundCoordEquiv Φ t).symm ⟨j.val, hj⟩)) = j := by
      rw [Equiv.apply_symm_apply]
      exact Fin.ext rfl
    rw [hfin]
  · simp only [padPayload, hj, dite_false]
    exact (hpad j (Nat.le_of_not_lt hj)).symm

omit [L.IsRelational] in
private theorem embedGroundSigma_injective {t₁ t₂ : Φ.GroundTag}
    {c₁ : t₁.Coord → Fin M.size} {c₂ : t₂.Coord → Fin M.size}
    (h : embedGroundSigma M t₁ c₁ = embedGroundSigma M t₂ c₂) :
    (⟨t₁, c₁⟩ : Σ t, t.Coord → Fin M.size) = ⟨t₂, c₂⟩ := by
  have hcode : groundTagCode Φ t₁ = groundTagCode Φ t₂ :=
    ((mkTagged_inj (bs₁ := groundTagCode Φ t₁)).mp h).1
  have ht : t₁ = t₂ := groundTagCode_injective Φ hcode
  subst ht
  refine congrArg (Sigma.mk t₁) ?_
  rw [← extractCoords_embedGroundSigma M t₁ c₁, h, extractCoords_embedGroundSigma]

section PrivateOrder

@[instance_reducible]
private def instCanonicalOrderStructure : ESO.orderLanguage.Structure M :=
  ESO.varLanguage.structure (arity := fun _ : Unit => 2) (ESO.orderRelOfEquiv (Equiv.refl M))

attribute [local instance] instCanonicalOrderStructure

private theorem realize_targetCompatGuard_iff (t tgt : Φ.GroundTag)
    (mp : tgt.Coord → Option t.Coord) (u v : Fin Φ.groundDim → Fin M.size) :
    (targetCompatGuard Φ t tgt mp).Realize (fun p => (![u, v] p.1) p.2) ↔
      ∃ (y : tgt.Coord → Fin M.size) (_ : (Φ.groundInterpretation.domain tgt).Realize y),
        v = embedGroundSigma M tgt y ∧
          ∀ j i, mp j = some i → y j = extractCoords M t u i := by
  rw [targetCompatGuard]
  by_cases hdom : inGroundDomain Φ tgt = true
  · simp only [hdom, ↓reduceIte]
    rw [Formula.realize_inf, Formula.realize_inf, realize_hasBinaryTag,
      realize_padZeroGuard, Formula.realize_iInf]
    constructor
    · rintro ⟨htag, hpad, hcompat⟩
      have htag' : MatchBinaryTag (groundTagCode Φ tgt) v := htag
      have hpad' : ∀ j : Fin Φ.groundPayloadDim, Φ.groundCoordArity tgt ≤ j.val →
          v (Fin.natAdd Φ.groundTagCard j) = 0 := hpad
      have hy : (Φ.groundInterpretation.domain tgt).Realize (extractCoords M tgt v) :=
        (realize_domain_iff_inGroundDomain Φ tgt _).mpr hdom
      refine ⟨extractCoords M tgt v, hy, (embedGroundSigma_extractCoords M htag' hpad').symm,
        fun j i hmp => ?_⟩
      have hj := hcompat j
      rw [hmp] at hj
      simpa only [QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        extractCoords] using hj
    · rintro ⟨y, -, rfl, hcompat⟩
      refine ⟨matchBinaryTag_embedGroundSigma M tgt y, padZero_embedGroundSigma M tgt y,
        fun j => ?_⟩
      cases hmp : mp j with
      | none => exact FO.formula_realize_top
      | some i =>
        simp only [QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hy_eq : embedGroundSigma M tgt y (coordIdx Φ tgt j) = y j :=
          congrFun (extractCoords_embedGroundSigma M tgt y) j
        rw [hy_eq]
        exact hcompat j i hmp
  · simp only [hdom, Bool.false_eq_true, ↓reduceIte, Formula.realize_bot, false_iff]
    rintro ⟨y, hy, -⟩
    exact hdom ((realize_domain_iff_inGroundDomain Φ tgt y).mp hy)

private theorem guard_eq_top_of_mem_clauseTemplates_succ (s : Φ.Subformula) (i : Fin 3)
    (hi : i ≠ 0) (b : Bool) :
    ∀ τ ∈ clauseTemplates s i b, τ.guard = ⊤ := by
  rcases s with ⟨⟨k, ψ⟩, hs⟩
  match i with
  | 0 => exact absurd rfl hi
  | 1 =>
    intro τ hτ
    cases ψ with
    | falsum | equal _ _ =>
      cases b <;> exact False.elim (List.not_mem_nil hτ)
    | rel R ts =>
      rcases R with R_in | r_var
      · cases b <;> exact False.elim (List.not_mem_nil hτ)
      · cases b <;> obtain rfl := List.mem_singleton.mp hτ <;> rfl
    | imp _ _ =>
      cases b
      · exact False.elim (List.not_mem_nil hτ)
      · rcases List.mem_cons.mp hτ with rfl | hτ'
        · rfl
        · obtain rfl := List.mem_singleton.mp hτ'
          rfl
    | all _ =>
      cases b <;> obtain rfl := List.mem_singleton.mp hτ <;> rfl
  | 2 =>
    intro τ hτ
    cases ψ with
    | falsum | equal _ _ | all _ =>
      cases b <;> exact False.elim (List.not_mem_nil hτ)
    | rel R _ =>
      rcases R with _ | _ <;> cases b <;> exact False.elim (List.not_mem_nil hτ)
    | imp _ _ =>
      cases b <;> obtain rfl := List.mem_singleton.mp hτ <;> rfl

private theorem guard_eq_top_of_mem_clauseTemplates_zero (s : Φ.Subformula) (b : Bool)
    (hψ : match s with
      | ⟨⟨_, .equal _ _⟩, _⟩ => False
      | ⟨⟨_, .rel (.inl _) _⟩, _⟩ => False
      | _ => True) :
    ∀ τ ∈ clauseTemplates s 0 b, τ.guard = ⊤ := by
  rcases s with ⟨⟨k, ψ⟩, hs⟩
  intro τ hτ
  cases ψ with
  | equal _ _ => exact hψ.elim
  | rel R ts =>
    rcases R with R_in | r_var
    · exact hψ.elim
    · cases b <;> obtain rfl := List.mem_singleton.mp hτ <;> rfl
  | falsum =>
    cases b
    · obtain rfl := List.mem_singleton.mp hτ
      rfl
    · exact False.elim (List.not_mem_nil hτ)
  | imp _ _ =>
    cases b
    · rcases List.mem_cons.mp hτ with rfl | hτ'
      · rfl
      · obtain rfl := List.mem_singleton.mp hτ'
        rfl
    · obtain rfl := List.mem_singleton.mp hτ
      rfl
  | all _ =>
    cases b <;> obtain rfl := List.mem_singleton.mp hτ <;> rfl

private theorem realize_uncondTemplatesFormula_of_guard_top (t : Φ.GroundTag) (b : Bool)
    (htop : ∀ τ ∈ Φ.groundTemplates t b, τ.guard = ⊤)
    (u v : Fin Φ.groundDim → Fin M.size) :
    (uncondTemplatesFormula Φ t b).toFormula.Realize (fun p => (![u, v] p.1) p.2) ↔
      ∃ τ ∈ Φ.groundTemplates t b, τ.guard.Realize (extractCoords M t u) ∧
        ∃ (y : τ.target.Coord → Fin M.size)
          (_ : (Φ.groundInterpretation.domain τ.target).Realize y),
          v = embedGroundSigma M τ.target y ∧ τ.Compat (extractCoords M t u) y := by
  rw [uncondTemplatesFormula, ProjectionFormula.realize_guardAnd]
  simp only [ProjectionFormula.realize_const_true, and_true, realize_templateListGuard]
  refine exists_congr fun τ => and_congr_right fun hτ => ?_
  rw [realize_targetCompatGuard_iff M t τ.target τ.map u v, htop τ hτ]
  exact ⟨fun h => ⟨FO.formula_realize_top, h⟩, fun ⟨_, h⟩ => h⟩

private theorem realize_singletonTemplate_iff {t tgt : Φ.GroundTag}
    {guard : (L.sum ESO.orderLanguage).Formula t.Coord}
    {mp : tgt.Coord → Option t.Coord} {b : Bool}
    (htemps : Φ.groundTemplates t b = [⟨tgt, guard, mp⟩])
    {P : Prop} {u v : Fin Φ.groundDim → Fin M.size}
    (hguard : P ↔ guard.Realize (extractCoords M t u)) :
    ((targetCompatGuard Φ t tgt mp).Realize (fun p => (![u, v] p.1) p.2) ∧ P) ↔
      ∃ τ ∈ Φ.groundTemplates t b, τ.guard.Realize (extractCoords M t u) ∧
        ∃ (y : τ.target.Coord → Fin M.size)
          (_ : (Φ.groundInterpretation.domain τ.target).Realize y),
          v = embedGroundSigma M τ.target y ∧ τ.Compat (extractCoords M t u) y := by
  rw [htemps, realize_targetCompatGuard_iff M t tgt mp u v, hguard, and_comm]
  simp only [List.mem_singleton, exists_eq_left]
  rfl

private theorem realize_activeTagFormula (t : Φ.GroundTag) (b : Bool)
    (u v : Fin Φ.groundDim → Fin M.size) :
    (activeTagFormula Φ t b).toFormula.Realize (fun p => (![u, v] p.1) p.2) ↔
      ∃ τ ∈ Φ.groundTemplates t b, τ.guard.Realize (extractCoords M t u) ∧
        ∃ (y : τ.target.Coord → Fin M.size)
          (_ : (Φ.groundInterpretation.domain τ.target).Realize y),
          v = embedGroundSigma M τ.target y ∧ τ.Compat (extractCoords M t u) y := by
  cases t with
  | var s =>
    exact realize_uncondTemplatesFormula_of_guard_top M (.var s) b
      (fun τ hτ => by obtain rfl := List.mem_singleton.mp hτ; rfl) u v
  | relVar r =>
    exact realize_uncondTemplatesFormula_of_guard_top M (.relVar r) b
      (fun τ hτ => by obtain rfl := List.mem_singleton.mp hτ; rfl) u v
  | top =>
    exact realize_uncondTemplatesFormula_of_guard_top M .top b
      (fun τ hτ => by
        cases b
        · exact False.elim (List.not_mem_nil hτ)
        · obtain rfl := List.mem_singleton.mp hτ
          rfl) u v
  | clause s i =>
    by_cases hi : i = 0
    · subst hi
      simp only [activeTagFormula, ↓reduceIte]
      rcases s with ⟨⟨k, ψ⟩, hs⟩
      cases ψ with
      | equal t₁ t₂ =>
        let sEq : Φ.Subformula := ⟨⟨k, .equal t₁ t₂⟩, hs⟩
        let tEq : Φ.GroundTag := .clause sEq 0
        simp only [clauseZeroFormula, ProjectionFormula.realize_guardAnd,
          ProjectionFormula.realize_const_true, and_true, Formula.realize_inf]
        refine realize_singletonTemplate_iff (t := tEq) (b := b) M rfl ?_
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_not,
            QFNumeric.realize_varEq, Matrix.cons_val_zero]
          rfl
        · simp only [↓reduceIte, QFNumeric.realize_varEq, Matrix.cons_val_zero]
          rfl
      | rel R ts =>
        rcases R with (R_in | ⟨⟨⟩, hr⟩) | r_var
        · let sRel : Φ.Subformula := ⟨⟨k, .rel (.inl (.inl R_in)) ts⟩, hs⟩
          let tRel : Φ.GroundTag := .clause sRel 0
          simp only [clauseZeroFormula, ProjectionFormula.realize_guardAnd]
          refine realize_singletonTemplate_iff (t := tRel) (b := b) M rfl ?_
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, ProjectionFormula.realize_negLit,
              Matrix.cons_val_zero]
            rfl
          · simp only [↓reduceIte, ProjectionFormula.realize_posLit, Matrix.cons_val_zero]
            rfl
        · subst hr
          let sOrd : Φ.Subformula := ⟨⟨k, .rel (.inl (.inr ⟨(), rfl⟩)) ts⟩, hs⟩
          let tOrd : Φ.GroundTag := .clause sOrd 0
          simp only [clauseZeroFormula, ProjectionFormula.realize_guardAnd,
            ProjectionFormula.realize_const_true, and_true, Formula.realize_inf]
          refine realize_singletonTemplate_iff (t := tOrd) (b := b) M rfl ?_
          have hlt_realize :
              (Relations.formula (L := L.sum ESO.orderLanguage) (Sum.inr ESO.ltSym)
                (fun j => .var (termCoord (ts j)))).Realize (extractCoords M tOrd u) ↔
                u (coordIdx Φ tOrd (termCoord (ts 0))) <
                  u (coordIdx Φ tOrd (termCoord (ts 1))) := by
            change (fun j => extractCoords M tOrd u (termCoord (ts j))) ∈
              ESO.orderRelOfEquiv (Equiv.refl M) () ↔ _
            simp only [ESO.orderRelOfEquiv, Set.mem_ofPred_eq, Equiv.refl_apply, extractCoords]
          cases b
          · exact (QFNumeric.realize_le _ _ _).trans (not_lt.symm.trans
              ((not_congr hlt_realize).symm.trans Formula.realize_not.symm))
          · exact Formula.realize_not.trans ((not_congr (QFNumeric.realize_le _ _ _)).trans
              (not_le.trans hlt_realize.symm))
        · exact realize_uncondTemplatesFormula_of_guard_top M _ b
            (guard_eq_top_of_mem_clauseTemplates_zero _ b trivial) u v
      | falsum =>
        exact realize_uncondTemplatesFormula_of_guard_top M _ b
          (guard_eq_top_of_mem_clauseTemplates_zero _ b trivial) u v
      | imp _ _ =>
        exact realize_uncondTemplatesFormula_of_guard_top M _ b
          (guard_eq_top_of_mem_clauseTemplates_zero _ b trivial) u v
      | all _ =>
        exact realize_uncondTemplatesFormula_of_guard_top M _ b
          (guard_eq_top_of_mem_clauseTemplates_zero _ b trivial) u v
    · simp only [activeTagFormula, hi, ↓reduceIte]
      exact realize_uncondTemplatesFormula_of_guard_top M (.clause s i) b
        (guard_eq_top_of_mem_clauseTemplates_succ s i hi b) u v

private theorem groundInterpretation_rel_lit' (b : Bool) (ts : Fin 2 → Φ.GroundTag) :
    Φ.groundInterpretation.rel (FO.cnf.lit b) ts =
      binaryRel (fun t w => Template.listFormula (Φ.groundTemplates t b) w) ts := by
  cases b <;> rfl

private theorem relMap_tupleStructure_groundQF_lit (b : Bool)
    (u v : Fin Φ.groundDim → Fin M.size) :
    ((Φ.groundQFInterpretation).tupleStructure M).RelMap (FO.cnf.lit b) ![u, v] ↔
      (dispatchBinaryTag (m := Φ.groundPayloadDim) 0 (groundTagCode Φ) (allGroundTags Φ)
        (fun t => tagBranch Φ t b) (selfTautology Φ)).toFormula.Realize
          (fun p => (![u, v] p.1) p.2) := by
  rw [groundQFInterpretation, FullTupleInterpretation.relMap_tupleStructure_ofQFProjection]
  cases b <;> rfl

private noncomputable def embedGroundModel :
    Φ.groundInterpretation.Model M → (Fin Φ.groundDim → Fin M.size) :=
  fun ⟨t, ⟨coords, _⟩⟩ => embedGroundSigma M t coords

private theorem embedGroundModel_injective :
    Function.Injective (embedGroundModel (Φ := Φ) M) := by
  rintro ⟨t₁, x₁, hx₁⟩ ⟨t₂, x₂, hx₂⟩ h
  exact Model.ext_toSigma (embedGroundSigma_injective M h)

private theorem relMap_lit_embedGroundModel (b : Bool)
    (m : Φ.groundInterpretation.Model M)
    (v : Fin Φ.groundDim → Fin M.size) :
    ((Φ.groundQFInterpretation).tupleStructure M).RelMap (FO.cnf.lit b)
        ![embedGroundModel M m, v] ↔
      ∃ m' : Φ.groundInterpretation.Model M,
        v = embedGroundModel M m' ∧ RelMap (FO.cnf.lit b) ![m, m'] := by
  rcases m with ⟨t, x, hx⟩
  let m₀ : Φ.groundInterpretation.Model M := ⟨t, x, hx⟩
  change ((Φ.groundQFInterpretation).tupleStructure M).RelMap (FO.cnf.lit b)
      ![embedGroundSigma M t x, v] ↔
    ∃ m' : Φ.groundInterpretation.Model M,
      v = embedGroundModel M m' ∧ RelMap (FO.cnf.lit b) ![m₀, m']
  rw [relMap_tupleStructure_groundQF_lit,
    realize_dispatchBinaryTag 0 (groundTagCode_injective Φ)]
  have hdom : inGroundDomain Φ t = true :=
    (realize_domain_iff_inGroundDomain Φ t x).mp hx
  have htag : MatchBinaryTag (groundTagCode Φ t) (embedGroundSigma M t x) :=
    matchBinaryTag_embedGroundSigma M t x
  have hpad : (padZeroGuard Φ t 0).Realize
      (fun p => (![embedGroundSigma M t x, v] p.1) p.2) :=
    (realize_padZeroGuard Φ t 0 _).mpr (padZero_embedGroundSigma M t x)
  have hlhs :
      ((∃ t' ∈ allGroundTags Φ,
          MatchBinaryTag (groundTagCode Φ t')
            (fun j => (![embedGroundSigma M t x, v] (0, j).1) (0, j).2) ∧
            (tagBranch Φ t' b).toFormula.Realize
              (fun p => (![embedGroundSigma M t x, v] p.1) p.2)) ∨
        ((∀ t' ∈ allGroundTags Φ,
            ¬ MatchBinaryTag (groundTagCode Φ t')
              (fun j => (![embedGroundSigma M t x, v] (0, j).1) (0, j).2)) ∧
          (selfTautology Φ).toFormula.Realize
            (fun p => (![embedGroundSigma M t x, v] p.1) p.2))) ↔
      (activeTagFormula Φ t b).toFormula.Realize
        (fun p => (![embedGroundSigma M t x, v] p.1) p.2) := by
    constructor
    · rintro (⟨t', -, htag', hbr⟩ | ⟨hall, -⟩)
      · have htt' : t' = t :=
          groundTagCode_injective Φ (matchBinaryTag_unique htag' htag)
        subst htt'
        simp only [tagBranch, hdom, ↓reduceIte, ProjectionFormula.realize_toFormula_branch] at hbr
        rcases hbr with ⟨-, hact⟩ | ⟨hnpad, -⟩
        · exact hact
        · exact absurd hpad hnpad
      · exact absurd htag (hall t (mem_allGroundTags Φ t))
    · intro hact
      refine Or.inl ⟨t, mem_allGroundTags Φ t, htag, ?_⟩
      simp only [tagBranch, hdom, ↓reduceIte, ProjectionFormula.realize_toFormula_branch]
      exact Or.inl ⟨hpad, hact⟩
  refine hlhs.trans ((realize_activeTagFormula M t b (embedGroundSigma M t x) v).trans ?_)
  rw [extractCoords_embedGroundSigma M t x]
  constructor
  · rintro ⟨τ, hτ, hg, y, hy, rfl, hcompat⟩
    let m' : Φ.groundInterpretation.Model M := ⟨τ.target, y, hy⟩
    exact ⟨m', rfl,
      (FO.cnf.relMap_lit_of_templates groundInterpretation_rel_lit' b m₀ m').mpr
        ⟨τ, hτ, hg, y, rfl, hcompat⟩⟩
  · rintro ⟨m', rfl, hrel⟩
    obtain ⟨τ, hτ, hg, y', heq, hcompat⟩ :=
      (FO.cnf.relMap_lit_of_templates groundInterpretation_rel_lit' b m₀ m').mp hrel
    obtain ⟨w, y, hy⟩ := m'
    obtain ⟨rfl, hheq⟩ := Sigma.mk.inj_iff.mp heq
    cases eq_of_heq hheq
    exact ⟨τ, hτ, hg, y, hy, rfl, hcompat⟩

private theorem relMap_self_of_not_mem_range_embedGroundModel (b : Bool)
    {u : Fin Φ.groundDim → Fin M.size}
    (hu : ¬ ∃ m : Φ.groundInterpretation.Model M, embedGroundModel M m = u) :
    ((Φ.groundQFInterpretation).tupleStructure M).RelMap (FO.cnf.lit b) ![u, u] := by
  rw [relMap_tupleStructure_groundQF_lit,
    realize_dispatchBinaryTag 0 (groundTagCode_injective Φ)]
  have hself : (selfTautology Φ).toFormula.Realize (fun p => (![u, u] p.1) p.2) :=
    (realize_selfTautology Φ u u).mpr rfl
  by_cases hex : ∃ t ∈ allGroundTags Φ, MatchBinaryTag (groundTagCode Φ t) u
  · obtain ⟨t, ht, htag⟩ := hex
    refine Or.inl ⟨t, ht, htag, ?_⟩
    by_cases hdom : inGroundDomain Φ t = true
    · have hnpad : ¬ (padZeroGuard Φ t 0).Realize (fun p => (![u, u] p.1) p.2) := by
        intro hpad
        have hpad' := (realize_padZeroGuard Φ t 0 _).mp hpad
        have hy : (Φ.groundInterpretation.domain t).Realize (extractCoords M t u) :=
          (realize_domain_iff_inGroundDomain Φ t _).mpr hdom
        exact hu ⟨⟨t, extractCoords M t u, hy⟩, embedGroundSigma_extractCoords M htag hpad'⟩
      simp only [tagBranch, hdom, ↓reduceIte, ProjectionFormula.realize_toFormula_branch]
      exact Or.inr ⟨hnpad, hself⟩
    · simp only [tagBranch, hdom, Bool.false_eq_true, ↓reduceIte]
      exact hself
  · simp only [not_exists, not_and] at hex
    exact Or.inr ⟨hex, hself⟩

end PrivateOrder

/-- **Tuple-level correctness of `Φ.groundQFInterpretation`**: on every ordered `L`-structure `M`,
`Φ.groundQFInterpretation.tupleStructure M` is satisfiable if and only if `Φ` holds on `M`
equipped with its canonical strict linear order. -/
theorem satisfiable_tupleStructure_groundQFInterpretation_iff :
    (letI := Φ.groundQFInterpretation.tupleStructure M;
      FO.cnf.Satisfiable (Fin Φ.groundDim → Fin M.size)) ↔
      (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
        (ESO.orderRelOfEquiv (Equiv.refl M));
        Φ.Realize M) := by
  let _ := Φ.groundQFInterpretation.tupleStructure M
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl M))
  have : Nonempty M := ⟨⟨0, Nat.zero_lt_of_lt M.size_ge_two⟩⟩
  rw [← Φ.satisfiable_groundInterpretation_iff (M := M)]
  constructor
  · rintro ⟨A_tup, hA_tup⟩
    refine ⟨fun m => A_tup (embedGroundModel M m), fun c => ?_⟩
    obtain ⟨v, ⟨hpos, hv⟩ | ⟨hneg, hv⟩⟩ := hA_tup (embedGroundModel M c)
    · obtain ⟨m', rfl, hrel⟩ := (relMap_lit_embedGroundModel M true c v).mp hpos
      exact ⟨m', .inl ⟨hrel, hv⟩⟩
    · obtain ⟨m', rfl, hrel⟩ := (relMap_lit_embedGroundModel M false c v).mp hneg
      exact ⟨m', .inr ⟨hrel, hv⟩⟩
  · rintro ⟨A, hA⟩
    let A_tup : (Fin Φ.groundDim → Fin M.size) → Prop :=
      fun u => ∃ m, embedGroundModel M m = u ∧ A m
    have hA_emb (m : Φ.groundInterpretation.Model M) :
        A_tup (embedGroundModel M m) ↔ A m :=
      ⟨fun ⟨m', hm', hm'A⟩ => embedGroundModel_injective M hm' ▸ hm'A, fun hm => ⟨m, rfl, hm⟩⟩
    refine ⟨A_tup, fun u => ?_⟩
    by_cases hu : ∃ m : Φ.groundInterpretation.Model M, embedGroundModel M m = u
    · obtain ⟨c, rfl⟩ := hu
      obtain ⟨m', ⟨hpos, hm'⟩ | ⟨hneg, hm'⟩⟩ := hA c
      · exact ⟨embedGroundModel M m',
          .inl ⟨(relMap_lit_embedGroundModel M true c _).mpr ⟨m', rfl, hpos⟩,
            (hA_emb m').mpr hm'⟩⟩
      · exact ⟨embedGroundModel M m',
          .inr ⟨(relMap_lit_embedGroundModel M false c _).mpr ⟨m', rfl, hneg⟩,
            mt (hA_emb m').mp hm'⟩⟩
    · by_cases hval : A_tup u
      · exact ⟨u, .inl ⟨relMap_self_of_not_mem_range_embedGroundModel M true hu, hval⟩⟩
      · exact ⟨u, .inr ⟨relMap_self_of_not_mem_range_embedGroundModel M false hu, hval⟩⟩

/-- **Ordered `SAT` membership of `Φ.groundQFInterpretation`**: on every ordered `L`-structure `M`,
the canonical ordered image of `M` under `Φ.groundQFInterpretation` belongs to `Ordered.SAT` if
and only if `Φ` holds on `M` with its canonical strict linear order. -/
theorem mem_SAT_groundQFInterpretation
    {hI : Φ.groundQFInterpretation.toDomainInterpretation.Admissible} :
    Φ.groundQFInterpretation.toDomainInterpretation.map hI M ∈ FO.Ordered.SAT ↔
      (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
        (ESO.orderRelOfEquiv (Equiv.refl M));
        Φ.Realize M) :=
  (FullTupleInterpretation.mem_of_isoClosed FO.cnf.isoClosed_SAT
    Φ.groundQFInterpretation Φ.groundDim_pos M).symm.trans
    (Φ.satisfiable_tupleStructure_groundQFInterpretation_iff M)

end Semantics

end GroundQF

end ESO.Sentence

namespace FO.Ordered

/-- **Every ordered query defined on canonical orders by a relational `ESO.Sentence` over
`L.sum ESO.orderLanguage` reduces to `Ordered.SAT` by a `BIT`-free quantifier-free projection**
[Immerman, Chapter 7][Immerman1999]. -/
theorem qfProjectionReduces_SAT_of_orderSentence {L : Language} [L.IsRelational] {K : Query L}
    (Φ : ESO.Sentence (L.sum ESO.orderLanguage))
    (hΦ : ∀ M : Structure L,
      M ∈ K ↔
        letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
          (ESO.orderRelOfEquiv (Equiv.refl M));
        Φ.Realize M) :
    QFProjectionReduces K SAT :=
  QFProjectionReduces.of_qfProjection Φ.isQFProjection_groundQFInterpretation Φ.groundDim_pos
    fun M => (hΦ M).trans (Φ.mem_SAT_groundQFInterpretation M).symm

end FO.Ordered

end Cslib.Logic
