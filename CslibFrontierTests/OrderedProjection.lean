/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.Ordered.Projection
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
import CslibFrontier.Tactic.FirstOrder
import Mathlib.ModelTheory.Graph

/-!
# Tests for ordered first-order and quantifier-free projections

Each projection is checked as a predicate and on concrete canonical structures:

* the off-diagonal complement of a directed graph, a one-dimensional quantifier-free projection
  with an equality guard, on `Fin 3` and `Fin 2`;
* the copy of the edge relation onto pairs, a two-dimensional first-order projection, whose image
  relation at lexicographic rank `5` of `Fin 3 × Fin 3` (`lexRank ![1, 2] = 5`) is the input edge
  `(1, 2)`, so two inputs that differ only there have different images; also at `n = 2`;
* the copy of a nullary relation, at both truth values.

The negative checks: a dimension-zero projection has no admissible image, and the conjunction of
two unary input relations is a quantifier-free full-tuple interpretation without numeric symbols
whose image is not a projection map. Finally the successor atom of the guard vocabulary does not
wrap, and projection maps are simulated in logarithmic space through `IsDomainMap`.
-/

namespace CslibFrontierTests.OrderedProjection

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

instance : Fact (2 ≤ 2) := ⟨le_rfl⟩
instance : Fact (2 ≤ 3) := ⟨by decide⟩

/-! ### The off-diagonal complement of a directed graph -/

/-- `x₀ ≠ x₁ ∧ ¬E(x₀, x₁)` as a decision tree: on the diagonal, false; otherwise the negated
edge literal. -/
def complementTree : ProjectionFormula qfNumericLanguage Language.graph (Fin 2 × Fin 1) :=
  .branch (Term.equal (.var (0, 0)) (.var (1, 0))) (.leaf (.const false))
    (.leaf (.rel Language.adj (fun i => (i, 0)) true))

/-- The off-diagonal complement, a one-dimensional quantifier-free projection. -/
noncomputable def complement : FullTupleInterpretation Language.graph Language.graph 1 :=
  FullTupleInterpretation.ofQFProjection (L' := Language.graph) fun
    | graphRel.adj => complementTree

theorem isQFProjection_complement : complement.IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection _ fun R => ?_
  cases R
  exact .branch (BoundedFormula.IsAtomic.equal _ _).isQF (ProjectionFormula.isQF_leaf _)
    (ProjectionFormula.isQF_leaf _)

/-- On canonical `Fin n`, the complement relation is the off-diagonal non-edge relation. -/
theorem realize_complement {n : ℕ} [Fact (2 ≤ n)] [Language.graph.Structure (Fin n)]
    (x : Fin 2 × Fin 1 → Fin n) :
    (complement.rel Language.adj).Realize x ↔
      x (0, 0) ≠ x (1, 0) ∧ ¬RelMap Language.adj fun i => x (i, 0) := by
  rw [complement, FullTupleInterpretation.realize_rel_ofQFProjection]
  simp only [Language.adj, complementTree, ProjectionFormula.select]
  split_ifs with h
  · simp only [Formula.realize_equal, Term.realize_var] at h
    simp [h, InputLiteral.realize_const]
  · simp only [Formula.realize_equal, Term.realize_var] at h
    exact (InputLiteral.realize_rel_true _ _ _).trans ⟨fun h' => ⟨h, h'⟩, And.right⟩

/-- The directed graph on `Fin n` given by an edge test. -/
@[instance_reducible]
def graphStructure (n : ℕ) (E : Fin n → Fin n → Prop) : Language.graph.Structure (Fin n) where
  RelMap | .adj, x => E (x 0) (x 1)

theorem relMap_graphStructure {n : ℕ} {E : Fin n → Fin n → Prop} (x : Fin 2 → Fin n) :
    RelMap (self := graphStructure n E) Language.adj x ↔ E (x 0) (x 1) :=
  Iff.rfl

section Fin3

local instance : Language.graph.Structure (Fin 3) :=
  graphStructure 3 fun a b => a = 1 ∧ b = 2

/-- On `Fin 3` with the single edge `1 → 2`, that edge is absent from the complement, the absent
edge `2 → 1` is present, and the diagonal is absent. -/
example : ¬(complement.rel Language.adj).Realize (fun p => (![1, 2] : Fin 2 → Fin 3) p.1) ∧
    (complement.rel Language.adj).Realize (fun p => (![2, 1] : Fin 2 → Fin 3) p.1) ∧
    ¬(complement.rel Language.adj).Realize (fun _ => (1 : Fin 3)) := by
  rw [realize_complement, realize_complement, realize_complement, relMap_graphStructure,
    relMap_graphStructure, relMap_graphStructure]
  decide

end Fin3

section Fin2

local instance : Language.graph.Structure (Fin 2) :=
  graphStructure 2 fun a b => a = 0 ∧ b = 1

/-- On `Fin 2` with the single edge `0 → 1`, the edge flips to a non-edge and `1 → 0` to an
edge. -/
example : ¬(complement.rel Language.adj).Realize (fun p => (![0, 1] : Fin 2 → Fin 2) p.1) ∧
    (complement.rel Language.adj).Realize (fun p => (![1, 0] : Fin 2 → Fin 2) p.1) := by
  rw [realize_complement, realize_complement, relMap_graphStructure, relMap_graphStructure]
  decide

end Fin2

/-! ### The copy of edges onto pairs -/

/-- The canonical ordered graph on `Fin n` given by an edge test. -/
def graphOn (n : ℕ) (hn : 2 ≤ n) (E : Fin n → Fin n → Prop) : Ordered.Structure Language.graph :=
  ⟨n, hn, graphStructure n E⟩

theorem relMap_graphOn {n : ℕ} {hn : 2 ≤ n} {E : Fin n → Fin n → Prop}
    (x : Fin 2 → Fin (graphOn n hn E).size) : RelMap Language.adj x ↔ E (x 0) (x 1) :=
  Iff.rfl

/-- The single edge `1 → 2` on `Fin 3`. -/
abbrev edge12 : Ordered.Structure Language.graph :=
  graphOn 3 (by decide) fun a b => a = 1 ∧ b = 2

/-- No edges on `Fin 3`. -/
abbrev noEdges : Ordered.Structure Language.graph :=
  graphOn 3 (by decide) fun _ _ => False

/-- The single edge `0 → 1` on `Fin 2`. -/
abbrev edge01 : Ordered.Structure Language.graph :=
  graphOn 2 le_rfl fun a b => a = 0 ∧ b = 1

/-- One unary relation symbol. -/
inductive URel : ℕ → Type where
  | u : URel 1

/-- A vocabulary with one unary relation. -/
def unary : Language := ⟨fun _ => Empty, URel⟩
  deriving IsRelational

/-- The unary relation symbol of `unary`. -/
abbrev uRel : unary.Relations 1 := .u

/-- `U(⟨a, b⟩) := E(a, b)`: a two-dimensional first-order projection with no guard. -/
noncomputable def copy : FullTupleInterpretation Language.graph unary 2 :=
  FullTupleInterpretation.ofProjection (L' := unary) fun
    | URel.u => .leaf (.rel Language.adj (fun i => (0, i)) false)

theorem isProjection_copy : copy.IsProjection :=
  FullTupleInterpretation.isProjection_ofProjection _

/-- The image of `copy`. -/
noncomputable abbrev copyMap : Ordered.Structure Language.graph → Ordered.Structure unary :=
  copy.toDomainInterpretation.map (copy.admissible_toDomainInterpretation two_pos)

theorem isProjectionMap_copyMap : IsProjectionMap copyMap :=
  isProjection_copy.isProjectionMap two_pos

/-- The image element of the pair `(a, b)`, at its lexicographic rank. -/
noncomputable def pairElt (M : Ordered.Structure Language.graph) (a b : Fin M.size) :
    copyMap M :=
  Fin.cast (FullTupleInterpretation.card_toDomainInterpretation M).symm (lexEquiv ![a, b])

/-- The image relation at the pair `(a, b)` is the input edge `(a, b)`. -/
theorem relMap_copyMap (M : Ordered.Structure Language.graph) (a b : Fin M.size) :
    RelMap (M := copyMap M) uRel ![pairElt M a b] ↔ RelMap Language.adj ![a, b] := by
  rw [FullTupleInterpretation.relMap_map_toDomainInterpretation two_pos]
  change (copy.rel uRel).Realize _ ↔ _
  rw [copy, FullTupleInterpretation.rel_ofProjection, ProjectionFormula.realize_toOrdered]
  change RelMap Language.adj _ ↔ _
  refine iff_of_eq (congrArg (RelMap Language.adj) (funext fun i => ?_))
  change lexEquiv.symm (Fin.cast (FullTupleInterpretation.card_toDomainInterpretation M)
    (Fin.cast (FullTupleInterpretation.card_toDomainInterpretation M).symm
      (lexEquiv ![a, b]))) i = ![a, b] i
  rw [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]

/-- At `n = 3`, the pair `(1, 2)` has lexicographic rank `5`. -/
example : lexRank (![1, 2] : Fin 2 → Fin 3) = 5 := by
  simp [lexRank_apply, Fin.sum_univ_two]

/-- The image element at the pair `(1, 2)` of a three-element input is the element `5`. -/
example : (pairElt edge12 ⟨1, by decide⟩ ⟨2, by decide⟩).val = 5 := by
  change lexRank (![1, 2] : Fin 2 → Fin 3) = 5
  simp [lexRank_apply, Fin.sum_univ_two]

/-- The image relation at `5` depends on the input edge `(1, 2)`: present in `edge12`, absent in
`noEdges`, which differ only there. -/
example : RelMap (M := copyMap edge12) uRel ![pairElt edge12 ⟨1, by decide⟩ ⟨2, by decide⟩] ∧
    ¬RelMap (M := copyMap noEdges) uRel ![pairElt noEdges ⟨1, by decide⟩ ⟨2, by decide⟩] := by
  rw [relMap_copyMap, relMap_copyMap, relMap_graphOn, relMap_graphOn]
  exact ⟨⟨rfl, rfl⟩, id⟩

/-- At `n = 2`, the image relation at the pair `(0, 1)` is the input edge `(0, 1)`, and at
`(1, 0)` it is the absent edge `(1, 0)`. -/
example : RelMap (M := copyMap edge01) uRel ![pairElt edge01 ⟨0, by decide⟩ ⟨1, by decide⟩] ∧
    ¬RelMap (M := copyMap edge01) uRel ![pairElt edge01 ⟨1, by decide⟩ ⟨0, by decide⟩] := by
  rw [relMap_copyMap, relMap_copyMap, relMap_graphOn, relMap_graphOn]
  exact ⟨⟨rfl, rfl⟩, fun h => absurd (congrArg Fin.val h.1) (by decide)⟩

/-! ### The copy of a nullary relation -/

/-- One nullary relation symbol. -/
inductive PRel : ℕ → Type where
  | p : PRel 0

/-- A vocabulary with one nullary relation. -/
def nullary : Language := ⟨fun _ => Empty, PRel⟩
  deriving IsRelational

/-- The nullary relation symbol of `nullary`. -/
abbrev pRel : nullary.Relations 0 := .p

/-- `Q() := P()` in dimension `k`. -/
noncomputable def nullaryCopy (k : ℕ) : FullTupleInterpretation nullary nullary k :=
  FullTupleInterpretation.ofQFProjection (L' := nullary) fun
    | PRel.p => .leaf (.rel pRel Fin.elim0 false)

theorem isQFProjection_nullaryCopy (k : ℕ) : (nullaryCopy k).IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection _ fun R => ?_
  cases R
  exact ProjectionFormula.isQF_leaf _

/-- The two-element structure where the nullary relation has truth value `b`. -/
def nullaryOn (b : Prop) : Ordered.Structure nullary :=
  ⟨2, le_rfl, { RelMap := fun | .p, _ => b }⟩

/-- The one-dimensional image of `nullaryCopy`. -/
noncomputable abbrev nullaryMap : Ordered.Structure nullary → Ordered.Structure nullary :=
  (nullaryCopy 1).toDomainInterpretation.map
    ((nullaryCopy 1).admissible_toDomainInterpretation one_pos)

/-- The image of `nullaryOn b` has the same truth value `b`. -/
theorem relMap_nullaryMap (b : Prop) (x : Fin 0 → nullaryMap (nullaryOn b)) :
    RelMap pRel x ↔ b := by
  rw [FullTupleInterpretation.relMap_map_toDomainInterpretation one_pos]
  change ((nullaryCopy 1).rel pRel).Realize _ ↔ _
  rw [nullaryCopy, FullTupleInterpretation.realize_rel_ofQFProjection]
  exact Iff.rfl

example : RelMap (M := nullaryMap (nullaryOn True)) pRel ![] :=
  (relMap_nullaryMap True _).mpr trivial

example : ¬RelMap (M := nullaryMap (nullaryOn False)) pRel ![] :=
  (relMap_nullaryMap False _).mp

/-! ### Dimension zero is rejected -/

/-- The nullary copy in dimension zero is a quantifier-free projection, but its image of a
two-element structure has one element, so it is not admissible: projection maps require positive
dimension. -/
example : (nullaryCopy 0).IsQFProjection ∧ ¬(nullaryCopy 0).toDomainInterpretation.Admissible :=
  ⟨isQFProjection_nullaryCopy 0,
    FullTupleInterpretation.not_admissible_toDomainInterpretation_zero _⟩

/-! ### A conjunction is not a projection map -/

/-- Two unary relation symbols. -/
inductive PQRel : ℕ → Type where
  | p : PQRel 1
  | q : PQRel 1

/-- A vocabulary with two unary relations. -/
def pq : Language := ⟨fun _ => Empty, PQRel⟩
  deriving IsRelational

/-- The relation symbol `P` of `pq`. -/
abbrev pqP : pq.Relations 1 := .p

/-- The relation symbol `Q` of `pq`. -/
abbrev pqQ : pq.Relations 1 := .q

/-- `P(x) ∧ Q(x)` in the ordered vocabulary. -/
noncomputable def conjFormula : (language pq).Formula (Fin 1 × Fin 1) :=
  (LHom.sumInl : pq →ᴸ language pq).onFormula
    (Relations.formula₁ pqP (.var (0, 0)) ⊓ Relations.formula₁ pqQ (.var (0, 0)))

/-- `T(x) := P(x) ∧ Q(x)`. -/
noncomputable def conj : FullTupleInterpretation pq unary 1 where
  rel | URel.u => conjFormula

/-- The conjunction is quantifier-free and mentions no numeric symbol, `BIT` included. -/
example : (conj.rel uRel).IsQF := by
  change BoundedFormula.IsQF ((LHom.sumInl : pq →ᴸ language pq).onFormula _)
  fo_qf

/-- `P` and `Q` constant on a two-element universe, with truth values `a` and `b`. -/
@[instance_reducible]
def pqStructure (a b : Bool) : pq.Structure (Fin 2) where
  RelMap
    | .p, _ => a = true
    | .q, _ => b = true

/-- The canonical ordered structure of `pqStructure a b`. -/
def pqOn (a b : Bool) : Ordered.Structure pq := ⟨2, le_rfl, pqStructure a b⟩

/-- The image of `conj`. -/
noncomputable abbrev conjMap : Ordered.Structure pq → Ordered.Structure unary :=
  conj.toDomainInterpretation.map (conj.admissible_toDomainInterpretation one_pos)

theorem relMap_conjMap (a b : Bool) (y : Fin 1 → conjMap (pqOn a b)) :
    RelMap (M := conjMap (pqOn a b)) uRel y ↔ a = true ∧ b = true := by
  rw [FullTupleInterpretation.relMap_map_toDomainInterpretation one_pos]
  change conjFormula.Realize (M := Fin (pqOn a b).size) _ ↔ _
  rw [conjFormula, realize_inputFormula, Formula.realize_inf, Formula.realize_rel₁,
    Formula.realize_rel₁]
  exact Iff.rfl

/-- Equal ordered structures have the same relations, up to the size cast. -/
theorem relMap_of_eq {L : Language} {M N : Ordered.Structure L} (h : M = N) {r : ℕ}
    (R : L.Relations r) (x : Fin r → N) :
    RelMap R (Fin.cast (congrArg Ordered.Structure.size h).symm ∘ x) ↔ RelMap R x := by
  subst h
  exact Iff.rfl

/-- **A conjunction of two input bits is not a projection map**, although it is a quantifier-free
full-tuple interpretation: every output bit of a projection is a single input literal chosen from
the address alone (`IsProjection.exists_literal`), and no literal of `pq` is `P(x) ∧ Q(x)` on all
four constant structures of size two. -/
theorem not_isProjectionMap_conjMap : ¬IsProjectionMap conjMap := by
  rintro ⟨k, J, hk, hJ, heq⟩
  have hpos : 0 < 2 ^ k := pow_pos two_pos k
  let x₀ : Fin 1 × Fin k → Fin 2 := fun p => lexEquiv.symm (⟨0, hpos⟩ : Fin (2 ^ k)) p.2
  obtain ⟨l, hl⟩ := hJ.exists_literal uRel x₀
  have key (a b : Bool) :
      letI := pqStructure a b
      l.Realize x₀ ↔ a = true ∧ b = true := by
    let := pqStructure a b
    let M := pqOn a b
    let y : Fin 1 → J.toDomainInterpretation.map
        (J.admissible_toDomainInterpretation hk) M :=
      fun _ => Fin.cast (FullTupleInterpretation.card_toDomainInterpretation M).symm ⟨0, hpos⟩
    rw [← hl, ← relMap_conjMap a b
        (Fin.cast (congrArg Ordered.Structure.size (congrFun heq M)).symm ∘ y),
      relMap_of_eq (congrFun heq M) uRel y,
      FullTupleInterpretation.relMap_map_toDomainInterpretation hk]
    exact Iff.rfl
  cases l with
  | const c =>
    have h₀ := key false false
    have h₁ := key true true
    simp only [InputLiteral.Realize, Bool.false_eq_true, and_self, iff_false,
      iff_true] at h₀ h₁
    exact h₀ h₁
  | rel R args neg =>
    cases R <;> cases neg <;>
      have h₀ := key false true <;> have h₁ := key true false <;> have h₂ := key true true <;>
      simp [InputLiteral.Realize, RelMap] at h₀ h₁ h₂

/-! ### The successor atom of the guard vocabulary -/

/-- On `Fin 3`, successor holds on `(1, 2)`, does not wrap from `2` to `0`, and `x = 1` is the
atom `succ 0 x`. -/
example : (QFNumeric.succ (.var 0) (.var 1) : qfNumericLanguage.Formula (Fin 2)).Realize
      (![1, 2] : Fin 2 → Fin 3) ∧
    ¬(QFNumeric.succ (.var 0) (.var 1) : qfNumericLanguage.Formula (Fin 2)).Realize
      (![2, 0] : Fin 2 → Fin 3) ∧
    (QFNumeric.succ QFNumeric.zero (.var 0) : qfNumericLanguage.Formula (Fin 1)).Realize
      (![1] : Fin 1 → Fin 3) := by
  simp only [QFNumeric.realize_succ, Term.realize_var, QFNumeric.realize_zero_val]
  decide

/-- The translation into the canonical numeric vocabulary agrees on the same instances. -/
example : Formula.Realize (toNumeric (QFNumeric.succ (.var 0) (.var 1) :
        qfNumericLanguage.Formula (Fin 2))) (![1, 2] : Fin 2 → Fin 3) ∧
    ¬Formula.Realize (toNumeric (QFNumeric.succ (.var 0) (.var 1) :
        qfNumericLanguage.Formula (Fin 2))) (![2, 0] : Fin 2 → Fin 3) := by
  simp only [realize_toNumeric_formula, QFNumeric.realize_succ, Term.realize_var]
  decide

/-! ### Logspace simulation -/

/-- The complement map is simulated in logarithmic space: projection maps are domain maps. -/
example (v : Vocabulary Language.graph) :
    ∃ F, Turing.MultiTapeTM.ComputableInLogSpace F encStructure encStructure ∧
      ∀ a, decode? v (F a) = (decode? v a).map
        (complement.toDomainInterpretation.map
          (complement.admissible_toDomainInterpretation one_pos)) :=
  (isQFProjection_complement.isQFProjectionMap one_pos).isProjectionMap.isDomainMap
    |>.exists_computableInLogSpace v v

end CslibFrontierTests.OrderedProjection
