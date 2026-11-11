/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reachability
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure
import CslibFrontier.Foundations.Relation.Transport

/-! # Ordered `Reach` native `NL` membership, `STCON` bridges, and `FO`-completeness clients -/

@[expose] public section

namespace Cslib.Tests.OrderedReachCompleteness

open FirstOrder Language Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered Cslib.Complexity

/-! ### Helper constructor for concrete ordered directed graphs -/

/-- Build an ordered directed graph on `Fin n` (`2 ≤ n`) from a Boolean adjacency predicate. -/
def mkOrderedGraph (n : ℕ) (hn : 2 ≤ n) (edge : Fin n → Fin n → Bool) :
    Ordered.Structure Language.graph where
  size := n
  size_ge_two := hn
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .adj, x => edge (x 0) (x 1) = true }

theorem graphAdj_mkOrderedGraph {n : ℕ} (hn : 2 ≤ n) (edge : Fin n → Fin n → Bool)
    (x y : Fin n) :
    graphAdj (mkOrderedGraph n hn edge) x y ↔ edge x y = true :=
  Iff.rfl

/-! ### Concrete positive and negative `Reach` instances (directed arcs and self-loops) -/

/-- `Fin 2` with the single forward arc `0 → 1`. -/
def twoForwardGraph : Ordered.Structure Language.graph :=
  mkOrderedGraph 2 (by decide) fun x y => x == 0 && y == 1

/-- `Fin 2` with the reverse arc `1 → 0` and self-loops `0 → 0`, `1 → 1`. -/
def twoReverseLoopsGraph : Ordered.Structure Language.graph :=
  mkOrderedGraph 2 (by decide) fun x y => (x == 1 && y == 0) || x == y

/-- `0 → 1` reaches `max = 1` on `Fin 2`. -/
example : twoForwardGraph ∈ Reach := by
  rw [mem_Reach]
  exact Relation.ReflTransGen.single (by decide : (0 : Fin 2) == 0 && (1 : Fin 2) == 1)

/-- Reverse arc `1 → 0` and self-loops `0 → 0`, `1 → 1` do not make `1` reachable from `0`:
`Language.graph.Structure` permits directed edges and self-loops without symmetry. -/
theorem twoReverseLoopsGraph_not_mem_Reach : twoReverseLoopsGraph ∉ Reach := by
  rw [mem_Reach]
  intro h
  have hinv : ∀ {w : Fin 2}, Relation.ReflTransGen (graphAdj twoReverseLoopsGraph) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail u w _ huw ih =>
      subst ih
      have hedge : ((0 : Fin 2) == 1 && w == 0 || (0 : Fin 2) == w) = true := huw
      revert hedge
      fin_cases w <;> decide
  have h10 : (1 : Fin 2) = 0 := hinv h
  exact absurd h10 (by decide)

/-- `Fin 4` with the non-monotone directed path `0 → 2 → 1 → 3`. -/
def fourZigzagGraph : Ordered.Structure Language.graph :=
  mkOrderedGraph 4 (by decide) fun x y =>
    (x == 0 && y == 2) || (x == 2 && y == 1) || (x == 1 && y == 3)

/-- `0 → 2 → 1 → 3` reaches `max = 3` on `Fin 4` despite stepping backwards in `<`. -/
theorem fourZigzagGraph_mem_Reach : fourZigzagGraph ∈ Reach := by
  rw [mem_Reach]
  have h02 : graphAdj fourZigzagGraph (0 : Fin 4) (2 : Fin 4) := by
    change ((0 : Fin 4) == 0 && (2 : Fin 4) == 2 || _ || _) = true
    decide
  have h21 : graphAdj fourZigzagGraph (2 : Fin 4) (1 : Fin 4) := by
    change (_ || (2 : Fin 4) == 2 && (1 : Fin 4) == 1 || _) = true
    decide
  have h13 : graphAdj fourZigzagGraph (1 : Fin 4) (3 : Fin 4) := by
    change (_ || _ || (1 : Fin 4) == 1 && (3 : Fin 4) == 3) = true
    decide
  exact ((Relation.ReflTransGen.single h02).tail h21).tail h13

/-- `Fin 4` with directed cycle `0 → 1 → 2 → 0` and isolated self-loop `3 → 3`. -/
def fourCycleIsolatedMaxGraph : Ordered.Structure Language.graph :=
  mkOrderedGraph 4 (by decide) fun x y =>
    (x == 0 && y == 1) || (x == 1 && y == 2) || (x == 2 && y == 0) || (x == 3 && y == 3)

/-- A directed cycle on `{0, 1, 2}` and a self-loop at `max = 3` never reach `3` from `0`. -/
example : fourCycleIsolatedMaxGraph ∉ Reach := by
  rw [mem_Reach]
  intro h
  have hinv : ∀ {w : Fin 4},
      Relation.ReflTransGen (graphAdj fourCycleIsolatedMaxGraph) 0 w → w.val < 3 := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail u w _ huw ih =>
      have hedge :
          ((u == 0 && w == 1) || (u == 1 && w == 2) ||
            (u == 2 && w == 0) || (u == 3 && w == 3)) = true := huw
      revert ih hedge
      fin_cases u <;> fin_cases w <;> decide
  exact absurd (hinv h) (by decide)

/-! ### Endpoint normalization (`STReach` and `stReachToReachInterpretation`, including `s = t`) -/

/-- Edgeless graph structure on `Fin 3`. -/
@[instance_reducible]
def threeEmptyGraph : Language.graph.Structure (Fin 3) where
  funMap f := isEmptyElim f
  RelMap | .adj, _ => False

/-- `Fin 3` with the single backward edge `2 → 0`. -/
@[instance_reducible]
def threeBackEdgeGraph : Language.graph.Structure (Fin 3) where
  funMap f := isEmptyElim f
  RelMap | .adj, x => x 0 = 2 ∧ x 1 = 0

/-- **Endpoint normalization handles `s = t` on an edgeless graph**: marking `(1, 1)` on `Fin 3`
produces a member of `STReach` whose `stReachToReachInterpretation` image (of size `27`) belongs
to `Reach`. -/
example :
    let M := mkMarkedGraph (by decide) threeEmptyGraph 1 1
    let hI := stReachToReachInterpretation.admissible_toDomainInterpretation (by decide)
    M ∈ STReach ∧
      (stReachToReachInterpretation.toDomainInterpretation.map hI M).size = 27 ∧
      stReachToReachInterpretation.toDomainInterpretation.map hI M ∈ Reach := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_STReach_mkMarkedGraph]
  · exact stReachToReachInterpretation.card_toDomainInterpretation _
  · rw [mem_Reach_stReachToReachInterpretation, mem_STReach_mkMarkedGraph]

/-- **Endpoint normalization for `s ≠ t` (`s = 2, t = 0`)**: `2 → 0` makes `(2, 0)` reachable in
`STReach` (and in its `Reach` image), while the reversed query `(0, 2)` is unreachable. -/
example :
    let hI := stReachToReachInterpretation.admissible_toDomainInterpretation (by decide)
    let Mpos := mkMarkedGraph (by decide) threeBackEdgeGraph 2 0
    let Mneg := mkMarkedGraph (by decide) threeBackEdgeGraph 0 2
    stReachToReachInterpretation.toDomainInterpretation.map hI Mpos ∈ Reach ∧
      stReachToReachInterpretation.toDomainInterpretation.map hI Mneg ∉ Reach := by
  refine ⟨?_, ?_⟩
  · rw [mem_Reach_stReachToReachInterpretation, mem_STReach_mkMarkedGraph]
    exact Relation.ReflTransGen.single ⟨rfl, rfl⟩
  · rw [mem_Reach_stReachToReachInterpretation, mem_STReach_mkMarkedGraph]
    intro h
    have hinv : ∀ {w : Fin 3},
        Relation.ReflTransGen (fun x y : Fin 3 => threeBackEdgeGraph.RelMap Language.adj ![x, y])
          0 w → w = 0 := by
      intro w hw
      induction hw with
      | refl => rfl
      | @tail u w _ huw ih =>
        subst ih
        rcases huw with ⟨h02, _⟩
        have h02' : (0 : Fin 3) = 2 := h02
        exact absurd h02' (by decide)
    exact absurd (hinv h) (by decide)

/-! ### Semantic and logspace bridges between `Reach` and `STCON` -/

/-- Degenerate `1`-vertex `STCON` instance (`s = 0, t = 0`, no edges). -/
def oneVertexSTCON : STCONInstance where
  n := 1
  adj _ _ := false
  s := 0
  t := 0

/-- `STCONInstance.toOrderedGraph` pads `n = 1` to universe size `3` (`≥ 2`) and preserves trivial
`s = t` reachability. -/
example :
    oneVertexSTCON ∈ STCON ∧
      oneVertexSTCON.toOrderedGraph.size = 3 ∧
      oneVertexSTCON.toOrderedGraph ∈ Reach := by
  refine ⟨?_, rfl, ?_⟩
  · rw [mem_STCON]
    exact .refl
  · rw [STCONInstance.toOrderedGraph_mem_Reach, mem_STCON]
    exact .refl

/-- `3`-vertex `STCON` instance with path `2 → 1 → 0` from `s = 2` to `t = 0`. -/
abbrev threePathSTCON : STCONInstance where
  n := 3
  adj x y := (x == 2 && y == 1) || (x == 1 && y == 0)
  s := 2
  t := 0

/-- `3`-vertex `STCON` negative control with reversed path `0 → 1 → 2` for `s = 2, t = 0`. -/
abbrev threeReverseSTCON : STCONInstance where
  n := 3
  adj x y := (x == 0 && y == 1) || (x == 1 && y == 2)
  s := 2
  t := 0

/-- Both semantic instance bridges agree on positive and negative `STCON` and `Reach` instances. -/
example :
    threePathSTCON.toOrderedGraph ∈ Reach ∧
      threeReverseSTCON.toOrderedGraph ∉ Reach ∧
      Reach.toSTCONInstance fourZigzagGraph ∈ STCON ∧
      Reach.toSTCONInstance twoReverseLoopsGraph ∉ STCON := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [STCONInstance.toOrderedGraph_mem_Reach, mem_STCON]
    have h21 : threePathSTCON.Adj 2 1 := rfl
    have h10 : threePathSTCON.Adj 1 0 := rfl
    exact (Relation.ReflTransGen.single h21).tail h10
  · rw [STCONInstance.toOrderedGraph_mem_Reach, mem_STCON]
    intro h
    have hinv : ∀ {w : Fin 3},
        Relation.ReflTransGen threeReverseSTCON.Adj 2 w → w = 2 := by
      intro w hw
      induction hw with
      | refl => rfl
      | @tail u w _ huw ih =>
        subst ih
        have hedge : (((2 : Fin 3) == 0 && w == 1) || ((2 : Fin 3) == 1 && w == 2)) = true := huw
        revert hedge
        fin_cases w <;> decide
    have h02 : (0 : Fin 3) = 2 := hinv h
    exact absurd h02 (by decide)
  · rw [Reach.toSTCONInstance_mem_STCON]
    exact fourZigzagGraph_mem_Reach
  · rw [Reach.toSTCONInstance_mem_STCON]
    exact twoReverseLoopsGraph_not_mem_Reach

/-- Bidirectional logspace reductions transfer between complements of `Reach` and `STCON`, and
logspace `NL`-completeness reduces every `NL` problem to `Reach`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ NL enc) :
    LogSpaceReducible encStructure encSTCON (Reach.encodedLanguage graphVocabulary)ᶜ STCONᶜ ∧
      LogSpaceReducible encSTCON encStructure STCONᶜ (Reach.encodedLanguage graphVocabulary)ᶜ ∧
      LogSpaceReducible enc encStructure A (Reach.encodedLanguage graphVocabulary) :=
  let ⟨_, hhard⟩ := reach_logSpaceComplete_NL
  ⟨reach_logSpaceReducible_STCON.compl,
    stcon_logSpaceReducible_Reach.compl,
    hhard enc A hA⟩

/-! ### Unconditional ordered `FO`-completeness and `NL` closure under `Ordered.Reduces` -/

/-- Non-reachability (`0` cannot reach `max`) is defined by `reachSentence.neg`, which is outside
positive FO(TC) syntax yet lies in native `NL`; Theorem 3.16 therefore reduces `Reachᶜ` to `Reach`
by a single positive-dimensional `FullTupleInterpretation`. -/
theorem reduces_compl_Reach :
    ¬ TC.Positive reachSentence.neg true ∧
      Reduces (Reachᶜ) Reach ∧
      ∃ (d : ℕ) (hd : 0 < d) (I : FullTupleInterpretation Language.graph Language.graph d),
        ∀ M : Ordered.Structure Language.graph,
          M ∉ Reach ↔
            I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hd) M ∈ Reach := by
  have hnot_pos : ¬ TC.Positive reachSentence.neg true := fun h => Bool.false_ne_true h.1
  have htc : TCDefinable (Reachᶜ) :=
    ⟨reachSentence.neg, fun M => by
      rw [Set.mem_compl_iff, Operator.Formula.realize_neg, ← realize_reachSentence]⟩
  have hNL : Query.encodedLanguage (Reachᶜ) graphVocabulary ∈ NL encStructure :=
    htc.encodedLanguage_mem_NL graphVocabulary
  refine ⟨hnot_pos, (reduces_Reach_iff_encodedLanguage_mem_NL graphVocabulary).mpr hNL, ?_⟩
  exact exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL graphVocabulary hNL

/-- Converse ordered reachability: `max` reaches `0` along directed edges. -/
def ReverseReach : Ordered.Query Language.graph :=
  {M | Relation.ReflTransGen (graphAdj M) M.maxElem 0}

/-- Dimension-1 full-tuple interpretation reversing every directed edge `E'(x, y) := E(y, x)`. -/
def transposeGraphInterpretation : FullTupleInterpretation Language.graph Language.graph 1 where
  rel
    | .adj =>
      Relations.formula₂
        ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onRelation Language.adj)
        (.var (1, 0)) (.var (0, 0))

/-- Reversing edges reduces `ReverseReach` to `Reach` under `Ordered.Reduces`. -/
theorem reverseReach_reduces_Reach : Reduces ReverseReach Reach := by
  refine transposeGraphInterpretation.reduces (by decide) fun M => ?_
  let I := transposeGraphInterpretation
  let hI := I.admissible_toDomainInterpretation (by decide)
  have hc : (I.toDomainInterpretation.map hI M).size = M.size ^ 1 :=
    I.card_toDomainInterpretation M
  have hc1 : (I.toDomainInterpretation.map hI M).size = M.size := hc.trans (pow_one M.size)
  let e : Fin M.size ≃ Fin (I.toDomainInterpretation.map hI M).size := finCongr hc1.symm
  have hadj (x y : Fin M.size) :
      Function.swap (graphAdj M) x y ↔
        graphAdj (I.toDomainInterpretation.map hI M) (e x) (e y) := by
    rw [graphAdj, I.relMap_map_toDomainInterpretation (by decide)]
    change graphAdj M y x ↔
      (I.rel Language.adj).Realize
        (fun p => lexEquiv.symm (Fin.cast hc (![e x, e y] p.1)) p.2)
    have harg : (fun p : Fin 2 × Fin 1 =>
        lexEquiv.symm (Fin.cast hc (![e x, e y] p.1)) p.2) = fun p => ![x, y] p.1 := by
      funext p
      rcases p with ⟨a, j⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have hlex (z : Fin M.size) : lexEquiv (fun _ : Fin 1 => z) = Fin.cast hc (e z) := by
        apply Fin.ext
        change lexRank (fun _ : Fin 1 => z) = z.val
        rw [lexRank_apply, Fin.sum_univ_one]
        simp
      change lexEquiv.symm (Fin.cast hc (![e x, e y] a)) 0 = ![x, y] a
      cases a using Fin.cases with
      | zero =>
        change lexEquiv.symm (Fin.cast hc (e x)) 0 = x
        rw [← hlex x, Equiv.symm_apply_apply]
      | succ a' =>
        have ha' : a' = 0 := Subsingleton.elim _ _
        subst ha'
        change lexEquiv.symm (Fin.cast hc (e y)) 0 = y
        rw [← hlex y, Equiv.symm_apply_apply]
    rw [harg]
    simp only [I, transposeGraphInterpretation, Formula.realize_rel₂, Term.realize_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rfl
  have he0 : e 0 = 0 := Fin.ext rfl
  have hemax : e M.maxElem = (I.toDomainInterpretation.map hI M).maxElem := by
    apply Fin.ext
    change M.size - 1 = (I.toDomainInterpretation.map hI M).size - 1
    rw [hc1]
  change Relation.ReflTransGen (graphAdj M) M.maxElem 0 ↔
    Relation.ReflTransGen (graphAdj (I.toDomainInterpretation.map hI M)) 0
      (I.toDomainInterpretation.map hI M).maxElem
  rw [← Relation.reflTransGen_swap, ← he0, ← hemax]
  exact Relation.reflTransGen_equiv_iff e hadj 0 M.maxElem

/-- Pulling `NL` membership back along `Ordered.Reduces` via `Reduces.encodedLanguage_mem_NL`,
with concrete separation from `Reach` on `Fin 2`. -/
example :
    ReverseReach.encodedLanguage graphVocabulary ∈ NL encStructure ∧
      twoReverseLoopsGraph ∈ ReverseReach ∧
      twoForwardGraph ∉ ReverseReach := by
  refine ⟨reverseReach_reduces_Reach.encodedLanguage_mem_NL graphVocabulary graphVocabulary
    reach_encodedLanguage_mem_NL, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      (by decide : ((1 : Fin 2) == 1 && (0 : Fin 2) == 0 || (1 : Fin 2) == (0 : Fin 2)) = true)
  · intro h
    have hinv : ∀ {w : Fin 2},
        Relation.ReflTransGen (graphAdj twoForwardGraph) 1 w → w = 1 := by
      intro w hw
      induction hw with
      | refl => rfl
      | @tail u w _ huw ih =>
        subst ih
        have hedge : ((1 : Fin 2) == 0 && w == 1) = true := huw
        revert hedge
        fin_cases w <;> decide
    have h01 : (0 : Fin 2) = 1 := hinv h
    exact absurd h01 (by decide)

end Cslib.Tests.OrderedReachCompleteness
