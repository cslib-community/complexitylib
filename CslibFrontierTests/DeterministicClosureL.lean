/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure
import Mathlib.ModelTheory.Graph

/-!
# FO(DTC) ⊆ L clients

Deterministic reachability from `0` to `max` in a directed graph is defined by one FO(DTC)
sentence, so its encoded language is in native `L`. Concrete three-vertex graphs check that the
query is not vacuous and that it differs from ordinary reachability: a deterministic path, a
branching vertex, an unreachable target, cycles off and through the target, a negated closure,
a closure of width zero, and a closure nested in the body of another, parameterized by the
outer bound variable.
-/

namespace CslibFrontierTests.DeterministicClosureL

open FirstOrder Language Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

/-- The headline applies to every query defined by an FO(DTC) sentence. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : DTCDefinable K) : K.encodedLanguage v ∈ Cslib.Complexity.L encStructure :=
  hK.encodedLanguage_mem_L v

/-- First-order definable queries are covered through FO ⊆ FO(DTC). -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Ordered.Query L}
    (hK : Definable K) : K.encodedLanguage v ∈ Cslib.Complexity.L encStructure :=
  hK.dtcDefinable.encodedLanguage_mem_L v

/-! ### Deterministic reachability from `0` to `max` -/

/-- The vocabulary listing the adjacency relation. -/
def vocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

/-- The edge body, with the two endpoints as the bound variables of the closure, over any outer
variables `α`. -/
def edgeBody {α : Type} :
    Operator.Formula (language Language.graph) TC.shape [] (α ⊕ Fin (2 * 1)) :=
  .ofFO (Relations.formula₂
    ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onRelation adj)
    (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- `max` is reachable from `0`; read with `DTC.interpretation`, along unique successors. -/
def dreach : Operator.Formula (language Language.graph) TC.shape [] Empty :=
  TC.tc edgeBody (TC.pair ![zero Language.graph] ![max Language.graph])

/-- Adjacency in an ordered graph. -/
def Edge (M : Ordered.Structure Language.graph) (x y : Fin M.size) : Prop :=
  Structure.RelMap (L := Language.graph) adj ![x, y]

/-- The deterministic reachability query, stated semantically on vertices: the walk from `0`
along unique successors reaches `max`. -/
def DReach : Ordered.Query Language.graph :=
  {M | Relation.ReflTransGen (DTC.deterministicReduct (Edge M))
    ((zero Language.graph).realize (Empty.elim : Empty → Fin M.size))
    ((max Language.graph).realize (Empty.elim : Empty → Fin M.size))}

theorem realize_edgeBody (M : Ordered.Structure Language.graph)
    (I : Operator.Interpretation TC.shape (Fin M.size)) {α : Type} {v : α → Fin M.size}
    (us ws : Fin 1 → Fin M.size) :
    edgeBody.Realize I Operator.RelEnv.empty (Sum.elim v (TC.pair us ws)) ↔
      Edge M (us 0) (ws 0) := by
  simp only [edgeBody, Operator.Formula.realize_ofFO, Formula.realize_rel₂,
    LHom.map_onRelation]
  rfl

/-- Deterministic reachability between constant `1`-tuples is deterministic reachability
between their entries. -/
theorem reflTransGen_unary {β : Type*} (r : β → β → Prop) (x y : β) :
    Relation.ReflTransGen (DTC.deterministicReduct fun us ws : Fin 1 → β => r (us 0) (ws 0))
        (fun _ => x) (fun _ => y) ↔
      Relation.ReflTransGen (DTC.deterministicReduct r) x y := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift (fun us : Fin 1 → β => us 0)
      (fun _ _ huw => ⟨huw.1, fun z hz => congrFun (huw.2 (fun _ => z) hz) 0⟩) _ _ h
  · intro h
    exact Relation.ReflTransGen.lift (fun x : β => fun _ : Fin 1 => x)
      (fun _ _ hxy => ⟨hxy.1, fun zs hz => funext fun i => by
        rw [Subsingleton.elim i 0]; exact hxy.2 _ hz⟩) _ _ h

/-- The sentence `dreach`, read with deterministic closure, defines `DReach`. -/
theorem realize_dreach (M : Ordered.Structure Language.graph) :
    M ∈ DReach ↔
      dreach.Realize (M := M) DTC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [dreach, DTC.realize_tc_pair]
  simp only [realize_edgeBody, Matrix.cons_val_fin_one]
  exact (reflTransGen_unary _ _ _).symm

/-- **Deterministic reachability is in native `L`**, at the source-only encoding of graphs. -/
theorem dreach_mem_L : DReach.encodedLanguage vocabulary ∈ Cslib.Complexity.L encStructure :=
  DTCDefinable.encodedLanguage_mem_L ⟨dreach, realize_dreach⟩ vocabulary

/-! ### Concrete graphs -/

/-- The ordered graph on `Fin n` with edge relation `E`. -/
def graphOn (n : ℕ) (hn : 2 ≤ n) (E : Fin n → Fin n → Prop) : Ordered.Structure Language.graph where
  size := n
  size_ge_two := hn
  input.RelMap
    | .adj, xs => E (xs 0) (xs 1)

theorem mem_dReach_graphOn {n : ℕ} {hn : 2 ≤ n} {E : Fin n → Fin n → Prop} :
    graphOn n hn E ∈ DReach ↔
      Relation.ReflTransGen (DTC.deterministicReduct E) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ :=
  Iff.rfl

/-- The ordered graph on `Fin 3` with edge relation `E`. -/
abbrev graph3 (E : Fin 3 → Fin 3 → Prop) : Ordered.Structure Language.graph :=
  graphOn 3 (by omega) E

/-- The path `0 → 1 → 2`. -/
abbrev pathRel (x y : Fin 3) : Prop := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)

/-- Vertex `0` branches to `1` and to `2`. -/
abbrev branchRel (x y : Fin 3) : Prop := x = 0 ∧ y ≠ 0

/-- The single edge `0 → 1`; vertex `1` is a dead end. -/
abbrev deadEndRel (x y : Fin 3) : Prop := x = 0 ∧ y = 1

/-- The cycle `0 → 1 → 0`, which avoids the target `2`. -/
abbrev cycleRel (x y : Fin 3) : Prop := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

/-- The cycle `0 → 1 → 2 → 0`, through the target. -/
abbrev rotateRel (x y : Fin 3) : Prop := y = x + 1

/-- A deterministic path reaches the target. -/
theorem path_mem : graph3 pathRel ∈ DReach :=
  mem_dReach_graphOn.mpr (.head (b := 1) ⟨by decide, by decide⟩ (.single ⟨by decide, by decide⟩))

/-- A branching vertex has no unique successor, so the deterministic walk stops at `0`. -/
theorem branch_not_mem : graph3 branchRel ∉ DReach := by
  rw [mem_dReach_graphOn]
  intro h
  rcases h.cases_head with h | ⟨c, hc, -⟩
  · exact absurd h (by decide)
  · exact absurd ((hc.2 1 (by decide)).trans (hc.2 2 (by decide)).symm) (by decide)

/-- The same sentence read with ordinary closure holds on the branching graph: the edge `0 → 2`
is a path. -/
example : dreach.Realize (M := graph3 branchRel) TC.interpretation Operator.RelEnv.empty
    Empty.elim := by
  rw [dreach]
  refine TC.realize_tc_of_body _ _ _ _ _ ((realize_edgeBody _ _ _ _).mpr ?_)
  exact (show branchRel 0 2 by decide)

/-- No edge enters the target, so it is unreachable. -/
theorem deadEnd_not_mem : graph3 deadEndRel ∉ DReach := by
  rw [mem_dReach_graphOn]
  intro h
  rcases h.cases_tail with h | ⟨c, -, hc⟩
  · exact absurd h (by decide)
  · exact absurd hc.1.2 (by decide)

/-- The deterministic walk `0, 1, 0, 1, …` cycles forever without reaching the target. -/
theorem cycle_not_mem : graph3 cycleRel ∉ DReach := by
  rw [mem_dReach_graphOn]
  intro h
  have key : ∀ c : Fin 3, ¬ cycleRel c 2 := by decide
  rcases h.cases_tail with h | ⟨c, -, hc⟩
  · exact absurd h (by decide)
  · exact key c hc.1

/-- A cycle through the target reaches it. -/
theorem rotate_mem : graph3 rotateRel ∈ DReach :=
  mem_dReach_graphOn.mpr (.head (b := 1) ⟨by decide, by decide⟩ (.single ⟨by decide, by decide⟩))

/-- The language decided in `L` contains the encoding of the path and not that of the branching
graph. -/
example : encode vocabulary (graph3 pathRel) ∈ DReach.encodedLanguage vocabulary :=
  (mem_encodedLanguage_encode _ _ _).mpr path_mem

example : encode vocabulary (graph3 branchRel) ∉
    DReach.encodedLanguage vocabulary :=
  fun h => branch_not_mem ((mem_encodedLanguage_encode _ _ _).mp h)

/-! ### A negated closure -/

/-- The walk from `0` along unique successors does not reach `max`. -/
def NonDReach : Ordered.Query Language.graph := DReachᶜ

/-- The sentence `dreach.neg` defines `NonDReach`. -/
theorem realize_nonDReach (M : Ordered.Structure Language.graph) :
    M ∈ NonDReach ↔
      dreach.neg.Realize (M := M) DTC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [Operator.Formula.realize_neg, ← realize_dreach]
  rfl

/-- **Deterministic non-reachability is in native `L`**: a negated closure needs no inductive
counting. -/
example : NonDReach.encodedLanguage vocabulary ∈ Cslib.Complexity.L encStructure :=
  DTCDefinable.encodedLanguage_mem_L ⟨dreach.neg, realize_nonDReach⟩ vocabulary

example : graph3 cycleRel ∈ NonDReach := cycle_not_mem

example : graph3 pathRel ∉ NonDReach := fun h => h path_mem

/-! ### A nested, parameterized closure -/

/-- The outer edge `x → y` together with an inner closure, parameterized by the outer bound
variable `y`: the walk from `y` along unique successors reaches `max`. -/
def nestedBody :
    Operator.Formula (language Language.graph) TC.shape [] (Empty ⊕ Fin (2 * 1)) :=
  edgeBody.conj (TC.tc edgeBody (TC.pair ![Term.var (Sum.inr 1)] ![max Language.graph]))

/-- Deterministic reachability from `0` to `max` along the edges whose head deterministically
reaches `max`. -/
def nested : Operator.Formula (language Language.graph) TC.shape [] Empty :=
  TC.tc nestedBody (TC.pair ![zero Language.graph] ![max Language.graph])

example : TC.width nested = 1 := rfl

/-- The query defined by `nested`, stated semantically on vertices. -/
def NestedReach : Ordered.Query Language.graph :=
  {M | Relation.ReflTransGen
    (DTC.deterministicReduct fun x y => Edge M x y ∧
      Relation.ReflTransGen (DTC.deterministicReduct (Edge M)) y
        ((max Language.graph).realize (Empty.elim : Empty → Fin M.size)))
    ((zero Language.graph).realize (Empty.elim : Empty → Fin M.size))
    ((max Language.graph).realize (Empty.elim : Empty → Fin M.size))}

/-- The sentence `nested`, read with deterministic closure, defines `NestedReach`. -/
theorem realize_nested (M : Ordered.Structure Language.graph) :
    M ∈ NestedReach ↔
      nested.Realize (M := M) DTC.interpretation Operator.RelEnv.empty Empty.elim := by
  rw [nested, DTC.realize_tc_pair]
  simp only [nestedBody, Operator.Formula.realize_conj, DTC.realize_tc_pair, realize_edgeBody,
    Matrix.cons_val_fin_one, Term.realize_var, Sum.elim_inr]
  exact (reflTransGen_unary _ _ _).symm.trans (by simp only [reflTransGen_unary]; rfl)

/-- **The nested query is in native `L`**: the compiled inner loop runs inside the body of the
outer loop. -/
example : NestedReach.encodedLanguage vocabulary ∈ Cslib.Complexity.L encStructure :=
  DTCDefinable.encodedLanguage_mem_L ⟨nested, realize_nested⟩ vocabulary

theorem mem_nestedReach_graphOn {n : ℕ} {hn : 2 ≤ n} {E : Fin n → Fin n → Prop} :
    graphOn n hn E ∈ NestedReach ↔
      Relation.ReflTransGen (DTC.deterministicReduct fun x y =>
          E x y ∧ Relation.ReflTransGen (DTC.deterministicReduct E) y ⟨n - 1, by omega⟩)
        ⟨0, by omega⟩ ⟨n - 1, by omega⟩ :=
  Iff.rfl

/-- The inner closure prunes the dead end `1`, so the outer walk from the branching vertex `0`
is deterministic, although the plain deterministic walk stops there (`branch_not_mem`). -/
theorem branch_mem_nested : graph3 branchRel ∈ NestedReach := by
  refine mem_nestedReach_graphOn.mpr (.single ⟨⟨by decide, .refl⟩, fun z ⟨hz, hr⟩ => ?_⟩)
  rcases hr.cases_head with h | ⟨c, hc, -⟩
  · exact h
  · exact absurd hc.1.1 hz.2

/-- No edge enters the target, so the nested query fails as well. -/
theorem cycle_not_mem_nested : graph3 cycleRel ∉ NestedReach := by
  rw [mem_nestedReach_graphOn]
  intro h
  have key : ∀ c : Fin 3, ¬ cycleRel c 2 := by decide
  rcases h.cases_tail with h | ⟨c, -, hc⟩
  · exact absurd h (by decide)
  · exact key c hc.1.1

/-! ### Width zero -/

/-- A closure of width zero: the empty tuple reaches itself, so the sentence always holds. -/
def emptyWalk : Operator.Formula (language Language.graph) TC.shape [] Empty :=
  TC.tc (k := 0) (.ofFO ⊥) (TC.pair Fin.elim0 Fin.elim0)

example : TC.width emptyWalk = 0 := rfl

/-- The query containing every ordered graph. -/
def AllGraphs : Ordered.Query Language.graph := Set.univ

example : AllGraphs.encodedLanguage vocabulary ∈ Cslib.Complexity.L encStructure :=
  DTCDefinable.encodedLanguage_mem_L
    ⟨emptyWalk, fun _ => iff_of_true (Set.mem_univ _) (DTC.realize_tc_refl _ _ _ _)⟩ vocabulary

end CslibFrontierTests.DeterministicClosureL
