/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.ExtensionAxiom
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.ModelTheory.Order
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

/-! # Pebble games and finite-variable logic: checked instances

* **Variable reuse.** On linear orders, the two-variable formulas `chain m i` say that at least `m`
  elements lie strictly below `xᵢ`; they reuse both variables and have quantifier rank `m`
  ([Libkin2004], formula (11.4), in a variant with one quantifier per step). The sentence
  `atLeast m` separates `Fin (m + 1)` from `Fin m`, so Spoiler wins the `(m + 1)`-round
  `2`-pebble game on them.
* **Two pebbles do not suffice for triangles.** The cycle `C₆` and two disjoint triangles `2C₃`
  are both `2`-regular on six vertices. Duplicator wins the infinite `2`-pebble game on them, so
  they agree on every two-variable sentence; the three-variable sentence "there is a triangle"
  separates them, so Spoiler wins the `3`-round `3`-pebble game, and the hard direction turns
  this back into a separating Hintikka sentence. Color refinement does not separate this pair
  either (`CslibFrontierTests/Foundations/Combinatorics/SimpleGraph/ColorRefinement.lean`); by
  the Immerman–Lander theorem, still to be formalized, that is the counting-logic analogue of the
  `2`-pebble result. -/

@[expose] public section

namespace Cslib.Tests.FOPebbleGames

open FirstOrder Language Structure
open Cslib.Logic.FO

private theorem comp_vec_two {α β : Type*} (a : α → β) (i j : α) : a ∘ ![i, j] = ![a i, a j] :=
  (FinVec.map_eq a ![i, j]).symm

/-! ### Linear orders: variable reuse -/

instance (m : ℕ) : Language.order.Structure (Fin m) := orderStructure _

instance (m : ℕ) : Language.order.OrderedStructure (Fin m) := ⟨fun _ => Iff.rfl⟩

/-- `xᵢ < xⱼ`, as `¬ xⱼ ≤ xᵢ`. -/
def lt (i j : Fin 2) : FiniteVariable.Formula Language.order 2 :=
  (FiniteVariable.Formula.rel leSymb ![j, i]).not

/-- At least `m` elements lie strictly below `xᵢ`: there is `xⱼ < xᵢ` below which lie at least
`m - 1` elements, where `j` is the other variable. The variable `i` is quantified again inside. -/
def chain : ℕ → Fin 2 → FiniteVariable.Formula Language.order 2
  | 0, _ => ⊤
  | m + 1, i => .ex (i + 1) (lt (i + 1) i ⊓ chain m (i + 1))

/-- The order has more than `m` elements. -/
def atLeast (m : ℕ) : FiniteVariable.Formula Language.order 2 :=
  .ex 0 (chain m 0)

private theorem add_one_ne_self (i : Fin 2) : i + 1 ≠ i := by
  revert i
  decide

theorem realize_chain {n : ℕ} : ∀ (m : ℕ) (i : Fin 2) (a : Fin 2 → Fin n),
    (chain m i).Realize a ↔ m ≤ (a i).val
  | 0, i, a => by simp only [chain, FiniteVariable.Formula.realize_top, Nat.zero_le]
  | m + 1, i, a => by
    simp only [chain, lt, FiniteVariable.Formula.realize_ex, FiniteVariable.Formula.realize_inf,
      FiniteVariable.Formula.realize_not, FiniteVariable.Formula.realize_rel, realize_chain m,
      comp_vec_two, relMap_leSymb, Matrix.cons_val_zero, Matrix.cons_val_one, Function.update_self,
      Function.update_of_ne (add_one_ne_self i).symm, not_le, Fin.lt_def]
    constructor
    · rintro ⟨c, hc, hm⟩
      omega
    · intro h
      exact ⟨⟨m, by omega⟩, by simp only; omega, le_rfl⟩

theorem realize_atLeast {n m : ℕ} (a : Fin 2 → Fin n) : (atLeast m).Realize a ↔ m < n := by
  simp only [atLeast, FiniteVariable.Formula.realize_ex, realize_chain, Function.update_self]
  exact ⟨fun ⟨c, hc⟩ => by omega, fun h => ⟨⟨m, h⟩, le_rfl⟩⟩

theorem quantifierRank_chain : ∀ (m : ℕ) (i : Fin 2), (chain m i).quantifierRank = m
  | 0, _ => by simp only [chain, FiniteVariable.Formula.quantifierRank_top]
  | m + 1, i => by
    simp only [chain, lt, FiniteVariable.Formula.quantifierRank_ex,
      FiniteVariable.Formula.quantifierRank_inf, FiniteVariable.Formula.quantifierRank_not,
      FiniteVariable.Formula.quantifierRank_rel, quantifierRank_chain m, Nat.zero_max]

/-- `atLeast m` has quantifier rank `m + 1` although it uses only two variables. -/
theorem quantifierRank_atLeast (m : ℕ) : (atLeast m).quantifierRank = m + 1 := by
  rw [atLeast, FiniteVariable.Formula.quantifierRank_ex, quantifierRank_chain]

private theorem freeVars_lt_subset (i : Fin 2) :
    ((Finset.univ.image ![i, i + 1]) ∪ {i + 1}).erase (i + 1) ⊆ {i} := by
  revert i
  decide

theorem freeVars_chain_subset : ∀ (m : ℕ) (i : Fin 2), (chain m i).freeVars ⊆ {i}
  | 0, _ => by simp only [chain, FiniteVariable.Formula.freeVars_top, Finset.empty_subset]
  | m + 1, i => by
    simp only [chain, lt, FiniteVariable.Formula.freeVars_ex, FiniteVariable.Formula.freeVars_inf,
      FiniteVariable.Formula.freeVars_not, FiniteVariable.Formula.freeVars_rel]
    exact (Finset.erase_subset_erase _ (Finset.union_subset_union (subset_refl _)
      (freeVars_chain_subset m (i + 1)))).trans (freeVars_lt_subset i)

/-- `atLeast m` is a sentence. -/
theorem freeVars_atLeast (m : ℕ) : (atLeast m).freeVars = ∅ := by
  rw [atLeast, FiniteVariable.Formula.freeVars_ex, Finset.erase_eq_empty_iff]
  exact Finset.subset_singleton_iff.1 (freeVars_chain_subset m 0)

/-- Spoiler wins the `(m + 1)`-round `2`-pebble game on `Fin (m + 1)` and `Fin m`, from any
position with no pebbles placed: `atLeast m` has two variables and rank `m + 1`. -/
theorem not_pebbleWins_fin (m : ℕ) (a : Fin 2 → Fin (m + 1)) (b : Fin 2 → Fin m) :
    ¬ PebbleWins Language.order (m + 1) ∅ a b := fun h => by
  have := h.realize_iff (quantifierRank_atLeast m).le (by simp only [freeVars_atLeast,
    Finset.coe_empty, subset_refl])
  rw [realize_atLeast, realize_atLeast] at this
  omega

/-- The sentence is first-order: its translation to Mathlib's formulas holds in `Fin n` exactly
when `m < n`, and has the same quantifier rank. -/
example {n : ℕ} (m : ℕ) (a : Fin 2 → Fin n) :
    (atLeast m).toFormula.Realize a ↔ m < n := by
  rw [FiniteVariable.Formula.realize_toFormula, realize_atLeast]

example (m : ℕ) : quantifierRank (atLeast m).toFormula = m + 1 := by
  rw [FiniteVariable.Formula.quantifierRank_toFormula, quantifierRank_atLeast]

/-! ### `C₆` and two triangles -/

/-- Two disjoint triangles, on `Bool × Fin 3`. -/
def twoTriangles : SimpleGraph (Bool × Fin 3) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance : DecidableRel twoTriangles.Adj := fun x y =>
  inferInstanceAs (Decidable (x.1 = y.1 ∧ x.2 ≠ y.2))

instance : Language.graph.Structure (Fin 6) := (SimpleGraph.cycleGraph 6).structure

instance : Language.graph.Structure (Bool × Fin 3) := twoTriangles.structure

theorem relMap_adj_fin {x y : Fin 6} :
    RelMap adj ![x, y] ↔ (SimpleGraph.cycleGraph 6).Adj x y := Iff.rfl

theorem relMap_adj_twoTriangles {x y : Bool × Fin 3} :
    RelMap adj ![x, y] ↔ twoTriangles.Adj x y := Iff.rfl

variable {V W : Type*} [Language.graph.Structure V] [Language.graph.Structure W]

/-- With two pebbles in the language of graphs, a partial isomorphism on placed pebbles preserves
equality and adjacency between them. -/
theorem partialIsoOn_graph_iff {S : Set (Fin 2)} {a : Fin 2 → V} {b : Fin 2 → W} :
    PartialIsoOn Language.graph S a b ↔ ∀ i ∈ S, ∀ j ∈ S,
      (a i = a j ↔ b i = b j) ∧ (RelMap adj ![a i, a j] ↔ RelMap adj ![b i, b j]) := by
  constructor
  · intro h i hi j hj
    refine ⟨h.eq_iff i hi j hj, ?_⟩
    have := h.relMap_iff adj ![i, j] (by intro t; fin_cases t <;> assumption)
    rwa [comp_vec_two, comp_vec_two] at this
  · intro h
    refine ⟨fun i hi j hj => (h i hi j hj).1, fun {l} R f hf => ?_⟩
    cases R
    have hf' : f = ![f 0, f 1] := funext fun t => by fin_cases t <;> rfl
    rw [hf', comp_vec_two, comp_vec_two]
    exact (h _ (hf 0) _ (hf 1)).2

private theorem eq_add_one_of_ne {i p : Fin 2} (h : p ≠ i) : p = i + 1 := by
  revert i p
  decide

/-- The forth step of the `2`-pebble game on loopless symmetric graphs: if every pair `(c, x)` of
`V` has a counterpart `(d, y)` in `W` with the same equality and adjacency type, Duplicator can
answer any move while keeping a partial isomorphism. -/
theorem forth_graph (hV : ∀ x : V, ¬ RelMap adj ![x, x]) (hW : ∀ y : W, ¬ RelMap adj ![y, y])
    (hVs : ∀ x y : V, RelMap adj ![x, y] → RelMap adj ![y, x])
    (hWs : ∀ x y : W, RelMap adj ![x, y] → RelMap adj ![y, x])
    (hext : ∀ (c x : V) (y : W), ∃ d : W, (c = x ↔ d = y) ∧
      (RelMap adj ![c, x] ↔ RelMap adj ![d, y]))
    {S : Set (Fin 2)} {a : Fin 2 → V} {b : Fin 2 → W} (h : PartialIsoOn Language.graph S a b)
    (i : Fin 2) (c : V) : ∃ d : W,
      PartialIsoOn Language.graph (insert i S) (Function.update a i c) (Function.update b i d) := by
  obtain ⟨d, hdeq, hdadj⟩ := hext c (a (i + 1)) (b (i + 1))
  refine ⟨d, partialIsoOn_graph_iff.2 fun p hp q hq => ?_⟩
  have hcases : ∀ p ∈ insert i S, p = i ∨ (p = i + 1 ∧ i + 1 ∈ S) := by
    intro p hp
    by_cases hpi : p = i
    · exact Or.inl hpi
    · obtain rfl := eq_add_one_of_ne hpi
      exact Or.inr ⟨rfl, (Set.mem_insert_iff.1 hp).resolve_left hpi⟩
  have hupd_a : Function.update a i c (i + 1) = a (i + 1) :=
    Function.update_of_ne (add_one_ne_self i) c a
  have hupd_b : Function.update b i d (i + 1) = b (i + 1) :=
    Function.update_of_ne (add_one_ne_self i) d b
  rcases hcases p hp with rfl | ⟨rfl, hS⟩ <;> rcases hcases q hq with rfl | ⟨rfl, -⟩
  · rw [Function.update_self, Function.update_self]
    exact ⟨iff_of_true rfl rfl, iff_of_false (hV c) (hW d)⟩
  · rw [Function.update_self, Function.update_self, hupd_a, hupd_b]
    exact ⟨hdeq, hdadj⟩
  · rw [Function.update_self, Function.update_self, hupd_a, hupd_b]
    exact ⟨eq_comm.trans (hdeq.trans eq_comm),
      ⟨fun h => hWs _ _ (hdadj.1 (hVs _ _ h)), fun h => hVs _ _ (hdadj.2 (hWs _ _ h))⟩⟩
  · rw [hupd_a, hupd_b]
    exact (partialIsoOn_graph_iff.1 h) _ hS _ hS

/-- Every pair of vertices of `C₆` has a counterpart in `2C₃` with the same equality and adjacency
type, and conversely. -/
theorem extension_fin_twoTriangles : ∀ (c x : Fin 6) (y : Bool × Fin 3), ∃ d : Bool × Fin 3,
    (c = x ↔ d = y) ∧
      ((SimpleGraph.cycleGraph 6).Adj c x ↔ twoTriangles.Adj d y) := by
  decide

theorem extension_twoTriangles_fin : ∀ (c x : Bool × Fin 3) (y : Fin 6), ∃ d : Fin 6,
    (c = x ↔ d = y) ∧
      (twoTriangles.Adj c x ↔ (SimpleGraph.cycleGraph 6).Adj d y) := by
  decide

/-- **Duplicator wins the infinite `2`-pebble game on `C₆` and `2C₃`**, from any position with no
pebbles placed: being a partial isomorphism on the placed pebbles is a back-and-forth invariant. -/
theorem pebbleWinsForever_fin_twoTriangles (a : Fin 2 → Fin 6) (b : Fin 2 → Bool × Fin 3) :
    PebbleWinsForever Language.graph ∅ a b := by
  have hV : ∀ x : Fin 6, ¬ RelMap adj ![x, x] := fun _ =>
    relMap_adj_fin.not.2 (SimpleGraph.cycleGraph 6).irrefl
  have hW : ∀ y : Bool × Fin 3, ¬ RelMap adj ![y, y] := fun _ =>
    relMap_adj_twoTriangles.not.2 twoTriangles.irrefl
  have hVs : ∀ x y : Fin 6, RelMap adj ![x, y] → RelMap adj ![y, x] :=
    fun _ _ h => relMap_adj_fin.2 (relMap_adj_fin.1 h).symm
  have hWs : ∀ x y : Bool × Fin 3, RelMap adj ![x, y] → RelMap adj ![y, x] :=
    fun _ _ h => relMap_adj_twoTriangles.2 (relMap_adj_twoTriangles.1 h).symm
  refine IsPebbleBackAndForth.pebbleWinsForever
    (I := fun S a b => PartialIsoOn Language.graph S a b)
    ⟨id, fun h i c => ?_, fun h i d => ?_⟩ (partialIsoOn_empty a b)
  · exact forth_graph hV hW hVs hWs (fun c x y => extension_fin_twoTriangles c x y) h i c
  · obtain ⟨c, hc⟩ := forth_graph hW hV hWs hVs
      (fun c x y => extension_twoTriangles_fin c x y) h.symm i d
    exact ⟨c, hc.symm⟩

/-- Hence `C₆` and `2C₃` satisfy the same two-variable sentences. -/
theorem realize_iff_of_freeVars_eq_empty {φ : FiniteVariable.Formula Language.graph 2}
    (hφ : φ.freeVars = ∅) (a : Fin 2 → Fin 6) (b : Fin 2 → Bool × Fin 3) :
    φ.Realize a ↔ φ.Realize b :=
  (pebbleWinsForever_fin_twoTriangles a b).realize_iff (by simp only [hφ, Finset.coe_empty,
    subset_refl])

/-- There is a triangle: a sentence with three variables and quantifier rank `3`. -/
def triangle : FiniteVariable.Formula Language.graph 3 :=
  .ex 0 (.ex 1 (.ex 2 (.rel adj ![0, 1] ⊓ .rel adj ![1, 2] ⊓ .rel adj ![0, 2])))

theorem quantifierRank_triangle : triangle.quantifierRank = 3 := by
  simp only [triangle, FiniteVariable.Formula.quantifierRank_ex,
    FiniteVariable.Formula.quantifierRank_inf, FiniteVariable.Formula.quantifierRank_rel,
    max_self]

theorem freeVars_triangle : triangle.freeVars = ∅ := by
  simp only [triangle, FiniteVariable.Formula.freeVars_ex, FiniteVariable.Formula.freeVars_inf,
    FiniteVariable.Formula.freeVars_rel]
  decide

theorem realize_triangle_iff (a : Fin 3 → V) :
    triangle.Realize a ↔ ∃ x y z : V,
      RelMap adj ![x, y] ∧ RelMap adj ![y, z] ∧ RelMap adj ![x, z] := by
  simp only [triangle, FiniteVariable.Formula.realize_ex, FiniteVariable.Formula.realize_inf,
    FiniteVariable.Formula.realize_rel, comp_vec_two, Function.update_self,
    Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide), and_assoc]

theorem not_realize_triangle_fin (a : Fin 3 → Fin 6) : ¬ triangle.Realize a := by
  rw [realize_triangle_iff]
  simp only [relMap_adj_fin, not_exists, not_and]
  decide

theorem realize_triangle_twoTriangles (a : Fin 3 → Bool × Fin 3) : triangle.Realize a :=
  (realize_triangle_iff a).2 ⟨(false, 0), (false, 1), (false, 2),
    relMap_adj_twoTriangles.2 (by decide), relMap_adj_twoTriangles.2 (by decide),
    relMap_adj_twoTriangles.2 (by decide)⟩

/-- **Spoiler wins the `3`-round `3`-pebble game on `C₆` and `2C₃`**, from any position with no
pebbles placed: `triangle` has three variables and rank `3`. -/
theorem not_pebbleWins_fin_twoTriangles (a : Fin 3 → Fin 6) (b : Fin 3 → Bool × Fin 3) :
    ¬ PebbleWins Language.graph 3 ∅ a b := fun h =>
  not_realize_triangle_fin a ((h.realize_iff quantifierRank_triangle.le (by
    simp only [freeVars_triangle, Finset.coe_empty, subset_refl])).2
      (realize_triangle_twoTriangles b))

/-- The hard direction in action: since Spoiler wins, the Hintikka formula of the type of `a`, a
`3`-variable sentence of quantifier rank at most `3`, holds in `C₆` and fails in `2C₃`. -/
example (a : Fin 3 → Fin 6) (b : Fin 3 → Bool × Fin 3) :
    ∃ φ : FiniteVariable.Formula Language.graph 3, φ.quantifierRank ≤ 3 ∧
      ↑φ.freeVars ⊆ (∅ : Set (Fin 3)) ∧ φ.Realize a ∧ ¬ φ.Realize b := by
  refine ⟨pebbleHintikka ∅ (pebbleType (L := Language.graph) 3 ∅ a),
    quantifierRank_pebbleHintikka_le _ _, freeVars_pebbleHintikka_subset _ _, ?_, ?_⟩
  · rw [realize_pebbleHintikka]
  · rw [realize_pebbleHintikka, eq_comm, pebbleType_eq_iff]
    exact not_pebbleWins_fin_twoTriangles a b

end Cslib.Tests.FOPebbleGames
