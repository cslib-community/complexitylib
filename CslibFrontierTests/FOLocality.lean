/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Locality.Hanf

/-! # Hanf and Gaifman locality: checked instances

* Balls in the Gaifman graph of a simple graph are balls of the graph.
* **Nonvacuity.** The 8-cycle and two disjoint 4-cycles are Hanf-equivalent at radius `1`: every
  vertex of the 8-cycle has the same radius-`1` neighborhood (a path on three vertices) as its
  image. So Hanf locality shows that they satisfy the same sentences of quantifier rank at most
  `1`, although they are not isomorphic (only the second contains a 4-cycle).
* **The nonempty hypothesis is needed.** Two empty structures that disagree on a nullary relation
  are Hanf-equivalent at every radius, but Duplicator loses even the `0`-round game. -/

@[expose] public section

namespace Cslib.Tests.FOLocality

open FirstOrder Language Structure
open Cslib.Logic.FO Cslib.Logic.FO.Locality

/-! ### Balls of a simple graph -/

/-- In the Gaifman graph of a simple graph, the ball of radius `r` around `c` is the graph ball. -/
example {V : Type*} (G : SimpleGraph V) (c x : V) (r : ℕ) :
    (letI := G.structure; x ∈ ball Language.graph (fun _ : Fin 1 => c) r) ↔ G.edist c x ≤ r := by
  let := G.structure
  rw [mem_ball_const, gaifmanGraph_structure]

/-! ### The 8-cycle and two disjoint 4-cycles -/

/-- The 8-cycle on `Fin 8`. -/
def cycle8 : SimpleGraph (Fin 8) where
  Adj x y := (x.val + 1) % 8 = y.val ∨ (y.val + 1) % 8 = x.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by rcases h with h | h <;> omega⟩

instance : DecidableRel cycle8.Adj := fun x y =>
  inferInstanceAs (Decidable ((x.val + 1) % 8 = y.val ∨ (y.val + 1) % 8 = x.val))

/-- Two disjoint 4-cycles on `Bool × Fin 4`. -/
def twoCycle4 : SimpleGraph (Bool × Fin 4) where
  Adj x y := x.1 = y.1 ∧ ((x.2.val + 1) % 4 = y.2.val ∨ (y.2.val + 1) % 4 = x.2.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => by rcases h.2 with h | h <;> omega⟩

instance : DecidableRel twoCycle4.Adj := fun x y =>
  inferInstanceAs (Decidable (x.1 = y.1 ∧
    ((x.2.val + 1) % 4 = y.2.val ∨ (y.2.val + 1) % 4 = x.2.val)))

section Cycles

/-- `cycle8` as a structure of the language of graphs. -/
local instance : Language.graph.Structure (Fin 8) := cycle8.structure

/-- `twoCycle4` as a structure of the language of graphs. -/
local instance : Language.graph.Structure (Bool × Fin 4) := twoCycle4.structure

theorem mem_ball_one_cycle8 {c x : Fin 8} :
    x ∈ ball Language.graph (fun _ : Fin 1 => c) 1 ↔ cycle8.Adj c x ∨ c = x := by
  rw [mem_ball_const, Nat.cast_one, ← SimpleGraph.edist_le_one_iff_adj_or_eq]
  exact Iff.of_eq (congrArg (· ≤ 1) (congrArg (fun G : SimpleGraph (Fin 8) => G.edist c x)
    (gaifmanGraph_structure cycle8)))

theorem mem_ball_one_twoCycle4 {c x : Bool × Fin 4} :
    x ∈ ball Language.graph (fun _ : Fin 1 => c) 1 ↔ twoCycle4.Adj c x ∨ c = x := by
  rw [mem_ball_const, Nat.cast_one, ← SimpleGraph.edist_le_one_iff_adj_or_eq]
  exact Iff.of_eq (congrArg (· ≤ 1)
    (congrArg (fun G : SimpleGraph (Bool × Fin 4) => G.edist c x)
      (gaifmanGraph_structure twoCycle4)))

/-- Vertex `v` of the 8-cycle goes to vertex `v mod 4` of the first 4-cycle if `v < 4`, of the
second otherwise. -/
def e8 : Fin 8 ≃ Bool × Fin 4 where
  toFun v := (decide (4 ≤ v.val), ⟨v.val % 4, by omega⟩)
  invFun p := ⟨p.2.val + if p.1 then 4 else 0, by split <;> omega⟩
  left_inv := by decide
  right_inv := by decide

/-- The local isomorphism at `c`: reduce modulo `4`, in the copy of `c`. -/
def hAt (c : Fin 8) (x : Fin 8) : Bool × Fin 4 := (decide (4 ≤ c.val), ⟨x.val % 4, by omega⟩)

/-- Every vertex of the 8-cycle has the same radius-`1` neighborhood as its image. -/
theorem nbhdIso_cycle8 (c : Fin 8) :
    NbhdIso Language.graph 1 (fun _ : Fin 1 => c) (fun _ : Fin 1 => e8 c) := by
  refine (IsNbhdIso.nbhdIso (h := hAt c) ⟨⟨?_, ?_, ?_⟩, fun _ => ?_, ?_⟩)
  · intro x hx
    rw [mem_ball_one_cycle8] at hx
    rw [mem_ball_one_twoCycle4]
    revert c x
    decide
  · intro x hx y hy hxy
    rw [mem_ball_one_cycle8] at hx hy
    revert c x y
    decide
  · intro y hy
    rw [mem_ball_one_twoCycle4] at hy
    simp only [Set.mem_image, mem_ball_one_cycle8]
    revert c y
    decide
  · revert c
    decide
  · intro l R t ht
    cases R
    simp only [mem_ball_one_cycle8] at ht
    change twoCycle4.Adj (hAt c (t 0)) (hAt c (t 1)) ↔ cycle8.Adj (t 0) (t 1)
    have key : ∀ c x y : Fin 8, (cycle8.Adj c x ∨ c = x) → (cycle8.Adj c y ∨ c = y) →
        (twoCycle4.Adj (hAt c x) (hAt c y) ↔ cycle8.Adj x y) := by decide
    exact key c (t 0) (t 1) (ht 0) (ht 1)

/-- **Hanf locality applied**: the 8-cycle and two disjoint 4-cycles satisfy the same sentences of
quantifier rank at most `1`. -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 1) :
    Fin 8 ⊨ φ ↔ (Bool × Fin 4) ⊨ φ :=
  realize_sentence_iff_of_nbhdIso (n := 1) e8 nbhdIso_cycle8 hφ

/-- The two graphs are not isomorphic: two disjoint 4-cycles contain a 4-cycle, and the 8-cycle
does not. -/
example : IsEmpty (cycle8 ≃g twoCycle4) := by
  refine ⟨fun f => ?_⟩
  have h8 : ∀ x y : Fin 8, cycle8.Adj x y → ∀ z, cycle8.Adj y z → ∀ w, cycle8.Adj z w →
      cycle8.Adj w x → x ≠ z → y = w := by decide
  have := h8 _ _ (f.symm.map_adj_iff.2 (by decide : twoCycle4.Adj (false, 0) (false, 1))) _
    (f.symm.map_adj_iff.2 (by decide : twoCycle4.Adj (false, 1) (false, 2))) _
    (f.symm.map_adj_iff.2 (by decide : twoCycle4.Adj (false, 2) (false, 3)))
    (f.symm.map_adj_iff.2 (by decide : twoCycle4.Adj (false, 3) (false, 0)))
    (fun h => absurd (f.symm.injective h) (by decide))
  exact absurd (f.symm.injective this) (by decide)

end Cycles

/-! ### The nonempty hypothesis -/

/-- A language with a single nullary relation symbol. -/
def nullaryLang : Language := ⟨fun _ => Empty, fun | 0 => Unit | _ + 1 => Empty⟩

/-- On `Empty` the nullary relation holds. -/
local instance : nullaryLang.Structure Empty where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun _ _ => True

/-- On `PEmpty` the nullary relation fails. -/
local instance : nullaryLang.Structure PEmpty.{1} where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun _ _ => False

/-- The relation symbol. -/
def nullaryRel : nullaryLang.Relations 0 := ()

/-- Two empty structures are Hanf-equivalent at every radius. -/
example (d : ℕ) :
    HanfEquiv nullaryLang d (default : Fin 0 → Empty) (default : Fin 0 → PEmpty) :=
  hanfEquiv_iff.2 ⟨Equiv.equivPEmpty Empty, fun c => c.elim⟩

/-- They differ on the nullary relation, so Duplicator loses the `0`-round game. -/
example :
    ¬ DuplicatorWins nullaryLang 0 (default : Fin 0 → Empty) (default : Fin 0 → PEmpty) := by
  intro h
  have := (duplicatorWins_zero.1 h).relMap_iff nullaryRel Fin.elim0
  exact this.1 trivial

end Cslib.Tests.FOLocality
