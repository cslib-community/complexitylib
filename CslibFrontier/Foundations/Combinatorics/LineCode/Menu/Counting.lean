/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Combinatorics.FiniteCover.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting tools for universal menus

Three finite counting principles replace probability in the construction of universal menus.

* **Collision cut** (`exists_collisionCut`). In a graph, let every vertex of a finite set `bad`
  either satisfy a property `P` or have a neighbor. Two-coloring a spanning forest gives a subset
  of at least half of `bad` whose vertices satisfy `P` or have a neighbor outside the subset.
* **Conditional counting** (`card_filter_forall_mem_le`). If the allowed values of each selected
  coordinate depend only on the unselected coordinates, then at most `M ^ #S` assignments of the
  `#S` selected coordinates are allowed for each assignment of the others.
* **Covering menus** (`exists_coveringMenu`). If for every state at most a `2 ^ (-m)` fraction of
  the candidates fail, and there are fewer than `2 ^ (m * r)` states, then some list of `r`
  candidates contains a successful candidate for every state.

## Main results

* `Cslib.LineCode.exists_collisionCut`: the collision cut.
* `Cslib.LineCode.card_filter_forall_mem_le`: conditional counting.
* `Cslib.LineCode.exists_coveringMenu`: covering menus.

## References

* Adapted from MassProduction/Nonuniform/CollisionCut.lean,
  MassProduction/Nonuniform/ConditionalCounting.lean and MassProduction/Nonuniform/Menu.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

open Finset

/-- **Collision cut.** If every vertex of `bad` satisfies `P` or has a neighbor, then some
`S ⊆ bad` with `#bad ≤ 2 * #S` has every vertex satisfying `P` or adjacent to a vertex outside
`S`. -/
theorem exists_collisionCut {V : Type*} (G : SimpleGraph V) (P : V → Prop) (bad : Finset V)
    (h : ∀ v ∈ bad, P v ∨ ∃ w, G.Adj v w) :
    ∃ S ⊆ bad, #bad ≤ 2 * #S ∧ ∀ v ∈ S, P v ∨ ∃ w ∉ S, G.Adj v w := by
  classical
  obtain ⟨F, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  let c := hF.coloringTwo
  -- A vertex with a neighbor in `G` has a neighbor in the forest, of the other color.
  have opposite : ∀ v w, G.Adj v w → ∃ w', c v ≠ c w' ∧ G.Adj v w' := by
    intro v w hvw
    have hvw' : F.Reachable v w := hreach ▸ hvw.reachable
    obtain ⟨w', hw'⟩ := (F.mem_support).mp (SimpleGraph.mem_support_of_reachable hvw.ne hvw')
    exact ⟨w', c.valid hw', hFG hw'⟩
  have witness : ∀ a, ∀ v ∈ bad.filter (c · = a),
      P v ∨ ∃ w ∉ bad.filter (c · = a), G.Adj v w := by
    intro a v hv
    obtain ⟨hv, hva⟩ := mem_filter.mp hv
    refine (h v hv).imp_right fun ⟨w, hw⟩ => ?_
    obtain ⟨w', hne, hw'⟩ := opposite v w hw
    exact ⟨w', fun hw'a => hne (hva.trans (mem_filter.mp hw'a).2.symm), hw'⟩
  have hsum : #(bad.filter (c · = 0)) + #(bad.filter (c · = 1)) = #bad := by
    rw [filter_congr fun v _ => (by decide : ∀ a : Fin 2, a = 1 ↔ ¬a = 0) (c v)]
    exact card_filter_add_card_filter_not _
  by_cases h0 : #bad ≤ 2 * #(bad.filter (c · = 0))
  · exact ⟨_, filter_subset _ _, h0, witness 0⟩
  · exact ⟨_, filter_subset _ _, by omega, witness 1⟩

/-- **Conditional counting.** Suppose the allowed values `A y i` of each coordinate `i ∈ S`
depend only on the values `y` of the coordinates outside `S`, and number at most `M`. Then at
most `Fintype.card α ^ (Fintype.card ι - #S) * M ^ #S` assignments take allowed values on all of
`S`. -/
theorem card_filter_forall_mem_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (S : Finset ι) (A : ({i // i ∉ S} → α) → ι → Finset α) (M : ℕ)
    (hA : ∀ y, ∀ i ∈ S, #(A y i) ≤ M)
    [DecidablePred fun x : ι → α => ∀ i ∈ S, x i ∈ A (fun j => x j) i] :
    #{x : ι → α | ∀ i ∈ S, x i ∈ A (fun j => x j) i} ≤
      Fintype.card α ^ (Fintype.card ι - #S) * M ^ #S := by
  classical
  set T : Finset (ι → α) := {x | ∀ i ∈ S, x i ∈ A (fun j => x j) i}
  let outside : (ι → α) → {i // i ∉ S} → α := fun x j => x j
  calc #T = ∑ y, #{x ∈ T | outside x = y} :=
        card_eq_sum_card_fiberwise fun _ _ => mem_coe.mpr (mem_univ _)
    _ ≤ ∑ _y : {i // i ∉ S} → α, M ^ #S := sum_le_sum fun y _ => ?_
    _ = Fintype.card α ^ (Fintype.card ι - #S) * M ^ #S := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_subtype_compl,
          Fintype.card_coe, smul_eq_mul]
  -- Each fiber injects into the allowed values on `S`.
  calc #{x ∈ T | outside x = y}
      ≤ #(Fintype.piFinset fun i : {i // i ∈ S} => A y i) := by
        refine card_le_card_of_injOn (fun x i => x i) (fun x hx => ?_) fun x hx x' hx' hxx' => ?_
        · obtain ⟨hxT, rfl⟩ := mem_filter.mp hx
          exact Fintype.mem_piFinset.mpr fun i => (mem_filter.mp hxT).2 i i.2
        · have hy : outside x = outside x' :=
            (mem_filter.mp hx).2.trans (mem_filter.mp hx').2.symm
          funext i
          by_cases hi : i ∈ S
          · exact congrFun hxx' ⟨i, hi⟩
          · exact congrFun hy ⟨i, hi⟩
    _ = ∏ i : {i // i ∈ S}, #(A y i) := Fintype.card_piFinset _
    _ ≤ M ^ #(univ : Finset {i // i ∈ S}) := prod_le_pow_card _ _ _ fun i _ => hA y i i.2
    _ = M ^ #S := by rw [card_univ, Fintype.card_coe]

/-- **Covering menus.** If for every state `s` at most a `2 ^ (-m)` fraction of the candidates
fail `good s`, and there are fewer than `2 ^ (m * r)` states, then some list of `r` candidates
contains, for every state, a candidate that is good for it. -/
theorem exists_coveringMenu {σ α : Type*} [Fintype σ] [Fintype α] [Nonempty α]
    (good : σ → α → Prop) [∀ s, DecidablePred (good s)] (m r : ℕ)
    (hgood : ∀ s, #{a | ¬good s a} * 2 ^ m ≤ Fintype.card α)
    (hσ : Fintype.card σ < 2 ^ (m * r)) :
    ∃ menu : Fin r → α, ∀ s, ∃ e, good s (menu e) := by
  classical
  apply Cslib.exists_cover_of_scaled_card_lt (fun a s => good s a) 1 (2 ^ m) r
  · intro s
    rw [Fintype.card_subtype, one_mul, Nat.mul_comm]
    exact hgood s
  · rwa [one_pow, mul_one, ← pow_mul]

end Cslib.LineCode
