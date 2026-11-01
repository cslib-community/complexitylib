/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
import Complexity.Foundations.Data.List.Boole
import Mathlib.Data.List.GetD

/-!
# Tables of explicit tensor networks

Tables for the vertices of an `ExplicitTensorNetwork`, and two contraction identities for
networks assembled from them.

A *bounded table* lists the values `f 0, …, f (2 ^ w - 1)` of a function on the words of length
`w`, by keeping the numbers below `2 ^ w` among the first `2 ^ B` for a bound `w ≤ B`
(`ExplicitTensorNetwork.boundedTable`), so that a network with degrees at most `B` is computed
from constant-length lists. Looking it up at a word evaluates `f` at the value of the word
(`ExplicitTensorNetwork.entry_boundedTable`). The equality table on two ports
(`ExplicitTensorNetwork.eqTable`) joins two edges into one bit: equality vertices on consecutive
pairs of edges reduce the contraction to a sum over one bit per pair
(`ExplicitTensorNetwork.contraction_append_pairs`). Mapping every table entry by a semiring
homomorphism maps the contraction (`ExplicitTensorNetwork.map_contraction`).

## Main definitions

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.boundedTable`: the table of a function on the
  words of length `w`, for a bound `w ≤ B`.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.eqTable`: the equality table on two ports.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.mapTables`: maps of the table entries.

## Main results

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.boundedTable_eq`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.length_boundedTable`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.entry_boundedTable`: bounded tables.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.contraction_append_pairs`: equality vertices on
  consecutive pairs of edges reduce the contraction to a sum over one bit per pair.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.map_contraction`: the contraction commutes with
  maps of semirings applied to the tables.
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

/-! ### Bounded tables -/

section BoundedTable

variable {R : Type*}

/-- A table of the `2 ^ w` values `f 0, …, f (2 ^ w - 1)` when `w ≤ B`, listed by keeping the
numbers below `2 ^ w` among the first `2 ^ B`. -/
@[expose] def boundedTable (B w : ℕ) (f : ℕ → R) : List R :=
  ((List.range (2 ^ B)).filter fun idx => idx < 2 ^ w).map f

/-- For `w ≤ B`, the bounded table is the table of `f` on `0, …, 2 ^ w - 1`. -/
theorem boundedTable_eq {B w : ℕ} (f : ℕ → R) (h : w ≤ B) :
    boundedTable B w f = (List.range (2 ^ w)).map f := by
  have hle : 2 ^ w ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h
  unfold boundedTable
  congr 1
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  rw [hc, List.range_add, List.filter_append, List.filter_eq_self.mpr (by simp),
    List.filter_eq_nil_iff.mpr (by simp), List.append_nil]

theorem length_boundedTable {B w : ℕ} (f : ℕ → R) (h : w ≤ B) :
    (boundedTable B w f).length = 2 ^ w := by
  simp [boundedTable_eq f h]

/-- Looking up a bounded table at a word of length at most `B` evaluates its function at the
value of the word. -/
theorem entry_boundedTable [Zero R] {B : ℕ} (f : ℕ → R) {bs : List Bool} (h : bs.length ≤ B) :
    entry (boundedTable B bs.length f) bs = f (BitString.lsbValue bs) := by
  rw [entry, boundedTable_eq f h,
    List.getD_eq_getElem _ _ (by simpa using BitString.lsbValue_lt bs)]
  simp

end BoundedTable

/-! ### Equality vertices and maps of tables -/

/-- The equality table on two ports. -/
@[expose] def eqTable {R : Type*} [Zero R] [One R] : List R := [1, 0, 0, 1]

theorem entry_eqTable {R : Type*} [Zero R] [One R] (a b : Bool) :
    entry (eqTable : List R) [a, b] = if a = b then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- **Equality vertices on pairs of edges.** If the last vertices of a network with `2 W` edges are
`W` equality vertices, vertex `w` joining the edges `2 w` and `2 w + 1`, then the contraction is the
sum over one bit `y w` per pair of the product of the other entries, where edge `e` carries
`y (e / 2)`. -/
theorem contraction_append_pairs {R : Type*} [CommSemiring R] (W : ℕ)
    (rows : List (List ℕ × List R)) :
    contraction (⟨2 * W, rows ++ (List.range W).map fun w => ([2 * w, 2 * w + 1], eqTable)⟩ :
        ExplicitTensorNetwork R) =
      ∑ y : Fin W → Bool, (rows.map fun v => entry v.2
        (v.1.map fun e => if h : e / 2 < W then y ⟨e / 2, h⟩ else false)).prod := by
  classical
  set G : ExplicitTensorNetwork R :=
    ⟨2 * W, rows ++ (List.range W).map fun w => ([2 * w, 2 * w + 1], eqTable)⟩
  -- an assignment that repeats each bit of `y` on the two edges of its pair
  let dup : (Fin W → Bool) → Fin (2 * W) → Bool := fun y e => y ⟨e / 2, by omega⟩
  have hdup : Function.Injective dup := by
    intro y y' h
    funext w
    have := congrFun h ⟨2 * w, by omega⟩
    simpa [dup, show 2 * (w : ℕ) / 2 = w by omega] using this
  have hpb (x : Fin (2 * W) → Bool) (ps : List ℕ) :
      G.portBits x ps = ps.map fun i => if h : i < 2 * W then x ⟨i, h⟩ else false := rfl
  -- the weight of an assignment
  let F : (Fin (2 * W) → Bool) → R := fun x =>
    (G.vertices.map fun v => entry v.2 (G.portBits x v.1)).prod
  have hcol (x : Fin (2 * W) → Bool) :
      (((List.range W).map fun w => (([2 * w, 2 * w + 1], eqTable) : List ℕ × List R)).map
          fun v => entry v.2 (G.portBits x v.1)).prod =
        if ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ then 1 else 0 := by
    rw [List.map_map]
    have h1 : ∀ w ∈ List.range W, ((fun v => entry v.2 (G.portBits x v.1)) ∘
        fun w => (([2 * w, 2 * w + 1], eqTable) : List ℕ × List R)) w =
          if (∀ h : w < W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩) then 1 else 0 := by
      intro w hw
      have hw' : w < W := List.mem_range.mp hw
      simp only [Function.comp_apply, hpb, List.map_cons, List.map_nil,
        show 2 * w < 2 * W by omega, show 2 * w + 1 < 2 * W by omega, dite_true, entry_eqTable]
      simp [hw']
    rw [List.map_congr_left h1]
    have key := List.prod_map_boole (M₀ := R) (List.range W)
      (fun w => ∀ h : w < W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩)
    rw [key]
    congr 1
    exact propext ⟨fun h w => h w (List.mem_range.mpr w.2) w.2,
      fun h w _ hw => h ⟨w, hw⟩⟩
  have hF (x : Fin (2 * W) → Bool) : F x =
      (rows.map fun v => entry v.2 (G.portBits x v.1)).prod *
        if ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ then 1 else 0 := by
    simp only [F, G, List.map_append, List.prod_append]
    rw [← hcol]
  -- assignments off the image of `dup` have weight zero
  have hzero (x : Fin (2 * W) → Bool) (hx : x ∉ Finset.univ.image dup) : F x = 0 := by
    rw [hF]
    have : ¬ ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ := by
      intro h
      refine hx (Finset.mem_image.mpr ⟨fun w => x ⟨2 * w, by omega⟩, Finset.mem_univ _, ?_⟩)
      funext e
      obtain ⟨e, he⟩ := e
      simp only [dup]
      rcases Nat.even_or_odd' e with ⟨w, rfl | rfl⟩
      · exact congrArg x (Fin.ext (by change 2 * (2 * w / 2) = 2 * w; omega))
      · refine (congrArg x (Fin.ext ?_)).trans (h ⟨w, by omega⟩)
        change 2 * ((2 * w + 1) / 2) = 2 * w
        omega
    rw [ite_eq_right this, mul_zero]
  change ∑ x, F x = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image dup)) fun x _ hx => hzero x hx,
    Finset.sum_image fun y _ y' _ h => hdup h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hF, ite_eq_left fun w => by simp [dup, show 2 * (w : ℕ) / 2 = w by omega,
    show (2 * (w : ℕ) + 1) / 2 = w by omega], mul_one]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  rw [hpb]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  by_cases he : e < 2 * W
  · simp [he, dup, show e / 2 < W by omega]
  · simp [he, show ¬ e / 2 < W by omega]

/-- The network with every table entry mapped by `ψ`. -/
@[expose] def mapTables {R S : Type*} (ψ : R → S) (d : ExplicitTensorNetwork R) :
    ExplicitTensorNetwork S :=
  ⟨d.numEdges, d.vertices.map fun v => (v.1, v.2.map ψ)⟩

/-- **The contraction commutes with maps of semirings** applied to the tables. -/
theorem map_contraction {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : R →+* S)
    (d : ExplicitTensorNetwork R) : ψ d.contraction = (d.mapTables ψ).contraction := by
  rw [contraction, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_list_prod, List.map_map]
  simp only [mapTables, List.map_map]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, entry]
  rw [← map_zero ψ, List.getD_map]
  rfl

end Cslib.Circuits.Frontier.ExplicitTensorNetwork

