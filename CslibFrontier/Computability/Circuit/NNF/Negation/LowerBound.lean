/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.NNF.Rectangle
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CubicEdgeColoring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Balanced rectangles inside the zeros of `f_G` are small

Let `M` be a cubic graph with a proper `3`-edge-colouring and `f_G = M.someButNotAllColors` the
function that is true when the subgraph induced by `x` contains an edge but at most two colours
[ArenasBroadrickLiewVanDenBroeck2026, Section 5]. Its zeros contain the independent sets `I`.

**Rectangle size** (`CubicEdgeColoring.card_filter_mem_le`). Let `R ⊆ f_G⁻¹(0)` be a rectangle for
the cut `(A, Aᶜ)`, and let `S` be the ends in `A` of `k` crossing edges `eᵤ = {u, mate c u}` of a
single colour `c` with pairwise disjoint neighbourhoods `N(eᵤ)`
(`CubicEdgeColoring.IsSeparatedCrossing`). Then `|R ∩ I| ≤ (47/48)^k |I|`. This combines Lemmas
5.5 and 5.6 of the paper into one counting argument, without probabilities:

* **The claim of Lemma 5.5.** For each `u` there is an end `w` of `eᵤ`, depending only on the
  values of `x` off the ends of the chosen edges, that is false in every independent `x ∈ R` with
  those values: otherwise combining the `A`-part of one member of `R` with the rest of another
  gives a member of `R` whose induced subgraph contains `eᵤ` and edges of colour `c` only, where
  `f_G` is true.
* **Free edges.** Call `eᵤ` free in `x` when the other neighbours of its ends are false. Fix `x`
  off the two ends of `eᵤ`; if `eᵤ` is free, exactly three independent sets remain, of which the
  one with `w` true is excluded. Edge by edge this gives `|R ∩ I| ≤ ∑_{x ∈ I} (2/3)^{free(x)}`.
* **Most edges are free.** Fix `x` off the at most four other neighbours of the ends of `eᵤ`:
  at most `16` independent sets remain, among them the one making `eᵤ` free. Edge by edge,
  `∑_{x ∈ I} (3/2)^{k - free(x)} ≤ (47/32)^k |I|`, a moment bound replacing the Chernoff bound.

Both steps average over the fibres of a map clearing a few coordinates
(`sum_mul_le_of_fiber`).

## Main definitions

* `Cslib.CubicEdgeColoring.otherNbrs`, `Cslib.CubicEdgeColoring.edgeNbhd`: the other neighbours
  of the ends of an edge and its neighbourhood `N(e)`.
* `Cslib.CubicEdgeColoring.IsSeparatedCrossing`: crossing edges of one colour with pairwise
  disjoint neighbourhoods.

## Main results

* `Cslib.CubicEdgeColoring.mem_edgeNbhd_iff`: `N(e)` consists of the ends and their neighbours.
* `Cslib.CubicEdgeColoring.card_filter_mem_le`: the rectangle size bound.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib.CubicEdgeColoring

open Finset

/-- **Averaging over fibres.** If `g` is constant on the fibres of `φ` and nonnegative, and on
each fibre the sum of `a` is at most `k` times its size, then `∑ a g ≤ ∑ k(φ) g`. -/
private theorem sum_mul_le_of_fiber {α β : Type*} [DecidableEq β] (s : Finset α) (φ : α → β)
    (a g : α → ℝ) (k : β → ℝ)
    (hg : ∀ x ∈ s, ∀ y ∈ s, φ x = φ y → g x = g y) (hg0 : ∀ x ∈ s, 0 ≤ g x)
    (ha : ∀ x ∈ s, ∑ y ∈ s with φ y = φ x, a y ≤ k (φ x) * (#{y ∈ s | φ y = φ x} : ℝ)) :
    ∑ x ∈ s, a x * g x ≤ ∑ x ∈ s, k (φ x) * g x := by
  have hmaps : ∀ x ∈ s, φ x ∈ s.image φ := fun x hx => mem_image_of_mem φ hx
  rw [← sum_fiberwise_of_maps_to hmaps, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
  have hgc : ∀ y ∈ s.filter (φ · = φ x), g y = g x := fun y hy =>
    hg y (mem_filter.mp hy).1 x hx (mem_filter.mp hy).2
  calc ∑ y ∈ s with φ y = φ x, a y * g y
      = (∑ y ∈ s with φ y = φ x, a y) * g x := by
        rw [sum_mul]; exact sum_congr rfl fun y hy => by rw [hgc y hy]
    _ ≤ (k (φ x) * (#{y ∈ s | φ y = φ x} : ℝ)) * g x :=
        mul_le_mul_of_nonneg_right (ha x hx) (hg0 x hx)
    _ = ∑ y ∈ s with φ y = φ x, k (φ y) * g y := by
        rw [sum_congr rfl fun y hy => by rw [hgc y hy, (mem_filter.mp hy).2], sum_const,
          nsmul_eq_mul]
        ring

variable {V : Type*} [DecidableEq V] (M : CubicEdgeColoring V)

/-- The neighbours of the ends of the edge of colour `c` at `u`, other than these ends. -/
def otherNbrs (c : Fin 3) (u : V) : Finset V :=
  ((univ.erase c).image fun c' => M.mate c' u) ∪
    ((univ.erase c).image fun c' => M.mate c' (M.mate c u))

/-- The *neighbourhood* `N(e)` of the edge `e` of colour `c` at `u`: its two ends and all their
neighbours. -/
def edgeNbhd (c : Fin 3) (u : V) : Finset V :=
  insert u (insert (M.mate c u) (M.otherNbrs c u))

variable {M}

theorem mate_mem_otherNbrs {c c' : Fin 3} (h : c' ≠ c) (u : V) :
    M.mate c' u ∈ M.otherNbrs c u :=
  mem_union_left _ (mem_image.mpr ⟨c', mem_erase.mpr ⟨h, mem_univ _⟩, rfl⟩)

theorem mate_mate_mem_otherNbrs {c c' : Fin 3} (h : c' ≠ c) (u : V) :
    M.mate c' (M.mate c u) ∈ M.otherNbrs c u :=
  mem_union_right _ (mem_image.mpr ⟨c', mem_erase.mpr ⟨h, mem_univ _⟩, rfl⟩)

theorem card_otherNbrs_le (c : Fin 3) (u : V) : (M.otherNbrs c u).card ≤ 4 := by
  have h : ((univ : Finset (Fin 3)).erase c).card = 2 := by simp
  refine (card_union_le _ _).trans ?_
  have h1 := card_image_le (s := (univ : Finset (Fin 3)).erase c) (f := fun c' => M.mate c' u)
  have h2 := card_image_le (s := (univ : Finset (Fin 3)).erase c)
    (f := fun c' => M.mate c' (M.mate c u))
  omega

theorem self_notMem_otherNbrs (c : Fin 3) (u : V) : u ∉ M.otherNbrs c u := by
  simp only [otherNbrs, mem_union, mem_image, mem_erase, mem_univ, and_true, not_or, not_exists,
    not_and]
  exact ⟨fun c' _ h => M.mate_ne c' u h,
    fun c' hc' h => hc' (M.color_unique (M.mate_eq_iff.mp h) rfl)⟩

theorem mate_notMem_otherNbrs (c : Fin 3) (u : V) : M.mate c u ∉ M.otherNbrs c u := by
  simp only [otherNbrs, mem_union, mem_image, mem_erase, mem_univ, and_true, not_or, not_exists,
    not_and]
  exact ⟨fun c' hc' h => hc' (M.color_unique h rfl), fun c' _ h => M.mate_ne c' _ h⟩

theorem otherNbrs_subset_edgeNbhd (c : Fin 3) (u : V) : M.otherNbrs c u ⊆ M.edgeNbhd c u :=
  fun _ ht => mem_insert_of_mem (mem_insert_of_mem ht)

theorem self_mem_edgeNbhd (c : Fin 3) (u : V) : u ∈ M.edgeNbhd c u := mem_insert_self _ _

theorem mate_mem_edgeNbhd (c : Fin 3) (u : V) : M.mate c u ∈ M.edgeNbhd c u :=
  mem_insert_of_mem (mem_insert_self _ _)

/-- `N(e)` consists of the ends of `e` and their neighbours. -/
theorem mem_edgeNbhd_iff {c : Fin 3} {u t : V} :
    t ∈ M.edgeNbhd c u ↔ t = u ∨ t = M.mate c u ∨ M.toSimpleGraph.Adj u t ∨
      M.toSimpleGraph.Adj (M.mate c u) t := by
  simp only [edgeNbhd, mem_insert, toSimpleGraph_adj]
  constructor
  · rintro (h | h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · simp only [otherNbrs, mem_union, mem_image, mem_erase, mem_univ, and_true] at h
      rcases h with ⟨c', -, h⟩ | ⟨c', -, h⟩
      exacts [.inr (.inr (.inl ⟨c', h⟩)), .inr (.inr (.inr ⟨c', h⟩))]
  · rintro (h | h | ⟨c', rfl⟩ | ⟨c', rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · by_cases hc : c' = c
      · exact .inr (.inl (hc ▸ rfl))
      · exact .inr (.inr (mate_mem_otherNbrs hc u))
    · by_cases hc : c' = c
      · subst hc; exact .inl (M.mate_mate c' u)
      · exact .inr (.inr (mate_mate_mem_otherNbrs hc u))

variable (M) in
/-- `S` lists the ends in `A` of edges of colour `c` crossing from `A` to its complement, with
pairwise disjoint neighbourhoods. -/
structure IsSeparatedCrossing (A : Finset V) (c : Fin 3) (S : Finset V) : Prop where
  /-- The listed ends lie in `A`. -/
  mem : ∀ u ∈ S, u ∈ A
  /-- The other ends lie outside `A`. -/
  mate_notMem : ∀ u ∈ S, M.mate c u ∉ A
  /-- The neighbourhoods are pairwise disjoint. -/
  disjoint : ∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → Disjoint (M.edgeNbhd c u) (M.edgeNbhd c u')

/-! ### Clearing coordinates -/

/-- `x` with the coordinates in `T` set to false. -/
def clearOn (T : Finset V) (x : V → Bool) : V → Bool :=
  fun t => if t ∈ T then false else x t

theorem clearOn_eq_of_notMem {T : Finset V} {x : V → Bool} {t : V} (ht : t ∉ T) :
    clearOn T x t = x t := ite_eq_right ht

theorem clearOn_eq_of_mem {T : Finset V} {x : V → Bool} {t : V} (ht : t ∈ T) :
    clearOn T x t = false := ite_eq_left ht

theorem clearOn_clearOn (T : Finset V) (x : V → Bool) : clearOn T (clearOn T x) = clearOn T x := by
  funext t; unfold clearOn; split_ifs <;> rfl

theorem eq_of_clearOn_eq {T : Finset V} {x y : V → Bool} (h : clearOn T x = clearOn T y) {t : V}
    (ht : t ∉ T) : x t = y t := by
  rw [← clearOn_eq_of_notMem (x := x) ht, ← clearOn_eq_of_notMem (x := y) ht, h]

theorem le_of_clearOn (T : Finset V) (x : V → Bool) (t : V) :
    clearOn T x t = true → x t = true := by
  unfold clearOn; split_ifs <;> simp

theorem IsIndep.clearOn {x : V → Bool} (hx : M.IsIndep x) (T : Finset V) :
    M.IsIndep (clearOn T x) := fun c v ⟨h1, h2⟩ =>
  hx c v ⟨le_of_clearOn T x v h1, le_of_clearOn T x _ h2⟩

section Fiber

variable [Fintype V]

/-- A fibre of clearing `T` has at most `2 ^ |T|` elements. -/
theorem card_filter_clearOn_le (s : Finset (V → Bool)) (T : Finset V) (b : V → Bool) :
    #{y ∈ s | clearOn T y = b} ≤ 2 ^ #T := by
  calc #{y ∈ s | clearOn T y = b}
      ≤ (univ : Finset (↥T → Bool)).card := by
        refine card_le_card_of_injOn (fun y t => y t) (fun _ _ => mem_univ _) ?_
        intro y hy y' hy' h
        funext t
        by_cases ht : t ∈ T
        · exact congrFun h ⟨t, ht⟩
        · exact eq_of_clearOn_eq ((mem_filter.mp hy).2.trans (mem_filter.mp hy').2.symm) ht
    _ = 2 ^ #T := by simp

end Fiber

/-! ### The rectangle size bound -/

variable (M) in
/-- The ends of the listed edges. -/
def ends (c : Fin 3) (S : Finset V) : Finset V :=
  S.biUnion fun u => {u, M.mate c u}

theorem mem_ends {c : Fin 3} {S : Finset V} {t : V} :
    t ∈ M.ends c S ↔ ∃ u ∈ S, t = u ∨ t = M.mate c u := by
  simp [ends]

variable (M) in
/-- The edge of colour `c` at `u` is *free* in `x` when the other neighbours of its ends are
false. -/
def IsFree (c : Fin 3) (u : V) (x : V → Bool) : Prop :=
  ∀ t ∈ M.otherNbrs c u, x t = false

instance (c : Fin 3) (u : V) (x : V → Bool) : Decidable (M.IsFree c u x) :=
  inferInstanceAs (Decidable (∀ t ∈ M.otherNbrs c u, x t = false))

namespace IsSeparatedCrossing

variable {A : Finset V} {c : Fin 3} {S : Finset V} (hS : M.IsSeparatedCrossing A c S)
include hS

theorem notMem_edgeNbhd {u u' : V} (hu : u ∈ S) (hu' : u' ∈ S) (hne : u ≠ u') {t : V}
    (ht : t ∈ M.edgeNbhd c u) : t ∉ M.edgeNbhd c u' :=
  Finset.disjoint_left.mp (hS.disjoint u hu u' hu' hne) ht

/-- The other neighbours of a listed edge are not ends of listed edges. -/
theorem otherNbrs_notMem_ends {u t : V} (hu : u ∈ S) (ht : t ∈ M.otherNbrs c u) :
    t ∉ M.ends c S := by
  rw [mem_ends]
  rintro ⟨u', hu', htu⟩
  by_cases h : u = u'
  · rw [← h] at htu
    rcases htu with htu | htu <;> rw [htu] at ht
    exacts [self_notMem_otherNbrs c u ht, mate_notMem_otherNbrs c u ht]
  · have hn := hS.notMem_edgeNbhd hu hu' h (otherNbrs_subset_edgeNbhd c u ht)
    rcases htu with htu | htu <;> rw [htu] at hn
    exacts [hn (self_mem_edgeNbhd c u'), hn (mate_mem_edgeNbhd c u')]

/-- An edge of another colour at an end of a listed edge leads off the ends. -/
theorem mate_notMem_ends {a : V} (ha : a ∈ M.ends c S) {c' : Fin 3} (hc' : c' ≠ c) :
    M.mate c' a ∉ M.ends c S := by
  obtain ⟨u, hu, hau | hau⟩ := mem_ends.mp ha <;> rw [hau]
  · exact hS.otherNbrs_notMem_ends hu (mate_mem_otherNbrs hc' u)
  · exact hS.otherNbrs_notMem_ends hu (mate_mate_mem_otherNbrs hc' u)

/-- The ends of another listed edge lie outside the neighbourhood of a listed edge. -/
theorem end_notMem_edgeNbhd {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hne : v ≠ u) {t : V}
    (ht : t = v ∨ t = M.mate c v) : t ∉ M.edgeNbhd c u := by
  rcases ht with rfl | rfl
  exacts [hS.notMem_edgeNbhd hv hu hne (self_mem_edgeNbhd c _),
    hS.notMem_edgeNbhd hv hu hne (mate_mem_edgeNbhd c _)]

/-- The other neighbours of distinct listed edges are disjoint. -/
theorem otherNbrs_disjoint {u u' : V} (hu : u ∈ S) (hu' : u' ∈ S) (hne : u ≠ u') :
    Disjoint (M.otherNbrs c u) (M.otherNbrs c u') :=
  (hS.disjoint u hu u' hu' hne).mono (otherNbrs_subset_edgeNbhd c u)
    (otherNbrs_subset_edgeNbhd c u')

end IsSeparatedCrossing

section Bound

variable [Fintype V] {A : Finset V} {c : Fin 3} {S : Finset V} {R : Set (V → Bool)}

variable (M c S R) in
open Classical in
/-- The end of the edge at `u` that is false in every independent member of `R` agreeing with `x`
off the ends of the listed edges. -/
noncomputable def witness (u : V) (x : V → Bool) : V :=
  if ∃ y ∈ R, M.IsIndep y ∧ (∀ t ∉ M.ends c S, y t = x t) ∧ y u = true then M.mate c u else u

theorem witness_congr {u : V} {x x' : V → Bool} (h : ∀ t ∉ M.ends c S, x t = x' t) :
    M.witness c S R u x = M.witness c S R u x' := by
  have hiff : (∃ y ∈ R, M.IsIndep y ∧ (∀ t ∉ M.ends c S, y t = x t) ∧ y u = true) ↔
      (∃ y ∈ R, M.IsIndep y ∧ (∀ t ∉ M.ends c S, y t = x' t) ∧ y u = true) :=
    exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => and_congr_left
      fun _ => forall₂_congr fun t ht => by rw [h t ht]
  unfold witness
  by_cases h1 : ∃ y ∈ R, M.IsIndep y ∧ (∀ t ∉ M.ends c S, y t = x t) ∧ y u = true
  · rw [ite_eq_left h1, ite_eq_left (hiff.mp h1)]
  · rw [ite_eq_right h1, ite_eq_right (mt hiff.mpr h1)]

theorem witness_eq (u : V) (x : V → Bool) :
    M.witness c S R u x = u ∨ M.witness c S R u x = M.mate c u := by
  unfold witness; split_ifs <;> simp

/-- **The claim of Lemma 5.5.** In an independent member of a rectangle inside the zeros of
`f_G`, the witness end of every listed edge is false. -/
theorem witness_eq_false (hS : M.IsSeparatedCrossing A c S)
    (hR : ∀ x ∈ R, ∀ y ∈ R, A.piecewise x y ∈ R)
    (hR0 : ∀ x ∈ R, M.someButNotAllColors x = false) {x : V → Bool} (hxR : x ∈ R)
    (hx : M.IsIndep x) {u : V} (hu : u ∈ S) : x (M.witness c S R u x) = false := by
  unfold witness
  split_ifs with h
  · obtain ⟨y, hyR, hy, hyx, hyu⟩ := h
    by_contra hxv
    rw [Bool.not_eq_false] at hxv
    have hz : ∀ t, A.piecewise y x t = true → x t = true ∨ y t = true := fun t ht => by
      by_cases htA : t ∈ A
      · rw [Finset.piecewise_eq_of_mem _ _ _ htA] at ht; exact .inr ht
      · rw [Finset.piecewise_eq_of_notMem _ _ _ htA] at ht; exact .inl ht
    -- `z` contains the edge at `u`, of colour `c` ...
    have hzc : M.HasColor (A.piecewise y x) c := ⟨u, by
      rw [Finset.piecewise_eq_of_mem _ _ _ (hS.mem u hu)]; exact hyu, by
      rw [Finset.piecewise_eq_of_notMem _ _ _ (hS.mate_notMem u hu)]; exact hxv⟩
    -- ... and no edge of another colour.
    have hzc' : ∀ c', c' ≠ c → ¬M.HasColor (A.piecewise y x) c' := by
      rintro c' hc' ⟨a, ha, hb⟩
      have hboth : ∀ t ∉ M.ends c S, A.piecewise y x t = true → x t = true ∧ y t = true :=
          fun t ht hzt => by
        rcases hz t hzt with h | h
        · exact ⟨h, (hyx t ht).trans h⟩
        · exact ⟨(hyx t ht).symm.trans h, h⟩
      by_cases haE : a ∈ M.ends c S
      · obtain ⟨hxb, hyb⟩ := hboth _ (hS.mate_notMem_ends haE hc') hb
        rcases hz a ha with h | h
        exacts [hx c' a ⟨h, hxb⟩, hy c' a ⟨h, hyb⟩]
      · obtain ⟨hxa, hya⟩ := hboth a haE ha
        rcases hz _ hb with h | h
        exacts [hx c' a ⟨hxa, h⟩, hy c' a ⟨hya, h⟩]
    have hf := hR0 _ (hR y hyR x hxR)
    simp only [someButNotAllColors, decide_eq_false_iff_not, not_and, not_exists, not_not] at hf
    exact hzc' (c + 1) (by omega) (hf ⟨c, hzc⟩ (c + 1))
  · cases hxu : x u
    · rfl
    · exact absurd ⟨x, hxR, hx, fun _ _ => rfl, hxu⟩ h

/-- **Most edges are free.** Clearing the other neighbours of one edge at a time,
`∑_{x ∈ I} (3/2)^{#non-free edges of J} ≤ (47/32)^{|J|} |I|`. -/
theorem sum_pow_card_filter_not_isFree_le (hS : M.IsSeparatedCrossing A c S) :
    ∀ J ⊆ S, ∑ x ∈ univ.filter M.IsIndep, (3 / 2 : ℝ) ^ #(J.filter fun u => ¬M.IsFree c u x) ≤
      (47 / 32 : ℝ) ^ #J * #(univ.filter M.IsIndep) := by
  intro J
  induction J using Finset.induction_on with
  | empty => intro _; simp
  | insert u J hu ih =>
    intro hJ
    have huS := hJ (mem_insert_self u J)
    have hJS := (subset_insert u J).trans hJ
    set I : Finset (V → Bool) := univ.filter M.IsIndep with hI
    set T := M.otherNbrs c u
    let a : (V → Bool) → ℝ := fun x => if M.IsFree c u x then 1 else 3 / 2
    let g : (V → Bool) → ℝ := fun x => (3 / 2 : ℝ) ^ #(J.filter fun u => ¬M.IsFree c u x)
    have hsplit : ∀ x, (3 / 2 : ℝ) ^ #((insert u J).filter fun u => ¬M.IsFree c u x) =
        a x * g x := fun x => by
      by_cases hf : M.IsFree c u x
      · simp only [a, g, filter_insert, hf, not_true_eq_false, ite_false, ite_true, one_mul]
      · simp only [a, g, filter_insert, hf, not_false_eq_true, ite_true, ite_false]
        rw [card_insert_of_notMem fun h => hu (mem_filter.mp h).1, pow_succ, mul_comm]
    calc ∑ x ∈ I, (3 / 2 : ℝ) ^ #((insert u J).filter fun u => ¬M.IsFree c u x)
        = ∑ x ∈ I, a x * g x := sum_congr rfl fun x _ => hsplit x
      _ ≤ ∑ x ∈ I, (fun _ => (47 / 32 : ℝ)) (clearOn T x) * g x := by
        refine sum_mul_le_of_fiber I (clearOn T) a g (fun _ => (47 / 32 : ℝ)) ?_
          (fun _ _ => by positivity) ?_
        · -- Freeness of the other edges ignores the cleared coordinates.
          intro x _ y _ hxy
          simp only [g]
          congr 2
          refine filter_congr fun u' hu' => not_congr (forall₂_congr fun t ht => ?_)
          have hne : u ≠ u' := fun h => hu (h ▸ hu')
          rw [eq_of_clearOn_eq hxy (Finset.disjoint_right.mp
            (hS.otherNbrs_disjoint huS (hJS hu') hne) ht)]
        · -- A fibre has at most `16` elements, one of which makes the edge free.
          intro x hx
          set b := clearOn T x
          have hbF : b ∈ I.filter fun y => clearOn T y = b :=
            mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.clearOn T⟩,
              clearOn_clearOn T x⟩
          have hab : a b = 1 := ite_eq_left fun t ht => clearOn_eq_of_mem ht
          have hcard : #(I.filter fun y => clearOn T y = b) ≤ 16 :=
            (card_filter_clearOn_le I T b).trans
              ((Nat.pow_le_pow_right (by norm_num) (card_otherNbrs_le c u)).trans (by norm_num))
          have hle : ∀ y, a y ≤ 3 / 2 := fun y => by simp only [a]; split_ifs <;> norm_num
          rw [← add_sum_erase _ _ hbF, hab]
          have h1 := card_erase_add_one hbF
          have hsum : ∑ y ∈ (I.filter fun y => clearOn T y = b).erase b, a y ≤
              #((I.filter fun y => clearOn T y = b).erase b) * (3 / 2 : ℝ) := by
            rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun y _ => hle y
          have hc : (#((I.filter fun y => clearOn T y = b).erase b) : ℝ) + 1 =
              #(I.filter fun y => clearOn T y = b) := by exact_mod_cast h1
          have hc16 : (#(I.filter fun y => clearOn T y = b) : ℝ) ≤ 16 := by exact_mod_cast hcard
          nlinarith
      _ = 47 / 32 * ∑ x ∈ I, g x := by rw [mul_sum]
      _ ≤ 47 / 32 * ((47 / 32 : ℝ) ^ #J * #I) := by gcongr; exact ih hJS
      _ = (47 / 32 : ℝ) ^ #(insert u J) * #I := by rw [card_insert_of_notMem hu, pow_succ]; ring

/-- **Free edges cut the rectangle.** Clearing the ends of one edge at a time,
`∑_{x ∈ I} [the witnesses of J are false in x] h(x) ≤ ∑_{x ∈ I} (2/3)^{#free edges of J} h(x)`
for every nonnegative `h` depending only on the coordinates off the ends. -/
theorem sum_witness_le (hS : M.IsSeparatedCrossing A c S) :
    ∀ J ⊆ S, ∀ h : (V → Bool) → ℝ, (∀ x, 0 ≤ h x) →
      (∀ x y, (∀ t ∉ M.ends c S, x t = y t) → h x = h y) →
      ∑ x ∈ univ.filter M.IsIndep,
          (if ∀ u ∈ J, x (M.witness c S R u x) = false then (1 : ℝ) else 0) * h x ≤
        ∑ x ∈ univ.filter M.IsIndep, (2 / 3 : ℝ) ^ #(J.filter fun u => M.IsFree c u x) * h x := by
  intro J
  induction J using Finset.induction_on with
  | empty => intro _ h _ _; simp
  | insert u J hu ih =>
    intro hJ h h0 hh
    have huS := hJ (mem_insert_self u J)
    have hJS := (subset_insert u J).trans hJ
    set I : Finset (V → Bool) := univ.filter M.IsIndep with hI
    set T : Finset V := {u, M.mate c u}
    have hT : ∀ t ∈ T, t ∈ M.ends c S := fun t ht => mem_ends.mpr ⟨u, huS, by simpa [T] using ht⟩
    have hoff : ∀ x : V → Bool, ∀ t ∉ M.ends c S, clearOn T x t = x t :=
      fun x t ht => clearOn_eq_of_notMem fun h => ht (hT t h)
    have hfreeT : ∀ x : V → Bool, M.IsFree c u (clearOn T x) ↔ M.IsFree c u x :=
      fun x => forall₂_congr fun t ht => by
        rw [clearOn_eq_of_notMem]
        simp only [T, mem_insert, mem_singleton, not_or]
        exact ⟨fun h => self_notMem_otherNbrs c u (h ▸ ht),
          fun h => mate_notMem_otherNbrs c u (h ▸ ht)⟩
    let P : (V → Bool) → Prop := fun x => ∀ v ∈ J, x (M.witness c S R v x) = false
    let a : (V → Bool) → ℝ := fun x => if x (M.witness c S R u x) = false then 1 else 0
    let g : (V → Bool) → ℝ := fun x => (if P x then 1 else 0) * h x
    let k : (V → Bool) → ℝ := fun b => if M.IsFree c u b then 2 / 3 else 1
    have hsplit : ∀ x, (if ∀ v ∈ insert u J, x (M.witness c S R v x) = false then (1 : ℝ)
        else 0) * h x = a x * g x := fun x => by
      simp only [a, g, P, forall_mem_insert]
      split_ifs <;> simp_all
    calc ∑ x ∈ I, (if ∀ v ∈ insert u J, x (M.witness c S R v x) = false then (1 : ℝ) else 0) *
          h x
        = ∑ x ∈ I, a x * g x := sum_congr rfl fun x _ => hsplit x
      _ ≤ ∑ x ∈ I, k (clearOn T x) * g x := by
        refine sum_mul_le_of_fiber I (clearOn T) a g k ?_ (fun x _ => ?_) ?_
        · -- The witnesses of the other edges and `h` ignore the cleared ends.
          intro x _ y _ hxy
          have hZ : ∀ t ∉ M.ends c S, x t = y t := fun t ht =>
            eq_of_clearOn_eq hxy fun h => ht (hT t h)
          have hP : P x ↔ P y := forall₂_congr fun v hv => by
            have hne : v ≠ u := fun h => hu (h ▸ hv)
            have hwT : M.witness c S R v y ∉ T := fun hw => by
              refine hS.end_notMem_edgeNbhd huS (hJS hv) hne (witness_eq (S := S) (R := R) v y) ?_
              simp only [T, mem_insert, mem_singleton] at hw
              rcases hw with hw | hw <;> rw [hw]
              exacts [self_mem_edgeNbhd c u, mate_mem_edgeNbhd c u]
            rw [witness_congr hZ, eq_of_clearOn_eq hxy hwT]
          simp only [g, hP, hh x y hZ]
        · simp only [g]; split_ifs <;> simp [h0 x]
        · intro x hx
          set b := clearOn T x
          set F := I.filter fun y => clearOn T y = b
          have hale : ∀ y, a y ≤ 1 := fun y => by simp only [a]; split_ifs <;> norm_num
          by_cases hfree : M.IsFree c u b
          · -- The fibre has at most three elements, one of which has its witness true.
            simp only [k, ite_eq_left hfree]
            set w := M.witness c S R u x
            have hwT : w ∈ T := by
              rcases witness_eq (M := M) (c := c) (S := S) (R := R) u x with h | h <;>
                simp [T, w, h]
            set y := Function.update b w true
            have hyb : ∀ t, t ≠ w → y t = b t := fun t ht => Function.update_of_ne ht _ _
            have hnbr : ∀ c', b (M.mate c' w) = false := fun c' => by
              by_cases hc' : c' = c
              · subst hc'
                refine clearOn_eq_of_mem ?_
                simp only [T, mem_insert, mem_singleton] at hwT ⊢
                rcases hwT with hw | hw <;> rw [hw]
                · exact .inr rfl
                · exact .inl (M.mate_mate c' u)
              · simp only [T, mem_insert, mem_singleton] at hwT
                rcases hwT with hw | hw <;> rw [hw]
                · exact hfree _ (mate_mem_otherNbrs hc' u)
                · exact hfree _ (mate_mate_mem_otherNbrs hc' u)
            have hbI : M.IsIndep b := (mem_filter.mp hx).2.clearOn T
            have hyI : M.IsIndep y := by
              rintro c' v ⟨h1, h2⟩
              by_cases hv : v = w
              · subst hv
                rw [hyb _ (M.mate_ne c' _), hnbr] at h2; exact absurd h2 (by simp)
              by_cases hmv : M.mate c' v = w
              · have : v = M.mate c' w := by rw [← hmv, M.mate_mate]
                rw [hyb v hv, this, hnbr] at h1; exact absurd h1 (by simp)
              · rw [hyb v hv] at h1; rw [hyb _ hmv] at h2; exact hbI c' v ⟨h1, h2⟩
            have hyF : y ∈ F := by
              refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hyI⟩, ?_⟩
              funext t
              by_cases ht : t ∈ T
              · rw [clearOn_eq_of_mem ht]; exact (clearOn_eq_of_mem ht).symm
              · rw [clearOn_eq_of_notMem ht, hyb t fun h => ht (h ▸ hwT)]
            have hay : a y = 0 := by
              have hwy : M.witness c S R u y = w := by
                rw [witness_congr (x' := x) fun t ht => ?_]
                rw [hyb t fun h => ht (h ▸ hT w hwT)]
                exact hoff x t ht
              simp [a, hwy, y]
            have hcard : #F ≤ 3 := by
              calc #F ≤ ((univ : Finset (Bool × Bool)).erase (true, true)).card := by
                    refine card_le_card_of_injOn (fun y => (y u, y (M.mate c u))) ?_ ?_
                    · intro z hz
                      refine mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩
                      simp only [Prod.mk.injEq] at h
                      exact (mem_filter.mp (mem_filter.mp hz).1).2 c u h
                    · intro z hz z' hz' hzz
                      simp only [Prod.mk.injEq] at hzz
                      funext t
                      by_cases ht : t ∈ T
                      · simp only [T, mem_insert, mem_singleton] at ht
                        rcases ht with rfl | rfl
                        exacts [hzz.1, hzz.2]
                      · exact eq_of_clearOn_eq ((mem_filter.mp hz).2.trans
                          (mem_filter.mp hz').2.symm) ht
                _ = 3 := by simp
            rw [← add_sum_erase _ _ hyF, hay, zero_add]
            have hsum : ∑ z ∈ F.erase y, a z ≤ #(F.erase y) := by
              rw [← mul_one (#(F.erase y) : ℝ), ← nsmul_eq_mul, ← sum_const]
              exact sum_le_sum fun z _ => hale z
            have hc : (#(F.erase y) : ℝ) + 1 = #F := by exact_mod_cast card_erase_add_one hyF
            have hc3 : (#F : ℝ) ≤ 3 := by exact_mod_cast hcard
            linarith
          · simp only [k, ite_eq_right hfree, one_mul]
            rw [← mul_one (#F : ℝ), ← nsmul_eq_mul, ← sum_const]
            exact sum_le_sum fun z _ => hale z
      _ = ∑ x ∈ I, (if P x then (1 : ℝ) else 0) * (k x * h x) := by
        refine sum_congr rfl fun x _ => ?_
        simp only [k, g, hfreeT]
        ring
      _ ≤ ∑ x ∈ I, (2 / 3 : ℝ) ^ #(J.filter fun u => M.IsFree c u x) * (k x * h x) := by
        refine ih hJS _ (fun x => mul_nonneg (by simp only [k]; split_ifs <;> norm_num) (h0 x))
          fun x y hxy => ?_
        have hfr : M.IsFree c u x ↔ M.IsFree c u y := forall₂_congr fun t ht => by
          rw [hxy t (hS.otherNbrs_notMem_ends huS ht)]
        simp only [k, hfr, hh x y hxy]
      _ = ∑ x ∈ I, (2 / 3 : ℝ) ^ #((insert u J).filter fun u => M.IsFree c u x) * h x := by
        refine sum_congr rfl fun x _ => ?_
        simp only [k, filter_insert]
        split_ifs with h1
        · rw [card_insert_of_notMem fun h => hu (mem_filter.mp h).1, pow_succ]; ring
        · ring

/-- **Rectangle size** [ArenasBroadrickLiewVanDenBroeck2026, Lemmas 5.5 and 5.6]. Let `R` be a
rectangle for the cut `(A, Aᶜ)` (closed under combining the `A`-part of one member with the rest
of another) inside the zeros of `f_G`, and let `S` list `k` crossing edges of one colour with
pairwise disjoint neighbourhoods. Then at most a `(47/48)^k` fraction of the independent sets lie
in `R`. -/
theorem card_filter_mem_le [DecidablePred (· ∈ R)] (hS : M.IsSeparatedCrossing A c S)
    (hR : ∀ x ∈ R, ∀ y ∈ R, A.piecewise x y ∈ R)
    (hR0 : ∀ x ∈ R, M.someButNotAllColors x = false) :
    (#{x ∈ univ.filter M.IsIndep | x ∈ R} : ℝ) ≤
      (47 / 48 : ℝ) ^ #S * #(univ.filter M.IsIndep) := by
  set I : Finset (V → Bool) := univ.filter M.IsIndep
  have hfac : ∀ x : V → Bool, (2 / 3 : ℝ) ^ #(S.filter fun u => M.IsFree c u x) =
      (2 / 3 : ℝ) ^ #S * (3 / 2 : ℝ) ^ #(S.filter fun u => ¬M.IsFree c u x) := fun x => by
    rw [← card_filter_add_card_filter_not (s := S) (fun u => M.IsFree c u x), pow_add, mul_assoc,
      ← mul_pow]
    norm_num
  calc (#{x ∈ I | x ∈ R} : ℝ)
      = ∑ x ∈ I, if x ∈ R then (1 : ℝ) else 0 := by rw [sum_boole]
    _ ≤ ∑ x ∈ I, (if ∀ u ∈ S, x (M.witness c S R u x) = false then (1 : ℝ) else 0) * 1 := by
        refine sum_le_sum fun x hx => ?_
        rw [mul_one]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (fun u hu => witness_eq_false hS hR hR0 h1 (mem_filter.mp hx).2 hu) h2
        · norm_num
        · exact le_rfl
    _ ≤ ∑ x ∈ I, (2 / 3 : ℝ) ^ #(S.filter fun u => M.IsFree c u x) * 1 :=
        sum_witness_le hS S subset_rfl _ (fun _ => zero_le_one) fun _ _ _ => rfl
    _ = (2 / 3 : ℝ) ^ #S * ∑ x ∈ I, (3 / 2 : ℝ) ^ #(S.filter fun u => ¬M.IsFree c u x) := by
        rw [mul_sum]; exact sum_congr rfl fun x _ => by rw [mul_one, hfac]
    _ ≤ (2 / 3 : ℝ) ^ #S * ((47 / 32 : ℝ) ^ #S * #I) := by
        gcongr; exact sum_pow_card_filter_not_isFree_le hS S subset_rfl
    _ = (47 / 48 : ℝ) ^ #S * #I := by rw [← mul_assoc, ← mul_pow]; norm_num

end Bound

/-! ### Many separated crossing edges in an expander -/

/-- **Greedy selection.** In a finite set where each element is related to at most `K` elements
(itself included), some pairwise unrelated subset has at least a `1/K` fraction of the elements. -/
private theorem exists_subset_pairwise_not {α : Type*} (r : α → α → Prop)
    [DecidableRel r] (hsymm : ∀ a b, r a b → r b a) (hrefl : ∀ a, r a a) (K : ℕ) :
    ∀ U : Finset α, (∀ u ∈ U, #(U.filter (r u)) ≤ K) →
      ∃ S ⊆ U, (∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → ¬r u u') ∧ #U ≤ K * #S := by
  classical
  intro U
  induction hU : #U using Nat.strong_induction_on generalizing U with
  | _ m ih =>
    intro hK
    rcases U.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨∅, empty_subset _, by simp, by simp at hU; omega⟩
    set U' := U.filter fun v => ¬r u v
    have hlt : #U' < m := hU ▸ card_lt_card (filter_ssubset.mpr ⟨u, hu, not_not.mpr (hrefl u)⟩)
    obtain ⟨S, hSU, hS, hcard⟩ := ih _ hlt U' rfl fun v hv =>
      (card_le_card (filter_subset_filter _ (filter_subset _ U))).trans
        (hK v (filter_subset _ U hv))
    have huS : u ∉ S := fun h => (mem_filter.mp (hSU h)).2 (hrefl u)
    refine ⟨insert u S, insert_subset hu (hSU.trans (filter_subset _ U)), ?_, ?_⟩
    · simp only [mem_insert]
      rintro v (rfl | hv) v' (rfl | hv') hne
      · exact absurd rfl hne
      · exact (mem_filter.mp (hSU hv')).2
      · exact fun h => (mem_filter.mp (hSU hv)).2 (hsymm _ _ h)
      · exact hS v hv v' hv' hne
    · have := card_filter_add_card_filter_not (s := U) (r u)
      rw [card_insert_of_notMem huS]
      have := hK u hu
      nlinarith

/-- The vertices `u'` whose edge of colour `c` has `t` in its neighbourhood. -/
private def nbhdPre (c : Fin 3) (t : V) : Finset V :=
  insert t ((univ.image fun c' => M.mate c' t) ∪ univ.image fun c' => M.mate c (M.mate c' t))

private theorem mem_nbhdPre {c : Fin 3} {t u' : V} (h : t ∈ M.edgeNbhd c u') :
    u' ∈ M.nbhdPre c t := by
  simp only [edgeNbhd, mem_insert, otherNbrs, mem_union, mem_image, mem_erase, mem_univ,
    and_true] at h
  simp only [nbhdPre, mem_insert, mem_union, mem_image, mem_univ, true_and]
  rcases h with rfl | h | ⟨c', -, h⟩ | ⟨c', -, h⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨c, M.mate_eq_iff.mp h.symm⟩)
  · exact .inr (.inl ⟨c', M.mate_eq_iff.mp h⟩)
  · exact .inr (.inr ⟨c', by rw [M.mate_eq_iff.mp h, M.mate_mate]⟩)

private theorem card_nbhdPre_le (c : Fin 3) (t : V) : #(M.nbhdPre c t) ≤ 7 := by
  refine (card_insert_le _ _).trans ?_
  have h1 := card_image_le (s := (univ : Finset (Fin 3))) (f := fun c' => M.mate c' t)
  have h2 := card_image_le (s := (univ : Finset (Fin 3))) (f := fun c' => M.mate c (M.mate c' t))
  have := card_union_le (univ.image fun c' => M.mate c' t)
    (univ.image fun c' => M.mate c (M.mate c' t))
  simp only [card_univ, Fintype.card_fin] at h1 h2
  omega

theorem card_edgeNbhd_le (c : Fin 3) (u : V) : #(M.edgeNbhd c u) ≤ 6 := by
  have := card_otherNbrs_le (M := M) c u
  have h1 := card_insert_le (M.mate c u) (M.otherNbrs c u)
  have h2 := card_insert_le u (insert (M.mate c u) (M.otherNbrs c u))
  simp only [edgeNbhd]
  omega

/-- An edge's neighbourhood meets the neighbourhoods of at most `42` edges of its colour. -/
private theorem card_filter_not_disjoint_le (c : Fin 3) (U : Finset V) (u : V) :
    #(U.filter fun u' => ¬Disjoint (M.edgeNbhd c u) (M.edgeNbhd c u')) ≤ 42 := by
  calc #(U.filter fun u' => ¬Disjoint (M.edgeNbhd c u) (M.edgeNbhd c u'))
      ≤ #((M.edgeNbhd c u).biUnion (M.nbhdPre c)) := by
        refine card_le_card fun u' hu' => ?_
        obtain ⟨t, htu, htu'⟩ := not_disjoint_iff.mp (mem_filter.mp hu').2
        exact mem_biUnion.mpr ⟨t, htu, mem_nbhdPre htu'⟩
    _ ≤ ∑ t ∈ M.edgeNbhd c u, #(M.nbhdPre c t) := card_biUnion_le
    _ ≤ ∑ _t ∈ M.edgeNbhd c u, 7 := sum_le_sum fun t _ => card_nbhdPre_le c t
    _ ≤ 42 := by rw [sum_const, smul_eq_mul]; have := card_edgeNbhd_le (M := M) c u; omega

section Expander

variable [Fintype V]

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Lemma 5.4].** If the graph is a balanced-cut
`γ`-edge expander, every balanced cut `(A, Aᶜ)` is crossed by `k ≥ γ |V| / 126` edges of a
single colour with pairwise disjoint neighbourhoods. -/
theorem exists_isSeparatedCrossing {γ : ℝ} (hG : IsBalancedCutExpander M.toSimpleGraph γ)
    {A : Finset V} (hA : Fintype.card V ≤ 3 * #A) (hAc : Fintype.card V ≤ 3 * #Aᶜ) :
    ∃ c S, M.IsSeparatedCrossing A c S ∧ γ * Fintype.card V ≤ 126 * #S := by
  have hcross := hG A hA hAc
  rw [M.card_interedges A, Fin.sum_univ_three] at hcross
  -- Some colour carries a third of the crossing edges.
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, γ * Fintype.card V ≤ 3 * #(A.filter fun u => M.mate c u ∉ A) := by
    by_contra! h
    push_cast at hcross
    linarith [h 0, h 1, h 2]
  obtain ⟨S, hSU, hS, hcard⟩ := exists_subset_pairwise_not
    (fun u u' => ¬Disjoint (M.edgeNbhd c u) (M.edgeNbhd c u'))
    (fun _ _ h h' => h h'.symm)
    (fun u => Finset.not_disjoint_iff.mpr ⟨u, self_mem_edgeNbhd c u, self_mem_edgeNbhd c u⟩)
    42 _ fun u _ => card_filter_not_disjoint_le c _ u
  refine ⟨c, S, ⟨fun u hu => (mem_filter.mp (hSU hu)).1, fun u hu => (mem_filter.mp (hSU hu)).2,
    fun u hu u' hu' hne => not_not.mp (hS u hu u' hu' hne)⟩, ?_⟩
  have : (#(A.filter fun u => M.mate c u ∉ A) : ℝ) ≤ 42 * #S := by exact_mod_cast hcard
  linarith

/-! ### The cover number of the zeros of `f_G` -/

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Theorem 5.3], lower bound, for every cover.** If the
graph is a balanced-cut `γ`-edge expander, every cover of the zeros of `f_G` by balanced
rectangles has at least `(48/47)^(γ |V| / 126)` rectangles. -/
theorem le_card_of_isCover {γ : ℝ} (hG : IsBalancedCutExpander M.toSimpleGraph γ) {k : ℕ}
    {R : Fin k → Set (V → Bool)}
    (hR : Communication.MultiPartition.IsCover (M.someButNotAllColors ⁻¹' {false}) R) :
    (48 / 47 : ℝ) ^ (γ * Fintype.card V / 126) ≤ k := by
  classical
  set I : Finset (V → Bool) := univ.filter M.IsIndep
  set e : ℝ := γ * Fintype.card V / 126
  have hIpos : (0 : ℝ) < #I := by
    exact_mod_cast card_pos.mpr ⟨fun _ => false, mem_filter.mpr ⟨mem_univ _, by
      simp [IsIndep]⟩⟩
  -- Each rectangle holds at most a `(47/48)^e` fraction of the independent sets.
  have hrect : ∀ i, (#{x ∈ I | x ∈ R i} : ℝ) ≤ (47 / 48 : ℝ) ^ e * #I := fun i => by
    obtain ⟨X, ⟨hX1, hX2⟩, P, Q, hRi⟩ := hR.1 i
    have hsub : ∀ x ∈ R i, M.someButNotAllColors x = false := fun x hx => by
      have : x ∈ ⋃ j, R j := Set.mem_iUnion.mpr ⟨i, hx⟩
      rw [hR.2] at this
      exact this
    have hmix : ∀ x ∈ R i, ∀ y ∈ R i, X.piecewise x y ∈ R i := fun x hx y hy => by
      rw [hRi] at hx hy ⊢
      refine ⟨?_, ?_⟩
      · convert hx.1 using 1
        funext ⟨t, ht⟩
        exact Finset.piecewise_eq_of_mem _ _ _ ht
      · convert hy.2 using 1
        funext ⟨t, ht⟩
        exact Finset.piecewise_eq_of_notMem _ _ _ ht
    obtain ⟨c, S, hS, hcard⟩ := M.exists_isSeparatedCrossing hG hX1 hX2
    refine (card_filter_mem_le hS hmix hsub).trans (mul_le_mul_of_nonneg_right ?_ hIpos.le)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by simp only [e]; linarith)
  -- The independent sets are zeros of `f_G`, so the rectangles cover them.
  have hcover : (#I : ℝ) ≤ k * ((47 / 48 : ℝ) ^ e * #I) := by
    calc (#I : ℝ) ≤ ∑ i : Fin k, (#{x ∈ I | x ∈ R i} : ℝ) := by
          rw [← Nat.cast_sum]
          refine Nat.cast_le.mpr ((card_le_card fun x hx => ?_).trans card_biUnion_le)
          have : x ∈ ⋃ j, R j := by
            rw [hR.2]; exact someButNotAllColors_of_isIndep M (mem_filter.mp hx).2
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp this
          exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨hx, hj⟩⟩
      _ ≤ ∑ _i : Fin k, (47 / 48 : ℝ) ^ e * #I := sum_le_sum fun i _ => hrect i
      _ = k * ((47 / 48 : ℝ) ^ e * #I) := by simp
  have hone : 1 ≤ k * (47 / 48 : ℝ) ^ e := by nlinarith
  have hinv : (48 / 47 : ℝ) ^ e * (47 / 48 : ℝ) ^ e = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < (48 / 47 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
  calc (48 / 47 : ℝ) ^ e = (48 / 47 : ℝ) ^ e * 1 := (mul_one _).symm
    _ ≤ (48 / 47 : ℝ) ^ e * (k * (47 / 48 : ℝ) ^ e) := by gcongr
    _ = k * ((48 / 47 : ℝ) ^ e * (47 / 48 : ℝ) ^ e) := by ring
    _ = k := by rw [hinv, mul_one]

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Theorem 5.3], the cover number.** For a balanced-cut
`γ`-edge expander on at least two vertices, `(48/47)^(γ |V| / 126) ≤ Cov^m_0(f_G) ≤ 2^|V|`. -/
theorem le_coverNumberFun {γ : ℝ} (hG : IsBalancedCutExpander M.toSimpleGraph γ)
    (hn : 2 ≤ Fintype.card V) :
    (48 / 47 : ℝ) ^ (γ * Fintype.card V / 126) ≤
        Communication.MultiPartition.coverNumberFun false M.someButNotAllColors ∧
      Communication.MultiPartition.coverNumberFun false M.someButNotAllColors ≤
        2 ^ Fintype.card V := by
  classical
  obtain ⟨R, hR⟩ := Communication.MultiPartition.exists_isCover_card hn
    (M.someButNotAllColors ⁻¹' {false})
  refine ⟨?_, hR.coverNumber_le.trans ?_⟩
  · obtain ⟨R', hR'⟩ := Nat.sInf_mem (s := {k | ∃ R : Fin k → Set (V → Bool),
      Communication.MultiPartition.IsCover (M.someButNotAllColors ⁻¹' {false}) R}) ⟨_, R, hR⟩
    exact le_card_of_isCover hG hR'
  · exact (card_filter_le _ _).trans (by simp)

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Theorem 5.3], DNNF size.** For a balanced-cut
`γ`-edge expander on at least two vertices, every DNNF computing `¬f_G` has at least
`(48/47)^(γ |V| / 126)` nodes, even without determinism. -/
theorem le_size_of_isDecomposable {γ : ℝ} (hG : IsBalancedCutExpander M.toSimpleGraph γ)
    (hn : 2 ≤ Fintype.card V) {N : Type*} [Fintype N] {D : Circuits.NNF V N}
    (hD : D.IsDecomposable)
    (hf : ∀ x, D.toFun x = !M.someButNotAllColors x) :
    (48 / 47 : ℝ) ^ (γ * Fintype.card V / 126) ≤ D.size := by
  obtain ⟨R, hR⟩ := Circuits.NNF.exists_isCover hD hn
  have : D.toFun ⁻¹' {true} = M.someButNotAllColors ⁻¹' {false} := by ext x; simp [hf]
  rw [this] at hR
  exact le_card_of_isCover hG hR

end Expander

end Cslib.CubicEdgeColoring
