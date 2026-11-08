/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/ColorRefinement.lean`, after
-- counting classes by `Nat.card (Set.range _)` instead of `Cslib.SetPartition.blocks`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SetPartition.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Multiset.Sum

/-!
# Color refinement

*Color refinement*, also called the 1-dimensional Weisfeiler–Leman algorithm or naive vertex
classification, refines a vertex coloring `χ₀` of a graph `G` round by round: in each round, a
vertex is recolored by the pair of its old color and the multiset of the old colors of its
neighbors. Two vertices that have the same color so far get different colors in the next round
when, for some color `c`, they have different numbers of neighbors of color `c`.

The colors of round `n` live in a type `RefinementColor α n` that depends only on the type `α` of
initial colors and on `n`, not on the graph. Colors of different graphs are therefore directly
comparable, which is the canonical color naming behind the color refinement isomorphism test.

A coloring `χ` is *equitable* (`SimpleGraph.IsEquitable`) when vertices of the same color have the
same multiset of neighbor colors, that is, when one round of refinement does not split any color
class. For partitions, given as setoids, this is the classical notion of an equitable partition
(`SimpleGraph.IsEquitablePartition`): any two vertices of a block have the same number of neighbors
in every block. This is unrelated to Mathlib's `Finpartition.IsEquipartition`, which asks for blocks
of almost equal sizes.

A coloring is compared with others through its partition into color classes, `Setoid.ker χ`, and
`Cslib.SetPartition.blocks` counts the classes. The partitions of successive rounds refine each
other, and the number of classes increases strictly until the partition stops changing. So on a
finite graph whose initial coloring has `k₀` classes, the partition is stable after `|V| - k₀`
rounds. The coloring after `|V|` rounds, `SimpleGraph.stableColoring`, is equitable, and its
partition is the coarsest equitable partition refining the initial one.

A graph isomorphism transports the colors of every round, so isomorphic graphs have the same color
histogram (multiset of vertex colors) in every round. This is the soundness of the color
refinement isomorphism test. The test is incomplete: two `d`-regular graphs with the same number of
vertices have the same histograms in every round. Running color refinement on the disjoint union
shows that agreement in round `|V| + |W|` implies agreement in every round.

The graphs are assumed `LocallyFinite`, which is what neighbor multisets need. Mathlib provides
this instance for a disjoint union `G ⊕g H` but no decidable adjacency instance.

## Main definitions

* `SimpleGraph.RefinementColor`: the type of colors of round `n`.
* `SimpleGraph.refineColoring`: one round of color refinement.
* `SimpleGraph.refinementColoring`: the coloring after `n` rounds.
* `SimpleGraph.IsEquitable`: equitable colorings.
* `SimpleGraph.IsEquitablePartition`: equitable partitions, given as setoids.
* `SimpleGraph.stableColoring`: the coloring after `|V|` rounds.
* `SimpleGraph.colorHistogram`: the multiset of the colors of round `n`.

## Main results

* `SimpleGraph.blocks_ker_refinementColoring_lt_succ`: the number of color classes increases
  strictly while the partition changes.
* `SimpleGraph.ker_refinementColoring_eq`: the partition is stable after `|V| - k₀` rounds.
* `SimpleGraph.isEquitable_stableColoring`: the stable coloring is equitable.
* `SimpleGraph.isGreatest_ker_stableColoring`: the partition of the stable coloring is the coarsest
  equitable partition refining the initial coloring.
* `SimpleGraph.Iso.colorHistogram_eq`: isomorphic colored graphs have the same color histograms.
* `SimpleGraph.isEmpty_iso_of_colorHistogram_ne`: soundness of the color refinement isomorphism
  test.
* `SimpleGraph.forall_colorHistogram_eq_iff`: histograms agree in every round when they agree in
  round `|V| + |W|`.
* `SimpleGraph.IsRegularOfDegree.colorHistogram_eq`: color refinement does not distinguish two
  `d`-regular graphs of the same order.

## Implementation notes

[GroheKerstingMladenovSelman2014] describe color refinement on graphs in words at the start of
Section 1 (Introduction). In its paragraph "Colour Refinement on Matrices" they work with the
color refinement of a matrix `A ∈ ℝ^{V×W}`, a weighted bipartite graph whose two sides are the rows
`V` and the columns `W`, from the trivial partition. They state stabilization within `|V| + |W|`
rounds, the number of vertices of that one bipartite graph, and that the result is the coarsest
equitable partition. A `0`-`1` matrix gives the bipartite graph `B_A`; according to the source,
general weighted directed graphs correspond to square matrices, but the source presents only the
bipartite case. The present file treats simple graphs with an arbitrary initial coloring directly.
The bound of `|V| - k₀` rounds is the standard counting argument. In
`SimpleGraph.forall_colorHistogram_eq_iff`, `V` and `W` are the vertex types of two graphs, so its
`|V| + |W|` is the order of their disjoint union and is unrelated to the source's bound. That
lemma and the regular-graph example are standard.

## References

* [M. Grohe, K. Kersting, M. Mladenov, E. Selman, *Dimension Reduction via Colour
  Refinement*][GroheKerstingMladenovSelman2014], Section 1 (Introduction), including the paragraph
  "Colour Refinement on Matrices".
-/

public section

open Finset

namespace SimpleGraph

/-- The colors of round `n` of color refinement started from colors in `α`: a color of round
`n + 1` is a color of round `n` together with a multiset of colors of round `n`. -/
@[expose] def RefinementColor (α : Type*) : ℕ → Type _
  | 0 => α
  | n + 1 => RefinementColor α n × Multiset (RefinementColor α n)

/-- Colors of every round have decidable equality when the initial colors do. -/
instance RefinementColor.instDecidableEq {α : Type*} [DecidableEq α] :
    (n : ℕ) → DecidableEq (RefinementColor α n)
  | 0 => inferInstanceAs (DecidableEq α)
  | n + 1 =>
    haveI := RefinementColor.instDecidableEq (α := α) n
    inferInstanceAs (DecidableEq (RefinementColor α n × Multiset (RefinementColor α n)))

variable {V W α β γ : Type*}

/-- If `g` is constant on the fibers of `f`, then two multisets with the same image under `f` have
the same image under `g`. -/
theorem _root_.Multiset.map_eq_map_of_ker_le {f : α → β} {g : α → γ}
    (h : Setoid.ker f ≤ Setoid.ker g) {s t : Multiset α} (hst : s.map f = t.map f) :
    s.map g = t.map g := by
  have hfg : g.FactorsThrough f := fun _ _ hab => h hab
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
  · rw [Multiset.eq_zero_of_forall_notMem (s := s) (fun x _ => hα.elim x),
      Multiset.eq_zero_of_forall_notMem (s := t) (fun x _ => hα.elim x)]
  · rw [← hfg.extend_comp (fun _ => g a), ← Multiset.map_map, ← Multiset.map_map, hst]

/-- One round of color refinement: the color of `v` together with the multiset of the colors of
its neighbors. -/
def refineColoring (G : SimpleGraph V) [G.LocallyFinite] (χ : V → β) (v : V) :
    β × Multiset β :=
  (χ v, (G.neighborFinset v).val.map χ)

/-- The coloring after `n` rounds of color refinement started from `χ₀`. -/
def refinementColoring (G : SimpleGraph V) [G.LocallyFinite] (χ₀ : V → α) :
    (n : ℕ) → V → RefinementColor α n
  | 0 => χ₀
  | n + 1 => G.refineColoring (G.refinementColoring χ₀ n)

/-- A coloring is *equitable* when vertices of the same color have the same multiset of neighbor
colors. -/
def IsEquitable (G : SimpleGraph V) [G.LocallyFinite] (χ : V → β) : Prop :=
  ∀ ⦃v w⦄, χ v = χ w → (G.neighborFinset v).val.map χ = (G.neighborFinset w).val.map χ

/-- A partition of the vertices, given as a setoid, is *equitable* when any two vertices of the
same block have the same number of neighbors in every block. The numbers are counted in `ℕ∞`, so
the definition also makes sense when neighborhoods are infinite. -/
def IsEquitablePartition (G : SimpleGraph V) (r : Setoid V) : Prop :=
  ∀ ⦃v w⦄, r v w → ∀ u,
    (G.neighborSet v ∩ {x | r u x}).encard = (G.neighborSet w ∩ {x | r u x}).encard

/-- The coloring after `|V|` rounds of color refinement started from `χ₀`. By
`SimpleGraph.ker_refinementColoring_eq`, its partition is the stable partition. -/
def stableColoring [Fintype V] (G : SimpleGraph V) [G.LocallyFinite] (χ₀ : V → α) :
    V → RefinementColor α (Fintype.card V) :=
  G.refinementColoring χ₀ (Fintype.card V)

/-- The color histogram of round `n`: the multiset of the colors of the vertices after `n`
rounds. -/
def colorHistogram [Fintype V] (G : SimpleGraph V) [G.LocallyFinite] (χ₀ : V → α) (n : ℕ) :
    Multiset (RefinementColor α n) :=
  (univ : Finset V).val.map (G.refinementColoring χ₀ n)

/-! ### One round -/

section Basic

variable {G : SimpleGraph V} [G.LocallyFinite] {χ₀ : V → α}

theorem refineColoring_apply (χ : V → β) (v : V) :
    G.refineColoring χ v = (χ v, (G.neighborFinset v).val.map χ) := by
  rw [refineColoring]

theorem refinementColoring_zero : G.refinementColoring χ₀ 0 = χ₀ := by
  rw [refinementColoring]

theorem refinementColoring_succ (n : ℕ) :
    G.refinementColoring χ₀ (n + 1) = G.refineColoring (G.refinementColoring χ₀ n) := by
  rw [refinementColoring]

theorem stableColoring_eq [Fintype V] :
    G.stableColoring χ₀ = G.refinementColoring χ₀ (Fintype.card V) := by
  rw [stableColoring]

theorem colorHistogram_eq [Fintype V] (n : ℕ) :
    G.colorHistogram χ₀ n = (univ : Finset V).val.map (G.refinementColoring χ₀ n) := by
  rw [colorHistogram]

theorem mem_colorHistogram [Fintype V] {n : ℕ} {c : RefinementColor α n} :
    c ∈ G.colorHistogram χ₀ n ↔ ∃ v, G.refinementColoring χ₀ n v = c := by
  simp only [colorHistogram, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

theorem isEquitable_iff {χ : V → β} : G.IsEquitable χ ↔
    ∀ ⦃v w⦄, χ v = χ w → (G.neighborFinset v).val.map χ = (G.neighborFinset w).val.map χ :=
  Iff.rfl

theorem refineColoring_eq_refineColoring_iff {χ : V → β} {v w : V} :
    G.refineColoring χ v = G.refineColoring χ w ↔
      χ v = χ w ∧ (G.neighborFinset v).val.map χ = (G.neighborFinset w).val.map χ :=
  Prod.ext_iff

/-- The multiset part of a refined color has as many elements as the vertex has neighbors. -/
theorem card_refineColoring_snd (χ : V → β) (v : V) :
    Multiset.card (G.refineColoring χ v).2 = G.degree v := by
  rw [refineColoring, Multiset.card_map, Finset.card_val, card_neighborFinset_eq_degree]

/-- A round of refinement refines the partition. -/
theorem ker_refineColoring_le (χ : V → β) : Setoid.ker (G.refineColoring χ) ≤ Setoid.ker χ :=
  fun _ _ h => (refineColoring_eq_refineColoring_iff.1 h).1

/-- A round of refinement is monotone in the partition. -/
theorem ker_refineColoring_mono {χ : V → β} {ψ : V → γ} (h : Setoid.ker χ ≤ Setoid.ker ψ) :
    Setoid.ker (G.refineColoring χ) ≤ Setoid.ker (G.refineColoring ψ) := by
  intro v w hvw
  obtain ⟨h1, h2⟩ := refineColoring_eq_refineColoring_iff.1 hvw
  exact refineColoring_eq_refineColoring_iff.2 ⟨h h1, Multiset.map_eq_map_of_ker_le h h2⟩

/-- A coloring is equitable exactly when a round of refinement does not split its classes. -/
theorem isEquitable_iff_ker_le {χ : V → β} :
    G.IsEquitable χ ↔ Setoid.ker χ ≤ Setoid.ker (G.refineColoring χ) :=
  ⟨fun h _ _ hvw => refineColoring_eq_refineColoring_iff.2 ⟨hvw, h hvw⟩,
    fun h _ _ hvw => (refineColoring_eq_refineColoring_iff.1 (h hvw)).2⟩

/-- Being equitable depends only on the partition into color classes. -/
theorem isEquitable_congr_ker {χ : V → β} {ψ : V → γ} (h : Setoid.ker χ = Setoid.ker ψ) :
    G.IsEquitable χ ↔ G.IsEquitable ψ := by
  rw [isEquitable_iff_ker_le, isEquitable_iff_ker_le, h,
    le_antisymm (ker_refineColoring_mono h.le) (ker_refineColoring_mono h.ge)]

/-- A constant coloring is equitable exactly when all vertices have the same degree. -/
theorem isEquitable_const_iff (b : β) :
    G.IsEquitable (fun _ => b) ↔ ∀ v w, G.degree v = G.degree w := by
  simp only [IsEquitable, Multiset.map_const', Finset.card_val, card_neighborFinset_eq_degree,
    forall_const, Multiset.replicate_left_injective b |>.eq_iff]

/-- A coloring is equitable exactly when vertices of the same color have the same number of
neighbors of each color. -/
theorem isEquitable_iff_card_filter [DecidableEq β] {χ : V → β} :
    G.IsEquitable χ ↔ ∀ ⦃v w⦄, χ v = χ w → ∀ c,
      ((G.neighborFinset v).filter (χ · = c)).card =
        ((G.neighborFinset w).filter (χ · = c)).card := by
  refine forall₂_congr fun v w => imp_congr_right fun _ => ?_
  rw [Multiset.ext]
  refine forall_congr' fun c => ?_
  rw [Multiset.count_map, Multiset.count_map]
  simp only [Finset.card_def, Finset.filter_val, eq_comm (a := c)]

private theorem encard_neighborSet_inter (v : V) (p : V → Prop) [DecidablePred p] :
    (G.neighborSet v ∩ {x | p x}).encard = ((G.neighborFinset v).filter p).card := by
  rw [← Set.encard_coe_eq_coe_finsetCard, Finset.coe_filter]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_neighborSet, mem_neighborFinset]

/-- A partition is equitable exactly when its quotient map is an equitable coloring. -/
theorem isEquitablePartition_iff_isEquitable_mk {r : Setoid V} :
    G.IsEquitablePartition r ↔ G.IsEquitable (Quotient.mk r) := by
  classical
  rw [isEquitable_iff_card_filter]
  refine forall₂_congr fun v w => ?_
  refine imp_congr Quotient.eq.symm ⟨fun h c => ?_, fun h u => ?_⟩
  · induction c using Quotient.inductionOn with
    | h u =>
      have hu := h u
      rw [encard_neighborSet_inter, encard_neighborSet_inter, Nat.cast_inj] at hu
      simpa only [Quotient.eq, Setoid.comm' r] using hu
  · have hu := h (Quotient.mk r u)
    rw [encard_neighborSet_inter, encard_neighborSet_inter, Nat.cast_inj]
    simpa only [Quotient.eq, Setoid.comm' r] using hu

/-- The partition into the color classes of `χ` is equitable exactly when `χ` is. -/
theorem isEquitablePartition_ker_iff {χ : V → β} :
    G.IsEquitablePartition (Setoid.ker χ) ↔ G.IsEquitable χ := by
  rw [isEquitablePartition_iff_isEquitable_mk, isEquitable_congr_ker (Setoid.ker_mk_eq _)]

end Basic

/-! ### Refinement and stabilization -/

section Refinement

variable {G : SimpleGraph V} [G.LocallyFinite] {χ₀ : V → α}

/-- Each round refines the partition of the previous round. -/
theorem ker_refinementColoring_succ_le (n : ℕ) :
    Setoid.ker (G.refinementColoring χ₀ (n + 1)) ≤ Setoid.ker (G.refinementColoring χ₀ n) :=
  ker_refineColoring_le _

theorem antitone_ker_refinementColoring :
    Antitone fun n => Setoid.ker (G.refinementColoring χ₀ n) :=
  antitone_nat_of_succ_le ker_refinementColoring_succ_le

/-- Every round refines the initial coloring. -/
theorem ker_refinementColoring_le_ker (n : ℕ) :
    Setoid.ker (G.refinementColoring χ₀ n) ≤ Setoid.ker χ₀ :=
  antitone_ker_refinementColoring (Nat.zero_le n)

/-- The coloring of round `n` is equitable exactly when round `n + 1` has the same partition. -/
theorem isEquitable_refinementColoring_iff {n : ℕ} :
    G.IsEquitable (G.refinementColoring χ₀ n) ↔
      Setoid.ker (G.refinementColoring χ₀ (n + 1)) = Setoid.ker (G.refinementColoring χ₀ n) :=
  isEquitable_iff_ker_le.trans
    ⟨fun h => le_antisymm (ker_refinementColoring_succ_le n) h, fun h => h.ge⟩

/-- Once a round does not change the partition, no later round does. -/
theorem ker_refinementColoring_eq_of_succ_eq {n : ℕ}
    (h : Setoid.ker (G.refinementColoring χ₀ (n + 1)) = Setoid.ker (G.refinementColoring χ₀ n))
    {m : ℕ} (hm : n ≤ m) :
    Setoid.ker (G.refinementColoring χ₀ m) = Setoid.ker (G.refinementColoring χ₀ n) := by
  have step : ∀ k, n ≤ k → Setoid.ker (G.refinementColoring χ₀ (k + 1)) =
      Setoid.ker (G.refinementColoring χ₀ k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k _ ih =>
      exact le_antisymm (ker_refinementColoring_succ_le _)
        (ker_refineColoring_mono (G := G) ih.ge)
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [step k hk, ih]

/-- An equitable partition refining the initial coloring refines the coloring of every round. -/
theorem IsEquitable.ker_le_ker_refinementColoring {ψ : V → β} (hψ : G.IsEquitable ψ)
    (h : Setoid.ker ψ ≤ Setoid.ker χ₀) (n : ℕ) :
    Setoid.ker ψ ≤ Setoid.ker (G.refinementColoring χ₀ n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (isEquitable_iff_ker_le.1 hψ).trans (ker_refineColoring_mono ih)

end Refinement

section Stabilization

open Cslib.SetPartition

variable {G : SimpleGraph V} [G.LocallyFinite] {χ₀ : V → α}

/-- The number of color classes does not decrease from one round to the next. -/
theorem blocks_ker_refinementColoring_le_succ [Finite V] (n : ℕ) :
    blocks (Setoid.ker (G.refinementColoring χ₀ n)) ≤
      blocks (Setoid.ker (G.refinementColoring χ₀ (n + 1))) :=
  blocks_le_of_le (ker_refinementColoring_succ_le n)

/-- The number of color classes increases strictly as long as the partition changes. -/
theorem blocks_ker_refinementColoring_lt_succ [Finite V] {n : ℕ}
    (h : Setoid.ker (G.refinementColoring χ₀ (n + 1)) ≠ Setoid.ker (G.refinementColoring χ₀ n)) :
    blocks (Setoid.ker (G.refinementColoring χ₀ n)) <
      blocks (Setoid.ker (G.refinementColoring χ₀ (n + 1))) :=
  blocks_lt_of_lt (lt_of_le_of_ne (ker_refinementColoring_succ_le n) h)

variable [Fintype V]

/-- **Stabilization**: if the initial coloring has `k₀` classes, then the partition does not change
after round `|V| - k₀`. -/
theorem ker_refinementColoring_eq {m : ℕ}
    (hm : Fintype.card V - blocks (Setoid.ker χ₀) ≤ m) :
    Setoid.ker (G.refinementColoring χ₀ m) =
      Setoid.ker (G.refinementColoring χ₀ (Fintype.card V - blocks (Setoid.ker χ₀))) := by
  set N := Fintype.card V - blocks (Setoid.ker χ₀)
  suffices ∃ i ≤ N, Setoid.ker (G.refinementColoring χ₀ (i + 1)) =
      Setoid.ker (G.refinementColoring χ₀ i) by
    obtain ⟨i, hi, h⟩ := this
    rw [ker_refinementColoring_eq_of_succ_eq h (hi.trans hm),
      ker_refinementColoring_eq_of_succ_eq h hi]
  by_contra hne
  push Not at hne
  have key : ∀ i ≤ N + 1, blocks (Setoid.ker χ₀) + i ≤
      blocks (Setoid.ker (G.refinementColoring χ₀ i)) := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      have := blocks_ker_refinementColoring_lt_succ (hne i (by omega))
      have := ih (by omega)
      omega
  have h1 := key (N + 1) le_rfl
  have h2 := blocks_le_card (Setoid.ker (G.refinementColoring χ₀ (N + 1)))
  have h3 := blocks_le_card (Setoid.ker χ₀)
  rw [Nat.card_eq_fintype_card] at h2 h3
  omega

/-- From round `|V|` on, the partition is that of the stable coloring. -/
theorem ker_stableColoring {m : ℕ} (hm : Fintype.card V ≤ m) :
    Setoid.ker (G.refinementColoring χ₀ m) = Setoid.ker (G.stableColoring χ₀) := by
  rw [stableColoring, ker_refinementColoring_eq ((Nat.sub_le _ _).trans hm),
    ker_refinementColoring_eq (Nat.sub_le _ _ |>.trans le_rfl)]

/-- The stable coloring is equitable. -/
theorem isEquitable_stableColoring : G.IsEquitable (G.stableColoring χ₀) := by
  rw [isEquitable_iff_ker_le]
  exact (ker_stableColoring (Nat.le_succ _)).ge

/-- The stable coloring refines the initial coloring. -/
theorem ker_stableColoring_le : Setoid.ker (G.stableColoring χ₀) ≤ Setoid.ker χ₀ :=
  ker_refinementColoring_le_ker _

/-- Every equitable coloring refining the initial coloring refines the stable coloring. -/
theorem IsEquitable.ker_le_ker_stableColoring {ψ : V → β} (hψ : G.IsEquitable ψ)
    (h : Setoid.ker ψ ≤ Setoid.ker χ₀) : Setoid.ker ψ ≤ Setoid.ker (G.stableColoring χ₀) :=
  hψ.ker_le_ker_refinementColoring h _

/-- **Coarsest equitable partition**: the partition of the stable coloring is the coarsest
equitable partition refining the initial coloring. -/
theorem isGreatest_ker_stableColoring :
    IsGreatest {r : Setoid V | r ≤ Setoid.ker χ₀ ∧ G.IsEquitablePartition r}
      (Setoid.ker (G.stableColoring χ₀)) := by
  refine ⟨⟨ker_stableColoring_le, isEquitablePartition_ker_iff.2 isEquitable_stableColoring⟩,
    fun r ⟨hr, hq⟩ => ?_⟩
  rw [isEquitablePartition_iff_isEquitable_mk] at hq
  rw [← Setoid.ker_mk_eq r] at hr ⊢
  exact hq.ker_le_ker_stableColoring hr

end Stabilization

/-! ### Isomorphism invariance and soundness -/

section Iso

variable {G : SimpleGraph V} [G.LocallyFinite] {H : SimpleGraph W} [H.LocallyFinite]

/-- An isomorphism maps the neighbors of `v` onto the neighbors of its image. -/
theorem Iso.neighborFinset_apply (e : G ≃g H) (v : V) :
    H.neighborFinset (e v) = (G.neighborFinset v).map e.toEquiv.toEmbedding := by
  ext w
  obtain ⟨w, rfl⟩ := e.surjective w
  simp only [mem_neighborFinset, mem_map_equiv, Iso.map_adj_iff]
  rw [show e.toEquiv.symm (e w) = w from e.toEquiv.symm_apply_apply w]

/-- An isomorphism of colored graphs preserves the colors of every round. -/
theorem Iso.refinementColoring_apply (e : G ≃g H) {χ₀ : V → α} {ψ₀ : W → α}
    (h₀ : ∀ v, ψ₀ (e v) = χ₀ v) (n : ℕ) (v : V) :
    H.refinementColoring ψ₀ n (e v) = G.refinementColoring χ₀ n v := by
  induction n generalizing v with
  | zero => exact h₀ v
  | succ n ih =>
    rw [refinementColoring_succ, refinementColoring_succ, refineColoring, refineColoring,
      ih, e.neighborFinset_apply, Finset.map_val, Multiset.map_map]
    congr 2
    exact funext ih

variable [Fintype V] [Fintype W]

/-- Isomorphic colored graphs have the same color histogram in every round. -/
theorem Iso.colorHistogram_eq (e : G ≃g H) {χ₀ : V → α} {ψ₀ : W → α}
    (h₀ : ∀ v, ψ₀ (e v) = χ₀ v) (n : ℕ) :
    H.colorHistogram ψ₀ n = G.colorHistogram χ₀ n := by
  rw [colorHistogram, colorHistogram, ← Finset.map_univ_equiv e.toEquiv, Finset.map_val,
    Multiset.map_map]
  congr 1
  exact funext (e.refinementColoring_apply h₀ n)

/-- **Soundness of the color refinement test** for colored graphs: if the color histograms differ
in some round, then no isomorphism preserves the initial colors. -/
theorem not_exists_iso_of_colorHistogram_ne {χ₀ : V → α} {ψ₀ : W → α} {n : ℕ}
    (h : G.colorHistogram χ₀ n ≠ H.colorHistogram ψ₀ n) :
    ¬∃ e : G ≃g H, ∀ v, ψ₀ (e v) = χ₀ v :=
  fun ⟨e, he⟩ => h (e.colorHistogram_eq he n).symm

/-- **Soundness of the color refinement test**: if the color histograms from the constant coloring
differ in some round, then the graphs are not isomorphic. -/
theorem isEmpty_iso_of_colorHistogram_ne {n : ℕ}
    (h : G.colorHistogram (fun _ => ()) n ≠ H.colorHistogram (fun _ => ()) n) :
    IsEmpty (G ≃g H) :=
  ⟨fun e => h (e.colorHistogram_eq (χ₀ := fun _ => ()) (ψ₀ := fun _ => ()) (fun _ => rfl) n).symm⟩

end Iso

/-! ### Disjoint unions -/

section Sum

variable {G : SimpleGraph V} [G.LocallyFinite] {H : SimpleGraph W} [H.LocallyFinite]
  [(G ⊕g H).LocallyFinite]

omit [H.LocallyFinite] in
theorem neighborFinset_sum_inl (v : V) :
    (G ⊕g H).neighborFinset (.inl v) = (G.neighborFinset v).map .inl := by
  ext (w | w) <;> simp

omit [G.LocallyFinite] in
theorem neighborFinset_sum_inr (w : W) :
    (G ⊕g H).neighborFinset (.inr w) = (H.neighborFinset w).map .inr := by
  ext (v | v) <;> simp

omit [H.LocallyFinite] in
/-- On the left summand, color refinement of a disjoint union is color refinement of `G`. -/
theorem refinementColoring_sum_inl (χ₀ : V ⊕ W → α) (n : ℕ) (v : V) :
    (G ⊕g H).refinementColoring χ₀ n (.inl v) = G.refinementColoring (χ₀ ∘ .inl) n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [refinementColoring_succ, refinementColoring_succ, refineColoring, refineColoring, ih,
      neighborFinset_sum_inl, Finset.map_val, Multiset.map_map]
    congr 2
    exact funext ih

omit [G.LocallyFinite] in
/-- On the right summand, color refinement of a disjoint union is color refinement of `H`. -/
theorem refinementColoring_sum_inr (χ₀ : V ⊕ W → α) (n : ℕ) (w : W) :
    (G ⊕g H).refinementColoring χ₀ n (.inr w) = H.refinementColoring (χ₀ ∘ .inr) n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [refinementColoring_succ, refinementColoring_succ, refineColoring, refineColoring, ih,
      neighborFinset_sum_inr, Finset.map_val, Multiset.map_map]
    congr 2
    exact funext ih

/-- The histogram of a disjoint union is the sum of the histograms. -/
theorem colorHistogram_sum [Fintype V] [Fintype W] (χ₀ : V ⊕ W → α) (n : ℕ) :
    (G ⊕g H).colorHistogram χ₀ n =
      G.colorHistogram (χ₀ ∘ .inl) n + H.colorHistogram (χ₀ ∘ .inr) n := by
  rw [colorHistogram, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
  simp only [refinementColoring_sum_inl, refinementColoring_sum_inr]
  rfl

end Sum

/-! ### Earlier rounds and completeness of round `|V| + |W|` -/

section Truncate

/-- Forget the last `k` rounds of a color of round `n + k`. -/
def RefinementColor.truncate (n : ℕ) : (k : ℕ) → RefinementColor α (n + k) → RefinementColor α n
  | 0, c => c
  | k + 1, c => truncate n k c.1

variable {G : SimpleGraph V} [G.LocallyFinite]

/-- The color of round `n + k` determines the color of round `n`. -/
theorem truncate_refinementColoring (χ₀ : V → α) (n k : ℕ) (v : V) :
    (G.refinementColoring χ₀ (n + k) v).truncate n k = G.refinementColoring χ₀ n v := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

variable [Fintype V] [Fintype W]

/-- The histogram of round `n + k` determines the histogram of round `n`. -/
theorem colorHistogram_map_truncate (χ₀ : V → α) (n k : ℕ) :
    (G.colorHistogram χ₀ (n + k)).map (RefinementColor.truncate n k) = G.colorHistogram χ₀ n := by
  rw [colorHistogram, colorHistogram, Multiset.map_map]
  congr 1
  exact funext (truncate_refinementColoring χ₀ n k)

/-- Histograms that agree in some round agree in every earlier round. -/
theorem colorHistogram_eq_of_le {H : SimpleGraph W} [H.LocallyFinite] {χ₀ : V → α}
    {ψ₀ : W → α} {m n : ℕ} (hnm : n ≤ m) (h : G.colorHistogram χ₀ m = H.colorHistogram ψ₀ m) :
    G.colorHistogram χ₀ n = H.colorHistogram ψ₀ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [← colorHistogram_map_truncate χ₀ n k, ← colorHistogram_map_truncate ψ₀ n k, h]

end Truncate

section Completeness

variable [Fintype V] [Fintype W] {G : SimpleGraph V} [G.LocallyFinite] {H : SimpleGraph W}
  [H.LocallyFinite]

/-- Color refinement distinguishes two graphs in some round exactly when it distinguishes them in
round `|V| + |W|`. The proof runs color refinement on the disjoint union, whose partition is stable
from round `|V| + |W|` on. -/
theorem forall_colorHistogram_eq_iff {χ₀ : V → α} {ψ₀ : W → α} :
    (∀ n, G.colorHistogram χ₀ n = H.colorHistogram ψ₀ n) ↔
      G.colorHistogram χ₀ (Fintype.card V + Fintype.card W) =
        H.colorHistogram ψ₀ (Fintype.card V + Fintype.card W) := by
  classical
  refine ⟨fun h => h _, fun h m => ?_⟩
  set N := Fintype.card V + Fintype.card W
  rcases le_total m N with hm | hm
  · exact colorHistogram_eq_of_le hm h
  let χ : V ⊕ W → α := Sum.elim χ₀ ψ₀
  have hker : Setoid.ker ((G ⊕g H).refinementColoring χ N) ≤
      Setoid.ker ((G ⊕g H).refinementColoring χ m) := by
    have hN : Fintype.card (V ⊕ W) = N := Fintype.card_sum
    rw [ker_stableColoring hN.le, ker_stableColoring (hN.le.trans hm)]
  have hG : ∀ n, G.colorHistogram χ₀ n =
      (univ : Finset V).val.map ((G ⊕g H).refinementColoring χ n ∘ Sum.inl) := fun n => by
    rw [colorHistogram]
    congr 1
    exact funext fun v => (refinementColoring_sum_inl χ n v).symm
  have hH : ∀ n, H.colorHistogram ψ₀ n =
      (univ : Finset W).val.map ((G ⊕g H).refinementColoring χ n ∘ Sum.inr) := fun n => by
    rw [colorHistogram]
    congr 1
    exact funext fun w => (refinementColoring_sum_inr χ n w).symm
  rw [hG, hH, ← Multiset.map_map, ← Multiset.map_map]
  rw [hG, hH, ← Multiset.map_map, ← Multiset.map_map] at h
  exact Multiset.map_eq_map_of_ker_le hker h

end Completeness

/-! ### Regular graphs -/

section Regular

/-- The color of every vertex of a `d`-regular graph after `n` rounds from the constant
coloring. -/
private def regularColor (d : ℕ) : (n : ℕ) → RefinementColor Unit n
  | 0 => ()
  | n + 1 => (regularColor d n, Multiset.replicate d (regularColor d n))

private theorem refinementColoring_of_isRegularOfDegree {G : SimpleGraph V} [G.LocallyFinite]
    {d : ℕ} (hG : G.IsRegularOfDegree d) (n : ℕ) (v : V) :
    G.refinementColoring (fun _ => ()) n v = regularColor d n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    have hc : G.refinementColoring (fun _ => ()) n = fun _ => regularColor d n := funext ih
    change (G.refinementColoring (fun _ => ()) n v,
        (G.neighborFinset v).val.map (G.refinementColoring (fun _ => ()) n)) =
      (regularColor d n, Multiset.replicate d (regularColor d n))
    rw [hc, Multiset.map_const', Finset.card_val, card_neighborFinset_eq_degree, hG.degree_eq]

/-- **Incompleteness of the color refinement test**: two `d`-regular graphs with the same number of
vertices have the same color histograms in every round. -/
theorem IsRegularOfDegree.colorHistogram_eq [Fintype V] [Fintype W] {G : SimpleGraph V}
    [G.LocallyFinite] {H : SimpleGraph W} [H.LocallyFinite] {d : ℕ} (hG : G.IsRegularOfDegree d)
    (hH : H.IsRegularOfDegree d) (hcard : Fintype.card V = Fintype.card W) (n : ℕ) :
    G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [colorHistogram, colorHistogram, funext (refinementColoring_of_isRegularOfDegree hG n),
    funext (refinementColoring_of_isRegularOfDegree hH n), Multiset.map_const',
    Multiset.map_const', Finset.card_val, Finset.card_val, Finset.card_univ, Finset.card_univ,
    hcard]

end Regular

end SimpleGraph
