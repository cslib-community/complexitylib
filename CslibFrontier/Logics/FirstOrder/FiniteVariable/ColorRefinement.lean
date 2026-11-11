/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ColorRefinement
public import CslibFrontier.Foundations.ModelTheory.Graph
public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Basic
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.BijectiveGame
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

/-!
# The Immerman–Lander theorem: `C²` and color refinement

On finite simple graphs, color refinement (1-dimensional Weisfeiler–Leman) started from the
constant coloring `fun _ => ()` characterizes equivalence in the two-variable counting logic `C²`
over `FirstOrder.Language.graph`.

In Hella's bijective `2`-pebble game, moving one pebble while the other rests on `v` in `G` and `w`
in `H` asks for a bijection `f : V ≃ W` carrying `v` to `w`, neighbors of `v` to neighbors of `w`,
and colors of the previous round to equal colors. Because `SimpleGraph.refineColoring` records a
vertex's old color together with the multiset of old colors of its **neighbors**, while a bijection
on `V` and `W` must also match the **non-neighbors** of each color, such a bijection exists
(`SimpleGraph.exists_equiv_adj_iff_refineColoring_eq`) if and only if `v` and `w` receive the same
refined color and the two graphs have the same color histogram in the previous round (compare
[CaiFurerImmerman1992], Section 5, where `1`-dimensional Weisfeiler–Leman explicitly records counts
across every adjacency relation including non-adjacency). When no other pebble is placed, moving a
pebble simply matches the vertices color by color, which is equality of the previous round's color
histograms (`Equiv.exists_apply_eq_iff_map_univ_eq`).

Simultaneous induction over the placed-pebble set `S : Set (Fin 2)` therefore identifies winning
positions of the `(n + 1)`-round bijective `2`-pebble game with round-`n` color histograms and
round-`(n + 1)` vertex colors (`bijPebbleWins_graph_iff`), with specializations to `∅`, `{i}` and
`Set.univ`. Note the round-index shift on sentences: the first round of the bijective game from `∅`
already tests equal order (`colorHistogram _ 0`), while one round of neighbor counting corresponds
to quantifier rank `2` (`colorHistogram _ 1`).

Combining the game equivalence with the Hintikka characterization of `C^k` on finite structures
(`Cslib.Logic.FO.bijPebbleWins_iff_forall_realize_iff`) gives the **Immerman–Lander theorem** both
for single vertices (`forall_realize_countingFormula_singleton_le_iff`,
`forall_realize_countingFormula_singleton_iff`) and for sentences
(`forall_realize_countingFormula_empty_le_iff`, `forall_realize_countingFormula_empty_iff`). By
stabilization on the disjoint union (`SimpleGraph.forall_colorHistogram_eq_iff` and
`SimpleGraph.forall_refinementColoring_eq_iff`), `C²`-equivalence across all quantifier ranks
reduces to round `|V| + |W|` (`forall_realize_countingFormula_empty_iff_card_add_card`,
`forall_realize_countingFormula_singleton_iff_card_add_card`).

Because `CountingFormula.Realize` takes a total assignment `Fin 2 → V`, sentence statements
quantifying over assignments are vacuous when `V` or `W` is empty; the graph-level sentence
equivalences therefore assume `[Nonempty V] [Nonempty W]`. All results assume only `[Fintype]` and
`[LocallyFinite]`, with no decidable-adjacency requirement, so they apply directly to disjoint
unions `G ⊕g H`.

## Main results

* `SimpleGraph.exists_equiv_adj_iff_refineColoring_eq`: a color-preserving bijection carrying `v`
  to `w` and neighbors of `v` to neighbors of `w` exists iff `v` and `w` have equal refined colors
  and the overall color multisets agree.
* `Cslib.Logic.FO.bijPebbleWins_graph_iff`, `Cslib.Logic.FO.bijPebbleWins_graph_empty_iff`,
  `Cslib.Logic.FO.bijPebbleWins_graph_singleton_iff`,
  `Cslib.Logic.FO.bijPebbleWins_graph_univ_iff`: round-by-round equivalence between the bijective
  `2`-pebble game on simple graphs and color refinement.
* `Cslib.Logic.FO.bijPebbleWinsForever_graph_empty_iff`,
  `Cslib.Logic.FO.bijPebbleWinsForever_graph_singleton_iff`: infinite bijective `2`-pebble game and
  color refinement across all rounds.
* `Cslib.Logic.FO.forall_realize_countingFormula_singleton_le_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff_card_add_card`: **Immerman–Lander
  theorem, vertex form** (`C²` formulas in one free variable vs vertex colors and histograms).
* `Cslib.Logic.FO.forall_realize_countingFormula_empty_le_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_empty_iff`,
  `Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_card_add_card`,
  `Cslib.Logic.FO.realize_countingFormula_iff_of_colorHistogram_eq`: **Immerman–Lander theorem,
  sentence form** (`C²` sentences vs color histograms).

## References

* [N. Immerman and E. Lander, *Describing graphs: a first-order approach to graph
  canonization*][ImmermanLander1990] (unverified locator).
* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 5, Theorem 5.2 (`k = 1` case).
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.5 (unverified locator).
-/

public section

open FirstOrder Language Structure SimpleGraph

/-! ### Fiber bijections for one round of color refinement -/

section Fiber

variable {V W β : Type*} [Fintype V] [Fintype W]

private theorem count_map_adjLabel [DecidableEq V] [DecidableEq β] (G : SimpleGraph V)
    [G.LocallyFinite] [DecidableRel G.Adj] (χ : V → β) (v : V) (x : β) :
    let label : V → Bool × Bool × β := fun c => (decide (c = v), decide (G.Adj v c), χ c)
    (Finset.univ.val.map label).count (true, true, x) = 0 ∧
      (Finset.univ.val.map label).count (true, false, x) = (if χ v = x then 1 else 0) ∧
      (Finset.univ.val.map label).count (false, true, x) =
        ((G.neighborFinset v).val.map χ).count x ∧
      (Finset.univ.val.map label).count (false, false, x) +
          (Finset.univ.val.map label).count (false, true, x) +
          (Finset.univ.val.map label).count (true, false, x) =
        (Finset.univ.val.map χ).count x := by
  intro label
  have hcnt : ∀ b₁ b₂, (Finset.univ.val.map label).count (b₁, b₂, x) =
      (Finset.univ.filter fun c =>
        decide (c = v) = b₁ ∧ decide (G.Adj v c) = b₂ ∧ χ c = x).card := by
    intro b₁ b₂
    rw [Multiset.count_map, Finset.card_def, ← Finset.filter_val]
    congr 2
    ext c
    simp only [label, Prod.mk.injEq, eq_comm]
  have h1 : (Finset.univ.val.map label).count (true, true, x) = 0 := by
    rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨hcv, hadj, -⟩
    rw [decide_eq_true_eq] at hcv hadj
    subst hcv
    exact G.irrefl hadj
  have h2 : (Finset.univ.val.map label).count (true, false, x) = if χ v = x then 1 else 0 := by
    rw [hcnt]
    have hfilt : (Finset.univ.filter fun c =>
        decide (c = v) = true ∧ decide (G.Adj v c) = false ∧ χ c = x) =
        if χ v = x then {v} else ∅ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
        decide_eq_false_iff_not]
      split_ifs with hx
      · simp only [Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, G.irrefl, hx⟩⟩
      · simp only [Finset.notMem_empty, iff_false, not_and]
        rintro rfl -
        exact hx
    rw [hfilt]
    split_ifs <;> simp
  have h3 : (Finset.univ.val.map label).count (false, true, x) =
      ((G.neighborFinset v).val.map χ).count x := by
    rw [hcnt, Multiset.count_map, Finset.card_def, ← Finset.filter_val]
    congr 2
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not,
      decide_eq_true_eq, mem_neighborFinset, eq_comm (a := x)]
    exact ⟨fun ⟨_, hadj, hx⟩ => ⟨hadj, hx⟩, fun ⟨hadj, hx⟩ => ⟨G.ne_of_adj hadj |>.symm, hadj, hx⟩⟩
  refine ⟨h1, h2, h3, ?_⟩
  have htot : (Finset.univ.val.map χ).count x = (Finset.univ.filter fun c => χ c = x).card := by
    rw [Multiset.count_map, Finset.card_def, ← Finset.filter_val]
    simp only [eq_comm (a := x)]
  rw [hcnt, hcnt, hcnt, htot]
  set S := Finset.univ.filter fun c : V => χ c = x
  have hsplit1 := S.card_filter_add_card_filter_not (fun c => c = v)
  have hsplit2 := (S.filter fun c => ¬c = v).card_filter_add_card_filter_not (fun c => G.Adj v c)
  have heq_tf : (Finset.univ.filter fun c =>
      decide (c = v) = true ∧ decide (G.Adj v c) = false ∧ χ c = x) =
      S.filter fun c => c = v := by
    ext c
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      decide_eq_false_iff_not]
    exact ⟨fun ⟨hcv, _, hx⟩ => ⟨hx, hcv⟩, fun ⟨hx, hcv⟩ => by subst hcv; exact ⟨rfl, G.irrefl, hx⟩⟩
  have heq_ft : (Finset.univ.filter fun c =>
      decide (c = v) = false ∧ decide (G.Adj v c) = true ∧ χ c = x) =
      (S.filter fun c => ¬c = v).filter fun c => G.Adj v c := by
    ext c
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not,
      decide_eq_true_eq]
    tauto
  have heq_ff : (Finset.univ.filter fun c =>
      decide (c = v) = false ∧ decide (G.Adj v c) = false ∧ χ c = x) =
      (S.filter fun c => ¬c = v).filter fun c => ¬G.Adj v c := by
    ext c
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not]
    tauto
  rw [heq_tf, heq_ft, heq_ff]
  omega

/-- A bijection `f : V ≃ W` carrying `v` to `w`, neighbors of `v` to neighbors of `w`, and
`χ`-colors to `ψ`-colors exists if and only if `v` and `w` receive the same refined color and `χ`
and `ψ` have the same overall multiset of colors. -/
theorem SimpleGraph.exists_equiv_adj_iff_refineColoring_eq
    {G : SimpleGraph V} [G.LocallyFinite] {H : SimpleGraph W} [H.LocallyFinite]
    {χ : V → β} {ψ : W → β} {v : V} {w : W} :
    (∃ f : V ≃ W, ∀ c, (c = v ↔ f c = w) ∧ (G.Adj v c ↔ H.Adj w (f c)) ∧ χ c = ψ (f c)) ↔
      G.refineColoring χ v = H.refineColoring ψ w ∧
        (Finset.univ : Finset V).val.map χ = (Finset.univ : Finset W).val.map ψ := by
  constructor
  · rintro ⟨f, hf⟩
    have hv : f v = w := (hf v).1.1 rfl
    have hχv : χ v = ψ w := by
      have := (hf v).2.2
      rwa [hv] at this
    have huniv : (Finset.univ : Finset V).val.map χ = (Finset.univ : Finset W).val.map ψ :=
      Equiv.exists_apply_eq_iff_map_univ_eq.1 ⟨f, fun c => ((hf c).2.2).symm⟩
    have hnbhd : H.neighborFinset w = (G.neighborFinset v).map f.toEmbedding := by
      ext d
      obtain ⟨c, rfl⟩ := f.surjective d
      simp only [mem_neighborFinset, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact ((hf c).2.1).symm
    refine ⟨refineColoring_eq_refineColoring_iff.2 ⟨hχv, ?_⟩, huniv⟩
    rw [hnbhd, Finset.map_val, Multiset.map_map]
    congr 1
    exact funext fun c => (hf c).2.2
  · rintro ⟨href, huniv⟩
    classical
    obtain ⟨hχv, hnbhd⟩ := refineColoring_eq_refineColoring_iff.1 href
    let labelG : V → Bool × Bool × β := fun c => (decide (c = v), decide (G.Adj v c), χ c)
    let labelH : W → Bool × Bool × β := fun d => (decide (d = w), decide (H.Adj w d), ψ d)
    have hlabel : (Finset.univ : Finset V).val.map labelG =
        (Finset.univ : Finset W).val.map labelH := by
      refine Multiset.ext.2 fun ⟨b₁, b₂, x⟩ => ?_
      obtain ⟨hG11, hG10, hG01, hGsum⟩ := count_map_adjLabel G χ v x
      obtain ⟨hH11, hH10, hH01, hHsum⟩ := count_map_adjLabel H ψ w x
      dsimp only [labelG, labelH]
      have hx : (Finset.univ.val.map χ).count x = (Finset.univ.val.map ψ).count x := by rw [huniv]
      have hnx : ((G.neighborFinset v).val.map χ).count x =
          ((H.neighborFinset w).val.map ψ).count x := by rw [hnbhd]
      rcases b₁ <;> rcases b₂
      · rw [hG01, hG10, hχv, hnx, hx] at hGsum
        rw [hH01, hH10] at hHsum
        omega
      · rw [hG01, hH01, hnx]
      · rw [hG10, hH10, hχv]
      · rw [hG11, hH11]
    obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hlabel
    refine ⟨f, fun c => ?_⟩
    have hc := (hf c).symm
    simp only [labelG, labelH, Prod.mk.injEq, decide_eq_decide] at hc
    exact hc

end Fiber

namespace Cslib.Logic.FO

section GraphPebble

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

private theorem fin_two_add_one_ne (p : Fin 2) : p + 1 ≠ p := by
  revert p
  decide

private theorem fin_two_eq_or_add_one (p q : Fin 2) : q = p ∨ q = p + 1 := by
  revert p q
  decide

private theorem fin_two_add_one_add_one (p : Fin 2) : p + 1 + 1 = p := by
  revert p
  decide

private theorem comp_vec_two {α β : Type*} (a : α → β) (i j : α) : a ∘ ![i, j] = ![a i, a j] :=
  (FinVec.map_eq a ![i, j]).symm

private theorem partialIsoOn_graph_two_iff {S : Set (Fin 2)} {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure; PartialIsoOn Language.graph S a b) ↔
      ∀ i ∈ S, ∀ j ∈ S, (a i = a j ↔ b i = b j) ∧ (G.Adj (a i) (a j) ↔ H.Adj (b i) (b j)) := by
  let := G.structure
  let := H.structure
  constructor
  · intro h i hi j hj
    refine ⟨h.eq_iff i hi j hj, ?_⟩
    have hadj := h.relMap_iff adj ![i, j] (by intro t; fin_cases t <;> assumption)
    rwa [comp_vec_two, comp_vec_two] at hadj
  · intro h
    refine ⟨fun i hi j hj => (h i hi j hj).1, fun {l} R f hf => ?_⟩
    cases R
    have hf' : f = ![f 0, f 1] := funext fun t => by fin_cases t <;> rfl
    rw [hf', comp_vec_two, comp_vec_two]
    exact (h _ (hf 0) _ (hf 1)).2

private theorem partialIsoOn_graph_singleton (i : Fin 2) (a : Fin 2 → V) (b : Fin 2 → W) :
    letI := G.structure; letI := H.structure
    PartialIsoOn Language.graph {i} a b := by
  rw [partialIsoOn_graph_two_iff]
  rintro p rfl q rfl
  exact ⟨iff_of_true rfl rfl, iff_of_false G.irrefl H.irrefl⟩

private theorem partialIsoOn_graph_insert_iff {S : Set (Fin 2)} {a : Fin 2 → V} {b : Fin 2 → W}
    (p : Fin 2) (c : V) (d : W) :
    (letI := G.structure; letI := H.structure
      PartialIsoOn Language.graph (insert p S) (Function.update a p c) (Function.update b p d)) ↔
      (p + 1 ∈ S → (c = a (p + 1) ↔ d = b (p + 1)) ∧
        (G.Adj (a (p + 1)) c ↔ H.Adj (b (p + 1)) d)) := by
  rw [partialIsoOn_graph_two_iff]
  have hupd_a : Function.update a p c (p + 1) = a (p + 1) :=
    Function.update_of_ne (fin_two_add_one_ne p) c a
  have hupd_b : Function.update b p d (p + 1) = b (p + 1) :=
    Function.update_of_ne (fin_two_add_one_ne p) d b
  constructor
  · intro h hp1
    have h1 := h p (Set.mem_insert p S) (p + 1) (Set.mem_insert_of_mem p hp1)
    rw [Function.update_self, Function.update_self, hupd_a, hupd_b] at h1
    exact ⟨h1.1, (G.adj_comm _ _).trans (h1.2.trans (H.adj_comm _ _))⟩
  · intro h i hi j hj
    have hmem : ∀ r ∈ insert p S, r = p ∨ (r = p + 1 ∧ p + 1 ∈ S) := by
      intro r hr
      rcases fin_two_eq_or_add_one p r with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, (Set.mem_insert_iff.1 hr).resolve_left (fin_two_add_one_ne p)⟩
    rcases hmem i hi with rfl | ⟨rfl, hpSi⟩ <;> rcases hmem j hj with rfl | ⟨rfl, hpSj⟩
    · rw [Function.update_self, Function.update_self]
      exact ⟨iff_of_true rfl rfl, iff_of_false G.irrefl H.irrefl⟩
    · rw [Function.update_self, Function.update_self, hupd_a, hupd_b]
      exact ⟨(h hpSj).1, (G.adj_comm _ _).trans ((h hpSj).2.trans (H.adj_comm _ _))⟩
    · rw [Function.update_self, Function.update_self, hupd_a, hupd_b]
      exact ⟨eq_comm.trans ((h hpSi).1.trans eq_comm), (h hpSi).2⟩
    · rw [hupd_a, hupd_b]
      exact ⟨iff_of_true rfl rfl, iff_of_false G.irrefl H.irrefl⟩

/-! ### Bijective `2`-pebble game and color refinement -/

variable [Fintype V] [Fintype W] [G.LocallyFinite] [H.LocallyFinite]

/-- **Bijective `2`-pebble game and color refinement.** For every round count `m` and placed-pebble
set `S : Set (Fin 2)`, Duplicator wins the `m`-round bijective `2`-pebble game on two finite
simple graphs from `(S, a, b)` if and only if the placed pebbles form a partial isomorphism, each
placed pebble has the same round-`m` color in `G` and `H`, and the color histograms agree in every
round `< m`. -/
theorem bijPebbleWins_graph_iff (m : ℕ) (S : Set (Fin 2)) (a : Fin 2 → V) (b : Fin 2 → W) :
    (letI := G.structure; letI := H.structure; BijPebbleWins Language.graph m S a b) ↔
      (letI := G.structure; letI := H.structure; PartialIsoOn Language.graph S a b) ∧
        (∀ j ∈ S, G.refinementColoring (fun _ => ()) m (a j) =
          H.refinementColoring (fun _ => ()) m (b j)) ∧
        ∀ k < m, G.colorHistogram (fun _ => ()) k = H.colorHistogram (fun _ => ()) k := by
  induction m generalizing S a b with
  | zero =>
    let := G.structure
    let := H.structure
    rw [bijPebbleWins_zero]
    exact ⟨fun h => ⟨h, fun _ _ => rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩, fun h => h.1⟩
  | succ m ih =>
    have hhead : (letI := G.structure; letI := H.structure
        BijPebbleWins Language.graph (m + 1) S a b) ↔
        (letI := G.structure; letI := H.structure; PartialIsoOn Language.graph S a b) ∧
          ∀ p : Fin 2, ∃ f : V ≃ W, ∀ c,
            (letI := G.structure; letI := H.structure
              BijPebbleWins Language.graph m (insert p S)
                (Function.update a p c) (Function.update b p (f c))) := by
      let := G.structure
      let := H.structure
      exact bijPebbleWins_succ
    rw [hhead]
    refine and_congr Iff.rfl ?_
    have hmove : ∀ p : Fin 2,
        (∃ f : V ≃ W, ∀ c,
          (letI := G.structure; letI := H.structure
            BijPebbleWins Language.graph m (insert p S)
              (Function.update a p c) (Function.update b p (f c)))) ↔
          (p + 1 ∈ S → G.refinementColoring (fun _ => ()) (m + 1) (a (p + 1)) =
              H.refinementColoring (fun _ => ()) (m + 1) (b (p + 1))) ∧
            G.colorHistogram (fun _ => ()) m = H.colorHistogram (fun _ => ()) m := by
      intro p
      simp only [ih, partialIsoOn_graph_insert_iff]
      have hupd_a : ∀ c, Function.update a p c (p + 1) = a (p + 1) := fun c =>
        Function.update_of_ne (fin_two_add_one_ne p) c a
      have hupd_b : ∀ d, Function.update b p d (p + 1) = b (p + 1) := fun d =>
        Function.update_of_ne (fin_two_add_one_ne p) d b
      by_cases hpS : p + 1 ∈ S
      · simp only [hpS, forall_const]
        have hstep : (∃ f : V ≃ W, ∀ c,
            ((c = a (p + 1) ↔ f c = b (p + 1)) ∧
              (G.Adj (a (p + 1)) c ↔ H.Adj (b (p + 1)) (f c))) ∧
            (∀ j ∈ insert p S,
              G.refinementColoring (fun _ => ()) m (Function.update a p c j) =
                H.refinementColoring (fun _ => ()) m (Function.update b p (f c) j)) ∧
            ∀ k < m, G.colorHistogram (fun _ => ()) k = H.colorHistogram (fun _ => ()) k) ↔
            ∃ f : V ≃ W, ∀ c,
              (c = a (p + 1) ↔ f c = b (p + 1)) ∧
              (G.Adj (a (p + 1)) c ↔ H.Adj (b (p + 1)) (f c)) ∧
              G.refinementColoring (fun _ => ()) m c =
                H.refinementColoring (fun _ => ()) m (f c) := by
          constructor
          · rintro ⟨f, hf⟩
            refine ⟨f, fun c => ⟨(hf c).1.1, (hf c).1.2, ?_⟩⟩
            have hpc := (hf c).2.1 p (Set.mem_insert p S)
            rwa [Function.update_self, Function.update_self] at hpc
          · rintro ⟨f, hf⟩
            have hhist : G.colorHistogram (fun _ => ()) m = H.colorHistogram (fun _ => ()) m := by
              rw [colorHistogram_eq, colorHistogram_eq]
              exact Equiv.exists_apply_eq_iff_map_univ_eq.1 ⟨f, fun c => ((hf c).2.2).symm⟩
            have hcol_q : G.refinementColoring (fun _ => ()) m (a (p + 1)) =
                H.refinementColoring (fun _ => ()) m (b (p + 1)) := by
              have hfa : f (a (p + 1)) = b (p + 1) := (hf (a (p + 1))).1.1 rfl
              have hca := (hf (a (p + 1))).2.2
              rwa [hfa] at hca
            refine ⟨f, fun c => ⟨⟨(hf c).1, (hf c).2.1⟩, fun j _ => ?_,
              fun k hk => colorHistogram_eq_of_le hk.le hhist⟩⟩
            rcases fin_two_eq_or_add_one p j with rfl | rfl
            · rw [Function.update_self, Function.update_self]
              exact (hf c).2.2
            · rw [hupd_a, hupd_b]
              exact hcol_q
        rw [hstep, exists_equiv_adj_iff_refineColoring_eq, ← refinementColoring_succ,
          ← refinementColoring_succ, ← colorHistogram_eq, ← colorHistogram_eq]
        exact Iff.rfl
      · simp only [hpS, IsEmpty.forall_iff, true_and]
        have hins : insert p S = {p} := by
          ext r
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases fin_two_eq_or_add_one p r with rfl | rfl
          · simp
          · simp [fin_two_add_one_ne p, hpS]
        rw [hins]
        simp only [Set.mem_singleton_iff, forall_eq, Function.update_self]
        constructor
        · rintro ⟨f, hf⟩
          rw [colorHistogram_eq, colorHistogram_eq]
          exact Equiv.exists_apply_eq_iff_map_univ_eq.1 ⟨f, fun c => ((hf c).1).symm⟩
        · intro hhist
          have hmap := hhist
          rw [colorHistogram_eq, colorHistogram_eq] at hmap
          obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmap
          exact ⟨f, fun c => ⟨(hf c).symm, fun k hk => colorHistogram_eq_of_le hk.le hhist⟩⟩
    simp only [hmove]
    constructor
    · intro h
      have hhist := (h 0).2
      refine ⟨fun j hj => ?_, fun k hk => colorHistogram_eq_of_le (by omega) hhist⟩
      have hj' := (h (j + 1)).1
      rw [fin_two_add_one_add_one] at hj'
      exact hj' hj
    · rintro ⟨hcol, hhist⟩ p
      exact ⟨fun hpS => hcol (p + 1) hpS, hhist m (Nat.lt_succ_self m)⟩

/-- With no pebbles placed, Duplicator wins the `(n + 1)`-round bijective `2`-pebble game on two
finite simple graphs if and only if their round-`n` color histograms agree. -/
theorem bijPebbleWins_graph_empty_iff {n : ℕ} {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph (n + 1) ∅ a b) ↔
      G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [bijPebbleWins_graph_iff]
  have hemp : (letI := G.structure; letI := H.structure
      PartialIsoOn Language.graph ∅ a b) := by
    let := G.structure
    let := H.structure
    exact partialIsoOn_empty a b
  simp only [hemp, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, true_and]
  exact ⟨fun h => h n (Nat.lt_succ_self n), fun h k hk => colorHistogram_eq_of_le (by omega) h⟩

/-- With one pebble placed at index `i`, Duplicator wins the `(n + 1)`-round bijective `2`-pebble
game on two finite simple graphs if and only if `a i` and `b i` have the same round-`(n + 1)`
color and the round-`n` color histograms agree. -/
theorem bijPebbleWins_graph_singleton_iff {n : ℕ} {i : Fin 2} {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph (n + 1) {i} a b) ↔
      G.refinementColoring (fun _ => ()) (n + 1) (a i) =
          H.refinementColoring (fun _ => ()) (n + 1) (b i) ∧
        G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [bijPebbleWins_graph_iff]
  simp only [partialIsoOn_graph_singleton, Set.mem_singleton_iff, forall_eq, true_and]
  exact and_congr Iff.rfl
    ⟨fun h => h n (Nat.lt_succ_self n), fun h k hk => colorHistogram_eq_of_le (by omega) h⟩

/-- With both pebbles placed, Duplicator wins the `(n + 1)`-round bijective `2`-pebble game on two
finite simple graphs if and only if `(a, b)` is a partial isomorphism, each pebble has the same
round-`(n + 1)` color in `G` and `H`, and the round-`n` color histograms agree. -/
theorem bijPebbleWins_graph_univ_iff {n : ℕ} {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph (n + 1) Set.univ a b) ↔
      (letI := G.structure; letI := H.structure; PartialIso Language.graph a b) ∧
        (∀ j, G.refinementColoring (fun _ => ()) (n + 1) (a j) =
          H.refinementColoring (fun _ => ()) (n + 1) (b j)) ∧
        G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  rw [bijPebbleWins_graph_iff]
  have huniv : (letI := G.structure; letI := H.structure
      PartialIsoOn Language.graph Set.univ a b) ↔
      (letI := G.structure; letI := H.structure; PartialIso Language.graph a b) := by
    let := G.structure
    let := H.structure
    exact partialIsoOn_univ_iff
  rw [huniv]
  simp only [Set.mem_univ, forall_const]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    ⟨fun h => h n (Nat.lt_succ_self n), fun h k hk => colorHistogram_eq_of_le (by omega) h⟩)

/-- With no pebbles placed, Duplicator wins the infinite bijective `2`-pebble game on two finite
simple graphs if and only if their color histograms agree in every round. -/
theorem bijPebbleWinsForever_graph_empty_iff {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph ∅ a b) ↔
      ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  have hforever : (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph ∅ a b) ↔
      ∀ m, (letI := G.structure; letI := H.structure
        BijPebbleWins Language.graph m ∅ a b) := by
    let := G.structure
    let := H.structure
    exact bijPebbleWinsForever_iff_forall_bijPebbleWins
  rw [hforever]
  constructor
  · intro h n
    exact bijPebbleWins_graph_empty_iff.1 (h (n + 1))
  · intro h m
    cases m with
    | zero =>
      let := G.structure
      let := H.structure
      exact bijPebbleWins_zero.2 (partialIsoOn_empty a b)
    | succ n => exact bijPebbleWins_graph_empty_iff.2 (h n)

/-- With one pebble placed at index `i`, Duplicator wins the infinite bijective `2`-pebble game on
two finite simple graphs if and only if `a i` and `b i` receive the same color in every round and
the color histograms agree in every round. -/
theorem bijPebbleWinsForever_graph_singleton_iff {i : Fin 2} {a : Fin 2 → V} {b : Fin 2 → W} :
    (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph {i} a b) ↔
      (∀ n, G.refinementColoring (fun _ => ()) n (a i) =
          H.refinementColoring (fun _ => ()) n (b i)) ∧
        ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  have hforever : (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph {i} a b) ↔
      ∀ m, (letI := G.structure; letI := H.structure
        BijPebbleWins Language.graph m {i} a b) := by
    let := G.structure
    let := H.structure
    exact bijPebbleWinsForever_iff_forall_bijPebbleWins
  rw [hforever]
  constructor
  · intro h
    refine ⟨fun n => ?_, fun n => (bijPebbleWins_graph_singleton_iff.1 (h (n + 1))).2⟩
    cases n with
    | zero => rfl
    | succ n => exact (bijPebbleWins_graph_singleton_iff.1 (h (n + 1))).1
  · rintro ⟨hcol, hhist⟩ m
    cases m with
    | zero =>
      let := G.structure
      let := H.structure
      exact bijPebbleWins_zero.2 (partialIsoOn_graph_singleton i a b)
    | succ n => exact bijPebbleWins_graph_singleton_iff.2 ⟨hcol (n + 1), hhist n⟩

/-! ### The Immerman–Lander theorem (`C²` and color refinement) -/

/-- **Immerman–Lander theorem, bounded-rank vertex form** ([ImmermanLander1990];
[CaiFurerImmerman1992], Section 5, Theorem 5.2). Two vertices `v` of `G` and `w` of `H` satisfy the
same `C²` formulas of quantifier rank at most `n + 1` in the single free variable `xᵢ` if and only
if `v` and `w` have the same round-`(n + 1)` color and `G` and `H` have the same round-`n` color
histogram. -/
theorem forall_realize_countingFormula_singleton_le_iff {n : ℕ} {i : Fin 2} {v : V} {w : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      φ.quantifierRank ≤ n + 1 → ↑φ.freeVars ⊆ ({i} : Set (Fin 2)) →
        ((letI := G.structure; φ.Realize (fun _ => v)) ↔
          (letI := H.structure; φ.Realize (fun _ => w)))) ↔
      G.refinementColoring (fun _ => ()) (n + 1) v =
          H.refinementColoring (fun _ => ()) (n + 1) w ∧
        G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  have hgame : (letI := G.structure; letI := H.structure
      BijPebbleWins Language.graph (n + 1) {i} (fun _ => v) (fun _ => w)) ↔
      ∀ φ : FiniteVariable.CountingFormula Language.graph 2,
        φ.quantifierRank ≤ n + 1 → ↑φ.freeVars ⊆ ({i} : Set (Fin 2)) →
          ((letI := G.structure; φ.Realize (fun _ => v)) ↔
            (letI := H.structure; φ.Realize (fun _ => w))) := by
    let := G.structure
    let := H.structure
    exact bijPebbleWins_iff_forall_realize_iff
  rw [← hgame, bijPebbleWins_graph_singleton_iff]

/-- **Immerman–Lander theorem, vertex form** ([ImmermanLander1990]; [CaiFurerImmerman1992],
Section 5, Theorem 5.2). Two vertices `v` of `G` and `w` of `H` satisfy the same `C²` formulas in
the single free variable `xᵢ` if and only if `v` and `w` receive the same color in every round of
color refinement and `G` and `H` have the same color histogram in every round. -/
theorem forall_realize_countingFormula_singleton_iff {i : Fin 2} {v : V} {w : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      ↑φ.freeVars ⊆ ({i} : Set (Fin 2)) →
        ((letI := G.structure; φ.Realize (fun _ => v)) ↔
          (letI := H.structure; φ.Realize (fun _ => w)))) ↔
      (∀ n, G.refinementColoring (fun _ => ()) n v =
          H.refinementColoring (fun _ => ()) n w) ∧
        ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  have hgame : (letI := G.structure; letI := H.structure
      BijPebbleWinsForever Language.graph {i} (fun _ => v) (fun _ => w)) ↔
      ∀ φ : FiniteVariable.CountingFormula Language.graph 2,
        ↑φ.freeVars ⊆ ({i} : Set (Fin 2)) →
          ((letI := G.structure; φ.Realize (fun _ => v)) ↔
            (letI := H.structure; φ.Realize (fun _ => w))) := by
    let := G.structure
    let := H.structure
    exact bijPebbleWinsForever_iff_forall_realize_iff
  rw [← hgame, bijPebbleWinsForever_graph_singleton_iff]

/-- **Immerman–Lander theorem, stabilized vertex form.** Two vertices `v` of `G` and `w` of `H`
satisfy the same `C²` formulas in `xᵢ` if and only if their colors and the graphs' color histograms
agree in round `|V| + |W|`. -/
theorem forall_realize_countingFormula_singleton_iff_card_add_card {i : Fin 2} {v : V} {w : W} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      ↑φ.freeVars ⊆ ({i} : Set (Fin 2)) →
        ((letI := G.structure; φ.Realize (fun _ => v)) ↔
          (letI := H.structure; φ.Realize (fun _ => w)))) ↔
      G.refinementColoring (fun _ => ()) (Fintype.card V + Fintype.card W) v =
          H.refinementColoring (fun _ => ()) (Fintype.card V + Fintype.card W) w ∧
        G.colorHistogram (fun _ => ()) (Fintype.card V + Fintype.card W) =
          H.colorHistogram (fun _ => ()) (Fintype.card V + Fintype.card W) := by
  rw [forall_realize_countingFormula_singleton_iff, forall_refinementColoring_eq_iff,
    forall_colorHistogram_eq_iff]

/-- If `G` and `H` have the same round-`n` color histogram, then they agree on every `C²` sentence
of quantifier rank at most `n + 1` under any assignments. -/
theorem realize_countingFormula_iff_of_colorHistogram_eq {n : ℕ}
    (h : G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n)
    {φ : FiniteVariable.CountingFormula Language.graph 2}
    (hr : φ.quantifierRank ≤ n + 1) (hφ : φ.freeVars = ∅) (a : Fin 2 → V) (b : Fin 2 → W) :
    (letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b) := by
  have hwin := bijPebbleWins_graph_empty_iff (a := a) (b := b) |>.2 h
  let := G.structure
  let := H.structure
  exact hwin.realize_iff hr (by simp only [hφ, Finset.coe_empty, Set.empty_subset])

/-- **Immerman–Lander theorem, bounded-rank sentence form** ([ImmermanLander1990];
[CaiFurerImmerman1992], Section 5, Theorem 5.2). Two nonempty finite simple graphs satisfy the same
`C²` sentences of quantifier rank at most `n + 1` if and only if their round-`n` color histograms
agree. Nonemptiness is needed because `CountingFormula.Realize` takes a total assignment
`Fin 2 → V`, making universal quantification over assignments vacuous when `V` or `W` is empty. -/
theorem forall_realize_countingFormula_empty_le_iff [Nonempty V] [Nonempty W] {n : ℕ} :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      φ.quantifierRank ≤ n + 1 → φ.freeVars = ∅ →
        ∀ (a : Fin 2 → V) (b : Fin 2 → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) ↔
      G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  constructor
  · intro h
    obtain ⟨v₀⟩ := ‹Nonempty V›
    obtain ⟨w₀⟩ := ‹Nonempty W›
    let a : Fin 2 → V := fun _ => v₀
    let b : Fin 2 → W := fun _ => w₀
    refine (bijPebbleWins_graph_empty_iff (a := a) (b := b)).1 ?_
    let := G.structure
    let := H.structure
    exact bijPebbleWins_of_forall_realize_iff fun φ hr hS =>
      h φ hr (Finset.coe_eq_empty.1 (Set.Subset.antisymm hS (Set.empty_subset _))) a b
  · exact fun h φ hr hφ a b => realize_countingFormula_iff_of_colorHistogram_eq h hr hφ a b

/-- **Immerman–Lander theorem, sentence form** ([ImmermanLander1990]; [CaiFurerImmerman1992],
Section 5, Theorem 5.2; [Immerman1999], Section 12.5). Two nonempty finite simple graphs satisfy
the same `C²` sentences if and only if their color histograms agree in every round of color
refinement. -/
theorem forall_realize_countingFormula_empty_iff [Nonempty V] [Nonempty W] :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      φ.freeVars = ∅ →
        ∀ (a : Fin 2 → V) (b : Fin 2 → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) ↔
      ∀ n, G.colorHistogram (fun _ => ()) n = H.colorHistogram (fun _ => ()) n := by
  constructor
  · intro h n
    exact forall_realize_countingFormula_empty_le_iff.1 (fun φ _ hφ => h φ hφ)
  · intro h φ hφ a b
    exact realize_countingFormula_iff_of_colorHistogram_eq (h φ.quantifierRank)
      (Nat.le_succ _) hφ a b

/-- **Immerman–Lander theorem, stabilized sentence form.** Two nonempty finite simple graphs
satisfy the same `C²` sentences if and only if their color histograms agree in round `|V| + |W|`. -/
theorem forall_realize_countingFormula_empty_iff_card_add_card [Nonempty V] [Nonempty W] :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      φ.freeVars = ∅ →
        ∀ (a : Fin 2 → V) (b : Fin 2 → W),
          ((letI := G.structure; φ.Realize a) ↔ (letI := H.structure; φ.Realize b))) ↔
      G.colorHistogram (fun _ => ()) (Fintype.card V + Fintype.card W) =
        H.colorHistogram (fun _ => ()) (Fintype.card V + Fintype.card W) := by
  rw [forall_realize_countingFormula_empty_iff, forall_colorHistogram_eq_iff]

end GraphPebble

end Cslib.Logic.FO
