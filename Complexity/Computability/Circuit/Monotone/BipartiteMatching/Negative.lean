/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.BipartiteMatching.Approximator
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Negative errors of matching approximators

The negative test inputs are the graphs of the `4 ^ n` two-colourings `c` of the `2 n` vertices,
whose edges join vertices of the same colour (`Cslib.Circuits.BipartiteMatching.ofColoring`). Such a
graph has a perfect matching only if both sides have equally many vertices of colour `true`, so at
most `C(2n, n) ≤ 4 ^ n / √(2n + 1)` of them have one
(`Cslib.Circuits.BipartiteMatching.card_filter_bipartitePerfectMatching_ofColoring_le`,
`Cslib.Circuits.BipartiteMatching.centralBinom_sq_mul_le`) [Jukna, Lemma 9.33][Jukna2012].

The events that edges lie in the graph are not independent, but they are along *fresh* edges.
Flipping the colour of a vertex outside the vertices `U ∪ V` on which an event depends toggles
every edge at that vertex and keeps the event, so an edge with an endpoint outside `U ∪ V` lies in
the graph for exactly half of the colourings in the event. So a matching of `d` edges, each with
an endpoint outside `U ∪ V`, lies in the graph for exactly a `2 ^ (-d)` fraction of them; with no
event, for `4 ^ n / 2 ^ d` colourings
(`Cslib.Circuits.BipartiteMatching.card_filter_contains_ofColoring_mul_two_pow`). This replaces
the linear algebra over `GF(2)` of [Jukna, Lemma 9.35][Jukna2012].

Intersecting families makes no negative errors; only closing does. One closure step adds a matching
`W` implied by `r` members `V i` of the family, and errs on `c` only when the graph contains `W` but
none of the `V i`. The petals `V i \ W` are then nonempty and pairwise disjoint. If `(q s) ^ 2 < r`,
we choose `q` of them greedily, each with no edge between the left and the right vertices touched
by those chosen before [Jukna, Lemma 9.36][Jukna2012]: after `k` choices at most `k s` vertices
are touched on each side, and the at most `(k s) ^ 2` edges between them lie in at most as many
petals. So the chosen petals
are fresh in turn, and a step errs on at most `(1 - 2 ^ (-s)) ^ q 4 ^ n` colourings
(`Cslib.Circuits.BipartiteMatching.card_filter_forall_not_contains_mul_le`)
[Jukna, Lemma 9.37][Jukna2012]. The closure takes at most as many steps as there are matchings
with at most `s` edges (`Cslib.ImplicationClosure.relatesInSteps_closure`).

## Main definitions

* `Cslib.Circuits.BipartiteMatching.Coloring`, `Cslib.Circuits.BipartiteMatching.ofColoring`: the
  two-colourings of the vertices and their graphs.
* `Cslib.Circuits.BipartiteMatching.Razborov.Negative.stepCap`,
  `Cslib.Circuits.BipartiteMatching.Razborov.Negative.errorCap`: the negative errors of one closure
  step and of a gate.
* `Cslib.Circuits.BipartiteMatching.Razborov.Negative.scheme`: the approximation scheme on the
  graphs of colourings.

## Main results

* `Cslib.Circuits.BipartiteMatching.card_filter_bipartitePerfectMatching_ofColoring_le`: at most
  `C(2n, n)` graphs of colourings have a perfect matching.
* `Cslib.Circuits.BipartiteMatching.centralBinom_sq_mul_le`: `C(2n, n) ^ 2 (2n + 1) ≤ 16 ^ n`.
* `Cslib.Circuits.BipartiteMatching.card_filter_contains_ofColoring_mul_two_pow`: a matching of `d`
  edges lies in the graphs of exactly `4 ^ n / 2 ^ d` colourings.
* `Cslib.Circuits.BipartiteMatching.card_filter_forall_not_contains_mul_le`: the graphs of at most
  `(1 - 2 ^ (-s)) ^ q 4 ^ n` colourings contain none of more than `(q s) ^ 2` pairwise disjoint
  nonempty matchings of at most `s` edges.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.BipartiteMatching

open Finset

variable {n s : ℕ}

/-! ### Graphs of colourings -/

/-- The two-colourings of the vertices of `K_{n,n}`: `inl u` is the left vertex `u` and `inr v` the
right vertex `v`. -/
abbrev Coloring (n : ℕ) : Type :=
  Fin n ⊕ Fin n → Bool

/-- The graph of a colouring: the left vertex `u` and the right vertex `v` are adjacent when they
have the same colour. -/
def ofColoring (c : Coloring n) : BitString (n * n) :=
  fun i => decide (c (.inl (finProdFinEquiv.symm i).1) = c (.inr (finProdFinEquiv.symm i).2))

/-- The edges of the graph of `c` join vertices of the same colour. -/
@[simp] theorem graph_ofColoring (c : Coloring n) (e : Fin n × Fin n) :
    graph (ofColoring c) e = decide (c (.inl e.1) = c (.inr e.2)) := by
  simp only [graph, ofColoring, Equiv.symm_apply_apply]

/-- The graph of `c` contains `E` when the endpoints of every edge of `E` have the same colour. -/
theorem contains_ofColoring_iff {c : Coloring n} {E : Finset (Fin n × Fin n)} :
    Contains (ofColoring c) E ↔ ∀ e ∈ E, c (.inl e.1) = c (.inr e.2) := by
  simp [Contains]

/-- There are `4 ^ n` colourings. -/
theorem card_coloring (n : ℕ) : Fintype.card (Coloring n) = 4 ^ n := by
  rw [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, ← two_mul, pow_mul]
  norm_num

/-- If the graph of a colouring has a perfect matching, both sides have equally many vertices of
colour `true`. -/
theorem card_filter_inl_eq_card_filter_inr {c : Coloring n}
    (h : bipartitePerfectMatching n (ofColoring c) = true) :
    #{u | c (.inl u) = true} = #{v | c (.inr v) = true} := by
  obtain ⟨σ, hσ⟩ := bipartitePerfectMatching_eq_true_iff.1 h
  have hc (u : Fin n) : c (.inl u) = c (.inr (σ u)) := by simpa using hσ u
  exact card_equiv σ fun u => by simp [hc]

/-- **Graphs of colourings with a perfect matching** [Jukna, Lemma 9.33][Jukna2012]. At most
`C(2n, n)` graphs of colourings have a perfect matching: such a colouring is determined by the
`n`-set of the left vertices of colour `true` and the right vertices of colour `false`. -/
theorem card_filter_bipartitePerfectMatching_ofColoring_le :
    #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = true} ≤ n.centralBinom := by
  let f : Coloring n → Finset (Fin n ⊕ Fin n) := fun c => univ.filter fun v => c v = v.isLeft
  have hf (c : Coloring n) : f c = (univ.filter fun u => c (.inl u) = true).disjSum
      (univ.filter fun v => c (.inr v) = false) := by
    ext (u | v) <;> simp [f]
  calc #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = true}
      ≤ #(powersetCard n (univ : Finset (Fin n ⊕ Fin n))) := by
        refine card_le_card_of_injOn f (fun c hc => ?_) fun c _ c' _ h => funext fun v => ?_
        · have h := card_filter_inl_eq_card_filter_inr (mem_filter.1 hc).2
          have hsplit := card_filter_add_card_filter_not (s := univ) fun v => c (.inr v) = true
          simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsplit
          rw [mem_coe, mem_powersetCard, hf, card_disjSum]
          exact ⟨subset_univ _, by omega⟩
        · have hv := congrArg (v ∈ ·) h
          simp only [f, mem_filter, mem_univ, true_and, eq_iff_iff] at hv
          revert hv
          cases c v <;> cases c' v <;> cases v.isLeft <;> decide
    _ = n.centralBinom := by
        rw [card_powersetCard, card_univ, Fintype.card_sum, Fintype.card_fin, ← two_mul,
          Nat.centralBinom_eq_two_mul_choose]

/-- `C(2n, n) ^ 2 (2n + 1) ≤ 16 ^ n`: the product of the ratios `(2k - 1) / (2k)` is at most
`1 / √(2n + 1)`. -/
theorem centralBinom_sq_mul_le (n : ℕ) : n.centralBinom ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    refine Nat.le_of_mul_le_mul_left (c := (n + 1) ^ 2) ?_ (by positivity)
    calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1))
        = ((n + 1) * (n + 1).centralBinom) ^ 2 * (2 * n + 3) := by ring
      _ = 4 * (2 * n + 1) * n.centralBinom ^ 2 * ((2 * n + 1) * (2 * n + 3)) := by rw [h]; ring
      _ ≤ 4 * (2 * n + 1) * n.centralBinom ^ 2 * (4 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = 16 * (n + 1) ^ 2 * (n.centralBinom ^ 2 * (2 * n + 1)) := by ring
      _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring

/-- If `4 ^ (s + 1) ≤ 2n + 1`, at most a `2 ^ (-(s + 1))` fraction of the graphs of colourings has a
perfect matching. -/
theorem card_filter_bipartitePerfectMatching_ofColoring_mul_le (hs : 4 ^ (s + 1) ≤ 2 * n + 1) :
    #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = true} * 2 ^ (s + 1) ≤ 4 ^ n := by
  refine (Nat.mul_le_mul_right _ card_filter_bipartitePerfectMatching_ofColoring_le).trans ?_
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  calc (n.centralBinom * 2 ^ (s + 1)) ^ 2 = n.centralBinom ^ 2 * 4 ^ (s + 1) := by
        rw [mul_pow, ← pow_mul, mul_comm (s + 1), pow_mul]
        norm_num
    _ ≤ n.centralBinom ^ 2 * (2 * n + 1) := Nat.mul_le_mul_left _ hs
    _ ≤ 16 ^ n := centralBinom_sq_mul_le n
    _ = (4 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-! ### Fresh edges -/

/-- A set of colourings determined by the colours of the left vertices in `U` and of the right
vertices in `V`. -/
private def Determined (U V : Finset (Fin n)) (S : Finset (Coloring n)) : Prop :=
  ∀ c c', (∀ u ∈ U, c (.inl u) = c' (.inl u)) → (∀ v ∈ V, c (.inr v) = c' (.inr v)) → c ∈ S →
    c' ∈ S

/-- Flip the colour of the vertex `w`. -/
private def flip (w : Fin n ⊕ Fin n) (c : Coloring n) : Coloring n :=
  Function.update c w (!c w)

private theorem flip_flip (w : Fin n ⊕ Fin n) (c : Coloring n) : flip w (flip w c) = c := by
  funext v
  by_cases hv : v = w
  · subst hv
    simp [flip]
  · simp [flip, Function.update_of_ne hv]

/-- An edge with an endpoint outside the vertices determining `S` lies in the graphs of exactly
half of the colourings in `S`: flipping that endpoint toggles the edge and keeps `S`. -/
private theorem two_mul_card_filter_edge {U V : Finset (Fin n)} {S : Finset (Coloring n)}
    (hS : Determined U V S) {e : Fin n × Fin n} (he : e.1 ∉ U ∨ e.2 ∉ V) :
    2 * #{c ∈ S | c (.inl e.1) = c (.inr e.2)} = #S := by
  obtain ⟨w, hwS, hw⟩ : ∃ w : Fin n ⊕ Fin n, (∀ c ∈ S, flip w c ∈ S) ∧
      ∀ c, (flip w c (.inl e.1) = flip w c (.inr e.2) ↔ ¬c (.inl e.1) = c (.inr e.2)) := by
    rcases he with he | he
    · refine ⟨.inl e.1, fun c hc => hS c _ (fun u hu => ?_) (fun v _ => ?_) hc, fun c => ?_⟩
      · have : u ≠ e.1 := fun h => he (h ▸ hu)
        simp [flip, this]
      · simp [flip]
      · have h1 : flip (.inl e.1) c (.inl e.1) = !c (.inl e.1) := by simp [flip]
        have h2 : flip (.inl e.1) c (.inr e.2) = c (.inr e.2) := by simp [flip]
        rw [h1, h2]
        cases c (.inl e.1) <;> cases c (.inr e.2) <;> decide
    · refine ⟨.inr e.2, fun c hc => hS c _ (fun u _ => ?_) (fun v hv => ?_) hc, fun c => ?_⟩
      · simp [flip]
      · have : v ≠ e.2 := fun h => he (h ▸ hv)
        simp [flip, this]
      · have h1 : flip (.inr e.2) c (.inl e.1) = c (.inl e.1) := by simp [flip]
        have h2 : flip (.inr e.2) c (.inr e.2) = !c (.inr e.2) := by simp [flip]
        rw [h1, h2]
        cases c (.inl e.1) <;> cases c (.inr e.2) <;> decide
  have hbij : #{c ∈ S | c (.inl e.1) = c (.inr e.2)} = #{c ∈ S | ¬c (.inl e.1) = c (.inr e.2)} :=
    card_nbij' (flip w) (flip w)
      (fun c hc => mem_filter.2 ⟨hwS c (mem_filter.1 hc).1, by
        rw [hw, not_not]; exact (mem_filter.1 hc).2⟩)
      (fun c hc => mem_filter.2 ⟨hwS c (mem_filter.1 hc).1, (hw c).2 (mem_filter.1 hc).2⟩)
      (fun c _ => flip_flip w c) fun c _ => flip_flip w c
  rw [two_mul]
  nth_rw 2 [hbij]
  exact card_filter_add_card_filter_not _

/-- Along a matching whose every edge has an endpoint outside the vertices determining `S`, the
matching lies in the graphs of exactly a `2 ^ (-#D)` fraction of the colourings in `S`. -/
private theorem card_filter_contains_mul_two_pow_of_determined {U V : Finset (Fin n)}
    {S : Finset (Coloring n)} (hS : Determined U V S) {D : Finset (Fin n × Fin n)}
    (hD : IsMatching D) (hfresh : ∀ e ∈ D, e.1 ∉ U ∨ e.2 ∉ V) :
    #{c ∈ S | Contains (ofColoring c) D} * 2 ^ D.card = #S := by
  induction D using Finset.induction_on with
  | empty => simp [Contains]
  | insert e D he ih =>
    have hD' := hD.mono (subset_insert e D)
    have ih' := ih hD' fun e' he' => hfresh e' (mem_insert_of_mem he')
    set S' := S.filter fun c => Contains (ofColoring c) D
    have hS' : Determined (U ∪ D.image Prod.fst) (V ∪ D.image Prod.snd) S' := by
      intro c c' hU hV hc
      refine mem_filter.2 ⟨hS c c' (fun u hu => hU u (mem_union_left _ hu))
        (fun v hv => hV v (mem_union_left _ hv)) (mem_filter.1 hc).1, ?_⟩
      have hcD := contains_ofColoring_iff.1 (mem_filter.1 hc).2
      refine contains_ofColoring_iff.2 fun e' he' => ?_
      rw [← hU _ (mem_union_right _ (mem_image_of_mem _ he')),
        ← hV _ (mem_union_right _ (mem_image_of_mem _ he'))]
      exact hcD e' he'
    have hne (e' : Fin n × Fin n) (he' : e' ∈ D) : e.1 ≠ e'.1 ∧ e.2 ≠ e'.2 := by
      have h := hD e (mem_insert_self e D) e' (mem_insert_of_mem he')
      exact ⟨fun h' => he (h (Or.inl h') ▸ he'), fun h' => he (h (Or.inr h') ▸ he')⟩
    have hfresh' : e.1 ∉ U ∪ D.image Prod.fst ∨ e.2 ∉ V ∪ D.image Prod.snd := by
      rcases hfresh e (mem_insert_self e D) with h | h
      · refine Or.inl fun h' => ?_
        rcases mem_union.1 h' with h' | h'
        · exact h h'
        · obtain ⟨e', he', heq⟩ := mem_image.1 h'
          exact (hne e' he').1 heq.symm
      · refine Or.inr fun h' => ?_
        rcases mem_union.1 h' with h' | h'
        · exact h h'
        · obtain ⟨e', he', heq⟩ := mem_image.1 h'
          exact (hne e' he').2 heq.symm
    have h2 := two_mul_card_filter_edge hS' hfresh'
    have hfilter : S.filter (fun c => Contains (ofColoring c) (insert e D)) =
        S'.filter fun c => c (.inl e.1) = c (.inr e.2) := by
      ext c
      simp only [S', mem_filter, contains_ofColoring_iff, mem_insert, forall_eq_or_imp]
      tauto
    rw [hfilter, card_insert_of_notMem he, pow_succ, ← ih', ← h2]
    ring

/-- A matching whose every edge has an endpoint outside the vertices determining `S` and which has
at most `s` edges misses the graphs of at most a `1 - 2 ^ (-s)` fraction of the colourings in
`S`. -/
private theorem card_filter_not_contains_mul_le {U V : Finset (Fin n)} {S : Finset (Coloring n)}
    (hS : Determined U V S) {D : Finset (Fin n × Fin n)} (hD : IsMatching D)
    (hfresh : ∀ e ∈ D, e.1 ∉ U ∨ e.2 ∉ V) (hDs : D.card ≤ s) :
    #{c ∈ S | ¬Contains (ofColoring c) D} * 2 ^ s ≤ (2 ^ s - 1) * #S := by
  have h := card_filter_contains_mul_two_pow_of_determined hS hD hfresh
  have hsplit := card_filter_add_card_filter_not (s := S) fun c => Contains (ofColoring c) D
  have hle : #S ≤ #{c ∈ S | Contains (ofColoring c) D} * 2 ^ s :=
    h ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos hDs)
  have hmul : #{c ∈ S | ¬Contains (ofColoring c) D} * 2 ^ s +
      #{c ∈ S | Contains (ofColoring c) D} * 2 ^ s = #S * 2 ^ s := by
    rw [← add_mul, add_comm, hsplit]
  rw [Nat.sub_one_mul, mul_comm (2 ^ s)]
  omega

/-- A matching of `d` edges lies in the graphs of exactly `4 ^ n / 2 ^ d` colourings. -/
theorem card_filter_contains_ofColoring_mul_two_pow {D : Finset (Fin n × Fin n)}
    (hD : IsMatching D) : #{c : Coloring n | Contains (ofColoring c) D} * 2 ^ D.card = 4 ^ n := by
  rw [← card_coloring, ← card_univ]
  exact card_filter_contains_mul_two_pow_of_determined (U := ∅) (V := ∅)
    (fun _ _ _ _ _ => mem_univ _) hD fun _ _ => Or.inl (notMem_empty _)

/-- Fewer than `(k s) ^ 2` of pairwise disjoint matchings have an edge between the at most `k s`
left vertices and `k s` right vertices touched by `k` matchings of at most `s` edges, so one of
more than `(k s) ^ 2` such matchings is fresh. -/
private theorem exists_fresh {𝒟 𝒞 : Finset (Finset (Fin n × Fin n))} (h𝒞 : 𝒞 ⊆ 𝒟)
    (hne : ∀ D ∈ 𝒟, D.Nonempty) (hcard : ∀ D ∈ 𝒟, D.card ≤ s)
    (hdisj : (𝒟 : Set (Finset (Fin n × Fin n))).PairwiseDisjoint id)
    (hlt : (𝒞.card * s) ^ 2 < 𝒟.card) :
    ∃ D ∈ 𝒟, D ∉ 𝒞 ∧ ∀ e ∈ D, e.1 ∉ 𝒞.biUnion (·.image Prod.fst) ∨
      e.2 ∉ 𝒞.biUnion (·.image Prod.snd) := by
  set U := 𝒞.biUnion (·.image Prod.fst)
  set V := 𝒞.biUnion (·.image Prod.snd)
  have hU : U.card ≤ 𝒞.card * s := card_biUnion_le_card_mul _ _ _ fun D hD =>
    card_image_le.trans (hcard D (h𝒞 hD))
  have hV : V.card ≤ 𝒞.card * s := card_biUnion_le_card_mul _ _ _ fun D hD =>
    card_image_le.trans (hcard D (h𝒞 hD))
  set B := 𝒟.filter fun D => ∃ e ∈ D, e.1 ∈ U ∧ e.2 ∈ V
  have hB : B.card ≤ (𝒞.card * s) ^ 2 := by
    have hsub : B.biUnion (fun D => D.filter fun e => e.1 ∈ U ∧ e.2 ∈ V) ⊆ U ×ˢ V := by
      intro e he
      obtain ⟨_, -, he⟩ := mem_biUnion.1 he
      exact mem_product.2 (mem_filter.1 he).2
    have hdisj' : (B : Set (Finset (Fin n × Fin n))).PairwiseDisjoint
        fun D => D.filter fun e => e.1 ∈ U ∧ e.2 ∈ V := fun D hD D' hD' hDD' =>
      disjoint_filter_filter (hdisj (filter_subset _ _ hD) (filter_subset _ _ hD') hDD')
    calc B.card = ∑ _D ∈ B, 1 := by simp
      _ ≤ ∑ D ∈ B, (D.filter fun e => e.1 ∈ U ∧ e.2 ∈ V).card := sum_le_sum fun D hD => by
          obtain ⟨e, he, heU⟩ := (mem_filter.1 hD).2
          exact card_pos.2 ⟨e, mem_filter.2 ⟨he, heU⟩⟩
      _ = (B.biUnion fun D => D.filter fun e => e.1 ∈ U ∧ e.2 ∈ V).card :=
          (card_biUnion hdisj').symm
      _ ≤ (U ×ˢ V).card := card_le_card hsub
      _ ≤ (𝒞.card * s) ^ 2 := by
          rw [card_product, sq]
          exact Nat.mul_le_mul hU hV
  obtain ⟨D, hD, hDB⟩ := exists_mem_notMem_of_card_lt_card (hB.trans_lt hlt)
  have hfresh : ∀ e ∈ D, e.1 ∉ U ∨ e.2 ∉ V := fun e he => by
    by_contra h
    push Not at h
    exact hDB (mem_filter.2 ⟨hD, e, he, h⟩)
  refine ⟨D, hD, fun hD𝒞 => ?_, hfresh⟩
  obtain ⟨e, he⟩ := hne D hD
  rcases hfresh e he with h | h
  · exact h (mem_biUnion.2 ⟨D, hD𝒞, mem_image_of_mem _ he⟩)
  · exact h (mem_biUnion.2 ⟨D, hD𝒞, mem_image_of_mem _ he⟩)

/-- **Many disjoint matchings are rarely all missed** [Jukna, proof of Lemma 9.37][Jukna2012]. If
`𝒟` is a family of more than `(q s) ^ 2` pairwise disjoint nonempty matchings with at most `s`
edges, the graphs of at most `(1 - 2 ^ (-s)) ^ q 4 ^ n` colourings contain none of them. -/
theorem card_filter_forall_not_contains_mul_le {𝒟 : Finset (Finset (Fin n × Fin n))}
    (hmatch : ∀ D ∈ 𝒟, IsMatching D) (hne : ∀ D ∈ 𝒟, D.Nonempty)
    (hcard : ∀ D ∈ 𝒟, D.card ≤ s) (hdisj : (𝒟 : Set (Finset (Fin n × Fin n))).PairwiseDisjoint id)
    {q : ℕ} (hq : (q * s) ^ 2 < 𝒟.card) :
    #{c : Coloring n | ∀ D ∈ 𝒟, ¬Contains (ofColoring c) D} * 2 ^ (s * q) ≤
      (2 ^ s - 1) ^ q * 4 ^ n := by
  suffices h : ∀ k ≤ q, ∃ 𝒞 ⊆ 𝒟, 𝒞.card = k ∧
      #{c : Coloring n | ∀ D ∈ 𝒞, ¬Contains (ofColoring c) D} * 2 ^ (s * k) ≤
        (2 ^ s - 1) ^ k * 4 ^ n by
    obtain ⟨𝒞, h𝒞, -, h⟩ := h q le_rfl
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun c hc => ?_)) h
    exact mem_filter.2 ⟨mem_univ _, fun D hD => (mem_filter.1 hc).2 D (h𝒞 hD)⟩
  intro k hk
  induction k with
  | zero =>
    refine ⟨∅, empty_subset _, rfl, ?_⟩
    rw [filter_true_of_mem fun c _ D hD => absurd hD (notMem_empty _), card_univ, card_coloring]
    simp
  | succ k ih =>
    obtain ⟨𝒞, h𝒞, hk𝒞, hcount⟩ := ih (by omega)
    obtain ⟨D, hD, hD𝒞, hfresh⟩ := exists_fresh h𝒞 hne hcard hdisj
      (lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2) hq)
    refine ⟨insert D 𝒞, insert_subset hD h𝒞, by rw [card_insert_of_notMem hD𝒞, hk𝒞], ?_⟩
    set S := univ.filter fun c : Coloring n => ∀ D ∈ 𝒞, ¬Contains (ofColoring c) D
    have hS : Determined (𝒞.biUnion (·.image Prod.fst)) (𝒞.biUnion (·.image Prod.snd)) S := by
      intro c c' hU hV hc
      refine mem_filter.2 ⟨mem_univ _, fun D' hD' hc' => (mem_filter.1 hc).2 D' hD' ?_⟩
      refine contains_ofColoring_iff.2 fun e he => ?_
      rw [hU _ (mem_biUnion.2 ⟨D', hD', mem_image_of_mem _ he⟩),
        hV _ (mem_biUnion.2 ⟨D', hD', mem_image_of_mem _ he⟩)]
      exact contains_ofColoring_iff.1 hc' e he
    have hfilter : univ.filter (fun c : Coloring n => ∀ D' ∈ insert D 𝒞,
        ¬Contains (ofColoring c) D') = S.filter fun c => ¬Contains (ofColoring c) D := by
      ext c
      simp only [S, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp]
      tauto
    have hstep := card_filter_not_contains_mul_le hS (hmatch D hD) hfresh (hcard D hD)
    rw [hfilter]
    calc #(S.filter fun c => ¬Contains (ofColoring c) D) * 2 ^ (s * (k + 1))
        = #(S.filter fun c => ¬Contains (ofColoring c) D) * 2 ^ s * 2 ^ (s * k) := by ring
      _ ≤ (2 ^ s - 1) * #S * 2 ^ (s * k) := Nat.mul_le_mul_right _ hstep
      _ = (2 ^ s - 1) * (#S * 2 ^ (s * k)) := by ring
      _ ≤ (2 ^ s - 1) * ((2 ^ s - 1) ^ k * 4 ^ n) := Nat.mul_le_mul_left _ hcount
      _ = (2 ^ s - 1) ^ (k + 1) * 4 ^ n := by ring

/-! ### Negative errors of closure steps -/

namespace Razborov.Negative

open Cslib.ImplicationClosure Approximator Relation
open Cslib.Circuits.Monotone (signature Op interpretation_mono)

variable {r q : ℕ}

/-- The colourings whose graphs `G` accepts and `F` rejects. -/
def stepExceptions (F G : Finset (Finset (Fin n × Fin n))) : Finset (Coloring n) :=
  univ.filter fun c => Accepts G (ofColoring c) ∧ ¬Accepts F (ofColoring c)

/-- A colouring belongs to `stepExceptions F G` when `G` accepts its graph and `F` rejects it. -/
@[simp] theorem mem_stepExceptions {F G : Finset (Finset (Fin n × Fin n))} {c : Coloring n} :
    c ∈ stepExceptions F G ↔ Accepts G (ofColoring c) ∧ ¬Accepts F (ofColoring c) := by
  simp [stepExceptions]

/-- The negative exceptions between `F` and `H` lie in those between `F` and `G` and those between
`G` and `H`. -/
theorem stepExceptions_subset (F G H : Finset (Finset (Fin n × Fin n))) :
    stepExceptions F H ⊆ stepExceptions F G ∪ stepExceptions G H := fun c hc => by
  obtain ⟨hH, hF⟩ := mem_stepExceptions.1 hc
  by_cases hG : Accepts G (ofColoring c)
  · exact mem_union_left _ (mem_stepExceptions.2 ⟨hG, hF⟩)
  · exact mem_union_right _ (mem_stepExceptions.2 ⟨hH, hG⟩)

/-- The number of negative errors charged to one closure step. -/
def stepCap (n s q : ℕ) : ℕ :=
  (2 ^ s - 1) ^ q * 4 ^ n / 2 ^ (s * q)

/-- If `(q s) ^ 2 < r`, one closure step of a family of matchings with at most `s` edges makes at
most `stepCap n s q` negative errors. -/
theorem card_stepExceptions_le_of_step {F G : Finset (Finset (Fin n × Fin n))}
    (hF : F ⊆ matchings n s) (h : Step r (matchings n s) F G) (hq : (q * s) ^ 2 < r) :
    (stepExceptions F G).card ≤ stepCap n s q := by
  obtain ⟨W, -, ⟨-, V, hV, hVW⟩, rfl⟩ := h
  rw [stepCap, Nat.le_div_iff_mul_le (by positivity)]
  have hexc (c : Coloring n) (hc : c ∈ stepExceptions F (insert W F)) :
      Contains (ofColoring c) W ∧ ∀ i, ¬Contains (ofColoring c) (V i) := by
    obtain ⟨⟨t, ht, hct⟩, hF'⟩ := mem_stepExceptions.1 hc
    rcases mem_insert.1 ht with rfl | ht
    · exact ⟨hct, fun i hi => hF' ⟨V i, hV i, hi⟩⟩
    · exact absurd ⟨t, ht, hct⟩ hF'
  by_cases hsub : ∃ i, V i ⊆ W
  · obtain ⟨i, hi⟩ := hsub
    refine (Nat.mul_le_mul_right _ (card_eq_zero.2 (eq_empty_of_forall_notMem fun c hc =>
      ?_)).le).trans (by simp)
    obtain ⟨hcW, hcV⟩ := hexc c hc
    exact hcV i (hcW.mono hi)
  push Not at hsub
  have hinter (i j : Fin r) (hij : i ≠ j) : (V i \ W) ∩ (V j \ W) = ∅ := by
    refine eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨⟨hei, heW⟩, ⟨hej, -⟩⟩ := (mem_inter.1 he).imp mem_sdiff.1 mem_sdiff.1
    exact heW (hVW i j hij (mem_inter.2 ⟨hei, hej⟩))
  have hinj : Function.Injective fun i => V i \ W := by
    intro i j hij
    by_contra hne
    have h := hinter i j hne
    rw [show V j \ W = V i \ W from hij.symm, inter_self, sdiff_eq_empty_iff_subset] at h
    exact hsub i h
  set 𝒟 := univ.image fun i => V i \ W
  have hcount := card_filter_forall_not_contains_mul_le (𝒟 := 𝒟) (s := s) (q := q)
    (fun D hD => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 hD
      exact (mem_matchings.1 (hF (hV i))).1.mono sdiff_subset)
    (fun D hD => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 hD
      exact sdiff_nonempty.2 (hsub i))
    (fun D hD => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 hD
      exact (card_le_card sdiff_subset).trans (mem_matchings.1 (hF (hV i))).2)
    (fun D hD D' hD' hDD' => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hD)
      obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hD')
      exact disjoint_iff_inter_eq_empty.2 (hinter i j fun hij => hDD' (hij ▸ rfl)))
    (by rwa [card_image_of_injective _ hinj, card_univ, Fintype.card_fin])
  refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun c hc => ?_)) hcount
  obtain ⟨hcW, hcV⟩ := hexc c hc
  refine mem_filter.2 ⟨mem_univ _, fun D hD hcD => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hD
  refine hcV i fun e he => ?_
  by_cases heW : e ∈ W
  · exact hcW e heW
  · exact hcD e (mem_sdiff.2 ⟨he, heW⟩)

/-- `m` closure steps make at most `m` times `stepCap n s q` negative errors. -/
theorem card_stepExceptions_le_of_relatesInSteps {F G : Finset (Finset (Fin n × Fin n))} {m : ℕ}
    (h : RelatesInSteps (Step r (matchings n s)) F G m) (hF : F ⊆ matchings n s)
    (hq : (q * s) ^ 2 < r) : (stepExceptions F G).card ≤ m * stepCap n s q := by
  induction h with
  | refl => simp [stepExceptions]
  | tail G H m hFG hGH ih =>
    calc (stepExceptions F H).card
        ≤ (stepExceptions F G ∪ stepExceptions G H).card :=
          card_le_card (stepExceptions_subset F G H)
      _ ≤ m * stepCap n s q + stepCap n s q :=
          (card_union_le _ _).trans (Nat.add_le_add ih (card_stepExceptions_le_of_step
            (subset_of_relatesInSteps_of_subset hFG hF) hGH hq))
      _ = (m + 1) * stepCap n s q := (Nat.succ_mul _ _).symm

/-- The number of negative errors charged to any gate. -/
def errorCap (n s q : ℕ) : ℕ :=
  (matchings n s).card * stepCap n s q

/-- If `(q s) ^ 2 < r`, closing a family of matchings with at most `s` edges makes at most
`errorCap n s q` negative errors. -/
theorem card_stepExceptions_closure_le {F : Finset (Finset (Fin n × Fin n))}
    (hF : F ⊆ matchings n s) (hq : (q * s) ^ 2 < r) :
    (stepExceptions F (closure r (matchings n s) F)).card ≤ errorCap n s q :=
  let ⟨_, hm, h⟩ := relatesInSteps_closure (r := r) (P := matchings n s) F
  (card_stepExceptions_le_of_relatesInSteps h hF hq).trans (Nat.mul_le_mul_right _ hm)

/-- Only disjunctions make negative errors. -/
def errorCost (n s q : ℕ) : Op → ℕ
  | .or => errorCap n s q
  | _ => 0

/-- The negative errors of a gate: for a disjunction, those of closing the union of the families of
its arguments. -/
noncomputable def exceptions : (op : Op) → (Fin (signature.Arity op) → Approximator n r s) →
    Finset (Coloring n)
  | .or, A => stepExceptions ((A 0).terms ∪ (A 1).terms)
      (closure r (matchings n s) ((A 0).terms ∪ (A 1).terms))
  | _, _ => ∅

/-- If `(q s) ^ 2 < r`, the number of negative exceptions at an `op` gate is at most
`errorCost n s q op`. -/
theorem card_exceptions_le (hq : (q * s) ^ 2 < r) (op : Op)
    (A : Fin (signature.Arity op) → Approximator n r s) :
    (exceptions op A).card ≤ errorCost n s q op := by
  cases op with
  | or =>
    exact card_stepExceptions_closure_le
      (union_subset (A 0).subset_matchings (A 1).subset_matchings) hq
  | const | and => simp [exceptions]

variable [Fact (2 ≤ r)]

/-- Away from its exceptions, a gate is negatively correct on the graphs of colourings. -/
theorem gate_correct (op : Op) (A : Fin (signature.Arity op) → Approximator n r s)
    (c : Coloring n) (hc : c ∉ exceptions op A) :
    (Approximator.interpretation op A).decode (ofColoring c) ≤
      Monotone.interpretation op fun i => (A i).decode (ofColoring c) := by
  rw [Bool.le_iff_imp]
  intro h
  cases op with
  | const b => simpa using h
  | and =>
    rw [decode_eq_true, terms_interpretation_and] at h
    obtain ⟨W, hW, hcW⟩ := h
    rw [Monotone.interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true]
    exact ⟨⟨W, (mem_inter.1 hW).1, hcW⟩, ⟨W, (mem_inter.1 hW).2, hcW⟩⟩
  | or =>
    rw [decode_eq_true, terms_interpretation_or] at h
    have hG : Accepts ((A 0).terms ∪ (A 1).terms) (ofColoring c) :=
      not_not.1 fun hG => hc (mem_stepExceptions.2 ⟨h, hG⟩)
    obtain ⟨W, hW, hcW⟩ := hG
    rw [Monotone.interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true]
    rcases mem_union.1 hW with hW | hW
    · exact Or.inl ⟨W, hW, hcW⟩
    · exact Or.inr ⟨W, hW, hcW⟩

/-- **Negative errors.** If `(q s) ^ 2 < r`, the approximation scheme on the graphs of colourings:
the approximate value is at most the exact one away from the errors of closing. -/
noncomputable def scheme (hs : 1 ≤ s) (hq : (q * s) ^ 2 < r) :
    Approximation.Scheme Monotone.interpretation
      (Approximator.interpretation (n := n) (r := r) (s := s))
      (fun (A : Approximator n r s) (c : Coloring n) => A.decode (ofColoring c))
      ofColoring Approximator.input where
  relation u v := v ≤ u
  relation_trans h h' := h'.trans h
  map_relation op _ _ h := interpretation_mono op h
  errorCost := errorCost n s q
  exceptions := exceptions
  input_correct c i := by rw [decode_input hs]
  gate_correct := gate_correct
  exceptions_card_le := card_exceptions_le hq

end Razborov.Negative

end Cslib.Circuits.BipartiteMatching
