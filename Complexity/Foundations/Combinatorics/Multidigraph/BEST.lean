/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Multidigraph.Arborescence
import Mathlib.Data.Fintype.List
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Permutation

/-!
# The BEST theorem

An *Eulerian circuit* of a finite multidigraph `src tgt : E → V` is a closed walk that uses every
arc exactly once. Fixing the arc `e₀` with which it starts, it is a duplicate-free list of all the
arcs, starting with `e₀`, in which each arc ends where the next one starts and the last one ends
where `e₀` starts (`Cslib.Multidigraph.IsEulerianCircuit`). Every Eulerian circuit is a rotation of
exactly one that starts with `e₀`, so these are the Eulerian circuits counted up to rotation.

The **BEST theorem** (named after de Bruijn, van Aardenne-Ehrenfest, Smith and Tutte; the result
is due to van Aardenne-Ehrenfest and de Bruijn [vanAardenneEhrenfestDeBruijn1951], while Smith and
Tutte [SmithTutte1941] counted a special class) counts them. If every vertex has as many outgoing as
incoming arcs and at least one outgoing arc, the number of Eulerian circuits starting with `e₀` is
`τ * ∏ v, (d⁺ v - 1)!`, where `τ` is the number of spanning in-arborescences rooted at the source
of `e₀` and `d⁺ v` is the number of arcs out of `v` (`Cslib.Multidigraph.natCard_isEulerianCircuit`;
[Stanley2013], Theorem 10.2). With the directed matrix-tree theorem, `τ` is the determinant of the
reduced Laplacian (`Cslib.Multidigraph.natCard_isEulerianCircuit_eq_det_mul`; [Stanley2013],
Corollary 10.5). The source assumes a connected balanced digraph. Connected and balanced with at
least one arc implies that every vertex has an outgoing arc, so the hypotheses here are weaker:
connectivity is not assumed, and a multidigraph that is not connected and in which every vertex
has an outgoing arc has neither Eulerian circuits nor spanning arborescences. Conversely, a
multidigraph with an Eulerian circuit is balanced
(`Cslib.Multidigraph.IsEulerianCircuit.card_filter_src_eq`).

The proof sorts the arcs out of each vertex `v` in the order in which a circuit uses them. For
`v ≠ r = src e₀` the last of these arcs is the *last exit* from `v`, and the last exits form a
spanning in-arborescence rooted at `r`: the last arc of the circuit leaving a set of vertices that
never reach `r` would have to end inside that set. The orders determine the circuit, since the
next arc is always the first unused arc out of the current vertex. Conversely, any orders that
start with `e₀` at `r` and end with the arc of a fixed arborescence everywhere else are realized:
the walk that always takes the next arc in the order can stop only at `r` once all arcs out of `r`
are used, by the balance, and then every arc is used, because the set of vertices with unused arcs
is closed under following the arborescence and avoids `r`. There are `(d⁺ v - 1)!` such orders at
each vertex.

## Main definitions

* `Cslib.Multidigraph.IsEulerianCircuit`: Eulerian circuits starting with a given arc.

## Main results

* `Cslib.Multidigraph.natCard_isEulerianCircuit`: **the BEST theorem**.
* `Cslib.Multidigraph.natCard_isEulerianCircuit_eq_det_mul`: the BEST theorem with the number of
  arborescences given by the directed matrix-tree theorem.
* `Cslib.Multidigraph.IsEulerianCircuit.card_filter_src_eq`: a multidigraph with an Eulerian
  circuit is balanced.

## References

* [R. P. Stanley, *Topics in Algebraic Combinatorics*][Stanley2013], Chapter 10: Theorem 10.2
  and Corollary 10.5, with the last-exit proof followed here.
* [T. van Aardenne-Ehrenfest, N. G. de Bruijn, *Circuits and trees in oriented linear
  graphs*][vanAardenneEhrenfestDeBruijn1951] (Theorem 5a, according to [Stanley2013]; the primary
  source was not inspected)
* [C. A. B. Smith, W. T. Tutte, *On unicursal paths in a network of degree 4*][SmithTutte1941]
-/

public section

open Finset

namespace Cslib.Multidigraph

variable {V E : Type*} (src tgt : E → V)

/-- `l` is an **Eulerian circuit** of the multidigraph `src tgt : E → V` starting with the arc
`e₀`: a list of all the arcs, each exactly once, starting with `e₀`, in which each arc ends where
the next one starts and the last arc ends where `e₀` starts. -/
structure IsEulerianCircuit (e₀ : E) (l : List E) : Prop where
  /-- No arc is used twice. -/
  nodup : l.Nodup
  /-- Every arc is used. -/
  mem : ∀ e, e ∈ l
  /-- The circuit starts with `e₀`. -/
  head : l.head? = some e₀
  /-- Each arc ends where the next one starts. -/
  isChain : l.IsChain fun a b => tgt a = src b
  /-- The last arc ends where `e₀` starts. -/
  getLast : ∀ e ∈ l.getLast?, tgt e = src e₀

/-! ### Lists -/

/-- A list with an element satisfying `P` splits at the last such element. -/
private theorem exists_split_last {α : Type*} (P : α → Prop) :
    ∀ l : List α, (∃ a ∈ l, P a) → ∃ p a q, l = p ++ a :: q ∧ P a ∧ ∀ b ∈ q, ¬ P b
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | x :: l, h => by
    by_cases hl : ∃ a ∈ l, P a
    · obtain ⟨p, a, q, rfl, ha, hq⟩ := exists_split_last P l hl
      exact ⟨x :: p, a, q, rfl, ha, hq⟩
    · push Not at hl
      obtain ⟨a, ha, hPa⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨[], a, l, rfl, hPa, hl⟩
      · exact absurd hPa (hl a ha)

/-- A proper prefix of a duplicate-free list does not contain its last element. -/
private theorem not_mem_of_prefix_of_length_lt {α : Type*} {q s : List α} {x : α}
    (hpre : q <+: s) (hlt : q.length < s.length) (hs : s.Nodup) (hx : s.getLast? = some x) :
    x ∉ q := by
  obtain ⟨t, rfl⟩ := hpre
  have ht : t ≠ [] := by
    rintro rfl
    simp at hlt
  have hxt : x ∈ t := by
    rw [List.getLast?_append, List.getLast?_eq_some_getLast ht] at hx
    simp only [Option.some_or, Option.some.injEq] at hx
    exact hx ▸ List.getLast_mem ht
  exact fun hxq => List.disjoint_of_nodup_append hs hxq hxt

/-- A list is duplicate-free if its sublists of elements with a fixed value of `g` are. -/
private theorem nodup_of_nodup_filter {α β : Type*} [DecidableEq β] (g : α → β) :
    ∀ {l : List α}, (∀ b, (l.filter fun a => g a = b).Nodup) → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_of_nodup_filter g fun b => ?_⟩
    · have := h (g x)
      rw [List.filter_cons_of_pos (by simp)] at this
      exact (List.nodup_cons.mp this).1 (List.mem_filter.mpr ⟨hx, by simp⟩)
    · have := h b
      by_cases hb : g x = b
      · rw [List.filter_cons_of_pos (by simpa using hb)] at this
        exact (List.nodup_cons.mp this).2
      · rwa [List.filter_cons_of_neg (by simpa using hb)] at this

/-! ### Counting orders -/

/-- There are `#s!` orders of a finite set `s`. -/
private theorem natCard_nodup_mem {α : Type*} (s : Finset α) :
    Nat.card {l : List α // l.Nodup ∧ ∀ e, e ∈ l ↔ e ∈ s} = s.card.factorial := by
  classical
  have hiff : ∀ l : List α,
      (l.Nodup ∧ ∀ e, e ∈ l ↔ e ∈ s) ↔ l ∈ s.toList.permutations.toFinset := by
    intro l
    rw [List.mem_toFinset, List.mem_permutations]
    constructor
    · rintro ⟨hl, hmem⟩
      exact (List.perm_ext_iff_of_nodup hl s.nodup_toList).mpr fun e => by simp [hmem]
    · intro hp
      exact ⟨hp.nodup_iff.mpr s.nodup_toList, fun e => by simp [hp.mem_iff]⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_coe, List.toFinset_card_of_nodup (List.nodup_permutations _ s.nodup_toList),
    List.length_permutations, Finset.length_toList]

/-- There are `(#s - 1)!` orders of a finite set `s` that start with a given `x ∈ s`. -/
private theorem natCard_nodup_mem_head {α : Type*} {s : Finset α} {x : α} (hx : x ∈ s) :
    Nat.card {l : List α // l.Nodup ∧ (∀ e, e ∈ l ↔ e ∈ s) ∧ l.head? = some x} =
      (s.card - 1).factorial := by
  classical
  rw [← Finset.card_erase_of_mem hx, ← natCard_nodup_mem (s.erase x)]
  have hcons : ∀ l : List α, l.head? = some x → l = x :: l.tail := fun l h =>
    List.eq_cons_of_mem_head? h
  refine Nat.card_congr
    { toFun := fun l => ⟨l.1.tail, ?_, ?_⟩
      invFun := fun t => ⟨x :: t.1, ?_, ?_, rfl⟩
      left_inv := fun l => Subtype.ext (hcons l.1 l.2.2.2).symm
      right_inv := fun t => rfl }
  · exact l.2.1.sublist (List.tail_sublist _)
  · intro e
    have hn := l.2.1
    have hm := l.2.2.1
    rw [hcons l.1 l.2.2.2] at hn hm
    rw [Finset.mem_erase, ← hm, List.mem_cons]
    constructor
    · intro he
      exact ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ he), Or.inr he⟩
    · rintro ⟨hne, rfl | he⟩
      · exact absurd rfl hne
      · exact he
  · refine List.nodup_cons.mpr ⟨fun h => ?_, t.2.1⟩
    simpa using (t.2.2 x).mp h
  · intro e
    rw [List.mem_cons, t.2.2, Finset.mem_erase]
    by_cases he : e = x
    · simp [he, hx]
    · simp [he]

/-- There are `(#s - 1)!` orders of a finite set `s` that end with a given `x ∈ s`. -/
private theorem natCard_nodup_mem_getLast {α : Type*} {s : Finset α} {x : α} (hx : x ∈ s) :
    Nat.card {l : List α // l.Nodup ∧ (∀ e, e ∈ l ↔ e ∈ s) ∧ l.getLast? = some x} =
      (s.card - 1).factorial := by
  rw [← natCard_nodup_mem_head hx]
  refine Nat.card_congr
    { toFun := fun l => ⟨l.1.reverse, ?_, ?_, ?_⟩
      invFun := fun l => ⟨l.1.reverse, ?_, ?_, ?_⟩
      left_inv := fun l => Subtype.ext (List.reverse_reverse _)
      right_inv := fun l => Subtype.ext (List.reverse_reverse _) }
  · exact List.nodup_reverse.mpr l.2.1
  · simpa using l.2.2.1
  · rw [List.head?_reverse]
    exact l.2.2.2
  · exact List.nodup_reverse.mpr l.2.1
  · simpa using l.2.2.1
  · rw [List.getLast?_reverse]
    exact l.2.2.2

/-! ### Walks -/

variable [DecidableEq V]

/-- Along a walk, the arcs out of `w`, plus one if the walk ends at `w`, are as many as the arcs
into `w`, plus one if the walk starts at `w`. -/
private theorem countP_src_add (w : V) :
    ∀ (e : E) (l : List E), (e :: l).IsChain (fun a b => tgt a = src b) →
      ∀ z ∈ (e :: l).getLast?,
        (e :: l).countP (fun a => decide (src a = w)) + (if tgt z = w then 1 else 0) =
          (e :: l).countP (fun a => decide (tgt a = w)) + (if src e = w then 1 else 0)
  | e, [], _, z, hz => by
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hz
    subst hz
    simp only [List.countP_singleton, decide_eq_true_eq]
    split_ifs <;> omega
  | e, e' :: l, h, z, hz => by
    rw [List.isChain_cons_cons] at h
    have ih := countP_src_add w e' l h.2 z (by simpa using hz)
    rw [List.countP_cons (l := e' :: l), List.countP_cons (l := e' :: l)]
    simp only [decide_eq_true_eq] at ih ⊢
    rw [h.1]
    split_ifs at ih ⊢ <;> omega

variable [Fintype E]

/-- The arcs of a duplicate-free list into `w` are at most the arcs into `w`. -/
private theorem countP_tgt_le {l : List E} (hl : l.Nodup) (w : V) :
    l.countP (fun a => decide (tgt a = w)) ≤ (univ.filter fun e => tgt e = w).card := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  exact Finset.card_le_card fun e he => by simp_all

/-- The arcs of a duplicate-free list into `w` are fewer than the arcs into `w` if one of them is
missing. -/
private theorem countP_tgt_lt {l : List E} (hl : l.Nodup) {e : E} (he : e ∉ l) :
    l.countP (fun a => decide (tgt a = tgt e)) < (univ.filter fun e' => tgt e' = tgt e).card := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  refine Finset.card_lt_card ⟨fun e' he' => by simp_all, fun h => he ?_⟩
  have := h (Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl⟩)
  simp only [List.mem_toFinset, List.mem_filter] at this
  exact this.1

variable {src tgt} in
/-- A multidigraph with an Eulerian circuit is balanced: every vertex has as many outgoing as
incoming arcs. This is the necessity half of [Stanley2013], Theorem 10.1. -/
theorem IsEulerianCircuit.card_filter_src_eq {e₀ : E} {l : List E}
    (hl : IsEulerianCircuit src tgt e₀ l) (v : V) :
    (univ.filter fun e => src e = v).card = (univ.filter fun e => tgt e = v).card := by
  classical
  obtain ⟨l', hl'⟩ : ∃ l', l = e₀ :: l' := ⟨l.tail, List.eq_cons_of_mem_head? hl.head⟩
  subst hl'
  obtain ⟨z, hz⟩ : ∃ z, (e₀ :: l').getLast? = some z :=
    Option.ne_none_iff_exists'.mp (by simp)
  have h := countP_src_add src tgt v e₀ l' hl.isChain z hz
  rw [hl.getLast z hz] at h
  have hcount : ∀ p : E → Prop, [DecidablePred p] →
      (e₀ :: l').countP (fun a => decide (p a)) = (univ.filter p).card := by
    intro p _
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.nodup.filter _)]
    congr 1
    ext e
    simpa using fun _ : p e => hl.mem e
  rw [hcount, hcount] at h
  omega

/-! ### Last exits -/

section LastExit

variable (e₀ : E)

/-- The last arc of `l` out of `v`, or `e₀` if there is none. -/
private def lastExit (l : List E) (v : V) : E :=
  ((l.filter fun e => src e = v).getLast?).getD e₀

omit [Fintype E] in
private theorem getLast?_filter_eq_lastExit {l : List E} (hl : ∀ e, e ∈ l) {v : V}
    (hv : ∃ e, src e = v) :
    (l.filter fun e => src e = v).getLast? = some (lastExit src e₀ l v) := by
  obtain ⟨e, he⟩ := hv
  have hne : l.filter (fun e => src e = v) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.mpr ⟨hl e, by simpa using he⟩)
  rw [lastExit, List.getLast?_eq_some_getLast hne, Option.getD_some]

omit [Fintype E] in
private theorem src_lastExit {l : List E} (hl : ∀ e, e ∈ l) {v : V} (hv : ∃ e, src e = v) :
    src (lastExit src e₀ l v) = v := by
  have := List.mem_of_getLast? (getLast?_filter_eq_lastExit src e₀ hl hv)
  simpa using (List.mem_filter.mp this).2

omit [Fintype E] in
/-- Following the last exits of an Eulerian circuit leads from every vertex to the source of its
first arc. -/
private theorem reachable_lastExit {l : List E} (hl : IsEulerianCircuit src tgt e₀ l)
    (hpos : ∀ v, ∃ e, src e = v) (v : V) :
    Relation.ReflTransGen
      (fun v w => ∃ h : v ≠ src e₀, tgt (lastExit src e₀ l (⟨v, h⟩ : {v // v ≠ src e₀})) = w)
      v (src e₀) := by
  by_contra hv
  set Rel := fun v w => ∃ h : v ≠ src e₀,
    tgt (lastExit src e₀ l (⟨v, h⟩ : {v // v ≠ src e₀})) = w with hRel
  obtain ⟨p, a, q, hl_eq, ha, hq⟩ := exists_split_last
    (fun e => ¬ Relation.ReflTransGen Rel (src e) (src e₀)) l
    (by
      obtain ⟨e, he⟩ := hpos v
      exact ⟨e, hl.mem e, he ▸ hv⟩)
  have hlast : lastExit src e₀ l (src a) = a := by
    have hfilter : l.filter (fun e => src e = src a) =
        p.filter (fun e => src e = src a) ++ [a] := by
      rw [hl_eq, List.filter_append, List.filter_cons_of_pos (by simp)]
      congr 2
      rw [List.filter_eq_nil_iff]
      intro b hb hba
      simp only [decide_eq_true_eq] at hba
      exact hq b hb (hba ▸ ha)
    rw [lastExit, hfilter, List.getLast?_append]
    simp
  have hsrc : src a ≠ src e₀ := fun h => ha (h ▸ Relation.ReflTransGen.refl)
  have htgt : ¬ Relation.ReflTransGen Rel (tgt a) (src e₀) := fun h =>
    ha (Relation.ReflTransGen.head ⟨hsrc, by simp only [hlast]⟩ h)
  rcases q with _ | ⟨b, q⟩
  · have hz : a ∈ l.getLast? := by simp [hl_eq]
    exact htgt (hl.getLast a hz ▸ Relation.ReflTransGen.refl)
  · have hab : tgt a = src b := by
      have := hl.isChain
      rw [hl_eq] at this
      exact (List.isChain_append_cons_cons.mp this).2.1
    exact hq b (by simp) (hab ▸ htgt)

omit [Fintype E] in
/-- The last exits of an Eulerian circuit form a spanning in-arborescence rooted at the source of
its first arc. -/
private theorem isInArborescence_lastExit {l : List E} (hl : IsEulerianCircuit src tgt e₀ l)
    (hpos : ∀ v, ∃ e, src e = v) :
    IsInArborescence src tgt (src e₀) fun v => lastExit src e₀ l v :=
  ⟨fun v => src_lastExit src e₀ hl.mem (hpos v), reachable_lastExit src tgt e₀ hl hpos⟩

end LastExit

/-! ### The circuit is determined by the orders of the arcs out of each vertex -/

omit [Fintype E] in
/-- Removing a common first element from two lists keeps their sublists of elements with a fixed
value of `g` equal. -/
private theorem filter_eq_of_cons {α β : Type*} [DecidableEq β] (g : α → β) {a : α}
    {l₁ l₂ : List α} (h : ∀ v, (a :: l₁).filter (fun e => g e = v) =
      (a :: l₂).filter (fun e => g e = v)) (v : β) :
    l₁.filter (fun e => g e = v) = l₂.filter (fun e => g e = v) := by
  have := h v
  by_cases hv : g a = v
  · rw [List.filter_cons_of_pos (by simpa using hv),
      List.filter_cons_of_pos (by simpa using hv)] at this
    exact List.cons_inj_right _ |>.mp this
  · rwa [List.filter_cons_of_neg (by simpa using hv),
      List.filter_cons_of_neg (by simpa using hv)] at this

omit [Fintype E] in
/-- Two walks continuing the same nonempty walk, with the same orders of the arcs out of each
vertex, are equal: the next arc is always the first unused arc out of the current vertex. -/
private theorem eq_of_filter_eq_of_isChain :
    ∀ (p l₁ l₂ : List E), p ≠ [] → (p ++ l₁).IsChain (fun a b => tgt a = src b) →
      (p ++ l₂).IsChain (fun a b => tgt a = src b) →
      (∀ v, l₁.filter (fun e => src e = v) = l₂.filter (fun e => src e = v)) → l₁ = l₂
  | _, [], [], _, _, _, _ => rfl
  | _, [], b :: _, _, _, _, h => by
    have := h (src b)
    rw [List.filter_cons_of_pos (by simp)] at this
    simp at this
  | _, a :: _, [], _, _, _, h => by
    have := h (src a)
    rw [List.filter_cons_of_pos (by simp)] at this
    simp at this
  | p, a :: l₁, b :: l₂, hp, h₁, h₂, h => by
    have e₁ := h₁.rel_getLast_head_of_append hp (List.cons_ne_nil a l₁)
    have e₂ := h₂.rel_getLast_head_of_append hp (List.cons_ne_nil b l₂)
    simp only [List.head_cons] at e₁ e₂
    have hba : src b = src a := e₂.symm.trans e₁
    have hab : a = b := by
      have := h (src a)
      rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_pos (by simpa using hba)] at this
      exact (List.cons.inj this).1
    subst hab
    congr 1
    refine eq_of_filter_eq_of_isChain (p ++ [a]) l₁ l₂ (by simp) ?_ ?_ (filter_eq_of_cons src h)
    · rwa [List.append_assoc, List.singleton_append]
    · rwa [List.append_assoc, List.singleton_append]

omit [Fintype E] in
/-- An Eulerian circuit is determined by the orders in which it uses the arcs out of each
vertex. -/
private theorem IsEulerianCircuit.eq_of_filter_eq {e₀ : E} {l₁ l₂ : List E}
    (h₁ : IsEulerianCircuit src tgt e₀ l₁) (h₂ : IsEulerianCircuit src tgt e₀ l₂)
    (h : ∀ v, l₁.filter (fun e => src e = v) = l₂.filter (fun e => src e = v)) : l₁ = l₂ := by
  obtain ⟨t₁, rfl⟩ : ∃ t, l₁ = e₀ :: t := ⟨_, List.eq_cons_of_mem_head? h₁.head⟩
  obtain ⟨t₂, rfl⟩ : ∃ t, l₂ = e₀ :: t := ⟨_, List.eq_cons_of_mem_head? h₂.head⟩
  congr 1
  exact eq_of_filter_eq_of_isChain src tgt [e₀] t₁ t₂ (by simp) h₁.isChain h₂.isChain
    (filter_eq_of_cons src h)

/-! ### Every admissible family of orders is realized -/

section Extend

variable {e₀ : E} {a : {v // v ≠ src e₀} → E}

/-- The walk that follows given orders of the arcs out of each vertex, extended as long as
possible, is an Eulerian circuit realizing the orders, provided the orders end with the arcs of a
spanning in-arborescence and the multidigraph is balanced. -/
private theorem exists_isEulerianCircuit_of_prefix
    (hbal : ∀ v, (univ.filter fun e => src e = v).card = (univ.filter fun e => tgt e = v).card)
    (ha : IsInArborescence src tgt (src e₀) a) (s : V → List E) (hs_nodup : ∀ v, (s v).Nodup)
    (hs_mem : ∀ v e, e ∈ s v ↔ src e = v)
    (hs_last : ∀ v : {v // v ≠ src e₀}, (s v).getLast? = some (a v))
    (p : List E) (hp_head : p.head? = some e₀) (hp_chain : p.IsChain fun a b => tgt a = src b)
    (hp_pre : ∀ v, p.filter (fun e => src e = v) <+: s v) :
    ∃ l, IsEulerianCircuit src tgt e₀ l ∧ ∀ v, l.filter (fun e => src e = v) = s v := by
  classical
  have hp_nodup : p.Nodup :=
    nodup_of_nodup_filter src fun v => (hs_nodup v).sublist (hp_pre v).sublist
  have hlen_s : ∀ v, (s v).length = (univ.filter fun e => src e = v).card := by
    intro v
    rw [← List.toFinset_card_of_nodup (hs_nodup v)]
    congr 1
    ext e
    simp [hs_mem]
  obtain ⟨z, hz⟩ : ∃ z, p.getLast? = some z := by
    rcases p with _ | ⟨e, p⟩
    · simp at hp_head
    · exact ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil e p)⟩
  by_cases hext : (p.filter fun e => src e = tgt z).length < (s (tgt z)).length
  · -- Extend the walk by the next arc out of `tgt z`.
    obtain ⟨t, ht⟩ := hp_pre (tgt z)
    rcases t with _ | ⟨b, t⟩
    · rw [List.append_nil] at ht
      rw [ht] at hext
      exact absurd hext (lt_irrefl _)
    have hbsrc : src b = tgt z := (hs_mem _ b).mp (ht ▸ by simp)
    have hfilter : ∀ v, (p ++ [b]).filter (fun e => src e = v) =
        p.filter (fun e => src e = v) ++ if src b = v then [b] else [] := by
      intro v
      rw [List.filter_append]
      by_cases hv : src b = v <;> simp [hv]
    have hpre' : ∀ v, (p ++ [b]).filter (fun e => src e = v) <+: s v := by
      intro v
      rw [hfilter]
      by_cases hv : src b = v
      · subst hv
        rw [ite_eq_left rfl, hbsrc]
        exact ⟨t, by rw [← ht, List.append_assoc, List.singleton_append]⟩
      · rw [ite_eq_right hv, List.append_nil]
        exact hp_pre v
    have hnodup' : (p ++ [b]).Nodup :=
      nodup_of_nodup_filter src fun v => (hs_nodup v).sublist (hpre' v).sublist
    have hle : (p ++ [b]).length ≤ Fintype.card E := hnodup'.length_le_card
    refine exists_isEulerianCircuit_of_prefix hbal ha s hs_nodup hs_mem hs_last (p ++ [b]) ?_ ?_
      hpre'
    · rw [List.head?_append, hp_head]
      rfl
    · refine hp_chain.append (List.isChain_singleton b) fun x hx y hy => ?_
      rw [hz, Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hx, ← hy, hbsrc]
  · -- The walk is stuck at `z`: all arcs out of `tgt z` are used.
    have hfull : p.filter (fun e => src e = tgt z) = s (tgt z) :=
      (hp_pre (tgt z)).eq_of_length (le_antisymm (hp_pre (tgt z)).length_le (not_lt.mp hext))
    obtain ⟨p', rfl⟩ : ∃ p', p = e₀ :: p' := ⟨_, List.eq_cons_of_mem_head? hp_head⟩
    have hcount := countP_src_add src tgt
    -- the walk ends at the root
    have hzr : tgt z = src e₀ := by
      by_contra hne
      have h := hcount (tgt z) e₀ p' hp_chain z hz
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hne)] at h
      have h1 : (e₀ :: p').countP (fun a => decide (src a = tgt z)) =
          (univ.filter fun e => src e = tgt z).card := by
        rw [List.countP_eq_length_filter, ← hlen_s, ← hfull]
      have h2 := countP_tgt_le tgt hp_nodup (tgt z)
      rw [h1, hbal] at h
      omega
    -- every arc out of every vertex is used
    have hall : ∀ v, (e₀ :: p').filter (fun e => src e = v) = s v := by
      by_contra hne
      push Not at hne
      obtain ⟨v₀, hv₀⟩ := hne
      let D : V → Prop := fun v =>
        ((e₀ :: p').filter fun e => src e = v).length < (s v).length
      have hD : ∀ v, ¬ D v → (e₀ :: p').filter (fun e => src e = v) = s v := fun v hv =>
        (hp_pre v).eq_of_length (le_antisymm (hp_pre v).length_le (not_lt.mp hv))
      have hDr : ¬ D (src e₀) := by
        intro h
        rw [← hzr] at h
        exact hext h
      have hDv₀ : D v₀ := by
        by_contra h
        exact hv₀ (hD v₀ h)
      -- `D` is closed under following the arborescence
      have hstep : ∀ v w, (∃ h : v ≠ src e₀, tgt (a ⟨v, h⟩) = w) → D v → D w := by
        rintro v w ⟨hv, rfl⟩ hDv
        have hnot : a ⟨v, hv⟩ ∉ e₀ :: p' := by
          intro hmem
          refine not_mem_of_prefix_of_length_lt (hp_pre v) hDv (hs_nodup v) (hs_last ⟨v, hv⟩) ?_
          exact List.mem_filter.mpr ⟨hmem, by simpa using ha.src_eq ⟨v, hv⟩⟩
        have hlt := countP_tgt_lt tgt hp_nodup hnot
        have h := hcount (tgt (a ⟨v, hv⟩)) e₀ p' hp_chain z hz
        have hsrc : (e₀ :: p').countP (fun e => decide (src e = tgt (a ⟨v, hv⟩))) =
            ((e₀ :: p').filter fun e => src e = tgt (a ⟨v, hv⟩)).length := by
          rw [List.countP_eq_length_filter]
        have hcard := hlen_s (tgt (a ⟨v, hv⟩))
        have hb := hbal (tgt (a ⟨v, hv⟩))
        rw [hzr] at h
        change ((e₀ :: p').filter fun e => src e = tgt (a ⟨v, hv⟩)).length <
          (s (tgt (a ⟨v, hv⟩))).length
        omega
      have hprop : ∀ v w, Relation.ReflTransGen
          (fun v w => ∃ h : v ≠ src e₀, tgt (a ⟨v, h⟩) = w) v w → D v → D w := by
        intro v w hvw
        induction hvw with
        | refl => exact id
        | tail _ hbc ih => exact fun h => hstep _ _ hbc (ih h)
      exact hDr (hprop v₀ _ (ha.reachable v₀) hDv₀)
    refine ⟨e₀ :: p', ⟨hp_nodup, fun e => ?_, hp_head, hp_chain, fun e he => ?_⟩, hall⟩
    · have : e ∈ s (src e) := (hs_mem _ e).mpr rfl
      rw [← hall] at this
      exact (List.mem_filter.mp this).1
    · rw [hz, Option.mem_def, Option.some.injEq] at he
      rw [← he, hzr]
termination_by Fintype.card E - p.length
decreasing_by
  simp only [List.length_append, List.length_singleton] at hle ⊢
  omega

/-- Orders of the arcs out of each vertex, starting with `e₀` at its source and ending with the
arcs of a spanning in-arborescence elsewhere, are realized by an Eulerian circuit. -/
private theorem exists_isEulerianCircuit
    (hbal : ∀ v, (univ.filter fun e => src e = v).card = (univ.filter fun e => tgt e = v).card)
    (ha : IsInArborescence src tgt (src e₀) a) (s : V → List E) (hs_nodup : ∀ v, (s v).Nodup)
    (hs_mem : ∀ v e, e ∈ s v ↔ src e = v) (hs_head : (s (src e₀)).head? = some e₀)
    (hs_last : ∀ v : {v // v ≠ src e₀}, (s v).getLast? = some (a v)) :
    ∃ l, IsEulerianCircuit src tgt e₀ l ∧ ∀ v, l.filter (fun e => src e = v) = s v := by
  refine exists_isEulerianCircuit_of_prefix src tgt hbal ha s hs_nodup hs_mem hs_last [e₀] rfl
    (List.isChain_singleton e₀) fun v => ?_
  by_cases hv : src e₀ = v
  · subst hv
    obtain ⟨t, ht⟩ : ∃ t, s (src e₀) = e₀ :: t := ⟨_, List.eq_cons_of_mem_head? hs_head⟩
    rw [ht]
    simp
  · simp [hv]

end Extend

/-! ### Counting -/

/-- The orders of the arcs out of `v` that start with `e₀` if `v` is the source of `e₀`, and
otherwise end with the arc `a v` of a spanning in-arborescence. -/
private def Fib (e₀ : E) (a : {v // v ≠ src e₀} → E) (v : V) (l : List E) : Prop :=
  l.Nodup ∧ (∀ e, e ∈ l ↔ src e = v) ∧
    if h : v = src e₀ then l.head? = some e₀ else l.getLast? = some (a ⟨v, h⟩)

omit [Fintype E] in
private theorem natCard_fib [Fintype E] {e₀ : E} {a : {v // v ≠ src e₀} → E}
    (ha : IsInArborescence src tgt (src e₀) a) (v : V) :
    Nat.card {l // Fib src e₀ a v l} = ((univ.filter fun e => src e = v).card - 1).factorial := by
  classical
  by_cases hv : v = src e₀
  · subst hv
    rw [← natCard_nodup_mem_head (s := univ.filter fun e => src e = src e₀) (x := e₀)
      (by simp)]
    unfold Fib
    simp
  · rw [← natCard_nodup_mem_getLast (s := univ.filter fun e => src e = v) (x := a ⟨v, hv⟩)
      (by simpa using ha.src_eq ⟨v, hv⟩)]
    unfold Fib
    simp [hv]

omit [Fintype E] in
private theorem fib_filter {e₀ : E} {l : List E} (hl : IsEulerianCircuit src tgt e₀ l)
    (hpos : ∀ v, ∃ e, src e = v) {a : {v // v ≠ src e₀} → E}
    (ha : a = fun v : {v // v ≠ src e₀} => lastExit src e₀ l v) (v : V) :
    Fib src e₀ a v (l.filter fun e => src e = v) := by
  refine ⟨hl.nodup.filter _, fun e => by simp [hl.mem e], ?_⟩
  split_ifs with hv
  · subst hv
    obtain ⟨t, ht⟩ : ∃ t, l = e₀ :: t := ⟨_, List.eq_cons_of_mem_head? hl.head⟩
    rw [ht, List.filter_cons_of_pos (by simp)]
    rfl
  · rw [ha]
    exact getLast?_filter_eq_lastExit src e₀ hl.mem (hpos v)

variable [Fintype V]

/-- **The BEST theorem** [vanAardenneEhrenfestDeBruijn1951] ([Stanley2013], Theorem 10.2). In a
finite multidigraph in which every vertex has as many outgoing as incoming arcs, and at least one
outgoing arc, the number of Eulerian circuits starting with the arc `e₀` is the number of spanning
in-arborescences rooted at the source of `e₀`, times `∏ v, (d⁺ v - 1)!`, where `d⁺ v` is the
number of arcs out of `v`. The source assumes a connected balanced digraph, which implies these
hypotheses; connectivity is not needed. -/
theorem natCard_isEulerianCircuit
    (hbal : ∀ v, (univ.filter fun e => src e = v).card = (univ.filter fun e => tgt e = v).card)
    (hpos : ∀ v, ∃ e, src e = v) (e₀ : E) :
    Nat.card {l : List E // IsEulerianCircuit src tgt e₀ l} =
      Nat.card {f : {v // v ≠ src e₀} → E // IsInArborescence src tgt (src e₀) f} *
        ∏ v, ((univ.filter fun e => src e = v).card - 1).factorial := by
  classical
  let Tour := {l : List E // IsEulerianCircuit src tgt e₀ l}
  let Arb := {f : {v // v ≠ src e₀} → E // IsInArborescence src tgt (src e₀) f}
  let φ : Tour → Arb := fun l =>
    ⟨fun v => lastExit src e₀ l.1 v, isInArborescence_lastExit src tgt e₀ l.2 hpos⟩
  have hfib : ∀ a : Arb, Nat.card {l // φ l = a} =
      ∏ v, ((univ.filter fun e => src e = v).card - 1).factorial := by
    intro a
    let Ψ : {l // φ l = a} → ((v : V) → {l // Fib src e₀ a.1 v l}) := fun l v =>
      ⟨l.1.1.filter fun e => src e = v,
        fib_filter src tgt l.1.2 hpos (congrArg Subtype.val l.2).symm v⟩
    rw [Nat.card_eq_of_bijective Ψ ⟨?_, ?_⟩, Nat.card_pi]
    · exact Finset.prod_congr rfl fun v _ => natCard_fib src tgt a.2 v
    · intro l₁ l₂ h
      have hv : ∀ v, l₁.1.1.filter (fun e => src e = v) = l₂.1.1.filter (fun e => src e = v) :=
        fun v => congrArg Subtype.val (congrFun h v)
      exact Subtype.ext (Subtype.ext (IsEulerianCircuit.eq_of_filter_eq src tgt l₁.1.2 l₂.1.2 hv))
    · intro g
      have hhead : ((g (src e₀)).1).head? = some e₀ := by
        have := (g (src e₀)).2.2.2
        rwa [dite_eq_left rfl] at this
      have hlast : ∀ v : {v // v ≠ src e₀}, ((g v).1).getLast? = some (a.1 v) := by
        intro v
        have := (g v).2.2.2
        rwa [dite_eq_right v.2] at this
      obtain ⟨l, hl, hls⟩ := exists_isEulerianCircuit src tgt hbal a.2 (fun v => (g v).1)
        (fun v => (g v).2.1) (fun v => (g v).2.2.1) hhead hlast
      have hφ : φ ⟨l, hl⟩ = a := by
        refine Subtype.ext (funext fun v => ?_)
        have h1 := getLast?_filter_eq_lastExit src e₀ hl.mem (hpos v)
        rw [hls, hlast v] at h1
        exact (Option.some.inj h1).symm
      exact ⟨⟨⟨l, hl⟩, hφ⟩, funext fun v => Subtype.ext (hls v)⟩
  have : Finite Tour :=
    Finite.of_injective (fun l : Tour => (⟨l.1, l.2.nodup⟩ : {l : List E // l.Nodup}))
      fun l₁ l₂ h => Subtype.ext (by simpa using h)
  change Nat.card Tour = Nat.card Arb * _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma,
    Finset.sum_congr rfl fun a _ => hfib a, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card]

/-- **The BEST theorem**, determinant form ([Stanley2013], Corollary 10.5). In a finite
multidigraph in which every vertex has as many outgoing as incoming arcs, and at least one
outgoing arc, the number of Eulerian circuits starting with the arc `e₀` is the determinant of the
reduced Laplacian of the arc-count matrix, with the row and column of the source of `e₀` deleted,
times `∏ v, (d⁺ v - 1)!`. -/
theorem natCard_isEulerianCircuit_eq_det_mul (R : Type*) [CommRing R]
    (hbal : ∀ v, (univ.filter fun e => src e = v).card = (univ.filter fun e => tgt e = v).card)
    (hpos : ∀ v, ∃ e, src e = v) (e₀ : E) :
    (Nat.card {l : List E // IsEulerianCircuit src tgt e₀ l} : R) =
      ((arcMatrix src tgt R).laplacian.submatrix (Subtype.val : {v // v ≠ src e₀} → V)
          Subtype.val).det *
        ∏ v, (((univ.filter fun e => src e = v).card - 1).factorial : R) := by
  rw [natCard_isEulerianCircuit src tgt hbal hpos, Nat.cast_mul, Nat.cast_prod,
    det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence]

end Cslib.Multidigraph
