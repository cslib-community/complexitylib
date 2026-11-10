/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.LabelCover
public import CslibFrontier.Computability.PCP.Encoded.ParallelEdges
public import CslibFrontier.Computability.PCP.ParallelRepetition
import CslibFrontier.Computability.PCP.Encoded.Count
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Parallel repetition of Label Cover instances

The `k`-fold parallel repetition of a Label Cover instance `g` with left labels `β` and right
labels `γ` has left labels `Fin k → β` and right labels `Fin k → γ`. Its edges are the `k`-tuples
of edges of `g`. The tuple `e` goes from the tuple of the left ends of its entries to the tuple of
their right ends, numbered by iterated `Nat.pair` (`tupleCode`). It carries the projection
that applies the projection of `e i` in each coordinate `i`. A labelling satisfies it when it
satisfies all the coordinates at once. This is the repetition `V^ℓ` of a two-query projection
verifier [Arora and Barak, Definition 19.1][AroraBarak07]; repetition keeps the projection
property, as noted in Section 19.4 of the same draft.

A Label Cover instance with at least one edge is a two-prover game (`LabelCoverRepetition.game`):
the verifier picks a uniformly random edge and asks its left end of the first prover and its right
end of the second. When the instance has no parallel edges
(`Cslib.PCP.Encoded.Graph.NoParallelEdges`), the edge is determined by its two ends, and the
verifier accepts when the answers satisfy it. The value of the
game is at most the value of the instance (`value_game_le`), and the value of its `k`-fold
repetition is at least the value of the repeated instance (`one_sub_unsatVal_pow_le_value_pow`).
Holenstein's parallel repetition theorem (`Cslib.PCP.TwoProverGame.value_pow_le_of_value_le`)
then bounds the value of the repeated instance.

**Scope.** This is the parallel repetition theorem of Raz [Raz1998] for Label Cover instances
without parallel edges, in the explicit form of Holenstein [Holenstein2009]. The constants are
explicit but astronomically large: an instance of value at most `1 - ε` repeats to value at most
`(1 - ε³ / 6000)^{k / log₂ (|β| |γ|)}`. The absence of parallel edges is a limit of this proof
route, which reads the instance as the game of a uniformly random edge: parallel edges with
different projections need not give a game of the same value as the instance. Parallel edges
with equal projections do.

## Main definitions

* `Cslib.PCP.Encoded.LabelCoverRepetition.tupleCode`: iterated `Nat.pair` of tuples.
* `Cslib.PCP.Encoded.LabelCoverRepetition.tuples`: the `k`-tuples of the entries of a list.
* `Cslib.PCP.Encoded.LabelCoverRepetition.pow`: the `k`-fold parallel repetition of an instance.
* `Cslib.PCP.Encoded.LabelCoverRepetition.game`: the two-prover game of an instance.

## Main results

* `Cslib.PCP.Encoded.LabelCoverRepetition.satisfiable_pow`: repetition keeps satisfiability.
* `Cslib.PCP.Encoded.LabelCoverRepetition.value_game_le`: the game is no easier than the instance.
* `Cslib.PCP.Encoded.LabelCoverRepetition.one_sub_unsatVal_pow_le_value_pow`: without parallel
  edges, the repeated game is no harder than the repeated instance.
* `Cslib.PCP.Encoded.LabelCoverRepetition.one_sub_unsatVal_pow_le`: **parallel repetition for
  Label Cover without parallel edges**, with Holenstein's bound.

## References

* [R. Raz, *A parallel repetition theorem*][Raz1998]
* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft,
  Sections 19.1 and 19.4][AroraBarak07]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.LabelCoverRepetition

open Cslib.Complexity Finset

/-! ### Tuples -/

/-- The number of a `k`-tuple of natural numbers, by iterated `Nat.pair`: the empty tuple is
`0`, and `Fin.cons a t` is `Nat.pair a (tupleCode t)`. Since `Nat.pair a b < (max a b + 1)²`,
the number of a tuple of entries below `n` is below `n ^ (2 ^ k)` (`tupleCode_lt_pow`):
polynomial in `n` for fixed `k`, of degree exponential in `k`. -/
def tupleCode : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, t => Nat.pair (t 0) (tupleCode k (Fin.tail t))

/-- The tuple with a given number, inverting `tupleCode`. -/
def tupleDecode : (k : ℕ) → ℕ → Fin k → ℕ
  | 0, _ => Fin.elim0
  | k + 1, n => Fin.cons (Nat.unpair n).1 (tupleDecode k (Nat.unpair n).2)

/-- Decoding inverts the numbering of tuples. -/
@[simp]
theorem tupleDecode_tupleCode : ∀ (k : ℕ) (t : Fin k → ℕ), tupleDecode k (tupleCode k t) = t
  | 0, t => funext fun i => i.elim0
  | k + 1, t => by
    rw [tupleCode, tupleDecode, Nat.unpair_pair, tupleDecode_tupleCode k]
    exact Fin.cons_self_tail t

/-- The numbering of tuples is injective. -/
theorem tupleCode_injective (k : ℕ) : Function.Injective (tupleCode k) :=
  Function.LeftInverse.injective (tupleDecode_tupleCode k)

/-- The numbering of tuples is monotone in every coordinate. -/
theorem tupleCode_mono : ∀ (k : ℕ) {s t : Fin k → ℕ}, (∀ i, s i ≤ t i) →
    tupleCode k s ≤ tupleCode k t
  | 0, _, _, _ => le_rfl
  | k + 1, s, t, h => by
    have hl : StrictMono fun a => Nat.pair a (tupleCode k (Fin.tail s)) :=
      fun _ _ hab => Nat.pair_lt_pair_left _ hab
    have hr : StrictMono fun b => Nat.pair (t 0) b := fun _ _ hab => Nat.pair_lt_pair_right _ hab
    exact (hl.monotone (h 0)).trans (hr.monotone (tupleCode_mono k fun i => h i.succ))

/-- The number of a `k`-tuple of entries below `n` is below `n ^ (2 ^ k)`. -/
theorem tupleCode_lt_pow : ∀ (k : ℕ) {n : ℕ} {t : Fin k → ℕ}, 0 < n → (∀ i, t i < n) →
    tupleCode k t < n ^ (2 ^ k)
  | 0, n, _, hn, _ => by simpa [tupleCode] using hn
  | k + 1, n, t, hn, h => by
    have ht : t 0 < n ^ (2 ^ k) :=
      (h 0).trans_le (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)) n)
    have hc := tupleCode_lt_pow k hn fun i => h i.succ
    calc tupleCode (k + 1) t < (max (t 0) (tupleCode k (Fin.tail t)) + 1) ^ 2 :=
          Nat.pair_lt_max_add_one_sq _ _
      _ ≤ (n ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt (max_lt ht hc)) 2
      _ = n ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

/-- The `k`-tuples of entries of a list, in lexicographic order. -/
def tuples {α : Type*} : (k : ℕ) → List α → List (Fin k → α)
  | 0, _ => [Fin.elim0]
  | k + 1, l => l.flatMap fun a => (tuples k l).map (Fin.cons a)

/-- A list of length `m` has `m ^ k` tuples of length `k`. -/
@[simp]
theorem length_tuples {α : Type*} (l : List α) : ∀ k, (tuples k l).length = l.length ^ k
  | 0 => rfl
  | k + 1 => by
    simp [tuples, List.length_flatMap, length_tuples l k, List.map_const', List.sum_replicate,
      pow_succ, Nat.mul_comm]

/-- Counting tuples by a predicate counts tuples of positions in the list. -/
theorem countP_tuples {α : Type*} (l : List α) :
    ∀ (k : ℕ) (p : (Fin k → α) → Bool),
      (tuples k l).countP p = #{t : Fin k → Fin l.length | p (fun i => l.get (t i)) = true}
  | 0, p => by
    have h (t : Fin 0 → Fin l.length) : p (fun i => l.get (t i)) = p Fin.elim0 :=
      congrArg p (Subsingleton.elim _ _)
    rw [filter_congr (q := fun _ => p Fin.elim0 = true) fun t _ => by rw [h t]]
    by_cases hp : p Fin.elim0 = true <;> simp [tuples, hp]
  | k + 1, p => by
    have hstep (a : α) : ((tuples k l).map (Fin.cons a)).countP p =
        #{t : Fin k → Fin l.length | p (Fin.cons a fun i => l.get (t i)) = true} := by
      rw [List.countP_map, countP_tuples l k]
      rfl
    rw [tuples, List.countP_flatMap, ← Fin.sum_univ_fun_getElem]
    simp only [Function.comp_apply, hstep]
    rw [card_eq_sum_ones, sum_filter, ← (Fin.consEquiv fun _ => Fin l.length).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [card_eq_sum_ones, sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h : (fun i => l.get ((Fin.consEquiv fun _ => Fin l.length) (a, t) i)) =
        Fin.cons l[a.1] fun i => l.get (t i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [h]

/-- The tuples of a list are exactly the tuples of its entries. -/
theorem mem_tuples {α : Type*} {l : List α} :
    ∀ {k : ℕ} {t : Fin k → α}, t ∈ tuples k l ↔ ∀ i, t i ∈ l
  | 0, t => by simpa [tuples] using Subsingleton.elim t Fin.elim0
  | k + 1, t => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, s, hs, rfl⟩ i
      refine Fin.cases ha (fun j => ?_) i
      simpa using mem_tuples.mp hs j
    · intro h
      exact ⟨t 0, h 0, Fin.tail t, mem_tuples.mpr fun j => h j.succ, Fin.cons_self_tail t⟩

/-! ### Repetition -/

variable {β γ : Type}

/-- The edge of the `k`-fold repetition given by a `k`-tuple `e` of edges: it joins the tuples
of their ends and applies the projection of `e i` in each coordinate `i`. -/
def repEdge {k : ℕ} (e : Fin k → Edge (β → γ)) : Edge ((Fin k → β) → Fin k → γ) :=
  ⟨tupleCode k fun i => (e i).src, tupleCode k fun i => (e i).dst,
    fun a i => (e i).constraint (a i)⟩

/-- The **`k`-fold parallel repetition** of a Label Cover instance: the left labels are the
`k`-tuples of left labels, the right labels the `k`-tuples of right labels, and the edges the
`k`-tuples of edges (`repEdge`). The vertex count bounds the numbers of tuples of declared
vertices; with `n` declared vertices it is at most `(n + 1) ^ (2 ^ k)` (`vertices_pow_le`). -/
def pow (k : ℕ) (g : Graph (β → γ)) : Graph ((Fin k → β) → Fin k → γ) :=
  ⟨tupleCode k (fun _ => g.vertices) + 1, (tuples k g.edges).map repEdge⟩

/-- The edges of the repetition are the repetitions of the tuples of edges. -/
theorem edges_pow (k : ℕ) (g : Graph (β → γ)) :
    (pow k g).edges = (tuples k g.edges).map repEdge := rfl

/-- The `k`-fold repetition of an instance with `n` declared vertices declares at most
`(n + 1) ^ (2 ^ k)` vertices: polynomial for fixed `k`, of degree exponential in `k`. -/
theorem vertices_pow_le (k : ℕ) (g : Graph (β → γ)) :
    (pow k g).vertices ≤ (g.vertices + 1) ^ (2 ^ k) :=
  Nat.succ_le_of_lt (tupleCode_lt_pow k (Nat.succ_pos _) fun _ => Nat.lt_succ_self _)

/-- The repetition has the `k`-th power of the number of edges. -/
@[simp]
theorem length_edges_pow (k : ℕ) (g : Graph (β → γ)) :
    (pow k g).edges.length = g.edges.length ^ k := by
  simp [pow]

/-- Prepend an edge to a repeated edge: the new first coordinate. -/
def consEdge {k : ℕ} (d : Edge (β → γ)) (e : Edge ((Fin k → β) → Fin k → γ)) :
    Edge ((Fin (k + 1) → β) → Fin (k + 1) → γ) :=
  ⟨Nat.pair d.src e.src, Nat.pair d.dst e.dst,
    fun a => Fin.cons (d.constraint (a 0)) (e.constraint (Fin.tail a))⟩

/-- Repeating a tuple with a first entry prepends that entry to the repetition of the rest. -/
theorem repEdge_cons {k : ℕ} (d : Edge (β → γ)) (e : Fin k → Edge (β → γ)) :
    repEdge (Fin.cons d e : Fin (k + 1) → Edge (β → γ)) = consEdge d (repEdge e) := by
  simp only [repEdge, consEdge, tupleCode, Fin.cons_zero]
  congr 1 with a i : 2
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

/-- The edges of the `(k + 1)`-fold repetition, by prepending each edge to each edge of the
`k`-fold repetition. -/
theorem edges_pow_succ (k : ℕ) (g : Graph (β → γ)) :
    (pow (k + 1) g).edges = g.edges.flatMap fun d => (pow k g).edges.map (consEdge d) := by
  simp only [edges_pow, tuples, List.map_flatMap, List.map_map]
  congr 1 with d : 1
  congr 1 with e : 1
  exact repEdge_cons d e

/-- The repetition of a well-formed instance is well formed: the numbers of tuples of declared
vertices are below its vertex count. -/
theorem wellFormed_pow (k : ℕ) {g : Graph (β → γ)} (hg : g.WellFormed) : (pow k g).WellFormed := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have hmem := mem_tuples.mp he
  exact ⟨Nat.lt_succ_of_le (tupleCode_mono k fun i => (hg _ (hmem i)).1.le),
    Nat.lt_succ_of_le (tupleCode_mono k fun i => (hg _ (hmem i)).2.le)⟩

variable [DecidableEq γ]

/-- **Repetition keeps satisfiability**: the labels of the tuples of vertices are the tuples of
the labels [Arora and Barak, Remark 19.2][AroraBarak07]. -/
theorem satisfiable_pow (k : ℕ) {g : Graph (β → γ)}
    (hg : (g.toGraph projectionEval).Satisfiable) :
    ((pow k g).toGraph projectionEval).Satisfiable := by
  obtain ⟨ℓ, r, h⟩ := (satisfiable_toGraph_projectionEval_iff g).mp hg
  refine (satisfiable_toGraph_projectionEval_iff _).mpr
    ⟨fun v i => ℓ (tupleDecode k v i), fun v i => r (tupleDecode k v i), fun d hd => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  funext i
  simp only [repEdge, tupleDecode_tupleCode]
  exact h _ (mem_tuples.mp he i)

/-! ### The game of an instance -/

/-- Some bound exceeds all the endpoints of a graph, whether or not it is well formed. -/
theorem _root_.Cslib.PCP.Encoded.Graph.exists_endpoint_bound {C : Type} (g : Graph C) :
    ∃ N, ∀ d ∈ g.edges, d.src < N ∧ d.dst < N := by
  refine ⟨(g.edges.map fun d => d.src + d.dst).sum + 1, fun d hd => ?_⟩
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun d : Edge C => d.src + d.dst) hd)
  constructor <;> omega

/-- The **two-prover game of a Label Cover instance** `g` with at least one edge, whose endpoints
lie below `N`: the verifier picks a uniformly random edge and asks its left end of the first prover
and its right end of the second. It accepts answers `a` and `b` when they satisfy every edge with
these two ends; when `g` has no parallel edges, this is the chosen edge. -/
noncomputable def game (g : Graph (β → γ)) (hg : g.edges ≠ []) (N : ℕ)
    (hN : ∀ d ∈ g.edges, d.src < N ∧ d.dst < N) : TwoProverGame (Fin N) (Fin N) β γ :=
  have : Nonempty (Fin g.edges.length) := ⟨⟨0, List.length_pos_iff.mpr hg⟩⟩
  { questions := (Probability.PMF.uniformOfFintype (Fin g.edges.length)).map fun i =>
      (⟨(g.edges.get i).src, (hN _ (List.get_mem _ _)).1⟩,
        ⟨(g.edges.get i).dst, (hN _ (List.get_mem _ _)).2⟩)
    accepts := fun x y a b => ∀ d ∈ g.edges, d.src = x → d.dst = y → d.constraint a = b }

omit [DecidableEq γ] in
/-- The proportion of edges that a labelling satisfies, as a number of edge indices. -/
private theorem one_sub_unsatFrac_eq {C α : Type} (g : Graph C) (hg : g.edges ≠ [])
    {eval : C → α → α → Bool} (σ : ℕ → α) [DecidablePred ((g.toGraph eval).Satisfies σ)] :
    1 - (g.toGraph eval).unsatFrac σ =
      #{i | (g.toGraph eval).Satisfies σ i} / g.edges.length := by
  have hlen : (g.edges.length : ℝ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr hg).ne'
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin g.edges.length)))
    ((g.toGraph eval).Satisfies σ)
  rw [card_univ, Fintype.card_fin] at hcard
  have hunsat : #((g.toGraph eval).unsatEdges σ) = #{i | ¬(g.toGraph eval).Satisfies σ i} := by
    congr 1
    ext i
    simp
  rw [ConstraintGraph.unsatFrac, hunsat, Fintype.card_fin]
  have hcard' : (#{i | (g.toGraph eval).Satisfies σ i} : ℝ) +
      #{i | ¬(g.toGraph eval).Satisfies σ i} = g.edges.length := by
    exact_mod_cast hcard
  field_simp
  linarith

omit [DecidableEq γ] in
/-- The proportion of edges that a labelling satisfies, as a count along the edge list. -/
private theorem one_sub_unsatFrac_toGraph {C α : Type} (g : Graph C) (hg : g.edges ≠ [])
    (eval : C → α → α → Bool) (σ : ℕ → α) :
    1 - (g.toGraph eval).unsatFrac σ =
      (g.edges.countP fun d => eval d.constraint (σ d.src) (σ d.dst)) / g.edges.length := by
  have hlen : (g.edges.length : ℝ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr hg).ne'
  have h := List.length_eq_countP_add_countP
    (fun d : Edge C => eval d.constraint (σ d.src) (σ d.dst)) (l := g.edges)
  have hneg : g.edges.countP (fun d => decide ¬(eval d.constraint (σ d.src) (σ d.dst) = true)) =
      g.edges.countP (fun d => !eval d.constraint (σ d.src) (σ d.dst)) := by
    simp
  rw [hneg] at h
  have h' : (g.edges.length : ℝ) =
      (g.edges.countP fun d => eval d.constraint (σ d.src) (σ d.dst)) +
        (g.edges.countP fun d => !eval d.constraint (σ d.src) (σ d.dst)) := by
    exact_mod_cast h
  rw [Graph.unsatFrac_toGraph]
  field_simp
  linarith

/-- **The game is no easier than the instance**: its value is at most the largest proportion of
the edges that a labelling satisfies. -/
theorem value_game_le [Nonempty β] [Nonempty γ] (g : Graph (β → γ))
    (hg : g.edges ≠ []) (N : ℕ) (hN : ∀ d ∈ g.edges, d.src < N ∧ d.dst < N) :
    (game g hg N hN).value ≤ 1 - (g.toGraph projectionEval).unsatVal := by
  classical
  refine ciSup_le fun ha => ciSup_le fun hb => ?_
  obtain ⟨b₀⟩ := ‹Nonempty β›
  obtain ⟨c₀⟩ := ‹Nonempty γ›
  let σ : ℕ → β × γ := fun v =>
    if h : v < N then (ha ⟨v, h⟩, hb ⟨v, h⟩) else (b₀, c₀)
  refine le_trans ?_ (sub_le_sub_left ((g.toGraph projectionEval).unsatVal_le σ) 1)
  have : Nonempty (Fin g.edges.length) := ⟨⟨0, List.length_pos_iff.mpr hg⟩⟩
  rw [one_sub_unsatFrac_eq _ hg, TwoProverGame.winProb, game, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card fun i hi => ?_))
    (Nat.cast_nonneg _)
  simp only [mem_filter, mem_univ, true_and, Set.mem_preimage, Set.mem_ofPred_eq] at hi ⊢
  have h := hi _ (List.get_mem _ _) rfl rfl
  have hs := (hN _ (List.get_mem g.edges i)).1
  have hd := (hN _ (List.get_mem g.edges i)).2
  change projectionEval (g.edges.get i).constraint (σ (g.edges.get i).src)
    (σ (g.edges.get i).dst) = true
  simp only [projectionEval, decide_eq_true_eq, σ, dite_eq_left hs, dite_eq_left hd]
  exact h

/-- **Without parallel edges, the repeated game is no harder than the repeated instance.** A
labelling of the tuples of vertices gives strategies that answer each tuple of questions by the
labels of its number; they win on every tuple of edges that the labelling satisfies. -/
theorem one_sub_unsatVal_pow_le_value_pow [Finite β] [Finite γ] [Nonempty β] [Nonempty γ]
    {g : Graph (β → γ)} (hpar : g.NoParallelEdges) (hg : g.edges ≠ []) (N : ℕ)
    (hN : ∀ d ∈ g.edges, d.src < N ∧ d.dst < N) (k : ℕ) :
    1 - ((pow k g).toGraph projectionEval).unsatVal ≤ ((game g hg N hN).pow k).value := by
  classical
  obtain ⟨τ, hτ⟩ := ((pow k g).toGraph projectionEval).exists_unsatFrac_eq_unsatVal
  rw [← hτ]
  let ha : (Fin k → Fin N) → Fin k → β := fun x => (τ (tupleCode k fun i => x i)).1
  let hb : (Fin k → Fin N) → Fin k → γ := fun y => (τ (tupleCode k fun i => y i)).2
  refine le_trans ?_ (((game g hg N hN).pow k).winProb_le_value ha hb)
  have : Nonempty (Fin g.edges.length) := ⟨⟨0, List.length_pos_iff.mpr hg⟩⟩
  have hpow : (pow k g).edges ≠ [] := by grind [length_edges_pow]
  have hq : ((game g hg N hN).pow k).questions =
      (Probability.PMF.uniformOfFintype (Fin k → Fin g.edges.length)).map fun t =>
        (fun i => (⟨(g.edges.get (t i)).src, (hN _ (List.get_mem _ _)).1⟩ : Fin N),
          fun i => (⟨(g.edges.get (t i)).dst, (hN _ (List.get_mem _ _)).2⟩ : Fin N)) := by
    simp only [TwoProverGame.pow, game]
    rw [Probability.PMF.pi_map, Probability.PMF.pi_uniformOfFintype, PMF.map_comp]
    rfl
  rw [one_sub_unsatFrac_toGraph _ hpow, length_edges_pow, edges_pow, List.countP_map,
    countP_tuples, TwoProverGame.winProb, hq, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  push_cast
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card fun t ht => ?_))
    (by positivity)
  have hsat := (mem_filter.mp ht).2
  simp only [mem_filter, mem_univ, true_and, Set.mem_preimage, Set.mem_ofPred_eq,
    TwoProverGame.pow, game]
  intro i d hd hsrc hdst
  obtain ⟨j, rfl⟩ := List.get_of_mem hd
  obtain rfl : j = t i := hpar.eq_of_src_eq_of_dst_eq hsrc hdst
  exact congrFun (of_decide_eq_true hsat) i

/-- **Parallel repetition for Label Cover without parallel edges** [Raz1998], with Holenstein's
bound [Holenstein, Theorem 2.5][Holenstein2009]: if every labelling of an instance `g` without
parallel edges violates at least the proportion `ε` of its edges, then every labelling of its
`k`-fold repetition satisfies at most the proportion `(1 - ε³ / 6000)^{k / log₂ (|β| |γ|)}` of the
edges. The constants are explicit but astronomically large. Instances with parallel edges are not
covered by this proof route. -/
theorem one_sub_unsatVal_pow_le [Fintype β] [Fintype γ] {g : Graph (β → γ)}
    (hpar : g.NoParallelEdges) (hβγ : 2 ≤ Fintype.card β * Fintype.card γ) {ε : ℝ}
    (hε : ε ≤ (g.toGraph projectionEval).unsatVal) (k : ℕ) :
    1 - ((pow k g).toGraph projectionEval).unsatVal ≤
      (1 - ε ^ 3 / 6000) ^ ((k : ℝ) / Real.logb 2 (Fintype.card β * Fintype.card γ)) := by
  have hβ : Nonempty β := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h => by simp_all)
  have hγ : Nonempty γ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h => by simp_all)
  have ht : 0 ≤ (k : ℝ) / Real.logb 2 (Fintype.card β * Fintype.card γ) :=
    div_nonneg k.cast_nonneg (Real.logb_nonneg one_lt_two (by exact_mod_cast (by omega : 1 ≤ _)))
  rcases eq_or_ne g.edges [] with hg | hg
  · have : IsEmpty (Fin g.edges.length) := ⟨fun i => by simpa [hg] using i.2⟩
    have h0 := (g.toGraph projectionEval).unsatVal_of_isEmpty
    have hε0 : ε ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) (hε.trans h0.le)
    refine le_trans ?_ (Real.one_le_rpow (by linarith) ht)
    linarith [((pow k g).toGraph projectionEval).unsatVal_nonneg]
  obtain ⟨N, hN⟩ := g.exists_endpoint_bound
  have hv : (game g hg N hN).value ≤ 1 - ε := (value_game_le g hg N hN).trans (by linarith)
  exact (one_sub_unsatVal_pow_le_value_pow hpar hg N hN k).trans
    ((game g hg N hN).value_pow_le_of_value_le hβγ hv k)

end Cslib.PCP.Encoded.LabelCoverRepetition
