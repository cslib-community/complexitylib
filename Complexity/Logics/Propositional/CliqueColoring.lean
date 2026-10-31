/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Complexity.Computability.Circuit.Clique
public import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Sort

/-!
# Clique and colouring formulas

Krajíček's formulas `Clique_{n,k}(p, q)` and `Color_{n,r}(p, r)` [Krajíček, Definition 7.1]
[Krajicek1997] share the variables `p` of the possible edges of a graph on `n` vertices, numbered
as the inputs of the clique function (`Cslib.Circuits.Clique.edgeEquiv`). The clique formula
(`Cslib.Logic.PL.CNF.clique`) has a variable `q (u, i)` for each `u : Fin k` and vertex `i`, read
as "the `u`-th member of the clique is `i`", and says that

* (1a) every member is some vertex (`Cslib.Logic.PL.CNF.cliqueMemberClause`),
* (1b) two members `u < v` are not the same vertex (`Cslib.Logic.PL.CNF.cliqueDistinctClause`),
* (1c) if members `u < v` are vertices `i ≠ j`, then `i` and `j` are adjacent
  (`Cslib.Logic.PL.CNF.cliqueEdgeClause`).

The colouring formula (`Cslib.Logic.PL.CNF.coloring`) has a variable `z (i, a)` for each vertex `i`
and colour `a : Fin r`, read as "`i` has colour `a`", and says that

* (2a) every vertex has a colour (`Cslib.Logic.PL.CNF.colorVertexClause`),
* (2b) no vertex has two colours `a < b` (`Cslib.Logic.PL.CNF.colorUniqueClause`),
* (2c) adjacent vertices do not have the same colour (`Cslib.Logic.PL.CNF.colorEdgeClause`).

Krajíček states (1c) for the unordered pair `{i, j}`; the clause is taken here for both orders of
`i` and `j`, as the reading of `Clique_{n,k}` as an injection onto a clique requires: were (1c)
taken only for `i < j`, the members assigned to vertices in decreasing order would satisfy every
clause (1c), whatever the graph. Clause (2c) is symmetric in `i` and `j` and is taken once for each
pair `i < j`.

An assignment of the edges extends to a model of the clique formula exactly when its graph has a
`k`-clique (`Cslib.Logic.PL.CNF.exists_eval_clique_iff`), and to a model of the colouring formula
exactly when its graph is `r`-colourable (`Cslib.Logic.PL.CNF.exists_eval_coloring_iff`). The edge
variables occur only positively in the clique formula and only negatively in the colouring
formula, which is what monotone feasible interpolation needs.

## Main definitions

* `Cslib.Logic.PL.CNF.clique`, `Cslib.Logic.PL.CNF.coloring`: the clique and colouring formulas.
* `Cslib.Logic.PL.CNF.cliqueMemberClause`, `Cslib.Logic.PL.CNF.cliqueDistinctClause`,
  `Cslib.Logic.PL.CNF.cliqueEdgeClause`, `Cslib.Logic.PL.CNF.colorVertexClause`,
  `Cslib.Logic.PL.CNF.colorUniqueClause`, `Cslib.Logic.PL.CNF.colorEdgeClause`: their clauses.

## Main results

* `Cslib.Logic.PL.CNF.mem_clique`, `Cslib.Logic.PL.CNF.mem_coloring`: the clauses of the two
  formulas.
* `Cslib.Logic.PL.CNF.eval_clique_eq_true_iff`, `Cslib.Logic.PL.CNF.eval_coloring_eq_true_iff`:
  the semantics of the two formulas.
* `Cslib.Logic.PL.CNF.exists_eval_clique_iff`: the edge assignments extendible to the clique
  formula are the graphs with a `k`-clique.
* `Cslib.Logic.PL.CNF.exists_eval_coloring_iff`: the edge assignments extendible to the colouring
  formula are the `r`-colourable graphs.
* `Cslib.Logic.PL.CNF.eq_true_of_mem_clique`, `Cslib.Logic.PL.CNF.eq_false_of_mem_coloring`: the
  edge variables occur only positively in the clique formula and only negatively in the colouring
  formula.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]; Definition 7.1 is numbered as in the author's preprint.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Clique

namespace CNF

variable {n k r : ℕ}

/-! ### The clique formula -/

/-- Clause (1a) of the clique formula: the `u`-th member of the clique is one of the vertices. -/
def cliqueMemberClause (n : ℕ) (u : Fin k) : Clause (Fin (edgeCount n) ⊕ Fin k × Fin n) :=
  (List.finRange n).map fun i => (.inr (u, i), true)

/-- Clause (1b) of the clique formula: the members `u` and `v` are not both the vertex `i`. -/
def cliqueDistinctClause (u v : Fin k) (i : Fin n) : Clause (Fin (edgeCount n) ⊕ Fin k × Fin n) :=
  [(.inr (u, i), false), (.inr (v, i), false)]

/-- Clause (1c) of the clique formula: if the members `u` and `v` are the vertices `i ≠ j`, then
`i` and `j` are adjacent. -/
noncomputable def cliqueEdgeClause (u v : Fin k) {i j : Fin n} (h : i ≠ j) :
    Clause (Fin (edgeCount n) ⊕ Fin k × Fin n) :=
  [(.inr (u, i), false), (.inr (v, j), false), (.inl (edgeEquiv n (edge h)), true)]

/-- **The clique formula** `Clique_{n,k}(p, q)` [Krajíček, Definition 7.1][Krajicek1997], over the
edges `p` of a graph on `n` vertices and the variables `q (u, i)`, read as "the `u`-th member of the
clique is the vertex `i`": (1a) every member `u : Fin k` is some vertex, (1b) two members `u < v`
are not the same vertex, and (1c) if members `u < v` are vertices `i ≠ j`, then `i` and `j` are
adjacent. -/
noncomputable def clique (n k : ℕ) : CNF (Fin (edgeCount n) ⊕ Fin k × Fin n) :=
  (List.finRange k).map (cliqueMemberClause n) ++
    ((List.finRange k).flatMap fun u => ((List.finRange k).filter (u < ·)).flatMap fun v =>
      (List.finRange n).map (cliqueDistinctClause u v)) ++
    (List.finRange k).flatMap fun u => ((List.finRange k).filter (u < ·)).flatMap fun v =>
      (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
        if h : i = j then none else some (cliqueEdgeClause u v h)

/-- The clauses of the clique formula. -/
theorem mem_clique {c : Clause (Fin (edgeCount n) ⊕ Fin k × Fin n)} :
    c ∈ clique n k ↔ (∃ u, c = cliqueMemberClause n u) ∨
      (∃ u v, u < v ∧ ∃ i, c = cliqueDistinctClause u v i) ∨
        ∃ u v, u < v ∧ ∃ (i j : Fin n) (h : i ≠ j), c = cliqueEdgeClause u v h := by
  simp only [clique, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_filterMap,
    Option.dite_none_left_eq_some, Option.some.injEq]
  constructor
  · rintro ((⟨u, rfl⟩ | ⟨u, v, huv, i, rfl⟩) | ⟨u, v, huv, i, j, hij, rfl⟩)
    exacts [.inl ⟨u, rfl⟩, .inr (.inl ⟨u, v, huv, i, rfl⟩), .inr (.inr ⟨u, v, huv, i, j, hij, rfl⟩)]
  · rintro (⟨u, rfl⟩ | ⟨u, v, huv, i, rfl⟩ | ⟨u, v, huv, i, j, hij, rfl⟩)
    exacts [.inl (.inl ⟨u, rfl⟩), .inl (.inr ⟨u, v, huv, i, rfl⟩), .inr ⟨u, v, huv, i, j, hij, rfl⟩]

/-- Clause (1a) holds when the member `u` is some vertex. -/
@[simp] theorem eval_cliqueMemberClause (σ : Fin (edgeCount n) ⊕ Fin k × Fin n → Bool) (u : Fin k) :
    (cliqueMemberClause n u).eval σ = true ↔ ∃ i, σ (.inr (u, i)) = true := by
  simp [cliqueMemberClause, Clause.eval_eq_true_iff]

/-- Clause (1b) holds when the members `u` and `v` are not both the vertex `i`. -/
@[simp] theorem eval_cliqueDistinctClause (σ : Fin (edgeCount n) ⊕ Fin k × Fin n → Bool)
    (u v : Fin k) (i : Fin n) :
    (cliqueDistinctClause u v i).eval σ = (!σ (.inr (u, i)) || !σ (.inr (v, i))) := by
  simp [cliqueDistinctClause]

/-- Clause (1c) holds when the members `u` and `v` are not the vertices `i` and `j`, or `i` and
`j` are adjacent. -/
@[simp] theorem eval_cliqueEdgeClause (σ : Fin (edgeCount n) ⊕ Fin k × Fin n → Bool)
    (u v : Fin k) {i j : Fin n} (h : i ≠ j) :
    (cliqueEdgeClause u v h).eval σ =
      (!σ (.inr (u, i)) || !σ (.inr (v, j)) || σ (.inl (edgeEquiv n (edge h)))) := by
  simp [cliqueEdgeClause, Bool.or_assoc]

/-- **The semantics of the clique formula**: every member is some vertex, two members `u < v` are
not the same vertex, and members `u < v` that are vertices `i ≠ j` make `i` and `j` adjacent. -/
theorem eval_clique_eq_true_iff (σ : Fin (edgeCount n) ⊕ Fin k × Fin n → Bool) :
    (clique n k).eval σ = true ↔
      (∀ u, ∃ i, σ (.inr (u, i)) = true) ∧
        (∀ u v, u < v → ∀ i, σ (.inr (u, i)) = true → σ (.inr (v, i)) = false) ∧
          ∀ u v, u < v → ∀ (i j : Fin n) (h : i ≠ j), σ (.inr (u, i)) = true →
            σ (.inr (v, j)) = true → σ (.inl (edgeEquiv n (edge h))) = true := by
  rw [eval_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun u => (eval_cliqueMemberClause σ u).1 (h _ (mem_clique.2 (.inl ⟨u, rfl⟩))),
      fun u v huv i hu => ?_, fun u v huv i j hij hu hv => ?_⟩
    · simpa [hu] using h _ (mem_clique.2 (.inr (.inl ⟨u, v, huv, i, rfl⟩)))
    · simpa [hu, hv] using h _ (mem_clique.2 (.inr (.inr ⟨u, v, huv, i, j, hij, rfl⟩)))
  · rintro ⟨hmem, hdist, hedge⟩ c hc
    rcases mem_clique.1 hc with ⟨u, rfl⟩ | ⟨u, v, huv, i, rfl⟩ | ⟨u, v, huv, i, j, hij, rfl⟩
    · exact (eval_cliqueMemberClause σ u).2 (hmem u)
    · rw [eval_cliqueDistinctClause]
      cases hu : σ (.inr (u, i))
      · simp
      · simp [hdist u v huv i hu]
    · rw [eval_cliqueEdgeClause]
      cases hu : σ (.inr (u, i))
      · simp
      cases hv : σ (.inr (v, j))
      · simp
      · simp [hedge u v huv i j hij hu hv]

/-- **Extendibility for the clique formula.** An assignment `x` of the edges extends to a model of
the clique formula exactly when the graph of `x` has a `k`-clique. -/
theorem exists_eval_clique_iff (x : Fin (edgeCount n) → Bool) :
    (∃ q, (clique n k).eval (Sum.elim x q) = true) ↔ Circuits.clique n k x = true := by
  rw [clique_eq_true_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hmem, hdist, hedge⟩ := (eval_clique_eq_true_iff _).1 hq
    simp only [Sum.elim_inr, Sum.elim_inl] at hmem hdist hedge
    choose f hf using hmem
    have hinj : Function.Injective f := by
      intro u v huv
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd (hf v) (by rw [← huv, hdist u v h _ (hf u)]; simp)
      · exact absurd (hf u) (by rw [huv, hdist v u h _ (hf v)]; simp)
    refine ⟨Finset.univ.image f, (SimpleGraph.isNClique_iff _).2 ⟨?_, ?_⟩⟩
    · intro i hi j hj hij
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hi hj
      obtain ⟨u, rfl⟩ := hi
      obtain ⟨v, rfl⟩ := hj
      rw [graph_adj hij]
      rcases lt_or_gt_of_ne fun h => hij (congrArg f h) with h | h
      · exact hedge u v h _ _ hij (hf u) (hf v)
      · rw [edge_comm]
        exact hedge v u h _ _ _ (hf v) (hf u)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rintro ⟨s, hs⟩
    let e := s.orderEmbOfFin hs.card_eq
    refine ⟨fun ⟨u, i⟩ => decide (e u = i), (eval_clique_eq_true_iff _).2 ⟨?_, ?_, ?_⟩⟩
    · exact fun u => ⟨e u, by simp⟩
    · intro u v huv i hu
      simp only [Sum.elim_inr, decide_eq_true_eq, decide_eq_false_iff_not] at hu ⊢
      intro hv
      exact huv.ne (e.injective (hu.trans hv.symm))
    · intro u v _ i j hij hu hv
      simp only [Sum.elim_inr, Sum.elim_inl, decide_eq_true_eq] at hu hv ⊢
      subst hu hv
      exact (graph_adj hij).1 (hs.isClique (s.orderEmbOfFin_mem hs.card_eq u)
        (s.orderEmbOfFin_mem hs.card_eq v) hij)

/-- The edge variables occur only positively in the clique formula. -/
theorem eq_true_of_mem_clique {d : Clause (Fin (edgeCount n) ⊕ Fin k × Fin n)}
    (hd : d ∈ clique n k) {e : Fin (edgeCount n)} {b : Bool} (h : (.inl e, b) ∈ d) : b = true := by
  rcases mem_clique.1 hd with ⟨u, rfl⟩ | ⟨u, v, -, i, rfl⟩ | ⟨u, v, -, i, j, hij, rfl⟩ <;>
    simp_all [cliqueMemberClause, cliqueDistinctClause, cliqueEdgeClause]

/-! ### The colouring formula -/

/-- Clause (2a) of the colouring formula: the vertex `i` has one of the colours. -/
def colorVertexClause (r : ℕ) (i : Fin n) : Clause (Fin (edgeCount n) ⊕ Fin n × Fin r) :=
  (List.finRange r).map fun a => (.inr (i, a), true)

/-- Clause (2b) of the colouring formula: the vertex `i` does not have both colours `a` and `b`. -/
def colorUniqueClause (i : Fin n) (a b : Fin r) : Clause (Fin (edgeCount n) ⊕ Fin n × Fin r) :=
  [(.inr (i, a), false), (.inr (i, b), false)]

/-- Clause (2c) of the colouring formula: if the vertices `i ≠ j` both have the colour `a`, then
they are not adjacent. -/
noncomputable def colorEdgeClause (a : Fin r) {i j : Fin n} (h : i ≠ j) :
    Clause (Fin (edgeCount n) ⊕ Fin n × Fin r) :=
  [(.inr (i, a), false), (.inr (j, a), false), (.inl (edgeEquiv n (edge h)), false)]

/-- **The colouring formula** `Color_{n,r}(p, z)` [Krajíček, Definition 7.1][Krajicek1997], over
the edges `p` of a graph on `n` vertices and the variables `z (i, a)`, read as "the vertex `i` has
the colour `a`": (2a) every vertex has some colour `a : Fin r`, (2b) no vertex has two colours
`a < b`, and (2c) two vertices `i < j` of the same colour are not adjacent. -/
noncomputable def coloring (n r : ℕ) : CNF (Fin (edgeCount n) ⊕ Fin n × Fin r) :=
  (List.finRange n).map (colorVertexClause r) ++
    ((List.finRange n).flatMap fun i => (List.finRange r).flatMap fun a =>
      ((List.finRange r).filter (a < ·)).map (colorUniqueClause i a)) ++
    (List.finRange r).flatMap fun a => (List.finRange n).flatMap fun i =>
      (List.finRange n).filterMap fun j => if h : i < j then some (colorEdgeClause a h.ne) else none

/-- The clauses of the colouring formula. -/
theorem mem_coloring {c : Clause (Fin (edgeCount n) ⊕ Fin n × Fin r)} :
    c ∈ coloring n r ↔ (∃ i, c = colorVertexClause r i) ∨
      (∃ i a b, a < b ∧ c = colorUniqueClause i a b) ∨
        ∃ a, ∃ (i j : Fin n) (h : i < j), c = colorEdgeClause a h.ne := by
  simp only [coloring, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_filterMap,
    Option.dite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ((⟨i, rfl⟩ | ⟨i, a, b, hab, rfl⟩) | ⟨a, i, j, hij, rfl⟩)
    exacts [.inl ⟨i, rfl⟩, .inr (.inl ⟨i, a, b, hab, rfl⟩), .inr (.inr ⟨a, i, j, hij, rfl⟩)]
  · rintro (⟨i, rfl⟩ | ⟨i, a, b, hab, rfl⟩ | ⟨a, i, j, hij, rfl⟩)
    exacts [.inl (.inl ⟨i, rfl⟩), .inl (.inr ⟨i, a, b, hab, rfl⟩), .inr ⟨a, i, j, hij, rfl⟩]

/-- Clause (2a) holds when the vertex `i` has some colour. -/
@[simp] theorem eval_colorVertexClause (σ : Fin (edgeCount n) ⊕ Fin n × Fin r → Bool)
    (i : Fin n) : (colorVertexClause r i).eval σ = true ↔ ∃ a, σ (.inr (i, a)) = true := by
  simp [colorVertexClause, Clause.eval_eq_true_iff]

/-- Clause (2b) holds when the vertex `i` does not have both colours `a` and `b`. -/
@[simp] theorem eval_colorUniqueClause (σ : Fin (edgeCount n) ⊕ Fin n × Fin r → Bool)
    (i : Fin n) (a b : Fin r) :
    (colorUniqueClause i a b).eval σ = (!σ (.inr (i, a)) || !σ (.inr (i, b))) := by
  simp [colorUniqueClause]

/-- Clause (2c) holds when the vertices `i` and `j` do not both have the colour `a`, or are not
adjacent. -/
@[simp] theorem eval_colorEdgeClause (σ : Fin (edgeCount n) ⊕ Fin n × Fin r → Bool)
    (a : Fin r) {i j : Fin n} (h : i ≠ j) :
    (colorEdgeClause a h).eval σ =
      (!σ (.inr (i, a)) || !σ (.inr (j, a)) || !σ (.inl (edgeEquiv n (edge h)))) := by
  simp [colorEdgeClause, Bool.or_assoc]

/-- **The semantics of the colouring formula**: every vertex has some colour, no vertex has two
colours `a < b`, and vertices `i < j` with the same colour are not adjacent. -/
theorem eval_coloring_eq_true_iff (σ : Fin (edgeCount n) ⊕ Fin n × Fin r → Bool) :
    (coloring n r).eval σ = true ↔
      (∀ i, ∃ a, σ (.inr (i, a)) = true) ∧
        (∀ i a b, a < b → σ (.inr (i, a)) = true → σ (.inr (i, b)) = false) ∧
          ∀ a, ∀ (i j : Fin n) (h : i < j), σ (.inr (i, a)) = true →
            σ (.inr (j, a)) = true → σ (.inl (edgeEquiv n (edge h.ne))) = false := by
  rw [eval_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun i => (eval_colorVertexClause σ i).1 (h _ (mem_coloring.2 (.inl ⟨i, rfl⟩))),
      fun i a b hab ha => ?_, fun a i j hij hi hj => ?_⟩
    · simpa [ha] using h _ (mem_coloring.2 (.inr (.inl ⟨i, a, b, hab, rfl⟩)))
    · simpa [hi, hj] using h _ (mem_coloring.2 (.inr (.inr ⟨a, i, j, hij, rfl⟩)))
  · rintro ⟨hcol, huniq, hedge⟩ c hc
    rcases mem_coloring.1 hc with ⟨i, rfl⟩ | ⟨i, a, b, hab, rfl⟩ | ⟨a, i, j, hij, rfl⟩
    · exact (eval_colorVertexClause σ i).2 (hcol i)
    · rw [eval_colorUniqueClause]
      cases ha : σ (.inr (i, a))
      · simp
      · simp [huniq i a b hab ha]
    · rw [eval_colorEdgeClause]
      cases hi : σ (.inr (i, a))
      · simp
      cases hj : σ (.inr (j, a))
      · simp
      · simp [hedge a i j hij hi hj]

/-- **Extendibility for the colouring formula.** An assignment `x` of the edges extends to a model
of the colouring formula exactly when the graph of `x` is `r`-colourable. -/
theorem exists_eval_coloring_iff (x : Fin (edgeCount n) → Bool) :
    (∃ z, (coloring n r).eval (Sum.elim x z) = true) ↔ (graph x).Colorable r := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hcol, -, hedge⟩ := (eval_coloring_eq_true_iff _).1 hz
    simp only [Sum.elim_inr, Sum.elim_inl] at hcol hedge
    choose c hc using hcol
    refine ⟨SimpleGraph.Coloring.mk c fun {i j} hij hcij => ?_⟩
    have hx := (graph_adj hij.ne).1 hij
    rcases lt_or_gt_of_ne hij.ne with h | h
    · exact absurd hx (by rw [hedge (c i) i j h (hc i) (hcij ▸ hc j)]; simp)
    · rw [edge_comm] at hx
      exact absurd hx (by rw [hedge (c i) j i h (hcij ▸ hc j) (hc i)]; simp)
  · rintro ⟨C⟩
    refine ⟨fun ⟨i, a⟩ => decide (C i = a), (eval_coloring_eq_true_iff _).2 ⟨?_, ?_, ?_⟩⟩
    · exact fun i => ⟨C i, by simp⟩
    · intro i a b hab ha
      simp only [Sum.elim_inr, decide_eq_true_eq, decide_eq_false_iff_not] at ha ⊢
      exact fun hb => hab.ne (ha.symm.trans hb)
    · intro a i j hij hi hj
      simp only [Sum.elim_inr, Sum.elim_inl, decide_eq_true_eq] at hi hj ⊢
      by_contra hx
      exact C.valid ((graph_adj hij.ne).2 (Bool.not_eq_false _ ▸ hx)) (hi.trans hj.symm)

/-- The edge variables occur only negatively in the colouring formula. -/
theorem eq_false_of_mem_coloring {d : Clause (Fin (edgeCount n) ⊕ Fin n × Fin r)}
    (hd : d ∈ coloring n r) {e : Fin (edgeCount n)} {b : Bool} (h : (.inl e, b) ∈ d) :
    b = false := by
  rcases mem_coloring.1 hd with ⟨i, rfl⟩ | ⟨i, a, a', -, rfl⟩ | ⟨a, i, j, hij, rfl⟩ <;>
    simp_all [colorVertexClause, colorUniqueClause, colorEdgeClause]

end CNF

end Cslib.Logic.PL
