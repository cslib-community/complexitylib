/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Ramsey.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Central

/-!
# Ramsey numbers of graphs

The Ramsey number `R(k, l)` is the least `n` such that every simple graph on `n` vertices has a
clique of size `k` or an independent set of size `l`. A graph on `Fin n` is the same thing as a
red/blue colouring of the edges of the complete graph `K_n` (red edges are the adjacencies), so this
is the classical two-colour Ramsey number.

The upper bound is the induction of Erdős and Szekeres: a vertex `v` of a set with
`C(a + b + 1, a + 1)` vertices has `C(a + b, a)` neighbours or `C(a + b, a + 1)` non-neighbours in
the set, and an `a`-clique among the neighbours or a `(b + 1)`-independent set among the
non-neighbours extends by `v`. Hence `R(a + 1, b + 1) ≤ C(a + b, a)`, that is
`R(k, l) ≤ C(k + l - 2, k - 1)` for `k, l ≥ 1`, and `R(k, k) ≤ 4 ^ (k - 1)`
[ErdosSzekeres1935, pp. 466–467] [Jukna2011, §4.9].

## Main definitions

* `SimpleGraph.ramseyNumber k l`: the Ramsey number `R(k, l)`.

## Main results

* `SimpleGraph.exists_isNClique_or_isNIndepSet_of_choose_le`: every set of at least
  `C(a + b, a)` vertices contains an `(a + 1)`-clique or a `(b + 1)`-independent set.
* `SimpleGraph.ramseyNumber_le_card_iff`, `SimpleGraph.card_lt_ramseyNumber_iff`: the Ramsey number
  in terms of graphs on an arbitrary finite vertex type.
* `SimpleGraph.ramseyNumber_comm`: `R(k, l) = R(l, k)`.
* `SimpleGraph.ramseyNumber_succ_succ_le`: `R(a + 1, b + 1) ≤ C(a + b, a)`.
* `SimpleGraph.ramseyNumber_le_four_pow`: `R(k, k) ≤ 4 ^ (k - 1)`.

## References

* [P. Erdős, G. Szekeres, *A combinatorial problem in geometry*][ErdosSzekeres1935]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- **Erdős–Szekeres**: in any graph, every set of at least `C(a + b, a)` vertices contains a
clique of size `a + 1` or an independent set of size `b + 1` [ErdosSzekeres1935, pp. 466–467]. -/
theorem exists_isNClique_or_isNIndepSet_of_choose_le (G : SimpleGraph V) :
    ∀ (a b : ℕ) (s : Finset V), (a + b).choose a ≤ #s →
      (∃ t ⊆ s, G.IsNClique (a + 1) t) ∨ ∃ t ⊆ s, G.IsNIndepSet (b + 1) t := by
  classical
  intro a
  induction a with
  | zero =>
    intro b s hs
    obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by simpa using hs)
    exact .inl ⟨{v}, by simpa using hv, by simp⟩
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      intro s hs
      obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by simpa using hs)
      exact .inr ⟨{v}, by simpa using hv, by simp [isNIndepSet_iff]⟩
    | succ b ihb =>
      intro s hs
      obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (lt_of_lt_of_le (Nat.choose_pos (by omega)) hs)
      set N := (s.erase v).filter (G.Adj v) with hN
      set M := (s.erase v).filter (fun w => ¬ G.Adj v w) with hM
      have hcard : #N + #M + 1 = #s := by
        rw [hN, hM, card_filter_add_card_filter_not, card_erase_of_mem hv]
        have := card_pos.2 ⟨v, hv⟩
        omega
      have hpascal : (a + 1 + (b + 1)).choose (a + 1) =
          (a + (b + 1)).choose a + (a + 1 + b).choose (a + 1) := by
        rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega, Nat.choose_succ_succ',
          show a + (b + 1) = a + 1 + b by omega]
      have hNs : N ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
      have hMs : M ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
      by_cases hNc : (a + (b + 1)).choose a ≤ #N
      · rcases iha (b + 1) N hNc with ⟨t, ht, hcl⟩ | ⟨t, ht, hind⟩
        · refine .inl ⟨insert v t, insert_subset hv (ht.trans hNs), hcl.insert fun w hw => ?_⟩
          exact (mem_filter.1 (ht hw)).2
        · exact .inr ⟨t, ht.trans hNs, hind⟩
      · have hMc : (a + 1 + b).choose (a + 1) ≤ #M := by omega
        rcases ihb M hMc with ⟨t, ht, hcl⟩ | ⟨t, ht, hind⟩
        · exact .inl ⟨t, ht.trans hMs, hcl⟩
        · refine .inr ⟨insert v t, insert_subset hv (ht.trans hMs), ?_⟩
          rw [← isNClique_compl] at hind ⊢
          refine hind.insert fun w hw => ?_
          have hw' := mem_filter.1 (ht hw)
          rw [compl_adj]
          exact ⟨fun h => (mem_erase.1 hw'.1).1 h.symm, hw'.2⟩

/-- A clique or an independent set of a pulled-back graph maps to one of the original graph. -/
private theorem exists_of_comap {W : Type*} (G : SimpleGraph W) (f : V ↪ W) {k l : ℕ}
    (h : (∃ s, (G.comap f).IsNClique k s) ∨ ∃ s, (G.comap f).IsNIndepSet l s) :
    (∃ s, G.IsNClique k s) ∨ ∃ s, G.IsNIndepSet l s := by
  classical
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine .inl ⟨s.map f, ⟨?_, by rw [card_map, hs.2]⟩⟩
    rw [coe_map, IsClique, f.injective.injOn.pairwise_image]
    exact hs.1
  · refine .inr ⟨s.map f, ⟨?_, by rw [card_map, hs.2]⟩⟩
    rw [coe_map, IsIndepSet, f.injective.injOn.pairwise_image]
    exact hs.1

/-- The **Ramsey number** `R(k, l)`: the least `n` such that every simple graph on `Fin n` has a
clique of size `k` or an independent set of size `l`. Equivalently, every red/blue colouring of the
edges of `K_n` has a red `K_k` or a blue `K_l`. The set of such `n` is nonempty by
`SimpleGraph.exists_isNClique_or_isNIndepSet_of_choose_le`, so the infimum is attained, and
`SimpleGraph.ramseyNumber_le_card_iff` characterizes it on every finite vertex type. -/
noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {n | ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ ∃ s, G.IsNIndepSet l s}

private theorem ramseyNumber_set_nonempty (k l : ℕ) :
    {n | ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ ∃ s, G.IsNIndepSet l s}.Nonempty := by
  rcases k with _ | a
  · exact ⟨0, fun G => .inl ⟨∅, by simp⟩⟩
  rcases l with _ | b
  · exact ⟨0, fun G => .inr ⟨∅, by simp [isNIndepSet_iff]⟩⟩
  refine ⟨(a + b).choose a, fun G => ?_⟩
  rcases G.exists_isNClique_or_isNIndepSet_of_choose_le a b univ (by simp) with
    ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact .inl ⟨t, ht⟩
  · exact .inr ⟨t, ht⟩

/-- `R(k, l) ≤ |V|` exactly when every graph on `V` has a `k`-clique or an `l`-independent set. -/
theorem ramseyNumber_le_card_iff {k l : ℕ} [Fintype V] :
    ramseyNumber k l ≤ Fintype.card V ↔
      ∀ G : SimpleGraph V, (∃ s, G.IsNClique k s) ∨ ∃ s, G.IsNIndepSet l s := by
  constructor
  · intro h G
    have hmem := Nat.sInf_mem (ramseyNumber_set_nonempty k l)
    exact exists_of_comap G ((Fin.castLEEmb h).trans (Fintype.equivFin V).symm.toEmbedding)
      (hmem _)
  · intro h
    refine Nat.sInf_le fun G => ?_
    exact exists_of_comap G (Fintype.equivFin V).toEmbedding (h _)

/-- `|V| < R(k, l)` exactly when some graph on `V` has no `k`-clique and no `l`-independent set.
This is how lower bounds on Ramsey numbers are proved. -/
theorem card_lt_ramseyNumber_iff {k l : ℕ} [Fintype V] :
    Fintype.card V < ramseyNumber k l ↔ ∃ G : SimpleGraph V, G.CliqueFree k ∧ G.IndepSetFree l := by
  rw [← not_le, ramseyNumber_le_card_iff]
  simp only [not_forall, not_or, not_exists, CliqueFree, IndepSetFree]

/-- A graph with at least `R(k, l)` vertices has a `k`-clique or an `l`-independent set. -/
theorem exists_isNClique_or_isNIndepSet {k l : ℕ} [Fintype V] (G : SimpleGraph V)
    (h : ramseyNumber k l ≤ Fintype.card V) :
    (∃ s, G.IsNClique k s) ∨ ∃ s, G.IsNIndepSet l s :=
  ramseyNumber_le_card_iff.1 h G

/-- Ramsey numbers are symmetric: pass to the complement graph. -/
theorem ramseyNumber_comm (k l : ℕ) : ramseyNumber k l = ramseyNumber l k := by
  have key : ∀ k l n, (∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨
      ∃ s, G.IsNIndepSet l s) → ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique l s) ∨
      ∃ s, G.IsNIndepSet k s := by
    intro k l n h G
    rcases h Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact .inr ⟨s, (isNClique_compl G).1 hs⟩
    · exact .inl ⟨s, (isNIndepSet_compl G).1 hs⟩
  unfold ramseyNumber
  congr 1
  ext n
  exact ⟨key k l n, key l k n⟩

/-- **Erdős–Szekeres**: `R(a + 1, b + 1) ≤ C(a + b, a)`, that is, `R(k, l) ≤ C(k + l - 2, k - 1)`
for `k, l ≥ 1` [ErdosSzekeres1935, pp. 466–467] [Jukna2011, §4.9]. -/
theorem ramseyNumber_succ_succ_le (a b : ℕ) :
    ramseyNumber (a + 1) (b + 1) ≤ (a + b).choose a := by
  have h := ramseyNumber_le_card_iff (k := a + 1) (l := b + 1) (V := Fin ((a + b).choose a))
  rw [Fintype.card_fin] at h
  refine h.2 fun G => ?_
  rcases G.exists_isNClique_or_isNIndepSet_of_choose_le a b univ (by simp) with
    ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact .inl ⟨t, ht⟩
  · exact .inr ⟨t, ht⟩

/-- The diagonal upper bound `R(k, k) ≤ C(2k - 2, k - 1) ≤ 4 ^ (k - 1)`. -/
theorem ramseyNumber_le_four_pow (k : ℕ) : ramseyNumber k k ≤ 4 ^ (k - 1) := by
  rcases k with _ | m
  · have h := ramseyNumber_le_card_iff (k := 0) (l := 0) (V := Fin 0)
    rw [Fintype.card_fin] at h
    exact (h.2 fun G => .inl ⟨∅, by simp⟩).trans (Nat.zero_le _)
  · refine (ramseyNumber_succ_succ_le m m).trans ?_
    rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose, Nat.add_sub_cancel]
    exact Nat.centralBinom_le_four_pow m

end SimpleGraph

end
