/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity
public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties
public import CslibFrontier.Logics.FirstOrder.Locality.GraphProperties

/-! # Nondefinability by Hanf locality: checked instances

* **Quantifier rank `2`, radius `4`.** The cycle `C_20` and two disjoint cycles `C_10` are
  Hanf-equivalent at radius `4 = (3 ^ 2 - 1) / 2`, so they satisfy the same sentences of
  quantifier rank at most `2`; only the first is connected. So no sentence of rank at most `2`
  defines connectivity on `20`-vertex graphs. Likewise the path `P_18` and `P_8 ⊕ C_10` satisfy
  the same rank-`2` sentences, and only the first is a tree, so with the sharper bound for positive
  quantifier rank no sentence of rank at most `2` defines the trees on `18`-vertex graphs.
* **The sharper bound needs positive rank.** Every graph on two vertices is acyclic, so the rank-`0`
  sentence `⊤` defines acyclicity on `Fin 2`, and `|V| < 2 · 3 ^ q` fails there.
* **Alternative proofs.** The Ehrenfeucht–Fraïssé theorems
  `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected` and
  `Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic` follow from the Hanf-locality
  bounds, without games: for connectivity as in [Libkin, §4.1, Figure 4.2, with Theorem 4.12
  and the remark following Corollary 4.13][Libkin2004], and for acyclicity as
  [Libkin, Exercise 4.6][Libkin2004] asks.
* **Ball paths.** Balls in a cycle of length at least `2r + 2` and in a path are ball paths. The
  bound `2r + 2` is needed: the radius-`1` ball of the triangle is the whole triangle, which has
  no ball path. -/

@[expose] public section

namespace Cslib.Tests.FOLocalityGraphProperties

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO Cslib.Logic.FO.Locality

universe u

/-! ### Quantifier rank `2`: `C_20` against `2 · C_10` -/

/-- The radius-`4` neighborhoods of `C_20` and `C_10 ⊕ C_10` match: Hanf-equivalence at radius
`(3 ^ 2 - 1) / 2 = 4`. -/
example :
    letI := (cycleGraph (10 + 10)).structure
    letI := (cycleGraph 10 ⊕g cycleGraph 10).structure
    HanfEquiv Language.graph ((3 ^ 2 - 1) / 2) (default : Fin 0 → Fin (10 + 10))
      (default : Fin 0 → Fin 10 ⊕ Fin 10) :=
  hanfEquiv_cycleGraph (r := (3 ^ 2 - 1) / 2) (by norm_num) (by norm_num)

/-- `C_20` and `C_10 ⊕ C_10` satisfy the same sentences of quantifier rank at most `2`. -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 2) :
    (letI := (cycleGraph (10 + 10)).structure; Fin (10 + 10) ⊨ φ) ↔
      (letI := (cycleGraph 10 ⊕g cycleGraph 10).structure; (Fin 10 ⊕ Fin 10) ⊨ φ) :=
  realize_cycleGraph_iff_sum (by norm_num) (by norm_num) hφ

/-- `C_20` is connected. -/
example : (cycleGraph (10 + 10)).Connected := connected_cycleGraph_add_one (n := 19)

/-- `C_10 ⊕ C_10` is not connected. -/
example : ¬ (cycleGraph 10 ⊕g cycleGraph 10).Connected := not_connected_sum

/-- No sentence of quantifier rank at most `2` defines connectivity on `20`-vertex graphs. -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 2) :
    ¬ ∀ G : SimpleGraph (Fin 20), (letI := G.structure; Fin 20 ⊨ φ) ↔ G.Connected := by
  intro h
  have := card_le_of_realize_iff_connected h
  have h3 : 3 ^ quantifierRank φ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hφ
  rw [Nat.card_fin] at this
  omega

/-- `P_18` and `P_8 ⊕ C_10` satisfy the same sentences of quantifier rank at most `2`, while only
the first is a tree (or acyclic). -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 2) :
    (letI := (pathGraph (8 + 10)).structure; Fin (8 + 10) ⊨ φ) ↔
      (letI := (pathGraph 8 ⊕g cycleGraph 10).structure; (Fin 8 ⊕ Fin 10) ⊨ φ) :=
  realize_pathGraph_iff_sum (by norm_num) (by norm_num) hφ

/-- No sentence of quantifier rank at most `2` defines the trees on `18`-vertex graphs: rank `0`
is excluded by `card_le_of_realize_iff_isTree`, ranks `1` and `2` by the sharper
`card_lt_of_realize_iff_isTree`. -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 2) :
    ¬ ∀ G : SimpleGraph (Fin 18), (letI := G.structure; Fin 18 ⊨ φ) ↔ G.IsTree := by
  intro h
  have h3 : 3 ^ quantifierRank φ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hφ
  rcases Nat.eq_zero_or_pos (quantifierRank φ) with h0 | hq
  · have := card_le_of_realize_iff_isTree h
    rw [Nat.card_fin, h0] at this
    omega
  · have := card_lt_of_realize_iff_isTree hq h
    rw [Nat.card_fin] at this
    omega

/-- **The sharper bound needs positive rank**: every graph on two vertices is acyclic, so `⊤`, of
quantifier rank `0`, defines acyclicity on `Fin 2`, although `2 < 2 · 3 ^ 0` fails. -/
example : quantifierRank (⊤ : Language.graph.Sentence) = 0 ∧
    (∀ G : SimpleGraph (Fin 2), (letI := G.structure; Fin 2 ⊨ (⊤ : Language.graph.Sentence)) ↔
      G.IsAcyclic) ∧ ¬ Nat.card (Fin 2) < 2 * 3 ^ 0 := by
  refine ⟨quantifierRank_top, fun G => ?_, by simp⟩
  let := G.structure
  refine iff_of_true (Sentence.realize_top _) ?_
  refine IsAcyclic.anti le_top ?_
  rw [← pathGraph_two_eq_top]
  exact isAcyclic_pathGraph 2

/-! ### Alternative proofs without games -/

/-- **Connectivity is not first-order definable**, by Hanf locality instead of
Ehrenfeucht–Fraïssé games: the statement of `Connectivity.not_exists_sentence_connected`. -/
example :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.Connected := by
  rintro ⟨φ, hφ⟩
  have := card_le_of_realize_iff_connected
    (V := ULift.{u} (Fin (2 * 3 ^ quantifierRank φ + 2))) (hφ _)
  rw [Nat.card_ulift, Nat.card_fin] at this
  omega

/-- **Acyclicity is not first-order definable**, by Hanf locality instead of
Ehrenfeucht–Fraïssé games: the statement of `GraphProperties.not_exists_sentence_isAcyclic`. -/
example :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic := by
  rintro ⟨φ, hφ⟩
  have := card_le_of_realize_iff_isAcyclic
    (V := ULift.{u} (Fin (2 * 3 ^ quantifierRank φ + 1))) (hφ _)
  rw [Nat.card_ulift, Nat.card_fin] at this
  omega

/-- The game proofs and the locality proofs give the same statements. -/
example :
    (¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.Connected) ∧
    (¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic) ∧
    (¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsTree) :=
  ⟨Connectivity.not_exists_sentence_connected, GraphProperties.not_exists_sentence_isAcyclic,
    not_exists_sentence_isTree⟩

/-! ### Ball paths -/

/-- The radius-`4` ball around a vertex of `C_20` is a path on `9` vertices. -/
example (c : Fin 20) : ∃ φ : ℤ → Fin 20, φ 0 = c ∧ IsBallPath (cycleGraph 20) 4 (-4) 4 φ :=
  exists_isBallPath_cycleGraph (by norm_num) c

/-- In `C_20`, the vertices within distance `4` of `c` are `c - 4, …, c + 4`. -/
example (c x : Fin 20) :
    ∃ φ : ℤ → Fin 20, φ 0 = c ∧
      ((cycleGraph 20).edist c x ≤ 4 ↔ ∃ s ∈ Set.Icc (-4 : ℤ) 4, x = φ s) := by
  obtain ⟨φ, rfl, hφ⟩ := exists_isBallPath_cycleGraph (r := 4) (by norm_num) c
  exact ⟨φ, rfl, hφ.edist_le_radius_iff⟩

/-- The radius-`2` ball around vertex `1` of `P_5` is a path over `[-1, 2]`. -/
example : ∃ φ : ℤ → Fin 5, φ 0 = 1 ∧ IsBallPath (pathGraph 5) 2 (-1) 2 φ :=
  exists_isBallPath_pathGraph (r := 2) 1 (by norm_num) (by norm_num)

/-- **The bound `2r + 2 ≤ N` is needed**: the radius-`1` ball around a vertex of the triangle is the
whole triangle, so it has no ball path. -/
example (φ : ℤ → Fin 3) (lo hi : ℤ) : ¬ IsBallPath (cycleGraph 3) 1 lo hi φ := by
  intro hφ
  have h0 : (0 : ℤ) ∈ Set.Icc lo hi := ⟨hφ.lo_nonpos, hφ.hi_nonneg⟩
  have hball : ∀ x, ∃ s ∈ Set.Icc lo hi, x = φ s := fun x => by
    refine hφ.edist_le_radius_iff.1 ?_
    rcases eq_or_ne (φ 0) x with h | h
    · simp [h]
    · rw [Nat.cast_one]
      exact (edist_eq_one_iff_adj.2 (by rw [cycleGraph_three_eq_top]; exact h)).le
  obtain ⟨s, hs, hs'⟩ := hball (φ 0 + 1)
  obtain ⟨t, ht, ht'⟩ := hball (φ 0 + 2)
  have hne : ∀ x : Fin 3, x + 1 ≠ x ∧ x + 2 ≠ x ∧ x + 1 ≠ x + 2 := by decide
  have hs0 : s ≠ 0 := fun h => (hne (φ 0)).1 (by rw [hs', h])
  have ht0 : t ≠ 0 := fun h => (hne (φ 0)).2.1 (by rw [ht', h])
  have hst : φ s ≠ φ t := by rw [← hs', ← ht']; exact (hne (φ 0)).2.2
  have := (hφ.adj_iff hs ht).1 (by rw [cycleGraph_three_eq_top]; exact hst)
  have := hφ.neg_le_lo
  have := hφ.hi_le
  have : s ≠ t := fun h => hst (by rw [h])
  simp only [Set.mem_Icc] at hs ht
  omega

end Cslib.Tests.FOLocalityGraphProperties
