/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.BallPath
public import Complexity.Logics.FirstOrder.Locality.Hanf
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexity.Foundations.ModelTheory.Graph

/-!
# Connectivity, acyclicity and trees are not first-order: proofs by Hanf locality

Hanf locality ([Libkin, Theorem 4.12][Libkin2004], `realize_sentence_iff_of_nbhdIso`) says that
finite structures whose points can be matched by a bijection preserving radius-`(3 ^ n - 1) / 2`
neighborhoods satisfy the same sentences of quantifier rank at most `n`. This module applies it to
cycles and paths. For connectivity this follows [Libkin, §4.1, Figure 4.2 (p. 48), with Theorem 4.12
and the remark following Corollary 4.13 (p. 52)][Libkin2004]; for acyclicity and trees it answers
[Libkin, Exercise 4.6 (p. 63)][Libkin2004].

In a cycle on at least `2r + 2` vertices, and in the interior of a long path, the radius-`r`
neighborhood of every vertex is a path on `2r + 1` vertices centered at it
(`SimpleGraph.exists_isBallPath_cycleGraph`, `SimpleGraph.exists_isBallPath_pathGraph`); two such
neighborhoods are isomorphic (`nbhdIso_of_isBallPath`). Hence:

* The cycle `C_{a+b}` and the disjoint union `C_a ⊕ C_b` are Hanf-equivalent at radius `r` when
  `a, b ≥ 2r + 2` (`hanfEquiv_cycleGraph`). For `a = b = m` this is Libkin's Figure 4.2. So once
  `a, b > 3 ^ n` they satisfy the same sentences of quantifier rank at most `n`
  (`realize_cycleGraph_iff_sum`), although only the first is connected.
* The path `P_{a+b}` and `P_a ⊕ C_b` are Hanf-equivalent at radius `r` when `a ≥ 2r` and
  `b ≥ 2r + 2` (`hanfEquiv_pathGraph`): the vertices near the two ends of `P_{a+b}` go to `P_a`,
  the middle ones to `C_b`. They satisfy the same sentences of quantifier rank at most `n` once
  `3 ^ n ≤ a + 1` and `3 ^ n < b` (`realize_pathGraph_iff_sum`), although only the first is a tree
  and only the first is acyclic (`C_b` is a cycle as `b ≥ 3`).

The consequences are quantitative forms of the nondefinability of these properties: a sentence of
quantifier rank `q` that holds in exactly the connected graphs on a finite vertex type `V` forces
`|V| ≤ 2 · 3 ^ q + 1` (`card_le_of_realize_iff_connected`), and one that holds in exactly the trees,
or exactly the acyclic graphs, on `V` forces `|V| ≤ 2 · 3 ^ q` (`card_le_of_realize_iff_isTree`,
`card_le_of_realize_iff_isAcyclic`). For `q ≥ 1` all three improve to `|V| < 2 · 3 ^ q`
(`card_lt_of_realize_iff_connected`, `card_lt_of_realize_iff_isTree`,
`card_lt_of_realize_iff_isAcyclic`), by comparing `P_{a+b}` with `P_a ⊕ C_b` for `a = 3 ^ q - 1`.
The hypothesis `q ≥ 1` is needed for acyclicity: every graph on two vertices is acyclic, so the
rank-`0` sentence `⊤` defines acyclicity on a two-element type. The constants come from Hanf's
radius `(3 ^ q - 1) / 2`; they are not claimed to be sharp.

The unbounded statements follow at once. For trees this is [Libkin, Exercise 4.6][Libkin2004]:
being a tree is not first-order definable on finite graphs (`not_exists_sentence_isTree`). For
connectivity and acyclicity the library already has the statements, proved by
Ehrenfeucht–Fraïssé games: `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected` and
`Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic`. Their game-free derivations from
the bounds here are checked in the test module `ComplexityTests.FOLocalityGraphProperties` rather
than restated. For connectivity this is the game-free proof of [Libkin, §4.1, Figure 4.2, with
Theorem 4.12 and the remark following Corollary 4.13][Libkin2004]; for acyclicity it is what
[Libkin, Exercise 4.6][Libkin2004] asks for.

All sentences range over the pure graph vocabulary `FirstOrder.Language.graph`, with no built-in
order or arithmetic, and graphs are Mathlib's `SimpleGraph`s with the properties
`SimpleGraph.Connected`, `SimpleGraph.IsAcyclic` and `SimpleGraph.IsTree`.

## Main results

* `Cslib.Logic.FO.Locality.nbhdIso_of_isBallPath`: ball paths over the same interval give
  isomorphic neighborhoods.
* `Cslib.Logic.FO.Locality.hanfEquiv_cycleGraph`, `Cslib.Logic.FO.Locality.hanfEquiv_pathGraph`:
  the Hanf equivalences [Libkin, §4.1, Figure 4.2][Libkin2004].
* `Cslib.Logic.FO.Locality.realize_cycleGraph_iff_sum`,
  `Cslib.Logic.FO.Locality.realize_pathGraph_iff_sum`: the same sentences of bounded quantifier
  rank hold.
* `Cslib.Logic.FO.Locality.card_le_of_realize_iff_connected`,
  `Cslib.Logic.FO.Locality.card_le_of_realize_iff_isTree`,
  `Cslib.Logic.FO.Locality.card_le_of_realize_iff_isAcyclic`: the quantitative bounds.
* `Cslib.Logic.FO.Locality.card_lt_of_realize_iff_connected`,
  `Cslib.Logic.FO.Locality.card_lt_of_realize_iff_isTree`,
  `Cslib.Logic.FO.Locality.card_lt_of_realize_iff_isAcyclic`: the sharper bounds for positive
  quantifier rank.
* `Cslib.Logic.FO.Locality.not_exists_sentence_isTree`: being a tree is not first-order definable
  [Libkin, Exercise 4.6][Libkin2004].

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], §4.1 (Figure 4.2, p. 48),
  Theorem 4.12 and the remark following Corollary 4.13 (p. 52), and Exercise 4.6 (p. 63).
-/

public section

open FirstOrder Language Structure SimpleGraph

namespace Cslib.Logic.FO.Locality

universe u

variable {V W : Type*}

/-! ### Neighborhoods that are paths -/

/-- **Ball paths give isomorphic neighborhoods.** If `φ` and `ψ` parametrize the radius-`r` balls
around `a` in `G` and `b` in `H` as paths over the same parameter interval, the radius-`r`
neighborhoods of `a` and `b` are isomorphic. -/
theorem nbhdIso_of_isBallPath {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ} {lo hi : ℤ}
    {φ : ℤ → V} {ψ : ℤ → W} (hφ : G.IsBallPath r lo hi φ) (hψ : H.IsBallPath r lo hi ψ)
    {a : V} {b : W} (ha : φ 0 = a) (hb : ψ 0 = b) :
    letI := G.structure; letI := H.structure
    NbhdIso Language.graph r (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) := by
  let := G.structure
  let := H.structure
  subst ha hb
  have hballG : ∀ x, x ∈ ball Language.graph (fun _ : Fin 1 => φ 0) r ↔
      ∃ s ∈ Set.Icc lo hi, x = φ s := fun x => by
    rw [mem_ball_const, gaifmanGraph_structure, hφ.edist_le_radius_iff]
  have hballH : ∀ y, y ∈ ball Language.graph (fun _ : Fin 1 => ψ 0) r ↔
      ∃ s ∈ Set.Icc lo hi, y = ψ s := fun y => by
    rw [mem_ball_const, gaifmanGraph_structure, hψ.edist_le_radius_iff]
  classical
  let g : V → ℤ := Function.invFunOn φ (Set.Icc lo hi)
  have hg : ∀ s ∈ Set.Icc lo hi, g (φ s) = s := fun s hs =>
    hφ.injOn (Function.invFunOn_mem ⟨s, hs, rfl⟩) hs (Function.invFunOn_eq ⟨s, hs, rfl⟩)
  refine IsNbhdIso.nbhdIso (h := ψ ∘ g) ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩,
    fun _ => ?_, fun {l} R t ht => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := (hballG x).1 hx
    exact (hballH _).2 ⟨s, hs, by simp only [Function.comp_apply, hg s hs]⟩
  · obtain ⟨s, hs, rfl⟩ := (hballG x).1 hx
    obtain ⟨t, ht, rfl⟩ := (hballG y).1 hy
    simp only [Function.comp_apply, hg s hs, hg t ht] at hxy
    rw [hψ.injOn hs ht hxy]
  · obtain ⟨s, hs, rfl⟩ := (hballH y).1 hy
    exact ⟨φ s, (hballG _).2 ⟨s, hs, rfl⟩, by simp only [Function.comp_apply, hg s hs]⟩
  · simp only [Function.comp_apply, hg 0 ⟨hφ.lo_nonpos, hφ.hi_nonneg⟩]
  · cases R
    obtain ⟨s, hs, hs'⟩ := (hballG (t 0)).1 (ht 0)
    obtain ⟨u, hu, hu'⟩ := (hballG (t 1)).1 (ht 1)
    change H.Adj (ψ (g (t 0))) (ψ (g (t 1))) ↔ G.Adj (t 0) (t 1)
    rw [hs', hu', hg s hs, hg u hu, hψ.adj_iff hs hu, hφ.adj_iff hs hu]

/-! ### Cycles -/

/-- **The cycle `C_{a+b}` and the disjoint union `C_a ⊕ C_b` are Hanf-equivalent** at every radius
`r` with `2r + 2 ≤ a` and `2r + 2 ≤ b`: matched along `finSumFinEquiv`, every vertex on either
side has, as radius-`r` neighborhood, a path on `2r + 1` vertices centered at it. For `a = b` this
is [Libkin, §4.1, Figure 4.2][Libkin2004]. -/
theorem hanfEquiv_cycleGraph {a b r : ℕ} (ha : 2 * r + 2 ≤ a) (hb : 2 * r + 2 ≤ b)
    {x : Fin 0 → Fin (a + b)} {y : Fin 0 → Fin a ⊕ Fin b} :
    letI := (cycleGraph (a + b)).structure
    letI := (cycleGraph a ⊕g cycleGraph b).structure
    HanfEquiv Language.graph r x y := by
  let := (cycleGraph (a + b)).structure
  let := (cycleGraph a ⊕g cycleGraph b).structure
  refine hanfEquiv_zero_iff.2 ⟨finSumFinEquiv.symm, fun c => ?_⟩
  obtain ⟨φ, hφ0, hφ⟩ := exists_isBallPath_cycleGraph (by omega : 2 * r + 2 ≤ a + b) c
  rcases finSumFinEquiv.symm c with d | d
  · obtain ⟨ψ, hψ0, hψ⟩ := exists_isBallPath_cycleGraph ha d
    exact nbhdIso_of_isBallPath hφ (hψ.sumInl (H := cycleGraph b)) hφ0
      (by simp only [Function.comp_apply, hψ0])
  · obtain ⟨ψ, hψ0, hψ⟩ := exists_isBallPath_cycleGraph hb d
    exact nbhdIso_of_isBallPath hφ (hψ.sumInr (G := cycleGraph a)) hφ0
      (by simp only [Function.comp_apply, hψ0])

/-- The Hanf radius `(3 ^ n - 1) / 2` satisfies `2 r + 2 ≤ a` once `3 ^ n < a`. -/
private theorem two_mul_hanf_radius_add_two_le {n a : ℕ} (h : 3 ^ n < a) :
    2 * ((3 ^ n - 1) / 2) + 2 ≤ a := by
  obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  omega

/-- **Hanf locality for cycles**: once `a, b > 3 ^ n`, the cycle `C_{a+b}` and the disjoint union
`C_a ⊕ C_b` satisfy the same sentences of quantifier rank at most `n`. With `a = b = m` this is
the comparison of [Libkin, §4.1, Figure 4.2][Libkin2004] at Libkin's radius `d = (3 ^ n - 1) / 2`,
where `m > 2d + 1` is `m > 3 ^ n`. -/
theorem realize_cycleGraph_iff_sum {n a b : ℕ} (ha : 3 ^ n < a) (hb : 3 ^ n < b)
    {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ n) :
    (letI := (cycleGraph (a + b)).structure; Fin (a + b) ⊨ φ) ↔
      (letI := (cycleGraph a ⊕g cycleGraph b).structure; (Fin a ⊕ Fin b) ⊨ φ) := by
  let := (cycleGraph (a + b)).structure
  let := (cycleGraph a ⊕g cycleGraph b).structure
  have : NeZero (a + b) := ⟨by have := Nat.one_le_pow n 3 (by decide); omega⟩
  obtain ⟨e, he⟩ := hanfEquiv_zero_iff.1 (hanfEquiv_cycleGraph
    (two_mul_hanf_radius_add_two_le ha) (two_mul_hanf_radius_add_two_le hb) (x := Fin.elim0)
    (y := Fin.elim0))
  exact realize_sentence_iff_of_nbhdIso e he hφ

/-- Transfer along a bijection `V ≃ Fin (a + b)`: if `φ` holds in exactly the graphs on `V` with
property `P`, `P` holds for a copy of `G₁` and fails for a copy of `G₂`, then `φ` distinguishes
`G₁` from `G₂`. -/
private theorem not_realize_iff_of_transfer {a b : ℕ} (e : V ≃ Fin (a + b))
    {φ : Language.graph.Sentence} {P : SimpleGraph V → Prop}
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ P G)
    (G₁ : SimpleGraph (Fin (a + b))) (G₂ : SimpleGraph (Fin a ⊕ Fin b))
    (h₁ : P (G₁.comap e)) (h₂ : ¬ P (G₂.comap (e.trans finSumFinEquiv.symm))) :
    ¬ ((letI := G₁.structure; Fin (a + b) ⊨ φ) ↔
      (letI := G₂.structure; (Fin a ⊕ Fin b) ⊨ φ)) := fun h =>
  h₂ ((hφ _).1 ((Iso.comap _ G₂).realize_sentence_iff φ |>.2
    (h.1 ((Iso.comap e G₁).realize_sentence_iff φ |>.1 ((hφ _).2 h₁)))))

/-- **Connectivity needs quantifier rank `log₃` of the size** (the Hanf-locality proof that
connectivity is not first-order, [Libkin, §4.1, Figure 4.2, with Theorem 4.12 and the remark
following Corollary 4.13][Libkin2004], made quantitative): if a sentence `φ` of the language of
graphs holds in exactly the connected simple graphs on a finite vertex type `V`, then
`|V| ≤ 2 · 3 ^ q + 1` where `q` is the quantifier rank of `φ`. -/
theorem card_le_of_realize_iff_connected [Finite V] {φ : Language.graph.Sentence}
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.Connected) :
    Nat.card V ≤ 2 * 3 ^ quantifierRank φ + 1 := by
  by_contra! hV
  have := Fintype.ofFinite V
  obtain ⟨b, hb⟩ : ∃ b, Nat.card V = (3 ^ quantifierRank φ + 1) + b :=
    ⟨Nat.card V - (3 ^ quantifierRank φ + 1), by omega⟩
  let e : V ≃ Fin ((3 ^ quantifierRank φ + 1) + b) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hb)
  refine not_realize_iff_of_transfer e hφ _ _ ?_ ?_
    (realize_cycleGraph_iff_sum (by omega) (by omega) le_rfl)
  · rw [(Iso.comap e _).connected_iff]
    obtain ⟨k, hk⟩ : ∃ k, 3 ^ quantifierRank φ + 1 + b = k + 1 :=
      ⟨3 ^ quantifierRank φ + b, by omega⟩
    rw [hk]
    exact connected_cycleGraph_add_one
  · rw [(Iso.comap _ _).connected_iff]
    have : Nonempty (Fin (3 ^ quantifierRank φ + 1)) := ⟨0⟩
    have : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
    exact not_connected_sum

/-! ### Paths -/

/-- The bijection `Fin (a + b) ≃ Fin a ⊕ Fin b` for the path `P_{a+b}` against `P_a ⊕ C_b`: the
first `r` and the last `a - r` vertices of `P_{a+b}` go to `P_a` in order, the middle `b` vertices
to `C_b`. -/
private def pathCycleEquiv (a b r : ℕ) (hr : r ≤ a) : Fin (a + b) ≃ Fin a ⊕ Fin b where
  toFun c := if h : c.1 < r then .inl ⟨c.1, by omega⟩
    else if h' : c.1 < r + b then .inr ⟨c.1 - r, by omega⟩
    else .inl ⟨c.1 - b, by omega⟩
  invFun
    | .inl d => if d.1 < r then ⟨d.1, by omega⟩ else ⟨d.1 + b, by omega⟩
    | .inr d => ⟨d.1 + r, by omega⟩
  left_inv c := by
    have := c.2
    by_cases h : c.1 < r
    · simp only [h, dite_true, ite_true]
    · by_cases h' : c.1 < r + b
      · simp only [h, h', dite_false, dite_true]
        exact Fin.ext (by simp only; omega)
      · simp only [h, h', dite_false]
        split_ifs with h''
        · omega
        · exact Fin.ext (by simp only; omega)
  right_inv d := by
    rcases d with d | d
    · have := d.2
      by_cases h : d.1 < r
      · simp only [h, ite_true, dite_true]
      · simp only [h, ite_false]
        split_ifs with h₁ h₂
        · omega
        · omega
        · exact congrArg Sum.inl (Fin.ext (by simp only; omega))
    · have := d.2
      simp only
      split_ifs with h₁ h₂
      · omega
      · exact congrArg Sum.inr (Fin.ext (by simp only; omega))
      · omega

/-- **The path `P_{a+b}` and `P_a ⊕ C_b` are Hanf-equivalent** at every radius `r` with `2r ≤ a`
and `2r + 2 ≤ b` (the construction behind [Libkin, Exercise 4.6][Libkin2004]): the vertices near
the two ends of `P_{a+b}` are matched with those of `P_a` and the middle vertices with `C_b`, and
corresponding radius-`r` neighborhoods are the same path. -/
theorem hanfEquiv_pathGraph {a b r : ℕ} (ha : 2 * r ≤ a) (hb : 2 * r + 2 ≤ b)
    {x : Fin 0 → Fin (a + b)} {y : Fin 0 → Fin a ⊕ Fin b} :
    letI := (pathGraph (a + b)).structure
    letI := (pathGraph a ⊕g cycleGraph b).structure
    HanfEquiv Language.graph r x y := by
  let := (pathGraph (a + b)).structure
  let := (pathGraph a ⊕g cycleGraph b).structure
  refine hanfEquiv_zero_iff.2 ⟨pathCycleEquiv a b r (by omega), fun c => ?_⟩
  have hc := c.2
  by_cases h : c.1 < r
  · have he : pathCycleEquiv a b r (by omega) c = .inl ⟨c.1, by omega⟩ := by
      simp only [pathCycleEquiv, Equiv.coe_fn_mk, h, dite_true]
    rw [he]
    obtain ⟨φ, hφ0, hφ⟩ := exists_isBallPath_pathGraph (r := r) c rfl rfl
    obtain ⟨ψ, hψ0, hψ⟩ := exists_isBallPath_pathGraph (r := r) (⟨c.1, by omega⟩ : Fin a)
      (lo := -(min r c.1 : ℕ)) (hi := (min r (a + b - 1 - c.1) : ℕ)) rfl (by simp only; omega)
    exact nbhdIso_of_isBallPath hφ (hψ.sumInl (H := cycleGraph b)) hφ0
      (by simp only [Function.comp_apply, hψ0])
  by_cases h' : c.1 < r + b
  · have he : pathCycleEquiv a b r (by omega) c = .inr ⟨c.1 - r, by omega⟩ := by
      simp only [pathCycleEquiv, Equiv.coe_fn_mk, h, h', dite_false, dite_true]
    rw [he]
    obtain ⟨φ, hφ0, hφ⟩ := exists_isBallPath_pathGraph (r := r) c (lo := -r) (hi := r)
      (by omega) (by omega)
    obtain ⟨ψ, hψ0, hψ⟩ := exists_isBallPath_cycleGraph hb (⟨c.1 - r, by omega⟩ : Fin b)
    exact nbhdIso_of_isBallPath hφ (hψ.sumInr (G := pathGraph a)) hφ0
      (by simp only [Function.comp_apply, hψ0])
  · have he : pathCycleEquiv a b r (by omega) c = .inl ⟨c.1 - b, by omega⟩ := by
      simp only [pathCycleEquiv, Equiv.coe_fn_mk, h, h', dite_false]
    rw [he]
    obtain ⟨φ, hφ0, hφ⟩ := exists_isBallPath_pathGraph (r := r) c rfl rfl
    obtain ⟨ψ, hψ0, hψ⟩ := exists_isBallPath_pathGraph (r := r) (⟨c.1 - b, by omega⟩ : Fin a)
      (lo := -(min r c.1 : ℕ)) (hi := (min r (a + b - 1 - c.1) : ℕ))
      (by simp only; omega) (by simp only; omega)
    exact nbhdIso_of_isBallPath hφ (hψ.sumInl (H := cycleGraph b)) hφ0
      (by simp only [Function.comp_apply, hψ0])

/-- The Hanf radius `(3 ^ n - 1) / 2` satisfies `2 r ≤ a` once `3 ^ n ≤ a + 1`. -/
private theorem two_mul_hanf_radius_le {n a : ℕ} (h : 3 ^ n ≤ a + 1) :
    2 * ((3 ^ n - 1) / 2) ≤ a := by
  obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  omega

/-- **Hanf locality for paths**: once `3 ^ n ≤ a + 1` and `3 ^ n < b`, the path `P_{a+b}` and the
disjoint union `P_a ⊕ C_b` satisfy the same sentences of quantifier rank at most `n`. -/
theorem realize_pathGraph_iff_sum {n a b : ℕ} (ha : 3 ^ n ≤ a + 1) (hb : 3 ^ n < b)
    {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ n) :
    (letI := (pathGraph (a + b)).structure; Fin (a + b) ⊨ φ) ↔
      (letI := (pathGraph a ⊕g cycleGraph b).structure; (Fin a ⊕ Fin b) ⊨ φ) := by
  let := (pathGraph (a + b)).structure
  let := (pathGraph a ⊕g cycleGraph b).structure
  have : NeZero (a + b) := ⟨by have := Nat.one_le_pow n 3 (by decide); omega⟩
  obtain ⟨e, he⟩ := hanfEquiv_zero_iff.1 (hanfEquiv_pathGraph
    (two_mul_hanf_radius_le ha) (two_mul_hanf_radius_add_two_le hb) (x := Fin.elim0)
    (y := Fin.elim0))
  exact realize_sentence_iff_of_nbhdIso e he hφ

/-- A disjoint union with a cycle on at least three vertices is not acyclic. -/
private theorem not_isAcyclic_sum_cycleGraph {G : SimpleGraph V} {b : ℕ} (hb : 3 ≤ b) :
    ¬ (G ⊕g cycleGraph b).IsAcyclic := fun h =>
  isAcyclic_iff_free_cycleGraph.1 h b hb (Embedding.sumInr (G := G) (H := cycleGraph b)).isContained

/-- If `φ` holds in exactly the graphs on `V` with property `P`, and `P` holds for every copy of
`P_{a+b}` and fails for every copy of `P_a ⊕ C_b` with `b ≥ 3`, then `|V| ≤ 2 · 3 ^ q`, where `q`
is the quantifier rank of `φ`. -/
private theorem card_le_of_path [Finite V] {φ : Language.graph.Sentence}
    {P : SimpleGraph V → Prop} (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ P G)
    (hP : ∀ {n} (e : V ≃ Fin n), 1 ≤ n → P ((pathGraph n).comap e))
    (hP' : ∀ {a b} (e : V ≃ Fin a ⊕ Fin b), 3 ≤ b → ¬ P ((pathGraph a ⊕g cycleGraph b).comap e)) :
    Nat.card V ≤ 2 * 3 ^ quantifierRank φ := by
  by_contra! hV
  have := Fintype.ofFinite V
  have h1 : 1 ≤ 3 ^ quantifierRank φ := Nat.one_le_pow _ _ (by decide)
  obtain ⟨b, hb⟩ : ∃ b, Nat.card V = (3 ^ quantifierRank φ - 1) + b :=
    ⟨Nat.card V - (3 ^ quantifierRank φ - 1), by omega⟩
  let e : V ≃ Fin ((3 ^ quantifierRank φ - 1) + b) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hb)
  exact not_realize_iff_of_transfer e hφ _ _ (hP e (by omega)) (hP' _ (by omega))
    (realize_pathGraph_iff_sum (by omega) (by omega) le_rfl)

/-- The sharper form of `card_le_of_path` for quantifier rank `q ≥ 1`: if `P` holds for every copy
of `P_{a+b}` and fails for every copy of `P_a ⊕ C_b` with `a ≥ 1` and `b ≥ 3`, then
`|V| < 2 · 3 ^ q`. -/
private theorem card_lt_of_path [Finite V] {φ : Language.graph.Sentence}
    (hq : 1 ≤ quantifierRank φ) {P : SimpleGraph V → Prop}
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ P G)
    (hP : ∀ {n} (e : V ≃ Fin n), 1 ≤ n → P ((pathGraph n).comap e))
    (hP' : ∀ {a b} (e : V ≃ Fin a ⊕ Fin b), 1 ≤ a → 3 ≤ b →
      ¬ P ((pathGraph a ⊕g cycleGraph b).comap e)) :
    Nat.card V < 2 * 3 ^ quantifierRank φ := by
  by_contra! hV
  have := Fintype.ofFinite V
  have h3 : 3 ≤ 3 ^ quantifierRank φ := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hq
  obtain ⟨b, hb⟩ : ∃ b, Nat.card V = (3 ^ quantifierRank φ - 1) + b :=
    ⟨Nat.card V - (3 ^ quantifierRank φ - 1), by omega⟩
  let e : V ≃ Fin ((3 ^ quantifierRank φ - 1) + b) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hb)
  exact not_realize_iff_of_transfer e hφ _ _ (hP e (by omega)) (hP' _ (by omega) (by omega))
    (realize_pathGraph_iff_sum (by omega) (by omega) le_rfl)

/-- **Being a tree needs quantifier rank `log₃` of the size** ([Libkin, Exercise 4.6][Libkin2004],
made quantitative): if a sentence `φ` of the language of graphs holds in exactly the trees on a
finite vertex type `V`, then `|V| ≤ 2 · 3 ^ q` where `q` is the quantifier rank of `φ`. -/
theorem card_le_of_realize_iff_isTree [Finite V] {φ : Language.graph.Sentence}
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.IsTree) :
    Nat.card V ≤ 2 * 3 ^ quantifierRank φ :=
  card_le_of_path hφ
    (fun e hn => (Iso.comap e _).isTree_iff.2 (isTree_pathGraph.2 (by omega)))
    (fun e hb h => not_isAcyclic_sum_cycleGraph hb ((Iso.comap e _).isTree_iff.1 h).isAcyclic)

/-- **Acyclicity needs quantifier rank `log₃` of the size** ([Libkin, Exercise 4.6][Libkin2004],
made quantitative): if a sentence `φ` of the language of graphs holds in exactly the acyclic graphs
on a finite vertex type `V`, then `|V| ≤ 2 · 3 ^ q` where `q` is the quantifier rank of `φ`. -/
theorem card_le_of_realize_iff_isAcyclic [Finite V] {φ : Language.graph.Sentence}
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic) :
    Nat.card V ≤ 2 * 3 ^ quantifierRank φ :=
  card_le_of_path hφ
    (fun e _ => (Iso.comap e _).isAcyclic_iff.2 (isAcyclic_pathGraph _))
    (fun e hb h => not_isAcyclic_sum_cycleGraph hb ((Iso.comap e _).isAcyclic_iff.1 h))

/-- **The sharper bound for connectivity**: if a sentence `φ` of quantifier rank `q ≥ 1` holds in
exactly the connected simple graphs on a finite vertex type `V`, then `|V| < 2 · 3 ^ q`. The proof
compares `P_{a+b}` with `P_a ⊕ C_b` instead of `C_{a+b}` with `C_a ⊕ C_b`. -/
theorem card_lt_of_realize_iff_connected [Finite V] {φ : Language.graph.Sentence}
    (hq : 1 ≤ quantifierRank φ)
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.Connected) :
    Nat.card V < 2 * 3 ^ quantifierRank φ :=
  card_lt_of_path hq hφ
    (fun e hn => (Iso.comap e _).connected_iff.2 (isTree_pathGraph.2 (by omega)).connected)
    (fun {a b} e ha hb h => by
      have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      have : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
      exact not_connected_sum ((Iso.comap e _).connected_iff.1 h))

/-- **The sharper bound for trees**: if a sentence `φ` of quantifier rank `q ≥ 1` holds in exactly
the trees on a finite vertex type `V`, then `|V| < 2 · 3 ^ q`. -/
theorem card_lt_of_realize_iff_isTree [Finite V] {φ : Language.graph.Sentence}
    (hq : 1 ≤ quantifierRank φ)
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.IsTree) :
    Nat.card V < 2 * 3 ^ quantifierRank φ :=
  card_lt_of_path hq hφ
    (fun e hn => (Iso.comap e _).isTree_iff.2 (isTree_pathGraph.2 (by omega)))
    (fun e _ hb h => not_isAcyclic_sum_cycleGraph hb ((Iso.comap e _).isTree_iff.1 h).isAcyclic)

/-- **The sharper bound for acyclicity**: if a sentence `φ` of quantifier rank `q ≥ 1` holds in
exactly the acyclic graphs on a finite vertex type `V`, then `|V| < 2 · 3 ^ q`. The hypothesis
`q ≥ 1` is needed: every graph on two vertices is acyclic, so the rank-`0` sentence `⊤` defines
acyclicity on a two-element type. -/
theorem card_lt_of_realize_iff_isAcyclic [Finite V] {φ : Language.graph.Sentence}
    (hq : 1 ≤ quantifierRank φ)
    (hφ : ∀ G : SimpleGraph V, (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic) :
    Nat.card V < 2 * 3 ^ quantifierRank φ :=
  card_lt_of_path hq hφ
    (fun e _ => (Iso.comap e _).isAcyclic_iff.2 (isAcyclic_pathGraph _))
    (fun e _ hb h => not_isAcyclic_sum_cycleGraph hb ((Iso.comap e _).isAcyclic_iff.1 h))

/-- **Being a tree is not first-order definable** on finite graphs, even on graphs with at least
`t` vertices: no sentence of the language of graphs holds in exactly the trees among the finite
simple graphs with at least `t` vertices [Libkin, Exercise 4.6][Libkin2004]. -/
theorem not_exists_sentence_isTree_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.IsTree) := by
  rintro ⟨φ, hφ⟩
  have hcard : Nat.card (ULift.{u} (Fin (2 * 3 ^ quantifierRank φ + t + 1))) =
      2 * 3 ^ quantifierRank φ + t + 1 := by
    rw [Nat.card_ulift, Nat.card_fin]
  have := card_le_of_realize_iff_isTree
    (V := ULift.{u} (Fin (2 * 3 ^ quantifierRank φ + t + 1))) (fun G => hφ _ G (by omega))
  omega

/-- **Being a tree is not first-order definable** on finite graphs: no sentence of the language of
graphs holds in exactly the finite trees [Libkin, Exercise 4.6][Libkin2004]. -/
theorem not_exists_sentence_isTree :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsTree := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isTree_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

end Cslib.Logic.FO.Locality
