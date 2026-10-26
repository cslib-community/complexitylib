/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Mixing
import Complexity.Foundations.Data.Finset.Quantile
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Cheeger's inequality for regular graphs

The edge expansion `h(G)` of a regular graph measures combinatorially how well it is connected: it
is the least number of edges leaving a set of at most half of the vertices, per vertex of the set.
Its spectral counterpart is the gap `1 - λ₂(G)` between the two largest eigenvalues of the walk
operator (`walkEuclidean_eigenvalues_zero`, `secondEigenvalue_eq_walkEuclidean_eigenvalues_one`).
The **discrete Cheeger inequality**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09] says that the two agree up to a square: for a
`d`-regular graph,

`d (1 - λ₂(G)) / 2 ≤ h(G) ≤ d √(2 (1 - λ₂(G)))`.

The edge expansion `h(G)` (`edgeExpansion`) is normalized as in
[Hoory, Linial and Wigderson, Definition 2.1][HooryLinialWigderson2006]: it is the minimum of
`e(S, Sᶜ) / |S|` over the nonempty sets `S` of at most half of the vertices, where `e(S, Sᶜ)` counts
the edges between `S` and its complement; [Arora and Barak, Section 21.2][AroraBarak09] divides it
by `d`. The second eigenvalue `λ₂(G)` (`secondEigenvalue`) is the supremum of the Rayleigh quotient
`𝔼 f · G.walk f / 𝔼 f²` over the nonzero functions `f` of expectation zero
(`secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero`). It lies between `-λ(G)`
and `λ(G)`, and equals the spectral expansion `λ(G)` when the walk operator is positive
semidefinite. Both are defined without spectral theory and used through their characterizations
`secondEigenvalue_le_iff` and `le_edgeExpansion_iff`; on fewer than two vertices both are `0` by
convention.

The easy half is the one-sided expander mixing lemma
`le_card_interedges_compl_of_expect_mul_walk_le`. The hard half is proved for every function `f`
of expectation zero, with no eigenvector. Over a uniformly random dart `(u, w)`, the Dirichlet
form `𝔼 (f u - f w)²` is `2 (𝔼 f² - 𝔼 f · G.walk f)`, and it does not change when `f` is shifted
by a constant. Shifted by a median, `f` splits into a positive and a negative part, each vanishing
outside a set of at most half of the vertices. For such a nonnegative `φ`, the co-area inequality
bounds the variation of `φ²` along the darts from below by the edges leaving the level sets of `φ`,
and the Cauchy–Schwarz inequality turns this into `h(G)² 𝔼 φ² ≤ d² 𝔼 (φ u - φ w)²`.

Edge expansion bounds `λ₂(G)` but not `λ(G)`: a bipartite graph can be a good edge expander, yet
`-1` is an eigenvalue of its walk operator. The lazy walk `(f + G.walk f) / 2` of the lazy graph
`Cslib.RotationMap.lazy`, which stays put with probability `1 / 2`, is positive semidefinite, so
its spectral expansion is at most `1 - h(G)² / (4 d²)`
(`Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div`).

## Main definitions

* `Cslib.RotationMap.secondEigenvalue`: the second eigenvalue `λ₂(G)` of the walk operator.
* `Cslib.RotationMap.edgeExpansion`: the edge expansion `h(G)`.

## Main results

* `Cslib.RotationMap.secondEigenvalue_le_iff`, `Cslib.RotationMap.le_edgeExpansion_iff`: the
  characterizations of `λ₂(G)` and `h(G)`.
* `Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_card_interedges`: at least
  `h(G) |V| / 3` edges leave every set of between a third and two thirds of the vertices.
* `Cslib.RotationMap.abs_secondEigenvalue_le_spectralExpansion`: `|λ₂(G)| ≤ λ(G)`.
* `Cslib.RotationMap.spectralExpansion_eq_secondEigenvalue_of_nonneg`: `λ(G) = λ₂(G)` when the
  walk operator is positive semidefinite.
* `Cslib.RotationMap.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion`,
  `Cslib.RotationMap.le_edgeExpansion_of_spectralExpansion_le`: the easy half of Cheeger's
  inequality.
* `Cslib.RotationMap.expect_mul_walk_le_of_mul_card_le_card_interedges_compl`: the hard half of
  Cheeger's inequality in one-sided form, from any lower bound on the edges leaving small sets.
* `Cslib.RotationMap.edgeExpansion_le_card_mul_sqrt`,
  `Cslib.RotationMap.secondEigenvalue_le_one_sub_edgeExpansion_sq_div`: the hard half of
  Cheeger's inequality.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D)

section SecondEigenvalue

/-- The **second eigenvalue** `λ₂(G)` of the walk operator: the supremum of the Rayleigh quotient
`𝔼 v, f v * G.walk f v / 𝔼 v, f v ^ 2` over the nonzero functions `f` of expectation zero, that
is over the nonzero functions orthogonal to the constants. When `V` has at most one vertex there
is no such function, and `λ₂(G) = 0` by convention. Otherwise, as the walk operator is
self-adjoint and fixes the constants, this is the largest eigenvalue of its restriction to the
functions of expectation zero (`secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero`) and its
second largest eigenvalue on the full space counted with multiplicity
(`secondEigenvalue_eq_walkEuclidean_eigenvalues_one`), but nothing here depends on spectral
theory: `λ₂(G)` is used through `expect_mul_walk_le_secondEigenvalue_mul` and
`secondEigenvalue_le_iff`. -/
noncomputable def secondEigenvalue : ℝ :=
  ⨆ f : {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0}, (𝔼 v, f.1 v * G.walk f.1 v) / 𝔼 v, f.1 v ^ 2

/-- A nonzero function has a positive second moment. -/
private theorem expect_sq_pos {f : V → ℝ} (hf : f ≠ 0) : 0 < 𝔼 v, f v ^ 2 := by
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hf
  exact expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v, mem_univ v, sq_pos_iff.2 hv⟩

/-- With at least two vertices, some nonzero function has expectation zero. -/
private theorem exists_expect_eq_zero_ne_zero [Nontrivial V] :
    ∃ f : V → ℝ, 𝔼 v, f v = 0 ∧ f ≠ 0 := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  refine ⟨Pi.single a 1 - Pi.single b 1, ?_, fun h ↦ ?_⟩
  · simp [expect_sub_distrib, Fintype.expect_eq_sum_div_card]
  · simpa [hab] using congrFun h a

/-- The Rayleigh quotient of a function of expectation zero is at most `λ(G)`. -/
private theorem div_le_spectralExpansion {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    (𝔼 v, f v * G.walk f v) / 𝔼 v, f v ^ 2 ≤ G.spectralExpansion :=
  div_le_of_le_mul₀ (expect_nonneg fun _ _ ↦ sq_nonneg _) G.spectralExpansion_nonneg
    ((le_abs_self _).trans (G.abs_expect_mul_walk_le hf))

/-- The Rayleigh quotients of the nonzero functions of expectation zero are bounded above. -/
private theorem bddAbove_range_div :
    BddAbove (Set.range fun f : {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0} ↦
      (𝔼 v, f.1 v * G.walk f.1 v) / 𝔼 v, f.1 v ^ 2) :=
  ⟨G.spectralExpansion, Set.forall_mem_range.2 fun f ↦ G.div_le_spectralExpansion f.2.1⟩

/-- For `f` of expectation zero, `𝔼 v, f v * G.walk f v ≤ λ₂(G) 𝔼 f²`. -/
theorem expect_mul_walk_le_secondEigenvalue_mul {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, f v * G.walk f v ≤ G.secondEigenvalue * 𝔼 v, f v ^ 2 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  rw [← div_le_iff₀ (expect_sq_pos hf0)]
  exact le_ciSup G.bddAbove_range_div ⟨f, hf, hf0⟩

/-- On at least two vertices, `λ₂(G) ≤ μ` exactly when `𝔼 v, f v * G.walk f v ≤ μ 𝔼 f²` for every
function `f` of expectation zero. -/
theorem secondEigenvalue_le_iff [Nontrivial V] {μ : ℝ} :
    G.secondEigenvalue ≤ μ ↔
      ∀ f : V → ℝ, 𝔼 v, f v = 0 → 𝔼 v, f v * G.walk f v ≤ μ * 𝔼 v, f v ^ 2 := by
  refine ⟨fun h f hf ↦ (G.expect_mul_walk_le_secondEigenvalue_mul hf).trans
    (mul_le_mul_of_nonneg_right h (expect_nonneg fun _ _ ↦ sq_nonneg _)), fun h ↦ ?_⟩
  obtain ⟨f₀, hf₀⟩ := exists_expect_eq_zero_ne_zero (V := V)
  have : Nonempty {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0} := ⟨⟨f₀, hf₀⟩⟩
  exact ciSup_le fun f ↦ (div_le_iff₀ (expect_sq_pos f.2.2)).2 (h f.1 f.2.1)

/-- On at most one vertex, `λ₂(G) = 0` by convention. -/
theorem secondEigenvalue_eq_zero_of_subsingleton [Subsingleton V] : G.secondEigenvalue = 0 := by
  have : IsEmpty {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0} := by
    refine ⟨fun ⟨f, hf, hf0⟩ ↦ hf0 (funext fun v ↦ ?_)⟩
    have : Nonempty V := ⟨v⟩
    calc f v = 𝔼 _w : V, f v := (Fintype.expect_const _).symm
      _ = 𝔼 w, f w := expect_congr rfl fun w _ ↦ congrArg f (Subsingleton.elim v w)
      _ = 0 := hf
  exact Real.iSup_of_isEmpty _

/-- The second eigenvalue is at most the spectral expansion. -/
theorem secondEigenvalue_le_spectralExpansion : G.secondEigenvalue ≤ G.spectralExpansion :=
  Real.iSup_le (fun f ↦ G.div_le_spectralExpansion f.2.1) G.spectralExpansion_nonneg

/-- The second eigenvalue is at least minus the spectral expansion. -/
theorem neg_spectralExpansion_le_secondEigenvalue : -G.spectralExpansion ≤ G.secondEigenvalue := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.secondEigenvalue_eq_zero_of_subsingleton, neg_nonpos]
    exact G.spectralExpansion_nonneg
  obtain ⟨f, hf, hf0⟩ := exists_expect_eq_zero_ne_zero (V := V)
  refine le_trans ?_ (le_ciSup G.bddAbove_range_div ⟨f, hf, hf0⟩)
  rw [le_div_iff₀ (expect_sq_pos hf0), neg_mul]
  exact neg_le_of_abs_le (G.abs_expect_mul_walk_le hf)

/-- The second eigenvalue is at most the spectral expansion in absolute value. -/
theorem abs_secondEigenvalue_le_spectralExpansion : |G.secondEigenvalue| ≤ G.spectralExpansion :=
  abs_le.2 ⟨G.neg_spectralExpansion_le_secondEigenvalue, G.secondEigenvalue_le_spectralExpansion⟩

/-- The second eigenvalue is at most one. -/
theorem secondEigenvalue_le_one : G.secondEigenvalue ≤ 1 :=
  G.secondEigenvalue_le_spectralExpansion.trans G.spectralExpansion_le_one

/-- The second eigenvalue is at least minus one. -/
theorem neg_one_le_secondEigenvalue : -1 ≤ G.secondEigenvalue :=
  (neg_le_neg G.spectralExpansion_le_one).trans G.neg_spectralExpansion_le_secondEigenvalue

/-- The correlation of any function with its image under the walk operator is at most its second
moment in absolute value. -/
theorem abs_expect_mul_walk_le_expect_sq (f : V → ℝ) :
    |𝔼 v, f v * G.walk f v| ≤ 𝔼 v, f v ^ 2 := by
  refine abs_le_of_sq_le_sq ?_ (expect_nonneg fun _ _ ↦ sq_nonneg _)
  calc
    _ ≤ (𝔼 v, f v ^ 2) * 𝔼 v, G.walk f v ^ 2 := expect_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (𝔼 v, f v ^ 2) * 𝔼 v, f v ^ 2 :=
      mul_le_mul_of_nonneg_left (G.expect_walk_sq_le f) (expect_nonneg fun _ _ ↦ sq_nonneg _)
    _ = _ := by ring

/-- The Cauchy–Schwarz inequality for a positive semidefinite walk operator. -/
private theorem sq_expect_mul_walk_le (h : ∀ f : V → ℝ, 0 ≤ 𝔼 v, f v * G.walk f v)
    (f g : V → ℝ) :
    (𝔼 v, f v * G.walk g v) ^ 2 ≤ (𝔼 v, f v * G.walk f v) * 𝔼 v, g v * G.walk g v := by
  have hgf : 𝔼 v, g v * G.walk f v = 𝔼 v, f v * G.walk g v := by
    rw [G.expect_mul_walk_comm]
    exact expect_congr rfl fun v _ ↦ mul_comm _ _
  have hd := discrim_le_zero (a := 𝔼 v, g v * G.walk g v) (b := 2 * 𝔼 v, f v * G.walk g v)
    (c := 𝔼 v, f v * G.walk f v) fun x ↦ by
    have hx := h (f + x • g)
    rw [map_add, map_smul] at hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx
    calc
      0 ≤ _ := hx
      _ = 𝔼 v, (f v * G.walk f v + x * (f v * G.walk g v + g v * G.walk f v) +
            x * x * (g v * G.walk g v)) := expect_congr rfl fun v _ ↦ by ring
      _ = _ := by
        rw [expect_add_distrib, expect_add_distrib, ← mul_expect, ← mul_expect,
          expect_add_distrib, hgf]
        ring
  rw [discrim] at hd
  linarith

/-- If the walk operator is positive semidefinite, `0 ≤ 𝔼 v, f v * G.walk f v` for every `f`, then
the spectral expansion is the second eigenvalue: `λ(G) = λ₂(G)`. -/
theorem spectralExpansion_eq_secondEigenvalue_of_nonneg
    (h : ∀ f : V → ℝ, 0 ≤ 𝔼 v, f v * G.walk f v) :
    G.spectralExpansion = G.secondEigenvalue := by
  refine le_antisymm ?_ G.secondEigenvalue_le_spectralExpansion
  have hlam : 0 ≤ G.secondEigenvalue := by
    rcases subsingleton_or_nontrivial V with hV | hV
    · rw [G.secondEigenvalue_eq_zero_of_subsingleton]
    obtain ⟨f, hf, hf0⟩ := exists_expect_eq_zero_ne_zero (V := V)
    exact nonneg_of_mul_nonneg_left ((h f).trans (G.expect_mul_walk_le_secondEigenvalue_mul hf))
      (expect_sq_pos hf0)
  refine (spectralExpansion_le_iff hlam).2 fun f hf ↦ ?_
  have hW : 𝔼 v, f v * G.walk (G.walk f) v = 𝔼 v, G.walk f v ^ 2 := by
    rw [G.expect_mul_walk_comm]
    exact expect_congr rfl fun v _ ↦ (sq _).symm
  have h1 := G.expect_mul_walk_le_secondEigenvalue_mul hf
  have h2 := G.expect_mul_walk_le_secondEigenvalue_mul (G.expect_walk_eq_zero hf)
  have hcs := G.sq_expect_mul_walk_le h f (G.walk f)
  rw [hW] at hcs
  have ha : 0 ≤ 𝔼 v, G.walk f v ^ 2 := expect_nonneg fun _ _ ↦ sq_nonneg _
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha]
    positivity
  refine le_of_mul_le_mul_right ?_ ha
  calc
    _ = (𝔼 v, G.walk f v ^ 2) ^ 2 := by ring
    _ ≤ _ := hcs
    _ ≤ (G.secondEigenvalue * 𝔼 v, f v ^ 2) * (G.secondEigenvalue * 𝔼 v, G.walk f v ^ 2) :=
      mul_le_mul h1 h2 (h _) (le_trans (h f) h1)
    _ = _ := by ring

end SecondEigenvalue

section EdgeExpansion

variable [DecidableEq V]

/-- The **edge expansion** `h(G)`
[Hoory, Linial and Wigderson, Definition 2.1][HooryLinialWigderson2006]: the least ratio
`e(S, Sᶜ) / |S|` of the number `e(S, Sᶜ)` of edges leaving `S` to the size of `S`, over the nonempty
sets `S` of at most half of the vertices. It counts edges, so `0 ≤ h(G) ≤ |D|`;
[Arora and Barak, Section 21.2][AroraBarak09] divides it by the degree `|D|` instead. When `V` has
at most one vertex there is no such set, and `h(G) = 0` by convention. -/
noncomputable def edgeExpansion : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
    (#(G.interedges S.1 S.1ᶜ) : ℝ) / #S.1

/-- The edge expansion is nonnegative. -/
theorem edgeExpansion_nonneg : 0 ≤ G.edgeExpansion :=
  Real.iInf_nonneg fun _ ↦ by positivity

/-- At least `h(G) |S|` edges leave every set `S` of at most half of the vertices. -/
theorem edgeExpansion_mul_card_le {S : Finset V} (hS : 2 * #S ≤ Fintype.card V) :
    G.edgeExpansion * #S ≤ #(G.interedges S Sᶜ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [card_empty, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  have hb : BddBelow (Set.range fun S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} ↦
      (#(G.interedges S.1 S.1ᶜ) : ℝ) / #S.1) :=
    ⟨0, Set.forall_mem_range.2 fun _ ↦ by positivity⟩
  rw [← le_div_iff₀ (Nat.cast_pos.2 hne.card_pos)]
  exact ciInf_le hb ⟨S, hne, hS⟩

/-- On at least two vertices, `c ≤ h(G)` exactly when at least `c |S|` edges leave every set `S` of
at most half of the vertices. -/
theorem le_edgeExpansion_iff [Nontrivial V] {c : ℝ} :
    c ≤ G.edgeExpansion ↔
      ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ #(G.interedges S Sᶜ) := by
  refine ⟨fun h S hS ↦ (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans
    (G.edgeExpansion_mul_card_le hS), fun h ↦ ?_⟩
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have : Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨⟨{v}, singleton_nonempty v, by rw [card_singleton, mul_one]; exact Fintype.one_lt_card⟩⟩
  exact le_ciInf fun S ↦ (le_div_iff₀ (Nat.cast_pos.2 S.2.1.card_pos)).2 (h S.1 S.2.2)

/-- On at most one vertex, `h(G) = 0` by convention. -/
theorem edgeExpansion_eq_zero_of_subsingleton [Subsingleton V] : G.edgeExpansion = 0 := by
  have : IsEmpty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨fun ⟨S, hne, hS⟩ ↦ by
      have := Fintype.card_le_one_iff_subsingleton.2 ‹_›
      have := hne.card_pos
      omega⟩
  exact Real.iInf_of_isEmpty _

/-- The edge expansion is at most the degree `|D|`. -/
theorem edgeExpansion_le_card : G.edgeExpansion ≤ Fintype.card D := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.edgeExpansion_eq_zero_of_subsingleton]
    positivity
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h := G.edgeExpansion_mul_card_le (S := {v}) <| by
    rw [card_singleton, mul_one]
    exact Fintype.one_lt_card
  have h' := G.card_interedges_add_card_interedges_compl {v} {v}
  rw [card_singleton, Nat.cast_one, mul_one] at h
  rw [card_singleton, one_mul] at h'
  exact h.trans (Nat.cast_le.2 (by omega))

/-- At least `h(G) |V| / 3` edges leave every set of between a third and two thirds of the
vertices: the set, or its complement, has at most half and at least a third of the vertices. -/
theorem edgeExpansion_mul_card_div_three_le_card_interedges {S : Finset V}
    (h₁ : Fintype.card V ≤ 3 * #S) (h₂ : 3 * #S ≤ 2 * Fintype.card V) :
    G.edgeExpansion * Fintype.card V / 3 ≤ #(G.interedges S Sᶜ) := by
  have hc := card_add_card_compl S
  rcases le_or_gt (2 * #S) (Fintype.card V) with h | h
  · have hS : (Fintype.card V : ℝ) ≤ 3 * #S := by exact_mod_cast h₁
    have := G.edgeExpansion_mul_card_le h
    nlinarith [G.edgeExpansion_nonneg]
  · have hle : 2 * #Sᶜ ≤ Fintype.card V := by omega
    have hS : (Fintype.card V : ℝ) ≤ 3 * #Sᶜ := by exact_mod_cast (show _ ≤ _ by omega)
    have := G.edgeExpansion_mul_card_le hle
    rw [compl_compl, card_interedges_comm] at this
    nlinarith [G.edgeExpansion_nonneg]

end EdgeExpansion

section Dirichlet

/-- Summing a function of the first end of the darts counts every vertex `|D|` times. -/
private theorem sum_fst (g : V → ℝ) : ∑ p : V × D, g p.1 = Fintype.card D * ∑ v, g v := by
  rw [Fintype.sum_prod_type, mul_sum]
  simp only [sum_const, card_univ, nsmul_eq_mul]

/-- Summing a function of the second end of the darts counts every vertex `|D|` times. -/
private theorem sum_neighbor (g : V → ℝ) :
    ∑ p : V × D, g (G.neighbor p.1 p.2) = Fintype.card D * ∑ v, g v := by
  rw [← sum_fst]
  exact Fintype.sum_bijective G.rot G.rot_involutive.bijective _ _ fun p ↦ rfl

/-- The Dirichlet form: summed over the darts, the squared difference of `f` between the two ends
is `2 |V| |D| (𝔼 f² - 𝔼 f · G.walk f)`. -/
private theorem sum_sub_sq_eq (f : V → ℝ) :
    ∑ p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 =
      2 * Fintype.card V * Fintype.card D * (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) := by
  have h : ∑ p : V × D, f p.1 * f (G.neighbor p.1 p.2) =
      Fintype.card V * Fintype.card D * 𝔼 v, f v * G.walk f v := by
    rw [Fintype.sum_prod_type, mul_assoc, mul_expect, Fintype.card_mul_expect]
    refine sum_congr rfl fun v _ ↦ ?_
    rw [walk_apply, mul_left_comm, Fintype.card_mul_expect, mul_sum]
  calc
    _ = ∑ p : V × D, (f p.1 ^ 2 + f (G.neighbor p.1 p.2) ^ 2 -
          2 * (f p.1 * f (G.neighbor p.1 p.2))) := sum_congr rfl fun _ _ ↦ by ring
    _ = _ := by
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, h, sum_fst fun v ↦ f v ^ 2,
        G.sum_neighbor fun v ↦ f v ^ 2, ← Fintype.card_mul_expect]
      ring

end Dirichlet

section Median

/-- A median: some value has at most half of the vertices strictly above it and at most half
strictly below it. -/
private theorem exists_median (f : V → ℝ) :
    ∃ m : ℝ, 2 * #{v | m < f v} ≤ Fintype.card V ∧ 2 * #{v | f v < m} ≤ Fintype.card V := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨v₀, -, hlo, hhi⟩ := univ.exists_median univ_nonempty f
  have h₁ := card_filter_add_card_filter_not (s := univ) fun w ↦ f w ≤ f v₀
  have h₂ := card_filter_add_card_filter_not (s := univ) fun w ↦ f v₀ ≤ f w
  simp only [not_le, card_univ] at hlo hhi h₁ h₂
  exact ⟨f v₀, by omega, by omega⟩

/-- The positive and negative parts of two reals are closer than the reals themselves. -/
private theorem sq_max_sub_max_add_sq_max_sub_max_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
  simp only [max_eq_left, max_eq_right, ha, hb, neg_nonneg, neg_nonpos] <;> nlinarith

/-- The square of a real is the sum of the squares of its positive and negative parts. -/
private theorem sq_max_add_sq_max (a : ℝ) : max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by
  rcases le_total a 0 with ha | ha <;>
  simp only [max_eq_left, max_eq_right, ha, neg_nonneg, neg_nonpos] <;> ring

end Median

section Cheeger

variable [DecidableEq V]

/-- **The easy half of Cheeger's inequality**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09]: on at least two vertices,
`|D| (1 - λ₂(G)) / 2 ≤ h(G)`. -/
theorem card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion [Nontrivial V] :
    Fintype.card D * (1 - G.secondEigenvalue) / 2 ≤ G.edgeExpansion := by
  refine G.le_edgeExpansion_iff.2 fun S hS ↦ le_trans ?_
    (G.le_card_interedges_compl_of_expect_mul_walk_le
      (fun _ hf ↦ G.expect_mul_walk_le_secondEigenvalue_mul hf) S)
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  have hc : (Fintype.card V : ℝ) ≤ 2 * #Sᶜ := by
    have := card_compl_add_card S
    exact_mod_cast (show Fintype.card V ≤ 2 * #Sᶜ by omega)
  have hA : 0 ≤ (1 - G.secondEigenvalue) * Fintype.card D * #S :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 G.secondEigenvalue_le_one) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ two_pos hn]
  nlinarith [mul_le_mul_of_nonneg_left hc hA]

variable {G} in
/-- By the easy half of Cheeger's inequality, a regular multigraph on at least two vertices of
spectral expansion at most `μ` has edge expansion at least `|D| (1 - μ) / 2`. -/
theorem le_edgeExpansion_of_spectralExpansion_le [Nontrivial V] {μ : ℝ}
    (hG : G.spectralExpansion ≤ μ) :
    Fintype.card D * (1 - μ) / 2 ≤ G.edgeExpansion := by
  refine le_trans ?_ G.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion
  have := G.secondEigenvalue_le_spectralExpansion.trans hG
  gcongr

open Classical in
/-- When `ψ ≥ 0` vanishes outside `T` and takes minimum `ψ v₀` on `T`, peeling `ψ v₀` on `T` splits
`|ψ p.1 - ψ (G.neighbor p.1 p.2)|` into the peeled difference plus `ψ v₀` on darts crossing `T`. -/
private theorem abs_sub_eq_add_mul_ite_interedges {T : Finset V} {ψ : V → ℝ}
    (hψ : ∀ v, 0 ≤ ψ v) (hT : ∀ v ∉ T, ψ v = 0) {v₀ : V} (hmin : ∀ v ∈ T, ψ v₀ ≤ ψ v)
    (p : V × D) :
    let ψ' : V → ℝ := fun v ↦ if v ∈ T then ψ v - ψ v₀ else 0
    |ψ p.1 - ψ (G.neighbor p.1 p.2)| =
      |ψ' p.1 - ψ' (G.neighbor p.1 p.2)| + ψ v₀ * ((if p ∈ G.interedges T Tᶜ then 1 else 0) +
        if p ∈ G.interedges Tᶜ T then 1 else 0) := by
  intro ψ'
  have hu := hmin p.1
  have hw := hmin (G.neighbor p.1 p.2)
  by_cases h₁ : p.1 ∈ T <;> by_cases h₂ : G.neighbor p.1 p.2 ∈ T
  · simp [ψ', h₁, h₂]
  · simp only [ψ', mem_interedges, mem_compl, h₁, h₂, hT _ h₂, ite_true, ite_false, not_true,
      not_false_eq_true, and_true, and_false, sub_zero, add_zero, mul_one]
    rw [abs_of_nonneg (hψ _), abs_of_nonneg (sub_nonneg.2 (hu h₁))]
    ring
  · simp only [ψ', mem_interedges, mem_compl, h₁, h₂, hT _ h₁, ite_true, ite_false, not_true,
      not_false_eq_true, and_true, and_false, zero_sub, zero_add, mul_one, abs_neg]
    rw [abs_of_nonneg (hψ _), abs_of_nonneg (sub_nonneg.2 (hw h₂))]
    ring
  · simp [ψ', h₁, h₂, hT _ h₁, hT _ h₂]

/-- **The co-area inequality.** If `ψ ≥ 0` vanishes outside `T` and at least `c |S|` edges leave
every `S ⊆ T`, then the variation `∑ |ψ u - ψ w|` of `ψ` over the darts `(u, w)` is at least
`2 c ∑ ψ`. Writing `ψ` as its least value `μ` on `T` times the indicator of `T` plus a function
vanishing outside a smaller set, the first part contributes `2 μ e(T, Tᶜ)` to the variation. -/
private theorem two_mul_mul_sum_le_sum_abs_sub {c : ℝ} (T : Finset V) {ψ : V → ℝ}
    (hψ : ∀ v, 0 ≤ ψ v) (hT : ∀ v ∉ T, ψ v = 0)
    (hc : ∀ S ⊆ T, c * #S ≤ #(G.interedges S Sᶜ)) :
    2 * c * ∑ v, ψ v ≤ ∑ p : V × D, |ψ p.1 - ψ (G.neighbor p.1 p.2)| := by
  classical
  induction T using Finset.strongInduction generalizing ψ with | H T ih =>
  rcases T.eq_empty_or_nonempty with rfl | hne
  · have h0 : ∀ v, ψ v = 0 := fun v ↦ hT v (notMem_empty v)
    simp only [h0, sum_const_zero, mul_zero, sub_zero, abs_zero, le_refl]
  obtain ⟨v₀, hv₀, hmin⟩ := T.exists_min_image ψ hne
  set ψ' : V → ℝ := fun v ↦ if v ∈ T then ψ v - ψ v₀ else 0 with hψ'_def
  have hψ' (v : V) : 0 ≤ ψ' v := by
    by_cases hv : v ∈ T
    · simpa [ψ', hv] using hmin v hv
    · simp [ψ', hv]
  have hT' (v : V) (hv : v ∉ T.erase v₀) : ψ' v = 0 := by
    rw [mem_erase, not_and_or, not_ne_iff] at hv
    rcases hv with rfl | hv
    · simp [ψ', hv₀]
    · simp [ψ', hv]
  have ih' := ih _ (erase_ssubset hv₀) hψ' hT' fun S hS ↦ hc S (hS.trans (erase_subset _ _))
  have hsum : ∑ v, ψ' v = ∑ v, ψ v - #T * ψ v₀ := by
    rw [hψ'_def, sum_ite_mem, univ_inter, sum_sub_distrib, sum_const, nsmul_eq_mul,
      sum_subset (subset_univ T) fun v _ hv ↦ hT v hv]
  have he : ∑ p : V × D, ((if p ∈ G.interedges T Tᶜ then (1 : ℝ) else 0) +
      if p ∈ G.interedges Tᶜ T then 1 else 0) = 2 * #(G.interedges T Tᶜ) := by
    rw [sum_add_distrib, sum_boole, sum_boole, filter_mem_eq_inter, filter_mem_eq_inter,
      univ_inter, univ_inter, ← G.card_interedges_comm T Tᶜ]
    ring
  rw [sum_congr rfl fun p _ ↦ G.abs_sub_eq_add_mul_ite_interedges hψ hT hmin p, sum_add_distrib,
    ← mul_sum, he]
  have hμ := mul_le_mul_of_nonneg_left (hc T subset_rfl) (hψ v₀)
  rw [hsum] at ih'
  linarith

/-- If `φ ≥ 0` vanishes outside `T` and at least `c |S|` edges leave every `S ⊆ T`, where
`c ≥ 0`, then `c² ∑ φ² ≤ |D| ∑ (φ u - φ w)²` over the darts `(u, w)`: the co-area inequality for
`φ²` and the Cauchy–Schwarz inequality. -/
private theorem sq_mul_sum_sq_le {c : ℝ} (hc₀ : 0 ≤ c) (T : Finset V) {φ : V → ℝ}
    (hφ : ∀ v, 0 ≤ φ v) (hT : ∀ v ∉ T, φ v = 0)
    (hc : ∀ S ⊆ T, c * #S ≤ #(G.interedges S Sᶜ)) :
    c ^ 2 * ∑ v, φ v ^ 2 ≤
      Fintype.card D * ∑ p : V × D, (φ p.1 - φ (G.neighbor p.1 p.2)) ^ 2 := by
  have h₁ := G.two_mul_mul_sum_le_sum_abs_sub T (ψ := fun v ↦ φ v ^ 2) (fun v ↦ sq_nonneg _)
    (fun v hv ↦ by rw [hT v hv, sq, mul_zero]) hc
  have h₂ (p : V × D) : |φ p.1 ^ 2 - φ (G.neighbor p.1 p.2) ^ 2| =
      |φ p.1 - φ (G.neighbor p.1 p.2)| * (φ p.1 + φ (G.neighbor p.1 p.2)) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hφ _) (hφ _)), mul_comm]
  simp only [h₂] at h₁
  have h₃ := sum_mul_sq_le_sq_mul_sq univ (fun p : V × D ↦ |φ p.1 - φ (G.neighbor p.1 p.2)|)
    fun p ↦ φ p.1 + φ (G.neighbor p.1 p.2)
  simp only [sq_abs] at h₃
  have h₄ : ∑ p : V × D, (φ p.1 + φ (G.neighbor p.1 p.2)) ^ 2 ≤
      4 * Fintype.card D * ∑ v, φ v ^ 2 := by
    calc
      _ ≤ ∑ p : V × D, 2 * (φ p.1 ^ 2 + φ (G.neighbor p.1 p.2) ^ 2) :=
        sum_le_sum fun p _ ↦ by nlinarith [sq_nonneg (φ p.1 - φ (G.neighbor p.1 p.2))]
      _ = _ := by
        rw [← mul_sum, sum_add_distrib, sum_fst fun v ↦ φ v ^ 2,
          G.sum_neighbor fun v ↦ φ v ^ 2]
        ring
  have hA : 0 ≤ ∑ v, φ v ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hE : 0 ≤ ∑ p : V × D, (φ p.1 - φ (G.neighbor p.1 p.2)) ^ 2 :=
    sum_nonneg fun _ _ ↦ sq_nonneg _
  have h₅ := (pow_le_pow_left₀ (by positivity) h₁ 2).trans
    (h₃.trans (mul_le_mul_of_nonneg_left h₄ hE))
  rcases hA.eq_or_lt with hA | hA
  · rw [← hA, mul_zero]
    positivity
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 4 * ∑ v, φ v ^ 2)
  linarith

/-- The hard half of Cheeger's inequality in sums: for `f` summing to zero,
`c² ∑ f² ≤ |D| ∑ (f u - f w)²` over the darts `(u, w)`, if `c ≥ 0` and at least `c |S|` edges
leave every set `S` of at most half of the vertices. Split `f` at a median `m`: the positive and
negative parts of `f - m` vanish outside sets of at most half of the vertices. -/
private theorem sq_mul_sum_sq_le_of_sum_eq_zero {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ #(G.interedges S Sᶜ))
    {f : V → ℝ} (hf : ∑ v, f v = 0) :
    c ^ 2 * ∑ v, f v ^ 2 ≤
      Fintype.card D * ∑ p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_median f
  have hp := G.sq_mul_sum_sq_le hc₀ {v | m < f v} (φ := fun v ↦ max (f v - m) 0)
    (fun v ↦ le_max_right _ _)
    (fun v hv ↦ max_eq_right (sub_nonpos.2 (not_lt.1 fun h ↦ hv (mem_filter.2 ⟨mem_univ v, h⟩))))
    fun S hS ↦ hc S ((Nat.mul_le_mul_left 2 (card_le_card hS)).trans hm₁)
  have hn := G.sq_mul_sum_sq_le hc₀ {v | f v < m} (φ := fun v ↦ max (-(f v - m)) 0)
    (fun v ↦ le_max_right _ _)
    (fun v hv ↦ max_eq_right (neg_nonpos.2 (sub_nonneg.2
      (not_lt.1 fun h ↦ hv (mem_filter.2 ⟨mem_univ v, h⟩)))))
    fun S hS ↦ hc S ((Nat.mul_le_mul_left 2 (card_le_card hS)).trans hm₂)
  have hsq : ∑ v, f v ^ 2 ≤ ∑ v, max (f v - m) 0 ^ 2 + ∑ v, max (-(f v - m)) 0 ^ 2 := by
    rw [← sum_add_distrib]
    simp only [sq_max_add_sq_max]
    calc
      _ ≤ ∑ v, f v ^ 2 + Fintype.card V * m ^ 2 := le_add_of_nonneg_right (by positivity)
      _ = _ := by
        simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hf, sum_const,
          card_univ, nsmul_eq_mul]
        ring
  have hdir : ∑ p : V × D, (max (f p.1 - m) 0 - max (f (G.neighbor p.1 p.2) - m) 0) ^ 2 +
      ∑ p : V × D, (max (-(f p.1 - m)) 0 - max (-(f (G.neighbor p.1 p.2) - m)) 0) ^ 2 ≤
        ∑ p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun p _ ↦ (sq_max_sub_max_add_sq_max_sub_max_le _ _).trans_eq (by ring)
  have hd : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg c), mul_le_mul_of_nonneg_left hdir hd]

/-- **Edge expansion bounds the second eigenvalue**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09]: if `c ≥ 0` and at least `c |S|` edges leave every set
`S` of at most half of the vertices, then `𝔼 v, f v * G.walk f v ≤ (1 - c ^ 2 / (2 |D| ^ 2)) 𝔼 f²`
for every `f` of expectation zero. This is the hard half of the discrete Cheeger inequality in
one-sided form, converse to `le_card_interedges_compl_of_expect_mul_walk_le`. -/
theorem expect_mul_walk_le_of_mul_card_le_card_interedges_compl {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ #(G.interedges S Sᶜ))
    {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, f v * G.walk f v ≤ (1 - c ^ 2 / (2 * Fintype.card D ^ 2)) * 𝔼 v, f v ^ 2 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have hW (v : V) : G.walk f v = 0 := by rw [walk_apply, univ_eq_empty, expect_empty]
    simp only [hW, mul_zero, expect_const_zero, Fintype.card_eq_zero, Nat.cast_zero]
    rw [zero_pow two_ne_zero, mul_zero, div_zero, sub_zero, one_mul]
    exact expect_nonneg fun _ _ ↦ sq_nonneg _
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  have key := G.sq_mul_sum_sq_le_of_sum_eq_zero hc₀ hc (f := f)
    (by rw [← Fintype.card_mul_expect, hf, mul_zero])
  rw [G.sum_sub_sq_eq, ← Fintype.card_mul_expect fun v ↦ f v ^ 2] at key
  have key' : c ^ 2 * 𝔼 v, f v ^ 2 ≤
      2 * Fintype.card D ^ 2 * (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) := by
    refine le_of_mul_le_mul_left ?_ hn
    linarith
  have h : c ^ 2 / (2 * Fintype.card D ^ 2) * 𝔼 v, f v ^ 2 ≤
      𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v := by
    rw [div_mul_eq_mul_div, div_le_iff₀' (by positivity)]
    exact key'
  linarith

/-- **The hard half of Cheeger's inequality**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09], as a bound on the second eigenvalue:
`λ₂(G) ≤ 1 - h(G) ^ 2 / (2 |D| ^ 2)`. -/
theorem secondEigenvalue_le_one_sub_edgeExpansion_sq_div :
    G.secondEigenvalue ≤ 1 - G.edgeExpansion ^ 2 / (2 * Fintype.card D ^ 2) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.secondEigenvalue_eq_zero_of_subsingleton, G.edgeExpansion_eq_zero_of_subsingleton,
      zero_pow two_ne_zero, zero_div, sub_zero]
    exact zero_le_one
  exact G.secondEigenvalue_le_iff.2 fun _ ↦
    G.expect_mul_walk_le_of_mul_card_le_card_interedges_compl G.edgeExpansion_nonneg
      fun _ ↦ G.edgeExpansion_mul_card_le

/-- **The hard half of Cheeger's inequality**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09], squared: `h(G) ^ 2 ≤ 2 |D| ^ 2 (1 - λ₂(G))`. -/
theorem edgeExpansion_sq_le :
    G.edgeExpansion ^ 2 ≤ 2 * Fintype.card D ^ 2 * (1 - G.secondEigenvalue) := by
  rcases (Fintype.card D).eq_zero_or_pos with hD | hD
  · have h := G.edgeExpansion_le_card
    rw [hD, Nat.cast_zero] at h ⊢
    rw [le_antisymm h G.edgeExpansion_nonneg]
    simp
  have h := G.secondEigenvalue_le_one_sub_edgeExpansion_sq_div
  rw [← div_le_iff₀' (by positivity)]
  linarith

/-- **The hard half of Cheeger's inequality**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]
[Arora and Barak, Section 21.2][AroraBarak09]: `h(G) ≤ |D| √(2 (1 - λ₂(G)))`. -/
theorem edgeExpansion_le_card_mul_sqrt :
    G.edgeExpansion ≤ Fintype.card D * √(2 * (1 - G.secondEigenvalue)) := by
  rw [← Real.sqrt_sq (Nat.cast_nonneg (Fintype.card D)), ← Real.sqrt_mul (sq_nonneg _),
    ← mul_assoc, mul_comm (_ ^ 2 : ℝ) 2]
  exact (le_abs_self _).trans (Real.abs_le_sqrt G.edgeExpansion_sq_le)

end Cheeger

end Cslib.RotationMap
