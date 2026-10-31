/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cuts of weighted multigraphs

An undirected weighted multigraph without self-loops on a finite vertex type `V` is given here by
its symmetric weight matrix `W : V → V → ℕ` with zero diagonal (`Cslib.WeightedCut.IsMultigraph`):
`W u v` is the total weight, or the number of parallel edges, joining distinct `u` and `v`. A set
`C` of vertices with `C` and its complement both nonempty is a non-trivial cut, its weight is the
total weight of the edges between `C` and its complement, and the global minimum cut weight is the
least weight of a non-trivial cut.

Contracting a multigraph along a surjective map `part : V → U` of the vertices onto supervertices
sums the weights between the vertices sent to distinct supervertices
(`Cslib.WeightedCut.IsContractionOf`). Pulling a cut of the contracted multigraph back to the
original vertices gives a cut of the same weight (`Cslib.WeightedCut.cutWeight_pullbackCut`), so
contraction never decreases the global minimum cut weight. Karger's contraction algorithm and the
Karger–Stein algorithm (`Complexity.Algorithms.WordRAM.Karger.Graph`) are built on these facts.

The multigraphs given by their ends (`Cslib.Multigraph`) have weight matrices with the same cut
weights; see `Complexity.Foundations.Combinatorics.WeightedCut.Multigraph`.

## Main definitions

* `Cslib.WeightedCut.IsMultigraph`: a symmetric weight matrix with zero diagonal.
* `Cslib.WeightedCut.IsNonTrivialCut`: a set of vertices whose complement is also nonempty.
* `Cslib.WeightedCut.cutWeight`, `Cslib.WeightedCut.minCut`: cut weights and the global minimum cut
  weight.
* `Cslib.WeightedCut.rowDeg`, `Cslib.WeightedCut.totalDoubledWeight`: weighted degrees and their
  sum, twice the total edge weight.
* `Cslib.WeightedCut.pullbackCut`, `Cslib.WeightedCut.IsContractionOf`: cuts pulled back along a
  supervertex map, and contracted multigraphs.

## Main results

* `Cslib.WeightedCut.cutWeight_compl`: a cut and its complement have the same weight.
* `Cslib.WeightedCut.cutWeight_singleton`: a singleton cut weighs the degree of its vertex.
* `Cslib.WeightedCut.le_minCut_iff`: with at least two vertices, `m ≤ minCut W` exactly when every
  non-trivial cut weighs at least `m`.
* `Cslib.WeightedCut.mul_minCut_le_totalDoubledWeight`: `|V| * minCut W` is at most the sum of the
  degrees.
* `Cslib.WeightedCut.cutWeight_pullbackCut`: pulling a cut back along a contraction preserves its
  weight.
* `Cslib.WeightedCut.minCut_le_of_isContractionOf`: contraction does not decrease the global
  minimum cut weight.
* `Cslib.WeightedCut.two_vertex_contraction_output`: a contraction to two supervertices gives a
  non-trivial cut of the original multigraph whose weight is the remaining edge weight.
-/

@[expose] public section

namespace Cslib.WeightedCut

variable {V U : Type*}

/-! ### Weighted multigraphs and global minimum cuts -/

/-- An undirected weighted multigraph without self-loops on the vertices `V` is a symmetric weight
matrix `W : V → V → ℕ` with zero diagonal. -/
def IsMultigraph (W : V → V → ℕ) : Prop :=
  (∀ u v, W u v = W v u) ∧ (∀ u, W u u = 0)

variable [Fintype V]

/-- A vertex subset `C` defines a non-trivial cut when both `C` and its complement are
nonempty. -/
def IsNonTrivialCut (C : Finset V) : Prop :=
  C.Nonempty ∧ C ≠ Finset.univ

theorem isNonTrivialCut_iff_card (C : Finset V) :
    IsNonTrivialCut C ↔ 0 < C.card ∧ C.card < Fintype.card V := by
  unfold IsNonTrivialCut
  rw [Finset.card_pos, Finset.card_lt_iff_ne_univ]

theorem isNonTrivialCut_singleton (hV : 2 ≤ Fintype.card V) (a : V) :
    IsNonTrivialCut ({a} : Finset V) := by
  rw [isNonTrivialCut_iff_card]
  simp only [Finset.card_singleton]
  omega

theorem exists_isNonTrivialCut (hV : 2 ≤ Fintype.card V) :
    ∃ C : Finset V, IsNonTrivialCut C := by
  obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact ⟨{a}, isNonTrivialCut_singleton hV a⟩

/-- Weighted degree of vertex `u` in `W`. -/
def rowDeg (W : V → V → ℕ) (u : V) : ℕ :=
  ∑ v : V, W u v

/-- Sum of all row degrees `∑ u, ∑ v, W u v`, equal to twice the total edge weight of `W`. -/
def totalDoubledWeight (W : V → V → ℕ) : ℕ :=
  ∑ u : V, rowDeg W u

theorem entry_le_rowDeg (W : V → V → ℕ) (u v : V) :
    W u v ≤ rowDeg W u :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

theorem rowDeg_le_totalDoubledWeight (W : V → V → ℕ) (u : V) :
    rowDeg W u ≤ totalDoubledWeight W :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)

theorem entry_le_totalDoubledWeight (W : V → V → ℕ) (u v : V) :
    W u v ≤ totalDoubledWeight W :=
  (entry_le_rowDeg W u v).trans (rowDeg_le_totalDoubledWeight W u)

section Cut

variable [DecidableEq V]

theorem isNonTrivialCut_compl {C : Finset V} (hC : IsNonTrivialCut C) :
    IsNonTrivialCut (Finset.univ \ C) := by
  rcases hC with ⟨⟨x, hx⟩, hnu⟩
  refine ⟨?_, ?_⟩
  · by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
    exact hnu (Finset.eq_univ_of_forall fun y => h_empty (Finset.mem_univ y))
  · intro huniv
    have hx' : x ∈ Finset.univ \ C := by
      rw [huniv]
      exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp hx').2 hx

/-- Total weight of edges crossing `(C, Finset.univ \ C)`. -/
def cutWeight (W : V → V → ℕ) (C : Finset V) : ℕ :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, W u v

theorem cutWeight_compl {W : V → V → ℕ} (hW : IsMultigraph W) (C : Finset V) :
    cutWeight W (Finset.univ \ C) = cutWeight W C := by
  unfold cutWeight
  have hsdiff : Finset.univ \ (Finset.univ \ C) = C := by
    ext x
    simp
  rw [hsdiff, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hW.1 v u

theorem cutWeight_le_sum_rowDeg (W : V → V → ℕ) (C : Finset V) :
    cutWeight W C ≤ ∑ u ∈ C, rowDeg W u := by
  unfold cutWeight rowDeg
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

theorem two_mul_cutWeight_le_totalDoubledWeight {W : V → V → ℕ} (hW : IsMultigraph W)
    (C : Finset V) :
    2 * cutWeight W C ≤ totalDoubledWeight W := by
  have hdisj : Disjoint C (Finset.univ \ C) := Finset.disjoint_sdiff
  have hunion : C ∪ (Finset.univ \ C) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ C)
  have h1 := cutWeight_le_sum_rowDeg W C
  have h2 := cutWeight_le_sum_rowDeg W (Finset.univ \ C)
  rw [cutWeight_compl hW C] at h2
  have hsum : (∑ u ∈ C, rowDeg W u) + (∑ u ∈ Finset.univ \ C, rowDeg W u) =
      totalDoubledWeight W := by
    unfold totalDoubledWeight
    rw [← Finset.sum_union hdisj, hunion]
  omega

theorem cutWeight_singleton {W : V → V → ℕ} (hW : IsMultigraph W) (a : V) :
    cutWeight W {a} = rowDeg W a := by
  unfold cutWeight rowDeg
  rw [Finset.sum_singleton]
  have hsplit : (Finset.univ : Finset V) = insert a (Finset.univ \ {a}) := by
    ext x
    simp
  conv_rhs => rw [hsplit, Finset.sum_insert (by simp)]
  rw [hW.2 a, zero_add]

theorem cutWeight_two_singleton_zero {W : Fin 2 → Fin 2 → ℕ} (hW : IsMultigraph W) :
    cutWeight W ({0} : Finset (Fin 2)) = W 0 1 := by
  rw [cutWeight_singleton hW 0]
  unfold rowDeg
  rw [Fin.sum_univ_two, hW.2 0, zero_add]

/-- Global minimum cut weight of a multigraph `W`, defined as the greatest lower bound of
`cutWeight W C` over all non-trivial cuts `C`. -/
noncomputable def minCut (W : V → V → ℕ) : ℕ :=
  sInf {k | ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = k}

theorem minCut_le_cutWeight (W : V → V → ℕ) {C : Finset V} (hC : IsNonTrivialCut C) :
    minCut W ≤ cutWeight W C :=
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minCut_achiever (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) :
    ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = minCut W := by
  rcases exists_isNonTrivialCut hV with ⟨C₀, hC₀⟩
  have hne : {k | ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = k}.Nonempty :=
    ⟨cutWeight W C₀, C₀, hC₀, rfl⟩
  exact Nat.sInf_mem hne

theorem le_minCut_iff (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) (m : ℕ) :
    m ≤ minCut W ↔ ∀ C : Finset V, IsNonTrivialCut C → m ≤ cutWeight W C := by
  constructor
  · intro hm C hC
    exact hm.trans (minCut_le_cutWeight W hC)
  · intro h
    rcases exists_minCut_achiever hV W with ⟨C, hC, hEq⟩
    exact hEq ▸ h C hC

theorem minCut_pos_iff (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) :
    0 < minCut W ↔ ∀ C : Finset V, IsNonTrivialCut C → 0 < cutWeight W C :=
  le_minCut_iff hV W 1

theorem minCut_le_rowDeg (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ} (hW : IsMultigraph W)
    (a : V) :
    minCut W ≤ rowDeg W a := by
  rw [← cutWeight_singleton hW a]
  exact minCut_le_cutWeight W (isNonTrivialCut_singleton hV a)

theorem mul_minCut_le_totalDoubledWeight (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ}
    (hW : IsMultigraph W) :
    Fintype.card V * minCut W ≤ totalDoubledWeight W := by
  unfold totalDoubledWeight
  calc
    Fintype.card V * minCut W = ∑ _u : V, minCut W := by simp
    _ ≤ ∑ u : V, rowDeg W u := Finset.sum_le_sum fun u _ => minCut_le_rowDeg hV hW u

theorem totalDoubledWeight_pos_of_minCut_pos (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ}
    (hW : IsMultigraph W) (hpos : 0 < minCut W) :
    0 < totalDoubledWeight W := by
  have hmul : 0 < Fintype.card V * minCut W := Nat.mul_pos (by omega) hpos
  exact lt_of_lt_of_le hmul (mul_minCut_le_totalDoubledWeight hV hW)

end Cut

/-! ### Supervertex maps and contractions -/

variable [DecidableEq U]

/-- Pull back a cut `B` of the supervertices along a supervertex map `part : V → U`. -/
def pullbackCut (part : V → U) (B : Finset U) : Finset V :=
  Finset.univ.filter fun x => part x ∈ B

theorem mem_pullbackCut (part : V → U) (B : Finset U) (x : V) :
    x ∈ pullbackCut part B ↔ part x ∈ B := by
  simp [pullbackCut]

theorem pullbackCut_empty (part : V → U) :
    pullbackCut part ∅ = ∅ := by
  ext x
  simp [pullbackCut]

/-- `W : U → U → ℕ` is the contracted multigraph of `W₀ : V → V → ℕ` along the surjective
supervertex assignment `part : V → U`: the weight between distinct supervertices is the total
weight between the vertices sent to them. -/
structure IsContractionOf (W₀ : V → V → ℕ) (part : V → U) (W : U → U → ℕ) : Prop where
  surj : Function.Surjective part
  multigraph : IsMultigraph W
  offDiag : ∀ a b : U, a ≠ b →
    W a b = ∑ x ∈ Finset.univ.filter (part · = a),
      ∑ y ∈ Finset.univ.filter (part · = b), W₀ x y

variable [Fintype U]

theorem pullbackCut_univ (part : V → U) :
    pullbackCut part Finset.univ = Finset.univ := by
  ext x
  simp [pullbackCut]

theorem isNonTrivialCut_pullbackCut {part : V → U} (hsurj : Function.Surjective part)
    {B : Finset U} (hB : IsNonTrivialCut B) :
    IsNonTrivialCut (pullbackCut part B) := by
  rcases hB with ⟨⟨b, hb⟩, hnu⟩
  rcases hsurj b with ⟨x, rfl⟩
  refine ⟨⟨x, by simp [pullbackCut, hb]⟩, fun hall => hnu ?_⟩
  refine Finset.eq_univ_of_forall fun b' => ?_
  rcases hsurj b' with ⟨y, rfl⟩
  have hy : y ∈ pullbackCut part B := hall ▸ Finset.mem_univ y
  simpa [pullbackCut] using hy

theorem isNonTrivialCut_of_pullbackCut (part : V → U) {B : Finset U}
    (h : IsNonTrivialCut (pullbackCut part B)) :
    IsNonTrivialCut B := by
  rcases h with ⟨hne, hnu⟩
  refine ⟨?_, ?_⟩
  · rcases hne with ⟨x, hx⟩
    exact ⟨part x, (mem_pullbackCut part B x).mp hx⟩
  · intro hBu
    subst hBu
    exact hnu (pullbackCut_univ part)

variable [DecidableEq V]

theorem pullbackCut_compl (part : V → U) (B : Finset U) :
    pullbackCut part (Finset.univ \ B) = Finset.univ \ pullbackCut part B := by
  ext x
  simp [pullbackCut]

theorem isContractionOf_id {W₀ : V → V → ℕ} (hW₀ : IsMultigraph W₀) :
    IsContractionOf W₀ id W₀ where
  surj := Function.surjective_id
  multigraph := hW₀
  offDiag a b _ := by
    have hfa : (Finset.univ.filter fun x : V => id x = a) = {a} := by ext x; simp
    have hfb : (Finset.univ.filter fun y : V => id y = b) = {b} := by ext y; simp
    rw [hfa, hfb, Finset.sum_singleton, Finset.sum_singleton]

theorem cutWeight_pullbackCut {W₀ : V → V → ℕ} {part : V → U} {W : U → U → ℕ}
    (hC : IsContractionOf W₀ part W) (B : Finset U) :
    cutWeight W₀ (pullbackCut part B) = cutWeight W B := by
  unfold cutWeight
  rw [← pullbackCut_compl]
  have hdecomp : ∀ S : Finset U, ∀ f : V → ℕ,
      ∑ x ∈ pullbackCut part S, f x =
        ∑ a ∈ S, ∑ x ∈ Finset.univ.filter (part · = a), f x := by
    intro S f
    unfold pullbackCut
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x
      simp
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro x rfl hxb
      exact hab hxb
  rw [hdecomp B]
  refine Finset.sum_congr rfl fun a ha => ?_
  calc
    ∑ x ∈ Finset.univ.filter (part · = a), ∑ y ∈ pullbackCut part (Finset.univ \ B), W₀ x y
      = ∑ x ∈ Finset.univ.filter (part · = a),
          ∑ b ∈ Finset.univ \ B, ∑ y ∈ Finset.univ.filter (part · = b), W₀ x y := by
        refine Finset.sum_congr rfl fun x _ => hdecomp (Finset.univ \ B) (W₀ x)
    _ = ∑ b ∈ Finset.univ \ B,
          ∑ x ∈ Finset.univ.filter (part · = a), ∑ y ∈ Finset.univ.filter (part · = b), W₀ x y :=
        Finset.sum_comm
    _ = ∑ b ∈ Finset.univ \ B, W a b := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hab : a ≠ b := by
          intro hEq
          subst hEq
          exact (Finset.mem_sdiff.mp hb).2 ha
        exact (hC.offDiag a b hab).symm

theorem minCut_le_of_isContractionOf (hU : 2 ≤ Fintype.card U) {W₀ : V → V → ℕ}
    {part : V → U} {W : U → U → ℕ} (hC : IsContractionOf W₀ part W) :
    minCut W₀ ≤ minCut W := by
  rw [le_minCut_iff hU W]
  intro B hB
  rw [← cutWeight_pullbackCut hC B]
  exact minCut_le_cutWeight W₀ (isNonTrivialCut_pullbackCut hC.surj hB)

theorem two_vertex_contraction_output {W₀ : V → V → ℕ} {part : V → Fin 2}
    {W : Fin 2 → Fin 2 → ℕ} (hC : IsContractionOf W₀ part W) :
    IsNonTrivialCut (pullbackCut part ({0} : Finset (Fin 2))) ∧
      W 0 1 = cutWeight W₀ (pullbackCut part ({0} : Finset (Fin 2))) ∧
      minCut W₀ ≤ W 0 1 := by
  have hnt : IsNonTrivialCut (pullbackCut part ({0} : Finset (Fin 2))) :=
    isNonTrivialCut_pullbackCut hC.surj (isNonTrivialCut_singleton (by simp) 0)
  have hcw : cutWeight W₀ (pullbackCut part ({0} : Finset (Fin 2))) = W 0 1 := by
    rw [cutWeight_pullbackCut hC, cutWeight_two_singleton_zero hC.multigraph]
  exact ⟨hnt, hcw.symm, hcw ▸ minCut_le_cutWeight W₀ hnt⟩

end Cslib.WeightedCut
