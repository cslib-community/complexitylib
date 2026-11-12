/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Complexity.FineGrained.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Clause-Grouping Reduction from 3-SAT to Clique and ETH Lower Bounds

This file formalizes the clause-grouping reduction from `ThreeSAT` to `Clique` of Cygan et al.,
*Parameterized Algorithms* (2016-05-30 companion PDF,
https://parameterized-algorithms.mimuw.edu.pl/parameterized-algorithms.pdf).
The nice-tree definitions and Lemma 7.4 are at printed p.161; Theorem 14.21
and its proof are at pp.485–487.
The source proof of Theorem 14.21 groups 3-Coloring vertices and computes a group count from a
computable `f` to obtain one `2^o(n)` algorithm. This formalization adapts the argument to group
3-CNF clauses and chooses a fixed `r` separately for each target rate, accommodating arbitrary
real `f` and the library's `∀ rate ∃ machine` convention for subexponential bounding.
The generic CSP-counting DP extension is also an adaptation/original implementation.
Given a grouping parameter `r ≥ 1` and a 3-CNF formula `φ` with `m = φ.length` clauses,
partitioning `φ` into `r` blocks of at most
`⌈m / r⌉ = (m + r - 1) / r` clauses yields a graph `G` with at most `r * 2 ^ (3 * ⌈m / r⌉)`
vertices (one vertex per satisfying partial assignment to a block, with edges between compatible
assignments in distinct blocks) such that `(G, r) ∈ Clique ↔ φ ∈ ThreeSAT`.

Uniformity of the padded polynomial-time reduction over `(r, φ)` gives an
`O(2 ^ (O(m / r)) * poly)` construction whose polynomial exponent `D` is independent of `r`.
Choosing `r` sufficiently large transfers any `f(k) * |V| ^ o(k) * poly(|enc|)` or
`f(k) * |enc| ^ o(k)` algorithm for `Clique` to a subexponential-time algorithm for `ThreeSAT`
parameterized by `φ.length`, contradicting `ETH` (and in particular showing `Clique ∉ FPT`).

## Main definitions

* `Cslib.Complexity.SAT.groupClique`: the clause-grouping reduction mapping `(r, φ)` to `(G, r)`.

## Main results

* `Cslib.Complexity.SAT.groupClique_mem_Clique_iff`: correctness for all `r ≥ 1` and `φ : CNF ℕ`.
* `Cslib.Complexity.SAT.length_groupClique_vertices_le`:
  `|V(G)| ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r))`.
* `Cslib.Complexity.SAT.exists_computableInO_groupClique`: uniform runtime/size bound in
  `(r, φ)` via `ComputableInPolyTime.exists_computableInO_pad`.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_clique_subexpVertex`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_clique_subexpEnc`: unconditional transfers to
  subexponential `ThreeSAT` algorithms.
* `Cslib.Complexity.ETH.not_clique_subexpVertex`,
  `Cslib.Complexity.ETH.not_clique_subexpEnc`, `Cslib.Complexity.ETH.clique_not_mem_FPT`:
  `ETH`-conditional lower bounds ruling out `f(k) * n ^ o(k) * poly` and `FPT` algorithms for
  `Clique`.

## References

* Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk,
  Michał Pilipczuk, and Saket Saurabh, *Parameterized Algorithms* (2015).
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM

namespace Cslib.Complexity

namespace SAT

namespace GroupClique

/-- Upper bound on the number of clauses in each of `r` contiguous blocks of `φ`. -/
@[expose] def blockSize (φ : CNF ℕ) (r : ℕ) : ℕ :=
  (φ.length + r - 1) / r

/-- The `i`-th contiguous block of at most `blockSize φ r` clauses of `φ`. -/
@[expose] def block (φ : CNF ℕ) (r i : ℕ) : CNF ℕ :=
  (φ.drop (i * blockSize φ r)).take (blockSize φ r)

/-- Compatibility check between partial assignments `a₁` on `vs₁` and `a₂` on `vs₂`. -/
@[expose] def compat (vs₁ vs₂ : List ℕ) (a₁ a₂ : ℕ) : Bool :=
  vs₁.all fun x => !vs₂.contains x || (bitsAssignment vs₁ a₁ x == bitsAssignment vs₂ a₂ x)

/-- Encodes `(i, a)` as a vertex `i * bound + a`. -/
@[expose] def vertex (bound i a : ℕ) : ℕ :=
  i * bound + a

/-- Vertices for block assignments satisfying each block within `bound` codes per block. -/
@[expose] def verticesOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : List ℕ :=
  (List.range r).flatMap fun i =>
    let b := block φ r i
    let vs := b.distinctVars
    ((List.range bound).filter fun a => b.eval (bitsAssignment vs a)).map (vertex bound i)

/-- Edges between compatible satisfying assignments in distinct blocks. -/
@[expose] def edgesOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : List (ℕ × ℕ) :=
  (List.range r).flatMap fun i =>
    let b₁ := block φ r i
    let vs₁ := b₁.distinctVars
    (List.range bound).flatMap fun a =>
      if !b₁.eval (bitsAssignment vs₁ a) then []
      else
        (List.range r).flatMap fun j =>
          if j == i then []
          else
            let b₂ := block φ r j
            let vs₂ := b₂.distinctVars
            ((List.range bound).filter fun b =>
              b₂.eval (bitsAssignment vs₂ b) && compat vs₁ vs₂ a b).map
                fun b => (vertex bound i a, vertex bound j b)

/-- Reduction graph paired with clique target `r` using an explicit code bound `bound`. -/
@[expose] def graphOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : Graph × ℕ :=
  if r == 0 then
    (⟨[], []⟩, 1)
  else if !φ.all (fun c => decide (c.length ≤ 3)) then
    (⟨[], []⟩, r)
  else
    (⟨verticesOfBound r φ bound, edgesOfBound r φ bound⟩, r)

end GroupClique

/-- Clause-grouping reduction from `ThreeSAT` to `Clique` with block count `r`. -/
@[expose] def groupClique (r : ℕ) (φ : CNF ℕ) : Graph × ℕ :=
  GroupClique.graphOfBound r φ (2 ^ (3 * GroupClique.blockSize φ r))

/-! ### Block cover and variable-count bounds -/

private lemma blockSize_mul_ge {m r : ℕ} (hr : 1 ≤ r) :
    m ≤ r * ((m + r - 1) / r) := by
  have hr0 : 0 < r := hr
  have hdiv := Nat.div_add_mod (m + r - 1) r
  have hmod : (m + r - 1) % r ≤ r - 1 := Nat.lt_succ_iff.mp (by
    have hlt := Nat.mod_lt (m + r - 1) hr0
    omega)
  omega

private lemma mem_block_of_mem {φ : CNF ℕ} {r : ℕ} (hr : 1 ≤ r) {c : Clause ℕ} (hc : c ∈ φ) :
    ∃ i < r, c ∈ GroupClique.block φ r i := by
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨k, hk, rfl⟩
  set B := GroupClique.blockSize φ r
  have hcov : φ.length ≤ r * B := blockSize_mul_ge hr
  have hB : 0 < B := by
    by_contra hB0
    have h0 : B = 0 := Nat.eq_zero_of_not_pos hB0
    rw [h0, Nat.mul_zero] at hcov
    omega
  refine ⟨k / B, ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hk (by simpa [Nat.mul_comm] using hcov))
  · have hk_eq : k / B * B + k % B = k := by
      have hdiv := Nat.div_add_mod k B
      rw [Nat.mul_comm] at hdiv
      exact hdiv
    have hk_mod : k % B < B := Nat.mod_lt k hB
    have hlt_len : k / B * B + k % B < φ.length := by
      rw [hk_eq]
      exact hk
    have hdrop_len : k % B < (φ.drop (k / B * B)).length := by
      rw [List.length_drop]
      omega
    have htake_len : k % B < ((φ.drop (k / B * B)).take B).length := by
      rw [List.length_take]
      exact lt_min hk_mod hdrop_len
    refine List.mem_iff_getElem.mpr ⟨k % B, htake_len, ?_⟩
    dsimp only [GroupClique.block]
    rw [List.getElem_take, List.getElem_drop]
    congr 1

private lemma mem_of_mem_block {φ : CNF ℕ} {r i : ℕ} {c : Clause ℕ}
    (hc : c ∈ GroupClique.block φ r i) : c ∈ φ :=
  List.mem_of_mem_drop (List.mem_of_mem_take hc)

private lemma length_distinctVars_block_le {φ : CNF ℕ} {r i : ℕ}
    (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (GroupClique.block φ r i).distinctVars.length ≤ 3 * GroupClique.blockSize φ r := by
  have h1 := (GroupClique.block φ r i).length_distinctVars
  have h2 := (GroupClique.block φ r i).numVars_le_length_vars
  have h3b : ∀ c ∈ GroupClique.block φ r i, c.length ≤ 3 :=
    fun c hc => h3 c (mem_of_mem_block hc)
  have h4 := CNF.length_vars_le_mul_length h3b
  have h5 : (GroupClique.block φ r i).length ≤ GroupClique.blockSize φ r := by
    dsimp only [GroupClique.block]
    exact List.length_take_le _ _
  omega

/-! ### Vertex and edge characterization -/

private lemma vertex_div {bound i a : ℕ} (ha : a < bound) :
    GroupClique.vertex bound i a / bound = i := by
  rw [GroupClique.vertex, Nat.mul_comm, Nat.mul_add_div (lt_of_le_of_lt (Nat.zero_le a) ha),
    Nat.div_eq_of_lt ha, Nat.add_zero]

private lemma vertex_mod {bound i a : ℕ} (ha : a < bound) :
    GroupClique.vertex bound i a % bound = a := by
  rw [GroupClique.vertex, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

private lemma vertex_inj {bound i₁ a₁ i₂ a₂ : ℕ} (ha₁ : a₁ < bound) (ha₂ : a₂ < bound)
    (h : GroupClique.vertex bound i₁ a₁ = GroupClique.vertex bound i₂ a₂) :
    i₁ = i₂ ∧ a₁ = a₂ := by
  refine ⟨?_, ?_⟩
  · calc
      i₁ = GroupClique.vertex bound i₁ a₁ / bound := (vertex_div ha₁).symm
      _ = GroupClique.vertex bound i₂ a₂ / bound := by rw [h]
      _ = i₂ := vertex_div ha₂
  · calc
      a₁ = GroupClique.vertex bound i₁ a₁ % bound := (vertex_mod ha₁).symm
      _ = GroupClique.vertex bound i₂ a₂ % bound := by rw [h]
      _ = a₂ := vertex_mod ha₂

private lemma mem_verticesOfBound_iff {r : ℕ} {φ : CNF ℕ} {bound v : ℕ} :
    v ∈ GroupClique.verticesOfBound r φ bound ↔
      ∃ i < r, ∃ a < bound,
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
        v = GroupClique.vertex bound i a := by
  simp only [GroupClique.verticesOfBound, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter]
  constructor
  · rintro ⟨i, hi, a, ⟨ha, heval⟩, rfl⟩
    exact ⟨i, hi, a, ha, heval, rfl⟩
  · rintro ⟨i, hi, a, ha, heval, rfl⟩
    exact ⟨i, hi, a, ⟨ha, heval⟩, rfl⟩

private lemma compat_symm {vs₁ vs₂ : List ℕ} {a₁ a₂ : ℕ} :
    GroupClique.compat vs₁ vs₂ a₁ a₂ = true ↔ GroupClique.compat vs₂ vs₁ a₂ a₁ = true := by
  simp only [GroupClique.compat, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, beq_iff_eq]
  constructor
  · intro h x hx₂
    by_cases hx₁ : x ∈ vs₁
    · exact Or.inr ((h x hx₁).resolve_left (by simp [hx₂])).symm
    · exact Or.inl (by simp [hx₁])
  · intro h x hx₁
    by_cases hx₂ : x ∈ vs₂
    · exact Or.inr ((h x hx₂).resolve_left (by simp [hx₁])).symm
    · exact Or.inl (by simp [hx₂])

private lemma mem_edgesOfBound_iff {r : ℕ} {φ : CNF ℕ} {bound : ℕ} {e : ℕ × ℕ} :
    e ∈ GroupClique.edgesOfBound r φ bound ↔
      ∃ i < r, ∃ a < bound, ∃ j < r, ∃ b < bound,
        j ≠ i ∧
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
        (GroupClique.block φ r j).eval
          (bitsAssignment (GroupClique.block φ r j).distinctVars b) = true ∧
        GroupClique.compat (GroupClique.block φ r i).distinctVars
          (GroupClique.block φ r j).distinctVars a b = true ∧
        e = (GroupClique.vertex bound i a, GroupClique.vertex bound j b) := by
  simp only [GroupClique.edgesOfBound, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, a, ha, ha_mem⟩
    cases he₁ :
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a)
    · simp [he₁] at ha_mem
    · simp only [he₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
        List.mem_range] at ha_mem
      rcases ha_mem with ⟨j, hj, hj_mem⟩
      by_cases hji : j = i
      · simp [hji] at hj_mem
      · have hbeq : (j == i) = false := beq_false_of_ne hji
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter,
          List.mem_range, Bool.and_eq_true] at hj_mem
        rcases hj_mem with ⟨b, ⟨hb, he₂, hcomp⟩, rfl⟩
        exact ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
  · rintro ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
    refine ⟨i, hi, a, ha, ?_⟩
    simp only [he₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
      List.mem_range]
    refine ⟨j, hj, ?_⟩
    have hbeq : (j == i) = false := beq_false_of_ne hji
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter,
      List.mem_range, Bool.and_eq_true]
    exact ⟨b, ⟨hb, he₂, hcomp⟩, rfl⟩

/-! ### Correctness and vertex-count bounds -/

/-- For every `r ≥ 1` and `φ : CNF ℕ`, `SAT.groupClique r φ` sets target clique size `r`. -/
theorem groupClique_snd {r : ℕ} (hr : 1 ≤ r) (φ : CNF ℕ) :
    (groupClique r φ).2 = r := by
  have hr0 : (r == 0) = false := beq_false_of_ne (by omega)
  simp only [groupClique, GroupClique.graphOfBound, hr0, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

/-- Vertex list length bound: `|V(SAT.groupClique r φ)| ≤ r * 2 ^ (3 * ⌈|φ| / r⌉)`. -/
theorem length_groupClique_vertices_le (r : ℕ) (φ : CNF ℕ) :
    let graph := (groupClique r φ).1
    let verts := graph.vertices
    verts.length ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r)) := by
  dsimp only
  rw [groupClique, GroupClique.graphOfBound]
  by_cases hr0 : (r == 0) = true
  · simp [hr0]
  · simp only [hr0, Bool.false_eq_true, ↓reduceIte]
    by_cases h3 : (!φ.all fun c => decide (c.length ≤ 3)) = true
    · simp [h3]
    · simp only [h3, Bool.false_eq_true, ↓reduceIte]
      have hlen : (GroupClique.verticesOfBound r φ
          (2 ^ (3 * GroupClique.blockSize φ r))).length ≤
          (List.range r).length * 2 ^ (3 * GroupClique.blockSize φ r) := by
        apply List.length_flatMap_le
        intro i _
        rw [List.length_map]
        calc
          ((List.range (2 ^ (3 * GroupClique.blockSize φ r))).filter _).length ≤
              (List.range (2 ^ (3 * GroupClique.blockSize φ r))).length :=
            List.length_filter_le _ _
          _ = 2 ^ (3 * GroupClique.blockSize φ r) := List.length_range
      simpa [List.length_range, GroupClique.blockSize] using hlen

/-- Vertex finset cardinality bound for `SAT.groupClique r φ`. -/
theorem card_groupClique_vertices_le (r : ℕ) (φ : CNF ℕ) :
    let graph := (groupClique r φ).1
    let verts := graph.vertices
    verts.toFinset.card ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r)) :=
  le_trans (List.toFinset_card_le _) (length_groupClique_vertices_le r φ)

/-- Soundness and completeness of `SAT.groupClique`: for every `r ≥ 1` and `φ : CNF ℕ`,
`SAT.groupClique r φ ∈ Clique ↔ φ ∈ ThreeSAT`. -/
theorem groupClique_mem_Clique_iff {r : ℕ} (hr : 1 ≤ r) (φ : CNF ℕ) :
    groupClique r φ ∈ Clique ↔ φ ∈ ThreeSAT := by
  have hr0 : (r == 0) = false := beq_false_of_ne (by omega)
  by_cases h3bool : φ.all (fun c => decide (c.length ≤ 3)) = true
  · have h3 : ∀ c ∈ φ, c.length ≤ 3 := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using h3bool
    have hnot : (!φ.all fun c => decide (c.length ≤ 3)) = false := by simp [h3bool]
    have hgrp : groupClique r φ =
        (⟨GroupClique.verticesOfBound r φ (2 ^ (3 * GroupClique.blockSize φ r)),
          GroupClique.edgesOfBound r φ (2 ^ (3 * GroupClique.blockSize φ r))⟩, r) := by
      simp [groupClique, GroupClique.graphOfBound, hr0, hnot]
    rw [hgrp, mem_Clique_iff]
    set bound := 2 ^ (3 * GroupClique.blockSize φ r)
    constructor
    · rintro ⟨S, hSV, hclique⟩
      have hV : ∀ v ∈ S, ∃ i < r, ∃ a < bound,
          (GroupClique.block φ r i).eval
            (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
          v = GroupClique.vertex bound i a :=
        fun v hv => mem_verticesOfBound_iff.mp (hSV v hv)
      have hinj : ∀ v₁ ∈ S, ∀ v₂ ∈ S, v₁ / bound = v₂ / bound → v₁ = v₂ := by
        intro v₁ hv₁ v₂ hv₂ hdiv
        by_contra hne
        have hadj := hclique.1 hv₁ hv₂ hne
        rw [Graph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
        rcases hadj with ⟨_, hedge | hedge⟩
        · rcases mem_edgesOfBound_iff.mp hedge with
            ⟨i, _, a₁, ha₁, j, _, b₁, hb₁, hji, _, _, _, he⟩
          rw [Prod.mk.injEq] at he
          rcases he with ⟨he₁, he₂⟩
          rw [he₁, vertex_div ha₁, he₂, vertex_div hb₁] at hdiv
          exact hji hdiv.symm
        · rcases mem_edgesOfBound_iff.mp hedge with
            ⟨i, _, a₁, ha₁, j, _, b₁, hb₁, hji, _, _, _, he⟩
          rw [Prod.mk.injEq] at he
          rcases he with ⟨he₁, he₂⟩
          rw [he₂, vertex_div hb₁, he₁, vertex_div ha₁] at hdiv
          exact hji hdiv
      have himg_sub : S.image (fun v => v / bound) ⊆ Finset.range r := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
        rcases hV v hv with ⟨i', hi', a', ha', _, rfl⟩
        simpa [vertex_div ha'] using hi'
      have himg_card : (Finset.range r).card ≤ (S.image (fun v => v / bound)).card := by
        rw [Finset.card_image_of_injOn (fun v₁ hv₁ v₂ hv₂ => hinj v₁ hv₁ v₂ hv₂),
          hclique.2, Finset.card_range]
      have himg_eq : S.image (fun v => v / bound) = Finset.range r :=
        Finset.eq_of_subset_of_card_le himg_sub himg_card
      have hsurj : ∀ i < r, ∃ v ∈ S, v / bound = i := by
        intro i hi
        have hi' : i ∈ S.image (fun v => v / bound) := himg_eq ▸ Finset.mem_range.mpr hi
        exact Finset.mem_image.mp hi'
      choose sel hselS hsel_div using fun i (hi : i < r) => hsurj i hi
      let τ : ℕ → Bool := fun x =>
        if hx : ∃ i < r, x ∈ (GroupClique.block φ r i).distinctVars then
          let k := Nat.find hx
          have hk : k < r := (Nat.find_spec hx).1
          bitsAssignment (GroupClique.block φ r k).distinctVars (sel k hk % bound) x
        else
          false
      refine ⟨h3, τ, ?_⟩
      rw [CNF.eval_eq_true_iff]
      intro c hc
      rcases mem_block_of_mem hr hc with ⟨i, hi, hcb⟩
      have hiS : sel i hi ∈ S := hselS i hi
      rcases hV (sel i hi) hiS with ⟨i', hi', a', ha', ha'_eval, hs_eq⟩
      have hi'_eq : i' = i := by
        have := hsel_div i hi
        rw [hs_eq, vertex_div ha'] at this
        exact this
      rw [hi'_eq] at ha'_eval hs_eq
      have hclause_eval : Clause.eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a') c = true :=
        (CNF.eval_eq_true_iff _ _).mp ha'_eval c hcb
      have hcongr : Clause.eval τ c =
          Clause.eval (bitsAssignment (GroupClique.block φ r i).distinctVars a') c := by
        refine Clause.eval_congr fun ⟨x, pol⟩ hlit => ?_
        have hx_vars : x ∈ (GroupClique.block φ r i).vars :=
          CNF.mem_vars.2 ⟨c, hcb, pol, hlit⟩
        have hx_dvars : x ∈ (GroupClique.block φ r i).distinctVars :=
          CNF.mem_distinctVars.mpr hx_vars
        have hex : ∃ k < r, x ∈ (GroupClique.block φ r k).distinctVars := ⟨i, hi, hx_dvars⟩
        dsimp only [τ]
        split_ifs
        set j := Nat.find hex
        have hj : j < r := (Nat.find_spec hex).1
        have hxj : x ∈ (GroupClique.block φ r j).distinctVars := (Nat.find_spec hex).2
        by_cases hji : j = i
        · subst hji
          rw [hs_eq, vertex_mod ha']
        · rcases hV (sel j hj) (hselS j hj) with ⟨j', hj', b', hb', _, hsj_eq⟩
          have hj'_eq : j' = j := by
            have := hsel_div j hj
            rw [hsj_eq, vertex_div hb'] at this
            exact this
          rw [hj'_eq] at hsj_eq
          have hj_mod : sel j hj % bound = b' := by rw [hsj_eq, vertex_mod hb']
          rw [hj_mod]
          have hne_v : sel j hj ≠ sel i hi := by
            intro hEq
            have h1 := hsel_div j hj
            rw [hEq, hsel_div i hi] at h1
            exact hji h1.symm
          have hadj := hclique.1 (hselS j hj) hiS hne_v
          rw [Graph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
          have hcomp : GroupClique.compat (GroupClique.block φ r j).distinctVars
              (GroupClique.block φ r i).distinctVars b' a' = true := by
            rcases hadj with ⟨_, hedge | hedge⟩
            · rcases mem_edgesOfBound_iff.mp hedge with
                ⟨p, _, ap, hap, q, _, bq, hbq, _, _, _, hcp, he⟩
              rw [Prod.mk.injEq] at he
              rcases he with ⟨h1, h2⟩
              rw [hsj_eq] at h1
              rw [hs_eq] at h2
              rcases vertex_inj hb' hap h1 with ⟨rfl, rfl⟩
              rcases vertex_inj ha' hbq h2 with ⟨rfl, rfl⟩
              exact hcp
            · rcases mem_edgesOfBound_iff.mp hedge with
                ⟨p, _, ap, hap, q, _, bq, hbq, _, _, _, hcp, he⟩
              rw [Prod.mk.injEq] at he
              rcases he with ⟨h1, h2⟩
              rw [hs_eq] at h1
              rw [hsj_eq] at h2
              rcases vertex_inj ha' hap h1 with ⟨rfl, rfl⟩
              rcases vertex_inj hb' hbq h2 with ⟨rfl, rfl⟩
              exact compat_symm.mp hcp
          simp only [GroupClique.compat, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            List.contains_eq_mem, beq_iff_eq] at hcomp
          exact (hcomp x hxj).resolve_left (by simp [hx_dvars])
      rw [hcongr, hclause_eval]
    · rintro ⟨_, τ, hτ⟩
      have hcode_exists : ∀ i, ∃ ci < 2 ^ (GroupClique.block φ r i).distinctVars.length,
          ∀ v ∈ (GroupClique.block φ r i).distinctVars,
            bitsAssignment (GroupClique.block φ r i).distinctVars ci v = τ v := fun i =>
        exists_lt_two_pow_bitsAssignment_eq τ
      let code : ℕ → ℕ := fun i => (hcode_exists i).choose
      have hcode_lt : ∀ i, code i < bound := fun i =>
        lt_of_lt_of_le (hcode_exists i).choose_spec.1
          (Nat.pow_le_pow_right (by omega) (length_distinctVars_block_le h3))
      have hcode_eval : ∀ i,
          (GroupClique.block φ r i).eval
            (bitsAssignment (GroupClique.block φ r i).distinctVars (code i)) = true := by
        intro i
        rw [CNF.eval_eq_true_iff]
        intro c hc
        have hτc : Clause.eval τ c = true :=
          (CNF.eval_eq_true_iff _ _).mp hτ c (mem_of_mem_block hc)
        have hcongr :
            Clause.eval (bitsAssignment (GroupClique.block φ r i).distinctVars (code i)) c =
              Clause.eval τ c := by
          refine Clause.eval_congr fun ⟨x, pol⟩ hlit => ?_
          exact (hcode_exists i).choose_spec.2 x
            (CNF.mem_distinctVars.mpr (CNF.mem_vars.2 ⟨c, hc, pol, hlit⟩))
        rw [hcongr, hτc]
      let f : ℕ → ℕ := fun i => GroupClique.vertex bound i (code i)
      have hf_inj : Set.InjOn f (Finset.range r) := by
        intro i _ j _ hij
        exact (vertex_inj (hcode_lt i) (hcode_lt j) hij).1
      refine ⟨(Finset.range r).image f, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
        exact mem_verticesOfBound_iff.mpr
          ⟨i, Finset.mem_range.mp hi, code i, hcode_lt i, hcode_eval i, rfl⟩
      · refine ⟨?_, ?_⟩
        · intro u hu v hv huv
          rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
          rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
          have hij : i ≠ j := fun h => huv (by rw [h])
          rw [Graph.toSimpleGraph, SimpleGraph.fromRel_adj]
          refine ⟨huv, Or.inl ?_⟩
          refine mem_edgesOfBound_iff.mpr
            ⟨i, Finset.mem_range.mp hi, code i, hcode_lt i,
              j, Finset.mem_range.mp hj, code j, hcode_lt j, hij.symm,
              hcode_eval i, hcode_eval j, ?_, rfl⟩
          simp only [GroupClique.compat, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            List.contains_eq_mem, beq_iff_eq]
          intro x hx₁
          by_cases hx₂ : x ∈ (GroupClique.block φ r j).distinctVars
          · refine Or.inr ?_
            rw [(hcode_exists i).choose_spec.2 x hx₁, (hcode_exists j).choose_spec.2 x hx₂]
          · exact Or.inl (by simp [hx₂])
        · rw [Finset.card_image_of_injOn hf_inj, Finset.card_range]
  · have hnot3 : ¬∀ c ∈ φ, c.length ≤ 3 := by
      intro h3
      exact h3bool (by simpa only [List.all_eq_true, decide_eq_true_eq] using h3)
    have hnot : (!φ.all fun c => decide (c.length ≤ 3)) = true := by
      cases h : φ.all fun c => decide (c.length ≤ 3)
      · rfl
      · exfalso; exact h3bool h
    have hgrp : groupClique r φ = (⟨[], []⟩, r) := by
      simp [groupClique, GroupClique.graphOfBound, hr0, hnot]
    rw [hgrp, mem_Clique_iff]
    constructor
    · rintro ⟨S, hSV, hclique⟩
      have hS0 : S = ∅ := by
        ext v
        simp only [Finset.notMem_empty, iff_false]
        intro hv
        exact absurd (hSV v hv) List.not_mem_nil
      have hcard := hclique.2
      rw [hS0, Finset.card_empty] at hcard
      omega
    · rintro ⟨h3, _⟩
      exact absurd h3 hnot3

/-! ### Polynomial-time computability of the bounded builder -/

private theorem computableInPolyTime_takeClause {γ : Type} {encIn : γ ↪ List Bool}
    {xs : γ → CNF ℕ} {n : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn encCNF)
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun g => (xs g).take (n g)) encIn encCNF := by
  have hxs' : ComputableTidilyInPolyTime xs encIn (encList (encList (encPair encNat encBool))) :=
    (ComputableInPolyTime.of_enc_eq hxs fun _ => rfl).tidy
  exact ComputableInPolyTime.of_enc_eq
    (ComputableInPolyTime.of_tidy (hxs'.listTakeWithInput hn.tidy)) fun _ => rfl

private theorem computableInPolyTime_dropClause {γ : Type} {encIn : γ ↪ List Bool}
    {xs : γ → CNF ℕ} {n : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn encCNF)
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun g => (xs g).drop (n g)) encIn encCNF := by
  have hxs' : ComputableTidilyInPolyTime xs encIn (encList (encList (encPair encNat encBool))) :=
    (ComputableInPolyTime.of_enc_eq hxs fun _ => rfl).tidy
  exact ComputableInPolyTime.of_enc_eq
    (ComputableInPolyTime.of_tidy (hxs'.listDropWithInput hn.tidy)) fun _ => rfl

private theorem computableInPolyTime_blockSize {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.blockSize (φ g) (r g)) encIn encUnary := by
  have hlen := SAT.computableInPolyTime_length hφ
  have hnum := ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.unary_add' hlen hr) (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.unary_div' hnum hr

private theorem computableInPolyTime_block {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r i : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.block (φ g) (r g) (i g)) encIn encCNF := by
  have hbs := computableInPolyTime_blockSize hφ hr
  have hoff := ComputableInPolyTime.unary_mul' hi hbs
  exact computableInPolyTime_takeClause (computableInPolyTime_dropClause hφ hoff) hbs

private theorem computableInPolyTime_compat {γ : Type} {encIn : γ ↪ List Bool}
    {vs₁ vs₂ : γ → List ℕ} {a₁ a₂ : γ → ℕ}
    (hvs₁ : ComputableInPolyTime vs₁ encIn (encList encNat))
    (hvs₂ : ComputableInPolyTime vs₂ encIn (encList encNat))
    (ha₁ : ComputableInPolyTime a₁ encIn encNat)
    (ha₂ : ComputableInPolyTime a₂ encIn encNat) :
    ComputableInPolyTime
      (fun g => GroupClique.compat (vs₁ g) (vs₂ g) (a₁ g) (a₂ g)) encIn encBool := by
  have hnot_mem :
      ComputableInPolyTime
        (fun p : γ × ℕ => !(vs₂ p.1).contains p.2)
        (encPair encIn encNat) encBool :=
    ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.contains
        (hvs₂.comp (ComputableInPolyTime.fst encIn encNat))
        (ComputableInPolyTime.snd encIn encNat))
  have hbit₁ :
      ComputableInPolyTime
        (fun p : γ × ℕ => bitsAssignment (vs₁ p.1) (a₁ p.1) p.2)
        (encPair encIn encNat) encBool :=
    ComputableInPolyTime.binary_testBit
      (ha₁.comp (ComputableInPolyTime.fst encIn encNat))
      (ComputableInPolyTime.idxOfWithInput
        (hvs₁.comp (ComputableInPolyTime.fst encIn encNat))
        (ComputableInPolyTime.snd encIn encNat))
  have hbit₂ :
      ComputableInPolyTime
        (fun p : γ × ℕ => bitsAssignment (vs₂ p.1) (a₂ p.1) p.2)
        (encPair encIn encNat) encBool :=
    ComputableInPolyTime.binary_testBit
      (ha₂.comp (ComputableInPolyTime.fst encIn encNat))
      (ComputableInPolyTime.idxOfWithInput
        (hvs₂.comp (ComputableInPolyTime.fst encIn encNat))
        (ComputableInPolyTime.snd encIn encNat))
  have heq_bit :
      ComputableInPolyTime
        (fun p : γ × ℕ =>
          bitsAssignment (vs₁ p.1) (a₁ p.1) p.2 ==
            bitsAssignment (vs₂ p.1) (a₂ p.1) p.2)
        (encPair encIn encNat) encBool :=
    ComputableInPolyTime.beq hbit₁ hbit₂
  have hbody := ComputableInPolyTime.bool_or.comp (ComputableInPolyTime.prod hnot_mem heq_bit)
  exact ComputableInPolyTime.allWithInput hvs₁ hbody

private theorem computableInPolyTime_evalBlock {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r i a : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime
      (fun g =>
        (GroupClique.block (φ g) (r g) (i g)).eval
          (bitsAssignment (GroupClique.block (φ g) (r g) (i g)).distinctVars (a g)))
      encIn encBool := by
  have hb := computableInPolyTime_block hφ hr hi
  have hvs := SAT.computableInPolyTime_distinctVars.comp hb
  have ha_nat := ComputableInPolyTime.unary_to_binary.comp ha
  exact computableInPolyTime_eval_bitsAssignment.comp
    (ComputableInPolyTime.prod (ComputableInPolyTime.prod hb hvs) ha_nat)

private theorem computableInPolyTime_vertex {γ : Type} {encIn : γ ↪ List Bool}
    {bound i a : γ → ℕ}
    (hb : ComputableInPolyTime bound encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.vertex (bound g) (i g) (a g)) encIn encNat :=
  ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.unary_to_binary.comp hi)
      (ComputableInPolyTime.unary_to_binary.comp hb))
    (ComputableInPolyTime.unary_to_binary.comp ha)

private theorem computableInPolyTime_verticesOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.verticesOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) (encList encNat) := by
  let encIn := encPair (encPair encUnary encCNF) encUnary
  have hr : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.1) encIn encUnary :=
    (ComputableInPolyTime.fst encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hφ : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.2) encIn encCNF :=
    (ComputableInPolyTime.snd encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hbd : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.2) encIn encUnary :=
    ComputableInPolyTime.snd (encPair encUnary encCNF) encUnary
  have hrange_r := ComputableInPolyTime.range.comp hr
  refine ComputableInPolyTime.flatMapWithInput hrange_r ?_
  let encI := encPair encIn encUnary
  have hrI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.1.1) encI encUnary :=
    hr.comp (ComputableInPolyTime.fst encIn encUnary)
  have hφI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.1.2) encI encCNF :=
    hφ.comp (ComputableInPolyTime.fst encIn encUnary)
  have hbdI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.2) encI encUnary :=
    hbd.comp (ComputableInPolyTime.fst encIn encUnary)
  have hiI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.2) encI encUnary :=
    ComputableInPolyTime.snd encIn encUnary
  have hrange_bd := ComputableInPolyTime.range.comp hbdI
  have hfilt :
      ComputableInPolyTime
        (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ =>
          (List.range q.1.2).filter fun a =>
            (GroupClique.block q.1.1.2 q.1.1.1 q.2).eval
              (bitsAssignment (GroupClique.block q.1.1.2 q.1.1.1 q.2).distinctVars a))
        encI (encList encUnary) := by
    refine ComputableInPolyTime.filterWithInput hrange_bd ?_
    exact computableInPolyTime_evalBlock
      (hφI.comp (ComputableInPolyTime.fst encI encUnary))
      (hrI.comp (ComputableInPolyTime.fst encI encUnary))
      (hiI.comp (ComputableInPolyTime.fst encI encUnary))
      (ComputableInPolyTime.snd encI encUnary)
  refine ComputableInPolyTime.mapWithInput hfilt ?_
  exact computableInPolyTime_vertex
    (hbdI.comp (ComputableInPolyTime.fst encI encUnary))
    (hiI.comp (ComputableInPolyTime.fst encI encUnary))
    (ComputableInPolyTime.snd encI encUnary)

private theorem computableInPolyTime_edgesOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.edgesOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) (encList (encPair encNat encNat)) := by
  let encIn := encPair (encPair encUnary encCNF) encUnary
  have hr : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.1) encIn encUnary :=
    (ComputableInPolyTime.fst encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hφ : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.2) encIn encCNF :=
    (ComputableInPolyTime.snd encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hbd : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.2) encIn encUnary :=
    ComputableInPolyTime.snd (encPair encUnary encCNF) encUnary
  refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hr) ?_
  let encI := encPair encIn encUnary
  have hrI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.1.1) encI encUnary :=
    hr.comp (ComputableInPolyTime.fst encIn encUnary)
  have hφI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.1.2) encI encCNF :=
    hφ.comp (ComputableInPolyTime.fst encIn encUnary)
  have hbdI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.1.2) encI encUnary :=
    hbd.comp (ComputableInPolyTime.fst encIn encUnary)
  have hiI : ComputableInPolyTime (fun q : ((ℕ × CNF ℕ) × ℕ) × ℕ => q.2) encI encUnary :=
    ComputableInPolyTime.snd encIn encUnary
  refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hbdI) ?_
  let encA := encPair encI encUnary
  have hrA : ComputableInPolyTime (fun q : (((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1)
      encA encUnary := hrI.comp (ComputableInPolyTime.fst encI encUnary)
  have hφA : ComputableInPolyTime (fun q : (((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
      encA encCNF := hφI.comp (ComputableInPolyTime.fst encI encUnary)
  have hbdA : ComputableInPolyTime (fun q : (((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
      encA encUnary := hbdI.comp (ComputableInPolyTime.fst encI encUnary)
  have hiA : ComputableInPolyTime (fun q : (((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
      encA encUnary := hiI.comp (ComputableInPolyTime.fst encI encUnary)
  have haA : ComputableInPolyTime (fun q : (((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ => q.2)
      encA encUnary := ComputableInPolyTime.snd encI encUnary
  have hcondA := ComputableInPolyTime.bool_not.comp
    (computableInPolyTime_evalBlock hφA hrA hiA haA)
  dsimp only [Function.comp_def] at hcondA
  refine ComputableInPolyTime.ite_decide (by simpa only [Bool.decide_eq_true] using hcondA)
    (ComputableInPolyTime.const []) ?_
  refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hrA) ?_
  let encJ := encPair encA encUnary
  have hrJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.1)
      encJ encUnary := hrA.comp (ComputableInPolyTime.fst encA encUnary)
  have hφJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.2)
      encJ encCNF := hφA.comp (ComputableInPolyTime.fst encA encUnary)
  have hbdJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2)
      encJ encUnary := hbdA.comp (ComputableInPolyTime.fst encA encUnary)
  have hiJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2)
      encJ encUnary := hiA.comp (ComputableInPolyTime.fst encA encUnary)
  have haJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2)
      encJ encUnary := haA.comp (ComputableInPolyTime.fst encA encUnary)
  have hjJ : ComputableInPolyTime (fun q : ((((ℕ × CNF ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.2)
      encJ encUnary := ComputableInPolyTime.snd encA encUnary
  have hji := ComputableInPolyTime.beq hjJ hiJ
  refine ComputableInPolyTime.ite_decide (by simpa only [Bool.decide_eq_true] using hji)
    (ComputableInPolyTime.const []) ?_
  have hfilt :
      ComputableInPolyTime
        (fun q =>
          (List.range q.1.1.1.2).filter fun b =>
            (GroupClique.block q.1.1.1.1.2 q.1.1.1.1.1 q.2).eval
                (bitsAssignment
                  (GroupClique.block q.1.1.1.1.2 q.1.1.1.1.1 q.2).distinctVars b) &&
              GroupClique.compat
                (GroupClique.block q.1.1.1.1.2 q.1.1.1.1.1 q.1.1.2).distinctVars
                (GroupClique.block q.1.1.1.1.2 q.1.1.1.1.1 q.2).distinctVars
                q.1.2 b)
        encJ (encList encUnary) := by
    refine ComputableInPolyTime.filterWithInput (ComputableInPolyTime.range.comp hbdJ) ?_
    have hrB := hrJ.comp (ComputableInPolyTime.fst encJ encUnary)
    have hφB := hφJ.comp (ComputableInPolyTime.fst encJ encUnary)
    have hiB := hiJ.comp (ComputableInPolyTime.fst encJ encUnary)
    have haB := haJ.comp (ComputableInPolyTime.fst encJ encUnary)
    have hjB := hjJ.comp (ComputableInPolyTime.fst encJ encUnary)
    have hbB := ComputableInPolyTime.snd encJ encUnary
    have heval₂ := computableInPolyTime_evalBlock hφB hrB hjB hbB
    have hvs₁ := SAT.computableInPolyTime_distinctVars.comp
      (computableInPolyTime_block hφB hrB hiB)
    have hvs₂ := SAT.computableInPolyTime_distinctVars.comp
      (computableInPolyTime_block hφB hrB hjB)
    have hcomp := computableInPolyTime_compat hvs₁ hvs₂
      (ComputableInPolyTime.unary_to_binary.comp haB)
      (ComputableInPolyTime.unary_to_binary.comp hbB)
    exact ComputableInPolyTime.bool_and.comp (ComputableInPolyTime.prod heval₂ hcomp)
  refine ComputableInPolyTime.mapWithInput hfilt ?_
  have hbdB := hbdJ.comp (ComputableInPolyTime.fst encJ encUnary)
  have hiB := hiJ.comp (ComputableInPolyTime.fst encJ encUnary)
  have haB := haJ.comp (ComputableInPolyTime.fst encJ encUnary)
  have hjB := hjJ.comp (ComputableInPolyTime.fst encJ encUnary)
  have hbB := ComputableInPolyTime.snd encJ encUnary
  exact ComputableInPolyTime.prod
    (computableInPolyTime_vertex hbdB hiB haB)
    (computableInPolyTime_vertex hbdB hjB hbB)

private theorem computableInPolyTime_isThreeCNF :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.all fun c => decide (c.length ≤ 3))
      encCNF encBool := by
  have hid :
      ComputableInPolyTime (fun φ : CNF ℕ => φ)
        encCNF (encList (encList (encPair encNat encBool))) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  refine ComputableInPolyTime.allWithInput hid ?_
  have hlen :=
    (ComputableInPolyTime.length_list_binary (encPair encNat encBool)).comp
      (ComputableInPolyTime.snd encCNF (encList (encPair encNat encBool)))
  exact ComputableInPolyTime.binary_le' hlen (ComputableInPolyTime.const 3)

private theorem computableInPolyTime_graphOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.graphOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) (encPair encGraph encNat) := by
  let encIn := encPair (encPair encUnary encCNF) encUnary
  have hr : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.1) encIn encUnary :=
    (ComputableInPolyTime.fst encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hφ : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.2) encIn encCNF :=
    (ComputableInPolyTime.snd encUnary encCNF).comp
      (ComputableInPolyTime.fst (encPair encUnary encCNF) encUnary)
  have hr0 : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.1 == 0) encIn encBool :=
    ComputableInPolyTime.beq hr (ComputableInPolyTime.const 0)
  have hnot3 :
      ComputableInPolyTime
        (fun p : (ℕ × CNF ℕ) × ℕ => !p.1.2.all fun c => decide (c.length ≤ 3))
        encIn encBool :=
    ComputableInPolyTime.bool_not.comp (computableInPolyTime_isThreeCNF.comp hφ)
  have hmain :
      ComputableInPolyTime
        (fun p : (ℕ × CNF ℕ) × ℕ =>
          (⟨GroupClique.verticesOfBound p.1.1 p.1.2 p.2,
            GroupClique.edgesOfBound p.1.1 p.1.2 p.2⟩, p.1.1))
        encIn (encPair encGraph encNat) :=
    ComputableInPolyTime.prod
      (encGraph_mk_polyTime computableInPolyTime_verticesOfBound computableInPolyTime_edgesOfBound)
      (ComputableInPolyTime.unary_to_binary.comp hr)
  have hbad3 :
      ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => (⟨[], []⟩, p.1.1))
        encIn (encPair encGraph encNat) :=
    ComputableInPolyTime.prod (ComputableInPolyTime.const (⟨[], []⟩ : Graph))
      (ComputableInPolyTime.unary_to_binary.comp hr)
  refine ComputableInPolyTime.ite_decide (by simpa only [Bool.decide_eq_true] using hr0)
    (ComputableInPolyTime.const ((⟨[], []⟩, 1) : Graph × ℕ)) ?_
  exact ComputableInPolyTime.ite_decide (by simpa only [Bool.decide_eq_true] using hnot3)
    hbad3 hmain

/-- Uniform runtime and output-size bound for `(r, φ) ↦ SAT.groupClique r φ`: the exponential
exponent scales linearly in `3 * ((φ.length + r - 1) / r)` with polynomial degree `D` independent
of `r`. -/
theorem exists_computableInO_groupClique :
    ∃ C D : ℕ,
      ComputableInO (fun p : ℕ × CNF ℕ => groupClique p.1 p.2)
        (encPair encUnary encCNF) (encPair encGraph encNat)
        (fun p => C * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
          ((encPair encUnary encCNF p).length + 1) ^ D)
        (fun p => C * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
          ((encPair encUnary encCNF p).length + 1) ^ D) := by
  let encBase := encPair encUnary encCNF
  have hν :
      ComputableInPolyTime (fun p : ℕ × CNF ℕ => 3 * GroupClique.blockSize p.2 p.1)
        encBase encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3)
      (computableInPolyTime_blockSize
        (ComputableInPolyTime.snd encUnary encCNF)
        (ComputableInPolyTime.fst encUnary encCNF))
  exact ComputableInPolyTime.exists_computableInO_pad computableInPolyTime_graphOfBound hν

/-! ### ETH transfers and Clique lower bounds -/

private lemma blockSize_real_le {m r : ℕ} (hr : 1 ≤ r) :
    (((m + r - 1) / r : ℕ) : ℝ) ≤ (m : ℝ) / (r : ℝ) + 1 := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmul : ((m + r - 1) / r) * r ≤ m + r := by
    have hle := Nat.div_mul_le_self (m + r - 1) r
    omega
  have hmul_r : (((m + r - 1) / r : ℕ) : ℝ) * (r : ℝ) ≤ (m : ℝ) + (r : ℝ) := by
    exact_mod_cast hmul
  have hdiv_r : (((m + r - 1) / r : ℕ) : ℝ) * (r : ℝ) ≤
      ((m : ℝ) / (r : ℝ) + 1) * (r : ℝ) := by
    calc
      (((m + r - 1) / r : ℕ) : ℝ) * (r : ℝ) ≤ (m : ℝ) + (r : ℝ) := hmul_r
      _ = ((m : ℝ) / (r : ℝ) + 1) * (r : ℝ) := by field_simp
  exact le_of_mul_le_mul_right hdiv_r hr_pos

private lemma two_pow_blockSize_real_le {r D : ℕ} (hr : 1 ≤ r) (φ : CNF ℕ) :
    ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (3 * D) * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) := by
  have hbs : ((GroupClique.blockSize φ r : ℕ) : ℝ) ≤ (φ.length : ℝ) / (r : ℝ) + 1 :=
    blockSize_real_le hr
  have hexp_le :
      ((D * (3 * GroupClique.blockSize φ r) : ℕ) : ℝ) ≤
        (3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ) + (3 * D : ℕ) := by
    have hcast :
        ((D * (3 * GroupClique.blockSize φ r) : ℕ) : ℝ) =
          3 * (D : ℝ) * ((GroupClique.blockSize φ r : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    have h1 : 3 * (D : ℝ) * ((GroupClique.blockSize φ r : ℕ) : ℝ) ≤
        3 * (D : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1) := by gcongr
    calc
      3 * (D : ℝ) * ((GroupClique.blockSize φ r : ℕ) : ℝ)
          ≤ 3 * (D : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1) := h1
      _ = (3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ) + ((3 * D : ℕ) : ℝ) := by
        push_cast; ring
  have hpow_nat :
      ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) =
        (2 : ℝ) ^ ((D * (3 * GroupClique.blockSize φ r) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    rfl
  rw [hpow_nat]
  calc
    (2 : ℝ) ^ ((D * (3 * GroupClique.blockSize φ r) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ) + (3 * D : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    _ = (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) * (2 : ℝ) ^ (3 * D) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    _ = (2 : ℝ) ^ (3 * D) * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) := by ring

private lemma encPair_unary_cnf_length_le (r : ℕ) (φ : CNF ℕ) :
    (encPair encUnary encCNF (r, φ)).length + 1 ≤
      ((frame (encUnary r)).length + 1) * ((encCNF φ).length + 1) := by
  have hlen : (encPair encUnary encCNF (r, φ)).length =
      (frame (encUnary r)).length + (encCNF φ).length := by
    simp [encPair]
  rw [hlen]
  nlinarith

private lemma enc_groupClique_length_le {C₀ D c_len : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (hlen_red : ∀ p : ℕ × CNF ℕ,
      (encPair encGraph encNat (groupClique p.1 p.2)).length ≤
        c_len * (C₀ * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
          ((encPair encUnary encCNF p).length + 1) ^ D + 1)) :
    let Lr := (frame (encUnary r)).length + 1
    let K_enc : ℝ := (c_len : ℝ) * (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + (c_len : ℝ) + 1
    ∀ φ : CNF ℕ,
      ((encPair encGraph encNat (groupClique r φ)).length : ℝ) + 1 ≤
        K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
          (((encCNF φ).length : ℝ) + 1) ^ D := by
  intro Lr K_enc φ
  have hl1r :
      ((encPair encGraph encNat (groupClique r φ)).length : ℝ) + 1 ≤
        (c_len : ℝ) * ((C₀ : ℝ) *
          ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) *
          (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D) + ((c_len : ℝ) + 1) := by
    have hl := hlen_red (r, φ)
    have hmul_eq :
        c_len * (C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
          ((encPair encUnary encCNF (r, φ)).length + 1) ^ D + 1) =
          c_len * (C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
            ((encPair encUnary encCNF (r, φ)).length + 1) ^ D) + c_len := by
      ring
    have hl' : (encPair encGraph encNat (groupClique r φ)).length + 1 ≤
        c_len * (C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
          ((encPair encUnary encCNF (r, φ)).length + 1) ^ D) + (c_len + 1) := by
      change (encPair encGraph encNat (groupClique (r, φ).1 (r, φ).2)).length + 1 ≤ _
      have hl2 := Nat.add_le_add_right hl 1
      rw [hmul_eq] at hl2
      exact le_trans hl2 (by omega)
    exact_mod_cast hl'
  have hpow2 := two_pow_blockSize_real_le (D := D) hr φ
  have hpoly :
      (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D ≤
        (Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ D := by
    have hp : ((encPair encUnary encCNF (r, φ)).length + 1 : ℝ) ≤
        (Lr : ℝ) * (((encCNF φ).length : ℝ) + 1) := by
      exact_mod_cast encPair_unary_cnf_length_le r φ
    calc
      (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D
          ≤ ((Lr : ℝ) * (((encCNF φ).length : ℝ) + 1)) ^ D :=
        pow_le_pow_left₀ (by positivity) hp D
      _ = (Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ D := mul_pow _ _ _
  have hbase_ge :
      (1 : ℝ) ≤
        (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
          (((encCNF φ).length : ℝ) + 1) ^ D := by
    have hexp : (1 : ℝ) ≤ (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hpol : (1 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ D :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
    exact one_le_mul_of_one_le_of_one_le hexp hpol
  calc
    ((encPair encGraph encNat (groupClique r φ)).length : ℝ) + 1
        ≤ (c_len : ℝ) * ((C₀ : ℝ) *
              ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) *
              (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D) +
            ((c_len : ℝ) + 1) := hl1r
    _ ≤ (c_len : ℝ) * ((C₀ : ℝ) *
              ((2 : ℝ) ^ (3 * D) * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) *
              ((Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ D)) +
            ((c_len : ℝ) + 1) *
              ((2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
                (((encCNF φ).length : ℝ) + 1) ^ D) := by
      gcongr
      exact le_mul_of_one_le_right (by positivity) hbase_ge
    _ = K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
          (((encCNF φ).length : ℝ) + 1) ^ D := by
      simp only [K_enc]; ring

private lemma decidableInExpTime_threeSAT_of_groupClique_bound
    {dec : Graph × ℕ → Bool} {t₂ : Graph × ℕ → ℕ} {c₂ : ℕ}
    (hdec : ComputableInO dec (encPair encGraph encNat) encBool t₂ t₂)
    (hmem : ∀ x, x ∈ Clique ↔ dec x = true)
    (C₀ D r : ℕ) (hr : 1 ≤ r)
    (hred : ComputableInO (fun p : ℕ × CNF ℕ => groupClique p.1 p.2)
      (encPair encUnary encCNF) (encPair encGraph encNat)
      (fun p => C₀ * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
        ((encPair encUnary encCNF p).length + 1) ^ D)
      (fun p => C₀ * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
        ((encPair encUnary encCNF p).length + 1) ^ D))
    {δ : ℝ} (hδ : 0 ≤ δ) (hDr : (3 * (D : ℝ)) / (r : ℝ) ≤ δ)
    {A B : ℝ} {d : ℕ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (hBδ : B ≤ δ)
    (ht₂ : ∀ φ : CNF ℕ,
      (t₂ (groupClique r φ) : ℝ) ≤
        A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d + c₂) :
    DecidableInExpTime ThreeSAT encCNF List.length δ := by
  let prep : CNF ℕ → ℕ × CNF ℕ := fun φ => (r, φ)
  have hprep_poly : ComputableInPolyTime prep encCNF (encPair encUnary encCNF) :=
    ComputableInPolyTime.prod (ComputableInPolyTime.const r) ComputableInPolyTime.id'
  rcases hprep_poly.exists_computableInO with ⟨T₀, S₀, hT₀, hS₀, hprepO⟩
  rcases hT₀.exists_le with ⟨C₀', d₀, hT₀_le⟩
  have hcomp₁ := hred.comp hprepO
  have hcomp₂ := hdec.comp hcomp₁
  let tTot : CNF ℕ → ℕ := fun φ =>
    (T₀ φ +
      C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
        ((encPair encUnary encCNF (r, φ)).length + 1) ^ D) +
    t₂ (groupClique r φ)
  have heqv : ∀ φ : CNF ℕ, φ ∈ ThreeSAT ↔ dec (groupClique r φ) = true := by
    intro φ
    rw [← hmem, groupClique_mem_Clique_iff hr]
  let Lr : ℕ := (frame (encUnary r)).length + 1
  let E : ℕ := max d₀ (max D d)
  refine ⟨E, ?_⟩
  have hbase_ge : ∀ φ : CNF ℕ,
      (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E := by
    intro φ
    have hexp : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hδ (Nat.cast_nonneg _))
    have hpoly : (1 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ E :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
    exact one_le_mul_of_one_le_of_one_le hexp hpoly
  have hstep1 : ∀ φ : CNF ℕ,
      (T₀ φ : ℝ) ≤
        (C₀' : ℝ) *
          ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) := by
    intro φ
    have h1 : (T₀ φ : ℝ) ≤ (C₀' : ℝ) * (((encCNF φ).length : ℝ) + 1) ^ d₀ := by
      exact_mod_cast hT₀_le φ
    have hpow : (((encCNF φ).length : ℝ) + 1) ^ d₀ ≤ (((encCNF φ).length : ℝ) + 1) ^ E :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
        (le_max_left _ _)
    have hexp : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hδ (Nat.cast_nonneg _))
    have hterm : (((encCNF φ).length : ℝ) + 1) ^ d₀ ≤
        (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E :=
      le_trans hpow (le_mul_of_one_le_left (pow_nonneg (by positivity) _) hexp)
    exact h1.trans (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _))
  have hstep2 : ∀ φ : CNF ℕ,
      ((C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
          ((encPair encUnary encCNF (r, φ)).length + 1) ^ D : ℕ) : ℝ) ≤
        ((C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D) *
          ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) := by
    intro φ
    have hpow2 :
        ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (3 * D) * (2 : ℝ) ^ (δ * (φ.length : ℝ)) := by
      have hexp :
          (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) ≤
            (2 : ℝ) ^ (δ * (φ.length : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right hDr (by positivity))
      exact le_trans (two_pow_blockSize_real_le hr φ)
        (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hpoly_pair :
        (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D ≤
          (Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ E := by
      have hlen_r : ((encPair encUnary encCNF (r, φ)).length + 1 : ℝ) ≤
          (Lr : ℝ) * (((encCNF φ).length : ℝ) + 1) := by
        exact_mod_cast encPair_unary_cnf_length_le r φ
      calc
        (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D
            ≤ ((Lr : ℝ) * (((encCNF φ).length : ℝ) + 1)) ^ D :=
          pow_le_pow_left₀ (by positivity) hlen_r D
        _ = (Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ D := mul_pow _ _ _
        _ ≤ (Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ E := by
          gcongr
          · linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length]
          · exact le_trans (le_max_left D d) (le_max_right d₀ (max D d))
    have hcast :
        ((C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
            ((encPair encUnary encCNF (r, φ)).length + 1) ^ D : ℕ) : ℝ) =
          (C₀ : ℝ) * ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) *
            (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D := by
      push_cast; rfl
    rw [hcast]
    calc
      (C₀ : ℝ) * ((2 ^ (D * (3 * GroupClique.blockSize φ r)) : ℕ) : ℝ) *
          (((encPair encUnary encCNF (r, φ)).length + 1 : ℝ)) ^ D
          ≤ (C₀ : ℝ) * ((2 : ℝ) ^ (3 * D) * (2 : ℝ) ^ (δ * (φ.length : ℝ))) *
              ((Lr : ℝ) ^ D * (((encCNF φ).length : ℝ) + 1) ^ E) := by
        gcongr
      _ = ((C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D) *
            ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) := by ring
  have hstep3 : ∀ φ : CNF ℕ,
      (t₂ (groupClique r φ) : ℝ) ≤
        A * ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) + c₂ := by
    intro φ
    have hexp : (2 : ℝ) ^ (B * (φ.length : ℝ)) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hBδ (Nat.cast_nonneg _))
    have hpoly : (((encCNF φ).length : ℝ) + 1) ^ d ≤ (((encCNF φ).length : ℝ) + 1) ^ E :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
        (le_trans (le_max_right D d) (le_max_right d₀ (max D d)))
    calc
      (t₂ (groupClique r φ) : ℝ)
          ≤ A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d + c₂ :=
        ht₂ φ
      _ ≤ A * (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E + c₂ := by
        gcongr
      _ = A * ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) + c₂ := by
        ring
  let K : ℕ :=
    Nat.ceil ((C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A) + c₂
  have hK : ∀ φ : CNF ℕ,
      (tTot φ : ℝ) ≤
        (K : ℝ) * ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) +
          (K : ℝ) := by
    intro φ
    have hceil :
        (C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A ≤ (K : ℝ) := by
      have h1 := Nat.le_ceil
        ((C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A)
      have h2 : (Nat.ceil
          ((C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A) : ℝ) ≤
          (K : ℝ) := Nat.cast_le.mpr (Nat.le_add_right _ c₂)
      exact le_trans h1 h2
    have hc₂ : (c₂ : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr (Nat.le_add_left c₂ _)
    have hsum :
        (tTot φ : ℝ) ≤
          ((C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A) *
            ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) +
          c₂ := by
      have hT : (tTot φ : ℝ) = (T₀ φ : ℝ) +
          ((C₀ * 2 ^ (D * (3 * GroupClique.blockSize φ r)) *
            ((encPair encUnary encCNF (r, φ)).length + 1) ^ D : ℕ) : ℝ) +
          (t₂ (groupClique r φ) : ℝ) := by
        simp only [tTot, Nat.cast_add]
      rw [hT]
      have hs1 := hstep1 φ
      have hs2 := hstep2 φ
      have hs3 := hstep3 φ
      linarith
    have hbase0 : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E :=
      le_trans zero_le_one (hbase_ge φ)
    calc
      (tTot φ : ℝ)
          ≤ ((C₀' : ℝ) + (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + A) *
              ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) + c₂ :=
        hsum
      _ ≤ (K : ℝ) * ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ E) +
            (K : ℝ) := by
        gcongr
  have hO : DecidableInTimeO ThreeSAT encCNF (fun φ => (tTot φ : ℝ)) :=
    DecidableInTimeO.of_computableInO hcomp₂ heqv (fun _ => le_rfl)
  exact DecidableInTimeO.mono hO K hK (fun φ => by positivity)

end SAT

/-- An `f(k) * |V| ^ o(k) * poly(|enc|)` algorithm for `Clique` places `ThreeSAT` in
subexponential time parameterized by clause count `List.length`. -/
theorem DecidableInSubexpTime.threeSAT_of_clique_subexpVertex
    (f g : ℕ → ℝ) (e : ℕ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k ≥ k₀, g k ≤ ε * k)
    (hClique : DecidableInTimeO Clique (encPair encGraph encNat)
      (fun x =>
        let graph := x.1
        let verts := graph.1
        f x.2 * ((verts.length : ℝ) + 1) ^ g x.2 *
          (((encPair encGraph encNat x).length : ℝ) + 1) ^ e)) :
    DecidableInSubexpTime ThreeSAT encCNF List.length := by
  intro δ hδ
  rcases DecidableInTimeO.exists_computableInO hClique with ⟨dec, t₂, c₂, hdec, hmem, ht₂⟩
  rcases SAT.exists_computableInO_groupClique with ⟨C₀, D, hred⟩
  have hδ6 : 0 < δ / 6 := by positivity
  rcases hg (δ / 6) hδ6 with ⟨k₀, hk₀⟩
  let r : ℕ := max 1 (max k₀ (Nat.ceil (6 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) / δ)))
  have hr : 1 ≤ r := le_max_left _ _
  have hrk : k₀ ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrc : 6 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) / δ ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmul_r : 6 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) ≤ δ * (r : ℝ) :=
    ((div_le_iff₀ hδ).mp hrc).trans_eq (mul_comm _ _)
  have hDe_r : 3 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) / (r : ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hr_pos]
    linarith
  have hDr : (3 * (D : ℝ)) / (r : ℝ) ≤ δ := by
    have hD_le : (D : ℝ) ≤ ((e + 1 : ℕ) : ℝ) * (D : ℝ) := by
      have : (1 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos e
      exact le_mul_of_one_le_left (Nat.cast_nonneg _) this
    calc
      3 * (D : ℝ) / (r : ℝ) ≤ 3 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) / (r : ℝ) := by gcongr
      _ ≤ δ / 2 := hDe_r
      _ ≤ δ := by linarith
  let g' : ℝ := max (g r) 0
  have hg'0 : 0 ≤ g' := le_max_right _ _
  have hgr_le : g r ≤ g' := le_max_left _ _
  have hg' : g' ≤ (δ / 6) * (r : ℝ) :=
    max_le (hk₀ r hrk) (mul_nonneg hδ6.le hr_pos.le)
  let B : ℝ := (3 * g' + 3 * (e : ℝ) * (D : ℝ)) / (r : ℝ)
  have hB0 : 0 ≤ B := by positivity
  have hBδ : B ≤ δ := by
    have h1 : 3 * g' / (r : ℝ) ≤ δ / 2 := by
      rw [div_le_iff₀ hr_pos]
      linarith
    have h2 : 3 * (e : ℝ) * (D : ℝ) / (r : ℝ) ≤ δ / 2 := by
      have he_le : (e : ℝ) * (D : ℝ) ≤ ((e + 1 : ℕ) : ℝ) * (D : ℝ) := by
        have : (e : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ e
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      calc
        3 * (e : ℝ) * (D : ℝ) / (r : ℝ)
            = 3 * ((e : ℝ) * (D : ℝ)) / (r : ℝ) := by ring
        _ ≤ 3 * (((e + 1 : ℕ) : ℝ) * (D : ℝ)) / (r : ℝ) := by gcongr
        _ ≤ δ / 2 := hDe_r
    calc
      B = 3 * g' / (r : ℝ) + 3 * (e : ℝ) * (D : ℝ) / (r : ℝ) := by ring
      _ ≤ δ / 2 + δ / 2 := add_le_add h1 h2
      _ = δ := by ring
  have hred' := hred
  rcases hred' with ⟨c_len, _, hlen_red⟩
  let Lr : ℕ := (frame (encUnary r)).length + 1
  let K_enc : ℝ := (c_len : ℝ) * (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + (c_len : ℝ) + 1
  have hK_enc0 : 0 ≤ K_enc := by positivity
  have henc_le := SAT.enc_groupClique_length_le r hr hlen_red
  let A : ℝ :=
    (c₂ : ℝ) * |f r| * ((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) * K_enc ^ e
  have hA0 : 0 ≤ A := by positivity
  have ht₂_le : ∀ φ : CNF ℕ,
      (t₂ (SAT.groupClique r φ) : ℝ) ≤
        A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ (e * D) + c₂ := by
    intro φ
    have h1 := ht₂ (SAT.groupClique r φ)
    rw [SAT.groupClique_snd hr] at h1
    have hV_nat : (SAT.groupClique r φ).1.1.length + 1 ≤
        (r + 1) * 2 ^ (3 * ((φ.length + r - 1) / r)) := by
      have hv := SAT.length_groupClique_vertices_le r φ
      have hpow_pos : 1 ≤ 2 ^ (3 * ((φ.length + r - 1) / r)) := Nat.one_le_two_pow
      nlinarith
    have hV_r : ((SAT.groupClique r φ).1.1.length : ℝ) + 1 ≤
        (r + 1 : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1)) := by
      have hbs := SAT.blockSize_real_le (m := φ.length) hr
      have hv1 : ((SAT.groupClique r φ).1.1.length : ℝ) + 1 ≤
          (r + 1 : ℝ) * ((2 ^ (3 * ((φ.length + r - 1) / r)) : ℕ) : ℝ) := by
        exact_mod_cast hV_nat
      have hpow_nat :
          ((2 ^ (3 * ((φ.length + r - 1) / r)) : ℕ) : ℝ) =
            (2 : ℝ) ^ ((3 * ((φ.length + r - 1) / r) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        push_cast
        rfl
      have hv2 : ((2 ^ (3 * ((φ.length + r - 1) / r)) : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1)) := by
        rw [hpow_nat]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        linarith
      exact le_trans hv1 (mul_le_mul_of_nonneg_left hv2 (by positivity))
    have hV_pow :
        (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r ≤
          ((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
            (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ)) := by
      have hge1 : (1 : ℝ) ≤ ((SAT.groupClique r φ).1.1.length : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) (SAT.groupClique r φ).1.1.length]
      have hstepA :
          (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r ≤
            (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g' :=
        Real.rpow_le_rpow_of_exponent_le hge1 hgr_le
      have hstepB :
          (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g' ≤
            ((r + 1 : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1))) ^ g' :=
        Real.rpow_le_rpow (by positivity) hV_r hg'0
      have hmul :
          ((r + 1 : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1))) ^ g' =
            (r + 1 : ℝ) ^ g' *
              ((2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1))) ^ g' :=
        Real.mul_rpow (by positivity) (Real.rpow_nonneg (by norm_num) _)
      have hpow_rpow :
          ((2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1))) ^ g' =
            (2 : ℝ) ^ (3 * g') * (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num)]
        have hexp_eq :
            (3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1) * g' =
              3 * g' + (3 * g' / (r : ℝ)) * (φ.length : ℝ) := by ring
        rw [hexp_eq, Real.rpow_add (by norm_num)]
      have hstepEq :
          ((r + 1 : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * ((φ.length : ℝ) / (r : ℝ) + 1))) ^ g' =
            ((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
              (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ)) := by
        rw [hmul, hpow_rpow]; ring
      exact le_trans hstepA (hstepB.trans_eq hstepEq)
    have henc_pow :
        (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ e ≤
          K_enc ^ e * (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
            (((encCNF φ).length : ℝ) + 1) ^ (e * D) := by
      have he1 := pow_le_pow_left₀ (by positivity) (henc_le φ) e
      calc
        (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ e
            ≤ (K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
                (((encCNF φ).length : ℝ) + 1) ^ D) ^ e := he1
        _ = K_enc ^ e *
              ((2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) ^ e *
              ((((encCNF φ).length : ℝ) + 1) ^ D) ^ e := by rw [mul_pow, mul_pow]
        _ = K_enc ^ e *
              (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
              (((encCNF φ).length : ℝ) + 1) ^ (e * D) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
            ← pow_mul]
          have hexp :
              (3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ) * (e : ℝ) =
                (3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ) := by ring
          rw [hexp, Nat.mul_comm D e]
    have hf_le : f r ≤ |f r| := le_abs_self (f r)
    have hcomb :
        (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ)) *
            (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) =
          (2 : ℝ) ^ (B * (φ.length : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      simp only [B]; ring
    have hV0 : 0 ≤ (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r := by positivity
    have henc0 :
        0 ≤ (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ e := by
      positivity
    have hfa : f r * (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r ≤
        |f r| * (((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
          (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ))) := by
      calc
        f r * (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r
            ≤ |f r| * (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r :=
          mul_le_mul_of_nonneg_right hf_le hV0
        _ ≤ |f r| * (((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
              (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ))) :=
          mul_le_mul_of_nonneg_left hV_pow (abs_nonneg _)
    have hterm :
        f r * (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r *
            (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ e ≤
          |f r| *
              (((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
                (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ))) *
              (K_enc ^ e * (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
                (((encCNF φ).length : ℝ) + 1) ^ (e * D)) :=
      mul_le_mul hfa henc_pow henc0 (by positivity)
    calc
      (t₂ (SAT.groupClique r φ) : ℝ)
          ≤ (c₂ : ℝ) * (f r * (((SAT.groupClique r φ).1.1.length : ℝ) + 1) ^ g r *
              (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ e) + c₂ := h1
      _ ≤ (c₂ : ℝ) * (|f r| *
              (((r + 1 : ℝ) ^ g' * (2 : ℝ) ^ (3 * g')) *
                (2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ))) *
              (K_enc ^ e * (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
                (((encCNF φ).length : ℝ) + 1) ^ (e * D))) + c₂ := by gcongr
      _ = A * ((2 : ℝ) ^ ((3 * g' / (r : ℝ)) * (φ.length : ℝ)) *
              (2 : ℝ) ^ ((3 * (e : ℝ) * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) *
            (((encCNF φ).length : ℝ) + 1) ^ (e * D) + c₂ := by
        simp only [A]; ring
      _ = A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ (e * D) + c₂ := by
        rw [hcomb]
  exact SAT.decidableInExpTime_threeSAT_of_groupClique_bound
    hdec hmem C₀ D r hr hred hδ.le hDr hA0 hB0 hBδ ht₂_le

/-- An `f(k) * |enc| ^ o(k)` algorithm for `Clique` places `ThreeSAT` in subexponential time
parameterized by clause count `List.length`. -/
theorem DecidableInSubexpTime.threeSAT_of_clique_subexpEnc
    (f g : ℕ → ℝ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k ≥ k₀, g k ≤ ε * k)
    (hClique : DecidableInTimeO Clique (encPair encGraph encNat)
      (fun x => f x.2 * (((encPair encGraph encNat x).length : ℝ) + 1) ^ g x.2)) :
    DecidableInSubexpTime ThreeSAT encCNF List.length := by
  intro δ hδ
  rcases DecidableInTimeO.exists_computableInO hClique with ⟨dec, t₂, c₂, hdec, hmem, ht₂⟩
  rcases SAT.exists_computableInO_groupClique with ⟨C₀, D, hred⟩
  have hε_pos : 0 < δ / (6 * ((D + 1 : ℕ) : ℝ)) := by positivity
  rcases hg (δ / (6 * ((D + 1 : ℕ) : ℝ))) hε_pos with ⟨k₀, hk₀⟩
  let r : ℕ := max 1 (max k₀ (Nat.ceil (6 * ((D + 1 : ℕ) : ℝ) / δ)))
  have hr : 1 ≤ r := le_max_left _ _
  have hrk : k₀ ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrc : 6 * ((D + 1 : ℕ) : ℝ) / δ ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hDr : (3 * (D : ℝ)) / (r : ℝ) ≤ δ := by
    have h1 : 6 * ((D + 1 : ℕ) : ℝ) ≤ δ * (r : ℝ) :=
      ((div_le_iff₀ hδ).mp hrc).trans_eq (mul_comm _ _)
    have hD_le : (D : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ D
    rw [div_le_iff₀ hr_pos]
    linarith
  let g' : ℝ := max (g r) 0
  have hg'0 : 0 ≤ g' := le_max_right _ _
  have hgr_le : g r ≤ g' := le_max_left _ _
  have hg' : g' ≤ (δ / (6 * ((D + 1 : ℕ) : ℝ))) * (r : ℝ) :=
    max_le (hk₀ r hrk) (mul_nonneg hε_pos.le hr_pos.le)
  let N_g : ℕ := Nat.ceil g'
  have hNg : g' ≤ (N_g : ℝ) := Nat.le_ceil g'
  let B : ℝ := (3 * (D : ℝ) * g') / (r : ℝ)
  have hB0 : 0 ≤ B := by positivity
  have hBδ : B ≤ δ := by
    have hD_le : (D : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ D
    have hmul : 3 * (D : ℝ) * g' ≤ 3 * ((D + 1 : ℕ) : ℝ) * g' := by gcongr
    have hmul2 : 3 * ((D + 1 : ℕ) : ℝ) * g' ≤ (δ / 2) * (r : ℝ) := by
      have heq : 3 * ((D + 1 : ℕ) : ℝ) * ((δ / (6 * ((D + 1 : ℕ) : ℝ))) * (r : ℝ)) =
          (δ / 2) * (r : ℝ) := by
        have hpos : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      calc
        3 * ((D + 1 : ℕ) : ℝ) * g'
            ≤ 3 * ((D + 1 : ℕ) : ℝ) * ((δ / (6 * ((D + 1 : ℕ) : ℝ))) * (r : ℝ)) := by gcongr
        _ = (δ / 2) * (r : ℝ) := heq
    have hhalf : (δ / 2) * (r : ℝ) ≤ δ * (r : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hr_pos.le
    exact (div_le_iff₀ hr_pos).mpr (le_trans hmul (le_trans hmul2 hhalf))
  have hred' := hred
  rcases hred' with ⟨c_len, _, hlen_red⟩
  let Lr : ℕ := (frame (encUnary r)).length + 1
  let K_enc : ℝ := (c_len : ℝ) * (C₀ : ℝ) * (2 : ℝ) ^ (3 * D) * (Lr : ℝ) ^ D + (c_len : ℝ) + 1
  have hK_enc0 : 0 ≤ K_enc := by positivity
  have henc_le := SAT.enc_groupClique_length_le r hr hlen_red
  let A : ℝ := (c₂ : ℝ) * |f r| * K_enc ^ g'
  have hA0 : 0 ≤ A := by positivity
  have ht₂_le : ∀ φ : CNF ℕ,
      (t₂ (SAT.groupClique r φ) : ℝ) ≤
        A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) + c₂ := by
    intro φ
    have h1 := ht₂ (SAT.groupClique r φ)
    rw [SAT.groupClique_snd hr] at h1
    have henc_pow :
        (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r ≤
          K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ)) *
            (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) := by
      have hge1 :
          (1 : ℝ) ≤ ((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ)
          (encPair encGraph encNat (SAT.groupClique r φ)).length]
      have hsA :
          (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r ≤
            (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g' :=
        Real.rpow_le_rpow_of_exponent_le hge1 hgr_le
      have hsB :
          (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g' ≤
            (K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
              (((encCNF φ).length : ℝ) + 1) ^ D) ^ g' :=
        Real.rpow_le_rpow (by positivity) (henc_le φ) hg'0
      have hmul1 :
          (K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ)) *
              (((encCNF φ).length : ℝ) + 1) ^ D) ^ g' =
            (K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) ^ g' *
              ((((encCNF φ).length : ℝ) + 1) ^ D) ^ g' :=
        Real.mul_rpow (by positivity) (by positivity)
      have hmul2 :
          (K_enc * (2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) ^ g' =
            K_enc ^ g' * ((2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) ^ g' :=
        Real.mul_rpow hK_enc0 (Real.rpow_nonneg (by norm_num) _)
      have hpow2g :
          ((2 : ℝ) ^ ((3 * (D : ℝ) / (r : ℝ)) * (φ.length : ℝ))) ^ g' =
            (2 : ℝ) ^ (B * (φ.length : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num)]
        congr 1
        simp only [B]; ring
      have hpolyg :
          ((((encCNF φ).length : ℝ) + 1) ^ D) ^ g' ≤
            (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) := by
        have hge_poly : (1 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ D :=
          one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
        calc
          ((((encCNF φ).length : ℝ) + 1) ^ D) ^ g'
              ≤ ((((encCNF φ).length : ℝ) + 1) ^ D) ^ (N_g : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge_poly hNg
          _ = (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) := by
            rw [Real.rpow_natCast, ← pow_mul]
      have hpoly_part :
          0 ≤ K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ)) := by positivity
      have hsAB :
          (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r ≤
            (K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ))) *
              ((((encCNF φ).length : ℝ) + 1) ^ D) ^ g' :=
        le_trans hsA (hsB.trans_eq (by rw [hmul1, hmul2, hpow2g]))
      calc
        (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r
            ≤ (K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ))) *
                ((((encCNF φ).length : ℝ) + 1) ^ D) ^ g' := hsAB
        _ ≤ (K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ))) *
              (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) :=
          mul_le_mul_of_nonneg_left hpolyg hpoly_part
        _ = K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ)) *
              (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) := by ring
    have hf_le : f r ≤ |f r| := le_abs_self (f r)
    have henc0 :
        0 ≤ (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r := by
      positivity
    calc
      (t₂ (SAT.groupClique r φ) : ℝ)
          ≤ (c₂ : ℝ) * (f r *
              (((encPair encGraph encNat (SAT.groupClique r φ)).length : ℝ) + 1) ^ g r) + c₂ :=
        h1
      _ ≤ (c₂ : ℝ) * (|f r| *
              (K_enc ^ g' * (2 : ℝ) ^ (B * (φ.length : ℝ)) *
                (((encCNF φ).length : ℝ) + 1) ^ (D * N_g))) + c₂ := by
        gcongr
      _ = A * (2 : ℝ) ^ (B * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ (D * N_g) + c₂ := by
        simp only [A]; ring
  exact SAT.decidableInExpTime_threeSAT_of_groupClique_bound
    hdec hmem C₀ D r hr hred hδ.le hDr hA0 hB0 hBδ ht₂_le

/-- Under `ETH`, `Clique` cannot be decided in `f(k) * |V| ^ o(k) * poly(|enc|)` time. -/
theorem ETH.not_clique_subexpVertex (hETH : ETH)
    (f g : ℕ → ℝ) (e : ℕ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k ≥ k₀, g k ≤ ε * k) :
    ¬DecidableInTimeO Clique (encPair encGraph encNat)
      (fun x =>
        let graph := x.1
        let verts := graph.1
        f x.2 * ((verts.length : ℝ) + 1) ^ g x.2 *
          (((encPair encGraph encNat x).length : ℝ) + 1) ^ e) := by
  intro hClique
  exact (ETH_iff_not_decidableInSubexpTime_length.mp hETH)
    (DecidableInSubexpTime.threeSAT_of_clique_subexpVertex f g e hg hClique)

/-- Under `ETH`, `Clique` cannot be decided in `f(k) * |enc| ^ o(k)` time. -/
theorem ETH.not_clique_subexpEnc (hETH : ETH)
    (f g : ℕ → ℝ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k ≥ k₀, g k ≤ ε * k) :
    ¬DecidableInTimeO Clique (encPair encGraph encNat)
      (fun x => f x.2 * (((encPair encGraph encNat x).length : ℝ) + 1) ^ g x.2) := by
  intro hClique
  exact (ETH_iff_not_decidableInSubexpTime_length.mp hETH)
    (DecidableInSubexpTime.threeSAT_of_clique_subexpEnc f g hg hClique)

/-- Under `ETH`, parameterized `Clique` is not fixed-parameter tractable (`Clique ∉ FPT`). -/
theorem ETH.clique_not_mem_FPT (hETH : ETH) :
    Clique ∉ FPT (encPair encGraph encNat) Prod.snd := by
  rw [mem_FPT]
  rintro ⟨f, c, hFPT⟩
  refine hETH.not_clique_subexpVertex (fun k => (f k : ℝ)) (fun _ => 0) c
    (fun ε hε => ⟨0, fun k _ => by positivity⟩) ?_
  simpa using hFPT

end Cslib.Complexity
