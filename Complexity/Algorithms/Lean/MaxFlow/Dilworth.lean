/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching
public import Complexity.Foundations.Order.Mirsky

/-!
# Dilworth's theorem by Fulkerson's reduction to König's theorem

*Dilworth's decomposition theorem* ([Dilworth1950]; [Schrijver2017], Theorem 7.6): in a finite
poset, the maximum size of an antichain equals the minimum number of chains covering it. The dual
statement, Mirsky's theorem, is `exists_isChain_and_antichain_coloring`.

This file follows the bipartite-matching proof usually credited to Fulkerson ([Fulkerson1956]).
Join a left copy of `x` to a right copy of `y` whenever `x < y` (`ltGraph`, a graph on `α × α` in
the sense of `IsMatching`). Then:

* **Matchings give chains.** Start with every element in its own chain and, for each matching
  edge `(u, v)`, append `v`'s chain after `u` (`mergeLabel`). Because no other matching edge
  leaves `u` or enters `v`, `u` is the top of its chain and `v` the bottom of its chain, so the
  result is again a chain, and the number of chains drops by one per edge
  (`foldl_mergeLabel_spec`). A matching `M` therefore yields a covering by `|α| - |M|` chains
  (`exists_chain_coloring_of_isMatching`).
* **Vertex covers give antichains.** If `C` is a vertex cover, the elements whose left and right
  copies are both uncovered (`VertexCover.uncovered`) form an antichain, since a comparable pair
  among them would be an uncovered edge (`isAntichain_uncovered`). There are at least
  `|α| - |C|` of them (`card_sub_size_le_card_uncovered`).

König's theorem (`exists_maxMatching_eq_minVertexCover`) supplies `M` and `C` with `|M| = |C|`,
which gives an antichain `A` and a covering by `|A|` chains. Weak duality
(`IsAntichain.card_le_of_isChain_fibre`) makes both optimal.

Chains and antichains are Mathlib's `IsChain (· ≤ ·)` and `IsAntichain (· ≤ ·)`. A covering by `k`
chains is a colouring `α → Fin k` whose fibres are chains. The results are for finite posets only.
The executable version, through Hopcroft–Karp, is `Cslib.Algorithms.Lean.MaxFlow.minChainCoverM`.

## Main definitions

* `ltGraph`: Fulkerson's bipartite graph of a strict order.
* `mergeLabel`: merge the chain of `v` into the chain of `u`.
* `VertexCover.uncovered`: the elements missed on both sides by a vertex cover.

## Main results

* `foldl_mergeLabel_spec`, `exists_chain_coloring_of_isMatching`: matchings give chain covers.
* `isAntichain_uncovered`, `card_sub_size_le_card_uncovered`: vertex covers give antichains.
* `exists_isAntichain_and_chain_coloring`: **Dilworth's theorem**, an antichain `A` and a covering
  by `|A|` chains.
* `exists_chain_coloring_iff`: **Dilworth's theorem**, min–max form: `α` is covered by `k` chains
  if and only if every antichain has at most `k` elements.

## References

* [R. P. Dilworth, *A decomposition theorem for partially ordered sets*][Dilworth1950]
* [D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered
  sets*][Fulkerson1956]
* [D. Kőnig, *Gráfok és mátrixok*][Koenig1931]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 7.3
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

variable {α γ : Type*}

/-- Fulkerson's bipartite graph of a strict order: the left copy of `x` is joined to the right copy
of `y` when `x < y`. -/
@[expose] def ltGraph [LT α] [DecidableLT α] : α × α → Bool := fun e => decide (e.1 < e.2)

@[simp] theorem ltGraph_apply [LT α] [DecidableLT α] (e : α × α) : ltGraph e = true ↔ e.1 < e.2 :=
  decide_eq_true_iff

/-- Relabel along the edge `(u, v)`: every element carrying `v`'s label receives `u`'s label. -/
@[expose] def mergeLabel [DecidableEq γ] (f : α → γ) : α × α → α → γ := fun e x =>
  if f x = f e.2 then f e.1 else f x

section Fulkerson

private theorem mergeLabel_eq_mergeLabel [DecidableEq γ] {f : α → γ} {u v x y : α} :
    mergeLabel f (u, v) x = mergeLabel f (u, v) y →
      f x = f y ∨ (f x = f u ∧ f y = f v) ∨ (f x = f v ∧ f y = f u) := by
  unfold mergeLabel
  dsimp only
  split_ifs <;> intro h <;> grind

variable [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableEq γ]

/-- Invariant of the chain construction: the fibres of `f` are chains, an element with no
outgoing (incoming) edge of `M` is the top (bottom) of its chain, and every edge of `M` has merged
two chains. -/
private structure ChainInv (f : α → γ) (M : Finset (α × α)) : Prop where
  chain : ∀ c, IsChain (· ≤ ·) (f ⁻¹' {c})
  top : ∀ x, (∀ y, (x, y) ∉ M) → ∀ y, f y = f x → y ≤ x
  bot : ∀ x, (∀ y, (y, x) ∉ M) → ∀ y, f y = f x → x ≤ y
  card : (Finset.univ.image f).card + M.card = Fintype.card α

omit [DecidableEq α] in
private theorem chainInv_of_injective {f : α → γ} (hf : Function.Injective f) : ChainInv f ∅ where
  chain c := Set.Subsingleton.isChain fun x hx y hy => hf (hx.trans hy.symm)
  top x _ y hy := (hf hy).le
  bot x _ y hy := (hf hy).ge
  card := by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Finset.card_empty]; rfl

private theorem ChainInv.merge {f : α → γ} {M : Finset (α × α)} (h : ChainInv f M) {u v : α}
    (huv : u < v) (hu : ∀ y, (u, y) ∉ M) (hv : ∀ y, (y, v) ∉ M) (huvM : (u, v) ∉ M) :
    ChainInv (mergeLabel f (u, v)) (insert (u, v) M) := by
  have hne : f u ≠ f v := fun he => (h.top u hu v he.symm).not_gt huv
  have below : ∀ x, f x = f u → x ≤ u := fun x hx => h.top u hu x hx
  have above : ∀ y, f y = f v → v ≤ y := fun y hy => h.bot v hv y hy
  refine ⟨fun c x hx y hy hxy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_, ?_⟩
  · have hxy' : mergeLabel f (u, v) x = mergeLabel f (u, v) y := hx.trans hy.symm
    rcases mergeLabel_eq_mergeLabel hxy' with he | ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · exact h.chain (f y) he rfl hxy
    · exact .inl ((below x hxu).trans (huv.le.trans (above y hyv)))
    · exact .inr ((below y hyu).trans (huv.le.trans (above x hxv)))
  · have hxM : ∀ y, (x, y) ∉ M := fun y hy => hx y (Finset.mem_insert_of_mem hy)
    have hxu : x ≠ u := fun he => hx v (he ▸ Finset.mem_insert_self _ _)
    rcases mergeLabel_eq_mergeLabel hy with he | ⟨hyu, hxv⟩ | ⟨hyv, hxu'⟩
    · exact h.top x hxM y he
    · exact (below y hyu).trans (huv.le.trans (above x hxv))
    · exact absurd (le_antisymm (h.top x hxM u hxu'.symm) (below x hxu')) hxu.symm
  · have hxM : ∀ y, (y, x) ∉ M := fun y hy => hx y (Finset.mem_insert_of_mem hy)
    have hxv : x ≠ v := fun he => hx u (he ▸ Finset.mem_insert_self _ _)
    rcases mergeLabel_eq_mergeLabel hy with he | ⟨hyu, hxv'⟩ | ⟨hyv, hxu⟩
    · exact h.bot x hxM y he
    · exact absurd (le_antisymm (above x hxv') (h.bot x hxM v hxv'.symm)) hxv.symm
    · exact (h.bot x hxM u hxu.symm).trans (huv.le.trans (above y hyv))
  · have himage : Finset.univ.image (mergeLabel f (u, v)) = (Finset.univ.image f).erase (f v) := by
      ext c
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, mergeLabel]
      constructor
      · rintro ⟨x, rfl⟩
        split_ifs with hx
        · exact ⟨hne, u, rfl⟩
        · exact ⟨hx, x, rfl⟩
      · rintro ⟨hc, x, rfl⟩
        exact ⟨x, ite_eq_right_iff.mpr fun h => absurd h hc⟩
    rw [himage, Finset.card_insert_of_notMem huvM, Finset.card_erase_of_mem
      (Finset.mem_image_of_mem f (Finset.mem_univ v))]
    have := h.card
    have hpos : 0 < (Finset.univ.image f).card :=
      Finset.card_pos.mpr ⟨f v, Finset.mem_image_of_mem f (Finset.mem_univ v)⟩
    omega

private theorem ChainInv.foldl [DecidableLT α] {M : Finset (α × α)} {f : α → γ} (h : ChainInv f M)
    {l : List (α × α)} (hl : l.Nodup) (hdisj : ∀ e ∈ l, e ∉ M)
    (hML : IsMatching ltGraph (M ∪ l.toFinset)) :
    ChainInv (l.foldl (mergeLabel ·) f) (M ∪ l.toFinset) := by
  induction l generalizing M f with
  | nil => simpa using h
  | cons e l ih =>
    obtain ⟨u, v⟩ := e
    have hmem : (u, v) ∈ M ∪ (List.toFinset ((u, v) :: l)) := by simp
    have huv : u < v := (ltGraph_apply _).mp (hML.1 _ hmem)
    have huvM : (u, v) ∉ M := hdisj _ (List.mem_cons_self ..)
    have hu : ∀ y, (u, y) ∉ M := fun y hy =>
      huvM (hML.2.1 u y v (Finset.mem_union_left _ hy) hmem ▸ hy)
    have hv : ∀ y, (y, v) ∉ M := fun y hy =>
      huvM (hML.2.2 y u v (Finset.mem_union_left _ hy) hmem ▸ hy)
    have hunion : M ∪ ((u, v) :: l).toFinset = insert (u, v) M ∪ l.toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    rw [List.foldl_cons, hunion]
    rw [hunion] at hML
    refine ih (h.merge huv hu hv huvM) (List.nodup_cons.mp hl).2 (fun e he heM => ?_) hML
    rcases Finset.mem_insert.mp heM with rfl | heM
    · exact (List.nodup_cons.mp hl).1 he
    · exact hdisj e (List.mem_cons_of_mem _ he) heM

/-- **Fulkerson's chain construction.** Folding `mergeLabel` over the edges of a matching of
`ltGraph`, starting from an injective labelling, leaves chain fibres, and the number of labels
drops by one per edge. -/
theorem foldl_mergeLabel_spec [DecidableLT α] {f : α → γ} (hf : Function.Injective f)
    {l : List (α × α)} (hl : l.Nodup) (hM : IsMatching ltGraph l.toFinset) :
    (∀ c, IsChain (· ≤ ·) (l.foldl (mergeLabel ·) f ⁻¹' {c})) ∧
      (Finset.univ.image (l.foldl (mergeLabel ·) f)).card + l.length = Fintype.card α := by
  have h := (chainInv_of_injective hf).foldl hl (fun _ _ => Finset.notMem_empty _)
    (by simpa using hM)
  rw [Finset.empty_union] at h
  exact ⟨h.chain, List.toFinset_card_of_nodup hl ▸ h.card⟩

end Fulkerson

section Covers

variable [PartialOrder α] [Fintype α]

/-- **Fulkerson's reduction, matchings to chains.** A matching `M` of `ltGraph` yields a covering
by `|α| - |M|` chains. -/
theorem exists_chain_coloring_of_isMatching [DecidableLT α] {M : Finset (α × α)}
    (hM : IsMatching (ltGraph (α := α)) M) :
    ∃ f : α → Fin (Fintype.card α - M.card), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) := by
  classical
  obtain ⟨hchain, hcard⟩ := foldl_mergeLabel_spec (f := id) Function.injective_id
    M.nodup_toList (by simpa using hM)
  set g := M.toList.foldl (mergeLabel ·) (id : α → α)
  have hk : (Finset.univ.image g).card = Fintype.card α - M.card := by
    rw [Finset.length_toList] at hcard
    omega
  let e := (Finset.univ.image g).equivFin.trans (finCongr hk)
  refine ⟨fun x => e ⟨g x, Finset.mem_image_of_mem g (Finset.mem_univ x)⟩, fun i x hx y hy => ?_⟩
  have : g x = g y := congrArg Subtype.val (e.injective (hx.trans hy.symm))
  exact hchain (g y) this rfl

variable [DecidableEq α]

/-- The elements whose left and right copies are both missed by a vertex cover of a graph on
`α × α`. -/
def VertexCover.uncovered (C : VertexCover α α) : Finset α :=
  Finset.univ.filter fun x => x ∉ C.left ∧ x ∉ C.right

omit [PartialOrder α] in
theorem mem_uncovered {C : VertexCover α α} {x : α} :
    x ∈ C.uncovered ↔ x ∉ C.left ∧ x ∉ C.right := by
  simp [VertexCover.uncovered]

/-- **Fulkerson's reduction, covers to antichains.** The elements that a vertex cover of `ltGraph`
misses on both sides form an antichain. -/
theorem isAntichain_uncovered [DecidableLT α] {C : VertexCover α α}
    (hC : IsVertexCover (ltGraph (α := α)) C) : IsAntichain (· ≤ ·) (C.uncovered : Set α) := by
  intro x hx y hy hxy hle
  rw [Finset.mem_coe, mem_uncovered] at hx hy
  rcases hC x y ((ltGraph_apply _).mpr (lt_of_le_of_ne hle hxy)) with h | h
  · exact hx.1 h
  · exact hy.2 h

omit [PartialOrder α] in
/-- A vertex cover of size `|C|` misses at least `|α| - |C|` elements on both sides. -/
theorem card_sub_size_le_card_uncovered (C : VertexCover α α) :
    Fintype.card α - C.size ≤ C.uncovered.card := by
  have h : C.uncovered = Finset.univ \ (C.left ∪ C.right) := by
    ext x
    simp [VertexCover.uncovered]
  have h1 := Finset.card_union_le C.left C.right
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ (C.left ∪ C.right)
  rw [Finset.univ_inter, Finset.card_univ] at h2
  rw [h, VertexCover.size]
  omega

end Covers

section Dilworth

variable [PartialOrder α] [Finite α]

/-- **Dilworth's decomposition theorem** ([Dilworth1950]; [Schrijver2017], Theorem 7.6): a finite
poset has an antichain `A` and a covering by `|A|` chains. The proof is Fulkerson's reduction
([Fulkerson1956]): a maximum matching `M` of `ltGraph` gives `|α| - |M|` chains, and König's
theorem gives a vertex cover of size `|M|`, which misses an antichain of at least `|α| - |M|`
elements. By weak duality `A` is a largest antichain and the covering uses the fewest chains. -/
theorem exists_isAntichain_and_chain_coloring :
    ∃ (A : Finset α) (f : α → Fin A.card),
      IsAntichain (· ≤ ·) (A : Set α) ∧ ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) := by
  classical
  cases nonempty_fintype α
  obtain ⟨M, C, hM, hC, hMC⟩ := exists_maxMatching_eq_minVertexCover (ltGraph (α := α))
  obtain ⟨f, hf⟩ := exists_chain_coloring_of_isMatching hM.1
  have hle : Fintype.card α - M.card ≤ C.uncovered.card :=
    hMC ▸ card_sub_size_le_card_uncovered C
  refine ⟨C.uncovered, fun x => Fin.castLE hle (f x), isAntichain_uncovered hC.1,
    fun i x hx y hy => ?_⟩
  have hxy : f x = f y := Fin.castLE_injective _ (hx.trans hy.symm)
  exact hf (f y) hxy rfl

/-- **Dilworth's decomposition theorem**, min–max form ([Schrijver2017], Theorem 7.6): a finite
poset can be covered by `k` chains if and only if every antichain has at most `k` elements. -/
theorem exists_chain_coloring_iff {k : ℕ} :
    (∃ f : α → Fin k, ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ↔
      ∀ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ k := by
  constructor
  · rintro ⟨f, hf⟩ A hA
    simpa using hA.card_le_of_isChain_fibre hf
  · intro hk
    obtain ⟨A, f, hA, hf⟩ := exists_isAntichain_and_chain_coloring (α := α)
    refine ⟨fun x => Fin.castLE (hk A hA) (f x), fun i x hx y hy => ?_⟩
    have hxy : f x = f y := Fin.castLE_injective _ (hx.trans hy.symm)
    exact hf (f y) hxy rfl

end Dilworth

end Cslib.Algorithms.Lean.MaxFlow
