/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.Dilworth
public import Complexity.Algorithms.Lean.MaxFlow.HopcroftKarp

/-!
# Minimum chain cover by Hopcroft–Karp

`minChainCoverM e` computes a minimum chain cover and a maximum antichain of a finite poset `α`,
given as an enumeration `e : Fin n ≃ α` with decidable `<`. It runs Fulkerson's reduction
(`Complexity.Algorithms.Lean.MaxFlow.Dilworth`) on the output of Hopcroft–Karp:

1. `hopcroftKarpDenseM (enumLtGraph e)` returns a maximum matching `M` and a minimum König cover
   `C` of the bipartite graph joining index `i` to index `j` when `e i < e j`.
2. Starting from the labels `i ↦ i`, `chainLabelsM` scans every pair of indices and, for each pair
   `(i, j) ∈ M`, relabels `j`'s chain with `i`'s label (`mergeChainsM`). The resulting label
   fibres are chains, and there are `n - |M|` labels.
3. The indices missed by `C` on both sides form an antichain of at least `n - |C| = n - |M|`
   elements (`uncoveredStep`).

`minChainCoverM_correct` proves that the label fibres are chains, the returned index set is an
antichain, and the number of labels equals the size of the antichain, `n - |M|`. With weak
duality this certifies both as optimal (`card_le_card_antichain_of_isAntichain`,
`card_antichain_le_of_isChain_fibre`), which is the algorithmic content of Dilworth's theorem.

## Cost model and limitations

* **Charged (`TimeM ℕ` ticks):** Hopcroft–Karp on the dense `n × n` instance
  (`hopcroftKarpDenseM_time_le`); `n` ticks to allocate the label table; `1` tick per scanned
  pair (`n²`); `n` ticks per merge, one per label entry rewritten (`≤ n |M| ≤ n²`); and `1` tick per
  index when collecting the antichain (`n`). The total is at most
  `(2⌊√n⌋ + 1) (10 n + 1 + 4 n²) + 2 n² + 6 n` (`minChainCoverM_time_le`), that is `O(n^{5/2})`.
* **Abstract unit-cost primitives:** as in `hopcroftKarpDenseM`, `Vector` reads and maps (inside
  a charged merge), `Finset` membership and insertion, `Fin n` comparisons, and order queries
  `e i < e j` are `O(1)` within each charged step. Computing `e` is not charged. This is an
  abstract RAM-style step count, not Turing-machine time.
* The scan over all `n²` pairs replaces iteration over `M`, which `Finset` does not provide
  computably; it stays within the Hopcroft–Karp bound.

## Main definitions

* `enumLtGraph`: Fulkerson's graph `ltGraph` read through an enumeration.
* `ChainCoverOutput`, `ChainCoverOutput.label`: chain labels, antichain and matching.
* `mergeChainsM`, `chainLabelsM`, `uncoveredStep`: the steps of the algorithm.
* `minChainCoverM`: the algorithm.

## Main results

* `minChainCoverM_correct`: chain fibres, an antichain, and equal sizes `n - |M|`.
* `card_le_card_antichain_of_isAntichain`, `card_antichain_le_of_isChain_fibre`: the output is a
  maximum antichain and the labels form a minimum chain cover.
* `minChainCoverM_time_le`: `O(n^{5/2})` charged steps.

## References

* [D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered
  sets*][Fulkerson1956]
* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 7.3
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean
open scoped TimeM

variable {α : Type*} {n : ℕ}

/-- Fulkerson's graph `ltGraph` read through an enumeration `e : Fin n ≃ α`: index `i` is joined
to index `j` when `e i < e j`. -/
@[expose] def enumLtGraph [LT α] [DecidableLT α] (e : Fin n ≃ α) : Fin n × Fin n → Bool :=
  fun p => ltGraph (e p.1, e p.2)

/-- Output of `minChainCoverM`. -/
structure ChainCoverOutput (n : ℕ) where
  /-- Chain label of each index; indices with equal labels lie on one chain. -/
  labels : Vector (Fin n) n
  /-- A maximum antichain, as a set of indices. -/
  antichain : Finset (Fin n)
  /-- The maximum matching of `enumLtGraph e` found by Hopcroft–Karp. -/
  matching : Finset (Fin n × Fin n)

/-- Merge the chain of index `j` into the chain of index `i`, for `p = (i, j)`: every label equal
to `j`'s becomes `i`'s. Charges `n` ticks, one per entry rewritten. -/
@[expose] def mergeChainsM (labels : Vector (Fin n) n) (p : Fin n × Fin n) :
    TimeM ℕ (Vector (Fin n) n) := do
  ✓[n] pure (Vector.ofFn fun i =>
    if vget labels i = vget labels p.2 then vget labels p.1 else vget labels i)

/-- Scan the candidate pairs `ps`, charging one tick per pair, and merge along those in `M`. -/
@[expose] def chainLabelsM (M : Finset (Fin n × Fin n)) :
    List (Fin n × Fin n) → Vector (Fin n) n → TimeM ℕ (Vector (Fin n) n)
  | [], labels => pure labels
  | p :: ps, labels => do
    ✓
    let labels ← if p ∈ M then mergeChainsM labels p else pure labels
    chainLabelsM M ps labels

/-- Insert index `i` into the antichain when the König cover `C` misses it on both sides. -/
@[expose] def uncoveredStep (C : VertexCover (Fin n) (Fin n)) (A : Finset (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  if i ∉ C.left ∧ i ∉ C.right then insert i A else A

/-- **Minimum chain cover** of a finite poset enumerated by `e : Fin n ≃ α`, by Fulkerson's
reduction: a maximum matching of `enumLtGraph e` from `hopcroftKarpDenseM`, chains obtained by
merging along its edges, and a maximum antichain read off the König cover. -/
@[expose] def minChainCoverM [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    TimeM ℕ (ChainCoverOutput n) := do
  let hk ← hopcroftKarpDenseM (enumLtGraph e)
  let labels₀ ← ✓[n] pure (Vector.ofFn id)
  let labels ← chainLabelsM hk.matching (List.finRange n ×ˢ List.finRange n) labels₀
  let antichain ← foldlTickM (uncoveredStep hk.cover) (List.finRange n) ∅
  pure ⟨labels, antichain, hk.matching⟩

/-- The chain label of `x : α` in an output `out` for the enumeration `e`. -/
@[expose] def ChainCoverOutput.label (e : Fin n ≃ α) (out : ChainCoverOutput n) (x : α) : Fin n :=
  vget out.labels (e.symm x)

/-- The number of chains of an output: the number of distinct labels in the table. -/
@[expose] def ChainCoverOutput.numChains (out : ChainCoverOutput n) : ℕ :=
  (Finset.univ.image (vget out.labels)).card

/-! ### Correctness -/

section Proofs

private theorem mem_foldl_uncoveredStep (C : VertexCover (Fin n) (Fin n)) (l : List (Fin n))
    (A : Finset (Fin n)) (i : Fin n) :
    i ∈ l.foldl (uncoveredStep C) A ↔ i ∈ A ∨ (i ∈ l ∧ i ∉ C.left ∧ i ∉ C.right) := by
  induction l generalizing A with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    unfold uncoveredStep
    split_ifs with h
    · rw [Finset.mem_insert]
      constructor
      · rintro ((rfl | hA) | ⟨hl, hc⟩)
        · exact .inr ⟨List.mem_cons_self .., h⟩
        · exact .inl hA
        · exact .inr ⟨List.mem_cons_of_mem _ hl, hc⟩
      · rintro (hA | ⟨hl, hc⟩)
        · exact .inl (.inr hA)
        · rcases List.mem_cons.mp hl with rfl | hl
          · exact .inl (.inl rfl)
          · exact .inr ⟨hl, hc⟩
    · constructor
      · rintro (hA | ⟨hl, hc⟩)
        · exact .inl hA
        · exact .inr ⟨List.mem_cons_of_mem _ hl, hc⟩
      · rintro (hA | ⟨hl, hc⟩)
        · exact .inl hA
        · rcases List.mem_cons.mp hl with rfl | hl
          · exact absurd hc h
          · exact .inr ⟨hl, hc⟩

private theorem foldl_uncoveredStep (C : VertexCover (Fin n) (Fin n)) :
    (List.finRange n).foldl (uncoveredStep C) ∅ = C.uncovered := by
  ext i
  rw [mem_foldl_uncoveredStep, mem_uncovered]
  simp

/-- One merge step on the label table is `mergeLabel` on the label function. -/
private theorem vget_mergeChainsM (e : Fin n ≃ α) (labels : Vector (Fin n) n)
    (p : Fin n × Fin n) :
    (fun x => vget (mergeChainsM labels p).ret (e.symm x)) =
      mergeLabel (fun x => vget labels (e.symm x)) (e p.1, e p.2) := by
  funext x
  simp only [mergeChainsM, mergeLabel, vget, TimeM.ret_bind, TimeM.ret_pure, Vector.getElem_ofFn,
    Equiv.symm_apply_apply]
  rfl

private theorem chainLabelsM_ret (e : Fin n ≃ α) (M : Finset (Fin n × Fin n))
    (ps : List (Fin n × Fin n)) (labels : Vector (Fin n) n) :
    (fun x => vget (chainLabelsM M ps labels).ret (e.symm x)) =
      ((ps.filter (· ∈ M)).map (Prod.map e e)).foldl (mergeLabel ·)
        (fun x => vget labels (e.symm x)) := by
  induction ps generalizing labels with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : p ∈ M
    · rw [List.filter_cons_of_pos (by simpa using hp), List.map_cons, List.foldl_cons]
      simp only [chainLabelsM, hp, ite_true, TimeM.ret_bind, ih]
      rw [vget_mergeChainsM]
      rfl
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      simp only [chainLabelsM, hp, ite_false, TimeM.ret_bind, TimeM.ret_pure, ih]

private theorem chainLabelsM_time (M : Finset (Fin n × Fin n)) (ps : List (Fin n × Fin n))
    (labels : Vector (Fin n) n) :
    (chainLabelsM M ps labels).time = ps.length + n * (ps.filter (· ∈ M)).length := by
  induction ps generalizing labels with
  | nil => simp [chainLabelsM]
  | cons p ps ih =>
    by_cases hp : p ∈ M
    · rw [List.filter_cons_of_pos (by simpa using hp)]
      simp only [chainLabelsM, hp, ite_true, TimeM.time_bind, TimeM.time_tick, ih, mergeChainsM,
        TimeM.time_pure, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      simp only [chainLabelsM, hp, ite_false, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
        ih, List.length_cons]
      omega

/-- Scanning all pairs of indices visits each element of `M` exactly once. -/
private theorem nodup_filter_pairs (M : Finset (Fin n × Fin n)) :
    ((List.finRange n ×ˢ List.finRange n).filter (· ∈ M)).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

private theorem mem_filter_pairs {M : Finset (Fin n × Fin n)} {p : Fin n × Fin n} :
    p ∈ (List.finRange n ×ˢ List.finRange n).filter (· ∈ M) ↔ p ∈ M := by
  obtain ⟨i, j⟩ := p
  simp

private theorem length_filter_pairs (M : Finset (Fin n × Fin n)) :
    ((List.finRange n ×ˢ List.finRange n).filter (· ∈ M)).length = M.card := by
  rw [← List.toFinset_card_of_nodup (nodup_filter_pairs M)]
  congr 1
  ext p
  rw [List.mem_toFinset, mem_filter_pairs]

private theorem ret_minChainCoverM [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (minChainCoverM e).ret =
      ⟨(chainLabelsM (hopcroftKarpDenseM (enumLtGraph e)).ret.matching
          (List.finRange n ×ˢ List.finRange n) (Vector.ofFn id)).ret,
        (hopcroftKarpDenseM (enumLtGraph e)).ret.cover.uncovered,
        (hopcroftKarpDenseM (enumLtGraph e)).ret.matching⟩ := by
  simp only [minChainCoverM, TimeM.ret_bind, TimeM.ret_pure, foldlTickM_ret, foldl_uncoveredStep]

variable [PartialOrder α] [DecidableLT α]

/-- **Correctness of `minChainCoverM`.** The label fibres are chains, the returned indices form an
antichain, and the number of labels equals the size of the antichain, namely `n - |M|` for the
maximum matching `M` found by Hopcroft–Karp. By weak duality the antichain is maximum and the
chain cover minimum (`card_le_card_antichain_of_isAntichain`,
`card_antichain_le_of_isChain_fibre`). -/
theorem minChainCoverM_correct (e : Fin n ≃ α) :
    (∀ c, IsChain (· ≤ ·) ((minChainCoverM e).ret.label e ⁻¹' {c})) ∧
      IsAntichain (· ≤ ·) (e '' (minChainCoverM e).ret.antichain) ∧
      (minChainCoverM e).ret.numChains = (minChainCoverM e).ret.antichain.card ∧
      (minChainCoverM e).ret.antichain.card + (minChainCoverM e).ret.matching.card = n := by
  classical
  let _ : Fintype α := Fintype.ofEquiv _ e
  obtain ⟨hmax, hmin, hcard, -⟩ := hopcroftKarpDenseM_correct (enumLtGraph e)
  rw [ret_minChainCoverM]
  generalize (hopcroftKarpDenseM (enumLtGraph e)).ret = hk at hmax hmin hcard
  set M := hk.matching
  set C := hk.cover
  set ps := (List.finRange n ×ˢ List.finRange n).filter (· ∈ M)
  set L := ps.map (Prod.map e e)
  have hlabel : ChainCoverOutput.label e ⟨(chainLabelsM M (List.finRange n ×ˢ List.finRange n)
      (Vector.ofFn id)).ret, C.uncovered, M⟩ =
      L.foldl (mergeLabel ·) (fun x => vget (Vector.ofFn id : Vector (Fin n) n) (e.symm x)) :=
    chainLabelsM_ret e M _ _
  have hinj : Function.Injective fun x => vget (Vector.ofFn id : Vector (Fin n) n) (e.symm x) :=
    fun x y h => e.symm.injective (by simpa [vget] using h)
  have hemb : Function.Injective (Prod.map e e) := e.injective.prodMap e.injective
  have hL : L.Nodup := (nodup_filter_pairs M).map hemb
  have hmemL : ∀ a b : α, (a, b) ∈ L ↔ (e.symm a, e.symm b) ∈ M := by
    intro a b
    simp only [L, ps, List.mem_map, mem_filter_pairs, Prod.exists, Prod.map, Prod.mk.injEq]
    constructor
    · rintro ⟨i, j, h, rfl, rfl⟩
      simpa using h
    · intro h
      exact ⟨_, _, h, by simp, by simp⟩
  have hmatch : IsMatching (ltGraph (α := α)) L.toFinset := by
    refine ⟨fun ⟨a, b⟩ h => ?_, fun a b₁ b₂ h₁ h₂ => ?_, fun a₁ a₂ b h₁ h₂ => ?_⟩
    · rw [List.mem_toFinset, hmemL] at h
      have := hmax.1.1 _ h
      simpa [enumLtGraph] using this
    · rw [List.mem_toFinset, hmemL] at h₁ h₂
      exact e.symm.injective (hmax.1.2.1 _ _ _ h₁ h₂)
    · rw [List.mem_toFinset, hmemL] at h₁ h₂
      exact e.symm.injective (hmax.1.2.2 _ _ _ h₁ h₂)
  obtain ⟨hchain, hnum⟩ := foldl_mergeLabel_spec hinj hL hmatch
  rw [← hlabel] at hchain hnum
  set lab := ChainCoverOutput.label e ⟨(chainLabelsM M (List.finRange n ×ˢ List.finRange n)
      (Vector.ofFn id)).ret, C.uncovered, M⟩
  have hcardα : Fintype.card α = n := (Fintype.card_congr e.symm).trans (Fintype.card_fin n)
  have hLlen : L.length = M.card := by rw [List.length_map, length_filter_pairs]
  have hrange : (Finset.univ.image lab) = Finset.univ.image (vget (chainLabelsM M
      (List.finRange n ×ˢ List.finRange n) (Vector.ofFn id)).ret) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [lab, ChainCoverOutput.label]⟩
  have hanti : IsAntichain (· ≤ ·) (e '' C.uncovered) := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij hle
    rw [Finset.mem_coe, mem_uncovered] at hi hj
    have hlt : e i < e j := lt_of_le_of_ne hle hij
    rcases hmin.1 i j (by simpa [enumLtGraph] using hlt) with h | h
    · exact hi.1 h
    · exact hj.2 h
  have hle : n - M.card ≤ C.uncovered.card := by
    have := card_sub_size_le_card_uncovered C
    rwa [Fintype.card_fin, ← hcard] at this
  have hge : C.uncovered.card ≤ (Finset.univ.image lab).card := by
    have hinjOn : Set.InjOn lab (e '' C.uncovered) :=
      hanti.injOn_of_isChain_fibre hchain
    calc C.uncovered.card = (C.uncovered.map e.toEmbedding).card := (Finset.card_map _).symm
      _ ≤ (Finset.univ.image lab).card :=
        Finset.card_le_card_of_injOn lab (fun x _ => Finset.mem_coe.mpr
          (Finset.mem_image_of_mem lab (Finset.mem_univ x)))
          (by rwa [Finset.coe_map, Equiv.coe_toEmbedding])
  rw [hrange] at hnum hge
  refine ⟨hchain, hanti, ?_, ?_⟩ <;> simp only [ChainCoverOutput.numChains] <;> omega

variable (e : Fin n ≃ α)

/-- The antichain returned by `minChainCoverM` is maximum. -/
theorem card_le_card_antichain_of_isAntichain {A : Finset α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) : A.card ≤ (minChainCoverM e).ret.antichain.card := by
  obtain ⟨hchain, -, hnum, -⟩ := minChainCoverM_correct e
  rw [← hnum]
  calc A.card = (A.image ((minChainCoverM e).ret.label e)).card :=
        (Finset.card_image_of_injOn (hA.injOn_of_isChain_fibre hchain)).symm
    _ ≤ (minChainCoverM e).ret.numChains := Finset.card_le_card fun c hc => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- The chain cover returned by `minChainCoverM` is minimum: every covering of `α` by `k` chains
has `k` at least the number of its labels. -/
theorem card_antichain_le_of_isChain_fibre {k : ℕ} {f : α → Fin k}
    (hf : ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) : (minChainCoverM e).ret.antichain.card ≤ k := by
  obtain ⟨-, hanti, -, -⟩ := minChainCoverM_correct e
  have h := IsAntichain.card_le_of_isChain_fibre (t := (minChainCoverM e).ret.antichain.map
    e.toEmbedding) (by rwa [Finset.coe_map, Equiv.coe_toEmbedding]) hf
  rwa [Finset.card_map, Fintype.card_fin] at h

end Proofs

/-! ### Running time -/

/-- **Running time of `minChainCoverM`**: `O(n^{5/2})` charged steps, dominated by
Hopcroft–Karp on the dense `n × n` instance. -/
theorem minChainCoverM_time_le [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (minChainCoverM e).time ≤ (2 * Nat.sqrt n + 1) * (10 * n + 1 + 4 * (n * n)) + 2 * (n * n) +
      6 * n := by
  have hhk := hopcroftKarpDenseM_time_le (enumLtGraph e)
  have hM := (hopcroftKarpDenseM_correct (enumLtGraph e)).1.1.card_le_card_left
  rw [Fintype.card_fin] at hM
  rw [min_self, show 7 * n + 3 * n = 10 * n by omega] at hhk
  simp only [minChainCoverM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, foldlTickM_time,
    chainLabelsM_time, length_filter_pairs, List.length_product, List.length_finRange]
  have := Nat.mul_le_mul_left n hM
  omega

end Cslib.Algorithms.Lean.MaxFlow
