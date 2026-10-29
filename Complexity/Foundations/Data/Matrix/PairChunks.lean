/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.CeilDiv
public import Complexity.Foundations.Data.Finset.Quotient
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Fin

/-!
# Chunks of matrix index pairs

## Main definitions

* `pairIndex`, `rankIn`: row-major index and rank in a finite set.
* `chunk`, `numChunks`: consecutive chunks and their number.

## Main results

* `card_chunk_le`: each chunk has at most the capacity many pairs.
* `biUnion_chunk`: all chunks cover the input finite set.

## References

Adapted from [Chunks.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Chunks.lean) and the minimal definitions in
`PaperStatements.lean` at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
There are no graph or weight assumptions.
-/

@[expose] public section

namespace Cslib.Matrix

/-- The position of the pair `(a, b)` in the row-major order of `A × B`. -/
def pairIndex {n : ℕ} (q : Fin n × Fin n) : ℕ := q.1.val * n + q.2.val

/-- The number of pairs of `S` that come before `q` in row-major order. -/
def rankIn {n : ℕ} (S : Finset (Fin n × Fin n)) (q : Fin n × Fin n) : ℕ :=
  (S.filter fun r => pairIndex r < pairIndex q).card

/-- The `j`-th chunk (`j = 0, 1, …`) of `S` when `S` is cut, in row-major order, into chunks of
`cap` pairs each (the last one may be smaller). -/
def chunk {n : ℕ} (S : Finset (Fin n × Fin n)) (cap j : ℕ) : Finset (Fin n × Fin n) :=
  S.filter fun q => rankIn S q / cap = j

/-- The number `⌈|S| / cap⌉` of nonempty chunks of `S` (for `cap ≥ 1`). -/
def numChunks {n : ℕ} (S : Finset (Fin n × Fin n)) (cap : ℕ) : ℕ :=
  S.card ⌈/⌉ cap

variable {n : ℕ} {S : Finset (Fin n × Fin n)} {cap : ℕ}

/-! ### Ranks -/

/-- The position in row-major order determines the pair. -/
theorem pairIndex_injective : Function.Injective (pairIndex (n := n)) := fun q r h =>
  finProdFinEquiv.injective (Fin.ext (by simpa [pairIndex, add_comm, mul_comm] using h))

/-- Among the pairs of `S`, a pair that comes earlier in row-major order has a smaller rank. -/
theorem rankIn_lt_rankIn {q r : Fin n × Fin n} (hq : q ∈ S)
    (h : pairIndex q < pairIndex r) : rankIn S q < rankIn S r := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩
  · exact lt_irrefl _ (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hq, h⟩))).2

/-- Different pairs of `S` have different ranks. -/
theorem rankIn_injOn (S : Finset (Fin n × Fin n)) : Set.InjOn (rankIn S) S := by
  intro q hq r hr h
  rcases lt_trichotomy (pairIndex q) (pairIndex r) with hlt | heq | hgt
  · exact absurd h (rankIn_lt_rankIn hq hlt).ne
  · exact pairIndex_injective heq
  · exact absurd h (rankIn_lt_rankIn hr hgt).ne'

/-- The rank of a pair of `S` is less than the number of pairs of `S`. -/
theorem rankIn_lt_card {q : Fin n × Fin n} (hq : q ∈ S) : rankIn S q < S.card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _,
    fun hsub => lt_irrefl _ (Finset.mem_filter.mp (hsub hq)).2⟩

/-- In the full matrix, row-major rank is the row-major index itself. This avoids enumerating
all preceding pairs when applying the chunk API to a full matrix. -/
theorem rankIn_univ (q : Fin n × Fin n) :
    rankIn (Finset.univ : Finset (Fin n × Fin n)) q = pairIndex q := by
  calc rankIn (Finset.univ : Finset (Fin n × Fin n)) q
      = (Finset.Iio (finProdFinEquiv q)).card := by
        apply Finset.card_equiv finProdFinEquiv
        intro r
        simp [pairIndex, finProdFinEquiv, add_comm, mul_comm, Fin.lt_def]
    _ = pairIndex q := by simp [pairIndex, finProdFinEquiv, add_comm, mul_comm]

/-! ### Chunks -/

/-- A chunk has at most `cap` pairs: their ranks are different numbers in `[j cap, (j + 1) cap)`. -/
theorem card_chunk_le (S : Finset (Fin n × Fin n)) (hcap : 1 ≤ cap) (j : ℕ) :
    (chunk S cap j).card ≤ cap :=
  S.card_filter_div_eq_le (rankIn_injOn S) hcap j

/-- The first `⌈|S|/cap⌉` chunks cover `S`, because `|S| ≤ ⌈|S|/cap⌉ cap`. -/
theorem biUnion_chunk (S : Finset (Fin n × Fin n)) (hcap : 1 ≤ cap) :
    (Finset.range (numChunks S cap)).biUnion (fun j => chunk S cap j) = S := by
  have hcard : S.card ≤ numChunks S cap * cap := by
    rw [numChunks]
    exact Nat.le_ceilDiv_mul hcap
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_range, chunk, Finset.mem_filter]
  refine ⟨fun ⟨_, _, hq, _⟩ => hq, fun hq => ⟨rankIn S q / cap, ?_, hq, rfl⟩⟩
  exact (Nat.div_lt_iff_lt_mul hcap).mpr ((rankIn_lt_card hq).trans_le hcard)

end Cslib.Matrix
