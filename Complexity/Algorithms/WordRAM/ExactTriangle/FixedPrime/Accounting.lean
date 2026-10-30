/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.FailureAccounting
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Indexing
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Failures

/-!
# Global accounting for actual catalogue query blocks

Each block is decoded from the real protected producer memory, in its original rank order.
The mathematical products are those computed by the concrete native product; their answer
correctness is proved, not assumed. Failed occurrences in distinct records therefore share
one global false-positive budget. These value lemmas supply the native loop invariant.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Existing original-weight witness condition restricted to one existing chunk and piece. -/
@[expose] def recordHit {m n g p : ℕ} (values : ℕ → ℤ) (idx : InstanceIndex p) : Prop :=
  ∃ q ∈ chunkOf (fun u v : Fin n => values (pairIndex (u, v))) (D m) p idx.1 idx.2.1,
    ∃ c ∈ piece n (D m) g idx.2.2,
      weightSum (fun u v : Fin n => values (pairIndex (u, v)))
        (fun b c => values (n * n + pairIndex (b, c)))
        (fun u c => values (2 * (n * n) + pairIndex (u, c))) q.1 q.2 c = 0

/-- Real per-record product, root, query and controller charges, excluding interval scans.
The constant includes the outer loop's two control instructions. -/
@[expose] noncomputable def recordBase {m n p : ℕ} (hn : 0 < n)
    (values : ℕ → ℤ) (mem : ℕ → ℕ) (idx : InstanceIndex p) : ℕ :=
  let Q := RecordProduct.recordQueryCount n (D m) p values idx
  let qs := RecordProduct.decodedQueries hn mem (RecordProduct.recordQueries n (D m) p idx) Q
  RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q + 61

/-- Number of accepted queries without an original witness in one actual producer block.
This is a value specification for charged native scans, not an executable scan oracle. -/
@[expose] noncomputable def recordFailures {m n g p : ℕ} (hn : 0 < n)
    (values : ℕ → ℤ) (mem : ℕ → ℕ) (idx : InstanceIndex p) : ℕ :=
  let qs := RecordProduct.decodedQueries hn mem (RecordProduct.recordQueries n (D m) p idx)
    (RecordProduct.recordQueryCount n (D m) p values idx)
  let default : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  Nat.count (fun i =>
    (RecordProduct.leftMatrix m n g p values idx * RecordProduct.rightMatrix m n g p values idx)
        (qs.getD i default).1 (qs.getD i default).2 ≠ 0 ∧
      scanPiece (fun a b => values (pairIndex (a, b)))
        (fun b c => values (n * n + pairIndex (b, c)))
        (fun a c => values (2 * (n * n) + pairIndex (a, c))) (D m) g idx.2.2
        (qs.getD i default).1 (qs.getD i default).2 = none) qs.length

/-- Every original query occurs at most once in each actual chunk. -/
theorem actual_queries_chunk {m n g p : ℕ} (hn : 0 < n) (values : ℕ → ℤ)
    {initial a : Data 64} (h : Instances.Output n (D m) g p values initial a)
    (hD : 16 ≤ D m) (hDn : D m ≤ n) (hp : p ≠ 0) (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) (D m) g p) :
    let qs := RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx)
      (RecordProduct.recordQueryCount n (D m) p values idx)
    qs.Nodup ∧ qs.toFinset = chunkOf
      (fun u v : Fin n => values (pairIndex (u, v))) (D m) p idx.1 idx.2.1 := by
  let wAB := fun u v : Fin n => values (pairIndex (u, v))
  have hc := QuerySpec.card_residueClass wAB hp
    (fun q => (values q % (p : ℤ)).toNat) (by intro pair; rfl) idx.1
  obtain ⟨-, hnodup, hset⟩ := RecordProduct.decodedQueries_chunkOf values wAB hn hp
    (by intro u v; rfl) (by omega) hDn h idx.1 idx.2.1
    ((mem_instanceIndices wAB idx).mp hidx).1
  rw [hc] at hnodup hset
  exact ⟨hnodup, hset⟩

/-- Add distinct actual records before applying the global bound; no per-record false-positive
allowance is duplicated. The real product's detection theorem supplies answer correctness. -/
theorem sum_recordFailures_le {m n g p : ℕ} (hn : 0 < n) (values : ℕ → ℤ)
    {initial a : Data 64} (h : Instances.Output n (D m) g p values initial a)
    (hD : 16 ≤ D m) (hDn : D m ≤ n) (hg : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (I : Finset (InstanceIndex p))
    (hI : I ⊆ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) (D m) g p) :
    (∑ idx ∈ I, recordFailures (m := m) (g := g) hn values a.mem idx) ≤
      falsePositiveCount (fun u v : Fin n => values (pairIndex (u, v)))
        (fun b c => values (n * n + pairIndex (b, c)))
        (fun u c => values (2 * (n * n) + pairIndex (u, c))) p := by
  classical
  let wAB := fun u v : Fin n => values (pairIndex (u, v))
  let wBC := fun b c : Fin n => values (n * n + pairIndex (b, c))
  let wAC := fun u c : Fin n => values (2 * (n * n) + pairIndex (u, c))
  let queries := fun idx => RecordProduct.decodedQueries hn a.mem
    (RecordProduct.recordQueries n (D m) p idx)
    (RecordProduct.recordQueryCount n (D m) p values idx)
  let ans := fun (idx : InstanceIndex p) (q : Fin n × Fin n) => decide
    ((RecordProduct.leftMatrix m n g p values idx *
      RecordProduct.rightMatrix m n g p values idx) q.1 q.2 ≠ 0)
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  have hans : AnswersCorrect wAB wBC wAC (D m) g p ans :=
    RecordProduct.product_answers_correct values wAB wBC wAC hD hg hp
      (by intro b c; rfl) (by intro u c; rfl)
  have hquery (idx) (hi : idx ∈ I) :=
    actual_queries_chunk hn values h hD hDn hp0 idx (hI hi)
  have hbound := sum_failed_occurrences_le wAB wBC wAC hp0 ans hans I hI queries
    (⟨0, hn⟩, ⟨0, hn⟩) (fun idx hi => (hquery idx hi).1) (by
      intro idx hi q hq
      change q ∈ chunkOf wAB (D m) p idx.1 idx.2.1
      rw [← (hquery idx hi).2, List.mem_toFinset]
      exact hq)
  simpa only [recordFailures, queries, ans, decide_eq_true_eq] using hbound

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
