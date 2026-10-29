/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Classes
public import Complexity.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue
public import Complexity.Algorithms.ExactTriangle.Splitting
public import Mathlib.Data.Nat.Nth

/-!
# Native query ranks and the finite ExactTriangle chunks

The native scanner uses `Nat.count` on flat positions. The finite splitting construction uses
`Matrix.rankIn` on pairs. These lemmas identify their counts and ranks through the existing
row-major indexing; they introduce no alternative notion of a residue class or chunk.

## Main results

* `QuerySpec.card_residueClass`: the native count is the finite class cardinality.
* `QuerySpec.rank_residueClass`: native prefix rank is the existing finite rank.
* `QuerySpec.mem_chunkOf`: consecutive native query slices are the existing chunks.
* `QuerySpec.query_readback`: every occupied native query slot names exactly one class member.
* `QuerySpec.chunk_readback`: each local chunk slot names its unique existing finite member.
* `QuerySpec.before_eq_totalChunks`: the native catalogue count is the existing finite count.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.QuerySpec

open Cslib.Matrix Cslib.Algorithms.ExactTriangle

private theorem pairIndex_eq (n : ℕ) (q : Fin n × Fin n) :
    pairIndex q = (finProdFinEquiv q).val := by
  simp [pairIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

private theorem pairIndex_lt {n : ℕ} (q : Fin n × Fin n) : pairIndex q < n * n := by
  rw [pairIndex_eq]
  exact (finProdFinEquiv q).isLt

private theorem card_of_mem_pairIndex {n N : ℕ} (hN : N ≤ n * n)
    (S : Finset (Fin n × Fin n)) (P : ℕ → Prop) [DecidablePred P]
    (hS : ∀ q, q ∈ S ↔ pairIndex q < N ∧ P (pairIndex q)) :
    S.card = Nat.count P N := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun q _ => pairIndex q) ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((hS q).mp hq).1, ((hS q).mp hq).2⟩
  · intro q _ r _ h
    exact pairIndex_injective h
  · intro k hk
    obtain ⟨hkN, hkP⟩ := Finset.mem_filter.mp hk
    have hklt : k < n * n := (Finset.mem_range.mp hkN).trans_le hN
    let q := finProdFinEquiv.symm (⟨k, hklt⟩ : Fin (n * n))
    have hq : pairIndex q = k := by
      rw [pairIndex_eq]
      exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨k, hklt⟩)
    have hqS : q ∈ S := (hS q).mpr (by
      rw [hq]
      exact ⟨Finset.mem_range.mp hkN, hkP⟩)
    exact ⟨q, hqS, hq⟩

variable {n p : ℕ} (wAB : Fin n → Fin n → ℤ) (hp : p ≠ 0) (R : ℕ → ℕ)
  (hR : ∀ q : Fin n × Fin n, R (pairIndex q) = (resFin hp (wAB q.1 q.2)).val)

include hp hR

private theorem mem_class (rho : Fin p) (q : Fin n × Fin n) :
    q ∈ residueClass wAB p rho ↔ R (pairIndex q) = rho.val := by
  rw [mem_residueClass wAB hp, hR q]
  exact ⟨fun h => congrArg Fin.val h.symm, fun h => (Fin.ext h).symm⟩

/-- The count emitted by the native class scanner equals the existing finite class size. -/
theorem card_residueClass (rho : Fin p) :
    (residueClass wAB p rho).card = Nat.count (fun q => R q = rho.val) (n * n) :=
  card_of_mem_pairIndex le_rfl _ _ fun q => by
    rw [mem_class wAB hp R hR]
    exact ⟨fun h => ⟨pairIndex_lt q, h⟩, And.right⟩

/-- The concatenation controller's final counter is exactly the existing total chunk count.
The native table uses `Nat.count`; `card_residueClass` identifies each summand. -/
theorem before_eq_totalChunks (D : ℕ) :
    ChunkCatalogue.before (fun rho => Nat.count (fun q => R q = rho) (n * n))
      (queryCap n D) p = totalChunks wAB D p := by
  rw [totalChunks, ChunkCatalogue.before, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun rho _ => ?_
  rw [numChunks, card_residueClass wAB hp R hR]

/-- Iterating every actual catalogue entry over every piece creates exactly the existing
finite instance set's cardinality. This is the multiplier used by the native matrix caller. -/
theorem before_mul_numPieces (D g : ℕ) :
    ChunkCatalogue.before (fun rho => Nat.count (fun q => R q = rho) (n * n))
      (queryCap n D) p * numPieces n D g = (instanceIndices wAB D g p).card := by
  rw [before_eq_totalChunks wAB hp R hR, card_instanceIndices]

/-- Prefix rank agrees with the existing row-major rank used to split query chunks. -/
theorem rank_residueClass (rho : Fin p) (q : Fin n × Fin n) :
    rankIn (residueClass wAB p rho) q =
      Nat.count (fun j => R j = rho.val) (pairIndex q) :=
  card_of_mem_pairIndex (pairIndex_lt q).le _ _ fun r => by
    simp only [Finset.mem_filter, mem_class wAB hp R hR]
    exact and_comm

/-- Dividing the actual prefix rank by the query capacity gives precisely `chunkOf`. -/
theorem mem_chunkOf (D : ℕ) (rho : Fin p) (j : ℕ) (q : Fin n × Fin n) :
    q ∈ chunkOf wAB D p rho j ↔ R (pairIndex q) = rho.val ∧
      Nat.count (fun k => R k = rho.val) (pairIndex q) / queryCap n D = j := by
  simp only [chunkOf, chunk, Finset.mem_filter, mem_class wAB hp R hR,
    rank_residueClass wAB hp R hR]

/-- Every occupied native query slot names exactly one member of the existing residue class.
The readback premise is precisely the rank-indexed conclusion of `Classes.exec`; in particular,
this rules out unspecified or duplicate pairs below the computed count. -/
theorem query_readback (rho : Fin p) (mem : ℕ → ℕ) (base : ℕ)
    (hread : ∀ q < n * n, R q = rho.val →
      mem (base + 2 * Nat.count (fun j => R j = rho.val) q) = q / n ∧
      mem (base + 2 * Nat.count (fun j => R j = rho.val) q + 1) = q % n)
    (k : ℕ) (hk : k < (residueClass wAB p rho).card) :
    ∃! q : Fin n × Fin n, q ∈ residueClass wAB p rho ∧
      rankIn (residueClass wAB p rho) q = k ∧
      mem (base + 2 * k) = q.1.val ∧ mem (base + 2 * k + 1) = q.2.val := by
  rw [card_residueClass wAB hp R hR] at hk
  let P (q : ℕ) := R q = rho.val
  let t := Nat.nth P k
  have ht : t < n * n := Nat.nth_lt_of_lt_count hk
  have hfinite (hf : (Set.ofPred P).Finite) : k < hf.toFinset.card :=
    hk.trans_le (Nat.count_le_card hf (n * n))
  have htP : P t := Nat.nth_mem k hfinite
  have hcount : Nat.count P t = k := Nat.count_nth hfinite
  let q := finProdFinEquiv.symm (⟨t, ht⟩ : Fin (n * n))
  have hqindex : pairIndex q = t := by
    rw [pairIndex_eq]
    exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨t, ht⟩)
  have hq : q ∈ residueClass wAB p rho := (mem_class wAB hp R hR rho q).mpr (by
    rw [hqindex]
    exact htP)
  have hrank : rankIn (residueClass wAB p rho) q = k := by
    rw [rank_residueClass wAB hp R hR, hqindex]
    exact hcount
  have hcoords := hread t ht htP
  change mem (base + 2 * Nat.count P t) = t / n ∧
    mem (base + 2 * Nat.count P t + 1) = t % n at hcoords
  rw [hcount] at hcoords
  have hn : 0 < n := Nat.pos_of_ne_zero (by intro h; simpa [h] using q.1.isLt)
  have hrow : t / n = q.1.val := by
    rw [← hqindex, pairIndex, Nat.mul_comm q.1.val n, Nat.mul_add_div hn,
      Nat.div_eq_of_lt q.2.isLt, Nat.add_zero]
  have hcol : t % n = q.2.val := by
    rw [← hqindex, pairIndex, Nat.mul_add_mod_of_lt q.2.isLt]
  refine ⟨q, ⟨hq, hrank, hcoords.1.trans hrow, hcoords.2.trans hcol⟩, ?_⟩
  intro r hr
  exact rankIn_injOn _ hr.1 hq (hr.2.1.trans hrank.symm)

/-- Every occupied position of a native chunk names exactly one member of the existing finite
chunk. The local position is translated to its actual global class rank; the scanner's readback
premise is unchanged, so no list or ordering certificate is assumed. -/
theorem chunk_readback (D : ℕ) (rho : Fin p) (mem : ℕ → ℕ) (base : ℕ)
    (hread : ∀ q < n * n, R q = rho.val →
      mem (base + 2 * Nat.count (fun j => R j = rho.val) q) = q / n ∧
      mem (base + 2 * Nat.count (fun j => R j = rho.val) q + 1) = q % n)
    (hcap : 0 < queryCap n D) (k : ℕ)
    (hk : k < numChunks (residueClass wAB p rho) (queryCap n D))
    (r : ℕ) (hr : r < min (queryCap n D)
      ((residueClass wAB p rho).card - k * queryCap n D)) :
    ∃! q : Fin n × Fin n, q ∈ chunkOf wAB D p rho k ∧
      rankIn (residueClass wAB p rho) q = k * queryCap n D + r ∧
      mem (base + 2 * (k * queryCap n D + r)) = q.1.val ∧
      mem (base + 2 * (k * queryCap n D + r) + 1) = q.2.val := by
  have hkcard : k * queryCap n D < (residueClass wAB p rho).card := by
    by_contra h
    have hle : (residueClass wAB p rho).card ≤ k * queryCap n D := by omega
    have hceil := (Nat.ceilDiv_le_iff hcap).mpr hle
    change k < (residueClass wAB p rho).card ⌈/⌉ queryCap n D at hk
    omega
  have hrCap : r < queryCap n D := hr.trans_le (min_le_left _ _)
  have hrRem := hr.trans_le (min_le_right _ _)
  have hglobal : k * queryCap n D + r < (residueClass wAB p rho).card := by omega
  obtain ⟨q, hq, huniq⟩ := query_readback wAB hp R hR rho mem base hread _ hglobal
  have hdiv : (k * queryCap n D + r) / queryCap n D = k := by
    rw [Nat.mul_comm k (queryCap n D), Nat.mul_add_div hcap,
      Nat.div_eq_of_lt hrCap, Nat.add_zero]
  have hchunk : q ∈ chunkOf wAB D p rho k := by
    rw [mem_chunkOf wAB hp R hR]
    refine ⟨(mem_class wAB hp R hR rho q).mp hq.1, ?_⟩
    rw [← rank_residueClass wAB hp R hR, hq.2.1, hdiv]
  refine ⟨q, ⟨hchunk, hq.2⟩, ?_⟩
  intro q' hq'
  apply huniq q'
  exact ⟨(mem_class wAB hp R hR rho q').mpr
    ((mem_chunkOf wAB hp R hR D rho k q').mp hq'.1).1, hq'.2⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.QuerySpec
