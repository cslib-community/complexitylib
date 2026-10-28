/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Classes
public import Complexity.Algorithms.ExactTriangle.Splitting

/-!
# Native query ranks and the finite ExactTriangle chunks

The native scanner uses `Nat.count` on flat positions. The finite splitting construction uses
`Matrix.rankIn` on pairs. These lemmas identify their counts and ranks through the existing
row-major indexing; they introduce no alternative notion of a residue class or chunk.

## Main results

* `QuerySpec.card_residueClass`: the native count is the finite class cardinality.
* `QuerySpec.rank_residueClass`: native prefix rank is the existing finite rank.
* `QuerySpec.mem_chunkOf`: consecutive native query slices are the existing chunks.
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

end Cslib.Algorithms.WordRAM.ExactTriangle.QuerySpec
