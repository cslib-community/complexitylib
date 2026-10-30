/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer
import Mathlib.Data.List.Nodup

/-!
# The value of an actual decoded producer query block

The actual occurrence list is exactly the existing finite `chunkOf`, without repetitions,
and its `i`-th pair has class rank `k*queryCap+i`. Consumers can use original ET pairs directly
through this packaged readback; no alternative query notion or supplied routing table is added.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- The actual decoded list consists of all pairs of the existing chunk, once each, in
increasing class rank. The indexed equation specifies the order as well as set membership. -/
theorem decodedQueries_chunkOf {n D g p : ℕ} (values : ℕ → ℤ)
    (wAB : Fin n → Fin n → ℤ) (hn : 0 < n) (hp : p ≠ 0)
    (hAB : ∀ a b, values (pairIndex (a, b)) = wAB a b)
    (hD : 1 ≤ D) (hDn : D ≤ n)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (rho : Fin p) (k : ℕ)
    (hk : k < numChunks (residueClass wAB p rho) (queryCap n D)) :
    let q := 5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * queryCap n D)
    let Q := min (queryCap n D) ((residueClass wAB p rho).card - k * queryCap n D)
    let qs := decodedQueries hn y.mem q Q
    (∀ i : Fin qs.length, qs.get i ∈ chunkOf wAB D p rho k ∧
      rankIn (residueClass wAB p rho) (qs.get i) = k * queryCap n D + i.val) ∧
      qs.Nodup ∧ qs.toFinset = chunkOf wAB D p rho k := by
  let S := residueClass wAB p rho
  let cap := queryCap n D
  let q := 5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * cap)
  let Q := min cap (S.card - k * cap)
  let qs := decodedQueries hn y.mem q Q
  obtain ⟨-, hpair⟩ := output_query_coordinates values wAB hp hAB hD hDn h rho k hk
  have hget (i : Fin qs.length) : qs.get i ∈ chunkOf wAB D p rho k ∧
      rankIn S (qs.get i) = k * cap + i.val := by
    have hi : i.val < Q := by simpa only [qs, decodedQueries_length] using i.isLt
    obtain ⟨pair, hvalue, -⟩ := hpair i.val hi
    have hvA : y.mem (q + 2 * i.val) = pair.1.val := hvalue.2.2.1
    have hvB : y.mem (q + 2 * i.val + 1) = pair.2.val := hvalue.2.2.2
    have hv := decodedQueries_get_val hn y.mem q Q i
      (by rw [hvA]; exact pair.1.isLt) (by rw [hvB]; exact pair.2.isLt)
    have he : qs.get i = pair := by
      exact Prod.ext (Fin.ext (hv.1.trans hvA)) (Fin.ext (hv.2.trans hvB))
    rw [he]
    exact ⟨hvalue.1, hvalue.2.1⟩
  refine ⟨hget, ?_, ?_⟩
  · apply List.nodup_iff_injective_get.mpr
    intro i j hij
    have hi := (hget i).2
    have hj := (hget j).2
    exact Fin.ext (Nat.add_left_cancel
      (hi.symm.trans ((congrArg (rankIn S) hij).trans hj)))
  · apply Finset.ext
    intro pair
    rw [List.mem_toFinset]
    constructor
    · intro hm
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
      exact (hget i).1
    · intro hm
      have hchunk : pair ∈ S ∧ rankIn S pair / cap = k := by
        simpa only [chunkOf, chunk, Finset.mem_filter, S, cap] using hm
      have hrank := rankIn_lt_card hchunk.1
      have hcap : 0 < cap := one_le_queryCap hD hDn
      have hrem := Nat.mod_lt (rankIn S pair) hcap
      have hsplit := Nat.div_add_mod (rankIn S pair) cap
      rw [hchunk.2] at hsplit
      rw [Nat.mul_comm cap k] at hsplit
      have hi : rankIn S pair % cap < Q := by dsimp only [Q]; omega
      let i : Fin qs.length := ⟨rankIn S pair % cap, by
        simpa only [qs, decodedQueries_length] using hi⟩
      have hv := hget i
      have hmem : qs.get i ∈ S := by
        exact (Finset.mem_filter.mp hv.1).1
      have he : qs.get i = pair := rankIn_injOn S hmem hchunk.1 (by
        rw [hv.2]
        simpa only [i] using hsplit)
      exact List.mem_iff_get.mpr ⟨i, he⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
