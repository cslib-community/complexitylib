/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Bounds

/-!
# The actual first prepared record exists

The fixed initialized composition selects ordinal zero. An original vertex pair belongs to
one existing residue class, so that class has a chunk and the vertex set has a piece. The native
ordinal characterization then supplies the unique existing finite index of the first record.
No nonempty catalogue or index certificate is an extra runtime input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix

/-- Under the real producer geometry, ordinal zero always names an existing finite instance. -/
theorem first_index {n D g p : ℕ} (values : ℕ → ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0) :
    ∃ idx : InstanceIndex p,
      idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p ∧
      recordOrdinal n D g p values idx = 0 := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) (n * n)
  have hn : 0 < n := by omega
  let a : Fin n := ⟨0, hn⟩
  let rho := resFin hp (wAB a a)
  have hmem : (a, a) ∈ residueClass wAB p rho :=
    (mem_residueClass wAB hp rho (a, a)).mpr rfl
  have hcard : 0 < (residueClass wAB p rho).card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hcap : 0 < queryCap n D := one_le_queryCap (by omega) hDn
  have hchunks : 0 < numChunks (residueClass wAB p rho) (queryCap n D) := by
    have hc : (residueClass wAB p rho).card ≤
        numChunks (residueClass wAB p rho) (queryCap n D) * queryCap n D :=
      Nat.le_ceilDiv_mul hcap
    by_contra h
    have he : numChunks (residueClass wAB p rho) (queryCap n D) = 0 := by omega
    rw [he, Nat.zero_mul] at hc
    omega
  have hpieces : 0 < numPieces n D g := by
    have hc : n ≤ numPieces n D g * pieceSize D g :=
      Nat.le_ceilDiv_mul (pieceSize_pos hD hg)
    by_contra h
    have he : numPieces n D g = 0 := by omega
    rw [he, Nat.zero_mul] at hc
    omega
  have hnonempty : (instanceIndices wAB D g p).Nonempty := by
    refine ⟨(rho, 0, 0), (mem_instanceIndices wAB _).mpr ⟨hchunks, hpieces⟩⟩
  have hcount : 0 < ChunkCatalogue.before C (queryCap n D) p * numPieces n D g := by
    rw [QuerySpec.before_mul_numPieces wAB hp R (by intro q; rfl)]
    exact Finset.card_pos.mpr hnonempty
  obtain ⟨idx, ⟨hidx, hzero⟩, -⟩ := PreparationSpec.index_unique values wAB hp
    (by intro a b; rfl) hD hDn hg 0 hcount
  exact ⟨idx, hidx, hzero.symm⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
