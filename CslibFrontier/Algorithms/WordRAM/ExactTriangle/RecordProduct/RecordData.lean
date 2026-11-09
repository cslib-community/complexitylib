/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.ProducerQueries

/-!
# Pure record data from the actual native producer

Record ordinals, query spans and raw matrix values are shared by both product backends.
This module does not import a per-record product execution or initialized caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The unchanged complete producer occupies the original low register bank. -/
@[expose] def producerBank (i : Fin 64) : Fin 320 := i.castLE (by decide)

/-- Existing native writer arguments, with pointer fields omitted from the value-only view. -/
@[expose] def matrixArgs (n D g p rho piece : ℕ) : WriteMatrices.Args :=
  ⟨0, 0, n, D, p, piece * pieceSize D g,
    min (pieceSize D g) (n - piece * pieceSize D g), rho⟩

/-- Exact raw left adjacency matrix written by the actual producer. -/
@[expose] def leftMatrix (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    Matrix (Fin n) (Fin (D m)) ℤ := fun a k =>
  (WriteMatrices.entry false (matrixArgs n (D m) g p idx.1.val idx.2.2)
    (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) (a.val * D m + k.val) : ℤ)

/-- Exact raw right adjacency matrix, in its actual `D×n` storage order. -/
@[expose] def rightMatrix (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    Matrix (Fin (D m)) (Fin n) ℤ := fun k a =>
  (WriteMatrices.entry true (matrixArgs n (D m) g p idx.1.val idx.2.2)
    (fun q => (values (n * n + q) % (p : ℤ)).toNat) (k.val * n + a.val) : ℤ)

/-- The readback matrices satisfy the raw callee's original-entry hypotheses. -/
theorem matrices_zero_one (m n g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) :
    (∀ a k, 0 ≤ leftMatrix m n g p values idx a k ∧
      leftMatrix m n g p values idx a k ≤ 1) ∧
    (∀ k a, 0 ≤ rightMatrix m n g p values idx k a ∧
      rightMatrix m n g p values idx k a ≤ 1) := by
  constructor <;> intro a k
  · exact ⟨Int.natCast_nonneg _, by
      dsimp only [leftMatrix]
      exact_mod_cast WriteMatrices.entry_le_one false _ _ _⟩
  · exact ⟨Int.natCast_nonneg _, by
      dsimp only [rightMatrix]
      exact_mod_cast WriteMatrices.entry_le_one true _ _ _⟩

/-- The actual computed ordinal of an existing finite class/chunk/piece. This is a value
specification for the caller's selection register, not a table supplied to the adapter. -/
@[expose] def recordOrdinal (n D g p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) : ℕ :=
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  (ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1) * numPieces n D g + idx.2.2

/-- Actual descriptor occurrence count, rather than an assumed sparse set size. -/
@[expose] def recordQueryCount (n D p : ℕ) (values : ℕ → ℤ) (idx : InstanceIndex p) : ℕ :=
  min (queryCap n D)
    (Nat.count (fun q => (values q % (p : ℤ)).toNat = idx.1.val) (n * n) -
      idx.2.1 * queryCap n D)

/-- Every occupied finite instance has a nonempty actual descriptor query slice. -/
theorem recordQueryCount_pos {n D g p : ℕ} (values : ℕ → ℤ) (hp : p ≠ 0)
    (hD : 1 ≤ D) (hDn : D ≤ n) (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    0 < recordQueryCount n D p values idx := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let R := fun q => (values q % (p : ℤ)).toNat
  have hk := ((mem_instanceIndices wAB idx).mp hidx).1
  have hcard := QuerySpec.card_residueClass wAB hp R (by intro q; rfl) idx.1
  have hcap : 0 < queryCap n D := one_le_queryCap hD hDn
  have hkcard : idx.2.1 * queryCap n D < (residueClass wAB p idx.1).card := by
    by_contra h
    have hc := (Nat.ceilDiv_le_iff hcap).mpr
      (by omega : (residueClass wAB p idx.1).card ≤ idx.2.1 * queryCap n D)
    change idx.2.1 < (residueClass wAB p idx.1).card ⌈/⌉ queryCap n D at hk
    omega
  rw [hcard] at hkcard
  unfold recordQueryCount
  change 0 < min (queryCap n D) (Nat.count (fun q => R q = idx.1.val) (n * n) -
    idx.2.1 * queryCap n D)
  omega

/-- Actual query pointer into the protected producer catalogue. -/
@[expose] def recordQueries (n D p : ℕ) (idx : InstanceIndex p) : ℕ :=
  5 + 6 * (n * n) + p + 2 * idx.1.val * (n * n) + 2 * (idx.2.1 * queryCap n D)

/-- The complete real producer, using its original low bank. -/
@[expose] def produce : Code .standard 320 := Instances.program.rename producerBank

/-- The unchanged producer's original-header budget, including its standalone halt. -/
@[expose] def preparationTime (n D g p : ℕ) (values : List ℤ) : ℕ :=
  let C := fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n)
  Instances.timeBound n D p (ChunkCatalogue.before C (queryCap n D) p) (numPieces n D g)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
