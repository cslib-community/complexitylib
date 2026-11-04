/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prepare
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Kernel
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Bounds

/-!
# Initialized shared preparation and sparse box query

Original signed arrays and an output index determine both the actual shared table and
its native sparse traversal. The charged preparation is separate from the query's
leaf-count charge; the complete budget also includes the final halt.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Preparation, one actual sparse query, and the final halt. -/
@[expose] def timeBound {L : ℕ} (m t : ℕ) (η : OutStr L) : ℕ :=
  preparationTime L m t + queryTime m t η + 1

/-- The same initialized native execution constructs the table and computes the query,
restoring all memory outside its computed allocation. -/
theorem exec_input {w L m t A B : ℕ} (q : Fin (10 ^ L))
    (hη : (innerSetO (PrunedQuery.queryAt q)).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (originalAddressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input L m t q a b) ∧
    ∃ y, ExecWithin (w + 2) program (State.init (input L m t q a b)).data y
        (timeBound m t (PrunedQuery.queryAt q) - 1) ∧ y.Bounded (w + 2) ∧
      Parameters L t q.val 5 (5 + 10 ^ L) (directoryBase L) (valueBase L m t)
        (boxes L m t).card (stackBase L m t) y ∧
      y.regs Reg.top = 0 ∧
      y.regs Reg.answer = Signed.encode (queryValue m t (PrunedQuery.queryAt q)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))) ∧
      Readback m t (directoryBase L) (valueBase L m t) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L ≤ p ∧ p < memoryEnd L m t) →
        y.mem p = (State.init (input L m t q a b) : State registers).data.mem p) := by
  have hmL : m ≤ L := by
    have h := Finset.card_le_univ (innerSetO (PrunedQuery.queryAt q))
    simpa only [hη, Finset.card_univ, Fintype.card_fin] using h
  obtain ⟨hi, u, hu, _, uL, _, ut, uQ, _, uT, uD, _, uV, uK, uA, uB,
    uread, uframe⟩ := exec_prepare_input hmL q a b ha hb haddr hmag
  obtain ⟨y, hy, yp, ytop, yanswer, yread, yframe⟩ :=
    exec_queryProgram u (PrunedQuery.queryAt q) hη
      (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
      (fun τ => ha _) (fun τ => hb _) uL ut uT
      (by simpa only [PrunedQuery.queryIndex_queryAt] using uQ) uA uB uD uV uK rfl
      (by unfold valueBase recordBase directoryBase; omega)
      (by unfold valueBase recordBase directoryBase; omega)
      (by unfold valueBase recordBase; omega) uread
      (haddr.of_le (query_address_le L m t hmL)) hmag
  have he : ExecWithin (w + 2) program (State.init (input L m t q a b)).data y
      (timeBound m t (PrunedQuery.queryAt q) - 1) :=
    (hu.seq hy).mono (by unfold timeBound; omega)
  refine ⟨hi, y, he, he.bounded (Data.Bounded.init hi), ?_, ytop, yanswer, yread, ?_⟩
  · simpa only [PrunedQuery.queryIndex_queryAt, stackBase] using yp
  · intro p hp
    have hDF : directoryBase L ≤ valueBase L m t + (boxes L m t).card := by
      unfold valueBase recordBase
      omega
    rw [yframe p (by unfold memoryEnd stackBase at hp; omega)]
    exact uframe p (by unfold memoryEnd at hp; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
