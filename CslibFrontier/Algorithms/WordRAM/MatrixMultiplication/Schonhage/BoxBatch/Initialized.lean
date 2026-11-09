/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Prepare
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Exec

/-!
# Initialized execution of an entire native query batch

One actual table constructor and the complete batch loop share the same data witness.
Every original query occurrence has its signed result at the corresponding output
address, including repeated queries. The source arrays, wanted words and all memory
outside the computed allocation are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Construct one retained table from original input and execute every wanted query,
with separately charged shared preparation and complete native batch execution. -/
theorem exec_input {w L m t A B : ℕ} (hmL : m ≤ L) (qs : List (OutStr L))
    (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (originalAddressBound L m t qs.length))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input m t qs a b) ∧
    ∃ y, ExecWithin (w + 2) program (State.init (input m t qs a b)).data y
        (preparationTime L m t + queryTime m t qs) ∧
      y.Bounded (w + 2) ∧
      Arguments L t 5 (5 + 10 ^ L) (directoryBase L qs.length)
        (valueBase L m t qs.length) (boxes L m t).card y ∧
      y.regs Reg.next = queryBase L + qs.length ∧
      y.regs Reg.stop = queryBase L + qs.length ∧
      y.regs Reg.output = memoryEnd L m t qs.length ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m t qs.length + i.val) =
        Signed.encode (BoxQuery.queryValue m t (qs.get i)
          (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)))) ∧
      BoxQuery.Readback m t (directoryBase L qs.length) (valueBase L m t qs.length)
        5 (5 + 10 ^ L) (fun τ => a (Encoding.leafIndex τ))
          (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L qs.length ≤ p ∧ p < memoryEnd L m t qs.length) →
        y.mem p = (State.init (input m t qs a b) : State registers).data.mem p) := by
  have hi := input_fits qs a b ha hb haddr hmag
  obtain ⟨hL, hm, ht, hN, hleft, hright, hcodes⟩ := input_readback m t qs a b
  obtain ⟨u, hu, uL, ut, uT, uA, uB, uD, uV, uK, uQ, uN, uO, uread, uframe⟩ :=
    exec_prepare hmL (State.init (input m t qs a b)).data a b ha hb
      hL hm ht hN hleft hright haddr hmag
  have ucodes (i : Fin qs.length) :
      u.mem (queryBase L + i.val) = (PrunedQuery.queryIndex (qs.get i)).val := by
    rw [uframe _ (by unfold directoryBase; have := i.isLt; omega)]
    exact hcodes i
  obtain ⟨y, hy, ya, yQ, yN, yO, yvalues, yread, yframe⟩ :=
    exec_queryProgram qs u ⟨uL, ut, uT, uA, uB, uD, uV, uK⟩ uQ uN uO
      (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
      (fun τ => ha _) (fun τ => hb _) hη ucodes rfl
      (by unfold valueBase recordBase directoryBase queryBase; omega)
      (by unfold valueBase recordBase directoryBase queryBase; omega)
      (by unfold valueBase recordBase; omega)
      (by unfold valueBase recordBase directoryBase; omega)
      (by unfold outputBase stackBase; omega) uread
      (haddr.of_le (query_address_le L m t qs.length hmL)) hmag
  have he : ExecWithin (w + 2) program (State.init (input m t qs a b)).data y
      (preparationTime L m t + queryTime m t qs) := hu.seq hy
  refine ⟨hi, y, he, he.bounded (Data.Bounded.init hi), ya, yQ, yN, yO,
    yvalues, yread, ?_⟩
  intro p hp
  rw [yframe p (by
    simp only [memoryEnd, outputBase, stackBase, valueBase, recordBase] at hp ⊢
    omega), uframe p (by
    simp only [memoryEnd, outputBase, stackBase, valueBase, recordBase] at hp ⊢
    omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
