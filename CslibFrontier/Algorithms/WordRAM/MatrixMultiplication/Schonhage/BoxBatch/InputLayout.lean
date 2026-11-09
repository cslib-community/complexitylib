/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prepare

/-!
# Original input and allocation for a native query batch

Four headers contain depth, inner count, threshold and wanted-query count. Both signed
leaf arrays and the wanted codes follow. The table is constructed beyond these original
words; the work stack and result array follow the retained values. Wanted codes are
ordinary data, with their original order and repetitions preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original headers, signed leaf arrays, and ordinary wanted output codes. -/
@[expose] def input {L : ℕ} (m t : ℕ) (qs : List (OutStr L))
    (a b : Fin (10 ^ L) → ℤ) : List ℕ :=
  [L, m, t, qs.length] ++ List.ofFn (fun i => Signed.encode (a i)) ++
    List.ofFn (fun i => Signed.encode (b i)) ++
    qs.map (fun η => (PrunedQuery.queryIndex η).val)

/-- First wanted code, immediately after both original arrays. -/
@[expose] def queryBase (L : ℕ) : ℕ := 5 + 2 * 10 ^ L

/-- Shared geometry follows the entire wanted array. -/
@[expose] def directoryBase (L N : ℕ) : ℕ := queryBase L + N

/-- Compact descriptors follow the shared directory. -/
@[expose] def recordBase (L m t N : ℕ) : ℕ :=
  directoryBase L N + (m - t + 1) * 10 ^ L

/-- Retained signed values follow the compact descriptors. -/
@[expose] def valueBase (L m t N : ℕ) : ℕ :=
  recordBase L m t N + 3 * (boxes L m t).card

/-- The work stack starts beyond all retained table words. -/
@[expose] def stackBase (L m t N : ℕ) : ℕ :=
  valueBase L m t N + (boxes L m t).card

/-- Results follow the entire uncleared work-stack allocation. -/
@[expose] def outputBase (L m t N : ℕ) : ℕ :=
  stackBase L m t N + 5 * BoxQuery.stackCapacity L

/-- End of every potentially written word, including the result array. -/
@[expose] def memoryEnd (L m t N : ℕ) : ℕ := outputBase L m t N + N

/-- One original-input scalar bound covers adaptation, construction and batch execution. -/
@[expose] def originalAddressBound (L m t N : ℕ) : ℕ :=
  100000 * (L + m + t + N + (L + 1) * 10 ^ L + 64)

/-- Shared construction is paid once; the final twelve instructions adapt the batch layout. -/
@[expose] def preparationTime (L m t : ℕ) : ℕ :=
  BoxQuery.preparationTime L m t + 12

@[simp] theorem length_input {L : ℕ} (m t : ℕ) (qs : List (OutStr L))
    (a b : Fin (10 ^ L) → ℤ) :
    (input m t qs a b).length = 4 + 2 * 10 ^ L + qs.length := by
  simp only [input, List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn, List.length_map]
  omega

/-- Actual initialized scalar headers, source arrays and wanted codes. -/
theorem input_readback {L : ℕ} (m t : ℕ) (qs : List (OutStr L))
    (a b : Fin (10 ^ L) → ℤ) :
    let x : Data registers := (State.init (input m t qs a b)).data
    x.mem 1 = L ∧ x.mem 2 = m ∧ x.mem 3 = t ∧ x.mem 4 = qs.length ∧
      (∀ i : Fin (10 ^ L), x.mem (5 + i.val) = Signed.encode (a i)) ∧
      (∀ i : Fin (10 ^ L), x.mem (5 + 10 ^ L + i.val) = Signed.encode (b i)) ∧
      (∀ i : Fin qs.length, x.mem (queryBase L + i.val) =
        (PrunedQuery.queryIndex (qs[i.val])).val) := by
  dsimp only
  have hfive (n : ℕ) : 1 + (1 + (1 + (1 + (1 + n)))) = 5 + n := by omega
  refine ⟨by simp [State.init, Data.init, input], by simp [State.init, Data.init, input],
    by simp [State.init, Data.init, input], by simp [State.init, Data.init, input], ?_, ?_, ?_⟩
  · intro i
    have h := Data.init_realizes_append (r := registers) [L, m, t, qs.length]
      (List.ofFn (fun j => Signed.encode (a j)))
      (List.ofFn (fun j => Signed.encode (b j)) ++ qs.map (fun η => (PrunedQuery.queryIndex η).val))
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc] using hr
  · intro i
    have h := Data.init_realizes_append (r := registers)
      ([L, m, t, qs.length] ++ List.ofFn (fun j => Signed.encode (a j)))
      (List.ofFn (fun j => Signed.encode (b j)))
      (qs.map (fun η => (PrunedQuery.queryIndex η).val))
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, hfive] using hr
  · intro i
    have h := Data.init_realizes_append (r := registers)
      ([L, m, t, qs.length] ++ List.ofFn (fun j => Signed.encode (a j)) ++
        List.ofFn (fun j => Signed.encode (b j)))
      (qs.map (fun η => (PrunedQuery.queryIndex η).val)) []
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, queryBase, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul, hfive] using hr

/-- Original scalar and source envelopes admit the complete physical input. -/
theorem input_fits {w L m t A B : ℕ} (qs : List (OutStr L))
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (originalAddressBound L m t qs.length))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input m t qs a b) := by
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  constructor
  · rw [length_input]
    exact haddr.of_le (by unfold originalAddressBound; omega)
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (((rfl | rfl | rfl | rfl) | hv) | hv) | hv
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((ha i).trans
        (by unfold BoxQuery.magnitudeBound; omega)))).mono (by omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((hb i).trans
        (by unfold BoxQuery.magnitudeBound; omega)))).mono (by omega)
    · obtain ⟨η, _, rfl⟩ := List.mem_map.mp hv
      exact haddr.of_le (by
        have := (PrunedQuery.queryIndex η).isLt
        unfold originalAddressBound
        omega)

/-- Original bounds cover the unchanged complete shared-table constructor. -/
theorem constructor_address_le (L m t N : ℕ) (hm : m ≤ L) :
    100 * (directoryBase L N + 5 + (5 + 10 ^ L) + L + m + t +
      (m - t + 1) * 10 ^ L + 10) ≤ originalAddressBound L m t N := by
  have hS : (m - t + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  unfold directoryBase queryBase originalAddressBound
  omega

/-- Original bounds also cover the batch kernel, including every cursor increment. -/
theorem query_address_le (L m t N : ℕ) (hm : m ≤ L) :
    BoxQuery.queryAddressBound L t 5 (5 + 10 ^ L) (directoryBase L N)
      (valueBase L m t N) (boxes L m t).card + queryBase L + outputBase L m t N + 2 * N + 1 ≤
      originalAddressBound L m t N := by
  have hK := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hK
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  unfold BoxQuery.queryAddressBound outputBase stackBase valueBase recordBase
    directoryBase queryBase BoxQuery.stackCapacity originalAddressBound
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
