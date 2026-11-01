/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Magnitude
public import Complexity.Computability.WordRAM.InputArray
public import Complexity.Computability.GenericRAM.Signed.Fits

/-!
# Original input and workspace of a complete native box query

Four ordinary headers contain depth, inner count, threshold and the existing output
code. Both canonical signed leaf arrays follow. Shared geometry and retained values
are computed after these arrays; the query stack follows the actual compact table.
Original scalar and magnitude envelopes supply all preparation fits.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Four ordinary scalar words, followed by both actual signed leaf arrays. -/
@[expose] def input (L m t : ℕ) (q : Fin (10 ^ L)) (a b : Fin (10 ^ L) → ℤ) : List ℕ :=
  [L, m, t, q.val] ++ List.ofFn (fun i => Signed.encode (a i)) ++
    List.ofFn (fun i => Signed.encode (b i))

/-- First free word after the original headers and two arrays. -/
@[expose] def directoryBase (L : ℕ) : ℕ := 5 + 2 * 10 ^ L

/-- The compact three-word descriptors follow the computed shared directory. -/
@[expose] def recordBase (L m t : ℕ) : ℕ :=
  directoryBase L + (m - t + 1) * 10 ^ L

/-- The compact value table follows the actual number of emitted descriptors. -/
@[expose] def valueBase (L m t : ℕ) : ℕ := recordBase L m t + 3 * (boxes L m t).card

/-- The query stack starts after every retained compact value. -/
@[expose] def stackBase (L m t : ℕ) : ℕ := valueBase L m t + (boxes L m t).card

/-- One original-input address envelope covers setup and the complete native query stack. -/
@[expose] def originalAddressBound (L m t : ℕ) : ℕ :=
  10000 * (L + m + t + (L + 1) * 10 ^ L + 64)

/-- Preparation includes actual original-header adaptation, shared geometry and retained values. -/
@[expose] def preparationTime (L m t : ℕ) : ℕ :=
  4 * L + 21 + BoxTable.geometryTime L m t + 328 * (boxes L m t).card + 8

@[simp] theorem length_input (L m t : ℕ) (q : Fin (10 ^ L))
    (a b : Fin (10 ^ L) → ℤ) : (input L m t q a b).length = 4 + 2 * 10 ^ L := by
  simp [input]
  omega

/-- Actual initialized headers and array words have their original contents. -/
theorem input_readback (L m t : ℕ) (q : Fin (10 ^ L)) (a b : Fin (10 ^ L) → ℤ) :
    let x : Data registers := (State.init (input L m t q a b)).data
    x.mem 1 = L ∧ x.mem 2 = m ∧ x.mem 3 = t ∧ x.mem 4 = q.val ∧
      (∀ i : Fin (10 ^ L), x.mem (5 + i.val) = Signed.encode (a i)) ∧
      (∀ i : Fin (10 ^ L), x.mem (5 + 10 ^ L + i.val) = Signed.encode (b i)) := by
  dsimp only
  refine ⟨by simp [State.init, Data.init, input], by simp [State.init, Data.init, input],
    by simp [State.init, Data.init, input], by simp [State.init, Data.init, input], ?_, ?_⟩
  · intro i
    have h := Data.init_realizes_append (r := registers) [L, m, t, q.val]
      (List.ofFn (fun j => Signed.encode (a j))) (List.ofFn (fun j => Signed.encode (b j)))
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc] using hr
  · intro i
    have hfive (n : ℕ) : 1 + (1 + (1 + (1 + (1 + n)))) = 5 + n := by omega
    have h := Data.init_realizes_append (r := registers)
      ([L, m, t, q.val] ++ List.ofFn (fun j => Signed.encode (a j)))
      (List.ofFn (fun j => Signed.encode (b j))) []
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, hfive] using hr

/-- Original source and scalar envelopes derive the machine input-fit predicate. -/
theorem input_fits {w L m t A B : ℕ} (q : Fin (10 ^ L)) (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (originalAddressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input L m t q a b) := by
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  constructor
  · rw [length_input]
    exact haddr.of_le (by unfold originalAddressBound; omega)
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((rfl | rfl | rfl | rfl) | hv) | hv
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; omega)
    · exact haddr.of_le (by unfold originalAddressBound; have := q.isLt; omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((ha i).trans
        (by unfold magnitudeBound; omega)))).mono (by omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((hb i).trans
        (by unfold magnitudeBound; omega)))).mono (by omega)

/-- The larger query envelope also covers every unchanged box-table signed operation. -/
theorem table_magnitudeBound_le (L A B : ℕ) :
    A + B + 10 ^ L * (A * B) ≤ magnitudeBound L A B := by
  have hp : 10 ^ L ≤ 10 ^ (2 * L) := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hp) _

/-- The computed compact box count and original geometry fit the complete query envelope. -/
theorem constructor_address_le (L m t : ℕ) (hm : m ≤ L) :
    100 * (directoryBase L + 5 + (5 + 10 ^ L) + L + m + t +
      (m - t + 1) * 10 ^ L + 10) ≤ originalAddressBound L m t := by
  have hS : (m - t + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  unfold directoryBase originalAddressBound
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
