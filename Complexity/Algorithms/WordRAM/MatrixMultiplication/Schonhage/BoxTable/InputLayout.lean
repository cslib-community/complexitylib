/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Geometry
public import Complexity.Computability.WordRAM.InputArray
public import Complexity.Computability.GenericRAM.Signed.Fits

/-!
# Original input and native box-table layout

Three raw headers are followed by the two canonical signed leaf arrays. The directory,
compact descriptors and values are allocated after those original arrays. Their extents
are computed from the depth and finite box cardinality; no layout is an input certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Ordinary scalar headers and two actual canonical signed encoding arrays. -/
@[expose] def input (L m t : ℕ) (a b : Fin (10 ^ L) → ℤ) : List ℕ :=
  [L, m, t] ++ List.ofFn (fun i => Signed.encode (a i)) ++
    List.ofFn (fun i => Signed.encode (b i))

/-- The directory starts immediately after the original input. -/
@[expose] def directoryBase (L : ℕ) : ℕ := 4 + 2 * 10 ^ L

/-- The compact descriptors follow the complete shared directory. -/
@[expose] def recordBase (L m t : ℕ) : ℕ :=
  directoryBase L + (m - t + 1) * 10 ^ L

/-- The actual value array follows three words per emitted record. -/
@[expose] def valueBase (L m t : ℕ) : ℕ := recordBase L m t + 3 * (boxes L m t).card

/-- End of the shared directory, compact descriptors and one complete value table. -/
@[expose] def memoryEnd (L m t : ℕ) : ℕ := valueBase L m t + (boxes L m t).card

/-- One original-input scalar envelope covers all address arithmetic of construction. -/
@[expose] def addressBound (L m t : ℕ) : ℕ :=
  100 * (L + m + t + (m - t + 1) * 10 ^ L + 10)

/-- One signed envelope covers operands even when their opposite array is identically zero. -/
@[expose] def magnitudeBound (L A B : ℕ) : ℕ := A + B + 10 ^ L * (A * B)

@[simp] theorem length_input (L m t : ℕ) (a b : Fin (10 ^ L) → ℤ) :
    (input L m t a b).length = 3 + 2 * 10 ^ L := by simp [input]; omega

/-- The actual input fits under the same original scalar and signed envelopes as execution. -/
theorem input_fits {w L m t A B : ℕ} (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (haddr : Fits (w + 2) (addressBound L m t))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    InputFits (w + 2) (input L m t a b) := by
  have hp : 1 ≤ 10 ^ L := Nat.one_le_pow L _ (by decide)
  have hS : 10 ^ L ≤ (m - t + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  constructor
  · rw [length_input]
    exact haddr.of_le (by unfold addressBound; omega)
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((rfl | rfl | rfl) | hv) | hv
    · exact haddr.of_le (by unfold addressBound; omega)
    · exact haddr.of_le (by unfold addressBound; omega)
    · exact haddr.of_le (by unfold addressBound; omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((ha i).trans
        (by unfold magnitudeBound; omega)))).mono (by omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (Signed.encode_fits (hmag.of_natAbs_le ((hb i).trans
        (by unfold magnitudeBound; omega)))).mono (by omega)

/-- Actual initialized words contain the two original signed arrays at their computed bases. -/
theorem input_readback (L m t : ℕ) (a b : Fin (10 ^ L) → ℤ) :
    let x : Data registers := (State.init (input L m t a b)).data
    x.mem 1 = L ∧ x.mem 2 = m ∧ x.mem 3 = t ∧
      (∀ i : Fin (10 ^ L), x.mem (4 + i.val) = Signed.encode (a i)) ∧
      (∀ i : Fin (10 ^ L), x.mem (4 + 10 ^ L + i.val) = Signed.encode (b i)) := by
  dsimp only
  refine ⟨by simp [State.init, Data.init, input], by simp [State.init, Data.init, input],
    by simp [State.init, Data.init, input], ?_, ?_⟩
  · intro i
    have h := Data.init_realizes_append (r := registers) [L, m, t]
      (List.ofFn (fun j => Signed.encode (a j))) (List.ofFn (fun j => Signed.encode (b j)))
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc] using hr
  · intro i
    have hfour (n : ℕ) : 1 + (1 + (1 + (1 + n))) = 4 + n := by omega
    have h := Data.init_realizes_append (r := registers)
      ([L, m, t] ++ List.ofFn (fun j => Signed.encode (a j)))
      (List.ofFn (fun j => Signed.encode (b j))) []
    have hr := h ⟨i.val, by simp⟩
    simpa [State.init, input, Block.read, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, hfour] using hr

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
