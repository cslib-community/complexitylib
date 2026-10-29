/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Exec
import Mathlib.Data.List.GetD

/-!
# Ordinary initialized input for a callable product

The first input word is a runtime base pointer. An arbitrary caller prefix follows, then a
local ordinary input-length word and the unchanged original product input. No computed tables,
grouping, encodings, bounded scratch contents or execution certificates occur in this input.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Runtime location of the local length word after an arbitrary caller prefix. -/
@[expose] def inputBase (caller : List ℕ) : ℕ := caller.length + 2

/-- Original scalar headers, raw matrices and request pairs above a protected caller prefix. -/
@[expose] def input {m N : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : List ℕ :=
  let payload := QueriedProduct.input true (19 * m) X Y qs
  [inputBase caller] ++ caller ++ payload.length :: payload

/-- The initialized client loads the supplied runtime base before invoking the real kernel. -/
@[expose] def entryProgram : Code .standard 163 :=
  .seq (ram[ Reg.address ← #1; Reg.base ← *Reg.address ]) program

private theorem block_word (caller payload : List ℕ) (a : ℕ) :
    (Data.init ([inputBase caller] ++ caller ++ payload.length :: payload) : Data 163).mem
        (inputBase caller + a) = (Data.init payload : Data 160).mem a := by
  change (Data.init _ : Data 163).mem (caller.length + 2 + a) = _
  rw [show caller.length + 2 + a = (caller.length + 1 + a) + 1 by omega, Data.init_mem_succ]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_append, List.length_singleton]
  have hoff : caller.length + 1 + a - (1 + caller.length) = a := by omega
  rw [hoff]
  cases a with
  | zero => simp [Data.init]
  | succ a => simp [Data.init_mem_succ, List.getD_eq_getElem?_getD]

/-- Every local original input word has its actual initialized meaning at the runtime base. -/
theorem input_word {m N : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (a : ℕ) :
    (State.init (input caller X Y qs) : State 163).data.mem (inputBase caller + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a :=
  block_word caller _ a

/-- Original caller words and admitted original product words suffice for the global input fit. -/
theorem input_fits {W m N : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hcaller : ∀ v ∈ caller, Fits W v)
    (hfit : Fits W (inputBase caller + 4 * windowSize N qs.length + 1024)) :
    InputFits W (input caller X Y qs) := by
  have hXabs (i k) : |X i k| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hX i k).1]; exact (hX i k).2
  have hYabs (k j) : |Y k j| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hY k j).1]; exact (hY k j).2
  obtain ⟨hw, hmag, hbudget⟩ := source_admission (Q := qs.length) hN
  have htwo : sourceWidth N qs.length - 2 + 2 = sourceWidth N qs.length := by omega
  have hi := QueriedProduct.input_fits hw (show m ≤ 19 * m by omega)
    true X Y qs hXabs hYabs hmag (by simpa only [htwo] using hbudget)
  have hi' : InputFits (sourceWidth N qs.length) (QueriedProduct.input true (19 * m) X Y qs) := by
    simpa only [htwo] using hi
  have hlen : (QueriedProduct.input true (19 * m) X Y qs).length < windowSize N qs.length := hi'.1
  refine ⟨?_, ?_⟩
  · apply hfit.of_le
    simp only [input, List.length_append, List.length_cons, List.length_nil, inputBase]
    unfold inputBase at hfit
    omega
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((rfl | hv) | rfl | hv)
    · exact hfit.of_le (by omega)
    · exact hcaller _ hv
    · exact (hi'.1.mono (setup_fits hfit).1)
    · exact (hi'.2 v hv).mono (setup_fits hfit).1

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
