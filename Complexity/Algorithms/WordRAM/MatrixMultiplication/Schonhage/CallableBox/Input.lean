/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Exec
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Input
import Mathlib.Data.List.GetD

/-!
# Ordinary initialized input for a callable product

The first input word is a runtime base pointer. An arbitrary caller prefix follows, then a
local ordinary input-length word and the unchanged original product input. No computed tables,
grouping, encodings, bounded scratch contents or execution certificates occur in this input.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct

open Cslib.WordRAM
open CallableProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original scalar headers, raw matrices and request pairs above a protected caller prefix. -/
@[expose] def input {m N : ℕ} (t : ℕ) (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : List ℕ :=
  let payload := BoxProduct.input true (21 * m) t X Y qs
  [inputBase caller] ++ caller ++ payload.length :: payload

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
theorem input_word {m N : ℕ} (t : ℕ) (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (a : ℕ) :
    (State.init (input t caller X Y qs) : State 163).data.mem (inputBase caller + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a :=
  block_word caller _ a

/-- Original caller words and admitted original product words suffice for the global input fit. -/
theorem input_fits {W m N : ℕ} (t : ℕ) (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hcaller : ∀ v ∈ caller, Fits W v)
    (hfit : Fits W (inputBase caller + 4 * windowSize N qs.length + 1024)) :
    InputFits W (input t caller X Y qs) := by
  have hXabs (i k) : |X i k| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hX i k).1]; exact (hX i k).2
  have hYabs (k j) : |Y k j| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hY k j).1]; exact (hY k j).2
  obtain ⟨hw, hmag, hbudget⟩ := source_admission (Q := qs.length) ht hN
  have htwo : sourceWidth N qs.length - 2 + 2 = sourceWidth N qs.length := by omega
  have hi := BoxProduct.input_fits hw (show m ≤ 21 * m by omega)
    true X Y qs hXabs hYabs hmag (by simpa only [htwo] using hbudget)
  have hi' : InputFits (sourceWidth N qs.length) (BoxProduct.input true (21 * m) t X Y qs) := by
    simpa only [htwo] using hi
  have hlen : (BoxProduct.input true (21 * m) t X Y qs).length < windowSize N qs.length := hi'.1
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

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct
