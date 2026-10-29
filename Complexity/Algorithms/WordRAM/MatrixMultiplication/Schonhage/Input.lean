/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Exec
import Mathlib.Data.List.GetD

/-!
# Actual initialized-input clients for the shared encoders

## Main results

* `Encoding.exec_input`: flat signed array, concrete depth header and actual `State.init`.
* `Encoding.exec_left`, `Encoding.exec_right`: all public tensor encodings, at every depth.

The two programs and their thirty-two registers are independent of depth and word width.
Inputs are signed words encoded with `WordRAM.Signed.encode`; the depth and the machine's
length header are ordinary unsigned words. All input and reachable data words fit the target
width. Output and scratch are disjoint concrete blocks immediately after the input.

## References

The encodings are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CoordinateTransform

private theorem getD_ofFn {N : ℕ} (f : Fin N → ℤ) (i : Fin N) :
    (List.ofFn f).getD i.val 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The complete native encoder starts from the ordinary `State.init` convention with a
real depth header and encoded input words. It returns all flat shared-transform values, keeps
the input and every outside cell, and leaves only target-sized words in memory and registers. -/
theorem exec_input {w L : ℕ} (hw : 0 < w) (side : Bool) (a : Fin (7 ^ L) → ℤ)
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    InputFits (w + 2) (input L a) ∧
    ∃ y, ExecWithin (w + 2) (program side) (State.init (input L a)).data y (timeBound L) ∧
      y.Bounded (w + 2) ∧
      (∀ p < 10 ^ L, y.mem (outputBase L + p) = encode
        (value (table (coefficients side)) L 0 (fun i => (List.ofFn a).getD i 0) p 0)) ∧
      (∀ b, ¬(outputBase L ≤ b ∧ b < scratchBase L + 10 ^ L) →
        y.mem b = (State.init (input L a) : State 32).data.mem b) ∧
      y.regs output = outputBase L ∧ y.regs capacity = 10 ^ L := by
  have hi := input_fits hw a A hA ha hmag haddr
  let x : Data 32 := (State.init (input L a)).data
  have hheader : x.mem 1 = L := by
    simp [x, State.init, Data.init, input]
  have hinput (i : ℕ) (hi : i < 7 ^ L) :
      x.mem (2 + i) = encode ((List.ofFn a).getD i 0) := by
    have hidx : 2 + i = (i + 1) + 1 := by omega
    change (Data.init (input L a) : Data 32).mem (2 + i) = _
    rw [hidx, Data.init_mem_succ]
    simp only [input, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
    simpa using congrArg encode (getD_ofFn a ⟨i, hi⟩).symm
  have ha' (i : ℕ) (hi : i < 7 ^ L) : |(List.ofFn a).getD i 0| ≤ A := by
    rw [getD_ofFn a ⟨i, hi⟩]
    exact ha _
  obtain ⟨y, he, hv, hf, ho, hc⟩ := exec hw side (fun i => (List.ofFn a).getD i 0) x
    hheader hinput A hA ha' hmag haddr
  exact ⟨hi, y, he, he.bounded (Data.Bounded.init hi), hv, hf, ho, hc⟩

/-- Complete left encoder on arbitrary signed arrays indexed by the original seven-symbol
strings. Every one of the `10^L` leaves receives the unchanged public `encodingL` value. -/
theorem exec_left {w L : ℕ} (hw : 0 < w) (a : LeftStr L → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ u, |a u| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    InputFits (w + 2) (inputL a) ∧
    ∃ y, ExecWithin (w + 2) (program false) (State.init (inputL a)).data y (timeBound L) ∧
      y.Bounded (w + 2) ∧
      (∀ τ, y.mem (outputBase L + (leafIndex τ).val) = encode (encodingL a τ)) ∧
      (∀ b, ¬(outputBase L ≤ b ∧ b < scratchBase L + 10 ^ L) →
        y.mem b = (State.init (inputL a) : State 32).data.mem b) ∧
      y.regs output = outputBase L ∧ y.regs capacity = 10 ^ L := by
  let f : Fin (7 ^ L) → ℤ := fun i => a (fun ℓ => leftAt (finFunctionFinEquiv.symm i ℓ))
  obtain ⟨hi, y, he, hb, hv, hf, ho, hc⟩ := exec_input hw false f A hA (fun _ => ha _) hmag haddr
  refine ⟨hi, y, he, hb, ?_, hf, ho, hc⟩
  intro τ
  have harr (u : Fin L → Fin 7) : (List.ofFn f).getD (finFunctionFinEquiv u).val 0 =
      a (fun i => leftAt (u i)) := by
    rw [getD_ofFn]
    simp only [f, Equiv.symm_apply_apply]
  have h := hv (leafIndex τ) (leafIndex τ).isLt
  rw [value_final_left a _ harr τ] at h
  exact h

/-- Complete right encoder on arbitrary signed arrays with the original `encodingR` API. -/
theorem exec_right {w L : ℕ} (hw : 0 < w) (a : RightStr L → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ u, |a u| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    InputFits (w + 2) (inputR a) ∧
    ∃ y, ExecWithin (w + 2) (program true) (State.init (inputR a)).data y (timeBound L) ∧
      y.Bounded (w + 2) ∧
      (∀ τ, y.mem (outputBase L + (leafIndex τ).val) = encode (encodingR a τ)) ∧
      (∀ b, ¬(outputBase L ≤ b ∧ b < scratchBase L + 10 ^ L) →
        y.mem b = (State.init (inputR a) : State 32).data.mem b) ∧
      y.regs output = outputBase L ∧ y.regs capacity = 10 ^ L := by
  let f : Fin (7 ^ L) → ℤ := fun i => a (fun ℓ => rightAt (finFunctionFinEquiv.symm i ℓ))
  obtain ⟨hi, y, he, hb, hv, hf, ho, hc⟩ := exec_input hw true f A hA (fun _ => ha _) hmag haddr
  refine ⟨hi, y, he, hb, ?_, hf, ho, hc⟩
  intro τ
  have harr (u : Fin L → Fin 7) : (List.ofFn f).getD (finFunctionFinEquiv u).val 0 =
      a (fun i => rightAt (u i)) := by
    rw [getD_ofFn]
    simp only [f, Equiv.symm_apply_apply]
  have h := hv (leafIndex τ) (leafIndex τ).isLt
  rw [value_final_right a _ harr τ] at h
  exact h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
