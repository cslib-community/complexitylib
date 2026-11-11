/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Streaming list emission with actual callback resource sums

Unlike a polynomial callback bound in the entire record, these bounds preserve
the callback's given time and space profiles. The machine streams each emitted
list; time sums actual rounds and workspace takes a maximum, with the final
materialized output charged separately. This supports output-sensitive class
joins whose records are entire quarter buckets.

## Main definitions

* `streamFlatMapTime`, `streamFlatMapSpace`: charged round sum and simultaneous space.

## Main results

* `ComputableInO.flatMap_stream_sum`: execute a concrete list callback with these bounds.
-/

public section
namespace Turing.MultiTapeTM

/-- Actual callback times plus parameter/token replay and the input scan. -/
@[expose] def streamFlatMapTime {π α : Type} (encP : π ↪ List Bool) (encA : α ↪ List Bool)
    (T : π × α → ℕ) (input : π × List α) : ℕ :=
  let (parameter, rows) := input
  (encPair encP (encList encA) input).length +
    (rows.map (fun row => T (parameter, row) + (encPair encP encA (parameter, row)).length + 1)).sum

/-- Input, maximum callback workspace and materialized output coexist; round times are not
added to workspace. -/
@[expose] def streamFlatMapSpace {π α β : Type} (encP : π ↪ List Bool) (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (f : π × α → List β) (S : π × α → ℕ)
    (input : π × List α) : ℕ :=
  let (parameter, rows) := input
  (encPair encP (encList encA) input).length + listMax (fun row => S (parameter, row)) rows +
    (encList encB (rows.flatMap (fun row => f (parameter, row)))).length

/-- Stream concrete callback executions and their output, summing time and taking peak space.
No polynomial in a whole bucket is introduced by the streaming control. -/
theorem ComputableInO.flatMap_stream_sum {π α β : Type} {encP : π ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : π × α → List β}
    {T S : π × α → ℕ} (hf : ComputableInO f (encPair encP encA) (encList encB) T S) :
    ComputableInO (fun (parameter, rows) => rows.flatMap (fun row => f (parameter, row)))
      (encPair encP (encList encA)) (encList encB)
      (streamFlatMapTime encP encA T) (streamFlatMapSpace encP encA encB f S) := by
  have decode : ComputableInO (id : α → α) (encFramed encA) encA
      (fun a => (encFramed encA a).length) (fun a => (encFramed encA a).length) :=
    .of_linear (.of_unframe (fun _ => by simp))
  have arg := (ComputableInO.fst encP (encFramed encA)).prod
    (decode.comp_linear (ComputableInO.snd encP (encFramed encA)))
  have he : ComputableInO (fun q : π × α => encList encB (f q)) (encPair encP encA) encBits T S :=
    hf.of_enc_eq (fun _ => rfl)
  obtain ⟨cE, hE, _⟩ := (he.comp arg).tidy
  simp only [Function.comp_def, id_eq] at hE
  obtain ⟨cN, hN, _⟩ := (ComputableInO.fst encP (encFramed encA)).tidy
  obtain ⟨cF, hF⟩ := computableInTimeAndSpace_of_const
    (encIn := encP) (encOut := encBits) ([] : List Bool)
  let K := 10 * (cE + cN + 1)
  have rowBound (input : π × List α) (row : α) (hr : row ∈ input.2) :
      (encPair encP encA (input.1, row)).length ≤ (encPair encP (encList encA) input).length := by
    have := length_le_encList_of_mem encA hr
    simp only [length_encPair]
    omega
  have streaming := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun (parameter, rows) => rows.flatMap (fun row => f (parameter, row)))
    (encA := encFramed encA) (encIn := encPair encP (encList encA))
    (encOut := encList encB) (next := Prod.fst)
    rawFrameReader (fun row => frame (encA row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hN hE hF.computableTidilyInTimeAndSpace
    (fun input => by simp only [encBits_apply, flatMap_emission,
      Function.const_apply, List.append_nil])
    (roundCost := fun input j => if hj : j < input.2.length then K *
      (T (input.1, input.2[j]) + (encPair encP encA (input.1, input.2[j])).length + 1) else 0)
    (sMax := fun input => cN * (2 * (encPair encP (encList encA) input).length + 2) +
      cE * (4 * (encPair encP (encList encA) input).length +
        listMax (fun row => S (input.1, row)) input.2 + 3))
    (lMax := fun input => 2 * (encPair encP (encList encA) input).length + 2) ?_ ?_ ?_ ?_
  · obtain ⟨C, hc⟩ := streaming
    let D := C * (K + 2*cF + 2*cN + 4*cE + 100) + 1
    refine ComputableInO.of_bounds hc.computableInTimeAndSpace D ?_ ?_ ?_
    · intro input
      let I := (encPair encP (encList encA) input).length
      let u := fun row => T (input.1, row) + (encPair encP encA (input.1, row)).length + 1
      let U := (input.2.map u).sum
      have sumEq : (∑ j ∈ Finset.range input.2.length, if hj : j < input.2.length then
          K * u input.2[j] else 0) = K * U := by
        rw [← Fin.sum_univ_eq_sum_range]
        simp only [Fin.isLt, dite_true]
        rw [← Finset.mul_sum]
        congr 1
        dsimp only [U]
        conv_rhs => rw [← List.ofFn_getElem (xs := input.2), List.map_ofFn, List.sum_ofFn]
        rfl
      change C * (2*cF+2 + I + _ + (2*I+2) + 1) ≤ D * (I + U + 1)
      rw [sumEq]
      have h : 2*cF+2 + I + K*U + (2*I+2) + 1 ≤
          (K+2*cF+10) * (I+U+1) := by nlinarith
      exact (Nat.mul_le_mul_left C h).trans (by
        rw [← Nat.mul_assoc]
        apply Nat.mul_le_mul_right
        dsimp only [D]
        nlinarith)
    · intro input
      let I := (encPair encP (encList encA) input).length
      let M := listMax (fun row => S (input.1, row)) input.2
      let O := (encList encB (input.2.flatMap (fun row => f (input.1, row)))).length
      change C * (0 + (cN * (2*I+2) + cE * (4*I+M+3)) + (2*I+2) + 1) ≤
        D * (I + M + O + 1)
      simp only [Nat.zero_add]
      have h : cN * (2*I+2) + cE * (4*I+M+3) + (2*I+2) + 1 ≤
          (2*cN+4*cE+10) * (I+M+O+1) := by nlinarith
      exact (Nat.mul_le_mul_left C h).trans (by
        rw [← Nat.mul_assoc]
        apply Nat.mul_le_mul_right
        dsimp only [D]
        nlinarith)
    · intro input
      dsimp only [streamFlatMapSpace]
      have hd : 1 ≤ D := by dsimp only [D]; omega
      exact (by omega : (encList encB (input.2.flatMap (fun row => f (input.1, row)))).length ≤
        (encPair encP (encList encA) input).length +
          listMax (fun row => S (input.1, row)) input.2 +
          (encList encB (input.2.flatMap (fun row => f (input.1, row)))).length + 1).trans
        (Nat.le_mul_of_pos_left _ hd)
  · intro input j hj
    have hr := rowBound input input.2[j] (List.getElem_mem hj)
    simp only [state_fst, dite_eq_left hj, length_encPair, encFramed_apply, length_frame]
    dsimp only [K]
    nlinarith
  · intro input j hj
    have hr := rowBound input input.2[j] (List.getElem_mem hj)
    have hs := le_listMax (f := fun row => S (input.1, row)) (List.getElem_mem hj)
    simp only [state_fst, length_encPair, encFramed_apply, length_frame] at hr ⊢
    nlinarith
  · intro input j _
    simp only [state_fst, length_encPair]
    omega
  · intro input j hj
    have hr := rowBound input input.2[j] (List.getElem_mem hj)
    simp only [encFramed_apply, length_frame, length_encPair] at hr ⊢
    omega

end Turing.MultiTapeTM
