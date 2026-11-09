/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
import CslibFrontier.Computability.GenericRAM.Native.Certificate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Streaming computed lists per record

A polynomial-time callback emits a finite encoded list per input record. The
machine holds only the parameter/record and callback buffers; the complete
materialized input/output is explicitly charged. This is used by the uniform
packed-index generator and original-operand quarter evaluation, not a copying
list fold whose accumulator grows after every emission.
-/

public section
namespace Turing.MultiTapeTM

private theorem flatMap_emission {π α β : Type} (enc : β ↪ List Bool)
    (f : π × α → List β) (p : π) (rows : List α) :
    streamEmit Prod.fst (fun q => encList enc (f q)) p rows =
      encList enc (rows.flatMap (fun row => f (p, row))) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [streamEmit, ih]
    change (f (p, row)).flatMap _ ++ _ =
      (f (p, row) ++ rows.flatMap (fun row => f (p, row))).flatMap _
    rw [List.flatMap_append]
    rfl

/-- Execute the list callback on each record and stream its encoded output. Both machine and
polynomial are independent of the runtime parameter/list. The charged space includes output. -/
theorem ComputableInO.flatMap_stream {π α β : Type} {encP : π ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : π × α → List β}
    (hf : ComputableInPolyTime f (encPair encP encA) (encList encB)) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun input : π × List α =>
        input.2.flatMap (fun row => f (input.1, row)))
        (encPair encP (encList encA)) (encList encB)
        (fun input => (encPair encP (encList encA) input).length +
          (input.2.length + 1) * P (streamFilterWidth encP encA input))
        (fun input => (encPair encP (encList encA) input).length +
          (input.2.length + 1) * P (streamFilterWidth encP encA input)) := by
  have decode : ComputableTidilyInPolyTime (id : α → α) (encFramed encA) encA :=
    .of_linear (.of_unframe (fun row => by simp))
  have argument := (ComputableTidilyInPolyTime.fst encP (encFramed encA)).prod
    (decode.comp (ComputableTidilyInPolyTime.snd encP (encFramed encA)))
  have hemit := ((ComputableTidilyInPolyTime.encode (encList encB)).comp hf.tidy).comp argument
  obtain ⟨tN, sN, htN, hsN, hN⟩ := ComputableTidilyInPolyTime.fst encP (encFramed encA)
  obtain ⟨tE, sE, htE, hsE, hE⟩ := hemit
  simp only [Function.comp_def, id_eq] at hE
  obtain ⟨c, d, bound⟩ := (((htN.add hsN).add htE).add hsE).exists_le
  obtain ⟨cF, hF⟩ := computableInTimeAndSpace_of_const
    (encIn := encP) (encOut := encBits) ([] : List Bool)
  let P : ℕ → ℕ := fun B => c * (2 * B + 1) ^ d + 5 * B + 3
  have hP : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have monoP : Monotone P := by
    intro a b hab
    have hpow := Nat.mul_le_mul_left c
      (Nat.pow_le_pow_left (by omega : 2 * a + 1 ≤ 2 * b + 1) d)
    dsimp only [P]
    omega
  have row_bound (input : π × List α) (row : α) (hrow : row ∈ input.2) :
      (encA row).length ≤ streamRecordLength encA input.2 :=
    le_listMax (f := fun a => (encA a).length) hrow
  have callback (input : π × List α) (row : α) (hrow : row ∈ input.2) :
      tN (input.1, row) + sN (input.1, row) + tE (input.1, row) + sE (input.1, row) ≤
        c * (2 * streamFilterWidth encP encA input + 1) ^ d := by
    have hb := bound (input.1, row)
    have hr := row_bound input row hrow
    have hi : (encPair encP (encFramed encA) (input.1, row)).length ≤
        2 * streamFilterWidth encP encA input := by
      simp only [length_encPair, encFramed_apply, length_frame, streamFilterWidth]
      omega
    exact hb.trans (Nat.mul_le_mul_left c
      (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) d))
  have streaming := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun input : π × List α => input.2.flatMap (fun row => f (input.1, row)))
    (encA := encFramed encA) (encIn := encPair encP (encList encA))
    (encOut := encList encB) (next := Prod.fst)
    rawFrameReader (fun row => frame (encA row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hN hE hF.computableTidilyInTimeAndSpace
    (fun input => by simp only [encBits_apply, flatMap_emission,
      Function.const_apply, List.append_nil])
    (roundCost := fun input _ => P (streamFilterWidth encP encA input))
    (sMax := fun input => P (streamFilterWidth encP encA input))
    (lMax := fun input => 2 * streamFilterWidth encP encA input + 1) ?_ ?_ ?_ ?_
  · obtain ⟨C, hC⟩ := streaming
    let plain := Cslib.GenericRAM.NativeCertificate.ofTimeAndSpace hC.computableInTimeAndSpace
    have time_bound (input : π × List α) : plain.time input ≤
        (C * (2 * cF + 7) + 1) *
          ((encPair encP (encList encA) input).length +
            (input.2.length + 1) * P (streamFilterWidth encP encA input) + 1) := by
      change C * _ ≤ _
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hp : 2 * streamFilterWidth encP encA input + 2 ≤
          P (streamFilterWidth encP encA input) := by dsimp only [P]; omega
      let X := (encPair encP (encList encA) input).length +
        (input.2.length + 1) * P (streamFilterWidth encP encA input) + 1
      let K := 2 * cF + 6
      have hinner : 2 * cF + 2 + (encPair encP (encList encA) input).length +
          input.2.length * P (streamFilterWidth encP encA input) +
          (2 * streamFilterWidth encP encA input + 1) + 1 ≤ K + X := by
        dsimp only [K, X]
        nlinarith
      have hx : 1 ≤ X := by dsimp only [X]; omega
      have hscale : K + X ≤ (K + 1) * X := by nlinarith
      calc
        _ ≤ C * (K + X) := Nat.mul_le_mul_left C hinner
        _ ≤ C * ((K + 1) * X) := Nat.mul_le_mul_left C hscale
        _ ≤ (C * (2 * cF + 7) + 1) * X := by dsimp only [K]; nlinarith
    refine ⟨P, hP, monoP, plain.computes.mono (3 * (C * (2 * cF + 7) + 1)) ?_ ?_⟩
    · intro input
      have ht := time_bound input
      nlinarith
    · intro input
      have ht := time_bound input
      have hp : 2 * streamFilterWidth encP encA input + 2 ≤
          P (streamFilterWidth encP encA input) := by dsimp only [P]; omega
      have hmul := Nat.mul_le_mul_left (C * (2 * cF + 7) + 1)
        (show P (streamFilterWidth encP encA input) ≤
          (encPair encP (encList encA) input).length +
            (input.2.length + 1) * P (streamFilterWidth encP encA input) + 1 by nlinarith)
      have hdom := Nat.mul_le_mul_right (P (streamFilterWidth encP encA input))
        (show 2 * C ≤ 2 * (C * (2 * cF + 7) + 1) by nlinarith)
      have hscale := Nat.mul_le_mul_left C hp
      change C * (0 + P (streamFilterWidth encP encA input) +
        (2 * streamFilterWidth encP encA input + 1) + 1) + plain.time input ≤ _
      nlinarith
  · intro input j hj
    have hb := callback input input.2[j] (List.getElem_mem hj)
    have hr := row_bound input input.2[j] (List.getElem_mem hj)
    simp only [streamState, List.foldl_fixed, encFramed_apply, length_frame]
    dsimp only [streamFilterWidth] at hb
    dsimp only [P, streamFilterWidth]
    omega
  · intro input j hj
    have hb := callback input input.2[j] (List.getElem_mem hj)
    simp only [streamState, List.foldl_fixed]
    dsimp only [P]
    omega
  · intro input j _
    simp only [streamState, List.foldl_fixed, streamFilterWidth]
    omega
  · intro input j hj
    have hr := row_bound input input.2[j] (List.getElem_mem hj)
    simp only [encFramed_apply, length_frame, streamFilterWidth]
    omega

end Turing.MultiTapeTM
