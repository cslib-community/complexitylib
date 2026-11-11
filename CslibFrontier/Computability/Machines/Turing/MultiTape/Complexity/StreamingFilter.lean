/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Stable filtering by streaming framed records

One machine streams the framed input records, retains the parameter and one
record, and emits accepted frames directly. It never copies a growing output
accumulator. For a polynomial-time per-record test the total time is linear in
the record count times a polynomial in parameter/maximum-record size; workspace
uses a peak per-record bound and charges the whole encoded output separately.

This is a real streaming construction, using `streamFold_pair_sum`, not a
complexity claim for the ordinary copying `filterWith` implementation. It is a
building block for bounded-width radix sorting and sparse zero deletion.
-/

public section
namespace Turing.MultiTapeTM

/-- Largest actual record wire, zero for an empty list. -/
@[expose] def streamRecordLength {α : Type} (enc : α ↪ List Bool) (rows : List α) : ℕ :=
  listMax (fun row => (enc row).length) rows

/-- Parameter and maximum record size, with one unit for empty inputs/control. -/
@[expose] def streamFilterWidth {π α : Type} (encP : π ↪ List Bool) (encA : α ↪ List Bool)
    (input : π × List α) : ℕ :=
  let (parameter, rows) := input
  (encP parameter).length + streamRecordLength encA rows + 1

private theorem state_fst {π α : Type} (p : π) (rows : List α) (j : ℕ) :
    streamState p (Prod.fst : π × α → π) rows j = p := by
  simp [streamState]

private theorem filter_emission {π α : Type} (enc : α ↪ List Bool)
    (test : π × α → Bool) (p : π) (rows : List α) :
    streamEmit Prod.fst (fun q => if test q then frame (enc q.2) else []) p rows =
      encList enc (rows.filter (fun row => test (p, row))) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [streamEmit]
    by_cases h : test (p, row) = true <;> simp [h, ih, encList_cons]

/-- Streaming stable filtering with a polynomial per-record budget. The polynomial and machine
are chosen before the runtime parameter/list. No list traversal or resource bound is a premise;
the only component premise certifies the actual per-record predicate. -/
theorem ComputableInO.filter_stream {π α : Type} {encP : π ↪ List Bool}
    {encA : α ↪ List Bool} {test : π × α → Bool}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun input : π × List α =>
        input.2.filter (fun row => test (input.1, row)))
        (encPair encP (encList encA)) (encList encA)
        (fun input => (encPair encP (encList encA) input).length +
          (input.2.length + 1) * P (streamFilterWidth encP encA input))
        (fun input => (encPair encP (encList encA) input).length +
          P (streamFilterWidth encP encA input)) := by
  have decode : ComputableTidilyInPolyTime (id : α → α) (encFramed encA) encA :=
    .of_linear (.of_unframe (fun row => by simp))
  have argument := (ComputableTidilyInPolyTime.fst encP (encFramed encA)).prod
    (decode.comp (ComputableTidilyInPolyTime.snd encP (encFramed encA)))
  have hpred := htest.tidy.comp argument
  have hemit : ComputableTidilyInPolyTime
      (fun q : π × α => if test q then frame (encA q.2) else [])
      (encPair encP (encFramed encA)) encBits := by
    have hrow := (ComputableTidilyInPolyTime.encode (encFramed encA)).comp
      (ComputableTidilyInPolyTime.snd encP (encFramed encA))
    exact hpred.cond hrow (.const [])
  obtain ⟨tN, sN, htN, hsN, hN⟩ := ComputableTidilyInPolyTime.fst encP (encFramed encA)
  obtain ⟨tE, sE, htE, hsE, hE⟩ := hemit
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
    (g := fun input : π × List α => input.2.filter (fun row => test (input.1, row)))
    (encA := encFramed encA) (encIn := encPair encP (encList encA))
    (encOut := encList encA) (next := Prod.fst)
    rawFrameReader (fun row => frame (encA row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hN hE hF.computableTidilyInTimeAndSpace
    (fun input => by simp only [encBits_apply, filter_emission,
      Function.const_apply, List.append_nil])
    (roundCost := fun input _ => P (streamFilterWidth encP encA input))
    (sMax := fun input => P (streamFilterWidth encP encA input))
    (lMax := fun input => 2 * streamFilterWidth encP encA input + 1) ?_ ?_ ?_ ?_
  · obtain ⟨C, hC⟩ := streaming
    refine ⟨P, hP, monoP, ComputableInO.of_bounds hC.computableInTimeAndSpace
      (C * (2 * cF + 7) + 1) ?_ ?_ ?_⟩
    · intro input
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
      have hk : 1 ≤ K := by dsimp only [K]; omega
      have hx : 1 ≤ X := by dsimp only [X]; omega
      have hscale : K + X ≤ (K + 1) * X := by nlinarith
      calc
        _ ≤ C * (K + X) := Nat.mul_le_mul_left C hinner
        _ ≤ C * ((K + 1) * X) := Nat.mul_le_mul_left C hscale
        _ ≤ (C * (2 * cF + 7) + 1) * X := by dsimp only [K]; nlinarith
    · intro input
      have hp : 2 * streamFilterWidth encP encA input + 2 ≤
          P (streamFilterWidth encP encA input) := by dsimp only [P]; omega
      have hinner : 0 + P (streamFilterWidth encP encA input) +
          (2 * streamFilterWidth encP encA input + 1) + 1 ≤
          2 * ((encPair encP (encList encA) input).length +
            P (streamFilterWidth encP encA input) + 1) := by omega
      exact (Nat.mul_le_mul_left C hinner).trans (by
        have hk : 2 * C ≤ C * (2 * cF + 7) + 1 := by nlinarith
        simpa only [← Nat.mul_assoc, Nat.mul_comm C 2] using Nat.mul_le_mul_right
          ((encPair encP (encList encA) input).length +
            P (streamFilterWidth encP encA input) + 1) hk)
    · intro input
      have hl := ComputableTidilyInDegree.length_encList_filter_le encA
        (fun row => test (input.1, row)) input.2
      have hi : (encList encA input.2).length ≤
          (encPair encP (encList encA) input).length := by
        simp only [length_encPair]
        omega
      have hk : 1 ≤ C * (2 * cF + 7) + 1 := by omega
      have hscaled := Nat.mul_le_mul_right
        ((encPair encP (encList encA) input).length +
          P (streamFilterWidth encP encA input) + 1) hk
      simp only [Nat.one_mul] at hscaled
      apply (hl.trans hi).trans
      exact (show (encPair encP (encList encA) input).length ≤
        (encPair encP (encList encA) input).length +
          P (streamFilterWidth encP encA input) + 1 by omega).trans hscaled
  · intro input j hj
    have hb := callback input input.2[j] (List.getElem_mem hj)
    have hr := row_bound input input.2[j] (List.getElem_mem hj)
    simp only [state_fst, encFramed_apply, length_frame]
    dsimp only [streamFilterWidth] at hb
    dsimp only [P, streamFilterWidth]
    omega
  · intro input j hj
    have hb := callback input input.2[j] (List.getElem_mem hj)
    simp only [state_fst]
    dsimp only [P]
    omega
  · intro input j _
    simp only [state_fst, streamFilterWidth]
    omega
  · intro input j hj
    have hr := row_bound input input.2[j] (List.getElem_mem hj)
    simp only [encFramed_apply, length_frame, streamFilterWidth]
    omega

end Turing.MultiTapeTM
