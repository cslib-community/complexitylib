/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Init

/-!
# FAEST challenge decomposition

FAEST v3 splits the first `lambda - grindingBits` bits of its third Fiat--Shamir challenge among
`repetitions` small-VOLE instances.  The first `largeCount` instances receive `largeWidth` bits
and the remaining instances receive `largeWidth - 1` bits.  The final `grindingBits` challenge
bits must all be zero [BaumEtAl2026FAEST, Section 5.5, Figure 5.7].  The derived
parameter names follow Table 5.1; the standard parameter clients use Table 3.2 of version 3.0
dated 1 September 2026.

This module formalizes the parameter arithmetic and the `DecodeChall3` / `DecodeAllChall3`
procedures.  Challenge bits and each returned integer use the source's little-endian `NumRec`
convention from Section 3.2, Figure 3.5.  It is the challenge parser consumed by the later BAVC
and VOLE reconstruction algorithms; it does not construct those commitments or prove FAEST
security.

## Main definitions

* `Cslib.Crypto.FAEST.ChallengeParams`: valid challenge-splitting parameters.
* `Cslib.Crypto.FAEST.decodeChallengeBlock`: source `DecodeChall3`, including invalid-index and
  grinding-suffix rejection.
* `Cslib.Crypto.FAEST.decodeAllChallenge`: source `DecodeAllChall3`, returning each hidden index
  in its exact range.

## Main results

* `Cslib.Crypto.FAEST.ChallengeParams.blockOffset_succ`: consecutive instances receive
  consecutive slices.
* `Cslib.Crypto.FAEST.ChallengeParams.blockOffset_repetitions`: the slices end exactly after the
  non-grinding challenge prefix.
* `Cslib.Crypto.FAEST.decodeChallengeBlock_eq_some`: the exact accepted block.
* `Cslib.Crypto.FAEST.decodeAllChallenge_eq_some`: the exact vector of decoded hidden indices.

## References

* [C. Baum et al., *FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST]
-/

public section

namespace Cslib.Crypto.FAEST

/-- Parameters needed by FAEST v3 Figure 5.7.  The source parameter sets have a positive number
of small-VOLE instances and at least one non-grinding challenge bit per instance. -/
structure ChallengeParams where
  /-- Computational security parameter `lambda`. -/
  securityBits : Nat
  /-- Number `tau` of small-VOLE instances. -/
  repetitions : Nat
  /-- Grinding parameter `w_grind`. -/
  grindingBits : Nat
  grindingBits_le : grindingBits <= securityBits
  repetitions_pos : 0 < repetitions
  repetitions_le : repetitions <= securityBits - grindingBits

namespace ChallengeParams

/-- Number `n_Delta = lambda - w_grind` of challenge bits assigned to small-VOLE instances. -/
@[expose] def nonGrindingBits (p : ChallengeParams) : Nat := p.securityBits - p.grindingBits

/-- Number `tau_1 = n_Delta mod tau` of larger small-VOLE instances. -/
@[expose] def largeCount (p : ChallengeParams) : Nat := p.nonGrindingBits % p.repetitions

/-- Number `tau_0 = tau - tau_1` of smaller small-VOLE instances. -/
@[expose] def smallCount (p : ChallengeParams) : Nat := p.repetitions - p.largeCount

/-- Bit length `k = floor(n_Delta / tau) + 1` of a larger small-VOLE instance. -/
@[expose] def largeWidth (p : ChallengeParams) : Nat := p.nonGrindingBits / p.repetitions + 1

/-- Source width `d_i`: `k` for the first `tau_1` instances and `k - 1` thereafter. -/
@[expose] def blockWidth (p : ChallengeParams) (i : Nat) : Nat :=
  if (i < p.largeCount : Prop) then p.largeWidth else p.largeWidth - 1

/-- Starting offset of source block `i` in the non-grinding challenge prefix. -/
@[expose] def blockOffset (p : ChallengeParams) (i : Nat) : Nat :=
  if (i < p.largeCount : Prop) then i * p.largeWidth
  else p.largeCount * p.largeWidth + (i - p.largeCount) * (p.largeWidth - 1)

theorem largeCount_lt (p : ChallengeParams) : p.largeCount < p.repetitions :=
  Nat.mod_lt _ p.repetitions_pos

theorem largeCount_le (p : ChallengeParams) : p.largeCount <= p.repetitions :=
  (p.largeCount_lt).le

theorem smallCount_add_largeCount (p : ChallengeParams) :
    p.smallCount + p.largeCount = p.repetitions := by
  exact Nat.sub_add_cancel p.largeCount_le

theorem largeWidth_pos (p : ChallengeParams) : 0 < p.largeWidth := by
  exact Nat.zero_lt_succ _

theorem blockWidth_pos (p : ChallengeParams) {i : Nat} (_hi : i < p.repetitions) :
    0 < p.blockWidth i := by
  have hq : 0 < p.nonGrindingBits / p.repetitions :=
    Nat.div_pos p.repetitions_le p.repetitions_pos
  simp only [blockWidth, largeWidth]
  split <;> omega

theorem blockOffset_zero (p : ChallengeParams) : p.blockOffset 0 = 0 := by
  simp only [blockOffset]
  split <;> simp_all

/-- The source blocks are consecutive: the next block starts exactly after the current block. -/
theorem blockOffset_succ (p : ChallengeParams) {i : Nat} :
    p.blockOffset (i + 1) = p.blockOffset i + p.blockWidth i := by
  by_cases hir : i < p.largeCount
  · by_cases hnext : i + 1 < p.largeCount
    · simp only [blockOffset, blockWidth, hir, hnext, ↓reduceIte]
      rw [Nat.add_mul]
      simp
    · have heq : i + 1 = p.largeCount := by omega
      simp only [blockOffset, blockWidth, hir, hnext, ↓reduceIte]
      rw [heq]
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      rw [← heq, Nat.add_mul]
      simp
  · have hnext : ¬(i + 1 < p.largeCount) := by omega
    have hsub : i + 1 - p.largeCount = (i - p.largeCount) + 1 := by omega
    simp only [blockOffset, blockWidth, hir, hnext, ↓reduceIte, hsub, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc]

/-- The consecutive block slices end exactly at `n_Delta = lambda - w_grind`. -/
theorem blockOffset_repetitions (p : ChallengeParams) :
    p.blockOffset p.repetitions = p.nonGrindingBits := by
  have hnot : ¬(p.repetitions < p.largeCount) := Nat.not_lt.mpr p.largeCount_le
  simp only [blockOffset, hnot, ↓reduceIte, largeWidth, Nat.add_sub_cancel]
  have hcount := p.largeCount_le
  rw [Nat.mul_add, Nat.mul_one, Nat.sub_mul]
  have hmul : p.largeCount * (p.nonGrindingBits / p.repetitions) <=
      p.repetitions * (p.nonGrindingBits / p.repetitions) :=
    Nat.mul_le_mul_right (p.nonGrindingBits / p.repetitions) hcount
  calc
    p.largeCount * (p.nonGrindingBits / p.repetitions) + p.largeCount +
          (p.repetitions * (p.nonGrindingBits / p.repetitions) -
            p.largeCount * (p.nonGrindingBits / p.repetitions)) =
        p.largeCount +
          (p.largeCount * (p.nonGrindingBits / p.repetitions) +
            (p.repetitions * (p.nonGrindingBits / p.repetitions) -
              p.largeCount * (p.nonGrindingBits / p.repetitions))) := by ac_rfl
    _ = p.largeCount + p.repetitions * (p.nonGrindingBits / p.repetitions) := by
      rw [Nat.add_sub_of_le hmul]
    _ = p.nonGrindingBits := by
      simpa only [largeCount] using Nat.mod_add_div p.nonGrindingBits p.repetitions

/-- Every valid source block lies in the non-grinding challenge prefix. -/
theorem blockOffset_add_width_le (p : ChallengeParams) {i : Nat} (hi : i < p.repetitions) :
    p.blockOffset i + p.blockWidth i <= p.nonGrindingBits := by
  rw [← p.blockOffset_succ]
  have hmono : Monotone p.blockOffset := monotone_nat_of_le_succ fun j => by
    rw [p.blockOffset_succ]
    exact Nat.le_add_right _ _
  calc
    p.blockOffset (i + 1) <= p.blockOffset p.repetitions := hmono (by omega)
    _ = p.nonGrindingBits := p.blockOffset_repetitions

end ChallengeParams

open ChallengeParams

/-- The final `w_grind` bits are all zero, as required by FAEST v3 Figure 5.7. -/
@[expose] def grindingAccepted (p : ChallengeParams)
    (challenge : BitString p.securityBits) : Bool :=
  decide <| ∀ j : Fin p.grindingBits,
    challenge ⟨p.nonGrindingBits + j, by
      have hj := j.isLt
      have hgrind := p.grindingBits_le
      simp only [ChallengeParams.nonGrindingBits]
      omega⟩ = false

/-- The exact fixed-width challenge block assigned to a typed small-VOLE instance. -/
@[expose] def challengeBlock (p : ChallengeParams) (challenge : BitString p.securityBits)
    (i : Fin p.repetitions) : BitString (p.blockWidth i) :=
  fun j => challenge <| Fin.mk (p.blockOffset i + j) <| by
    have hprefix := p.blockOffset_add_width_le i.isLt
    have hng : p.nonGrindingBits <= p.securityBits := Nat.sub_le _ _
    omega

/-- `DecodeChall3` from FAEST v3 Figure 5.7.  A natural-number index is retained so that the
source's invalid-index rejection is represented explicitly. -/
@[expose] def decodeChallengeBlock (p : ChallengeParams)
    (challenge : BitString p.securityBits) (i : Nat) :
    Option (BitString (p.blockWidth i)) :=
  if hi : i < p.repetitions then
    if grindingAccepted p challenge = true then
      some (challengeBlock p challenge <| Fin.mk i hi)
    else none
  else none

/-- `DecodeAllChall3` from FAEST v3 Figure 5.7.  Each result is typed below `2 ^ d_i`, making the
hidden-leaf range required by the BAVC explicit. -/
@[expose] def decodeAllChallenge (p : ChallengeParams) (challenge : BitString p.securityBits) :
    Option (forall i : Fin p.repetitions, Fin (2 ^ p.blockWidth i)) :=
  if grindingAccepted p challenge = true then
    some fun i => BitString.equivFin (p.blockWidth i) (challengeBlock p challenge i)
  else none

@[simp] theorem challengeBlock_apply (p : ChallengeParams)
    (challenge : BitString p.securityBits) (i : Fin p.repetitions) (j : Fin (p.blockWidth i)) :
    challengeBlock p challenge i j = challenge (Fin.mk (p.blockOffset i + j) (by
      have hprefix := p.blockOffset_add_width_le i.isLt
      have hng : p.nonGrindingBits <= p.securityBits := Nat.sub_le _ _
      omega)) := by
  simp only [challengeBlock]

theorem length_challengeBlock (p : ChallengeParams) (challenge : BitString p.securityBits)
    (i : Fin p.repetitions) : (List.ofFn (challengeBlock p challenge i)).length = p.blockWidth i :=
  List.length_ofFn

theorem grindingAccepted_eq_true_iff (p : ChallengeParams)
    (challenge : BitString p.securityBits) :
    grindingAccepted p challenge = true ↔
      ∀ j : Fin p.grindingBits,
        challenge ⟨p.nonGrindingBits + j, by
          have hj := j.isLt
          have hgrind := p.grindingBits_le
          simp only [ChallengeParams.nonGrindingBits]
          omega⟩ = false := by
  simp only [grindingAccepted, decide_eq_true_eq]

theorem decodeChallengeBlock_eq_some (p : ChallengeParams)
    (challenge : BitString p.securityBits) {i : Nat} (hi : i < p.repetitions)
    (hgrind : grindingAccepted p challenge = true) :
    decodeChallengeBlock p challenge i =
      some (challengeBlock p challenge <| Fin.mk i hi) := by
  simp only [decodeChallengeBlock, hi, hgrind, ↓reduceDIte, ↓reduceIte]

theorem decodeChallengeBlock_eq_none_of_index (p : ChallengeParams)
    (challenge : BitString p.securityBits) {i : Nat} (hi : p.repetitions <= i) :
    decodeChallengeBlock p challenge i = none := by
  simp only [decodeChallengeBlock, Nat.not_lt.mpr hi, ↓reduceDIte]

theorem decodeChallengeBlock_eq_none_of_grinding (p : ChallengeParams)
    (challenge : BitString p.securityBits) (i : Nat)
    (hgrind : grindingAccepted p challenge = false) :
    decodeChallengeBlock p challenge i = none := by
  simp only [decodeChallengeBlock, hgrind]
  split <;> simp

theorem decodeAllChallenge_eq_some (p : ChallengeParams)
    (challenge : BitString p.securityBits) (hgrind : grindingAccepted p challenge = true) :
    decodeAllChallenge p challenge =
      some fun (i : Fin p.repetitions) =>
        BitString.equivFin (p.blockWidth i) (challengeBlock p challenge i) := by
  simp only [decodeAllChallenge, hgrind, ↓reduceIte]

theorem decodeAllChallenge_eq_none (p : ChallengeParams)
    (challenge : BitString p.securityBits) (hgrind : grindingAccepted p challenge = false) :
    decodeAllChallenge p challenge = none := by
  simp [decodeAllChallenge, hgrind]

theorem decodeAllChallenge_isSome_iff (p : ChallengeParams)
    (challenge : BitString p.securityBits) :
    (decodeAllChallenge p challenge).isSome = grindingAccepted p challenge := by
  cases hgrind : grindingAccepted p challenge <;> simp [decodeAllChallenge, hgrind]

end Cslib.Crypto.FAEST
