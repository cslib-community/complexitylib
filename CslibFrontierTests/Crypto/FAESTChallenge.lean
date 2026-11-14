/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.FAEST.Challenge

/-!
# FAEST v3 challenge-decomposition clients

These clients instantiate the zero-remainder, mixed-width, FAEST-EM-192s, and largest
repetition-count boundaries in FAEST v3 Table 3.2.  They also check the exact prefix/suffix
boundary, invalid-index rejection, and little-endian decoding across two consecutive blocks.
-/

public section

namespace CslibFrontierTests.Crypto.FAESTChallenge

open Cslib Cslib.Crypto.FAEST
open ChallengeParams

/-- FAEST-128s parameters from FAEST v3 Table 3.2. -/
abbrev faest128s : ChallengeParams where
  securityBits := 128
  repetitions := 11
  grindingBits := 7
  grindingBits_le := by decide
  repetitions_pos := by decide
  repetitions_le := by decide

/-- FAEST-128f parameters from FAEST v3 Table 3.2. -/
abbrev faest128f : ChallengeParams where
  securityBits := 128
  repetitions := 17
  grindingBits := 8
  grindingBits_le := by decide
  repetitions_pos := by decide
  repetitions_le := by decide

/-- FAEST-EM-192s parameters from FAEST v3 Table 3.2. -/
abbrev faestEM192s : ChallengeParams where
  securityBits := 192
  repetitions := 16
  grindingBits := 8
  grindingBits_le := by decide
  repetitions_pos := by decide
  repetitions_le := by decide

/-- FAEST-256f parameters from FAEST v3 Table 3.2. -/
abbrev faest256f : ChallengeParams where
  securityBits := 256
  repetitions := 33
  grindingBits := 8
  grindingBits_le := by decide
  repetitions_pos := by decide
  repetitions_le := by decide

-- FAEST-128s has `tau_1 = 0`, so all eleven blocks have the smaller width.
example : faest128s.nonGrindingBits = 121 := by decide
example : faest128s.largeCount = 0 := by decide
example : faest128s.largeWidth = 12 := by decide
example : faest128s.blockWidth 0 = 11 := by decide
example : faest128s.blockWidth 10 = 11 := by decide
example : faest128s.blockOffset 11 = 121 := by decide

-- FAEST-128f has one eight-bit block followed by sixteen seven-bit blocks.
example : faest128f.nonGrindingBits = 120 := by decide
example : faest128f.largeCount = 1 := by decide
example : faest128f.blockWidth 0 = 8 := by decide
example : faest128f.blockOffset 1 = 8 := by decide
example : faest128f.blockWidth 1 = 7 := by decide
example : faest128f.blockOffset 17 = 120 := by decide

-- The FAEST-EM-192s row uses eight grinding bits and has eight blocks of each width.
example : faestEM192s.nonGrindingBits = 184 := by decide
example : faestEM192s.largeCount = 8 := by decide
example : faestEM192s.blockWidth 7 = 12 := by decide
example : faestEM192s.blockWidth 8 = 11 := by decide
example : faestEM192s.blockOffset 16 = 184 := by decide

-- FAEST-256f is the Table 3.2 row with the largest repetition count.
example : faest256f.largeCount = 17 := by decide
example : faest256f.blockWidth 16 = 8 := by decide
example : faest256f.blockWidth 17 = 7 := by decide
example : faest256f.blockOffset 33 = 248 := by decide

/-- A single true bit at the final non-grinding position. -/
def lastPrefixBit : BitString 128 := fun i => decide (i.val = 119)

/-- A single true bit at the first grinding position. -/
def firstSuffixBit : BitString 128 := fun i => decide (i.val = 120)

example : grindingAccepted faest128f lastPrefixBit = true := by decide
example : grindingAccepted faest128f firstSuffixBit = false := by decide
example : decodeChallengeBlock faest128f firstSuffixBit 0 = none := by decide
example : decodeChallengeBlock faest128f (fun _ => false) 17 = none := by decide

/-- Bits 7 and 8 straddle the FAEST-128f boundary between blocks zero and one. -/
def boundaryBits : BitString 128 := fun i => decide (i.val = 7 ∨ i.val = 8)

example :
    (decodeChallengeBlock faest128f boundaryBits 0).map (BitString.equivFin 8) =
      some ⟨128, by decide⟩ := by
  decide

example :
    (decodeChallengeBlock faest128f boundaryBits 1).map (BitString.equivFin 7) =
      some ⟨1, by decide⟩ := by
  decide

example :
    (decodeAllChallenge faest128f boundaryBits).map (fun decoded =>
      ((decoded ⟨0, by decide⟩).val, (decoded ⟨1, by decide⟩).val)) = some (128, 1) := by
  decide

end CslibFrontierTests.Crypto.FAESTChallenge
