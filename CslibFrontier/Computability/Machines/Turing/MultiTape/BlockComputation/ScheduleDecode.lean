/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleBits

/-!
# Decoding aligned two-bit movements

`decodePairs` rejects incomplete or invalid aligned pairs and inverts `RelativeScan.encode`.
This is an executable semantic decoder; no machine cost is asserted here.
-/

public section

namespace Turing.MultiTapeTM.ScheduleBits

/-- Decode a complete sequence of aligned movement pairs, rejecting `11` and a trailing bit. -/
@[expose] def decodePairs : List Bool → Option (List SignType)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let s ← decodePair a b
    let ss ← decodePairs rest
    return s :: ss

/-- Canonical two-bit encoding followed by decoding returns the original movements. -/
@[simp] theorem decodePairs_encode (ss : List SignType) :
    decodePairs (RelativeScan.encode ss) = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [RelativeScan.encode, decodePairs, ih]

/-- Successfully decoded words are precisely the canonical encoding of their decoded value. -/
theorem decodePairs_eq_some_iff : ∀ (word : List Bool) (ss : List SignType),
    decodePairs word = some ss ↔ RelativeScan.encode ss = word
  | [], ss => by cases ss <;> simp [decodePairs, RelativeScan.encode]
  | [a], ss => by
    cases ss <;> simp [decodePairs, RelativeScan.encode]
  | a :: b :: rest, ss => by
    cases a <;> cases b <;> cases ss with
    | nil => simp [decodePairs, decodePair, RelativeScan.encode, Option.bind_eq_some_iff]
    | cons s ss =>
      cases s <;> simp [decodePairs, decodePair, RelativeScan.encode, RelativeScan.negative,
        RelativeScan.positive, Option.bind_eq_some_iff, decodePairs_eq_some_iff rest]

end Turing.MultiTapeTM.ScheduleBits
