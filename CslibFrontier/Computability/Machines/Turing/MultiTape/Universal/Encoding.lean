/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Encodings shared by universal multi-tape machines

This module contains the low-level encodings of deterministic universal-machine symbols,
transition keys and actions. It is intentionally independent of the universal interpreter's
complexity proofs so other finite machine descriptions can reuse the same encoded words and
generated projection certificates.

## Main definitions

* `Turing.MultiTapeTM.Universal.eSym`: optional natural-number symbols in unary.
* `Turing.MultiTapeTM.Universal.eKey`: deterministic transition keys as framed fields.
* `Turing.MultiTapeTM.Universal.eAct`: deterministic actions as framed fields.

## Main results

The `enc_structure` declarations generate the scoped projection and constructor certificates used
by the universal interpreter's complexity proofs.

## References

These encodings are extracted unchanged from the deterministic universal-machine development.
-/

namespace Turing.MultiTapeTM.Universal

/-- Symbols and blanks. -/
public abbrev eSym : Option ℕ ↪ List Bool := encOption encUnary

/-- Keys of transitions, as their fields. -/
enc_structure eKey : Key where state : encUnary, input : eSym, work : (encList eSym)

/-- An action on a work tape. -/
public abbrev TapeAct := Option (Option ℕ) × SignType

/-- Actions on a work tape. -/
public abbrev eTA : Option (Option ℕ) × SignType ↪ List Bool := encPair (encOption eSym) encSign

/-- Actions, as their fields. -/
enc_structure eAct : Act where
  inputTape : encSign, workTapes : (encList eTA), output : eSym, state : eSym

end Turing.MultiTapeTM.Universal
