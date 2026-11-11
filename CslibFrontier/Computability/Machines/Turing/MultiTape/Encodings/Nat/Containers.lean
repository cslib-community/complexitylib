/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Binary natural-number pair containers

Named reducible layouts for lists of binary pairs and optional binary pairs.
They record framing and tags without choosing an encoding through a default.
-/

public section
namespace Turing.MultiTapeTM

/-- List of binary natural-number pairs. Frame the first coordinate before the unframed second
coordinate, then frame each whole pair in the list, preserving order and repetitions. -/
abbrev encNatPairList : List (ℕ × ℕ) ↪ List Bool := encList (encPair encNat encNat)

/-- Optional binary natural-number pair. `none` is the empty word; `some` is a true bit
followed by the pair, whose first coordinate is framed before its unframed second coordinate. -/
abbrev encNatPairOption : Option (ℕ × ℕ) ↪ List Bool := encOption (encPair encNat encNat)

end Turing.MultiTapeTM
