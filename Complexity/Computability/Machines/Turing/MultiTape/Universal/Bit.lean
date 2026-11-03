/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `eBit` sits in `Universal/Compose.lean` on that branch; it is kept apart here so that
-- `Universal` does not depend on composition, which moved out of it (#2179)

public import Complexity.Init
public import Mathlib.Logic.Embedding.Basic

/-!
# Bits as symbols

Machines over bits are described for the universal machine, whose symbols are natural numbers,
through `Turing.MultiTapeTM.Universal.eBit`.

## Main definitions

* `Turing.MultiTapeTM.Universal.eBit`: bits as symbols.
-/

namespace Turing.MultiTapeTM.Universal

/-- Bits as symbols. -/
@[expose] public def eBit : Bool ↪ ℕ :=
  ⟨Bool.toNat, fun a b h => by cases a <;> cases b <;> simp_all⟩

end Turing.MultiTapeTM.Universal
