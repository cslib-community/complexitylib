/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Reassociating structured native execution proofs

## Main results

* `WordRAM.ExecWithin.seq_assoc`: compose an already proved instruction block with the
  surrounding right-associated program, without repeating its execution proof.

Reassociation preserves the same data states and charged bound. This narrow proof-rule
module avoids extending the interface of the widely imported structured-code core.
-/

@[expose] public section

namespace Cslib.WordRAM.ExecWithin

/-- Sequential blocks may be regrouped while preserving every instruction charge. -/
theorem seq_assoc {B : Basis} {r w T : ℕ} {a b c : Code B r} {x y : Data r} :
    ExecWithin w (.seq (.seq a b) c) x y T ↔ ExecWithin w (.seq a (.seq b c)) x y T := by
  constructor
  · rintro ⟨n, hn, he⟩
    cases he with
    | seq hab hc =>
      cases hab with
      | seq ha hb => exact ⟨_, by omega, .seq ha (.seq hb hc)⟩
  · rintro ⟨n, hn, he⟩
    cases he with
    | seq ha hbc =>
      cases hbc with
      | seq hb hc => exact ⟨_, by omega, .seq (.seq ha hb) hc⟩

end Cslib.WordRAM.ExecWithin
