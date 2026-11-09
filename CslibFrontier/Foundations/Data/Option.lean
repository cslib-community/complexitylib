/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Option lemmas

Lemmas about `Option` operations such as `Option.getD`.

## Main results

* `Option.getD_self_eq_iff`: `o.getD b = b ↔ ∀ b', o = some b' → b = b'`.
* `Option.getD_beq_self_eq_true_iff`: `(o.getD b == b) = true ↔ ∀ b', o = some b' → b = b'`.
-/

public section

namespace Option

/-- An optional Boolean value `o` agrees with `b` on the defined part (that is,
`b = b'` whenever `o = some b'`) if and only if `o.getD b = b` holds. -/
@[simp]
theorem getD_self_eq_iff {o : Option Bool} {b : Bool} :
    o.getD b = b ↔ ∀ b', o = some b' → b = b' := by
  cases o with
  | none => simp
  | some b' =>
    simp only [Option.getD_some, Option.some.injEq, forall_eq']
    exact eq_comm

/-- An optional Boolean value `o` agrees with `b` on the defined part (that is,
`b = b'` whenever `o = some b'`) if and only if `o.getD b == b` holds. -/
theorem getD_beq_self_eq_true_iff {o : Option Bool} {b : Bool} :
    (o.getD b == b) = true ↔ ∀ b', o = some b' → b = b' := by
  rw [beq_iff_eq, getD_self_eq_iff]

end Option

end
