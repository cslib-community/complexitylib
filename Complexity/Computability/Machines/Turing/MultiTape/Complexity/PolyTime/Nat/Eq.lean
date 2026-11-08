/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Tactic.PolyTime.Init

/-!
# Equality of unary naturals in polynomial time

`Turing.MultiTapeTM.ComputableInPolyTime.decide_eq'` compares two computed values through a
common encoding inferred from its operands. For natural numbers that encoding is ambiguous
(`encUnary` or `encNat`), so proof search cannot certify guards such as
`if word.length = n then … else …`, where both sides are unary. This module fixes the unary
encoding, so that `fun_prop` and `polytime` certify such guards with plain rules, together with
`Turing.MultiTapeTM.ComputableInPolyTime.ite_decide`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_eq'`: compare computed unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_beq'`: Boolean equality of computed unary
  naturals.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Compare computed unary naturals for equality, with both operand encodings fixed. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem unary_eq' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a = right a)) input encBool :=
  decide_eq' hleft hright

/-- Compare computed unary naturals with Boolean equality, with both operand encodings fixed. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem unary_beq' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a == right a) input encBool :=
  (unary_eq' hleft hright).of_enc_eq fun a => by
    cases h : (left a == right a) <;> simp_all

end Turing.MultiTapeTM.ComputableInPolyTime
