/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# The value of a De Morgan gate

A De Morgan operation has at most two arguments, so its value is a function of two bits.
`Op.value op a b` is that function, with the arguments beyond the arity of `op` ignored
(`Op.value_congr`). It agrees with the Boolean interpretation of `op`
(`Op.interpretation_eq_value`), and gives evaluators and encoders of gate lists one shared
semantics of the gates.

## Main definitions

* `Cslib.Circuits.Boolean.Op.value`: the value of a De Morgan gate on its first two arguments.

## Main results

* `Cslib.Circuits.Boolean.Op.value_congr`: the value ignores the arguments beyond the arity.
* `Cslib.Circuits.Boolean.Op.interpretation_eq_value`: the Boolean interpretation of a gate is its
  value on its first two arguments.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The value of a De Morgan operation whose first two arguments carry `a` and `b`; arguments
beyond its arity are ignored. -/
def Op.value : Op → Bool → Bool → Bool
  | .const v, _, _ => v
  | .not, a, _ => !a
  | .and, a, b => a && b
  | .or, a, b => a || b

/-- The value of a gate does not depend on the arguments beyond its arity. -/
theorem Op.value_congr (op : Op) {a a' b b' : Bool} (ha : 1 ≤ signature.Arity op → a = a')
    (hb : 2 ≤ signature.Arity op → b = b') : op.value a b = op.value a' b' := by
  cases op with
  | const v => rfl
  | not => simp only [Op.value, ha (by decide)]
  | and => simp only [Op.value, ha (by decide), hb (by decide)]
  | or => simp only [Op.value, ha (by decide), hb (by decide)]

/-- The Boolean interpretation of a gate whose `i`th argument carries `f i` is its value on
`f 0` and `f 1`. -/
theorem Op.interpretation_eq_value (op : Op) (f : ℕ → Bool) :
    (interpretation op fun i => f i) = op.value (f 0) (f 1) := by
  cases op <;> rfl

end Cslib.Circuits.Boolean
