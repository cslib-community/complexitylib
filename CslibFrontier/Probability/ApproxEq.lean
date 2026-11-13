/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Basic.Real.Basic

/-!
# Closeness of real numbers up to an error

`x ≈[ε] y` says that the real numbers `x` and `y` differ by at most `ε`: `|x - y| ≤ ε`. It is the
relation of a game-hopping argument [BonehShoup2023]: each hop changes the
probability of an event by at most its loss, and the losses add along a chain. The relation has a
`Trans` instance that adds the errors, and `Eq` steps compose with it, so a sequence of games reads
as a `calc` block:
```
calc Pr[G₀] = Pr[G₁] := by rw [h₀₁]
  _ ≈[ε₁] Pr[G₂] := h₁₂
  _ ≈[ε₂] Pr[G₃] := h₂₃
```
which proves `Pr[G₀] ≈[ε₁ + ε₂] Pr[G₃]`. The definition is exposed, so a proof of `|x - y| ≤ ε`
is a proof of `x ≈[ε] y`.

The notation is scoped: `open Cslib.Probability` enables it, as does `open Probability` inside the
namespace `Cslib`.

## Main definitions

* `Cslib.Probability.ApproxEq`: `x ≈[ε] y`, the real numbers `x` and `y` differ by at most `ε`.

## Main results

* `Cslib.Probability.ApproxEq.trans`: errors add along a chain; the `Trans` instance used by `calc`.
* `Cslib.Probability.ApproxEq.symm`, `Cslib.Probability.ApproxEq.mono`: symmetry, and enlarging
  the error.
* `Cslib.Probability.ApproxEq.le_add`, `Cslib.Probability.ApproxEq.sub_le`: the one-sided bounds.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Probability

/-- `x ≈[ε] y`: the real numbers `x` and `y` differ by at most `ε`, that is, `|x - y| ≤ ε`. -/
def ApproxEq (ε x y : ℝ) : Prop := |x - y| ≤ ε

@[inherit_doc] scoped notation:50 x:51 " ≈[" ε "] " y:51 => ApproxEq ε x y

namespace ApproxEq

variable {ε δ x y z : ℝ}

/-- A real number is `0`-close to itself. -/
theorem refl (x : ℝ) : x ≈[0] x := by
  rw [ApproxEq, sub_self, abs_zero]

/-- Closeness is symmetric. -/
theorem symm (h : x ≈[ε] y) : y ≈[ε] x := by
  rwa [ApproxEq, abs_sub_comm]

/-- **Game hopping**: errors add along a chain. -/
theorem trans (h₁ : x ≈[ε] y) (h₂ : y ≈[δ] z) : x ≈[ε + δ] z :=
  (abs_sub_le x y z).trans (add_le_add h₁ h₂)

instance : @Trans ℝ ℝ ℝ (ApproxEq ε) (ApproxEq δ) (ApproxEq (ε + δ)) := ⟨trans⟩

/-- Enlarging the error preserves closeness. -/
theorem mono (h : x ≈[ε] y) (hle : ε ≤ δ) : x ≈[δ] y :=
  le_trans (show |x - y| ≤ ε from h) hle

/-- The upper one-sided bound: `x ≤ y + ε`. -/
theorem le_add (h : x ≈[ε] y) : x ≤ y + ε :=
  sub_le_iff_le_add'.mp ((le_abs_self (x - y)).trans h)

/-- The lower one-sided bound: `y - ε ≤ x`. -/
theorem sub_le (h : x ≈[ε] y) : y - ε ≤ x :=
  sub_le_comm.mp ((le_abs_self (y - x)).trans h.symm)

end ApproxEq

end Cslib.Probability
