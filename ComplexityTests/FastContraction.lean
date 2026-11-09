/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastAlgorithm

/-! # The fast contraction machine: checked instances

The modulus at `m = 4` edges, the root call of a small network, its guard, and the arithmetic of
the call data. -/

namespace ComplexityTests.FastContraction

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
  Cslib.Complexity.CountingSimulation

-- At `m = 4`: `t = ⌊log₂ 10⌋ = 3`, so the modulus has `2 ⬝ 27 = 54` coefficients, `1` at `0` and
-- at `27`, which gives `2 ^ 54` interpolation residues.
example : modulusExp 4 = 3 := by decide
example : (modulus 4).length = 54 := by decide
example : (modulus 4).getD 0 0 = 1 ∧ (modulus 4).getD 27 0 = 1 ∧ (modulus 4).getD 1 0 = 0 := by
  decide

-- The modulus is irreducible modulo `2`, at every size.
example (m : ℕ) : Irreducible ((Cslib.GaloisRingArith.monicOf (modulus m)).map
    (Int.castRingHom (ZMod 2))) := irreducible_modulus m

/-- One row `0` and one column `1` joined by edge `0`, with full tables. -/
def tiny : ℕ × ExplicitTensorNetwork ℕ := (1, ⟨1, [([0], [1, 2]), ([0], [3, 4])]⟩)

-- The guard holds: rows first, full tables, degree `1 ≤ degreeBound 1 = 4`.
example : fastGuard tiny = true := by decide

-- The root of `(P, r, G)` at `P = 3`: scale `1`, depth `0`, bound `2`, capped precision `3`.
example : (root (3, tiny)).1.1 = 1 ∧ (root (3, tiny)).1.2.1 = 0 ∧
    (root (3, tiny)).1.2.2.1 = 2 ∧ (root (3, tiny)).1.2.2.2.1 = 3 := by decide

-- A call this small is a leaf: `leafSize 1 = 1`, so it has no more edges than the leaf size.
example : active (root (3, tiny)) = false := by decide

-- The contraction of `tiny` is `1 ⬝ 3 + 2 ⬝ 4 = 11`, and the machine's result is `11 mod 2 ^ P`
-- whenever its root is well-formed (`fastValue_eq`).
example : tiny.2.contraction = 11 := by decide

end ComplexityTests.FastContraction
