/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.BravermanAbstract
import Complexity.Computability.Circuit.Pi
import ComplexityTests.BravermanFooling
import Complexity.Probability.PMF.Expect

/-! # Concrete clients and non-vacuity checks for the Braverman abstract

Verifies that the circuit semantics of `BravermanAbstract` is the library's, that its
`k`-wise independence is the library's (`Cslib.BitString.IsKWiseIndependent`), and that the
headline applies to a distribution that is not uniform: the uniform distribution on the strings of
`K + 1` bits with even parity is `K`-wise but not `(K + 1)`-wise independent, and for every `K` at
least the headline's independence at `q = 2` and depth `1`, the headline bounds the probability
that `AND` of its first three bits is true. The even-parity distribution and the circuit are shared
with `ComplexityTests.BravermanFooling`.
-/

namespace ComplexityTests.Abstracts.BravermanTests

open ComplexityAbstracts.BravermanAbstract ComplexityTests.BravermanFooling
open Finset Cslib Cslib.BitString Cslib.Probability Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

example : meaning = Unbounded.interpretation :=
  rfl

example {n k : ℕ} (X : PMF (Fin n → Bool)) : KWiseIndependent k X ↔ IsKWiseIndependent k X :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.symm

-- The uniform distribution is `k`-wise independent for every `k`.
example {n : ℕ} (k : ℕ) : KWiseIndependent k (PMF.uniformOfFintype (Fin n → Bool)) :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.1
    (isKWiseIndependent_uniformOfFintype k)

/-- The even-parity distribution on `K + 1` bits is `K`-wise independent: any `K` of its bits are
uniform. -/
theorem kWiseIndependent_evenParity (K : ℕ) : KWiseIndependent K (evenParity (K + 1)) :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.1
    (isKWiseIndependent_evenParity K)

-- It is not `(K + 1)`-wise independent: every sample has even parity.
example (K : ℕ) : ¬KWiseIndependent (K + 1) (evenParity (K + 1)) := fun h =>
  not_isKWiseIndependent_evenParity K
    (ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.2 h)

-- The headline applies to `AND` of the first three of `K + 1` bits, with `q = 2` and depth `1`,
-- under the even-parity distribution for every
-- `K ≥ 128 ^ 41 = (64 · 2) ^ ((2 · 1 + 3) (1 + 7) + 1)`.
example (K : ℕ) (hK : 128 ^ 41 ≤ K) :
    |probabilityTrue (evenParity (K + 1))
        (and3 (Nat.succ_le_succ ((by norm_num : 2 ≤ 128 ^ 41).trans hK))) -
      fractionTrue (and3 (Nat.succ_le_succ ((by norm_num : 2 ≤ 128 ^ 41).trans hK)))| ≤
      1 / 2 ^ 2 :=
  braverman (d := 1) (q := 2) (by norm_num) _ (and3_fanInAtMost _)
    (by rw [Circuit.size_oneGate]; norm_num) (Circuit.depth_oneGate _ _).le _
    (kWiseIndependent_evenParity K) (by norm_num at hK ⊢; exact hK)

-- `AND₃` is true on one of the eight inputs.
example : fractionTrue (and3 (le_refl 3)) = 1 / 8 := by
  rw [fractionTrue, show (univ.filter fun x : Fin 3 → Bool =>
    (and3 (le_refl 3)).eval meaning x 0 = true).card = 1 by decide]
  norm_num

end ComplexityTests.Abstracts.BravermanTests
