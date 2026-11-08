/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.Boolean.Smolensky

/-! # Bridges for constant-depth parity lower bounds -/

namespace ComplexityTests.Abstracts.ConstantDepthBridge

/-- Parity is true when an odd number of bits are true. -/
def parity (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % 2 = 1)

/-- The elementary unbounded-fan-in basis has unary NOT and AND/OR of every arity.
Nullary AND and OR are the two constants. Its model module is explicitly allowed below. -/
abbrev ACBasis := Cslib.Circuits.Boolean.Unbounded.signature

/-- Ordinary Boolean meaning of unbounded AND/OR/NOT. -/
def meaning : Cslib.Circuits.Interpretation ACBasis Bool :=
  Cslib.Circuits.Boolean.Unbounded.interpretation

/-- Depth charges one for AND/OR, including their nullary constant cases, and zero for NOT.
This weight affects depth only: `C.size` counts every operation gate, including NOT and
constants. -/
def andOrCost : Cslib.Circuits.Boolean.Unbounded.Op → ℕ
  | .not => 0
  | .and _ | .or _ => 1

/-- Add one gate of each arity, true when its number of true inputs is nonzero modulo `p`. -/
def modularMeaning (p : ℕ) :
    Cslib.Circuits.Interpretation Cslib.Circuits.Boolean.Unbounded.extSignature Bool :=
  Cslib.Circuits.Boolean.Unbounded.extInterpretation
    (fun _ x => decide ((Finset.univ.filter fun i => x i = true).card % p ≠ 0))

/-- **Håstad.** A parity circuit of AND/OR depth at most `d` needs `2^s` gates whenever
`s ≥ 2` and `17s(16s+1)^(d-2) ≤ n`. Subtraction is in naturals. This gives the sharp exponent
`1/(d-1)` for every fixed `d ≥ 2`. Negations cost zero in depth and one gate in size. -/
theorem hastad {n d s : ℕ} (C : Cslib.Circuits.Circuit ACBasis n 1)
    (correct : ∀ x, C.eval meaning x 0 = parity n x) (hs : 2 ≤ s)
    (depth : C.depthWith andOrCost ≤ d) (budget : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ C.size :=
by
  apply Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depthWith_le
    (C := C) ?_ hs depth budget
  intro x
  funext i
  have : i = 0 := Fin.ext (by omega)
  subst i
  exact correct x

/-- **Razborov–Smolensky.** For an odd prime `p`, even circuits with MOD_p gates need
exponentially many gates for parity at every fixed depth. This finite bound counts every gate
and every depth level, including NOT and constants; the modulus is explicit and fixed. -/
theorem razborov_smolensky {p n ℓ : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.extSignature n 1)
    (correct : ∀ x, C.eval (modularMeaning p) x 0 = parity n x) (hℓ : 1 ≤ ℓ)
    (budget : 100 * (((p - 1) * ℓ) ^ C.depth + 1) ^ 2 ≤ n + 1) :
    2 * 2 ^ ℓ ≤ 5 * C.size :=
by
  let : Fact p.Prime := ⟨prime⟩
  apply Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity
    odd (C := C) ?_ hℓ budget
  intro x
  funext i
  have : i = 0 := Fin.ext (by omega)
  subst i
  exact correct x

end ComplexityTests.Abstracts.ConstantDepthBridge
