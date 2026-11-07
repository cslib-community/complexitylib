/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.ConstantDepthBridge

/-! # Parity resists shallow circuits

An AND or OR gate can inspect arbitrarily many input bits at once. Even with that freedom,
a fixed number of layers cannot compute parity with polynomially many gates: as input length
grows, every polynomial gate budget eventually fails. Håstad's argument uses random
restrictions; Razborov and Smolensky show that adding modular counting gates of any fixed odd
prime modulus still does not make parity easy.

The statements give finite numerical bounds and expose their different depth conventions.
These are nonuniform size lower bounds. The elementary gate basis and weighted-depth recursion
are the two allowed model modules; their meanings are explained below. Lean checks the bridge
proofs, and `#check_abstract` audits the remaining dependency boundary.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [A. Razborov, *Lower bounds on the size of bounded depth circuits*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds*][Smolensky1987]
* [S. Jukna, *Boolean Function Complexity*][Jukna2012]
-/

namespace ComplexityTests.Abstracts.ConstantDepthAbstract

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
  ConstantDepthBridge.hastad C correct hs depth budget

/-- **Razborov–Smolensky.** For an odd prime `p`, even circuits with MOD_p gates need
more than polynomially many gates for parity at every fixed depth. This bound counts every gate
and every depth level, including NOT and constants; the modulus is explicit and fixed. -/
theorem razborov_smolensky {p n ℓ : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.extSignature n 1)
    (correct : ∀ x, C.eval (modularMeaning p) x 0 = parity n x) (hℓ : 1 ≤ ℓ)
    (budget : 100 * (((p - 1) * ℓ) ^ C.depth + 1) ^ 2 ≤ n + 1) :
    2 * 2 ^ ℓ ≤ 5 * C.size :=
  ConstantDepthBridge.razborov_smolensky prime odd C correct hℓ budget

/-- info: abstract audit passed for `ComplexityTests.Abstracts.ConstantDepthAbstract`: 8 root
declarations -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.ConstantDepthAbstract allowing [
  Complexity.Computability.Circuit.Boolean.Unbounded,
  Complexity.Computability.Circuit.Depth
]

end ComplexityTests.Abstracts.ConstantDepthAbstract
