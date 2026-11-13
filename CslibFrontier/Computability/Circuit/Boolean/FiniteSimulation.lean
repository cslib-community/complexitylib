/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.BitBlastCompiler
public import CslibFrontier.Foundations.Data.BitString.FiniteEncoding

/-!
# Boolean simulation over every finite nonempty carrier

Any bounded-arity interpreted circuit over a finite nonempty carrier has a Boolean circuit
preserving all outputs on valid encoded inputs. The fixed carrier encoding is `fintypeEncoding`,
using `Nat.clog 2 (Fintype.card F)` bits per value. The per-gate Boolean cost therefore depends
only on the carrier, not on the circuit or its input count. Constants count as gates and wires
are free. The total decoder is supplied by the generic inverse-function construction.

For arithmetic circuits over finite fields this establishes the arithmetic-to-Boolean direction
of [Arora–Barak, web draft 2007-01-08, Chapter 14 Exercise 1,
printed p. 265/PDF p. 281][AroraBarak07], with the encoding and size convention explicit.
The reverse simulation is separate. Neither uniform runtime nor formal-polynomial equality
is claimed; the encoding uses a noncomputable finite enumeration.

## Main results

* `Cslib.Circuits.Circuit.exists_finite_boolean`: Boolean simulation with logarithmic-width
  finite-carrier encoding, without a supplied encoding hypothesis.
-/

public section

universe v

namespace Cslib.Circuits

/-- A finite nonempty carrier has a single fixed encoding under which every circuit whose
operations have arity at most two admits constant-factor Boolean simulation. The constant is
`bitBlastCost (Nat.clog 2 (Fintype.card F))`; correctness is on valid encoded inputs. -/
theorem Circuit.exists_finite_boolean {F : Type*} [Fintype F] [Nonempty F]
    {σ : Signature.{v}} (I : Interpretation σ F) (hArity : ∀ op, σ.Arity op ≤ 2)
    {N M : ℕ} (c : Circuit σ N M) :
    ∃ b : Circuit Boolean.signature (N * Nat.clog 2 (Fintype.card F))
        (M * Nat.clog 2 (Fintype.card F)),
      b.size ≤ c.size * bitBlastCost (Nat.clog 2 (Fintype.card F)) ∧
        ∀ x, b.eval Boolean.interpretation
          (BitString.blocksEquiv.symm (BitString.fintypeEncoding F ∘ x)) =
          BitString.blocksEquiv.symm (BitString.fintypeEncoding F ∘ c.eval I x) :=
  c.exists_encoded_boolean I hArity (BitString.fintypeEncoding F)
    (Function.invFun (BitString.fintypeEncoding F))
    (Function.leftInverse_invFun (BitString.fintypeEncoding F).injective)

end Cslib.Circuits
