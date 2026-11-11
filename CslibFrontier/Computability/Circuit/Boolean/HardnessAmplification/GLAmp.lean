/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Block
public import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct

/-!
# The Goldreich–Levin amplification of a Boolean function

`glAmp f k` is the function `Amp(f) = (f^k)^GL` of Carmosino, Impagliazzo, Kabanets and
Kolokolova [CarmosinoImpagliazzoKabanetsKolokolova2016, Thm 4.3]: the `k`-fold direct product of
`f` followed by the Goldreich–Levin inner product [GoldreichLevin1989]. On `k` blocks
`x₁, …, x_k` of `n` bits followed by a mask `r` of `k` bits, it is `∑ᵢ rᵢ f(xᵢ)` over GF(2).

The blocks come first, cut by `Cslib.BitString.block` as in `Cslib.Circuits.Boolean.xorPower`,
and the mask last, as in `Cslib.Circuits.Boolean.hardnessEncode`. This module has only the
definition and its evaluation; the circuit computing it with one parity gate is
`Cslib.Circuits.Boolean.glAmpCircuit`.

## Main definitions

* `Cslib.Circuits.Boolean.glAmp`: `Amp(f) = (f^k)^GL` on `k * n + k` bits.

## Main results

* `Cslib.Circuits.Boolean.glAmp_append`: at `(x, r)` it is the inner product of the values of
  `f` on the blocks of `x` with `r`.
* `Cslib.Circuits.Boolean.glAmp_append_eq_parityOn`: equivalently, the parity of the values of
  `f` on the blocks that `r` selects.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
* [O. Goldreich, L. A. Levin, *A hard-core predicate for all one-way
  functions*][GoldreichLevin1989]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-- **The Goldreich–Levin amplification** `Amp(f) = (f^k)^GL`
[CarmosinoImpagliazzoKabanetsKolokolova2016, Thm 4.3]. On an input of `k * n + k` bits, read the
first `k * n` bits as `k` blocks of `n` bits (`Cslib.BitString.block`) and the last `k` bits as a
mask `r`, and output the inner product over GF(2) of the values of `f` on the blocks with `r`. -/
def glAmp (f : BooleanFunction n) (k : ℕ) : BooleanFunction (k * n + k) :=
  fun y => (fun i => f (BitString.block (fun a => y (Fin.castAdd k a)) i)) ⬝ᵥ
    fun j => y (Fin.natAdd (k * n) j)

/-- At the input `(x, r)`, `glAmp f k` is the inner product of the values of `f` on the blocks of
`x` with `r`. -/
@[simp]
theorem glAmp_append (f : BooleanFunction n) (k : ℕ) (x : BitString (k * n)) (r : BitString k) :
    glAmp f k (Fin.append x r) = (fun i => f (BitString.block x i)) ⬝ᵥ r := by
  simp only [glAmp, Fin.append_left, Fin.append_right]

/-- At the input `(x, r)`, `glAmp f k` is the parity of the values of `f` on the blocks of `x`
that `r` selects. -/
theorem glAmp_append_eq_parityOn (f : BooleanFunction n) (k : ℕ) (x : BitString (k * n))
    (r : BitString k) :
    glAmp f k (Fin.append x r) = parityOn {i | r i = true} fun i => f (BitString.block x i) := by
  rw [glAmp_append, BitString.dotProduct_eq_parityOn]

end Cslib.Circuits.Boolean
