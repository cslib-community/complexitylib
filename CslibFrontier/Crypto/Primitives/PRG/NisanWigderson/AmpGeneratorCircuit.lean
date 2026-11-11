/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmpCircuit
public import CslibFrontier.Computability.MCSP.Basic
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.MXCircuit
import CslibFrontier.Computability.Circuit.CompositionDepth

/-!
# The functions of the CIKK generator in AC⁰[2]

Carmosino, Impagliazzo, Kabanets and Kolokolova build a black-box generator within AC⁰[p]
(Definition 3.1 and Theorem 3.2, p. 10:10) from the Nisan–Wigderson generator of the amplified
function `Amp(f)`. For a seed `z`, the function `g_z` maps `i` to bit `i` of the generator's output
on `z`, that is `g_z(i) = Amp(f)(z|S_i)`, and each `g_z` has small circuits relative to `f`
(Nonuniform AC⁰[p]-Efficiency, proof of Theorem 3.2, p. 10:11)
[CarmosinoImpagliazzoKabanetsKolokolova2016]. This file proves that efficiency clause for `p = 2`,
the amplification `Amp(f) = Cslib.Circuits.Boolean.glAmp f k` on `n' = k n + k` bits and the design
`Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial n' ℓ`.

From a circuit `C` for `f`, `glAmpGeneratorCircuit φ C k ℓ z` computes `g_z`. Its `ℓ` inputs `i`,
together with the seed `z` fixed by two constant gates, feed the selection
`Cslib.Crypto.PRG.NisanWigderson.mxCircuit` (Theorem 3.7, p. 10:13). Its `n'` outputs `z|S_i` feed
the amplification circuit `Cslib.Circuits.Boolean.glAmpCircuit` (proof of Theorem 4.3, p. 10:16).
It has at most `k |C| + 6 n'² + 3` gates and depth at most `C.depth + 7`.

The construction is generic in the basis, as `glAmpCircuit` is: `C` is a circuit over any
signature `σ`, and the rest is built over `Unbounded.extSignature` and translated into `σ` along a
map `φ` that keeps its meaning under `MOD₂` gates. For AC⁰[2] circuits take
`σ = Unbounded.extSignature`, `I = Unbounded.extInterpretation (modGate 2)` and
`φ = Signature.Hom.id _`.

This differs from the source in these ways:

* only `p = 2` is built, over `BinaryField e` with `e = binaryFieldDegree n'`, so for `k ≥ 1` the
  field has between `n'` and `2 n'` elements and the seed has `n' 2 ^ e ≤ 2 n'²` bits, where the
  source has `n'²`;
* the design has overlap `ℓ - 1` and `2 ^ ℓ` blocks, numbered by `BitString.equivFin` (least
  significant bit first), where the source has overlap at most `ℓ`;
* the bounds are explicit where the source has `poly(m)`: gates are counted
  (`Cslib.Circuits.Circuit.size`), not wires, and depth is the unit-cost
  `Cslib.Circuits.Circuit.depth`, negations included;
* the source puts `g_z` in `AC⁰[2]^f` (Definition 3.1). No oracle-circuit statement is formalized
  here. Because the construction is generic in the basis, taking for `C` the one-gate circuit of an
  `f`-oracle operation makes `glAmpGeneratorCircuit` that oracle circuit, with `k` oracle gates;
* only the efficiency clause of Definition 3.1 is proved here, and no uniformity is claimed.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.glAmpGeneratorCircuit`: the circuit for `g_z` built from a
  circuit for `f`.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.eval_glAmpGeneratorCircuit`,
  `Cslib.Circuits.Circuit.Computes.glAmpGeneratorCircuit`: it computes `g_z`.
* `Cslib.Crypto.PRG.NisanWigderson.size_glAmpGeneratorCircuit`,
  `Cslib.Crypto.PRG.NisanWigderson.size_glAmpGeneratorCircuit_le`: it has
  `k |C| + k + 3 + n' (2 e + 2 ^ e + 1) ≤ k |C| + 6 n'² + 3` gates.
* `Cslib.Crypto.PRG.NisanWigderson.depth_glAmpGeneratorCircuit_le`: its depth is at most
  `C.depth + 7`.
* `Cslib.Crypto.PRG.NisanWigderson.exists_circuit_generator_glAmp`: Theorem 3.2's Nonuniform
  AC⁰[2]-Efficiency for this generator.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016], Definition 3.1, Theorems 3.2, 3.7 and 4.3
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded

variable {σ : Signature} {I : Interpretation σ Bool} {n : ℕ}

/-- The circuit for `g_z(i) = glAmp f k (z|S_i)` from a circuit `C` for `f`: the inputs `i` and the
fixed seed `z` feed the selection `mxCircuit`, whose outputs feed `glAmpCircuit φ C k`. The
selection and the constant gates are translated into `σ` along `φ`. -/
noncomputable def glAmpGeneratorCircuit (φ : extSignature.Hom σ) (C : Circuit σ n 1) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) : Circuit σ ℓ 1 :=
  (glAmpCircuit φ C k).comp
    (((mxCircuit (k * n + k) ℓ).mapOp φ).comp
      ((Circuit.wiring σ id).append (constsCircuit (φ.comp toExt) z)))

section Circuit

variable (φ : extSignature.Hom σ)

/-- `glAmpGeneratorCircuit φ C k ℓ z` has `k |C| + k + 3 + n' (2 e + 2 ^ e + 1)` gates, where
`n' = k n + k` and `e = binaryFieldDegree n'`. -/
@[simp] theorem size_glAmpGeneratorCircuit (C : Circuit σ n 1) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    (glAmpGeneratorCircuit φ C k ℓ z).size = k * C.size + k + 3 + (k * n + k) *
      (2 * binaryFieldDegree (k * n + k) + 2 ^ binaryFieldDegree (k * n + k) + 1) := by
  simp only [glAmpGeneratorCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
    Circuit.size_mapOp, size_glAmpCircuit, size_mxCircuit, size_constsCircuit]
  omega

/-- `glAmpGeneratorCircuit φ C k ℓ z` has at most `k |C| + 6 n'² + 3` gates, where `n' = k n + k`,
whatever `ℓ`. -/
theorem size_glAmpGeneratorCircuit_le (C : Circuit σ n 1) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    (glAmpGeneratorCircuit φ C k ℓ z).size ≤ k * C.size + 6 * (k * n + k) ^ 2 + 3 := by
  have hmx := size_mxCircuit_le (k * n + k) ℓ
  have hk : k ≤ (k * n + k) ^ 2 :=
    (Nat.le_add_left k (k * n)).trans (Nat.le_self_pow two_ne_zero _)
  rw [size_mxCircuit] at hmx
  rw [size_glAmpGeneratorCircuit]
  omega

/-- `glAmpGeneratorCircuit φ C k ℓ z` is at most seven deeper than `C`: one for the constants,
four for the selection and two for the amplification. -/
theorem depth_glAmpGeneratorCircuit_le (C : Circuit σ n 1) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    (glAmpGeneratorCircuit φ C k ℓ z).depth ≤ C.depth + 7 := by
  have hin : ((Circuit.wiring σ id).append (constsCircuit (n := ℓ) (φ.comp toExt) z)).depth ≤ 1 :=
    (Circuit.depth_append_le _ _).trans (max_le (by simp) (depth_constsCircuit_le z))
  have hmx := Circuit.depth_comp_le ((mxCircuit (k * n + k) ℓ).mapOp φ)
    ((Circuit.wiring σ id).append (constsCircuit (n := ℓ) (φ.comp toExt) z))
  rw [Circuit.depth_mapOp] at hmx
  have := depth_mxCircuit_le (k * n + k) ℓ
  have := depth_glAmpCircuit_le φ C k
  refine (Circuit.depth_comp_le _ _).trans ?_
  omega

variable [φ.Preserves (extInterpretation (modGate 2)) I]

/-- `glAmpGeneratorCircuit φ C k ℓ z` computes `g_z`: on `i` it outputs bit `equivFin ℓ i` of the
Nisan–Wigderson generator of `glAmp f k` on the seed `z`, where `f` is the function `C`
computes. -/
theorem eval_glAmpGeneratorCircuit (C : Circuit σ n 1) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) (i : BitString ℓ)
    (o : Fin 1) :
    (glAmpGeneratorCircuit φ C k ℓ z).eval I i o =
      generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp (fun x => C.eval I x 0) k) z
        (BitString.equivFin ℓ i) := by
  have : (φ.comp toExt).Preserves interpretation I :=
    Signature.Hom.Preserves.comp inferInstance (preserves_toExt (modGate 2))
  rw [glAmpGeneratorCircuit, Circuit.eval_comp, eval_glAmpCircuit, Circuit.eval_comp,
    Circuit.eval_mapOp (I := extInterpretation (modGate 2)), Circuit.eval_append,
    Circuit.eval_wiring, eval_constsCircuit, Function.comp_id, eval_mxCircuit, generator_apply]

/-- **`g_z` has small circuits relative to `f`** [CarmosinoImpagliazzoKabanetsKolokolova2016,
proof of Thm 3.2, p. 10:11]: if `C` computes `f`, then `glAmpGeneratorCircuit φ C k ℓ z` computes
the function whose truth table is the Nisan–Wigderson generator of `glAmp f k` on the seed `z`. -/
theorem _root_.Cslib.Circuits.Circuit.Computes.glAmpGeneratorCircuit {C : Circuit σ n 1}
    {f : BooleanFunction n} (hC : C.Computes I (single f)) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    (glAmpGeneratorCircuit φ C k ℓ z).Computes I
      (single ((MCSP.truthTable ℓ).symm
        (generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp f k) z))) := fun i => by
  funext o
  rw [eval_glAmpGeneratorCircuit, single_apply, MCSP.truthTable_symm_apply]
  exact congrArg (fun g => generator _ (glAmp g k) z (BitString.equivFin ℓ i))
    (funext fun x => congrFun (hC x) 0)

end Circuit

/-- **Nonuniform AC⁰[2]-Efficiency of the CIKK generator**
[CarmosinoImpagliazzoKabanetsKolokolova2016, Def 3.1 and proof of Thm 3.2, pp. 10:10–10:11], for
`p = 2`, `Amp(f) = glAmp f k` and the design `Design.binaryPolynomial (k n + k) ℓ`. If `C`
computes `f`, then for every seed `z` the function `g_z`, whose truth table is the Nisan–Wigderson
generator of `glAmp f k` on `z`, is computed from `k` copies of `C` with at most `6 n'² + 3` more
gates (`n' = k n + k`) and at most `7` more depth. The basis is any `σ` into which `φ` translates
the unbounded fan-in basis with `MOD₂` gates; `σ = Unbounded.extSignature` with
`φ = Signature.Hom.id _` gives AC⁰[2] circuits. -/
theorem exists_circuit_generator_glAmp (φ : extSignature.Hom σ)
    [φ.Preserves (extInterpretation (modGate 2)) I] {C : Circuit σ n 1} {f : BooleanFunction n}
    (hC : C.Computes I (single f)) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    ∃ G : Circuit σ ℓ 1,
      G.Computes I (single ((MCSP.truthTable ℓ).symm
        (generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp f k) z))) ∧
      G.size ≤ k * C.size + 6 * (k * n + k) ^ 2 + 3 ∧ G.depth ≤ C.depth + 7 :=
  ⟨_, hC.glAmpGeneratorCircuit φ k ℓ z, size_glAmpGeneratorCircuit_le φ C k ℓ z,
    depth_glAmpGeneratorCircuit_le φ C k ℓ z⟩

end Cslib.Crypto.PRG.NisanWigderson
