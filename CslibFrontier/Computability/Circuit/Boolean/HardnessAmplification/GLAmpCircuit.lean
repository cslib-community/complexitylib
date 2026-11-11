/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Gadgets
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmp
public import CslibFrontier.Computability.Circuit.Replication
import CslibFrontier.Computability.Circuit.ReplicationDepth

/-!
# A circuit for the Goldreich–Levin amplification

From a circuit `C` for `f`, `glAmpCircuit φ C k` computes `glAmp f k = (f^k)^GL`: `k` copies of
`C` on the blocks of the input (`Cslib.Circuits.Circuit.replicateScalar`), then the inner product
over GF(2) with the mask (`Cslib.Circuits.Boolean.Unbounded.innerProductCircuit`). It has
`k * C.size + k + 1` gates and depth at most `C.depth + 2`. This is the efficiency part of
[CarmosinoImpagliazzoKabanetsKolokolova2016, Thm 4.3 and its proof, p. 10:16]: `Amp(f)` is
computable from `f` with only an additive `O(k)` more gates and constant more depth, using one
parity gate.

The construction is generic in the basis. `C` is a circuit over any signature `σ`, and the
`k` conjunctions and the parity gate are built over `Unbounded.extSignature` and translated into
`σ` along a map `φ` that keeps their meaning under `MOD₂` gates
(`φ.Preserves (Unbounded.extInterpretation (modGate 2)) I`). For AC⁰[2] circuits take
`σ = Unbounded.extSignature` and `φ = Signature.Hom.id _`.

Deviation from the source: CIKK's Nonuniform Λ-Efficiency (Def 3.4, pp. 10:10–10:11) puts `Amp(f)`
in `AC⁰[2]^f`. No oracle-circuit statement is formalized here. Because the construction is
generic in the basis, taking for `C` the one-gate circuit of an `f`-oracle operation makes
`glAmpCircuit` that oracle circuit, with `k` oracle gates.

Size counts gates (`Circuit.size`) and depth is the unit-cost `Circuit.depth`, in which negations
count.

## Main definitions

* `Cslib.Circuits.Boolean.glAmpCircuit`: the circuit for `glAmp f k` built from a circuit for `f`.

## Main results

* `Cslib.Circuits.Boolean.eval_glAmpCircuit`, `Cslib.Circuits.Circuit.Computes.glAmpCircuit`: it
  computes the amplification of the function `C` computes.
* `Cslib.Circuits.Boolean.size_glAmpCircuit`: it has `k * C.size + k + 1` gates.
* `Cslib.Circuits.Boolean.depth_glAmpCircuit_le`: its depth is at most `C.depth + 2`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016], Def 3.4, Thm 4.3
-/

public section

namespace Cslib.Circuits.Boolean

open Unbounded

variable {σ : Signature} {I : Interpretation σ Bool} {n : ℕ}

/-- The circuit for `glAmp f k` from a circuit `C` for `f`: `k` copies of `C` on the blocks of the
first `k * n` inputs, and the inner product over GF(2) of their outputs with the last `k` inputs,
translated into `σ` along `φ`. -/
def glAmpCircuit (φ : extSignature.Hom σ) (C : Circuit σ n 1) (k : ℕ) :
    Circuit σ (k * n + k) 1 :=
  ((innerProductCircuit k).mapOp φ).comp
    (((C.replicateScalar k).comp (Circuit.wiring σ (Fin.castAdd k))).append
      (Circuit.wiring σ (Fin.natAdd (k * n))))

variable (φ : extSignature.Hom σ) [φ.Preserves (extInterpretation (modGate 2)) I]

/-- `glAmpCircuit φ C k` computes the amplification of the function that `C` computes. -/
theorem eval_glAmpCircuit (C : Circuit σ n 1) (k : ℕ) (y : BitString (k * n + k)) (o : Fin 1) :
    (glAmpCircuit φ C k).eval I y o = glAmp (fun x => C.eval I x 0) k y := by
  rw [glAmpCircuit, Circuit.eval_comp, Circuit.eval_mapOp (I := extInterpretation (modGate 2)),
    Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_wiring,
    Circuit.eval_replicateScalar, eval_innerProductCircuit]
  rfl

/-- **The Goldreich–Levin amplification is efficient** [CarmosinoImpagliazzoKabanetsKolokolova2016,
proof of Thm 4.3, p. 10:16]: if `C` computes `f`, then `glAmpCircuit φ C k` computes `glAmp f k`.
-/
theorem _root_.Cslib.Circuits.Circuit.Computes.glAmpCircuit {C : Circuit σ n 1}
    {f : BooleanFunction n} (hC : C.Computes I (single f)) (k : ℕ) :
    (glAmpCircuit φ C k).Computes I (single (glAmp f k)) := fun y => by
  funext o
  rw [eval_glAmpCircuit, single_apply]
  exact congrArg (glAmp · k y) (funext fun x => congrFun (hC x) 0)

/-- `glAmpCircuit φ C k` has `k * C.size + k + 1` gates. -/
@[simp] theorem size_glAmpCircuit (C : Circuit σ n 1) (k : ℕ) :
    (glAmpCircuit φ C k).size = k * C.size + k + 1 := by
  simp only [glAmpCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
    Circuit.size_replicateScalar, Circuit.size_mapOp, size_innerProductCircuit]
  omega

/-- `glAmpCircuit φ C k` is at most two deeper than `C`. -/
theorem depth_glAmpCircuit_le (C : Circuit σ n 1) (k : ℕ) :
    (glAmpCircuit φ C k).depth ≤ C.depth + 2 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_mapOp, add_comm]
  refine Nat.add_le_add ((Circuit.depth_append_le _ _).trans (max_le ?_ (by simp)))
    (depth_innerProductCircuit_le k)
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, add_zero]
  exact Circuit.depth_replicateScalar_le C k

end Cslib.Circuits.Boolean
