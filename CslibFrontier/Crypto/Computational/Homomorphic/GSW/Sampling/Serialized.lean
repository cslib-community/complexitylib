/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Sampling
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PPT

/-!
# Serialized GSW encryption coins

The encryption coins retain the three indices `(n + 1) × w × m` as nested lists. Dimensions use
unary encodings and the strict PPT certificate charges the complete framed output. Serialized LWE
key-input sampling lives in `Crypto.Computational.LWE.KeyGen`.

## Main definitions

* `SerializedCoins`, `encSerializedCoins`: nested list representation and framing encoding.
* `sampleCoinsSerialized`: nested list-valued coin sampler.
* `serializeCoins`, `decodeCoins`: canonical lists and total defaulted decoders.

## Main results

* `isPPTOn_sampleCoinsSerialized`: uniform native sampler certificate.
* `eval_sampleCoinsSerialized`, `eval_decodeCoins_sampleCoinsSerialized`: exact bridges to the
  typed coin sampler.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability Turing.MultiTapeTM

/-- Encryption coins with the three indices `(n + 1) × w × m` kept in order. -/
abbrev SerializedCoins := List (List (List Bool))

/-- Two framed list levels around each raw Boolean row. -/
abbrev encSerializedCoins : SerializedCoins ↪ List Bool := encList (encList encBits)

/-- Independently sample the Boolean entries of the encryption matrix in index order. -/
noncomputable def sampleCoinsSerialized (n m w : ℕ) : ProbComp SerializedCoins :=
  OracleComp.replicate (n + 1)
    (OracleComp.replicate w (OracleComp.replicate m (ProbComp.uniform Bool)))

/-- List all three encryption-coin indices without flattening or reordering them. -/
def serializeCoins {n m w : ℕ}
    (coins : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) : SerializedCoins :=
  List.ofFn (fun i => List.ofFn (fun j => List.ofFn (fun k => coins (i, j) k)))

/-- Read the encryption-coin matrix from arbitrary nested lists, padding absent entries with
`false` and ignoring excess entries. -/
def decodeCoins (n m w : ℕ) (coins : SerializedCoins) :
    Matrix (Fin (n + 1) × Fin w) (Fin m) Bool :=
  fun i j => ((coins.getD i.1.val []).getD i.2.val []).getD j.val false

/-- Canonical coin lists decode to the original matrix, including empty dimensions. -/
@[simp] theorem decode_serializeCoins {n m w : ℕ}
    (coins : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    decodeCoins n m w (serializeCoins coins) = coins := by
  funext i j
  simp only [decodeCoins, serializeCoins, List.getD_ofFn]

/-- The efficient coin sampler has exactly the typed binary matrix's full joint law. -/
theorem eval_sampleCoinsSerialized (n m w : ℕ) :
    ProbComp.eval (sampleCoinsSerialized n m w) =
      (ProbComp.eval (sampleCoins n m w)).map serializeCoins := by
  have hrow := ProbComp.eval_replicateFin_map
    (PMF.map_id (ProbComp.eval (ProbComp.uniform Bool))).symm m
  have hinner := ProbComp.eval_replicateFin_map hrow w
  have houter := ProbComp.eval_replicateFin_map hinner (n + 1)
  unfold serializeCoins
  simp only [sampleCoins, bind_pure_comp, Matrix]
  rw [ProbComp.eval_map, PMF.map_comp]
  simpa only [sampleCoinsSerialized, Function.comp_def,
    Function.uncurry, id] using houter

/-- Decoding the efficient sampled lists recovers the mathematical encryption-coin sampler. -/
theorem eval_decodeCoins_sampleCoinsSerialized (n m w : ℕ) :
    ProbComp.eval (decodeCoins n m w <$> sampleCoinsSerialized n m w) =
      ProbComp.eval (sampleCoins n m w) := by
  rw [ProbComp.eval_map, eval_sampleCoinsSerialized, PMF.map_comp]
  simp only [Function.comp_def, decode_serializeCoins]
  exact PMF.map_id _

variable {α : Type} {input : α ↪ List Bool} {n m w : α → ℕ}

/-- Uniform strict PPT generation of the complete encryption coin matrix, including zero
dimensions. Every row and outer list delimiter is charged by the output encoding. -/
@[fun_prop]
theorem isPPTOn_sampleCoinsSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary) :
    IsPPTOn input encSerializedCoins
      (fun a => sampleCoinsSerialized (n a) (m a) (w a)) := by
  exact (((isPPTOn_uniform_bool input).replicate_bool hm).replicate
    hw).replicate (by fun_prop)

end Cslib.Crypto.Homomorphic.GSW
