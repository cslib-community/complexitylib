/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Sampling
public import Complexity.Computability.Probabilistic.CenteredBinomial
public import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Foundations.Data.List.Lookup
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PPT

/-!
# Serialized GSW random inputs

The key-input sampler returns a secret list, a list of public-matrix rows and a signed error
list. The encryption coins retain the three indices `(n + 1) × w × m` as nested lists. All
dimensions use unary encodings, residues use binary natural encodings, and errors use the
signed binary integer encoding. The strict PPT certificates charge the complete framed output.

These certificates concern random-input generation. They do not certify modular matrix
arithmetic, the complete GSW key-generation or encryption algorithms, or computational security.

## Main definitions

* `SerializedKeyInputs`, `SerializedCoins`: finite list representations of the sampled inputs.
* `sampleKeyInputsSerialized`, `sampleCoinsSerialized`: actual list-valued sampling programs.
* `serializeKeyInputs`, `serializeCoins`, `decodeKeyInputs`, `decodeCoins`: canonical lists and
  total defaulted decoders for the typed random inputs.

## Main results

* `isPPTOn_sampleKeyInputsSerialized`, `isPPTOn_sampleCoinsSerialized`: uniform native sampler
  certificates for efficiently computed dimensions.
* `eval_sampleKeyInputsSerialized`, `eval_sampleCoinsSerialized`: exact distribution bridges.
* `eval_decodeKeyInputs_sampleKeyInputsSerialized`, `eval_decodeCoins_sampleCoinsSerialized`:
  decoding the efficient samplers recovers the typed samplers' full joint laws.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Algorithm 8][NISTFIPS203]
  for the exact finite noise construction.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability Turing.MultiTapeTM

/-- Secret entries, public-matrix rows and signed errors, without dependent dimensions. -/
abbrev SerializedKeyInputs := List ℕ × (List (List ℕ) × List ℤ)

/-- Binary residues and signed binary errors, with all list and pair framing. -/
abbrev encSerializedKeyInputs : SerializedKeyInputs ↪ List Bool :=
  encPair (encList encNat) (encPair (encList (encList encNat)) (encList encIntBin))

/-- Encryption coins with the three indices `(n + 1) × w × m` kept in order. -/
abbrev SerializedCoins := List (List (List Bool))

/-- Two framed list levels around each raw Boolean row. -/
abbrev encSerializedCoins : SerializedCoins ↪ List Bool := encList (encList encBits)

/-- Independently sample every key-input entry using binary residues and signed errors. -/
noncomputable def sampleKeyInputsSerialized (n m w η : ℕ) : ProbComp SerializedKeyInputs := do
  let secret ← OracleComp.replicate n (sampleBinaryNat w)
  let publicPart ← OracleComp.replicate m (OracleComp.replicate n (sampleBinaryNat w))
  let error ← OracleComp.replicate m (sampleCenteredBinomial η)
  return (secret, (publicPart, error))

/-- Independently sample the Boolean entries of the encryption matrix in index order. -/
noncomputable def sampleCoinsSerialized (n m w : ℕ) : ProbComp SerializedCoins :=
  OracleComp.replicate (n + 1)
    (OracleComp.replicate w (OracleComp.replicate m (ProbComp.uniform Bool)))

/-- List every residue's canonical representative and every signed error in coordinate order. -/
def serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) : SerializedKeyInputs :=
  (List.ofFn (fun i => (inputs.secret i).val),
    (List.ofFn (fun i => List.ofFn (fun j => (inputs.publicPart i j).val)),
      List.ofFn inputs.error))

/-- Read fixed dimensions from arbitrary lists, padding absent entries with zero and reducing
natural representatives modulo `2 ^ w`. Excess entries are ignored. -/
def decodeKeyInputs (n m w : ℕ) (inputs : SerializedKeyInputs) : KeyInputs n m w :=
  ⟨fun i => (inputs.1.getD i.val 0 : ZMod (2 ^ w)),
    fun i j => ((inputs.2.1.getD i.val []).getD j.val 0 : ZMod (2 ^ w)),
    fun i => inputs.2.2.getD i.val 0⟩

/-- Canonical lists decode to their original typed key inputs, including empty dimensions. -/
@[simp] theorem decode_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    decodeKeyInputs n m w (serializeKeyInputs inputs) = inputs := by
  cases inputs
  simp only [decodeKeyInputs, serializeKeyInputs, List.getD_ofFn, ZMod.natCast_zmod_val]

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

private theorem eval_sampleBinaryNat_eq_map_val (w : ℕ) :
    ProbComp.eval (sampleBinaryNat w) =
      (ProbComp.eval (sampleResidue w)).map ZMod.val := by
  rw [sampleResidue, ProbComp.eval_map, PMF.map_comp]
  symm
  calc
    _ = (ProbComp.eval (sampleBinaryNat w)).map id :=
      PMF.map_congr_on_support _ _ _ (fun value hvalue =>
        ZMod.val_natCast_of_lt ((mem_support_sampleBinaryNat_iff w value).mp hvalue))
    _ = _ := PMF.map_id _

/-- The efficient key-input sampler has exactly the typed sampler's joint law, including the
independence of the secret, public-matrix part and signed errors. -/
theorem eval_sampleKeyInputsSerialized (n m w η : ℕ) :
    ProbComp.eval (sampleKeyInputsSerialized n m w η) =
      (ProbComp.eval (sampleKeyInputs n m w η)).map serializeKeyInputs := by
  have hsecret := ProbComp.eval_replicateFin_map (eval_sampleBinaryNat_eq_map_val w) n
  have hpublicPart := ProbComp.eval_replicateFin_map hsecret m
  have herror := ProbComp.eval_replicateFin_map
    (PMF.map_id (ProbComp.eval (sampleCenteredBinomial η))).symm m
  rw [eval_sampleKeyInputs]
  change _ = (ProbComp.eval (sampleVector n w)).map _ at hsecret
  change _ = (ProbComp.eval (sampleMatrix m n w)).map _ at hpublicPart
  rw [eval_sampleVector] at hsecret
  rw [eval_sampleMatrix] at hpublicPart
  simp only [sampleKeyInputsSerialized, ProbComp.eval_bind, ProbComp.eval_pure,
    hsecret, hpublicPart, herror, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    Matrix, PMF.bind_map, PMF.map_bind, PMF.pure_map, serializeKeyInputs,
    Function.comp_def, id]

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

/-- Decoding the efficient sampled lists recovers the mathematical key-input sampler. -/
theorem eval_decodeKeyInputs_sampleKeyInputsSerialized (n m w η : ℕ) :
    ProbComp.eval (decodeKeyInputs n m w <$> sampleKeyInputsSerialized n m w η) =
      ProbComp.eval (sampleKeyInputs n m w η) := by
  rw [ProbComp.eval_map, eval_sampleKeyInputsSerialized, PMF.map_comp]
  simp only [Function.comp_def, decode_serializeKeyInputs]
  exact PMF.map_id _

/-- Decoding the efficient sampled lists recovers the mathematical encryption-coin sampler. -/
theorem eval_decodeCoins_sampleCoinsSerialized (n m w : ℕ) :
    ProbComp.eval (decodeCoins n m w <$> sampleCoinsSerialized n m w) =
      ProbComp.eval (sampleCoins n m w) := by
  rw [ProbComp.eval_map, eval_sampleCoinsSerialized, PMF.map_comp]
  simp only [Function.comp_def, decode_serializeCoins]
  exact PMF.map_id _

variable {α : Type} {input : α ↪ List Bool} {n m w η : α → ℕ}

/-- Uniform strict PPT generation of every serialized key input. The dimensions may depend
on the caller's complete encoded input; no finite-rank output encoding is used. -/
@[fun_prop]
theorem isPPTOn_sampleKeyInputsSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hη : ComputableInPolyTime η input encUnary) :
    IsPPTOn input encSerializedKeyInputs
      (fun a => sampleKeyInputsSerialized (n a) (m a) (w a) (η a)) := by
  have hsecret := hw.sampleBinaryNat.replicate hn
  have hpublicPart := hsecret.replicate hm
  have herror := (isPPTOn_sampleCenteredBinomial.preprocess hη).replicate hm
  unfold sampleKeyInputsSerialized encSerializedKeyInputs
  ppt

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
