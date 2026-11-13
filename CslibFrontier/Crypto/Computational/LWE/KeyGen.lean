/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.CenteredBinomial
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.CenteredBinomial
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.SuppCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Generic LWE key generation, sampling, and serialization

Uniform power-of-two residue sampling, centered-binomial error sampling, LWE public matrix
generation `[B * t + e | B]`, flat uniform random tapes, serialized list/word codecs, exact
distributional bridges to `DecisionLWE`, and uniform strict polynomial-time certificates.

## Main definitions

* `Cslib.Crypto.LWE.secretVector`: the expanded secret `(1, -t)`.
* `Cslib.Crypto.LWE.publicMatrixInt`: `[B * t + e | B]` with integer errors cast modulo `2 ^ w`.
* `Cslib.Crypto.LWE.sampleResidue`, `Cslib.Crypto.LWE.sampleVector`,
  `Cslib.Crypto.LWE.sampleMatrix`: uniform modular samplers.
* `Cslib.Crypto.LWE.KeyInputs`, `Cslib.Crypto.LWE.sampleKeyInputs`,
  `Cslib.Crypto.LWE.keyGen`: typed LWE key generation.
* `Cslib.Crypto.LWE.noiseLaw`: scalar centered-binomial modular error distribution.
* `Cslib.Crypto.LWE.SerializedKeyInputs`, `Cslib.Crypto.LWE.encSerializedKeyInputs`,
  `Cslib.Crypto.LWE.sampleKeyInputsSerialized`, `Cslib.Crypto.LWE.serializeKeyInputs`,
  `Cslib.Crypto.LWE.decodeKeyInputs`: serialized random key inputs, encoding, and defaulted
  decoders.
* `Cslib.Crypto.LWE.serializePublicMatrix`, `Cslib.Crypto.LWE.serializeSecret`,
  `Cslib.Crypto.LWE.decodeSecret`: bit-word encodings for LWE matrices and secrets.
* `Cslib.Crypto.LWE.publicRowHead`, `Cslib.Crypto.LWE.publicMatrixSerialized`,
  `Cslib.Crypto.LWE.secretSerialized`, `Cslib.Crypto.LWE.keyGenSerialized`: executable bit-word
  key generation.

## Main results

* `Cslib.Crypto.LWE.publicMatrix_mulVec_secretVector`,
  `Cslib.Crypto.LWE.publicMatrixInt_mulVec_secretVector`: exact inner-product error identity.
* `Cslib.Crypto.LWE.mem_support_sampleKeyInputs_iff`: exact coordinatewise error bound on
  supported key inputs.
* `Cslib.Crypto.LWE.exists_uniform_seed_sampleKeyInputs`: flat uniform bit-tape realization.
* `Cslib.Crypto.LWE.eval_keyGen_publicMatrix`, `Cslib.Crypto.LWE.eval_keyGen_publicWord`,
  `Cslib.Crypto.LWE.eval_keyGenSerialized_publicWord`: exact match with `LWE.publicMatrixLaw`
  and `LWE.realEnsemble`.
* `Cslib.Crypto.LWE.isPPTOn_sampleKeyInputsSerialized`,
  `Cslib.Crypto.LWE.computableInPolyTime_publicMatrixSerialized`,
  `Cslib.Crypto.LWE.computableInPolyTime_secretSerialized`,
  `Cslib.Crypto.LWE.isPPTOn_keyGenSerialized`: uniform strict polynomial-time certificates.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*]
  [Regev2009]
* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Sections 2 and 3.1.
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Algorithm 8][NISTFIPS203]
  for the finite centered-binomial error distribution.
-/

@[expose] public section

namespace Cslib.Crypto.LWE

open ProbComp Probability BitString Turing.MultiTapeTM
open scoped BigOperators _root_.Matrix

/-! ### Secret vectors and LWE matrix identities -/

/-- The secret vector has leading coordinate one, followed by the negated secret entries. -/
def secretVector {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) : Fin (n + 1) → ZMod (2 ^ w) :=
  Fin.cons 1 (-t)

/-- Multiplying `[B * t + error | B]` by `(1, -t)` recovers the modular error vector. -/
theorem publicMatrix_mulVec_secretVector {n m w : ℕ}
    (B : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ZMod (2 ^ w)) :
    publicMatrix B t error *ᵥ secretVector t = error := by
  ext i
  simp [publicMatrix, secretVector, _root_.Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The LWE public matrix `[B * t + error | B]`, with integer errors cast modulo `2 ^ w`. -/
def publicMatrixInt {n m w : ℕ} (B : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ℤ) :
    _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) :=
  publicMatrix B t fun i => (error i : ZMod (2 ^ w))

/-- Multiplying `[B * t + error | B]` by `(1, -t)` recovers the cast integer errors. -/
theorem publicMatrixInt_mulVec_secretVector {n m w : ℕ}
    (B : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ℤ) :
    publicMatrixInt B t error *ᵥ secretVector t = fun i => (error i : ZMod (2 ^ w)) :=
  publicMatrix_mulVec_secretVector B t _

/-! ### Typed LWE key sampling -/

/-- Sample a uniformly random residue modulo `2 ^ w` from `w` fair bits. -/
noncomputable def sampleResidue (w : ℕ) : ProbComp (ZMod (2 ^ w)) :=
  ((↑) : ℕ → ZMod (2 ^ w)) <$> sampleBinaryNat w

/-- A uniform residue sample has the uniform finite-ring law modulo `2 ^ w`. -/
@[simp] theorem eval_sampleResidue (w : ℕ) :
    ProbComp.eval (sampleResidue w) = PMF.uniformOfFintype (ZMod (2 ^ w)) := by
  rw [sampleResidue, ProbComp.eval_map, eval_sampleBinaryNat, PMF.map_comp]
  let e : Fin (2 ^ w) ≃ ZMod (2 ^ w) :=
    { toFun := fun i => i.val
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := fun i => Fin.ext (ZMod.val_cast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  exact PMF.uniformOfFintype_map_equiv e

/-- Sample a uniformly random residue vector of length `count` modulo `2 ^ w`. -/
noncomputable def sampleVector (count w : ℕ) : ProbComp (Fin count → ZMod (2 ^ w)) :=
  OracleComp.replicateFin count (sampleResidue w)

/-- A uniform residue vector sample has the uniform product law modulo `2 ^ w`. -/
@[simp] theorem eval_sampleVector (count w : ℕ) :
    ProbComp.eval (sampleVector count w) =
      PMF.uniformOfFintype (Fin count → ZMod (2 ^ w)) := by
  simp only [sampleVector, ProbComp.eval_replicateFin, eval_sampleResidue,
    PMF.pi_uniformOfFintype]

/-- Sample a uniformly random `rows × cols` matrix modulo `2 ^ w`. -/
noncomputable def sampleMatrix (rows cols w : ℕ) :
    ProbComp (_root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) :=
  OracleComp.replicateFin rows (sampleVector cols w)

/-- A uniform matrix sample has the uniform finite-matrix law modulo `2 ^ w`. -/
@[simp] theorem eval_sampleMatrix (rows cols w : ℕ) :
    ProbComp.eval (sampleMatrix rows cols w) =
      PMF.uniformOfFintype (_root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) := by
  unfold _root_.Matrix
  simp only [sampleMatrix, ProbComp.eval_replicateFin, eval_sampleVector,
    PMF.pi_uniformOfFintype]
  congr 1

/-- The separately sampled secret, public-matrix part, and integer errors. -/
structure KeyInputs (n m w : ℕ) where
  /-- Uniform secret entries. -/
  secret : Fin n → ZMod (2 ^ w)
  /-- Uniform public matrix entries. -/
  publicPart : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w))
  /-- Independent bounded integer errors. -/
  error : Fin m → ℤ

/-- Draw the three inputs independently, using the specified finite centered-binomial error law. -/
noncomputable def sampleKeyInputs (n m w η : ℕ) : ProbComp (KeyInputs n m w) := do
  let secret ← sampleVector n w
  let publicPart ← sampleMatrix m n w
  let error ← OracleComp.replicateFin m (sampleCenteredBinomial η)
  return ⟨secret, publicPart, error⟩

/-- The complete joint law retains the independence of the secret, public part, and errors. -/
theorem eval_sampleKeyInputs (n m w η : ℕ) :
    ProbComp.eval (sampleKeyInputs n m w η) = (do
      let secret ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
      let publicPart ← PMF.uniformOfFintype (_root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
      let error ← ProbComp.eval (OracleComp.replicateFin m (sampleCenteredBinomial η))
      pure (KeyInputs.mk secret publicPart error)) := by
  simp only [pmf_norm, sampleKeyInputs, eval_sampleVector, eval_sampleMatrix]

/-- Every secret and public part is possible; the exact error restriction is coordinatewise. -/
theorem mem_support_sampleKeyInputs_iff (n m w η : ℕ) (inputs : KeyInputs n m w) :
    inputs ∈ (ProbComp.eval (sampleKeyInputs n m w η)).support ↔
      ∀ i, (inputs.error i).natAbs ≤ η := by
  cases inputs
  simp only [sampleKeyInputs, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleVector, eval_sampleMatrix, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  simp only [PMF.mem_support_uniformOfFintype, true_and, KeyInputs.mk.injEq,
    ProbComp.mem_support_replicateFin_iff, mem_support_sampleCenteredBinomial_iff]
  constructor
  · rintro ⟨_, _, error, herror, rfl, rfl, rfl⟩
    exact herror
  · intro herror
    exact ⟨_, _, _, herror, rfl, rfl, rfl⟩

/-- Generate an LWE public matrix `[B * t + e | B]` and retain the sampled secret `t`. -/
noncomputable def keyGen (n m w η : ℕ) :
    ProbComp (_root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))) := do
  let inputs ← sampleKeyInputs n m w η
  return (publicMatrixInt inputs.publicPart inputs.secret inputs.error, inputs.secret)

/-! ### Flat uniform tapes for key sampling -/

/-- A residue uses a uniform word of exactly its binary width. -/
theorem exists_uniform_seed_sampleResidue (w : ℕ) :
    ∃ evaluate : List Bool → ZMod (2 ^ w),
      ProbComp.eval (sampleResidue w) = (BitString.uniformList w).map evaluate := by
  refine ⟨fun bits => (BitString.binaryValue bits : ZMod (2 ^ w)), ?_⟩
  simp only [pmf_norm, sampleResidue, sampleBinaryNat, BitString.eval_sampleList]

/-- Independent residues use disjoint width-sized blocks. -/
theorem exists_uniform_seed_sampleVector (count w : ℕ) :
    ∃ evaluate : List Bool → Fin count → ZMod (2 ^ w),
      ProbComp.eval (sampleVector count w) =
        (BitString.uniformList (count * w)).map evaluate := by
  obtain ⟨evaluate, hlaw⟩ := exists_uniform_seed_sampleResidue w
  exact ⟨_, ProbComp.eval_replicateFin_of_uniformList count w _ evaluate hlaw⟩

/-- Independent rows use disjoint row-sized blocks. -/
theorem exists_uniform_seed_sampleMatrix (rows cols w : ℕ) :
    ∃ evaluate : List Bool → _root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)),
      ProbComp.eval (sampleMatrix rows cols w) =
        (BitString.uniformList (rows * (cols * w))).map evaluate := by
  obtain ⟨evaluate, hlaw⟩ := exists_uniform_seed_sampleVector cols w
  exact ⟨_, ProbComp.eval_replicateFin_of_uniformList rows (cols * w) _ evaluate hlaw⟩

/-- All key-generation inputs are independent functions of disjoint parts of one finite tape. -/
theorem exists_uniform_seed_sampleKeyInputs (n m w η : ℕ) :
    ∃ evaluate : List Bool → KeyInputs n m w,
      ProbComp.eval (sampleKeyInputs n m w η) =
        (BitString.uniformList (n * w + m * (n * w) + m * (2 * η))).map evaluate := by
  obtain ⟨secret, hsecret⟩ := exists_uniform_seed_sampleVector n w
  obtain ⟨publicPart, hpublicPart⟩ := exists_uniform_seed_sampleMatrix m n w
  have herror := ProbComp.eval_replicateFin_of_uniformList m (2 * η)
    (sampleCenteredBinomial η) _ (eval_sampleCenteredBinomial_eq_map η)
  have hrest (t : Fin n → ZMod (2 ^ w)) :=
    ProbComp.eval_bind_of_uniformList (m * (n * w)) (m * (2 * η))
      (sampleMatrix m n w)
      (fun B => KeyInputs.mk t B <$> OracleComp.replicateFin m (sampleCenteredBinomial η))
      publicPart _ hpublicPart (fun B => by rw [ProbComp.eval_map, herror, PMF.map_comp])
  have hfull := ProbComp.eval_bind_of_uniformList (n * w) (m * (n * w) + m * (2 * η))
    (sampleVector n w) _ secret _ hsecret hrest
  exact ⟨_, by simpa only [sampleKeyInputs, bind_pure_comp, Nat.add_assoc] using hfull⟩

/-! ### Serialized random inputs, key serialization, and Decision-LWE bridges -/

/-- Secret entries, public-matrix rows, and signed errors, without dependent dimensions. -/
@[ext]
structure SerializedKeyInputs where
  /-- List of secret vector residue representatives. -/
  secret : List ℕ
  /-- List of public-matrix rows (`m` rows of `n` residue representatives). -/
  publicPart : List (List ℕ)
  /-- List of signed integer errors. -/
  error : List ℤ
  deriving DecidableEq, Repr

/-- Binary residues and signed binary errors, with all list and pair framing. -/
enc_structure encSerializedKeyInputs : SerializedKeyInputs where
  secret : (encList encNat), publicPart : (encList (encList encNat)), error : (encList encIntBin)

attribute [fun_prop] encSerializedKeyInputs_secret_polyTime
  encSerializedKeyInputs_publicPart_polyTime encSerializedKeyInputs_error_polyTime
  encSerializedKeyInputs_mk_polyTime

/-- Independently sample every key-input entry using binary residues and signed errors. -/
noncomputable def sampleKeyInputsSerialized (n m w η : ℕ) : ProbComp SerializedKeyInputs := do
  let secret ← OracleComp.replicate n (sampleBinaryNat w)
  let publicPart ← OracleComp.replicate m (OracleComp.replicate n (sampleBinaryNat w))
  let error ← OracleComp.replicate m (sampleCenteredBinomial η)
  return { secret, publicPart, error }

/-- List every residue's canonical representative and every signed error in coordinate order. -/
def serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) : SerializedKeyInputs where
  secret := List.ofFn fun i => (inputs.secret i).val
  publicPart := List.ofFn fun i => List.ofFn fun j => (inputs.publicPart i j).val
  error := List.ofFn inputs.error

/-- Read fixed dimensions from arbitrary lists, padding absent entries with zero and reducing
natural representatives modulo `2 ^ w`. Excess entries are ignored. -/
def decodeKeyInputs (n m w : ℕ) (inputs : SerializedKeyInputs) : KeyInputs n m w :=
  ⟨fun i => (inputs.secret.getD i.val 0 : ZMod (2 ^ w)),
    fun i j => ((inputs.publicPart.getD i.val []).getD j.val 0 : ZMod (2 ^ w)),
    fun i => inputs.error.getD i.val 0⟩

/-- Canonical lists decode to their original typed key inputs, including empty dimensions. -/
@[simp] theorem decode_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    decodeKeyInputs n m w (serializeKeyInputs inputs) = inputs := by
  cases inputs
  simp only [decodeKeyInputs, serializeKeyInputs, List.getD_ofFn, ZMod.natCast_zmod_val]

/-- Sampling an unsigned `w`-bit integer gives the canonical residue representative law. -/
theorem eval_sampleBinaryNat_eq_map_val (w : ℕ) :
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
independence of the secret, public-matrix part, and signed errors. -/
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
  simp only [pmf_norm, sampleKeyInputsSerialized, hsecret, hpublicPart, herror,
    _root_.Matrix, serializeKeyInputs, id]

/-- Decoding the efficient sampled lists recovers the mathematical key-input sampler. -/
theorem eval_decodeKeyInputs_sampleKeyInputsSerialized (n m w η : ℕ) :
    ProbComp.eval (decodeKeyInputs n m w <$> sampleKeyInputsSerialized n m w η) =
      ProbComp.eval (sampleKeyInputs n m w η) := by
  rw [ProbComp.eval_map, eval_sampleKeyInputsSerialized, PMF.map_comp]
  simp only [Function.comp_def, decode_serializeKeyInputs]
  exact PMF.map_id _

/-- Canonical public matrices use the generic fixed-width row-major representation. -/
def serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) : List Bool :=
  Cslib.Matrix.toBinary A

/-- Canonical secret residues are consecutive low-order-first words. -/
def serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) : List Bool :=
  Cslib.Matrix.toBinary (fun _ : Fin 1 => secret)

/-- Total secret decoding reads the declared number of residue words, padding with zero bits. -/
def decodeSecret (n w : ℕ) (word : List Bool) : Fin n → ZMod (2 ^ w) :=
  Cslib.Matrix.ofBinary 1 n w word 0

/-- Canonical secret words retain every residue. -/
@[simp] theorem decode_serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) :
    decodeSecret n w (serializeSecret secret) = secret := by
  exact congrArg (fun A => A 0) (Cslib.Matrix.ofBinary_toBinary (fun _ : Fin 1 => secret))

/-- A serialized public matrix has exact bit length `m * (n + 1) * w`. -/
@[simp] theorem length_serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) :
    (serializePublicMatrix A).length = m * (n + 1) * w :=
  Cslib.Matrix.length_toBinary A

/-- A serialized secret vector has exact bit length `n * w`. -/
@[simp] theorem length_serializeSecret {n w : ℕ} (secret : Fin n → ZMod (2 ^ w)) :
    (serializeSecret secret).length = n * w := by
  simpa only [serializeSecret, Nat.one_mul] using
    Cslib.Matrix.length_toBinary (fun _ : Fin 1 => secret)

/-- Compute the leading entry `B * secret + error` of a public row in binary arithmetic. -/
def publicRowHead (n w : ℕ) (inputs : SerializedKeyInputs) (i : ℕ) : ℕ :=
  (((((List.range n).map fun j =>
    (inputs.publicPart.getD i []).getD j 0 * inputs.secret.getD j 0).sum : ℕ) +
      inputs.error.getD i 0 : ℤ) % (2 ^ w : ℤ)).toNat

/-- Compute the public word from arbitrary serialized sampled inputs. -/
def publicMatrixSerialized (n m w : ℕ) (inputs : SerializedKeyInputs) : List Bool :=
  (List.range m).flatMap fun i =>
    lowBits w (publicRowHead n w inputs i) ++
      (List.range n).flatMap fun j =>
        lowBits w ((inputs.publicPart.getD i []).getD j 0 % 2 ^ w)

/-- Normalize and serialize an arbitrary secret list to the declared dimensions. -/
def secretSerialized (n w : ℕ) (secret : List ℕ) : List Bool :=
  (List.range n).flatMap fun j => lowBits w (secret.getD j 0 % 2 ^ w)

/-- Sample random key inputs and run the actual serialized public-key computation. -/
noncomputable def keyGenSerialized (n m w η : ℕ) : ProbComp (List Bool × List Bool) := do
  let inputs ← sampleKeyInputsSerialized n m w η
  return (publicMatrixSerialized n m w inputs, secretSerialized n w inputs.secret)

/-- The binary signed-remainder computation returns the canonical leading public residue. -/
theorem publicRowHead_eq {n m w : ℕ} (inputs : SerializedKeyInputs) (i : Fin m) :
    publicRowHead n w inputs i.val =
      (publicMatrixInt (decodeKeyInputs n m w inputs).publicPart
        (decodeKeyInputs n m w inputs).secret (decodeKeyInputs n m w inputs).error i 0).val := by
  unfold publicRowHead publicMatrixInt publicMatrix decodeKeyInputs
  simp only [Fin.cons_zero, _root_.Matrix.mulVec, dotProduct]
  rw [List.map_range_eq_ofFn, List.sum_ofFn]
  have h : ((∑ j : Fin n,
      (inputs.publicPart.getD i.val []).getD j.val 0 * inputs.secret.getD j.val 0 : ℕ) :
        ZMod (2 ^ w)) =
      ∑ j : Fin n, ((inputs.publicPart.getD i.val []).getD j.val 0 : ZMod (2 ^ w)) *
        (inputs.secret.getD j.val 0 : ZMod (2 ^ w)) := by simp
  rw [← h]
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ w)
    (((∑ j : Fin n,
      (inputs.publicPart.getD i.val []).getD j.val 0 * inputs.secret.getD j.val 0 : ℕ) : ℤ) +
        inputs.error.getD i.val 0))
  simpa only [Int.toNat_natCast, Int.cast_add, Int.cast_natCast, Nat.cast_pow,
    Nat.cast_ofNat] using hv.symm

/-- The total public-key computation is exactly the typed public matrix of the decoded inputs. -/
theorem publicMatrixSerialized_eq (n m w : ℕ) (inputs : SerializedKeyInputs) :
    publicMatrixSerialized n m w inputs = serializePublicMatrix
      (publicMatrixInt (decodeKeyInputs n m w inputs).publicPart
        (decodeKeyInputs n m w inputs).secret (decodeKeyInputs n m w inputs).error) := by
  simp only [publicMatrixSerialized, serializePublicMatrix, Cslib.Matrix.toBinary_eq,
    List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [List.ofFn_succ]
  simp only [List.flatten_cons]
  congr 1
  · rw [publicRowHead_eq inputs i]
  · simp [publicMatrixInt, publicMatrix, decodeKeyInputs, ZMod.val_natCast]

/-- The total secret computation agrees with the same padded and modularly normalized inputs. -/
theorem secretSerialized_eq (n w : ℕ) (secret : List ℕ) :
    secretSerialized n w secret =
      serializeSecret (fun i : Fin n => (secret.getD i.val 0 : ZMod (2 ^ w))) := by
  unfold secretSerialized serializeSecret Cslib.Matrix.toBinary
  rw [ofFn_blocksEquiv_symm]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, ofFn_blocksEquiv_symm, List.flatMap_def, List.map_range_eq_ofFn,
    lowBits_eq_ofFn, ZMod.val_natCast]

/-- Canonical sampled inputs produce exactly the original typed public key. -/
theorem publicMatrixSerialized_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    publicMatrixSerialized n m w (serializeKeyInputs inputs) =
      serializePublicMatrix (publicMatrixInt inputs.publicPart inputs.secret inputs.error) := by
  rw [publicMatrixSerialized_eq, decode_serializeKeyInputs]

/-- Canonical sampled inputs produce exactly the original typed secret key. -/
theorem secretSerialized_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    secretSerialized n w (serializeKeyInputs inputs).secret = serializeSecret inputs.secret := by
  rw [secretSerialized_eq]
  congr 1 with i : 1
  simp [serializeKeyInputs]

/-- Every arbitrary input produces the complete declared public word. -/
theorem length_publicMatrixSerialized (n m w : ℕ) (inputs : SerializedKeyInputs) :
    (publicMatrixSerialized n m w inputs).length = m * (n + 1) * w := by
  simp [publicMatrixSerialized, List.length_flatMap, Nat.mul_add, Nat.add_mul,
    Nat.mul_assoc, Nat.add_comm]

/-- Secret normalization retains exactly the declared number of residue bits. -/
theorem length_secretSerialized (n w : ℕ) (secret : List ℕ) :
    (secretSerialized n w secret).length = n * w := by
  simp [secretSerialized, List.length_flatMap]

/-- The efficient key sampler retains the typed construction's complete public/secret joint law. -/
theorem eval_keyGenSerialized (n m w η : ℕ) :
    ProbComp.eval (keyGenSerialized n m w η) = (ProbComp.eval (keyGen n m w η)).map
      (fun keys => (serializePublicMatrix keys.1, serializeSecret keys.2)) := by
  simp only [pmf_norm, keyGenSerialized, keyGen, eval_sampleKeyInputsSerialized,
    publicMatrixSerialized_serializeKeyInputs, secretSerialized_serializeKeyInputs]

/-! ### Decision-LWE error law and public-word ensembles -/

/-- Reduce the difference of two independent `η`-bit counts modulo `2 ^ w`. -/
noncomputable def noiseLaw (w η : ℕ) : PMF (ZMod (2 ^ w)) :=
  (ProbComp.eval (sampleCenteredBinomial η)).map (fun error : ℤ => (error : ZMod (2 ^ w)))

/-- Reducing independent integer errors preserves the complete independent modular error law. -/
theorem eval_errorVector_mod (m w η : ℕ) :
    (ProbComp.eval (OracleComp.replicateFin m (sampleCenteredBinomial η))).map
      (fun error i => (error i : ZMod (2 ^ w))) =
        PMF.pi (fun _ : Fin m => noiseLaw w η) := by
  rw [← ProbComp.eval_replicateFin_map_coords, ProbComp.eval_replicateFin]
  simp only [noiseLaw, ProbComp.eval_map]

/-- The generated public matrix is an exact decision-LWE sample. -/
theorem eval_keyGen_publicMatrix (n m w η : ℕ) :
    (ProbComp.eval (keyGen n m w η)).map Prod.fst =
      publicMatrixLaw n m w (noiseLaw w η) := by
  simp only [pmf_norm, keyGen, eval_sampleKeyInputs, publicMatrixLaw]
  rw [← eval_errorVector_mod m w η]
  simp only [PMF.bind_map, Function.comp_def]
  rfl

/-- Encoding the actual public marginal gives the encoded real matrix `realEnsemble` of
`DecisionLWE` (`decisionLWE_iff_encoded`). -/
theorem eval_keyGen_publicWord (n m w η : ℕ → ℕ) (security : ℕ) :
    (ProbComp.eval (keyGen (n security) (m security) (w security) (η security))).map
      (fun keys => Cslib.Matrix.toBinary keys.1) =
        realEnsemble n m w (fun k => noiseLaw (w k) (η k)) security := by
  rw [realEnsemble, ← eval_keyGen_publicMatrix, PMF.map_comp]
  rfl

/-- The actual serialized key generator has precisely the public marginal `realEnsemble` of
`DecisionLWE`. -/
theorem eval_keyGenSerialized_publicWord (n m w η : ℕ → ℕ) (security : ℕ) :
    (ProbComp.eval
      (keyGenSerialized (n security) (m security) (w security) (η security))).map Prod.fst =
        realEnsemble n m w (fun k => noiseLaw (w k) (η k)) security := by
  rw [eval_keyGenSerialized, PMF.map_comp]
  exact eval_keyGen_publicWord n m w η security

/-! ### Uniform polynomial-time certificates for LWE key generation -/

section PolyTime

open Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n m w η i : α → ℕ}

/-- Uniform strict PPT generation of every serialized key input. -/
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
  unfold sampleKeyInputsSerialized
  ppt

/-- Compute a public row's leading residue from arbitrary binary inputs and signed errors. -/
@[fun_prop]
theorem computableInPolyTime_publicRowHead {inputs : α → SerializedKeyInputs}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => publicRowHead (n a) (w a) (inputs a) (i a))
      input encNat := by
  unfold publicRowHead
  have hrow := (listGetD (encA := encList encNat) []).comp
    ((encSerializedKeyInputs_publicPart_polyTime hinputs).prod hi)
  have hproduct : ComputableInPolyTime
      (fun p : α × ℕ => ((inputs p.1).publicPart.getD (i p.1) []).getD p.2 0 *
        (inputs p.1).secret.getD p.2 0) (encPair input encUnary) encNat := by
    apply binary_mul'
    · exact (listGetD (encA := encNat) 0).comp
        ((hrow.comp (fst input encUnary)).prod (snd input encUnary))
    · exact (listGetD (encA := encNat) 0).comp
        (((encSerializedKeyInputs_secret_polyTime hinputs).comp
          (fst input encUnary)).prod (snd input encUnary))
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a j => ((inputs a).publicPart.getD (i a) []).getD j 0 *
        (inputs a).secret.getD j 0)
      (range.comp hn) hproduct)
  have herror := (listGetD (encA := encIntBin) 0).comp
    ((encSerializedKeyInputs_error_polyTime hinputs).prod hi)
  have hadd := (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin by fun_prop).comp
      ((intBin_natCast.comp hsum).prod herror)
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    intBin_emodNat' hadd (binary_pow' (const 2) hw)

/-- Construct the entire public word, charging the runtime number and width of every entry. -/
@[fun_prop]
theorem computableInPolyTime_publicMatrixSerialized {inputs : α → SerializedKeyInputs}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs) :
    ComputableInPolyTime
      (fun a => publicMatrixSerialized (n a) (m a) (w a) (inputs a)) input encBits := by
  unfold publicMatrixSerialized
  apply flatMapToBitsWithInput (range.comp hm)
  apply bitsAppend
  · fun_prop
  · apply flatMapToBitsWithInput (range.comp (hn.comp (fst input encUnary)))
    apply bitsLow (by fun_prop)
    have hrow := (listGetD (encA := encList encNat) []).comp
      (((encSerializedKeyInputs_publicPart_polyTime hinputs).comp
        (fst input encUnary)).prod (snd input encUnary))
    have hentry := (listGetD (encA := encNat) 0).comp
      ((hrow.comp (fst (encPair input encUnary) encUnary)).prod
        (snd (encPair input encUnary) encUnary))
    exact binary_mod.comp (hentry.prod (binary_pow' (const 2) (by fun_prop)))

/-- Normalize and write the declared number of binary secret coordinates. -/
@[fun_prop]
theorem computableInPolyTime_secretSerialized {secret : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecret : ComputableInPolyTime secret input (encList encNat)) :
    ComputableInPolyTime (fun a => secretSerialized (n a) (w a) (secret a))
      input encBits := by
  unfold secretSerialized
  apply flatMapToBitsWithInput (range.comp hn)
  apply bitsLow (hw.comp (fst input encUnary))
  have hentry := (listGetD (encA := encNat) 0).comp
    ((hsecret.comp (fst input encUnary)).prod (snd input encUnary))
  exact binary_mod.comp (hentry.prod (binary_pow' (const 2) (hw.comp (fst input encUnary))))

/-- The complete key generator is strict PPT for arbitrary efficient runtime dimensions. -/
@[fun_prop]
theorem isPPTOn_keyGenSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hη : ComputableInPolyTime η input encUnary) :
    IsPPTOn input (encPair encBits encBits)
      (fun a => keyGenSerialized (n a) (m a) (w a) (η a)) := by
  have hsample := isPPTOn_sampleKeyInputsSerialized hn hm hw hη
  unfold keyGenSerialized
  ppt

end PolyTime

end Cslib.Crypto.LWE
