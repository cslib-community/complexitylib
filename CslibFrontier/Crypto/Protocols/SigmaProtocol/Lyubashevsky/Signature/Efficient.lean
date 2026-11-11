/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature
public import CslibFrontier.Computability.Interactive.Security.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Tactic.PolyTime

/-!
# Efficient bounded signing with aborts

The native signer uses binary integer matrices, unary dimensions and sampling width, and an
explicit polynomial attempt budget. Each attempt samples the existing approximate uniform box,
computes its commitment, hashes the message and commitment, and tests the shifted response
against the inner box. Short matrix rows and challenge words are padded with zero.

The hash is a deterministic function on encoded message/commitment pairs. Its polynomial-time
certificate is an input to the signing efficiency theorem; this module makes no random-oracle
security claim. The comparison with the exact signer includes the abort outcome. Its distance
is at most `K * m * (2γ + 1) / 2^width`. The failure bound keeps the exact single-attempt
abort probability:
a commitment-dependent hash need not have the abort probability of a fixed interactive challenge.
These implementation and approximation lemmas are original formalization results.

## Main definitions

* `encLyubashevskySignWithRandomness`: the encoding of a signing input with its commitment
  randomness.
* `lyubashevskySignPostprocess`: native deterministic signing from a candidate random vector.
* `lyubashevskySignAttemptNative`: one strict fair-bit signing attempt.
* `lyubashevskySignBoundedNative`: a unary-budget bounded signing program.

## Main results

* `isPPTOn_lyubashevskySignBoundedNative`: actual machine-backed uniform strict-PPT efficiency.
* `closeTo_lyubashevskySignBoundedNative`: comparison with the exact bounded signer.
* `lyubashevskySignBoundedNative_none_le`: quantitative failure bound.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Mathlib.Tactic.Matrix

open Probability Probability.PMF Turing.MultiTapeTM Interactive
open scoped ENNReal _root_.Matrix

/-- Native signing input: parameters, secret integer rows, public matrix rows, message bits. -/
abbrev LyubashevskySignInput :=
  LyubashevskyParams × List (List ℤ) × List (List ℤ) × List Bool

/-- Matrix entries are binary; dimensions and sampling width retain the parameter encoding. -/
@[expose] def encLyubashevskySignInput : LyubashevskySignInput ↪ List Bool :=
  encPair encLyubashevskyParams
    (encPair (encList (encList encIntBin)) (encPair (encList (encList encIntBin)) encBits))

/-- Input `(input, y)` of the native commitment, with the commitment randomness `y` in binary: the
signing input encoded by `encLyubashevskySignInput`, then `y : List ℤ` as a list of binary
integers. The signing postprocessing takes the same input, and the native response takes it paired
with the challenge bits. The signing input is framed, and so is each integer. -/
abbrev encLyubashevskySignWithRandomness : LyubashevskySignInput × List ℤ ↪ List Bool :=
  encPair encLyubashevskySignInput (encList encIntBin)

/-- Native commitment from public matrix rows and commitment randomness. -/
def lyubashevskySignCommitment
    (input : LyubashevskySignInput × List ℤ) : List Bool :=
  let ((p, _, matrix, _), randomness) := input
  encList encIntBin ((List.range p.n).map fun i =>
    zmodReduce p.q (ListMatrix.dotProduct p.m (matrix.getD i []) randomness))

/-- Native shifted response from secret rows, commitment randomness and raw challenge bits. -/
def lyubashevskySignResponse
    (input : (LyubashevskySignInput × List ℤ) × List Bool) : List ℤ :=
  let (((p, secret, _, _), randomness), challenge) := input
  (List.range p.m).map fun i =>
    randomness.getD i 0 +
      ListMatrix.dotProduct p.k (secret.getD i []) (challengeIntList p.k challenge)

/-- Compute the commitment and shifted response, retaining exactly the inner-box responses.
A short hash result is padded with false bits, and excess bits are ignored. -/
def lyubashevskySignPostprocess (hash : List Bool × List Bool → List Bool)
    (input : LyubashevskySignInput × List ℤ) : Option (List Bool × List Bool) :=
  let ((p, _, _, msg), _) := input
  let commitment := lyubashevskySignCommitment input
  let response := lyubashevskySignResponse (input, hash (msg, commitment))
  if inBoxList p.m (p.γ - p.β) response then
    some (commitment, encList encIntBin response)
  else none

/-- Polynomial-time computation of the native commitment. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySignCommitment :
    ComputableInPolyTime lyubashevskySignCommitment
      encLyubashevskySignWithRandomness encBits := by
  unfold lyubashevskySignCommitment encLyubashevskySignWithRandomness encLyubashevskySignInput
    encLyubashevskyParams LyubashevskyParams.n LyubashevskyParams.m LyubashevskyParams.q
  fun_prop

/-- Polynomial-time computation of the native response. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySignResponse :
    ComputableInPolyTime lyubashevskySignResponse
      (encPair encLyubashevskySignWithRandomness encBits)
      (encList encIntBin) := by
  unfold lyubashevskySignResponse encLyubashevskySignWithRandomness encLyubashevskySignInput
    encLyubashevskyParams LyubashevskyParams.m LyubashevskyParams.k
  fun_prop

/-- The actual signing postprocessing is polynomial-time for a polynomial-time hash. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySignPostprocess
    {hash : List Bool × List Bool → List Bool}
    (hhash : ComputableInPolyTime hash (encPair encBits encBits) encBits) :
    ComputableInPolyTime (lyubashevskySignPostprocess hash)
      encLyubashevskySignWithRandomness encCommitResponseOrAbort := by
  let e := encPair encLyubashevskySignInput (encList encIntBin)
  have hw := computableInPolyTime_lyubashevskySignCommitment
  have hmsg : ComputableInPolyTime (fun x : LyubashevskySignInput × List ℤ => x.1.2.2.2)
      e encBits := by
    unfold e encLyubashevskySignInput
    fun_prop
  have hh := hhash.comp (hmsg.prod hw)
  have hz := computableInPolyTime_lyubashevskySignResponse.comp
    ((ComputableInPolyTime.id').prod hh)
  have hm : ComputableInPolyTime (fun x : LyubashevskySignInput × List ℤ => x.1.1.m)
      e encUnary := by
    unfold e encLyubashevskySignInput encLyubashevskyParams LyubashevskyParams.m
    fun_prop
  have hb : ComputableInPolyTime
      (fun x : LyubashevskySignInput × List ℤ => x.1.1.γ - x.1.1.β) e encNat := by
    unfold e encLyubashevskySignInput encLyubashevskyParams
      LyubashevskyParams.γ LyubashevskyParams.β
    fun_prop
  have hc := computableInPolyTime_inBoxList.comp (hm.prod (hb.prod hz))
  exact hc.ite' ((ComputableInPolyTime.optionSome (encPair encBits encBits)).comp
    (hw.prod hz.encoding_comp))
    (ComputableInPolyTime.const none)

/-- One native signing attempt, with `m * width` independent fair bits. -/
noncomputable def lyubashevskySignAttemptNative (hash : List Bool × List Bool → List Bool)
    (input : LyubashevskySignInput) : ProbComp (Option (List Bool × List Bool)) :=
  let (p, _, _, _) := input
  (fun r => lyubashevskySignPostprocess hash (input, r)) <$>
    sampleIntBoxList p.γ p.m p.width

/-- Uniform strict-PPT efficiency of the signing attempt, including its failure result. -/
theorem isPPTOn_lyubashevskySignAttemptNative
    {hash : List Bool × List Bool → List Bool}
    (hhash : ComputableInPolyTime hash (encPair encBits encBits) encBits) :
    IsPPTOn encLyubashevskySignInput encCommitResponseOrAbort
      (lyubashevskySignAttemptNative hash) := by
  have hγ : ComputableInPolyTime (fun x : LyubashevskySignInput => x.1.γ)
      encLyubashevskySignInput encNat := by
    unfold LyubashevskyParams.γ encLyubashevskySignInput encLyubashevskyParams
    fun_prop
  have hm : ComputableInPolyTime (fun x : LyubashevskySignInput => x.1.m)
      encLyubashevskySignInput encUnary := by
    unfold LyubashevskyParams.m encLyubashevskySignInput encLyubashevskyParams
    fun_prop
  have hw : ComputableInPolyTime (fun x : LyubashevskySignInput => x.1.width)
      encLyubashevskySignInput encUnary := by
    unfold LyubashevskyParams.width encLyubashevskySignInput encLyubashevskyParams
    fun_prop
  exact (isPPTOn_sampleIntBoxList hγ hm hw).map_with
    (computableInPolyTime_lyubashevskySignPostprocess hhash)

/-- Canonical native input for a typed secret and public matrix. The public `T = A S` matrix
is not needed by signing. -/
def lyubashevskySignInput (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (A : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (msg : List Bool) :
    LyubashevskySignInput :=
  (p, List.ofFn fun i => List.ofFn (S i),
    List.ofFn fun i => List.ofFn fun j => ZMod.cast (A i j), msg)

/-- The typed challenge function actually implemented by the native hash call. -/
def lyubashevskyNativeHash (hash : List Bool × List Bool → List Bool)
    (p : LyubashevskyParams) (query : List Bool × (Fin p.n → ZMod p.q)) : BitString p.k :=
  fun i => (hash (query.1, encZModVec p.n p.q query.2)).getD i.val false

/-- Serialize a typed signature; the outer `none` is preserved. -/
def lyubashevskySignatureWords (p : LyubashevskyParams)
    (sig : Option ((Fin p.n → ZMod p.q) × (Fin p.m → ℤ))) :
    Option (List Bool × List Bool) :=
  sig.map fun (w, z) => (encZModVec p.n p.q w, encList encIntBin (List.ofFn z))

/-- Commitment computation agrees with the typed matrix product on canonical inputs. -/
theorem lyubashevskySignCommitment_ofFn (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (A : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (msg : List Bool) (r : Fin p.m → ℤ) :
    lyubashevskySignCommitment (lyubashevskySignInput p S A msg, List.ofFn r) =
      encZModVec p.n p.q (A *ᵥ (Int.cast ∘ r)) := by
  change encList encIntBin _ = encList encIntBin _
  apply congrArg (encList encIntBin)
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, zmodReduce_eq_cast,
    ListMatrix.intCast_dotProduct_matrix_ofFn A r i]

/-- Response computation agrees with the typed integer matrix product on canonical inputs. -/
theorem lyubashevskySignResponse_ofFn (p : LyubashevskyParams)
    (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (A : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (msg : List Bool) (r : Fin p.m → ℤ)
    (challenge : List Bool) :
    lyubashevskySignResponse ((lyubashevskySignInput p S A msg, List.ofFn r), challenge) =
      List.ofFn (r + S *ᵥ lyubashevskyChallenge
        (fun i : Fin p.k => challenge.getD i.val false)) := by
  have hc : challengeIntList p.k challenge = List.ofFn
      (lyubashevskyChallenge (fun i : Fin p.k => challenge.getD i.val false)) := by
    unfold challengeIntList lyubashevskyChallenge
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    rfl
  dsimp only [lyubashevskySignResponse, lyubashevskySignInput]
  rw [hc, ← List.map_coe_finRange_eq_range, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, ↓reduceDIte, Option.getD_some]
  rw [ListMatrix.dotProduct_ofFn]
  rfl

/-- Native postprocessing has exactly the deterministic signing-step semantics. -/
theorem lyubashevskySignPostprocess_ofFn (hash : List Bool × List Bool → List Bool)
    (p : LyubashevskyParams) (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (msg : List Bool) (r : Fin p.m → ℤ) :
    lyubashevskySignPostprocess hash (lyubashevskySignInput p S y.1 msg, List.ofFn r) =
      lyubashevskySignatureWords p
        (fsAbortSignStep (lyubashevskyFamily p) (lyubashevskyNativeHash hash p) S y msg
          (y.1 *ᵥ (Int.cast ∘ r), r)) := by
  change (if inBoxList p.m (p.γ - p.β)
    (lyubashevskySignResponse ((lyubashevskySignInput p S y.1 msg, List.ofFn r),
      hash (msg, lyubashevskySignCommitment (lyubashevskySignInput p S y.1 msg, List.ofFn r))))
    then some (lyubashevskySignCommitment (lyubashevskySignInput p S y.1 msg, List.ofFn r),
      encList encIntBin (lyubashevskySignResponse
        ((lyubashevskySignInput p S y.1 msg, List.ofFn r),
          hash (msg, lyubashevskySignCommitment (lyubashevskySignInput p S y.1 msg, List.ofFn r)))))
    else none) = _
  rw [lyubashevskySignCommitment_ofFn, lyubashevskySignResponse_ofFn, inBoxList_ofFn]
  simp only [decide_eq_true_eq]
  split_ifs <;> simp only [lyubashevskySignatureWords, fsAbortSignStep, lyubashevskyFamily,
    lyubashevsky] <;> split_ifs <;> first | rfl | contradiction

/-- One native attempt approximates the exact signing law, preserving rejection and aborts. -/
theorem closeTo_lyubashevskySignAttemptNative (hash : List Bool × List Bool → List Bool)
    (p : LyubashevskyParams) (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (msg : List Bool) :
    CloseTo
      ((lyubashevskySignAttempt p.n p.m p.k p.q p.γ p.β
        (lyubashevskyNativeHash hash p) S y msg).map (lyubashevskySignatureWords p))
      (ProbComp.eval (lyubashevskySignAttemptNative hash (lyubashevskySignInput p S y.1 msg)))
      ((p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) := by
  let post (r : Fin p.m → ℤ) :=
    lyubashevskySignPostprocess hash (lyubashevskySignInput p S y.1 msg, List.ofFn r)
  have hideal :
      (lyubashevskySignAttempt p.n p.m p.k p.q p.γ p.β
        (lyubashevskyNativeHash hash p) S y msg).map (lyubashevskySignatureWords p) =
      (PMF.uniformOfFinset (intBox (Fin p.m) p.γ) (intBox_nonempty p.γ)).map post := by
    simp only [lyubashevskySignAttempt, fsAbortSignAttempt, lyubashevsky, PMF.map_comp]
    congr 1 with r : 1
    exact (lyubashevskySignPostprocess_ofFn hash p S y msg r).symm
  have hreal :
      ProbComp.eval (lyubashevskySignAttemptNative hash (lyubashevskySignInput p S y.1 msg)) =
      (ProbComp.eval (sampleIntBoxVec p.γ p.m p.width)).map post := by
    have hlist : ProbComp.eval (sampleIntBoxList p.γ p.m p.width) =
        (ProbComp.eval (sampleIntBoxVec p.γ p.m p.width)).map List.ofFn := by
      rw [eval_sampleIntBoxVec_eq_iid, sampleIntBoxList, ProbComp.eval_replicate_iid]
    change ProbComp.eval
      ((fun r => lyubashevskySignPostprocess hash (lyubashevskySignInput p S y.1 msg, r)) <$>
        sampleIntBoxList p.γ p.m p.width) = _
    rw [ProbComp.eval_map, hlist, PMF.map_comp]
    rfl
  rw [hideal, hreal]
  exact (closeTo_uniform_intBox_sampleIntBoxVec p.γ p.m p.width).map post

/-- Sample every attempt and return the first successful signature. Charging the entire list
makes the deterministic attempt budget explicit even after an early success. -/
noncomputable def lyubashevskySignBoundedNative (hash : List Bool × List Bool → List Bool)
    (input : LyubashevskySignInput × ℕ) : ProbComp (Option (List Bool × List Bool)) :=
  (fun attempts => (attempts.find? Option.isSome).getD none) <$>
    OracleComp.replicate input.2 (lyubashevskySignAttemptNative hash input.1)

/-- The bounded signer is uniformly strict PPT when its attempt budget is unary. -/
theorem isPPTOn_lyubashevskySignBoundedNative
    {hash : List Bool × List Bool → List Bool}
    (hhash : ComputableInPolyTime hash (encPair encBits encBits) encBits) :
    IsPPTOn (encPair encLyubashevskySignInput encUnary)
      encCommitResponseOrAbort (lyubashevskySignBoundedNative hash) := by
  have hattempt := (isPPTOn_lyubashevskySignAttemptNative hhash).preprocess
    (ComputableInPolyTime.fst encLyubashevskySignInput encUnary)
  apply (hattempt.replicate (ComputableInPolyTime.snd _ _)).map
  have hfind : ComputableInPolyTime
      (fun attempts : List (Option (List Bool × List Bool)) => attempts.find? Option.isSome)
      (encList (encOption (encPair encBits encBits)))
      (encOption (encOption (encPair encBits encBits))) := by
    fun_prop
  exact hfind.optionGetDWithInput (ComputableInPolyTime.const none)

/-- `K` native attempts differ from the exact bounded signing law by at most `K` times the
one-attempt box-sampling error. No signature or abort outcome is conditioned away. -/
theorem closeTo_lyubashevskySignBoundedNative (hash : List Bool × List Bool → List Bool)
    (p : LyubashevskyParams) (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (msg : List Bool) (K : ℕ) :
    CloseTo
      ((lyubashevskySignBounded p.n p.m p.k p.q p.γ p.β
        (lyubashevskyNativeHash hash p) K S y msg).map (lyubashevskySignatureWords p))
      (ProbComp.eval (lyubashevskySignBoundedNative hash
        (lyubashevskySignInput p S y.1 msg, K)))
      ((K : ℝ≥0∞) * ((p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width))) := by
  have h := CloseTo.iid_replicate
    (prog := lyubashevskySignAttemptNative hash (lyubashevskySignInput p S y.1 msg))
    (closeTo_lyubashevskySignAttemptNative hash p S y msg) K
  have hm := h.map (fun attempts => (attempts.find? Option.isSome).getD none)
  rw [lyubashevskySignBoundedNative, ProbComp.eval_map]
  unfold lyubashevskySignBounded lyubashevskySignatureWords
  rw [fsAbortSignBounded_map_eq_iid]
  unfold lyubashevskySignatureWords lyubashevskySignAttempt at hm
  simpa only [PMF.map_comp, Function.comp_def] using hm

/-- The real signer's failure probability is bounded by exact all-attempt rejection plus the
explicit fair-bit sampling error. The hash may depend on the commitment. -/
theorem lyubashevskySignBoundedNative_none_le (hash : List Bool × List Bool → List Bool)
    (p : LyubashevskyParams) (S : Matrix (Fin p.m) (Fin p.k) ℤ)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q))
    (msg : List Bool) (K : ℕ) :
    ProbComp.eval (lyubashevskySignBoundedNative hash
        (lyubashevskySignInput p S y.1 msg, K)) none ≤
      (lyubashevskySignAttempt p.n p.m p.k p.q p.γ p.β
        (lyubashevskyNativeHash hash p) S y msg none) ^ K +
      (K : ℝ≥0∞) * ((p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) := by
  have h := (closeTo_lyubashevskySignBoundedNative hash p S y msg K).symm {none}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at h
  have hpre : (lyubashevskySignatureWords p) ⁻¹' {none} = {none} := by
    ext sig
    cases sig <;> simp [lyubashevskySignatureWords]
  rw [hpre, PMF.toOuterMeasure_apply_singleton, lyubashevskySignBounded_apply_none] at h
  exact h

end Cslib.Crypto.Protocols.SigmaProtocol
