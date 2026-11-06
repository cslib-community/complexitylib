/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.Encryption.KEMFromPKE.CCA
public import ComplexityTests.Crypto.HybridEncryption
import Complexity.Tactic.PPT
import Complexity.Probability.PMF.Bind

/-!
# Adaptive encrypted-key KEM regressions

Exercise the actual CCA endpoint at doubled key length, an unconditional correct zero-width
instance, and a native oracle adversary exploiting a ciphertext tag ignored by decapsulation.
The attack queries a distinct ciphertext word; semantic equivalence does not trigger freshness
rejection. The honest fixture and adversary both have native machine certificates.
-/

public section

namespace ComplexityTests.Crypto.KEMFromPKECCA

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.Crypto.HybridEncryption
open scoped NNReal

/-- The nonidentity schedule uses the actual CCA assumption and existing security predicates. -/
example (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    (hsecure : WordINDCCA2 keyGen encrypt decrypt) :
    Game.Indistinguishable
      (fun D n => ProbComp.eval (kemCCARealGame keyGen
        (encryptKeyEncaps (fun n => 2 * n) encrypt) decrypt D n))
      (fun D n => ProbComp.eval (kemCCAIdealGame (fun n => 2 * n) keyGen
        (encryptKeyEncaps (fun n => 2 * n) encrypt) decrypt D n)) (IsOraclePPT encBool) :=
  hsecure.indistinguishable_encryptKeyEncaps (by fun_prop)

/-- The negative fixture needs no secret key. -/
def tagKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [])

theorem tagKeyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) tagKeyGen :=
  (ComputableInPolyTime.const ([], [])).isPPTOn

/-- A redundant tag is prepended to the ciphertext. This fixture is correct but insecure. -/
def tagEncrypt (_ : ℕ) (_ : List Bool) (m : List Bool) : ProbComp (List Bool) :=
  pure (false :: m)

/-- Either tag decodes the same message; an empty ciphertext is rejected. -/
def tagDecrypt (_ : ℕ) (_ : List Bool) (ct : List Bool) : Option (List Bool) :=
  if ct.isEmpty then none else some ct.tail

/-- Query the flipped tag and compare its bounded reply to the shown key. Reading at most
`shownKey.length + 1` bits gives a strict oracle-PPT adversary even for arbitrarily long replies. -/
def tagDistinguisher : OracleDistinguisher := fun _ input => do
  let key := unframe (dropFrame input)
  let ct := dropFrame (dropFrame input)
  let reply ← List.take (key.length + 1) <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), true :: ct.tail)
  return reply == true :: key

theorem tagDistinguisher_ppt : IsOraclePPT encBool tagDistinguisher := by
  have hquery : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => List.take ((unframe (dropFrame p.2)).length + 1) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), true :: (dropFrame (dropFrame p.2)).tail)) :=
    IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)
  exact (hquery.map_with' (f := fun p reply => reply == true :: unframe (dropFrame p.2))
    (by fun_prop)).isOraclePPT

/-- The second query is chosen only after observing rejection of the first, challenge query. -/
def adaptiveTagDistinguisher : OracleDistinguisher := fun n input => do
  let reply ← List.take 1 <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), dropFrame (dropFrame input))
  if reply.isEmpty then tagDistinguisher n input else pure false

theorem adaptiveTagDistinguisher_ppt : IsOraclePPT encBool adaptiveTagDistinguisher := by
  have hfirst : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), dropFrame (dropFrame p.2))) :=
    IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)
  apply IsOraclePPTOn.isOraclePPT
  exact hfirst.bind_with (IsOraclePPTOn.cond' (by fun_prop)
    (tagDistinguisher_ppt.on.preprocess' (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.const false).isPPTOn.isOraclePPTOn)

private theorem eval_adaptiveContinuation (n : ℕ) (sk pk k ct : List Bool) :
    ProbComp.eval (kemCCAContinuation tagDecrypt adaptiveTagDistinguisher n sk pk k ct) =
      ProbComp.eval (kemCCAContinuation tagDecrypt tagDistinguisher n sk pk k ct) := by
  simp only [kemCCAContinuation, adaptiveTagDistinguisher, encPair_apply, encBits_apply,
    dropFrame_frame_append]
  simp only [OracleComp.interpret_bind, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map]
  simp [StateT.run, cca2Phase2Oracle]

theorem tagEncrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun p => tagEncrypt p.1 p.2.1 p.2.2) := by
  unfold tagEncrypt
  ppt

theorem tagDecrypt_polytime : ComputableInPolyTime
    (fun p => tagDecrypt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  unfold tagDecrypt
  fun_prop

example : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => encryptKeyEncaps (fun n => 2 * n) tagEncrypt p.1 p.2) :=
  isPPTOn_encryptKeyEncaps (by fun_prop) tagEncrypt_ppt

example : (kemToCCAAdversary (fun n => 2 * n) tagDistinguisher).IsPPT encBits :=
  isPPT_kemToCCAAdversary (by fun_prop) tagDistinguisher_ppt

example : IsPPTOn encUnary encBool
      (kemCCARealGame tagKeyGen (encryptKeyEncaps (fun n => 2 * n) tagEncrypt)
        tagDecrypt tagDistinguisher) ∧
    IsPPTOn encUnary encBool
      (kemCCAIdealGame (fun n => 2 * n) tagKeyGen
        (encryptKeyEncaps (fun n => 2 * n) tagEncrypt) tagDecrypt tagDistinguisher) :=
  isPPTOn_kemCCAGames_encryptKeyEncaps (by fun_prop) tagKeyGen_ppt
    tagEncrypt_ppt tagDecrypt_polytime tagDistinguisher_ppt

/-- The option-valued correctness theorem applies to the actual encrypted-key constructor. -/
example (keyLen : ℕ → ℕ) (n : ℕ) (pk sk k ct : List Bool)
    (h : (k, ct) ∈ (ProbComp.eval (encryptKeyEncaps keyLen tagEncrypt n pk)).support) :
    tagDecrypt n sk ct = some k := by
  apply decrypt_encryptKeyEncaps_some tagDecrypt (fun m c _ hc => ?_) h
  simp only [tagEncrypt, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hc
  subst c
  simp [tagDecrypt]

/-- Exact challenge words and malformed empty ciphertexts reject, while a distinct tag returns
`some []`, whose encoded reply is nonempty. -/
example (n : ℕ) :
    cca2Phase2Oracle encBits tagDecrypt n [] [false] ((), [false]) () = pure ([], ()) ∧
    cca2Phase2Oracle encBits tagDecrypt n [] [false] ((), []) () = pure ([], ()) ∧
    cca2Phase2Oracle encBits tagDecrypt n [] [false] ((), [true]) () = pure ([true], ()) := by
  simp [cca2Phase2Oracle, tagDecrypt, encOption, encBits_apply]

/-- At zero width the actual correct encrypted-key fixture has identical real and ideal
oracle games for every adversary, including arbitrary adaptive query sequences. -/
theorem eval_zero_width (D : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (kemCCARealGame tagKeyGen
      (encryptKeyEncaps (fun _ => 0) tagEncrypt) tagDecrypt D n) =
    ProbComp.eval (kemCCAIdealGame (fun _ => 0) tagKeyGen
      (encryptKeyEncaps (fun _ => 0) tagEncrypt) tagDecrypt D n) := by
  simp [kemCCARealGame, kemCCAIdealGame, kemIdealGameWith, kemRealGameWith,
    encryptKeyEncaps, BitString.sampleList, tagKeyGen, tagEncrypt]

example : Game.Indistinguishable
    (fun D n => ProbComp.eval (kemCCARealGame tagKeyGen
      (encryptKeyEncaps (fun _ => 0) tagEncrypt) tagDecrypt D n))
    (fun D n => ProbComp.eval (kemCCAIdealGame (fun _ => 0) tagKeyGen
      (encryptKeyEncaps (fun _ => 0) tagEncrypt) tagDecrypt D n)) (IsOraclePPT encBool) := by
  intro D _
  simpa only [eval_zero_width, Game.advantage_self] using negligible_zero

private theorem eval_tagContinuation (n : ℕ) (k shown : List Bool)
    (hlen : k.length = shown.length) :
    ProbComp.eval (kemCCAContinuation tagDecrypt tagDistinguisher n [] [] shown (false :: k)) =
      PMF.pure (decide (shown = k)) := by
  simp only [kemCCAContinuation, tagDistinguisher, encPair_apply, encBits_apply,
    unframe_frame_append, dropFrame_frame_append, List.tail_cons]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure, StateT.run_map]
  simp [StateT.run, cca2Phase2Oracle, tagDecrypt, encOption, ← hlen, Bool.beq_eq_decide_eq, eq_comm]

/-- The flipped-tag query recovers the real key with certainty. -/
theorem eval_tagReal (keyLen : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (kemCCARealGame tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
      tagDecrypt tagDistinguisher n) = PMF.pure true := by
  simp only [kemCCARealGame, kemRealGameWith, tagKeyGen, encryptKeyEncaps, tagEncrypt,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.bind_bind, PMF.pure_bind]
  simp [eval_tagContinuation, PMF.bind_const]

private theorem eval_tagIdeal (keyLen : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (kemCCAIdealGame keyLen tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
      tagDecrypt tagDistinguisher n) =
    ((BitString.uniformList (keyLen n)).bind fun k =>
      (BitString.uniformList (keyLen n)).bind fun shown => PMF.pure (decide (shown = k))) := by
  simp only [kemCCAIdealGame, kemIdealGameWith, kemRealGameWith, tagKeyGen,
    encryptKeyEncaps, tagEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  refine PMF.bind_congr_on_support _ _ _ fun shown hshown => ?_
  exact eval_tagContinuation n k shown
    ((BitString.length_of_mem_support_uniformList hk).trans
      (BitString.length_of_mem_support_uniformList hshown).symm)

/-- In the ideal world the recovered key equals the independently shown key with probability
`2^(-keyLen n)`. -/
theorem eval_tagIdeal_true (keyLen : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (kemCCAIdealGame keyLen tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
      tagDecrypt tagDistinguisher n) true = (2 ^ keyLen n)⁻¹ := by
  rw [eval_tagIdeal, PMF.bind_apply]
  calc
    _ = ∑' k, BitString.uniformList (keyLen n) k * (2 ^ keyLen n)⁻¹ := by
      refine tsum_congr fun k => ?_
      by_cases hk : k ∈ (BitString.uniformList (keyLen n)).support
      · rw [uniformList_bind_decide_eq_apply_true
          (BitString.length_of_mem_support_uniformList hk)]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
    _ = (2 ^ keyLen n)⁻¹ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Exact nonzero attack advantage for the correct but malleable encrypted-key fixture. -/
theorem advantage_tag (keyLen : ℕ → ℕ) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemCCARealGame tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
        tagDecrypt tagDistinguisher n))
      (ProbComp.eval (kemCCAIdealGame keyLen tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
        tagDecrypt tagDistinguisher n)) = 1 - (2 ^ keyLen n)⁻¹ := by
  have hle : ((2 : ℝ≥0) ^ keyLen n)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  rw [Game.advantage, Game.succProbability, Game.succProbability, eval_tagReal,
    eval_tagIdeal_true, PMF.pure_apply_self, ENNReal.toNNReal_one, ENNReal.toNNReal_inv,
    ENNReal.toNNReal_pow, ENNReal.toNNReal_ofNat, NNReal.nndist_eq,
    tsub_eq_zero_of_le hle, max_eq_left zero_le]

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemCCARealGame tagKeyGen (encryptKeyEncaps (fun _ => 1) tagEncrypt)
        tagDecrypt tagDistinguisher n))
      (ProbComp.eval (kemCCAIdealGame (fun _ => 1) tagKeyGen
        (encryptKeyEncaps (fun _ => 1) tagEncrypt) tagDecrypt tagDistinguisher n)) = 1 / 2 := by
  rw [advantage_tag,
    tsub_eq_iff_eq_add_of_le (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))]
  norm_num

/-- The reply-dependent two-query adversary has the same exact attack advantage. Its first
query receives rejection, and its fresh flipped-tag query then obtains the encapsulated key. -/
example (keyLen : ℕ → ℕ) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemCCARealGame tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
        tagDecrypt adaptiveTagDistinguisher n))
      (ProbComp.eval (kemCCAIdealGame keyLen tagKeyGen (encryptKeyEncaps keyLen tagEncrypt)
        tagDecrypt adaptiveTagDistinguisher n)) = 1 - (2 ^ keyLen n)⁻¹ := by
  simpa only [kemCCARealGame, kemCCAIdealGame, kemRealGameWith, kemIdealGameWith,
    ProbComp.eval_bind, eval_adaptiveContinuation] using advantage_tag keyLen n

end ComplexityTests.Crypto.KEMFromPKECCA
