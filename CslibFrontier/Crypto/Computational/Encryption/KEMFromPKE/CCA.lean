/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.KEMFromPKE
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid.CCA
import CslibFrontier.Probability.PMF.Bind

/-!
# CCA security of encrypted-key encapsulation

The encrypted-key KEM of [BonehShoup2023], Exercise 12.5(f), has exactly the advantage of an
explicit adversary in the existing equal-length PKE CCA experiment. The reduction samples two
independent keys, retains the first, and forwards the KEM adversary's adaptive decapsulation
queries unchanged. Both experiments reject the exact challenge word and preserve `Option`
replies, including the distinction between `none` and `some []`.

Only postchallenge KEM queries are claimed. The source PKE notion permits queries in both
phases; this reduction uses zero queries in its first phase. Correctness and honest algorithm
efficiency are separate from indistinguishability. The security parameter remains `n`, while
the sampled keys have length `keyLen n`, including length zero.

## Main definitions

* `Cslib.Crypto.Encryption.kemToCCAAdversary`: the exact-loss reduction.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_kemCCAGames_encryptKeyEncaps`: native closed games.
* `Cslib.Crypto.Encryption.decrypt_encryptKeyEncaps_some`: supported-output correctness.
* `Cslib.Crypto.Encryption.isPPT_kemToCCAAdversary`: native oracle runtime certificate.
* `Cslib.Crypto.Encryption.advantage_encryptKeyEncaps_cca_eq`: exact advantage preservation.
* `Cslib.Crypto.Encryption.WordINDCCA2.indistinguishable_encryptKeyEncaps`:
  CCA-secure PKE gives a KEM secure against adaptive decapsulation queries.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.5(f), p. 514.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The CPA reduction's chosen-message sampler, followed by the oracle distinguisher with all
its decapsulation queries forwarded unchanged. The first stage makes no external query. -/
noncomputable def kemToCCAAdversary (keyLen : ℕ → ℕ)
    (distinguisher : OracleDistinguisher) : CCA2AdversaryOf (List Bool) where
  choose n pk := ProbOracleComp.sample (kemToPKEChoose keyLen n pk)
  guess n state ct := distinguisher n
    (encPair encBits (encPair encBits encBits) (unframe state, (dropFrame state, ct)))

/-- The source PKE experiment's prechallenge oracle is unused by this reduction. -/
theorem kemToCCAAdversary_choose_isQueryBounded (keyLen : ℕ → ℕ)
    (distinguisher : OracleDistinguisher) (n : ℕ) (pk : List Bool) :
    ((kemToCCAAdversary keyLen distinguisher).choose n pk).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample _

/-- Native uniform strict oracle PPT for the reduction. The key-length computation is charged
in unary; the reduction does not execute key generation, encryption or decryption. -/
theorem isPPT_kemToCCAAdversary {keyLen : ℕ → ℕ} {distinguisher : OracleDistinguisher}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hdist : IsOraclePPT encBool distinguisher) :
    (kemToCCAAdversary keyLen distinguisher).IsPPT encBits := by
  refine ⟨(isPPTOn_kemToPKEChoose hkeyLen).isOraclePPTOn.isOraclePPT, ?_⟩
  let hg1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hg2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  exact hdist.on.preprocess'
    (hg1.prod (((ComputableInPolyTime.unframe.comp' hg2.fst').prod
      ((ComputableInPolyTime.dropFrame.comp' hg2.fst').prod hg2.snd')).encoding_comp))

private theorem eval_cca2GameOn_kemToCCAAdversary (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (cca2GameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      encBits keyGen encrypt decrypt (kemToCCAAdversary keyLen distinguisher) bit n) =
      (do
        let keys ← ProbComp.eval (keyGen n)
        let k₀ ← BitString.uniformList (keyLen n)
        let k₁ ← BitString.uniformList (keyLen n)
        let ct ← ProbComp.eval (encrypt n keys.1 (if bit then k₁ else k₀))
        ProbComp.eval (kemCCAContinuation decrypt distinguisher n keys.2 keys.1 k₀ ct)) := by
  simp only [cca2GameOn, kemToCCAAdversary, kemToPKEChoose, kemCCAContinuation,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.run_interpret_sample, BitString.eval_sampleList, PMF.bind_map,
    PMF.bind_bind, PMF.pure_bind, PMF.monad_bind_eq_bind, Function.comp_def,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, encPair_apply, encBits_apply,
    apply_ite ProbComp.eval]
  congr 1; funext keys
  refine PMF.bind_congr_on_support _ _ _ fun k₀ hk₀ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun k₁ hk₁ => ?_
  simp [BitString.length_of_mem_support_uniformList hk₀,
    BitString.length_of_mem_support_uniformList hk₁]

/-- The first chosen-message CCA experiment is the real KEM experiment, including all adaptive
decapsulation replies. -/
theorem eval_cca2GameOn_kemToCCAAdversary_false (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (cca2GameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      encBits keyGen encrypt decrypt (kemToCCAAdversary keyLen distinguisher) false n) =
      ProbComp.eval (kemCCARealGame keyGen (encryptKeyEncaps keyLen encrypt)
        decrypt distinguisher n) := by
  rw [eval_cca2GameOn_kemToCCAAdversary]
  simp [kemCCARealGame, kemRealGameWith, encryptKeyEncaps, ProbComp.eval_bind,
    BitString.eval_sampleList, PMF.bind_const]

/-- The second chosen-message CCA experiment is the ideal KEM experiment. The same secret key
and ciphertext determine the oracle while the retained key is independent of the encrypted key. -/
theorem eval_cca2GameOn_kemToCCAAdversary_true (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (cca2GameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      encBits keyGen encrypt decrypt (kemToCCAAdversary keyLen distinguisher) true n) =
      ProbComp.eval (kemCCAIdealGame keyLen keyGen (encryptKeyEncaps keyLen encrypt)
        decrypt distinguisher n) := by
  rw [eval_cca2GameOn_kemToCCAAdversary]
  simp only [kemCCAIdealGame, kemIdealGameWith, kemRealGameWith, encryptKeyEncaps,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.bind_bind, PMF.pure_bind, PMF.monad_bind_eq_bind, ↓reduceIte]
  congr 1; funext keys
  rw [PMF.bind_comm]
  congr 1; funext k
  rw [PMF.bind_comm]

/-- Exact loss one in the existing adaptive CCA experiment. There is no correctness premise
and no error term: the reduction preserves both output distributions. -/
theorem advantage_encryptKeyEncaps_cca_eq (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemCCARealGame keyGen (encryptKeyEncaps keyLen encrypt)
        decrypt distinguisher n))
      (ProbComp.eval (kemCCAIdealGame keyLen keyGen (encryptKeyEncaps keyLen encrypt)
        decrypt distinguisher n)) =
    Encryption.advantage (cca2GameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits keyGen
      encrypt decrypt (kemToCCAAdversary keyLen distinguisher)) n := by
  rw [advantage, eval_cca2GameOn_kemToCCAAdversary_false, eval_cca2GameOn_kemToCCAAdversary_true]

/-- **CCA-secure word PKE gives adaptive decapsulation security** ([BonehShoup2023],
Exercise 12.5(f)). The KEM adversary receives one challenge and may query adaptively afterwards;
the security assertion uses the existing indistinguishability and native oracle PPT predicates. -/
theorem WordINDCCA2.indistinguishable_encryptKeyEncaps {keyLen : ℕ → ℕ}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hsecure : WordINDCCA2 keyGen encrypt decrypt)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    Game.Indistinguishable
      (fun D n => ProbComp.eval (kemCCARealGame keyGen
        (encryptKeyEncaps keyLen encrypt) decrypt D n))
      (fun D n => ProbComp.eval (kemCCAIdealGame keyLen keyGen
        (encryptKeyEncaps keyLen encrypt) decrypt D n)) (IsOraclePPT encBool) := by
  intro distinguisher hdist
  simpa only [advantage_encryptKeyEncaps_cca_eq] using
    hsecure (kemToCCAAdversary keyLen distinguisher)
      (isPPT_kemToCCAAdversary hkeyLen hdist)

/-- Both closed KEM experiments have native strict-PPT realizations when the honest algorithms
and the adversary do. The exact game equalities reuse the existing finite-machine certificates
for the complete CCA experiment, including the cost of answering adaptive oracle requests. -/
theorem isPPTOn_kemCCAGames_encryptKeyEncaps {keyLen : ℕ → ℕ}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    {distinguisher : OracleDistinguisher}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime (fun p => decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hdist : IsOraclePPT encBool distinguisher) :
    IsPPTOn encUnary encBool
      (kemCCARealGame keyGen (encryptKeyEncaps keyLen encrypt) decrypt distinguisher) ∧
    IsPPTOn encUnary encBool
      (kemCCAIdealGame keyLen keyGen (encryptKeyEncaps keyLen encrypt) decrypt distinguisher) := by
  have hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.1.length == p.2.2.2.length)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool := by fun_prop
  have hgame := isPPTOn_cca2GameOn
    (valid := fun _ _ (m₀ m₁ : List Bool) => m₀.length == m₁.length)
    hvalid hkeyGen hencrypt hdecrypt
    (isPPT_kemToCCAAdversary hkeyLen hdist)
  exact ⟨(hgame false).congr (fun n => eval_cca2GameOn_kemToCCAAdversary_false _ _ _ _ _ n),
    (hgame true).congr (fun n => eval_cca2GameOn_kemToCCAAdversary_true _ _ _ _ _ n)⟩

/-- Supported encrypted keys decrypt to `some key`; invalid ciphertexts may still return
`none`. In particular successful decapsulation of an empty key is not rejection. -/
theorem decrypt_encryptKeyEncaps_some {keyLen : ℕ → ℕ}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool))
    {n : ℕ} {pk sk k ct : List Bool}
    (hcorrect : ∀ m c, m.length = keyLen n →
      c ∈ (ProbComp.eval (encrypt n pk m)).support → decrypt n sk c = some m)
    (h : (k, ct) ∈ (ProbComp.eval (encryptKeyEncaps keyLen encrypt n pk)).support) :
    decrypt n sk ct = some k := by
  simp only [encryptKeyEncaps, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨k', hk, ct', hct, heq⟩ := h
  cases heq
  exact hcorrect _ _ (BitString.length_of_mem_support_uniformList hk) hct

end Cslib.Crypto.Encryption
