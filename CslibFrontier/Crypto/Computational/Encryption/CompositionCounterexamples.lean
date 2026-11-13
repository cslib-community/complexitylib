/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Generic Composition Counterexamples for Authenticated Encryption

This module formalizes the generic composition separations and counterexamples of
[Katz and Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020], Chapter 5.
They are stated in terms of fresh-message encryption unforgeability (`SymmetricCipher.EncForge`),
which is defined, with its positive results, in
`CslibFrontier/Crypto/Computational/Encryption/EncForge.lean`.

1. **Separation of `INDCPA ∧ EncForge` from `INDCCA` and `CiphertextIntegrity`
   (`SymmetricCipher.tailFallback`, `INDCPA.tailFallback`, `EncForge.tailFallback`,
   `not_ciphertextIntegrity_tailFallback`, `not_indcca_tailFallback`)**
   ([KatzLindell2020], Exercise 5.10, printed p. 165): for any `E : SymmetricCipher`,
   `E.tailFallback` keeps `keyGen` and `encrypt` unchanged and modifies `decrypt n k ct` to fall
   back to `E.decrypt n k ct.tail` whenever `E.decrypt n k ct = none` and `!ct.isEmpty`. This
   preserves `INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
   `OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (by prepending `false` to a queried
   ciphertext) and breaking `OneTimeINDCCA` and `INDCCA` whenever `E.EncForge` holds.
2. **Encrypt-then-MAC under a non-strong MAC (`MACScheme.redundantTag`, `EUFCMA.redundantTag`,
   `not_sufCma_redundantTag`, `not_indcca_encryptThenMAC_redundantTag`,
   `encryptThenMAC_redundantTag_counterexample`)** ([KatzLindell2020], Exercise 5.4, printed
   p. 164): for any `M : MACScheme`, `M.redundantTag` keeps `keyGen`, `msgLen`, and `sign`
   unchanged while accepting either `M.verify sk msg tag` or `!tag.isEmpty && M.verify sk msg
   tag.tail`. This preserves `EUFCMA` and `OneTimeEUFCMA` while breaking `OneTimeSUFCMA` and
   `SUFCMA`; when combined with any cipher `E` via `encryptThenMAC E M.redundantTag hctLen`, the
   resulting cipher satisfies `INDCPA` and `EncForge` (under `E.INDCPA` and `M.EUFCMA`) yet fails
   `OneTimeCiphertextIntegrity` and `CiphertextIntegrity` with adversary advantage `1`, and
   `OneTimeINDCCA` and `INDCCA` with advantage `1` for every `n ≥ 1`.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.tailFallback`, `tailCIAdversary`, `prependFalseBitCIAdversary`,
  `tailFallbackCCAAdversary`: Exercise 5.10 ciphertext-tail fallback transformation and reductions /
  attackers ([KatzLindell2020], Exercise 5.10).
* `Cslib.Crypto.MACScheme.redundantTag`, `tailTagForger`, `redundantTagForger`,
  `etmRedundantCIAdversary`, `etmRedundantCCAAdversary`: Exercise 5.4 redundant-tag MAC
  transformation and reductions / attackers ([KatzLindell2020], Exercise 5.4).

## Main results

* `Cslib.Crypto.SymmetricCipher.INDCPA.tailFallback`,
  `Cslib.Crypto.SymmetricCipher.EncForge.tailFallback`,
  `Cslib.Crypto.SymmetricCipher.not_ciphertextIntegrity_tailFallback`,
  `Cslib.Crypto.SymmetricCipher.not_indcca_tailFallback`,
  `Cslib.Crypto.SymmetricCipher.tailFallback_counterexample`: Exercise 5.10
  separation of `INDCPA ∧ EncForge` from `INDCCA` and `CiphertextIntegrity`.
* `Cslib.Crypto.MACScheme.EUFCMA.redundantTag`,
  `Cslib.Crypto.MACScheme.not_sufCma_redundantTag`,
  `Cslib.Crypto.not_ciphertextIntegrity_encryptThenMAC_redundantTag`,
  `Cslib.Crypto.not_indcca_encryptThenMAC_redundantTag`,
  `Cslib.Crypto.encryptThenMAC_redundantTag_counterexample`: Exercise 5.4 counterexample to
  Encrypt-then-MAC CCA security under a non-strong MAC.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Exercises 5.4 and 5.10 (pp. 164–165).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 9.1 and 9.4.1 (pp. 358–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

private theorem succProbability_bind_pure_bool_le {α : Type} (p : PMF α) (f g : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g a))) := by
  unfold Game.succProbability
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) (Probability.PMF.map_true_mono p hfg)

private theorem succProbability_bind_pure_bool_le_add {α : Type} (p : PMF α) (f g₁ g₂ : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g₁ a = true ∨ g₂ a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g₁ a))) +
        Game.succProbability (p.bind (fun a => PMF.pure (g₂ a))) := by
  unfold Game.succProbability
  rw [← ENNReal.toNNReal_add (PMF.apply_ne_top _ true) (PMF.apply_ne_top _ true)]
  exact ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ true, PMF.apply_ne_top _ true⟩)
    (Probability.PMF.map_true_le_add p hfg)

/-! ### Katz–Lindell Exercise 5.10: `INDCPA ∧ EncForge` Does Not Imply `INDCCA`

Given any symmetric cipher `E`, `E.tailFallback` has the same `keyGen` and `encrypt` as `E`, and
decrypts `ct` by returning `E.decrypt n k ct` when it is `some msg`, or falling back to
`E.decrypt n k ct.tail` when `ct` is non-empty and `E.decrypt n k ct = none`. This preserves
`INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
`OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (and breaking `OneTimeINDCCA` and `INDCCA`
whenever `E.EncForge` holds, by querying decryption on `false :: ct`). -/

namespace SymmetricCipher

/-- Modified symmetric cipher `E.tailFallback` ([KatzLindell2020], Exercise 5.10, printed p. 165):
`keyGen` and `encrypt` are identical to `E`, while `decrypt n k ct` returns `E.decrypt n k ct`
whenever that succeeds and otherwise falls back to `E.decrypt n k ct.tail` on non-empty `ct`. -/
noncomputable def tailFallback (E : SymmetricCipher) : SymmetricCipher where
  keyGen := E.keyGen
  encrypt := E.encrypt
  decrypt n k ct :=
    if (E.decrypt n k ct).isSome then
      E.decrypt n k ct
    else if ct.isEmpty then
      none
    else
      E.decrypt n k ct.tail
  keyGen_ppt := E.keyGen_ppt
  encrypt_ppt := E.encrypt_ppt
  decrypt_polyTime := by
    let EIn := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) EIn encUnary := by
      dsimp only [EIn]; fun_prop
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.1) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hctTail :
        ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2.tail) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hdec1 := E.computableInPolyTime_decrypt_comp hn hk hct
    have hdec2 := E.computableInPolyTime_decrypt_comp hn hk hctTail
    have hisSome : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (E.decrypt p.1 p.2.1 p.2.2).isSome) EIn encBool :=
      .of_tidy hdec1.tidy.optionIsSome
    have hisEmpty : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.2.2.isEmpty) EIn encBool := by
      dsimp only [EIn]; fun_prop
    exact ComputableInPolyTime.ite hisSome hdec1
      (ComputableInPolyTime.ite hisEmpty (ComputableInPolyTime.const none) hdec2)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp [E.decrypt_encrypt n k hk msg hmsg ct hct]

/-- `E.tailFallback` has the exact same `cpaGame` as `E`. -/
@[simp]
theorem cpaGame_tailFallback (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) :
    E.tailFallback.cpaGame adversary bit n = E.cpaGame adversary bit n :=
  rfl

/-- `E.tailFallback` has the exact same `cpaOneTimeGame` as `E`. -/
@[simp]
theorem cpaOneTimeGame_tailFallback (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) :
    E.tailFallback.cpaOneTimeGame adversary bit n = E.cpaOneTimeGame adversary bit n :=
  rfl

/-- `tailFallback` preserves `INDCPA` ([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem INDCPA.tailFallback {E : SymmetricCipher} (h : E.INDCPA) :
    E.tailFallback.INDCPA :=
  h

/-- `tailFallback` preserves `OneTimeINDCPA`. -/
theorem OneTimeINDCPA.tailFallback {E : SymmetricCipher} (h : E.OneTimeINDCPA) :
    E.tailFallback.OneTimeINDCPA :=
  h

/-- Reduction adversary that runs `adversary` and drops the leading bit of its candidate
ciphertext (`List.tail`). -/
def tailCIAdversary (adversary : CIAdversary) : CIAdversary :=
  fun n aux => List.tail <$> adversary n aux

/-- `tailCIAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_tailCIAdversary {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (tailCIAdversary adversary) :=
  (hadversary.on.map' (by fun_prop)).isOraclePPT

/-- `tailCIAdversary` preserves any per-input query-count bound `IsQueryBounded Q`. -/
theorem isQueryBounded_tailCIAdversary (adversary : CIAdversary) (n : ℕ) (aux : List Bool)
    {Q : ℕ} (hq : (adversary n aux).IsQueryBounded Q) :
    (tailCIAdversary adversary n aux).IsQueryBounded Q := by
  simpa only [tailCIAdversary, OracleComp.isCostBounded_map_iff] using hq

/-- **Quantitative `EncForge` bound for `E.tailFallback`** ([KatzLindell2020], Exercise 5.10,
printed p. 165): any fresh-message forgery against `E.tailFallback` either already succeeds
directly against `E` on `ct` or succeeds against `E` on `ct.tail` via `tailCIAdversary`. -/
theorem succProbability_encForgeGame_tailFallback_le (E : SymmetricCipher)
    (adversary : CIAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval (E.tailFallback.encForgeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (E.encForgeGame adversary n)) +
        Game.succProbability
          (ProbComp.eval (E.encForgeGame (tailCIAdversary adversary) n)) := by
  have horacle (k : List Bool) :
      E.tailFallback.encForgeOracle n k = E.encForgeOracle n k := rfl
  have hkeyGen : E.tailFallback.keyGen = E.keyGen := rfl
  let runDist : PMF (List Bool × List Bool × List (List Bool)) :=
    (ProbComp.eval (E.keyGen n)).bind fun k =>
      (ProbOracleComp.runWith (fun req s => ProbComp.eval (E.encForgeOracle n k req s))
        (adversary n []) []).map fun out => (k, out)
  have hfb :
      ProbComp.eval (E.tailFallback.encForgeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((E.tailFallback.decrypt n p.1 p.2.1).isSome &&
            !p.2.2.contains ((E.tailFallback.decrypt n p.1 p.2.1).getD []))) := by
    simp only [encForgeGame, hkeyGen, horacle, runDist, runWith_norm, pmf_norm]
  have hdir :
      ProbComp.eval (E.encForgeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((E.decrypt n p.1 p.2.1).isSome &&
            !p.2.2.contains ((E.decrypt n p.1 p.2.1).getD []))) := by
    simp only [encForgeGame, runDist, runWith_norm, pmf_norm]
  have htail :
      ProbComp.eval (E.encForgeGame (tailCIAdversary adversary) n) =
        runDist.bind (fun p => PMF.pure
          ((E.decrypt n p.1 p.2.1.tail).isSome &&
            !p.2.2.contains ((E.decrypt n p.1 p.2.1.tail).getD []))) := by
    simp only [encForgeGame, tailCIAdversary, runDist, runWith_norm, pmf_norm]
  rw [hfb, hdir, htail]
  refine succProbability_bind_pure_bool_le_add runDist _ _ _ fun p _ hwin => ?_
  dsimp only [tailFallback] at hwin
  split_ifs at hwin with h1 h2
  · exact Or.inl hwin
  · simp at hwin
  · exact Or.inr hwin

/-- `tailFallback` preserves `EncForge` ([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem EncForge.tailFallback {E : SymmetricCipher} (h : E.EncForge) :
    E.tailFallback.EncForge := by
  refine EncForge.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailCIAdversary adversary) (isOraclePPT_tailCIAdversary hadversary)
  negligible using E.succProbability_encForgeGame_tailFallback_le adversary

/-- One-query ciphertext-integrity / `EncForge` adversary that queries encryption on `bit^n`
(truncating the reply to `ctBound n`) and prepends `false` to the returned ciphertext. -/
def prependFalseBitCIAdversary (bit : Bool) (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n bit)
    return (false :: ct)

/-- `prependFalseBitCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_prependFalseBitCIAdversary (bit : Bool) {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (prependFalseBitCIAdversary bit ctBound) := by
  have hreq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 bit)
      (encPair encUnary encBits) encBits := by fun_prop
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1)
      (encPair encUnary encBits) encUnary := hctBound.comp (by fun_prop)
  have hout : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => false :: p.2)
      (encPair (encPair encUnary encBits) encBits) encBits := by fun_prop
  unfold prependFalseBitCIAdversary
  exact ((IsOraclePPTOn.query_take' () hreq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

private theorem decrypt_tailFallback_false_cons_isSome (E : SymmetricCipher) (n : ℕ)
    (k msg ct : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support) (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) :
    (E.tailFallback.decrypt n k (false :: ct)).isSome = true := by
  dsimp only [tailFallback]
  split_ifs with h1 h2
  · exact h1
  · simp at h2
  · simp [E.decrypt_encrypt n k hk msg hmsg ct hct]

private theorem singleton_contains_false_cons (ct : List Bool) :
    ([ct].contains (false :: ct)) = false := by
  rw [Bool.eq_false_iff]
  intro hmem
  have heq : false :: ct = ct := by
    simpa using List.contains_iff_mem.mp hmem
  have hlen := congrArg List.length heq
  simp at hlen

/-- In `ciOneTimeGame` against `E.tailFallback`, `prependFalseBitCIAdversary bit ctBound` wins
with probability `1` at every security parameter `n` where `ctBound n` bounds ciphertext lengths. -/
theorem eval_ciOneTimeGame_tailFallback_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval
      (E.tailFallback.ciOneTimeGame (prependFalseBitCIAdversary bit ctBound) n) =
        PMF.pure true := by
  simp only [ciOneTimeGame, prependFalseBitCIAdversary, oneTimeCIEncryptionOracle,
    List.isEmpty_nil, List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct),
    singleton_contains_false_cons,
    decrypt_tailFallback_false_cons_isSome E n k _ ct hk List.length_replicate hct]
  rfl

/-- In `ciGame` against `E.tailFallback`, `prependFalseBitCIAdversary bit ctBound` wins with
probability `1` at every security parameter `n` where `ctBound n` bounds ciphertext lengths. -/
theorem eval_ciGame_tailFallback_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval
      (E.tailFallback.ciGame (prependFalseBitCIAdversary bit ctBound) n) =
        PMF.pure true := by
  simp only [ciGame, prependFalseBitCIAdversary, ciEncryptionOracle,
    List.length_replicate, beq_self_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct),
    singleton_contains_false_cons,
    decrypt_tailFallback_false_cons_isSome E n k _ ct hk List.length_replicate hct]
  rfl

/-- `E.tailFallback` never satisfies `OneTimeCiphertextIntegrity` ([KatzLindell2020],
Exercise 5.10, printed p. 165). -/
theorem not_oneTimeCiphertextIntegrity_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.OneTimeCiphertextIntegrity := by
  intro hci
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := hci.negligible (prependFalseBitCIAdversary false ctBound)
    (isOraclePPT_prependFalseBitCIAdversary false hctBoundPoly)
  have heq : (fun n => Game.succProbability
      (ProbComp.eval
        (E.tailFallback.ciOneTimeGame (prependFalseBitCIAdversary false ctBound) n))) =
      fun _ => (1 : ℝ≥0) := by
    funext n
    rw [eval_ciOneTimeGame_tailFallback_prependFalseBitCIAdversary E false ctBound n (hctBound n)]
    simp [Game.succProbability]
  rw [heq] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `E.tailFallback` never satisfies `CiphertextIntegrity` ([KatzLindell2020], Exercise 5.10,
printed p. 165). -/
theorem not_ciphertextIntegrity_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.CiphertextIntegrity :=
  fun h => not_oneTimeCiphertextIntegrity_tailFallback E h.oneTimeCiphertextIntegrity

/-- `E.tailFallback` never satisfies `OneTimeAuthenticatedEncryption`. -/
theorem not_oneTimeAuthenticatedEncryption_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.OneTimeAuthenticatedEncryption :=
  fun h => not_oneTimeCiphertextIntegrity_tailFallback E h.2

/-- `E.tailFallback` never satisfies `AuthenticatedEncryption`. -/
theorem not_authenticatedEncryption_tailFallback (E : SymmetricCipher) :
    ¬ E.tailFallback.AuthenticatedEncryption :=
  fun h => not_ciphertextIntegrity_tailFallback E h.2

/-- Two-query CCA adversary against `E.tailFallback` ([KatzLindell2020], Exercise 5.10,
printed p. 165): queries left-or-right encryption on `(0^n, 1^n)` to obtain `ct`, queries
decryption on `false :: ct`, and outputs whether the decrypted message equals `some 1^n`. -/
def tailFallbackCCAAdversary (ctBound : ℕ → ℕ) : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$>
      ProbOracleComp.query (true, false :: ct)
    return (reply == encOption encBits (some m1))

/-- `tailFallbackCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_tailFallbackCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (tailFallbackCCAAdversary ctBound) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encBits
  let E2 := encPair E1 encBits
  have hreq1 : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 true))
      E0 encBits := by
    dsimp only [E0]; fun_prop
  have hlim1 : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1) E0 encUnary :=
    hctBound.comp (by dsimp only [E0]; fun_prop)
  have hreq2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => false :: p.2) E1 encBits := by
    dsimp only [E1, E0]; fun_prop
  have hlim2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => p.1.1 + 1) E1 encUnary := by
    dsimp only [E1, E0]; fun_prop
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool =>
        p.2 == encOption encBits (some (List.replicate p.1.1.1 true)))
      E2 encBool := by
    dsimp only [E2, E1, E0]; fun_prop
  unfold tailFallbackCCAAdversary
  exact ((IsOraclePPTOn.query_take' false hreq1 hlim1).bind_with
    ((IsOraclePPTOn.query_take' true hreq2 hlim2).bind_with hout.isOraclePPTOn)).isOraclePPT

private theorem eval_encForgeGame_prependFalseBitCIAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary bit ctBound) n) =
      ((ProbComp.eval (E.keyGen n)).bind fun k =>
        (ProbComp.eval (E.encrypt n k (List.replicate n bit))).map fun ct => (k, ct)).bind
          (fun p => PMF.pure
            ((E.decrypt n p.1 (false :: p.2)).isSome &&
              !([List.replicate n bit].contains ((E.decrypt n p.1 (false :: p.2)).getD [])))) := by
  simp only [encForgeGame, prependFalseBitCIAdversary, encForgeOracle,
    List.length_replicate, beq_self_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  peel_binds k ct
  rw [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem)]

private theorem eval_ccaOneTimeGame_tailFallback_tailFallbackCCAAdversary (E : SymmetricCipher)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) bit n) =
      ((ProbComp.eval (E.keyGen n)).bind fun k =>
        (ProbComp.eval (E.encrypt n k (List.replicate n bit))).map fun ct => (k, ct)).bind
          (fun p => PMF.pure
            (List.take (n + 1)
              (encOption encBits (E.tailFallback.decrypt n p.1 (false :: p.2))) ==
                encOption encBits (some (List.replicate n true)))) := by
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by
    cases bit <;> rfl
  have hkeyGen : E.tailFallback.keyGen = E.keyGen := rfl
  have henc : E.tailFallback.encrypt = E.encrypt := rfl
  simp only [ccaOneTimeGame, tailFallbackCCAAdversary, oneTimeCCAOracle, hkeyGen, henc,
    unframe_encPair_encBits, dropFrame_encPair_encBits, hbit, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  peel_binds k ct
  simp [List.take_of_length_le (hctBound k k_mem _ List.length_replicate ct ct_mem)]

private theorem replicate_false_ne_replicate_true {n : ℕ} (hn : 1 ≤ n) :
    List.replicate n false ≠ List.replicate n true := by
  cases n with
  | zero => contradiction
  | succ m => simp

private theorem take_encOption_some_replicate (n : ℕ) (b : Bool) :
    List.take (n + 1) (encOption encBits (some (List.replicate n b))) =
      encOption encBits (some (List.replicate n b)) := by
  apply List.take_of_length_le
  simp [encOption_some, encBits_apply]

private theorem encOption_some_replicate_false_beq_true {n : ℕ} (hn : 1 ≤ n) :
    (encOption encBits (some (List.replicate n false)) ==
      encOption encBits (some (List.replicate n true))) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have heq := (encOption encBits).injective (beq_iff_eq.mp h)
  exact replicate_false_ne_replicate_true hn (Option.some.inj heq)

private theorem one_le_succProbability_ccaOneTimeGame_tailFallback_true (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval
          (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n)) +
      Game.succProbability
        (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary true ctBound) n)) := by
  let dist : PMF (List Bool × List Bool) :=
    (ProbComp.eval (E.keyGen n)).bind fun k =>
      (ProbComp.eval (E.encrypt n k (List.replicate n true))).map fun ct => (k, ct)
  have h1 : (1 : ℝ≥0) = Game.succProbability (dist.bind fun _ => PMF.pure true) := by
    simp [Game.succProbability]
  rw [h1,
    eval_ccaOneTimeGame_tailFallback_tailFallbackCCAAdversary E true ctBound n hctBound,
    eval_encForgeGame_prependFalseBitCIAdversary E true ctBound n hctBound]
  refine succProbability_bind_pure_bool_le_add dist _ _ _ fun p hp _ => ?_
  simp only [dist, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hp
  obtain ⟨k, hk, ct, hct, hpEq⟩ := hp
  subst hpEq
  have hdecCt : E.decrypt n k ct = some (List.replicate n true) :=
    E.decrypt_encrypt n k hk (List.replicate n true) List.length_replicate ct hct
  cases hdec : E.decrypt n k (false :: ct) with
  | none =>
    left
    have hfb : E.tailFallback.decrypt n k (false :: ct) = some (List.replicate n true) := by
      simp [tailFallback, hdec, hdecCt]
    rw [hfb, take_encOption_some_replicate, beq_self_eq_true]
  | some msg =>
    by_cases hmsg : msg = List.replicate n true
    · left
      subst hmsg
      have hfb : E.tailFallback.decrypt n k (false :: ct) = some (List.replicate n true) := by
        simp [tailFallback, hdec]
      rw [hfb, take_encOption_some_replicate, beq_self_eq_true]
    · right
      simp [hmsg]

private theorem succProbability_ccaOneTimeGame_tailFallback_false_le (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    Game.succProbability
      (ProbComp.eval
        (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n)) ≤
    Game.succProbability
      (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary false ctBound) n)) := by
  let dist : PMF (List Bool × List Bool) :=
    (ProbComp.eval (E.keyGen n)).bind fun k =>
      (ProbComp.eval (E.encrypt n k (List.replicate n false))).map fun ct => (k, ct)
  rw [eval_ccaOneTimeGame_tailFallback_tailFallbackCCAAdversary E false ctBound n hctBound,
    eval_encForgeGame_prependFalseBitCIAdversary E false ctBound n hctBound]
  refine succProbability_bind_pure_bool_le dist _ _ fun p hp hwin => ?_
  simp only [dist, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hp
  obtain ⟨k, hk, ct, hct, hpEq⟩ := hp
  subst hpEq
  have hdecCt : E.decrypt n k ct = some (List.replicate n false) :=
    E.decrypt_encrypt n k hk (List.replicate n false) List.length_replicate ct hct
  cases hdec : E.decrypt n k (false :: ct) with
  | none =>
    have hfb : E.tailFallback.decrypt n k (false :: ct) = some (List.replicate n false) := by
      simp [tailFallback, hdec, hdecCt]
    rw [hfb, take_encOption_some_replicate,
      encOption_some_replicate_false_beq_true hn] at hwin
    contradiction
  | some msg =>
    have hfb : E.tailFallback.decrypt n k (false :: ct) = some msg := by
      simp [tailFallback, hdec]
    rw [hfb] at hwin
    have hmsgNe : msg ≠ List.replicate n false := by
      rintro rfl
      rw [take_encOption_some_replicate,
        encOption_some_replicate_false_beq_true hn] at hwin
      contradiction
    simp [hmsgNe]

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `OneTimeINDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem not_oneTimeINDCCA_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.OneTimeINDCCA := by
  intro hcca
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have := hcca (tailFallbackCCAAdversary ctBound)
    (isOraclePPT_tailFallbackCCAAdversary hctBoundPoly)
  have := hforge.negligible (prependFalseBitCIAdversary false ctBound)
    (isOraclePPT_prependFalseBitCIAdversary false hctBoundPoly)
  have := hforge.negligible (prependFalseBitCIAdversary true ctBound)
    (isOraclePPT_prependFalseBitCIAdversary true hctBoundPoly)
  have hle : ∀ᶠ n in Filter.atTop, (1 : ℝ≥0) ≤
      Game.succProbability
        (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary false ctBound) n)) +
      Game.advantage
        (ProbComp.eval (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n))
        (ProbComp.eval (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n)) +
      Game.succProbability
        (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary true ctBound) n)) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have htrue := one_le_succProbability_ccaOneTimeGame_tailFallback_true E ctBound n (hctBound n)
    have hfalse := succProbability_ccaOneTimeGame_tailFallback_false_le E ctBound n hn (hctBound n)
    have hadv := Game.succProbability_le_add_of_advantage_le
      (g₀ := ProbComp.eval
        (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n))
      (g₁ := ProbComp.eval
        (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n))
      (Game.advantage_comm _ _).le
    exact htrue.trans (by gcongr; exact hadv.trans (by gcongr))
  exact not_negligible_const one_ne_zero (by negligible eventually hle)

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `INDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 165). -/
theorem not_indcca_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.INDCCA :=
  fun hcca => not_oneTimeINDCCA_tailFallback hforge hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.10 counterexample**
([KatzLindell2020], Exercise 5.10, printed p. 165): from any `INDCPA` and `EncForge` symmetric
cipher `E`, `E.tailFallback` simultaneously satisfies `INDCPA` and `EncForge` while failing
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem tailFallback_counterexample {E : SymmetricCipher} (hcpa : E.INDCPA)
    (hforge : E.EncForge) :
    E.tailFallback.INDCPA ∧ E.tailFallback.EncForge ∧
      ¬ E.tailFallback.OneTimeCiphertextIntegrity ∧ ¬ E.tailFallback.CiphertextIntegrity ∧
      ¬ E.tailFallback.OneTimeINDCCA ∧ ¬ E.tailFallback.INDCCA :=
  ⟨hcpa.tailFallback, hforge.tailFallback, E.not_oneTimeCiphertextIntegrity_tailFallback,
    E.not_ciphertextIntegrity_tailFallback, not_oneTimeINDCCA_tailFallback hforge,
    not_indcca_tailFallback hforge⟩

end SymmetricCipher

/-! ### Katz–Lindell Exercise 5.4: Encrypt-then-MAC Under a Non-Strong MAC

Given any `M : MACScheme`, `M.redundantTag` keeps `msgLen`, `keyGen`, and `sign` unchanged, while
`verify` accepts `tag` whenever either `M.verify sk msg tag` holds or `tag` is non-empty and
`M.verify sk msg tag.tail` holds. Consequently:

* `M.redundantTag` preserves `EUFCMA` and `OneTimeEUFCMA` (any fresh-message forgery `(msg, tag)`
  against `M.redundantTag` yields a fresh-message forgery against `M` on either `(msg, tag)` or
  `(msg, tag.tail)`),
* `M.redundantTag` fails `OneTimeSUFCMA` and `SUFCMA` (`redundantTagForger` queries `0^(M.msgLen n)`
  to obtain `tag` and outputs `(0^(M.msgLen n), false :: tag)`),
* when composed with any `E : SymmetricCipher` via `encryptThenMAC E M.redundantTag hctLen`, the
  resulting cipher satisfies `INDCPA` (if `E.INDCPA`) and `EncForge` (if `M.EUFCMA`), yet fails
  `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`
  ([KatzLindell2020], Exercise 5.4, printed p. 164). -/

namespace MACScheme

/-- **Redundant-tag MAC transformation** ([KatzLindell2020], Exercise 5.4, printed p. 164):
`M.redundantTag` keeps `msgLen`, `keyGen`, and `sign` unchanged, while `verify` accepts `tag` when
either `M.verify sk msg tag` holds or `tag` is non-empty and `M.verify sk msg tag.tail` holds. -/
noncomputable def redundantTag (M : MACScheme) : MACScheme where
  msgLen := M.msgLen
  msgLen_polyTime := M.msgLen_polyTime
  keyGen := M.keyGen
  sign := M.sign
  verify sk msg tag := M.verify sk msg tag || (!tag.isEmpty && M.verify sk msg tag.tail)
  keyGen_ppt := M.keyGen_ppt
  sign_ppt := M.sign_ppt
  verify_polyTime := by fun_prop
  verify_sign n sk hsk msg hmsg tag htag := by
    simp [M.verify_sign n sk hsk msg hmsg tag htag]

/-- Forger reduction that strips the leading bit of the candidate forgery tag. -/
noncomputable def tailTagForger (adversary : Forger) : Forger :=
  fun n aux => (fun p : List Bool × List Bool => (p.1, p.2.tail)) <$> adversary n aux

/-- `tailTagForger` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_tailTagForger {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (tailTagForger adversary) :=
  (hadversary.on.map' (by fun_prop)).isOraclePPT

private theorem succProbability_redundantTag_runDist_le (M : MACScheme)
    (oracle :
      List Bool → Unit × List Bool → List (List Bool) → ProbComp (List Bool × List (List Bool)))
    (adversary : Forger) (n : ℕ) :
    let runDist : PMF (List Bool × (List Bool × List Bool) × List (List Bool)) :=
      (ProbComp.eval (M.keyGen n)).bind fun sk =>
        (ProbOracleComp.runWith (fun req s => ProbComp.eval (oracle sk req s))
          (adversary n []) []).map fun out => (sk, out)
    Game.succProbability (runDist.bind fun p => PMF.pure
        ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
          M.redundantTag.verify p.1 p.2.1.1 p.2.1.2)) ≤
      Game.succProbability (runDist.bind fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2)) +
        Game.succProbability (runDist.bind fun p => PMF.pure
            ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
              M.verify p.1 p.2.1.1 p.2.1.2.tail)) := by
  refine succProbability_bind_pure_bool_le_add _ _ _ _ fun p _ hwin => ?_
  dsimp only [redundantTag] at hwin
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hwin ⊢
  rcases hwin with ⟨⟨hlen, hfresh⟩, hver | ⟨_, hverTail⟩⟩
  · exact Or.inl ⟨⟨hlen, hfresh⟩, hver⟩
  · exact Or.inr ⟨⟨hlen, hfresh⟩, hverTail⟩

/-- **Quantitative `EUFCMA` bound for `M.redundantTag`** ([KatzLindell2020], Exercise 5.4,
printed p. 164): any fresh-message forgery against `M.redundantTag` either succeeds directly
against `M` or succeeds after stripping the leading bit of the tag via `tailTagForger`. -/
theorem succProbability_eufCmaGame_redundantTag_le (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.redundantTag.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) +
        Game.succProbability (ProbComp.eval (M.eufCmaGame (tailTagForger adversary) n)) := by
  have horacle (sk : List Bool) : M.redundantTag.signingOracle sk = M.signingOracle sk := rfl
  have hkeyGen : M.redundantTag.keyGen = M.keyGen := rfl
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simpa only [eufCmaGame, tailTagForger, hkeyGen, horacle, hmsgLen, runWith_norm, pmf_norm] using
    succProbability_redundantTag_runDist_le M M.signingOracle adversary n

/-- **Quantitative `OneTimeEUFCMA` bound for `M.redundantTag`**. -/
theorem succProbability_eufOneTimeGame_redundantTag_le (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.redundantTag.eufOneTimeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)) +
        Game.succProbability (ProbComp.eval (M.eufOneTimeGame (tailTagForger adversary) n)) := by
  have horacle (sk : List Bool) :
      M.redundantTag.oneTimeSigningOracle sk = M.oneTimeSigningOracle sk := rfl
  have hkeyGen : M.redundantTag.keyGen = M.keyGen := rfl
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  simpa only [eufOneTimeGame, tailTagForger, hkeyGen, horacle, hmsgLen, runWith_norm,
    pmf_norm] using succProbability_redundantTag_runDist_le M M.oneTimeSigningOracle adversary n

/-- `redundantTag` preserves `EUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem EUFCMA.redundantTag {M : MACScheme} (h : M.EUFCMA) : M.redundantTag.EUFCMA := by
  refine EUFCMA.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  negligible using M.succProbability_eufCmaGame_redundantTag_le adversary

/-- `redundantTag` preserves `OneTimeEUFCMA`. -/
theorem OneTimeEUFCMA.redundantTag {M : MACScheme} (h : M.OneTimeEUFCMA) :
    M.redundantTag.OneTimeEUFCMA := by
  refine OneTimeEUFCMA.of_negligible fun adversary hadversary => ?_
  have := h.negligible adversary hadversary
  have := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  negligible using M.succProbability_eufOneTimeGame_redundantTag_le adversary

/-- One-query strong-MAC forger against `M.redundantTag`: queries `0^(M.msgLen n)` (truncating the
reply to `tagBound n`) and prepends `false` to the returned tag. -/
noncomputable def redundantTagForger (M : MACScheme) (tagBound : ℕ → ℕ) : Forger :=
  fun n _ => do
    let msg := List.replicate (M.msgLen n) false
    let tag ← List.take (tagBound n) <$> ProbOracleComp.query ((), msg)
    return (msg, false :: tag)

/-- `redundantTagForger` is strict oracle-PPT whenever `tagBound` is computable in plain polynomial
time. -/
theorem isOraclePPT_redundantTagForger (M : MACScheme) {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPT (encPair encBits encBits) (M.redundantTagForger tagBound) := by
  have hreq : ComputableInPolyTime
      (fun p : ℕ × List Bool => List.replicate (M.msgLen p.1) false)
      (encPair encUnary encBits) encBits := by fun_prop
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => tagBound p.1)
      (encPair encUnary encBits) encUnary := htagBound.comp (by fun_prop)
  have hout : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        (List.replicate (M.msgLen p.1.1) false, false :: p.2))
      (encPair (encPair encUnary encBits) encBits) (encPair encBits encBits) := by fun_prop
  unfold redundantTagForger
  exact ((IsOraclePPTOn.query_take' () hreq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

/-- In `sufOneTimeGame` against `M.redundantTag`, `M.redundantTagForger tagBound` wins with
probability `1` at every security parameter `n` where `tagBound n` bounds tag lengths. -/
theorem eval_sufOneTimeGame_redundantTag_redundantTagForger (M : MACScheme)
    (tagBound : ℕ → ℕ) (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.redundantTag.sufOneTimeGame (M.redundantTagForger tagBound) n) =
      PMF.pure true := by
  simp only [sufOneTimeGame, redundantTagForger, oneTimeSigningPairOracle,
    List.isEmpty_nil, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun sk hsk =>
    PMF.bind_eq_pure_of_forall_mem_support fun tag htag => ?_
  have htake : List.take (tagBound n) tag = tag :=
    List.take_of_length_le (htagBound sk hsk _ List.length_replicate tag htag)
  have hver := M.verify_sign n sk hsk _ List.length_replicate tag htag
  simp [redundantTag, htake, hver]

/-- In `sufCmaGame` against `M.redundantTag`, `M.redundantTagForger tagBound` wins with probability
`1` at every security parameter `n` where `tagBound n` bounds tag lengths. -/
theorem eval_sufCmaGame_redundantTag_redundantTagForger (M : MACScheme)
    (tagBound : ℕ → ℕ) (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.redundantTag.sufCmaGame (M.redundantTagForger tagBound) n) =
      PMF.pure true := by
  simp only [sufCmaGame, redundantTagForger, signingPairOracle, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun sk hsk =>
    PMF.bind_eq_pure_of_forall_mem_support fun tag htag => ?_
  have htake : List.take (tagBound n) tag = tag :=
    List.take_of_length_le (htagBound sk hsk _ List.length_replicate tag htag)
  have hver := M.verify_sign n sk hsk _ List.length_replicate tag htag
  simp [redundantTag, htake, hver]

/-- `M.redundantTag` never satisfies `OneTimeSUFCMA` ([KatzLindell2020], Exercise 5.4,
printed p. 164). -/
theorem not_oneTimeSUFCMA_redundantTag (M : MACScheme) :
    ¬ M.redundantTag.OneTimeSUFCMA := by
  intro hsuf
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := M.exists_tag_length_bound_of_length_eq
  have hneg := hsuf.negligible (M.redundantTagForger tagBound)
    (M.isOraclePPT_redundantTagForger htagBoundPoly)
  have heq : (fun n => Game.succProbability
      (ProbComp.eval (M.redundantTag.sufOneTimeGame (M.redundantTagForger tagBound) n))) =
      fun _ => (1 : ℝ≥0) := by
    funext n
    rw [M.eval_sufOneTimeGame_redundantTag_redundantTagForger tagBound n (htagBound n)]
    simp [Game.succProbability]
  rw [heq] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `M.redundantTag` never satisfies `SUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_sufCma_redundantTag (M : MACScheme) :
    ¬ M.redundantTag.SUFCMA :=
  fun h => M.not_oneTimeSUFCMA_redundantTag h.oneTimeSUFCMA

end MACScheme

/-- If `M.EUFCMA` holds, then `encryptThenMAC E M.redundantTag hctLen` satisfies `EncForge`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem encForge_encryptThenMAC_redundantTag (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (heuf : M.EUFCMA) :
    (encryptThenMAC E M.redundantTag hctLen).EncForge :=
  encForge_encryptThenMAC E M.redundantTag hctLen heuf.redundantTag

/-- One-query ciphertext-integrity adversary against `encryptThenMAC E M.redundantTag hctLen`
([KatzLindell2020], Exercise 5.4, printed p. 164): queries encryption on `0^n` (truncating the
reply to `ctBound n`) to obtain `ct = encPair encBits encBits (c, tag)`, and outputs
`encPair encBits encBits (unframe ct, false :: dropFrame ct)`. -/
def etmRedundantCIAdversary (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n false)
    return encPair encBits encBits (unframe ct, false :: dropFrame ct)

/-- `etmRedundantCIAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (etmRedundantCIAdversary ctBound) := by
  have hreq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by fun_prop
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1)
      (encPair encUnary encBits) encUnary := hctBound.comp (by fun_prop)
  have hout : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        encPair encBits encBits (unframe p.2, false :: dropFrame p.2))
      (encPair (encPair encUnary encBits) encBits) encBits := by fun_prop
  unfold etmRedundantCIAdversary
  exact ((IsOraclePPTOn.query_take' () hreq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

private theorem singleton_encPair_contains_false_cons (c tag : List Bool) :
    ([encPair encBits encBits (c, tag)].contains
      (encPair encBits encBits (c, false :: tag))) = false := by
  rw [Bool.eq_false_iff]
  intro hmem
  have heq : encPair encBits encBits (c, false :: tag) = encPair encBits encBits (c, tag) := by
    simpa using List.contains_iff_mem.mp hmem
  have hp := (encPair encBits encBits).injective heq
  have hlen := congrArg (fun p : List Bool × List Bool => p.2.length) hp
  simp at hlen

private theorem decrypt_encryptThenMAC_redundantTag_false_cons (E : SymmetricCipher)
    (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (n : ℕ) (ke km msg c tag : List Bool)
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (hc : c ∈ (ProbComp.eval (E.encrypt n ke msg)).support)
    (htag : tag ∈ (ProbComp.eval (M.sign km c)).support) :
    (encryptThenMAC E M.redundantTag hctLen).decrypt n
      (encPair encBits encBits (ke, km))
      (encPair encBits encBits (c, false :: tag)) = some msg := by
  have hcLen : c.length = M.msgLen n := hctLen n ke hke msg hmsg c hc
  have hver : M.verify km c tag = true := M.verify_sign n km hkm c hcLen tag htag
  have hdec : E.decrypt n ke c = some msg := E.decrypt_encrypt n ke hke msg hmsg c hc
  dsimp only [encryptThenMAC, MACScheme.redundantTag]
  simp [hcLen, hver, hdec]

private theorem decrypt_encryptThenMAC_redundantTag_of_mem_support (E : SymmetricCipher)
    (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    {n : ℕ} {k msg ct : List Bool}
    (hk : k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈
      (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n k msg)).support) :
    ([ct].contains (encPair encBits encBits (unframe ct, false :: dropFrame ct))) = false ∧
      (encryptThenMAC E M.redundantTag hctLen).decrypt n k
        (encPair encBits encBits (unframe ct, false :: dropFrame ct)) = some msg := by
  simp only [encryptThenMAC, MACScheme.redundantTag, pmf_norm,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk
  obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
  simp only [encryptThenMAC, MACScheme.redundantTag, pmf_norm,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨c, hc, tag, htag, rfl⟩ := hct
  rw [unframe_encPair_encBits] at hc; rw [dropFrame_encPair_encBits] at htag
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  exact ⟨singleton_encPair_contains_false_cons c tag,
    decrypt_encryptThenMAC_redundantTag_false_cons E M hctLen n ke km msg c tag hke hkm hmsg hc
      htag⟩

/-- In `ciOneTimeGame` against `encryptThenMAC E M.redundantTag hctLen`,
`etmRedundantCIAdversary ctBound` wins with probability `1` at every security parameter `n` where
`ctBound n` bounds ciphertext lengths. -/
theorem eval_ciOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n k msg)).support,
        ct.length ≤ ctBound n) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ciOneTimeGame
        (etmRedundantCIAdversary ctBound) n) = PMF.pure true := by
  simp only [SymmetricCipher.ciOneTimeGame, etmRedundantCIAdversary,
    SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hnotMem, hdec⟩ :=
    decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct), hnotMem, hdec]
  rfl

/-- In `ciGame` against `encryptThenMAC E M.redundantTag hctLen`,
`etmRedundantCIAdversary ctBound` wins with probability `1` at every security parameter `n` where
`ctBound n` bounds ciphertext lengths. -/
theorem eval_ciGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n k msg)).support,
        ct.length ≤ ctBound n) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ciGame
        (etmRedundantCIAdversary ctBound) n) = PMF.pure true := by
  simp only [SymmetricCipher.ciGame, etmRedundantCIAdversary,
    SymmetricCipher.ciEncryptionOracle, List.length_replicate, beq_self_eq_true,
    ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hnotMem, hdec⟩ :=
    decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct), hnotMem, hdec]
  rfl

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeCiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeCiphertextIntegrity := by
  intro hci
  let ETM := encryptThenMAC E M.redundantTag hctLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := ETM.exists_ciphertext_length_bound_of_length_eq
  have hneg := hci.negligible (etmRedundantCIAdversary ctBound)
    (isOraclePPT_etmRedundantCIAdversary hctBoundPoly)
  have heq : (fun n => Game.succProbability
      (ProbComp.eval (ETM.ciOneTimeGame (etmRedundantCIAdversary ctBound) n))) =
      fun _ => (1 : ℝ≥0) := by
    funext n
    rw [eval_ciOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCIAdversary
      E M hctLen ctBound n (hctBound n)]
    simp [Game.succProbability]
  rw [heq] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `CiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_ciphertextIntegrity_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).CiphertextIntegrity :=
  fun h =>
    not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen
      h.oneTimeCiphertextIntegrity

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeAuthenticatedEncryption`. -/
theorem not_oneTimeAuthenticatedEncryption_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeAuthenticatedEncryption :=
  fun h => not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen h.2

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `AuthenticatedEncryption`. -/
theorem not_authenticatedEncryption_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).AuthenticatedEncryption :=
  fun h => not_ciphertextIntegrity_encryptThenMAC_redundantTag E M hctLen h.2

/-- Two-query CCA adversary against `encryptThenMAC E M.redundantTag hctLen`
([KatzLindell2020], Exercise 5.4, printed p. 164): queries left-or-right encryption on
`(0^n, 1^n)` to obtain `ct`, queries decryption on
`encPair encBits encBits (unframe ct, false :: dropFrame ct)`, and outputs whether the decrypted
message equals `some 1^n`. -/
def etmRedundantCCAAdversary (ctBound : ℕ → ℕ) : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (ctBound n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let reply ← List.take (n + 1) <$>
      ProbOracleComp.query (true, encPair encBits encBits (unframe ct, false :: dropFrame ct))
    return (reply == encOption encBits (some m1))

/-- `etmRedundantCCAAdversary` is strict oracle-PPT whenever `ctBound` is computable in plain
polynomial time. -/
theorem isOraclePPT_etmRedundantCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (etmRedundantCCAAdversary ctBound) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encBits
  let E2 := encPair E1 encBits
  have hreq1 : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 true))
      E0 encBits := by
    dsimp only [E0]; fun_prop
  have hlim1 : ComputableInPolyTime (fun p : ℕ × List Bool => ctBound p.1) E0 encUnary :=
    hctBound.comp (by dsimp only [E0]; fun_prop)
  have hreq2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        encPair encBits encBits (unframe p.2, false :: dropFrame p.2))
      E1 encBits := by
    dsimp only [E1, E0]; fun_prop
  have hlim2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => p.1.1 + 1) E1 encUnary := by
    dsimp only [E1, E0]; fun_prop
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool =>
        p.2 == encOption encBits (some (List.replicate p.1.1.1 true)))
      E2 encBool := by
    dsimp only [E2, E1, E0]; fun_prop
  unfold etmRedundantCCAAdversary
  exact ((IsOraclePPTOn.query_take' false hreq1 hlim1).bind_with
    ((IsOraclePPTOn.query_take' true hreq2 hlim2).bind_with hout.isOraclePPTOn)).isOraclePPT

/-- In `ccaOneTimeGame` against `encryptThenMAC E M.redundantTag hctLen` at challenge bit `bit`,
`etmRedundantCCAAdversary ctBound` outputs `true` iff `some (List.replicate n bit)` encodes to
`encOption encBits (some (List.replicate n true))`. -/
theorem eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (bit : Bool) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n k msg)).support,
        ct.length ≤ ctBound n) :
    ProbComp.eval
      ((encryptThenMAC E M.redundantTag hctLen).ccaOneTimeGame
        (etmRedundantCCAAdversary ctBound) bit n) =
      PMF.pure
        (List.take (n + 1) (encOption encBits (some (List.replicate n bit))) ==
          encOption encBits (some (List.replicate n true))) := by
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by
    cases bit <;> rfl
  simp only [SymmetricCipher.ccaOneTimeGame, etmRedundantCCAAdversary,
    SymmetricCipher.oneTimeCCAOracle, unframe_encPair_encBits, dropFrame_encPair_encBits, hbit,
    List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
    runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hnotMem, hdec⟩ :=
    decrypt_encryptThenMAC_redundantTag_of_mem_support E M hctLen hk List.length_replicate hct
  rw [List.take_of_length_le (hctBound k hk _ List.length_replicate ct hct), hnotMem, hdec]
  simp [ProbComp.eval_pure]

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeINDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_oneTimeINDCCA_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA := by
  intro hcca
  let ETM := encryptThenMAC E M.redundantTag hctLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := ETM.exists_ciphertext_length_bound_of_length_eq
  have := hcca (etmRedundantCCAAdversary ctBound)
    (isOraclePPT_etmRedundantCCAAdversary hctBoundPoly)
  have hle : ∀ᶠ n in Filter.atTop, (1 : ℝ≥0) ≤ Game.advantage
      (ProbComp.eval (ETM.ccaOneTimeGame (etmRedundantCCAAdversary ctBound) false n))
      (ProbComp.eval (ETM.ccaOneTimeGame (etmRedundantCCAAdversary ctBound) true n)) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have h0 := eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
      E M hctLen false ctBound n (hctBound n)
    have h1 := eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
      E M hctLen true ctBound n (hctBound n)
    rw [SymmetricCipher.take_encOption_some_replicate n false,
      SymmetricCipher.encOption_some_replicate_false_beq_true hn] at h0
    rw [SymmetricCipher.take_encOption_some_replicate n true, beq_self_eq_true] at h1
    rw [h0, h1, Game.advantage_comm, Game.advantage_pure_false]
    simp [Game.succProbability]
  exact not_negligible_const one_ne_zero (by negligible eventually hle)

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `INDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
theorem not_indcca_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).INDCCA :=
  fun hcca =>
    not_oneTimeINDCCA_encryptThenMAC_redundantTag E M hctLen hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.4 counterexample** ([KatzLindell2020], Exercise 5.4, printed p. 164):
for any `INDCPA` symmetric cipher `E` and any `EUFCMA` message authentication code `M`,
`M.redundantTag` is `EUFCMA`-secure yet not `SUFCMA`-secure, and
`encryptThenMAC E M.redundantTag hctLen` satisfies `INDCPA` and `EncForge` while failing
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem encryptThenMAC_redundantTag_counterexample
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (hcpa : E.INDCPA) (heuf : M.EUFCMA) :
    M.redundantTag.EUFCMA ∧ ¬ M.redundantTag.OneTimeSUFCMA ∧ ¬ M.redundantTag.SUFCMA ∧
      (encryptThenMAC E M.redundantTag hctLen).INDCPA ∧
      (encryptThenMAC E M.redundantTag hctLen).EncForge ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeCiphertextIntegrity ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).CiphertextIntegrity ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA ∧
      ¬ (encryptThenMAC E M.redundantTag hctLen).INDCCA :=
  ⟨heuf.redundantTag, M.not_oneTimeSUFCMA_redundantTag, M.not_sufCma_redundantTag,
    indcpa_encryptThenMAC E M.redundantTag hctLen hcpa,
    encForge_encryptThenMAC_redundantTag E M hctLen heuf,
    not_oneTimeCiphertextIntegrity_encryptThenMAC_redundantTag E M hctLen,
    not_ciphertextIntegrity_encryptThenMAC_redundantTag E M hctLen,
    not_oneTimeINDCCA_encryptThenMAC_redundantTag E M hctLen,
    not_indcca_encryptThenMAC_redundantTag E M hctLen⟩

/-! ### Concrete Non-Vacuous PRF-Based Instantiations -/

/-- **End-to-end PRF-based instantiation of Exercise 5.10**: for any secure
`PseudorandomFunction family`,
`(prfEncryptThenMAC family hprf.polyTime hprf.length_eq).tailFallback` satisfies `INDCPA` and
`EncForge` while failing `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and
`INDCCA`. -/
theorem PseudorandomFunction.tailFallback_prfEncryptThenMAC_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let E := (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).tailFallback
    E.INDCPA ∧ E.EncForge ∧ ¬ E.OneTimeCiphertextIntegrity ∧ ¬ E.CiphertextIntegrity ∧
      ¬ E.OneTimeINDCCA ∧ ¬ E.INDCCA :=
  SymmetricCipher.tailFallback_counterexample
    hprf.authenticatedEncryption_prfEncryptThenMAC.1
    hprf.authenticatedEncryption_prfEncryptThenMAC.2.encForge

/-- **Concrete PRF-based Encrypt-then-MAC cipher with a non-strong redundant-tag MAC**
([KatzLindell2020], Exercise 5.4, printed p. 164). -/
noncomputable def prfEncryptThenMACRedundantTag (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    SymmetricCipher :=
  encryptThenMAC
    (prfCipher family hpoly hlen)
    (((prfMAC family hpoly).reindex (fun n => 2 * n) (by fun_prop)).redundantTag)
    (prfCipher_ciphertext_length family hpoly hlen)

/-- **End-to-end PRF-based instantiation of Exercise 5.4**: for any secure
`PseudorandomFunction family`, `prfEncryptThenMACRedundantTag` satisfies `INDCPA` and `EncForge`
while failing `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`. -/
theorem PseudorandomFunction.prfEncryptThenMACRedundantTag_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let M := (prfMAC family hprf.polyTime).reindex (fun n => 2 * n) (by fun_prop)
    let ETM := prfEncryptThenMACRedundantTag family hprf.polyTime hprf.length_eq
    M.redundantTag.EUFCMA ∧ ¬ M.redundantTag.OneTimeSUFCMA ∧ ¬ M.redundantTag.SUFCMA ∧
      ETM.INDCPA ∧ ETM.EncForge ∧ ¬ ETM.OneTimeCiphertextIntegrity ∧
      ¬ ETM.CiphertextIntegrity ∧ ¬ ETM.OneTimeINDCCA ∧ ¬ ETM.INDCCA :=
  encryptThenMAC_redundantTag_counterexample
    (prfCipher family hprf.polyTime hprf.length_eq)
    ((prfMAC family hprf.polyTime).reindex (fun n => 2 * n) (by fun_prop))
    (prfCipher_ciphertext_length family hprf.polyTime hprf.length_eq)
    hprf.indcpa_prfCipher
    (hprf.eufCma_prfMAC.reindex (by fun_prop) (strictMono_mul_left_of_pos two_pos))

end Cslib.Crypto
