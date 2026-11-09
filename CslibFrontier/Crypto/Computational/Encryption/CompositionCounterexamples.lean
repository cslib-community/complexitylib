/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Encryption Unforgeability and Generic Composition Counterexamples

This module formalizes fresh-message encryption unforgeability (`EncForge`) and the generic
composition separations and counterexamples of
[Katz and Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020], Chapter 5:

1. **Fresh-message encryption unforgeability (`SymmetricCipher.encForgeOracle`,
   `SymmetricCipher.encForgeGame`, `SymmetricCipher.EncForge`, `CiphertextIntegrity.encForge`,
   `encForge_encryptThenMAC`)** ([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 176;
   Exercise 5.5, printed p. 191): in `encForgeGame`, an adaptive `CIAdversary` queries an
   encryption oracle on `n`-bit plaintexts (logging the queried plaintexts `queriedMsgs`) and wins
   by outputting a candidate ciphertext `ct` that decrypts to `some m` for a fresh plaintext
   `!queriedMsgs.contains m`. We prove that ciphertext integrity (`ciGame`,
   [BonehShoup2023], Definition 9.1) implies `EncForge` (`succProbability_encForgeGame_le_ciGame`,
   `CiphertextIntegrity.encForge`), and that for `encryptThenMAC E M hctLen`, ordinary fresh-message
   MAC unforgeability (`M.EUFCMA`, without `M.SUFCMA`) already suffices for
   `(encryptThenMAC E M hctLen).EncForge` (`succProbability_encForgeGame_encryptThenMAC_le`,
   `encForge_encryptThenMAC`, [KatzLindell2020], Exercise 5.5).
2. **Separation of `INDCPA ∧ EncForge` from `INDCCA` and `CiphertextIntegrity`
   (`SymmetricCipher.tailFallback`, `INDCPA.tailFallback`, `EncForge.tailFallback`,
   `not_ciphertextIntegrity_tailFallback`, `not_indcca_tailFallback`)**
   ([KatzLindell2020], Exercise 5.10, printed p. 192): for any `E : SymmetricCipher`,
   `E.tailFallback` keeps `keyGen` and `encrypt` unchanged and modifies `decrypt n k ct` to fall
   back to `E.decrypt n k ct.tail` whenever `E.decrypt n k ct = none` and `!ct.isEmpty`. This
   preserves `INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
   `OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (by prepending `false` to a queried
   ciphertext) and breaking `OneTimeINDCCA` and `INDCCA` whenever `E.EncForge` holds.
3. **Encrypt-then-MAC under a non-strong MAC (`MACScheme.redundantTag`, `EUFCMA.redundantTag`,
   `not_sufCma_redundantTag`, `not_indcca_encryptThenMAC_redundantTag`,
   `encryptThenMAC_redundantTag_counterexample`)** ([KatzLindell2020], Exercise 5.4, printed
   p. 191): for any `M : MACScheme`, `M.redundantTag` keeps `keyGen`, `msgLen`, and `sign`
   unchanged while accepting either `M.verify sk msg tag` or `!tag.isEmpty && M.verify sk msg
   tag.tail`. This preserves `EUFCMA` and `OneTimeEUFCMA` while breaking `OneTimeSUFCMA` and
   `SUFCMA`; when combined with any cipher `E` via `encryptThenMAC E M.redundantTag hctLen`, the
   resulting cipher satisfies `INDCPA` and `EncForge` (under `E.INDCPA` and `M.EUFCMA`) yet fails
   `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA` with
   adversary advantage `1`.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.encForgeOracle`, `encForgeGame`, `EncForge`: fresh-message
  encryption unforgeability experiment and security predicate ([KatzLindell2020], Definition 5.2).
* `Cslib.Crypto.SymmetricCipher.tailFallback`, `tailCIAdversary`, `prependFalseBitCIAdversary`,
  `tailFallbackCCAAdversary`: Exercise 5.10 ciphertext-tail fallback transformation and reductions /
  attackers ([KatzLindell2020], Exercise 5.10).
* `Cslib.Crypto.MACScheme.redundantTag`, `tailTagForger`, `redundantTagForger`,
  `etmRedundantCIAdversary`, `etmRedundantCCAAdversary`: Exercise 5.4 redundant-tag MAC
  transformation and reductions / attackers ([KatzLindell2020], Exercise 5.4).

## Main results

* `Cslib.Crypto.SymmetricCipher.succProbability_encForgeGame_le_ciGame`,
  `Cslib.Crypto.SymmetricCipher.CiphertextIntegrity.encForge`: ciphertext integrity implies
  fresh-message encryption unforgeability.
* `Cslib.Crypto.succProbability_encForgeGame_encryptThenMAC_le`,
  `Cslib.Crypto.encForge_encryptThenMAC`: Encrypt-then-MAC with an `EUFCMA`-secure MAC satisfies
  `EncForge` ([KatzLindell2020], Exercise 5.5).
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
  Section 5.2 (Definition 5.2, p. 176) and Exercises 5.4, 5.5, and 5.10 (pp. 191–192).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 9.1 and 9.4.1 (pp. 358–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

private theorem pmf_bind_pure_bool_le {α : Type} (p : PMF α) (f g : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g a = true) :
    (p.bind (fun a => PMF.pure (f a))) true ≤
      (p.bind (fun a => PMF.pure (g a))) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    cases hf : f a
    · simp
    · rw [hfg a ha hf]
  · simp [(p.apply_eq_zero_iff a).mpr ha]

private theorem pmf_bind_pure_bool_le_add {α : Type} (p : PMF α) (f g₁ g₂ : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g₁ a = true ∨ g₂ a = true) :
    (p.bind (fun a => PMF.pure (f a))) true ≤
      (p.bind (fun a => PMF.pure (g₁ a))) true +
        (p.bind (fun a => PMF.pure (g₂ a))) true := by
  rw [PMF.bind_apply, PMF.bind_apply, PMF.bind_apply, ← tsum_add]
  refine tsum_le_tsum fun a => ?_
  rw [← mul_add]
  by_cases ha : a ∈ p.support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    cases hf : f a
    · simp
    · rcases hfg a ha hf with h1 | h2
      · simp [h1]
      · simp [h2]
  · simp [(p.apply_eq_zero_iff a).mpr ha]

private theorem succProbability_bind_pure_bool_le {α : Type} (p : PMF α) (f g : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g a))) := by
  unfold Game.succProbability
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) (pmf_bind_pure_bool_le p f g hfg)

private theorem succProbability_bind_pure_bool_le_add {α : Type} (p : PMF α) (f g₁ g₂ : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g₁ a = true ∨ g₂ a = true) :
    Game.succProbability (p.bind (fun a => PMF.pure (f a))) ≤
      Game.succProbability (p.bind (fun a => PMF.pure (g₁ a))) +
        Game.succProbability (p.bind (fun a => PMF.pure (g₂ a))) := by
  unfold Game.succProbability
  rw [← ENNReal.toNNReal_add (PMF.apply_ne_top _ true) (PMF.apply_ne_top _ true)]
  exact ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ true, PMF.apply_ne_top _ true⟩)
    (pmf_bind_pure_bool_le_add p f g₁ g₂ hfg)

private theorem computableTidilyInPolyTime_contains_bits {α : Type} {enc : α ↪ List Bool}
    {list : α → List (List Bool)} {elem : α → List Bool}
    (hlist : ComputableTidilyInPolyTime list enc (encList encBits))
    (helem : ComputableTidilyInPolyTime elem enc encBits) :
    ComputableTidilyInPolyTime (fun a => (list a).contains (elem a)) enc encBool := by
  classical
  convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
  funext a
  rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]

namespace SymmetricCipher

/-! ### Fresh-Message Encryption Unforgeability (`encForgeGame`, `EncForge`, KL Definition 5.2) -/

/-- Stateful encryption oracle for the fresh-message encryption unforgeability game
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 176): if `request.2.length == n`,
encrypt `request.2` under `k`, prepend `request.2` to `queriedMsgs`, and return the ciphertext;
otherwise return `[]` without modifying `queriedMsgs`. -/
noncomputable def encForgeOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedMsgs =>
    if request.2.length == n then do
      let ct ← E.encrypt n k request.2
      return (ct, request.2 :: queriedMsgs)
    else
      return ([], queriedMsgs)

/-- Pair-logging encryption oracle recording `(msg, ct)` pairs for each valid `n`-bit query.
Projecting `Prod.fst` yields `encForgeOracle` and projecting `Prod.snd` yields
`ciEncryptionOracle`. -/
noncomputable def ciPairOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs =>
    if request.2.length == n then do
      let ct ← E.encrypt n k request.2
      return (ct, (request.2, ct) :: queriedPairs)
    else
      return ([], queriedPairs)

/-- The fresh-message encryption unforgeability experiment `Enc-Forge`
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 176): sample `k ← E.keyGen n`, run
`adversary n []` against `E.encForgeOracle n k`, and accept when `E.decrypt n k out.1` succeeds
with a plaintext `m` that was never queried (`!out.2.contains m`). -/
noncomputable def encForgeGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.encForgeOracle n k)) (adversary n [])).run []
  return (E.decrypt n k out.1).isSome && !out.2.contains ((E.decrypt n k out.1).getD [])

/-- Running an oracle-PPT adversary against `encForgeOracle` is uniformly strict PPT in `(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_encForgeOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.encForgeOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        p.2.1.2.length == p.1.1)
      EIn encBool :=
    ComputableTidilyInPolyTime.unary_beq
      (by dsimp only [EIn]; fun_prop) (by dsimp only [EIn]; fun_prop)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, p.2.1.2 :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; fun_prop : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.1.2.1.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.encForgeOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold encForgeOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess'
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ d + 2 * query.length + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queried _ result hresult
  unfold encForgeOracle at hresult
  split_ifs at hresult with hlenEq
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    have hctLen := hlen (caller.1, caller.2, request.2) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
    have hbound : ct.length ≤ c * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

private theorem computableTidilyInPolyTime_encForgePost (E : SymmetricCipher) :
    ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome &&
          !pair.2.2.contains ((E.decrypt pair.1.1 pair.1.2 pair.2.1).getD []))
      (encPair (encPair encUnary encBits) (encPair encBits (encList encBits))) encBool := by
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hdecArg : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        E.decrypt pair.1.1 pair.1.2 pair.2.1)
      EOut (encOption encBits) :=
    E.decrypt_polyTime.tidy.comp hdecArg
  have hisSome := hdec.optionIsSome
  have hgetD := ComputableTidilyInPolyTime.optionGetDWithInput hdec
    (ComputableTidilyInPolyTime.const [])
  have hlist : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.2)
      EOut (encList encBits) := by
    dsimp only [EOut]; fun_prop
  have hcontains := computableTidilyInPolyTime_contains_bits hlist hgetD
  exact ComputableTidilyInPolyTime.bool_and.comp
    (hisSome.prod (ComputableTidilyInPolyTime.bool_not.comp hcontains))

/-- The fresh-message encryption unforgeability experiment is uniformly strict PPT in the unary
security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_encForgeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.encForgeGame adversary) := by
  have hrun := E.isPPTOn_run_encForgeOracle hadversary
  unfold encForgeGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with E.computableTidilyInPolyTime_encForgePost.isPPTOn)

/-- The fresh-message encryption unforgeability experiment is uniformly strict PPT, independently of
unused auxiliary input. -/
@[program_certificate]
theorem isPPT_encForgeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.encForgeGame adversary n) :=
  ((E.isPPTOn_encForgeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Fresh-message encryption unforgeability (`EncForge`, or KL Definition 5.2)
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 176): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a ciphertext that decrypts
to an unqueried plaintext. -/
def EncForge (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.encForgeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- `EncForge` gives negligible winning probability in `encForgeGame` for every oracle-PPT
adversary. -/
theorem EncForge.negligible {E : SymmetricCipher} (h : E.EncForge)
    (adversary : CIAdversary) (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.encForgeGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `EncForge` by bounding every oracle-PPT adversary's winning probability. -/
theorem EncForge.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.encForgeGame adversary n)))) :
    E.EncForge := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Running an adaptive program against `encForgeOracle` produces the exact same distribution as
running it against `ciPairOracle` and projecting the pair log via `Prod.fst`. -/
theorem eval_run_encForgeOracle_eq_map_fst_ciPairOracle (E : SymmetricCipher)
    (n : ℕ) (k : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.encForgeOracle n k)) prog).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.ciPairOracle n k)) prog).run [])).map
      (fun (a, s') => (a, s'.map Prod.fst)) := by
  rw [ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact (ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (E.ciPairOracle n k q s))
    (oracle' := fun q s => ProbComp.eval (E.encForgeOracle n k q s))
    (represent := List.map Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      unfold ciPairOracle encForgeOracle
      split_ifs <;> simp [ProbComp.eval_pure, PMF.pure_map, PMF.map_comp, Function.comp_def])
    prog []).symm

/-- Running an adaptive program against `ciEncryptionOracle` produces the exact same distribution as
running it against `ciPairOracle` and projecting the pair log via `Prod.snd`. -/
theorem eval_run_ciEncryptionOracle_eq_map_snd_ciPairOracle (E : SymmetricCipher)
    (n : ℕ) (k : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.ciEncryptionOracle n k)) prog).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.ciPairOracle n k)) prog).run [])).map
      (fun (a, s') => (a, s'.map Prod.snd)) := by
  rw [ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact (ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (E.ciPairOracle n k q s))
    (oracle' := fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s))
    (represent := List.map Prod.snd)
    (step := by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      unfold ciPairOracle ciEncryptionOracle
      split_ifs <;> simp [ProbComp.eval_pure, PMF.pure_map, PMF.map_comp, Function.comp_def])
    prog []).symm

private theorem mem_support_ciPairOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (prog : WordOracleComp Unit (List Bool))
    (result : List Bool) (queriedPairs : List (List Bool × List Bool))
    (hmem : (result, queriedPairs) ∈ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.ciPairOracle n k)) prog).run [])).support) :
    ∀ pair ∈ queriedPairs,
      pair.1.length = n ∧ pair.2 ∈ (ProbComp.eval (E.encrypt n k pair.1)).support := by
  rw [ProbOracleComp.eval_run_interpret] at hmem
  refine ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
    (fun s => ∀ pair ∈ s,
      pair.1.length = n ∧ pair.2 ∈ (ProbComp.eval (E.encrypt n k pair.1)).support)
    ?_ prog [] (by simp) result queriedPairs hmem
  intro ⟨⟨⟩, msg⟩ s hs a s' hstep pair hpair
  unfold ciPairOracle at hstep
  split_ifs at hstep with hlen
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
    obtain ⟨ct, hct, hpairEq⟩ := hstep
    cases hpairEq
    rcases List.mem_cons.mp hpair with rfl | htail
    · exact ⟨beq_iff_eq.mp hlen, hct⟩
    · exact hs pair htail
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hstep
    cases hstep
    exact hs pair hpair

/-- **Quantitative `EncForge` vs. `CiphertextIntegrity` bound**: for every `SymmetricCipher`,
adaptive adversary, and security parameter `n`, the fresh-message forgery probability in
`encForgeGame` is at most the fresh-ciphertext forgery probability in `ciGame`. -/
theorem succProbability_encForgeGame_le_ciGame (E : SymmetricCipher)
    (adversary : CIAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval (E.encForgeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (E.ciGame adversary n)) := by
  simp only [Game.succProbability, encForgeGame, ciGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun k => ?_
  by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [E.eval_run_encForgeOracle_eq_map_fst_ciPairOracle n k (adversary n []),
      E.eval_run_ciEncryptionOracle_eq_map_snd_ciPairOracle n k (adversary n []),
      PMF.bind_map, PMF.bind_map]
    refine pmf_bind_pure_bool_le _ _ _ fun out hout hwin => ?_
    have hinv := E.mem_support_ciPairOracle n k (adversary n []) out.1 out.2 hout
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwin ⊢
    refine ⟨?_, hwin.1⟩
    rw [Bool.eq_false_iff]
    intro hmemCt
    obtain ⟨pair, hpairMem, hpairSnd⟩ := List.mem_map.mp (List.contains_iff_mem.mp hmemCt)
    have ⟨hmsgLen, hctSupport⟩ := hinv pair hpairMem
    have hdec : E.decrypt n k out.1 = some pair.1 := by
      rw [← hpairSnd]
      exact E.decrypt_encrypt n k hk pair.1 hmsgLen pair.2 hctSupport
    have hmemMsg : ((E.decrypt n k out.1).getD []) ∈ out.2.map Prod.fst := by
      rw [hdec, Option.getD_some]
      exact List.mem_map_of_mem hpairMem
    have hcontainsMsg : (out.2.map Prod.fst).contains ((E.decrypt n k out.1).getD []) = true :=
      List.contains_iff_mem.mpr hmemMsg
    rw [hwin.2] at hcontainsMsg
    contradiction
  · simp [(ProbComp.eval (E.keyGen n)).apply_eq_zero_iff k |>.mpr hk]

/-- Ciphertext integrity (`CiphertextIntegrity`) implies fresh-message encryption unforgeability
(`EncForge`). -/
theorem CiphertextIntegrity.encForge {E : SymmetricCipher} (h : E.CiphertextIntegrity) :
    E.EncForge :=
  h.of_succProbability_le fun adversary _ =>
    E.succProbability_encForgeGame_le_ciGame adversary

end SymmetricCipher

/-! ### KL Exercise 5.5: Encrypt-then-MAC with an `EUFCMA` MAC Satisfies `EncForge` -/

/-- Joint encryption oracle for `encryptThenMAC E M hctLen` recording `(msg, c)` pairs for each
valid `n`-bit plaintext query `msg` and its inner ciphertext `c ← E.encrypt n ke msg`. Projecting
`Prod.fst` recovers `(encryptThenMAC E M hctLen).encForgeOracle`, while projecting `Prod.snd`
recovers the inner ciphertext log of `M.signingOracle km` in `etmToMACForger`. -/
noncomputable def etmForgeJointOracle (E : SymmetricCipher) (M : MACScheme) (n : ℕ)
    (ke km : List Bool) (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs =>
    if request.2.length == n then do
      let c ← E.encrypt n ke request.2
      let tag ← M.sign km c
      return (encPair encBits encBits (c, tag), (request.2, c) :: queriedPairs)
    else
      return ([], queriedPairs)

private theorem eval_run_encForgeOracle_encryptThenMAC_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (n : ℕ) (ke km : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        ((encryptThenMAC E M hctLen).encForgeOracle n (encPair encBits encBits (ke, km))))
      prog).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (etmForgeJointOracle E M n ke km)) prog).run [])).map
      (fun (a, s') => (a, s'.map Prod.fst)) := by
  rw [ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
    simp [encPair_apply, dropFrame_frame_append]
  exact (ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (etmForgeJointOracle E M n ke km q s))
    (oracle' := fun q s =>
      ProbComp.eval ((encryptThenMAC E M hctLen).encForgeOracle n
        (encPair encBits encBits (ke, km)) q s))
    (represent := List.map Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      unfold etmForgeJointOracle SymmetricCipher.encForgeOracle
      dsimp only [encryptThenMAC]
      rw [hunframe_k, hdrop_k]
      split_ifs <;> simp [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
        PMF.map_comp, Function.comp_def])
    prog []).symm

private theorem eval_run_etmToMACHandler_signingOracle_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (n : ℕ) (tagBound : ℕ → ℕ) (ke km : List Bool)
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n)
    (prog : WordOracleComp Unit (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (M.signingOracle km q s)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (etmToMACHandler E n (tagBound n) ke))
        prog).run ())).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (etmForgeJointOracle E M n ke km)) prog).run [])).map
      (fun (a, s') => ((a, ()), s'.map Prod.snd)) := by
  rw [ProbOracleComp.run_interpret_run_interpret, ProbOracleComp.eval_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (etmForgeJointOracle E M n ke km q s))
    (oracle' := fun q (state : Unit × List (List Bool)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingOracle km q s)))
        (etmToMACHandler E n (tagBound n) ke q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun s : List (List Bool × List Bool) => ((), s.map Prod.snd))
    (step := by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      change (ProbComp.eval (etmForgeJointOracle E M n ke km ((), msg) queriedPairs)).map
          (fun x => (x.1, (), x.2.map Prod.snd)) =
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (M.signingOracle km q s)))
          (etmToMACHandler E n (tagBound n) ke ((), msg) ())).run
            (queriedPairs.map Prod.snd)).map
          (fun result => (result.1.1, result.1.2, result.2))
      unfold etmForgeJointOracle etmToMACHandler
      by_cases hlenEq : (msg.length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          ProbOracleComp.run_interpret_sample, Probability.PMF.monad_bind_eq_bind,
          PMF.bind_map, Function.comp_def, PMF.map_bind, ProbComp.eval_bind,
          ProbComp.eval_pure]
        apply PMF.bind_congr_on_support
        intro c hc
        have hcLen : c.length = M.msgLen n := hctLen n ke hke msg (beq_iff_eq.mp hlenEq) c hc
        simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          _root_.PMF.monad_map_eq_map, MACScheme.signingOracle, ProbComp.eval_bind,
          ProbComp.eval_pure]
        dsimp only [StateT.run]
        simp only [PMF.map_bind, PMF.pure_map]
        apply PMF.bind_congr_on_support
        intro tag htag
        rw [List.take_of_length_le (htagBound km hkm c hcLen tag htag)]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    prog []
  dsimp only [List.map] at hsim
  have hsim' :=
    congrArg (PMF.map (fun result => ((result.1, result.2.1), result.2.2))) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'.symm

private theorem mem_support_etmForgeJointOracle (E : SymmetricCipher) (M : MACScheme)
    (n : ℕ) (ke km : List Bool) (prog : WordOracleComp Unit (List Bool))
    (result : List Bool) (queriedPairs : List (List Bool × List Bool))
    (hmem : (result, queriedPairs) ∈ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (etmForgeJointOracle E M n ke km)) prog).run [])).support) :
    ∀ pair ∈ queriedPairs,
      pair.1.length = n ∧ pair.2 ∈ (ProbComp.eval (E.encrypt n ke pair.1)).support := by
  rw [ProbOracleComp.eval_run_interpret] at hmem
  refine ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (etmForgeJointOracle E M n ke km q s))
    (fun s => ∀ pair ∈ s,
      pair.1.length = n ∧ pair.2 ∈ (ProbComp.eval (E.encrypt n ke pair.1)).support)
    ?_ prog [] (by simp) result queriedPairs hmem
  intro ⟨⟨⟩, msg⟩ s hs a s' hstep pair hpair
  unfold etmForgeJointOracle at hstep
  split_ifs at hstep with hlen
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
    obtain ⟨c, hc, tag, _, hpairEq⟩ := hstep
    cases hpairEq
    rcases List.mem_cons.mp hpair with rfl | htail
    · exact ⟨beq_iff_eq.mp hlen, hc⟩
    · exact hs pair htail
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hstep
    cases hstep
    exact hs pair hpair

/-- **Quantitative `EncForge` to `EUFCMA` bound for Encrypt-then-MAC**
([KatzLindell2020], Exercise 5.5, printed p. 191): when `tagBound n` bounds all MAC tag lengths on
`M.msgLen n`-bit ciphertexts under supported keys at security parameter `n`, the `encForgeGame`
winning probability of `adversary` against `encryptThenMAC E M hctLen` is at most the `eufCmaGame`
winning probability of `etmToMACForger E M tagBound adversary` against `M`. -/
theorem succProbability_encForgeGame_encryptThenMAC_le (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval ((encryptThenMAC E M hctLen).encForgeGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (M.eufCmaGame (etmToMACForger E M tagBound adversary) n)) := by
  simp only [Game.succProbability, SymmetricCipher.encForgeGame, MACScheme.eufCmaGame,
    etmToMACForger, ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret]
  have hinner (km : List Bool) :
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingOracle km q s)))
        (do
          let ke ← ProbOracleComp.sample (E.keyGen n)
          (fun out : List Bool × Unit =>
            if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
                (E.decrypt n ke (unframe out.1)).isSome then
              (unframe out.1, dropFrame out.1)
            else
              (if M.msgLen n == 0 then [false] else [], [])) <$>
            (OracleComp.interpret
              (OracleComp.sumHandler
                (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
                (etmToMACHandler E n (tagBound n) ke))
              (adversary n [])).run ())).run []).bind
        (fun out => PMF.pure
          ((out.1.1.length == M.msgLen n) && !out.2.contains out.1.1 &&
            M.verify km out.1.1 out.1.2)) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (M.signingOracle km q s)))
          ((OracleComp.interpret
            (OracleComp.sumHandler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (etmToMACHandler E n (tagBound n) ke))
            (adversary n [])).run ())).run []).bind
          (fun out => PMF.pure
            (let pair :=
              if (encPair encBits encBits (unframe out.1.1, dropFrame out.1.1) == out.1.1) &&
                  (E.decrypt n ke (unframe out.1.1)).isSome then
                (unframe out.1.1, dropFrame out.1.1)
              else
                (if M.msgLen n == 0 then [false] else [], [])
             (pair.1.length == M.msgLen n) && !out.2.contains pair.1 &&
               M.verify km pair.1 pair.2))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
    congr 1; funext ke
    rw [OracleComp.interpret_map, StateT.run_map]
    simp only [_root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  simp only [hinner]
  rw [PMF.bind_comm (ProbComp.eval (M.keyGen n))]
  have hkeyGen : ProbComp.eval ((encryptThenMAC E M hctLen).keyGen n) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun ke => ?_
  by_cases hke : ke ∈ (ProbComp.eval (E.keyGen n)).support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun km => ?_
    by_cases hkm : km ∈ (ProbComp.eval (M.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      rw [ ← ProbOracleComp.eval_run_interpret,
        eval_run_encForgeOracle_encryptThenMAC_eq E M hctLen n ke km (adversary n []),
        eval_run_etmToMACHandler_signingOracle_eq E M hctLen n tagBound ke km hke hkm
          htagBound (adversary n []),
        PMF.bind_map, PMF.bind_map]
      refine pmf_bind_pure_bool_le _ _ _ fun out hout hwin => ?_
      have hinv := mem_support_etmForgeJointOracle E M n ke km (adversary n []) out.1 out.2 hout
      have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      dsimp only [Function.comp_def, encryptThenMAC] at hwin ⊢
      rw [hunframe_k, hdrop_k] at hwin
      split_ifs at hwin with hcond
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwin hcond
        have hpairCond : ((encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
            (E.decrypt n ke (unframe out.1)).isSome) = true := by
          rw [Bool.and_eq_true]
          exact ⟨hcond.1.1, hwin.1⟩
        simp only [hpairCond, ↓reduceIte, hcond.1.2, hcond.2, Bool.true_and, Bool.and_true,
          Bool.not_eq_true']
        rw [Bool.eq_false_iff]
        intro hmemCt
        obtain ⟨pair, hpairMem, hpairSnd⟩ := List.mem_map.mp (List.contains_iff_mem.mp hmemCt)
        have ⟨hmsgLen, hctSupport⟩ := hinv pair hpairMem
        have hdec : E.decrypt n ke (unframe out.1) = some pair.1 := by
          rw [← hpairSnd]
          exact E.decrypt_encrypt n ke hke pair.1 hmsgLen pair.2 hctSupport
        have hmemMsg : ((E.decrypt n ke (unframe out.1)).getD []) ∈ out.2.map Prod.fst := by
          rw [hdec, Option.getD_some]
          exact List.mem_map_of_mem hpairMem
        have hcontainsMsg :
            (out.2.map Prod.fst).contains ((E.decrypt n ke (unframe out.1)).getD []) = true :=
          List.contains_iff_mem.mpr hmemMsg
        rw [hwin.2] at hcontainsMsg
        contradiction
      · simp at hwin
    · simp [(ProbComp.eval (M.keyGen n)).apply_eq_zero_iff km |>.mpr hkm]
  · simp [(ProbComp.eval (E.keyGen n)).apply_eq_zero_iff ke |>.mpr hke]

private theorem exists_mac_tag_length_bound' (M : MACScheme) :
    ∃ tagBound : ℕ → ℕ,
      ComputableInPolyTime tagBound encUnary encUnary ∧
      ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
        ∀ c, c.length = M.msgLen n →
        ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n := by
  obtain ⟨ck, dk, hlenKey⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  have hmsgLen := M.msgLen_polyTime.tidy
  refine ⟨fun n => cs * (2 * (ck * (n + 1) ^ dk) + M.msgLen n + 2) ^ ds,
    .of_tidy (by fun_prop), fun n km hkm c hc tag htag => ?_⟩
  have hkmLen := hlenKey n km hkm
  have htagLen := hlenSign (km, c) tag htag
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkmLen
  simp only [length_encPair, encBits_apply, hc] at htagLen
  exact htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))

/-- **Encrypt-then-MAC `EncForge` security under `EUFCMA`**
([KatzLindell2020], Exercise 5.5, printed p. 191): if `M` satisfies ordinary fresh-message
existential unforgeability (`M.EUFCMA`), then `encryptThenMAC E M hctLen` satisfies fresh-message
encryption unforgeability (`EncForge`), without requiring `M.SUFCMA` or `E.INDCPA`. -/
theorem encForge_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (heuf : M.EUFCMA) :
    (encryptThenMAC E M hctLen).EncForge := by
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := exists_mac_tag_length_bound' M
  apply SymmetricCipher.EncForge.of_negligible
  intro adversary hadversary
  refine negligible_of_le
    (heuf.negligible (etmToMACForger E M tagBound adversary)
      (isOraclePPT_etmToMACForger E M htagBoundPoly hadversary)) fun n => ?_
  exact succProbability_encForgeGame_encryptThenMAC_le E M hctLen tagBound adversary n (htagBound n)

/-! ### Katz–Lindell Exercise 5.10: `INDCPA ∧ EncForge` Does Not Imply `INDCCA`

Given any symmetric cipher `E`, `E.tailFallback` has the same `keyGen` and `encrypt` as `E`, and
decrypts `ct` by returning `E.decrypt n k ct` when it is `some msg`, or falling back to
`E.decrypt n k ct.tail` when `ct` is non-empty and `E.decrypt n k ct = none`. This preserves
`INDCPA`, `OneTimeINDCPA`, and `EncForge`, while unconditionally breaking
`OneTimeCiphertextIntegrity` and `CiphertextIntegrity` (and breaking `OneTimeINDCCA` and `INDCCA`
whenever `E.EncForge` holds, by querying decryption on `false :: ct`). -/

namespace SymmetricCipher

/-- Modified symmetric cipher `E.tailFallback` ([KatzLindell2020], Exercise 5.10, printed p. 192):
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

/-- `tailFallback` preserves `INDCPA` ([KatzLindell2020], Exercise 5.10, printed p. 192). -/
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
printed p. 192): any fresh-message forgery against `E.tailFallback` either already succeeds
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
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (E.encForgeOracle n k)) (adversary n [])).run [])).map fun out => (k, out)
  have hfb :
      ProbComp.eval (E.tailFallback.encForgeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((E.tailFallback.decrypt n p.1 p.2.1).isSome &&
            !p.2.2.contains ((E.tailFallback.decrypt n p.1 p.2.1).getD []))) := by
    simp only [encForgeGame, hkeyGen, horacle, runDist, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hdir :
      ProbComp.eval (E.encForgeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((E.decrypt n p.1 p.2.1).isSome &&
            !p.2.2.contains ((E.decrypt n p.1 p.2.1).getD []))) := by
    simp only [encForgeGame, runDist, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have htail :
      ProbComp.eval (E.encForgeGame (tailCIAdversary adversary) n) =
        runDist.bind (fun p => PMF.pure
          ((E.decrypt n p.1 p.2.1.tail).isSome &&
            !p.2.2.contains ((E.decrypt n p.1 p.2.1.tail).getD []))) := by
    simp only [encForgeGame, tailCIAdversary, runDist, OracleComp.interpret_map, StateT.run_map,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
  rw [hfb, hdir, htail]
  refine succProbability_bind_pure_bool_le_add runDist _ _ _ fun p _ hwin => ?_
  dsimp only [tailFallback] at hwin
  split_ifs at hwin with h1 h2
  · exact Or.inl hwin
  · simp at hwin
  · exact Or.inr hwin

/-- `tailFallback` preserves `EncForge` ([KatzLindell2020], Exercise 5.10, printed p. 192). -/
theorem EncForge.tailFallback {E : SymmetricCipher} (h : E.EncForge) :
    E.tailFallback.EncForge := by
  apply EncForge.of_negligible
  intro adversary hadversary
  have h1 := h.negligible adversary hadversary
  have h2 := h.negligible (tailCIAdversary adversary) (isOraclePPT_tailCIAdversary hadversary)
  exact negligible_of_le (h1.add h2) (E.succProbability_encForgeGame_tailFallback_le adversary)

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
  simp only [ciOneTimeGame, prependFalseBitCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (E.tailFallback.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    change k ∈ (ProbComp.eval (E.keyGen n)).support at hk
    unfold oneTimeCIEncryptionOracle
    dsimp only [StateT.run]
    simp only [List.isEmpty_nil, List.length_replicate, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (E.encrypt n k (List.replicate n bit))).bind _ = PMF.pure true
    trans (ProbComp.eval (E.encrypt n k (List.replicate n bit))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
      have htake : List.take (ctBound n) ct = ct :=
        List.take_of_length_le (hctBound k hk (List.replicate n bit) List.length_replicate ct hct)
      rw [htake, singleton_contains_false_cons,
        decrypt_tailFallback_false_cons_isSome E n k (List.replicate n bit) ct hk
          List.length_replicate hct]
      rfl
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

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
  simp only [ciGame, prependFalseBitCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (E.tailFallback.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    change k ∈ (ProbComp.eval (E.keyGen n)).support at hk
    unfold ciEncryptionOracle
    dsimp only [StateT.run]
    simp only [List.length_replicate, beq_self_eq_true, ↓reduceIte,
      ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (E.encrypt n k (List.replicate n bit))).bind _ = PMF.pure true
    trans (ProbComp.eval (E.encrypt n k (List.replicate n bit))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
      have htake : List.take (ctBound n) ct = ct :=
        List.take_of_length_le (hctBound k hk (List.replicate n bit) List.length_replicate ct hct)
      rw [htake, singleton_contains_false_cons,
        decrypt_tailFallback_false_cons_isSome E n k (List.replicate n bit) ct hk
          List.length_replicate hct]
      rfl
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- `E.tailFallback` never satisfies `OneTimeCiphertextIntegrity` ([KatzLindell2020],
Exercise 5.10, printed p. 192). -/
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
printed p. 192). -/
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
printed p. 192): queries left-or-right encryption on `(0^n, 1^n)` to obtain `ct`, queries
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
  simp only [encForgeGame, prependFalseBitCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  unfold encForgeOracle
  dsimp only [StateT.run]
  simp only [List.length_replicate, beq_self_eq_true, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
  have htake : List.take (ctBound n) ct = ct :=
    List.take_of_length_le (hctBound k hk (List.replicate n bit) List.length_replicate ct hct)
  rw [htake]

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
  have hunf : unframe (encPair encBits encBits
      (List.replicate n false, List.replicate n true)) = List.replicate n false := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop : dropFrame (encPair encBits encBits
      (List.replicate n false, List.replicate n true)) = List.replicate n true := by
    simp [encPair_apply, dropFrame_frame_append]
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by
    cases bit <;> rfl
  simp only [ccaOneTimeGame, tailFallbackCCAAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  change k ∈ (ProbComp.eval (E.keyGen n)).support at hk
  unfold oneTimeCCAOracle
  dsimp only [StateT.run]
  simp only [hunf, hdrop, hbit, List.isEmpty_nil, List.length_replicate, beq_self_eq_true,
    Bool.and_self, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  change (ProbComp.eval (E.encrypt n k (List.replicate n bit))).bind _ = _
  refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
  have htake : List.take (ctBound n) ct = ct :=
    List.take_of_length_le (hctBound k hk (List.replicate n bit) List.length_replicate ct hct)
  simp [htake]

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
([KatzLindell2020], Exercise 5.10, printed p. 192). -/
theorem not_oneTimeINDCCA_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.OneTimeINDCCA := by
  intro hcca
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hnegAdv := hcca (tailFallbackCCAAdversary ctBound)
    (isOraclePPT_tailFallbackCCAAdversary hctBoundPoly)
  have hnegF := hforge.negligible (prependFalseBitCIAdversary false ctBound)
    (isOraclePPT_prependFalseBitCIAdversary false hctBoundPoly)
  have hnegT := hforge.negligible (prependFalseBitCIAdversary true ctBound)
    (isOraclePPT_prependFalseBitCIAdversary true hctBoundPoly)
  have hnegSum := (hnegAdv.add hnegF).add hnegT
  have hconst : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := by
    refine negligible_of_eventually_le hnegSum (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    rw [← NNReal.coe_le_coe]
    simp only [Pi.add_apply, NNReal.coe_add, NNReal.coe_one]
    have htrue := one_le_succProbability_ccaOneTimeGame_tailFallback_true E ctBound n (hctBound n)
    have hfalse := succProbability_ccaOneTimeGame_tailFallback_false_le E ctBound n hn (hctBound n)
    have htrueR : (1 : ℝ) ≤
        (Game.succProbability
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n)) : ℝ) +
        (Game.succProbability
          (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary true ctBound) n)) : ℝ) :=
      by exact_mod_cast htrue
    have hfalseR :
        (Game.succProbability
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n)) : ℝ) ≤
        (Game.succProbability
          (ProbComp.eval (E.encForgeGame (prependFalseBitCIAdversary false ctBound) n)) : ℝ) :=
      by exact_mod_cast hfalse
    have hadvR :
        (Game.succProbability
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n)) : ℝ) -
        (Game.succProbability
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n)) : ℝ) ≤
        (Game.advantage
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) false n))
          (ProbComp.eval
            (E.tailFallback.ccaOneTimeGame (tailFallbackCCAAdversary ctBound) true n)) : ℝ) := by
      rw [Game.coe_advantage, abs_sub_comm]
      exact le_abs_self _
    linarith
  exact not_negligible_const one_ne_zero hconst

/-- **If `E.EncForge` holds, then `E.tailFallback` fails `INDCCA`**
([KatzLindell2020], Exercise 5.10, printed p. 192). -/
theorem not_indcca_tailFallback {E : SymmetricCipher} (hforge : E.EncForge) :
    ¬ E.tailFallback.INDCCA :=
  fun hcca => not_oneTimeINDCCA_tailFallback hforge hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.10 counterexample**
([KatzLindell2020], Exercise 5.10, printed p. 192): from any `INDCPA` and `EncForge` symmetric
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
  ([KatzLindell2020], Exercise 5.4, printed p. 191). -/

namespace MACScheme

/-- **Redundant-tag MAC transformation** ([KatzLindell2020], Exercise 5.4, printed p. 191):
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

/-- `tailTagForger` preserves any per-input query-count bound `IsQueryBounded Q`. -/
theorem isQueryBounded_tailTagForger (adversary : Forger) (n : ℕ) (aux : List Bool)
    {Q : ℕ} (hq : (adversary n aux).IsQueryBounded Q) :
    (tailTagForger adversary n aux).IsQueryBounded Q := by
  simpa only [tailTagForger, OracleComp.isCostBounded_map_iff] using hq

/-- **Quantitative `EUFCMA` bound for `M.redundantTag`** ([KatzLindell2020], Exercise 5.4,
printed p. 191): any fresh-message forgery against `M.redundantTag` either succeeds directly
against `M` or succeeds after stripping the leading bit of the tag via `tailTagForger`. -/
theorem succProbability_eufCmaGame_redundantTag_le (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.redundantTag.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) +
        Game.succProbability (ProbComp.eval (M.eufCmaGame (tailTagForger adversary) n)) := by
  have horacle (sk : List Bool) :
      M.redundantTag.signingOracle sk = M.signingOracle sk := rfl
  have hkeyGen : M.redundantTag.keyGen = M.keyGen := rfl
  have hmsgLen : M.redundantTag.msgLen = M.msgLen := rfl
  let runDist : PMF (List Bool × (List Bool × List Bool) × List (List Bool)) :=
    (ProbComp.eval (M.keyGen n)).bind fun sk =>
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (M.signingOracle sk)) (adversary n [])).run [])).map fun out => (sk, out)
  have hred :
      ProbComp.eval (M.redundantTag.eufCmaGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.redundantTag.verify p.1 p.2.1.1 p.2.1.2)) := by
    simp only [eufCmaGame, hkeyGen, horacle, hmsgLen, runDist, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hdir :
      ProbComp.eval (M.eufCmaGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2)) := by
    simp only [eufCmaGame, runDist, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have htail :
      ProbComp.eval (M.eufCmaGame (tailTagForger adversary) n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2.tail)) := by
    simp only [eufCmaGame, tailTagForger, runDist, OracleComp.interpret_map, StateT.run_map,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
  rw [hred, hdir, htail]
  refine succProbability_bind_pure_bool_le_add runDist _ _ _ fun p _ hwin => ?_
  dsimp only [redundantTag] at hwin
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hwin ⊢
  rcases hwin with ⟨⟨hlen, hfresh⟩, hver | ⟨_, hverTail⟩⟩
  · exact Or.inl ⟨⟨hlen, hfresh⟩, hver⟩
  · exact Or.inr ⟨⟨hlen, hfresh⟩, hverTail⟩

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
  let runDist : PMF (List Bool × (List Bool × List Bool) × List (List Bool)) :=
    (ProbComp.eval (M.keyGen n)).bind fun sk =>
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (M.oneTimeSigningOracle sk)) (adversary n [])).run [])).map fun out => (sk, out)
  have hred :
      ProbComp.eval (M.redundantTag.eufOneTimeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.redundantTag.verify p.1 p.2.1.1 p.2.1.2)) := by
    simp only [eufOneTimeGame, hkeyGen, horacle, hmsgLen, runDist, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hdir :
      ProbComp.eval (M.eufOneTimeGame adversary n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2)) := by
    simp only [eufOneTimeGame, runDist, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have htail :
      ProbComp.eval (M.eufOneTimeGame (tailTagForger adversary) n) =
        runDist.bind (fun p => PMF.pure
          ((p.2.1.1.length == M.msgLen n) && !p.2.2.contains p.2.1.1 &&
            M.verify p.1 p.2.1.1 p.2.1.2.tail)) := by
    simp only [eufOneTimeGame, tailTagForger, runDist, OracleComp.interpret_map, StateT.run_map,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
  rw [hred, hdir, htail]
  refine succProbability_bind_pure_bool_le_add runDist _ _ _ fun p _ hwin => ?_
  dsimp only [redundantTag] at hwin
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hwin ⊢
  rcases hwin with ⟨⟨hlen, hfresh⟩, hver | ⟨_, hverTail⟩⟩
  · exact Or.inl ⟨⟨hlen, hfresh⟩, hver⟩
  · exact Or.inr ⟨⟨hlen, hfresh⟩, hverTail⟩

/-- `redundantTag` preserves `EUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 191). -/
theorem EUFCMA.redundantTag {M : MACScheme} (h : M.EUFCMA) : M.redundantTag.EUFCMA := by
  apply EUFCMA.of_negligible
  intro adversary hadversary
  have h1 := h.negligible adversary hadversary
  have h2 := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  exact negligible_of_le (h1.add h2) (M.succProbability_eufCmaGame_redundantTag_le adversary)

/-- `redundantTag` preserves `OneTimeEUFCMA`. -/
theorem OneTimeEUFCMA.redundantTag {M : MACScheme} (h : M.OneTimeEUFCMA) :
    M.redundantTag.OneTimeEUFCMA := by
  apply OneTimeEUFCMA.of_negligible
  intro adversary hadversary
  have h1 := h.negligible adversary hadversary
  have h2 := h.negligible (tailTagForger adversary) (isOraclePPT_tailTagForger hadversary)
  exact negligible_of_le (h1.add h2)
    (M.succProbability_eufOneTimeGame_redundantTag_le adversary)

/-- Every `MACScheme` admits a plain polynomial-time bound `tagBound : ℕ → ℕ` on the length of tags
produced on `M.msgLen n`-bit messages under keys sampled from `M.keyGen n`. -/
theorem exists_tag_length_bound_of_length_eq (M : MACScheme) :
    ∃ tagBound : ℕ → ℕ,
      ComputableInPolyTime tagBound encUnary encUnary ∧
      ∀ n, ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
        ∀ msg, msg.length = M.msgLen n →
        ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n := by
  obtain ⟨ck, dk, hlenk⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := M.sign_ppt.length_le
  refine ⟨fun n => cs * (2 * (ck * (n + 1) ^ dk) + M.msgLen n + 2) ^ ds, by fun_prop,
    fun n sk hsk msg hmsg tag htag => ?_⟩
  have hskLen := hlenk n sk hsk
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hskLen
  have h1 := hlens (sk, msg) tag htag
  simp only [length_encPair, encBits_apply, hmsg] at h1
  exact h1.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))

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
  simp only [sufOneTimeGame, redundantTagForger,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (M.redundantTag.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
    change sk ∈ (ProbComp.eval (M.keyGen n)).support at hsk
    unfold oneTimeSigningPairOracle
    dsimp only [StateT.run]
    simp only [List.isEmpty_nil, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (M.sign sk (List.replicate (M.msgLen n) false))).bind _ = PMF.pure true
    trans (ProbComp.eval (M.sign sk (List.replicate (M.msgLen n) false))).bind
      (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
      have htake : List.take (tagBound n) tag = tag :=
        List.take_of_length_le
          (htagBound sk hsk (List.replicate (M.msgLen n) false) List.length_replicate tag htag)
      have hver := M.verify_sign n sk hsk (List.replicate (M.msgLen n) false)
        List.length_replicate tag htag
      simp [redundantTag, htake, hver]
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- In `sufCmaGame` against `M.redundantTag`, `M.redundantTagForger tagBound` wins with probability
`1` at every security parameter `n` where `tagBound n` bounds tag lengths. -/
theorem eval_sufCmaGame_redundantTag_redundantTagForger (M : MACScheme)
    (tagBound : ℕ → ℕ) (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.redundantTag.sufCmaGame (M.redundantTagForger tagBound) n) =
      PMF.pure true := by
  simp only [sufCmaGame, redundantTagForger,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (M.redundantTag.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
    change sk ∈ (ProbComp.eval (M.keyGen n)).support at hsk
    unfold signingPairOracle
    dsimp only [StateT.run]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
      PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (M.sign sk (List.replicate (M.msgLen n) false))).bind _ = PMF.pure true
    trans (ProbComp.eval (M.sign sk (List.replicate (M.msgLen n) false))).bind
      (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
      have htake : List.take (tagBound n) tag = tag :=
        List.take_of_length_le
          (htagBound sk hsk (List.replicate (M.msgLen n) false) List.length_replicate tag htag)
      have hver := M.verify_sign n sk hsk (List.replicate (M.msgLen n) false)
        List.length_replicate tag htag
      simp [redundantTag, htake, hver]
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- `M.redundantTag` never satisfies `OneTimeSUFCMA` ([KatzLindell2020], Exercise 5.4,
printed p. 191). -/
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

/-- `M.redundantTag` never satisfies `SUFCMA` ([KatzLindell2020], Exercise 5.4, printed p. 191). -/
theorem not_sufCma_redundantTag (M : MACScheme) :
    ¬ M.redundantTag.SUFCMA :=
  fun h => M.not_oneTimeSUFCMA_redundantTag h.oneTimeSUFCMA

end MACScheme

/-- If `M.EUFCMA` holds, then `encryptThenMAC E M.redundantTag hctLen` satisfies `EncForge`
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
theorem encForge_encryptThenMAC_redundantTag (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n)
    (heuf : M.EUFCMA) :
    (encryptThenMAC E M.redundantTag hctLen).EncForge :=
  encForge_encryptThenMAC E M.redundantTag hctLen heuf.redundantTag

/-- One-query ciphertext-integrity adversary against `encryptThenMAC E M.redundantTag hctLen`
([KatzLindell2020], Exercise 5.4, printed p. 191): queries encryption on `0^n` (truncating the
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
  let ETM := encryptThenMAC E M.redundantTag hctLen
  simp only [SymmetricCipher.ciOneTimeGame, etmRedundantCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (ETM.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    unfold SymmetricCipher.oneTimeCIEncryptionOracle
    dsimp only [StateT.run]
    simp only [List.isEmpty_nil, List.length_replicate, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (ETM.encrypt n k (List.replicate n false))).bind _ = PMF.pure true
    trans (ProbComp.eval (ETM.encrypt n k (List.replicate n false))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
      have htake : List.take (ctBound n) ct = ct :=
        List.take_of_length_le
          (hctBound k hk (List.replicate n false) List.length_replicate ct hct)
      have hkSupp :
          k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support := hk
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkSupp
      obtain ⟨ke, hke, km, hkm, rfl⟩ := hkSupp
      have hctSupp : ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n
          (encPair encBits encBits (ke, km)) (List.replicate n false))).support := hct
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hctSupp
      obtain ⟨c, hc, tag, htag, rfl⟩ := hctSupp
      have hunfK : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdropK : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      rw [hunfK] at hc
      rw [hdropK] at htag
      have hunfCt : unframe (encPair encBits encBits (c, tag)) = c := by
        simp [encPair_apply, unframe_frame_append]
      have hdropCt : dropFrame (encPair encBits encBits (c, tag)) = tag := by
        simp [encPair_apply, dropFrame_frame_append]
      have hdec := decrypt_encryptThenMAC_redundantTag_false_cons E M hctLen n ke km
        (List.replicate n false) c tag hke hkm List.length_replicate hc htag
      have hnotMem := singleton_encPair_contains_false_cons c tag
      rw [htake, hunfCt, hdropCt, hnotMem, hdec]
      rfl
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

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
  let ETM := encryptThenMAC E M.redundantTag hctLen
  simp only [SymmetricCipher.ciGame, etmRedundantCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  trans (ProbComp.eval (ETM.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    unfold SymmetricCipher.ciEncryptionOracle
    dsimp only [StateT.run]
    simp only [List.length_replicate, beq_self_eq_true, ↓reduceIte,
      ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (ETM.encrypt n k (List.replicate n false))).bind _ = PMF.pure true
    trans (ProbComp.eval (ETM.encrypt n k (List.replicate n false))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
      have htake : List.take (ctBound n) ct = ct :=
        List.take_of_length_le
          (hctBound k hk (List.replicate n false) List.length_replicate ct hct)
      have hkSupp :
          k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support := hk
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkSupp
      obtain ⟨ke, hke, km, hkm, rfl⟩ := hkSupp
      have hctSupp : ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n
          (encPair encBits encBits (ke, km)) (List.replicate n false))).support := hct
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hctSupp
      obtain ⟨c, hc, tag, htag, rfl⟩ := hctSupp
      have hunfK : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdropK : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      rw [hunfK] at hc
      rw [hdropK] at htag
      have hunfCt : unframe (encPair encBits encBits (c, tag)) = c := by
        simp [encPair_apply, unframe_frame_append]
      have hdropCt : dropFrame (encPair encBits encBits (c, tag)) = tag := by
        simp [encPair_apply, dropFrame_frame_append]
      have hdec := decrypt_encryptThenMAC_redundantTag_false_cons E M hctLen n ke km
        (List.replicate n false) c tag hke hkm List.length_replicate hc htag
      have hnotMem := singleton_encPair_contains_false_cons c tag
      rw [htake, hunfCt, hdropCt, hnotMem, hdec]
      rfl
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeCiphertextIntegrity`
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
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
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
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
([KatzLindell2020], Exercise 5.4, printed p. 191): queries left-or-right encryption on
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
  let ETM := encryptThenMAC E M.redundantTag hctLen
  have hunf : unframe (encPair encBits encBits
      (List.replicate n false, List.replicate n true)) = List.replicate n false := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop : dropFrame (encPair encBits encBits
      (List.replicate n false, List.replicate n true)) = List.replicate n true := by
    simp [encPair_apply, dropFrame_frame_append]
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by
    cases bit <;> rfl
  simp only [SymmetricCipher.ccaOneTimeGame, etmRedundantCCAAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  trans (ProbComp.eval (ETM.keyGen n)).bind
    (fun _ => PMF.pure
      (List.take (n + 1) (encOption encBits (some (List.replicate n bit))) ==
        encOption encBits (some (List.replicate n true))))
  · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    unfold SymmetricCipher.oneTimeCCAOracle
    dsimp only [StateT.run]
    simp only [hunf, hdrop, hbit, List.isEmpty_nil, List.length_replicate, beq_self_eq_true,
      Bool.and_self, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    change (ProbComp.eval (ETM.encrypt n k (List.replicate n bit))).bind _ = _
    trans (ProbComp.eval (ETM.encrypt n k (List.replicate n bit))).bind
      (fun _ => PMF.pure
        (List.take (n + 1) (encOption encBits (some (List.replicate n bit))) ==
          encOption encBits (some (List.replicate n true))))
    · refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
      have htake : List.take (ctBound n) ct = ct :=
        List.take_of_length_le
          (hctBound k hk (List.replicate n bit) List.length_replicate ct hct)
      have hkSupp :
          k ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).keyGen n)).support := hk
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkSupp
      obtain ⟨ke, hke, km, hkm, rfl⟩ := hkSupp
      have hctSupp : ct ∈ (ProbComp.eval ((encryptThenMAC E M.redundantTag hctLen).encrypt n
          (encPair encBits encBits (ke, km)) (List.replicate n bit))).support := hct
      simp only [encryptThenMAC, MACScheme.redundantTag, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hctSupp
      obtain ⟨c, hc, tag, htag, rfl⟩ := hctSupp
      have hunfK : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdropK : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      rw [hunfK] at hc
      rw [hdropK] at htag
      have hunfCt : unframe (encPair encBits encBits (c, tag)) = c := by
        simp [encPair_apply, unframe_frame_append]
      have hdropCt : dropFrame (encPair encBits encBits (c, tag)) = tag := by
        simp [encPair_apply, dropFrame_frame_append]
      have hdec := decrypt_encryptThenMAC_redundantTag_false_cons E M hctLen n ke km
        (List.replicate n bit) c tag hke hkm List.length_replicate hc htag
      have hnotMem := singleton_encPair_contains_false_cons c tag
      rw [htake, hunfCt, hdropCt, hnotMem, hdec]
      simp [ProbComp.eval_pure]
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `OneTimeINDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
theorem not_oneTimeINDCCA_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).OneTimeINDCCA := by
  intro hcca
  let ETM := encryptThenMAC E M.redundantTag hctLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := ETM.exists_ciphertext_length_bound_of_length_eq
  have hneg := hcca (etmRedundantCCAAdversary ctBound)
    (isOraclePPT_etmRedundantCCAAdversary hctBoundPoly)
  have hconst : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := by
    refine negligible_of_eventually_le hneg (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    have h0 := eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
      E M hctLen false ctBound n (hctBound n)
    have h1 := eval_ccaOneTimeGame_encryptThenMAC_redundantTag_etmRedundantCCAAdversary
      E M hctLen true ctBound n (hctBound n)
    have htake0 : List.take (n + 1) (encOption encBits (some (List.replicate n false))) =
        encOption encBits (some (List.replicate n false)) := by
      apply List.take_of_length_le
      simp [encOption_some, encBits_apply]
    have htake1 : List.take (n + 1) (encOption encBits (some (List.replicate n true))) =
        encOption encBits (some (List.replicate n true)) := by
      apply List.take_of_length_le
      simp [encOption_some, encBits_apply]
    have hbeq0 : (encOption encBits (some (List.replicate n false)) ==
        encOption encBits (some (List.replicate n true))) = false := by
      rw [Bool.eq_false_iff]
      intro h
      have heq := Option.some.inj ((encOption encBits).injective (beq_iff_eq.mp h))
      cases n with
      | zero => contradiction
      | succ m => simp at heq
    rw [htake0, hbeq0] at h0
    rw [htake1, beq_self_eq_true] at h1
    change (1 : ℝ≥0) ≤ Game.advantage
      (ProbComp.eval (ETM.ccaOneTimeGame (etmRedundantCCAAdversary ctBound) false n))
      (ProbComp.eval (ETM.ccaOneTimeGame (etmRedundantCCAAdversary ctBound) true n))
    rw [h0, h1, Game.advantage_comm, Game.advantage_pure_false]
    simp [Game.succProbability]
  exact not_negligible_const one_ne_zero hconst

/-- `encryptThenMAC E M.redundantTag hctLen` never satisfies `INDCCA`
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
theorem not_indcca_encryptThenMAC_redundantTag
    (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = M.msgLen n) :
    ¬ (encryptThenMAC E M.redundantTag hctLen).INDCCA :=
  fun hcca =>
    not_oneTimeINDCCA_encryptThenMAC_redundantTag E M hctLen hcca.oneTimeINDCCA

/-- **Katz–Lindell Exercise 5.4 counterexample** ([KatzLindell2020], Exercise 5.4, printed p. 191):
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
([KatzLindell2020], Exercise 5.4, printed p. 191). -/
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
