/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Fresh-Message Encryption Unforgeability

This module defines fresh-message encryption unforgeability (`EncForge`) for symmetric ciphers,
following [Katz and Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
Section 5.2, Definition 5.2 (printed p. 151). In `encForgeGame`, an adaptive `CIAdversary` queries
an encryption oracle on `n`-bit plaintexts (logging the queried plaintexts `queriedMsgs`) and wins
by outputting a candidate ciphertext `ct` that decrypts to `some m` for a fresh plaintext
`!queriedMsgs.contains m`.

Ciphertext integrity (`ciGame`, [BonehShoup2023], Definition 9.1) implies `EncForge`
(`succProbability_encForgeGame_le_ciGame`, `CiphertextIntegrity.encForge`). For
`encryptThenMAC E M hctLen`, ordinary fresh-message MAC unforgeability (`M.EUFCMA`, without
`M.SUFCMA`) already suffices for `(encryptThenMAC E M hctLen).EncForge`
(`succProbability_encForgeGame_encryptThenMAC_le`, `encForge_encryptThenMAC`, [KatzLindell2020],
Exercise 5.5, printed p. 165).

The generic composition separations stated in terms of `EncForge` are in
`CslibFrontier/Crypto/Computational/Encryption/CompositionCounterexamples.lean`.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.encForgeOracle`, `encForgeGame`, `EncForge`: fresh-message
  encryption unforgeability experiment and security predicate ([KatzLindell2020], Definition 5.2).
* `Cslib.Crypto.SymmetricCipher.ciPairOracle`: encryption oracle logging `(msg, ct)` pairs, whose
  two projections recover `encForgeOracle` and `ciEncryptionOracle`.

## Main results

* `Cslib.Crypto.SymmetricCipher.isPPTOn_encForgeGame`, `isPPT_encForgeGame`: the experiment is
  uniformly strict PPT.
* `Cslib.Crypto.SymmetricCipher.succProbability_encForgeGame_le_ciGame`,
  `Cslib.Crypto.SymmetricCipher.CiphertextIntegrity.encForge`: ciphertext integrity implies
  fresh-message encryption unforgeability.
* `Cslib.Crypto.succProbability_encForgeGame_encryptThenMAC_le`,
  `Cslib.Crypto.encForge_encryptThenMAC`: Encrypt-then-MAC with an `EUFCMA`-secure MAC satisfies
  `EncForge` ([KatzLindell2020], Exercise 5.5).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 5.2 (Definition 5.2, p. 151) and Exercise 5.5 (p. 165).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 9.1 and 9.4.1 (pp. 358–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace SymmetricCipher

/-! ### Fresh-Message Encryption Unforgeability (`encForgeGame`, `EncForge`, KL Definition 5.2) -/

/-- Stateful encryption oracle for the fresh-message encryption unforgeability game
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 151): if `request.2.length == n`,
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
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 151): sample `k ← E.keyGen n`, run
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
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        p.2.1.2.length == p.1.1)
      EIn encBool :=
    ComputableInPolyTime.unary_beq'
      (by dsimp only [EIn]; fun_prop) (by dsimp only [EIn]; fun_prop)
  have hencArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, p.2.1.2 :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg).bind_with
      ((by dsimp only [EIn]; fun_prop : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.1.2.1.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.encForgeOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold encForgeOracle
    exact IsPPTOn.cond' hcond hyes hno
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

private theorem computableInPolyTime_encForgePost (E : SymmetricCipher) :
    ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome &&
          !pair.2.2.contains ((E.decrypt pair.1.1 pair.1.2 pair.2.1).getD []))
      (encPair (encPair encUnary encBits) (encPair encBits (encList encBits))) encBool := by
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hdecArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        E.decrypt pair.1.1 pair.1.2 pair.2.1)
      EOut (encOption encBits) :=
    E.decrypt_polyTime.comp hdecArg
  have hisSome := hdec.optionIsSome
  have hgetD := ComputableInPolyTime.optionGetDWithInput hdec (ComputableInPolyTime.const [])
  have hlist : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.2)
      EOut (encList encBits) := by
    dsimp only [EOut]; fun_prop
  have hcontains := ComputableInPolyTime.contains hlist hgetD
  exact ComputableInPolyTime.bool_and.comp
    (hisSome.prod (ComputableInPolyTime.bool_not.comp hcontains))

/-- The fresh-message encryption unforgeability experiment is uniformly strict PPT in the unary
security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_encForgeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.encForgeGame adversary) := by
  have hrun := E.isPPTOn_run_encForgeOracle hadversary
  unfold encForgeGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with E.computableInPolyTime_encForgePost.isPPTOn)

/-- The fresh-message encryption unforgeability experiment is uniformly strict PPT, independently of
unused auxiliary input. -/
@[program_certificate]
theorem isPPT_encForgeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.encForgeGame adversary n) :=
  ((E.isPPTOn_encForgeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Fresh-message encryption unforgeability (`EncForge`, or KL Definition 5.2)
([KatzLindell2020], Section 5.2, Definition 5.2, printed p. 151): every uniform strict
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
    refine Probability.PMF.map_true_mono _ fun out hout hwin => ?_
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
private noncomputable def etmForgeJointOracle (E : SymmetricCipher) (M : MACScheme) (n : ℕ)
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
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
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
      rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
      split_ifs <;> simp [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
        PMF.map_comp, Function.comp_def])
    prog []).symm

private theorem eval_run_etmToMACHandler_signingOracle_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
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
([KatzLindell2020], Exercise 5.5, printed p. 165): when `tagBound n` bounds all MAC tag lengths on
`M.msgLen n`-bit ciphertexts under supported keys at security parameter `n`, the `encForgeGame`
winning probability of `adversary` against `encryptThenMAC E M hctLen` is at most the `eufCmaGame`
winning probability of `etmToMACForger E M tagBound adversary` against `M`. -/
theorem succProbability_encForgeGame_encryptThenMAC_le (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
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
      refine Probability.PMF.map_true_mono _ fun out hout hwin => ?_
      have hinv := mem_support_etmForgeJointOracle E M n ke km (adversary n []) out.1 out.2 hout
      dsimp only [Function.comp_def, encryptThenMAC] at hwin ⊢
      rw [unframe_encPair_encBits, dropFrame_encPair_encBits] at hwin
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

/-- **Encrypt-then-MAC `EncForge` security under `EUFCMA`**
([KatzLindell2020], Exercise 5.5, printed p. 165): if `M` satisfies ordinary fresh-message
existential unforgeability (`M.EUFCMA`), then `encryptThenMAC E M hctLen` satisfies fresh-message
encryption unforgeability (`EncForge`), without requiring `M.SUFCMA` or `E.INDCPA`. -/
theorem encForge_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n, E.CiphertextLength n (M.msgLen n))
    (heuf : M.EUFCMA) :
    (encryptThenMAC E M hctLen).EncForge := by
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := M.exists_tag_length_bound_of_length_eq
  apply SymmetricCipher.EncForge.of_negligible
  intro adversary hadversary
  refine negligible_of_le
    (heuf.negligible (etmToMACForger E M tagBound adversary)
      (isOraclePPT_etmToMACForger E M htagBoundPoly hadversary)) fun n => ?_
  exact succProbability_encForgeGame_encryptThenMAC_le E M hctLen tagBound adversary n (htagBound n)

end Cslib.Crypto
