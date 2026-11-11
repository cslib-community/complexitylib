/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Real/Ideal Authenticated Encryption

This module formalizes the single-oracle real-versus-ideal definition of authenticated encryption
([Katz and Lindell, Definition 5.4][KatzLindell2020]) for a `SymmetricCipher`, and proves that it is
equivalent to adaptive chosen-ciphertext security together with ciphertext integrity
([Katz and Lindell, Theorem 5.5][KatzLindell2020]).

The adversary is a `CCAAdversary`: it queries one oracle with an encryption channel (`false`) and a
decryption channel (`true`). In the real world, an encryption query on an `n`-bit message returns a
fresh encryption of that message, and a decryption query returns the encoded decryption
`encOption encBits (E.decrypt n k ct)`. In the ideal world, an encryption query on an `n`-bit
message returns an encryption of the all-zero message, and every decryption query returns `[]`, the
encoding of rejection. A cipher satisfies `RealIdealAE` when no oracle-PPT adversary tells the two
worlds apart with non-negligible advantage.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.aeRealOracle`, `Cslib.Crypto.SymmetricCipher.aeIdealOracle`: the
  real and ideal two-channel oracles.
* `Cslib.Crypto.SymmetricCipher.aeRealGame`, `Cslib.Crypto.SymmetricCipher.aeIdealGame`: run an
  adversary against them under a fresh key.
* `Cslib.Crypto.SymmetricCipher.RealIdealAE`: real/ideal authenticated encryption.
* `Cslib.Crypto.SymmetricCipher.cpaToAEAdversary`, `Cslib.Crypto.SymmetricCipher.ciToAEAdversary`,
  `Cslib.Crypto.SymmetricCipher.aeToCCAAdversary`: the reductions used in the two directions.

## Main results

* `Cslib.Crypto.SymmetricCipher.advantage_cpaGame_le_aeRealGame_aeIdealGame`: the CPA advantage is
  at most the sum of two real/ideal advantages.
* `Cslib.Crypto.SymmetricCipher.succProbability_ciGame_eq_advantage_aeRealGame_aeIdealGame`: the
  ciphertext-integrity winning probability equals a real/ideal advantage.
* `Cslib.Crypto.SymmetricCipher.advantage_aeRealGame_aeIdealGame_le`: the real/ideal advantage is
  at most a CCA advantage plus a polynomial multiple of a ciphertext-integrity winning probability.
* `Cslib.Crypto.SymmetricCipher.realIdealAE_iff_indcca_and_ciphertextIntegrity`,
  `Cslib.Crypto.SymmetricCipher.realIdealAE_iff_authenticatedEncryption`: the two definitions of
  authenticated encryption are equivalent ([Katz and Lindell, Theorem 5.5][KatzLindell2020]).

## Implementation notes

* Katz and Lindell select the world with a hidden bit and bound the probability of guessing it by
  `1/2` plus a negligible function. This is equivalent to the two-world indistinguishability used
  here, which is also how `INDCPA` and `INDCCA` are stated.
* Katz and Lindell forbid decryption queries on ciphertexts returned by the encryption oracle. Here
  the real oracle records every ciphertext it returns and answers such a query with `[]`, the same
  reply as the ideal oracle, so these queries carry no information.
* Messages have length `n`, so the all-zero message is `List.replicate n false`. Encryption
  queries on messages of any other length return `[]` in both worlds.
* Katz and Lindell state Theorem 5.5 with unforgeability, where a forgery must decrypt to a message
  that was never queried. The equivalence here uses the library's `CiphertextIntegrity`, where a
  forgery only has to be a fresh ciphertext that decrypts. By decryption completeness every
  unforgeability break is also a ciphertext-integrity break.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Definition 5.4 and Theorem 5.5
  (pp. 152–153)][KatzLindell2020]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace SymmetricCipher

/-! ### The real and ideal worlds -/

/-- Real-world oracle of the authenticated-encryption experiment
([Katz and Lindell, Definition 5.4][KatzLindell2020]). Its state is the list of ciphertexts
returned so far.
* On an encryption query `(false, msg)` with `msg.length = n`, encrypt `msg` under `k`, record the
  ciphertext and return it; on other lengths return `[]`.
* On a decryption query `(true, ct)`, return `[]` if `ct` was returned by an earlier encryption
  query, and `encOption encBits (E.decrypt n k ct)` otherwise. -/
@[expose]
noncomputable def aeRealOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      if request.2.length == n then do
        let ct ← E.encrypt n k request.2
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- Ideal-world oracle of the authenticated-encryption experiment
([Katz and Lindell, Definition 5.4][KatzLindell2020]): an encryption query `(false, msg)` with
`msg.length = n` returns an encryption of the all-zero message `List.replicate n false`, other
encryption queries return `[]`, and every decryption query `(true, _)` returns `[]`, the encoding of
rejection. -/
@[expose]
noncomputable def aeIdealOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Bool × List Bool) : StateT Unit ProbComp (List Bool) :=
  fun _ =>
    if request.1 then
      return ([], ())
    else
      if request.2.length == n then do
        let ct ← E.encrypt n k (List.replicate n false)
        return (ct, ())
      else
        return ([], ())

/-- The real-world authenticated-encryption experiment: sample `k ← E.keyGen n` and run
`adversary n []` against `E.aeRealOracle n k`, starting with no recorded ciphertexts. -/
@[expose]
noncomputable def aeRealGame (E : SymmetricCipher) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.aeRealOracle n k)) (adversary n [])).run []
  return out.1

/-- The ideal-world authenticated-encryption experiment: sample `k ← E.keyGen n` and run
`adversary n []` against `E.aeIdealOracle n k`. -/
@[expose]
noncomputable def aeIdealGame (E : SymmetricCipher) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.aeIdealOracle n k)) (adversary n [])).run ()
  return out.1

/-- Real/ideal authenticated encryption ([Katz and Lindell, Definition 5.4][KatzLindell2020]):
every `IsOraclePPT encBool` adversary distinguishes `aeRealGame` from `aeIdealGame` with only
negligible advantage. -/
@[expose]
def RealIdealAE (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.aeRealGame adversary n))
    (fun adversary n => ProbComp.eval (E.aeIdealGame adversary n))
    (IsOraclePPT encBool)

/-! ### Real/ideal security implies CPA security -/

/-- Stateful handler for `cpaToAEAdversary`: a left-or-right request `req` whose two messages
`unframe req` and `dropFrame req` both have length `n` is sent to the encryption channel as
`(false, if bit then dropFrame req else unframe req)`, with the reply truncated to `ctBound`; other
requests return `[]`. -/
@[expose]
noncomputable def cpaToAEHandler (n ctBound : ℕ) (bit : Bool) (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Bool) (List Bool) :=
  fun _ =>
    if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
      (fun ct => (ct, ())) <$> (List.take ctBound <$>
        ProbOracleComp.query (false, if bit then dropFrame request.2 else unframe request.2))
    else
      pure ([], ())

/-- Reduction from `cpaGame` to the real/ideal experiment: run the CPA distinguisher against
`cpaToAEHandler n (ctBound n) bit`, which answers each left-or-right request by encrypting the
message chosen by the fixed `bit`. -/
@[expose]
noncomputable def cpaToAEAdversary (ctBound : ℕ → ℕ) (bit : Bool)
    (adversary : OracleDistinguisher) : CCAAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (cpaToAEHandler n (ctBound n) bit))
      (adversary n [])).run ()
    return out.1

/-- Running an oracle-PPT program against a stateless handler is oracle PPT when the handler is
oracle PPT and its replies at parameter `n` to a request `(op, word)` have length at most
`bound n word`. This is the common step of the three admissibility proofs of this module. -/
private theorem isOraclePPTOn_run_unitHandler {Operation β : Type} [DecidableEq Operation]
    {operationEncoding : Operation ↪ List Bool} {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β} (hprogram : IsOraclePPT output program)
    {handler : ℕ → Operation × List Bool → StateT Unit (WordOracleComp Bool) (List Bool)}
    {bound : ℕ → List Bool → ℕ}
    (hhandler : IsOraclePPTOn (encPair (encPair encUnary encBits)
        (encPair (encPair operationEncoding encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Operation × List Bool) × Unit) =>
        handler pair.1.1 pair.2.1 pair.2.2))
    (hbound : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => bound pair.1.1 pair.2)
      (encPair (encPair encUnary encBits) encBits) encUnary)
    (hreply : ∀ n request state, ∀ result ∈ OracleComp.support (handler n request state),
      result.1.length ≤ bound n request.2) :
    IsOraclePPTOn (encPair encUnary encBits) (encPair output (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (handler caller.1))
          (program caller.1 [])).run ()) := by
  apply hprogram.run_interpret_preprocess_open'
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ()) (resources := fun caller word => bound caller.1 word)
    (by fun_prop) hhandler (ComputableInPolyTime.const ()) (fun _ _ => True) (fun _ => trivial)
    hbound
  intro caller request state _ result hresult
  refine ⟨trivial, hreply caller.1 request state result hresult, ?_⟩
  cases state
  obtain ⟨reply, ⟨⟩⟩ := result
  exact Nat.le_add_right _ _

/-- `cpaToAEAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_cpaToAEAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) (bit : Bool)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cpaToAEAdversary ctBound bit adversary) := by
  have hhandler : IsOraclePPTOn (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        cpaToAEHandler pair.1.1 (ctBound pair.1.1) bit pair.2.1 pair.2.2) := by
    ppt [cpaToAEHandler]
  have hreply (n : ℕ) (request : Unit × List Bool) (state : Unit) :
      ∀ result ∈ OracleComp.support (cpaToAEHandler n (ctBound n) bit request state),
        result.1.length ≤ ctBound n := by
    intro result hresult
    unfold cpaToAEHandler at hresult
    split at hresult
    · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      exact List.length_take_le _ _
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      simp
  have hrun := isOraclePPTOn_run_unitHandler (handler := fun n => cpaToAEHandler n (ctBound n) bit)
    (bound := fun n _ => ctBound n) hadversary hhandler (hctBound.comp (by fun_prop)) hreply
  unfold cpaToAEAdversary
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- One step of `cpaToAEHandler` against the real oracle, after forgetting all state, is one step
of the left-or-right CPA encryption oracle. -/
private theorem map_runWith_cpaToAEHandler (E : SymmetricCipher) (ctBound : ℕ → ℕ) (bit : Bool)
    (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (request : Unit × List Bool) (state : Unit × List (List Bool)) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeRealOracle n k q s))
        ((cpaToAEHandler n (ctBound n) bit request).run state.1) state.2).map
      (fun result => (result.1.1, result.1.2, result.2))).map (fun x => (x.1, ())) =
      ProbComp.eval (E.cpaEncryptionOracle n k bit request ()) := by
  simp only [StateT.run, cpaToAEHandler, cpaEncryptionOracle]
  by_cases hlenEq : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
  · simp only [hlenEq, ↓reduceIte, Functor.map_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, aeRealOracle, Bool.false_eq_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
      cases bit <;> simp [hlenEq]
    simp only [hmbLen, beq_self_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq]
    apply PMF.bind_congr_on_support
    intro ct hct
    rw [List.take_of_length_le (hctBound _ hmbLen ct hct)]
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      ProbOracleComp.runWith_pure, PMF.pure_map]

/-- Running `cpaToAEHandler` against the real oracle simulates the left-or-right CPA oracle. -/
private theorem map_runWith_cpaEncryptionOracle_eq (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (bit : Bool) (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    {α : Type} (program : WordOracleComp Unit α) :
    (ProbOracleComp.runWith
        (fun q state =>
          (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeRealOracle n k q s))
              ((cpaToAEHandler n (ctBound n) bit q).run state.1) state.2).map
            (fun result => (result.1.1, result.1.2, result.2)))
        program ((), [])).map (fun x => (x.1, ())) =
      ProbOracleComp.runWith (fun q u => ProbComp.eval (E.cpaEncryptionOracle n k bit q u))
        program () :=
  ProbOracleComp.runWith_map_state _ _ (fun _ => ())
    (map_runWith_cpaToAEHandler E ctBound bit n k hctBound) program ((), [])

/-- When `ctBound n` bounds the ciphertext lengths of `n`-bit messages, running
`cpaToAEAdversary ctBound bit adversary` in the real world has the same output distribution as
running `adversary` in `cpaGame` with challenge bit `bit`. -/
theorem eval_aeRealGame_cpaToAEAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.aeRealGame (cpaToAEAdversary ctBound bit adversary) n) =
      ProbComp.eval (E.cpaGame adversary bit n) := by
  simp only [aeRealGame, cpaGame, cpaToAEAdversary, runWith_norm, pmf_norm]
  peel_binds k
  rw [← map_runWith_cpaEncryptionOracle_eq E ctBound bit n k (hctBound k k_mem) (adversary n [])]
  simp only [pmf_norm]

/-- Against the ideal oracle, one step of `cpaToAEHandler` does not depend on the fixed bit: both
selectable messages have length `n`, and the ideal oracle encrypts the all-zero message. -/
private theorem runWith_aeIdealOracle_cpaToAEHandler (E : SymmetricCipher) (n c : ℕ)
    (k : List Bool) (request : Unit × List Bool) (hidden external : Unit) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeIdealOracle n k q s))
        ((cpaToAEHandler n c true request).run hidden) external =
      ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeIdealOracle n k q s))
        ((cpaToAEHandler n c false request).run hidden) external := by
  simp only [StateT.run, cpaToAEHandler, ↓reduceIte, Bool.false_eq_true]
  by_cases hlen : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
  · simp only [hlen, ↓reduceIte, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
    simp only [Bool.and_eq_true, beq_iff_eq] at hlen
    simp only [aeIdealOracle, Bool.false_eq_true, ↓reduceIte, hlen.1, hlen.2, beq_self_eq_true]
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte]

/-- In the ideal world the fixed bit of `cpaToAEAdversary` makes no difference. -/
private theorem eval_aeIdealGame_cpaToAEAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound true adversary) n) =
      ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound false adversary) n) := by
  simp only [aeIdealGame, cpaToAEAdversary, runWith_norm, pmf_norm,
    runWith_aeIdealOracle_cpaToAEHandler]

/-- The CPA advantage of `adversary` is at most the sum of the real/ideal advantages of
`cpaToAEAdversary ctBound false adversary` and `cpaToAEAdversary ctBound true adversary`, when
`ctBound n` bounds the ciphertext lengths of `n`-bit messages. -/
theorem advantage_cpaGame_le_aeRealGame_aeIdealGame (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    Game.advantage (ProbComp.eval (E.cpaGame adversary false n))
        (ProbComp.eval (E.cpaGame adversary true n)) ≤
      Game.advantage (ProbComp.eval (E.aeRealGame (cpaToAEAdversary ctBound false adversary) n))
          (ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound false adversary) n)) +
        Game.advantage (ProbComp.eval (E.aeRealGame (cpaToAEAdversary ctBound true adversary) n))
          (ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound true adversary) n)) := by
  game_trans
    [ProbComp.eval (E.aeRealGame (cpaToAEAdversary ctBound false adversary) n),
     ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound false adversary) n),
     ProbComp.eval (E.aeIdealGame (cpaToAEAdversary ctBound true adversary) n),
     ProbComp.eval (E.aeRealGame (cpaToAEAdversary ctBound true adversary) n)]
    using [eval_aeRealGame_cpaToAEAdversary E ctBound adversary false n hctBound,
           le_rfl,
           eval_aeIdealGame_cpaToAEAdversary E ctBound adversary n,
           le_rfl,
           eval_aeRealGame_cpaToAEAdversary E ctBound adversary true n hctBound]

/-- Real/ideal authenticated encryption implies adaptive CPA security (`INDCPA`). -/
theorem RealIdealAE.indcpa {E : SymmetricCipher} (h : E.RealIdealAE) : E.INDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hfalse := h _ (isOraclePPT_cpaToAEAdversary hctBoundPoly false hadversary)
  have htrue := h _ (isOraclePPT_cpaToAEAdversary hctBoundPoly true hadversary)
  negligible using fun n =>
    advantage_cpaGame_le_aeRealGame_aeIdealGame E ctBound adversary n (hctBound n)

/-! ### Real/ideal security implies ciphertext integrity -/

/-- Stateful handler for `ciToAEAdversary`: send each encryption request of the CI adversary to
the encryption channel, truncating the reply to `ctBound`. -/
@[expose]
noncomputable def ciToAEHandler (ctBound : ℕ) (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Bool) (List Bool) :=
  fun _ => (fun ct => (ct, ())) <$> (List.take ctBound <$> ProbOracleComp.query (false, request.2))

/-- Reduction from `ciGame` to the real/ideal experiment: run the CI adversary with its encryption
requests sent to the encryption channel, submit its candidate ciphertext to the decryption channel,
and output `true` exactly when the reply encodes an accepted decryption. -/
@[expose]
noncomputable def ciToAEAdversary (ctBound : ℕ → ℕ) (adversary : CIAdversary) : CCAAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ciToAEHandler (ctBound n)))
      (adversary n [])).run ()
    let reply ← List.take 1 <$> ProbOracleComp.query (true, out.1)
    return reply == [true]

/-- `ciToAEAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ciToAEAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBool (ciToAEAdversary ctBound adversary) := by
  have hhandler : IsOraclePPTOn (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ciToAEHandler (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    ppt [ciToAEHandler]
  have hreply (n : ℕ) (request : Unit × List Bool) (state : Unit) :
      ∀ result ∈ OracleComp.support (ciToAEHandler (ctBound n) request state),
        result.1.length ≤ ctBound n := by
    intro result hresult
    unfold ciToAEHandler at hresult
    obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
    exact List.length_take_le _ _
  have hrun := isOraclePPTOn_run_unitHandler (handler := fun n => ciToAEHandler (ctBound n))
    (bound := fun n _ => ctBound n) hadversary hhandler (hctBound.comp (by fun_prop)) hreply
  have hcont : IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encPair encBits (encFinEnum Unit)))
      encBool (fun pair : (ℕ × List Bool) × (List Bool × Unit) =>
        (fun reply => reply == [true]) <$>
          (List.take 1 <$> ProbOracleComp.query (true, pair.2.1))) :=
    (IsOraclePPTOn.query_take' true (by fun_prop) (ComputableInPolyTime.const 1)).map'
      (by fun_prop)
  unfold ciToAEAdversary
  simpa only [bind_pure_comp] using (hrun.bind_with hcont).isOraclePPT

/-- One step of the CI encryption oracle, with its ciphertext log paired with the handler's unit
state, is one step of `ciToAEHandler` against the real oracle. -/
private theorem map_ciEncryptionOracle_eq_runWith_ciToAEHandler (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (request : Unit × List Bool) (queried : List (List Bool)) :
    (ProbComp.eval (E.ciEncryptionOracle n k request queried)).map (fun x => (x.1, (), x.2)) =
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeRealOracle n k q s))
          ((ciToAEHandler (ctBound n) request).run ()) queried).map
        (fun result => (result.1.1, result.1.2, result.2)) := by
  simp only [ciEncryptionOracle, StateT.run, ciToAEHandler, Functor.map_map,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, aeRealOracle, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hlen : (request.2.length == n) = true
  · simp only [hlen, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
      PMF.pure_map, Prod.map_apply, id_eq]
    apply PMF.bind_congr_on_support
    intro ct hct
    rw [List.take_of_length_le (hctBound _ (beq_iff_eq.mp hlen) ct hct)]
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
      List.take_nil, Prod.map_apply, id_eq]

/-- Running `ciToAEHandler` against the real oracle simulates the CI encryption oracle. -/
private theorem map_runWith_ciEncryptionOracle_eq (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (program : WordOracleComp Unit (List Bool)) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)) program
        []).map (fun x => (x.1, (), x.2)) =
      ProbOracleComp.runWith
        (fun q state =>
          (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.aeRealOracle n k q s))
              ((ciToAEHandler (ctBound n) q).run state.1) state.2).map
            (fun result => (result.1.1, result.1.2, result.2)))
        program ((), []) :=
  ProbOracleComp.runWith_map_state _ _ (fun queried => ((), queried))
    (map_ciEncryptionOracle_eq_runWith_ciToAEHandler E ctBound n k hctBound) program []

/-- When `ctBound n` bounds the ciphertext lengths of `n`-bit messages,
`ciToAEAdversary ctBound adversary` outputs `true` in the real world exactly as often as `adversary`
wins `ciGame`. -/
theorem eval_aeRealGame_ciToAEAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CIAdversary) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.aeRealGame (ciToAEAdversary ctBound adversary) n) =
      ProbComp.eval (E.ciGame adversary n) := by
  simp only [aeRealGame, ciGame, ciToAEAdversary, runWith_norm, pmf_norm]
  peel_binds k
  rw [← map_runWith_ciEncryptionOracle_eq E ctBound n k (hctBound k k_mem) (adversary n [])]
  simp only [pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨out, queried⟩ _ => ?_
  simp only [aeRealOracle, ↓reduceIte, pmf_norm]
  cases queried.contains out <;> cases E.decrypt n k out <;> simp

/-- The ideal oracle rejects every decryption query. -/
private theorem eval_run_aeIdealOracle_true (E : SymmetricCipher) (n : ℕ) (k ct : List Bool)
    (u : Unit) :
    ProbComp.eval ((E.aeIdealOracle n k (true, ct)).run u) = PMF.pure ([], ()) := by
  simp only [StateT.run, aeIdealOracle, ↓reduceIte, ProbComp.eval_pure]

/-- In the ideal world, `ciToAEAdversary ctBound adversary` always outputs `false`. -/
theorem eval_aeIdealGame_ciToAEAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CIAdversary) (n : ℕ) :
    ProbComp.eval (E.aeIdealGame (ciToAEAdversary ctBound adversary) n) = PMF.pure false := by
  simp [aeIdealGame, ciToAEAdversary, eval_run_aeIdealOracle_true,
    ProbOracleComp.eval_run_interpret_eq_runWith]

/-- The CI winning probability of `adversary` equals the real/ideal advantage of
`ciToAEAdversary ctBound adversary`, when `ctBound n` bounds the ciphertext lengths of `n`-bit
messages. -/
theorem succProbability_ciGame_eq_advantage_aeRealGame_aeIdealGame (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    Game.succProbability (ProbComp.eval (E.ciGame adversary n)) =
      Game.advantage (ProbComp.eval (E.aeRealGame (ciToAEAdversary ctBound adversary) n))
        (ProbComp.eval (E.aeIdealGame (ciToAEAdversary ctBound adversary) n)) := by
  rw [eval_aeIdealGame_ciToAEAdversary, Game.advantage_pure_false,
    eval_aeRealGame_ciToAEAdversary E ctBound adversary n hctBound]

/-- Real/ideal authenticated encryption implies ciphertext integrity (`CiphertextIntegrity`). -/
theorem RealIdealAE.ciphertextIntegrity {E : SymmetricCipher} (h : E.RealIdealAE) :
    E.CiphertextIntegrity := by
  refine CiphertextIntegrity.of_negligible fun adversary hadversary => ?_
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hae := h _ (isOraclePPT_ciToAEAdversary hctBoundPoly hadversary)
  negligible using fun n =>
    (succProbability_ciGame_eq_advantage_aeRealGame_aeIdealGame E ctBound adversary n
      (hctBound n)).le

/-! ### CCA security and ciphertext integrity imply real/ideal security -/

/-- Stateful handler for `aeToCCAAdversary`. A decryption request `(true, ct)` is sent to the CCA
decryption channel, with the reply truncated to `decBound n ct`. An encryption request
`(false, msg)` is sent to the CCA encryption channel as the left-or-right request
`frame msg ++ List.replicate n false`, whose left message is `msg` and whose right message is the
all-zero message, with the reply truncated to `ctBound`. -/
@[expose]
noncomputable def aeToCCAHandler (n ctBound : ℕ) (decBound : ℕ → List Bool → ℕ)
    (request : Bool × List Bool) : StateT Unit (WordOracleComp Bool) (List Bool) :=
  fun _ =>
    if request.1 then
      (fun reply => (reply, ())) <$>
        (List.take (decBound n request.2) <$> ProbOracleComp.query (true, request.2))
    else
      (fun ct => (ct, ())) <$>
        (List.take ctBound <$>
          ProbOracleComp.query (false, frame request.2 ++ List.replicate n false))

/-- Reduction from the real/ideal experiment to `ccaGame`: run the real/ideal adversary against
`aeToCCAHandler`, which turns each encryption request into a left-or-right request between the
message and the all-zero message. With challenge bit `false` the adversary sees the real world;
with challenge bit `true` and every decryption rejected (`ccaRejectGame`) it sees the ideal
world. -/
@[expose]
noncomputable def aeToCCAAdversary (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : CCAAdversary) : CCAAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (aeToCCAHandler n (ctBound n) decBound))
      (adversary n [])).run ()
    return out.1

/-- `aeToCCAHandler` is oracle PPT in the caller, the request and the state. -/
private theorem isOraclePPTOn_aeToCCAHandler {ctBound : ℕ → ℕ} {decBound : ℕ → List Bool → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary) :
    IsOraclePPTOn (encPair (encPair encUnary encBits)
        (encPair (encPair encBool encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        aeToCCAHandler pair.1.1 (ctBound pair.1.1) decBound pair.2.1 pair.2.2) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) (encFinEnum Unit))
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) => p.2.1.1) EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hdecQuery : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        (fun reply => (reply, ())) <$>
          (List.take (decBound p.1.1 p.2.1.2) <$> ProbOracleComp.query (true, p.2.1.2))) := by
    ppt
  have hencQuery : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        (fun ct => (ct, ())) <$> (List.take (ctBound p.1.1) <$>
          ProbOracleComp.query (false, frame p.2.1.2 ++ List.replicate p.1.1 false))) := by
    ppt
  unfold aeToCCAHandler
  exact IsOraclePPTOn.cond' hop hdecQuery hencQuery

/-- A reply of `aeToCCAHandler` at parameter `n` to a request `(op, word)` has length at most
`ctBound n + decBound n word`. -/
private theorem length_of_mem_support_aeToCCAHandler {ctBound : ℕ → ℕ}
    {decBound : ℕ → List Bool → ℕ} (n : ℕ) (request : Bool × List Bool) (state : Unit) :
    ∀ result ∈ OracleComp.support (aeToCCAHandler n (ctBound n) decBound request state),
      result.1.length ≤ ctBound n + decBound n request.2 := by
  intro result hresult
  unfold aeToCCAHandler at hresult
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
    obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
    exact (List.length_take_le _ _).trans (by lia)
  · simp only [hreq, ↓reduceIte] at hresult
    obtain ⟨reply, hrep, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨rawReply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hrep
    exact (List.length_take_le _ _).trans (by lia)

/-- `aeToCCAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_aeToCCAAdversary {ctBound : ℕ → ℕ} {decBound : ℕ → List Bool → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (aeToCCAAdversary ctBound decBound adversary) := by
  have hresCtArg : ComputableInPolyTime (fun pair : (ℕ × List Bool) × List Bool => pair.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    fun_prop
  have hresDecArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => (pair.1.1, pair.2))
      (encPair (encPair encUnary encBits) encBits) (encPair encUnary encBits) := by
    fun_prop
  have hrun := isOraclePPTOn_run_unitHandler
    (handler := fun n => aeToCCAHandler n (ctBound n) decBound)
    (bound := fun n word => ctBound n + decBound n word) hadversary
    (isOraclePPTOn_aeToCCAHandler hctBound hdecBound)
    (ComputableInPolyTime.unary_add' (hctBound.comp hresCtArg) (hdecBound.comp hresDecArg))
    length_of_mem_support_aeToCCAHandler
  unfold aeToCCAAdversary
  simpa only [bind_pure_comp] using (hrun.map' (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- One step of the real oracle, with its record paired with the handler's unit state, is one step
of `aeToCCAHandler` against the CCA oracle with challenge bit `false`. -/
private theorem map_aeRealOracle_eq_runWith_aeToCCAHandler (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ) (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (hdecBound : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct)
    (request : Bool × List Bool) (queried : List (List Bool)) :
    (ProbComp.eval (E.aeRealOracle n k request queried)).map (fun x => (x.1, (), x.2)) =
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
          ((aeToCCAHandler n (ctBound n) decBound request).run ()) queried).map
        (fun result => (result.1.1, result.1.2, result.2)) := by
  cases hreq : request.1
  · simp only [aeRealOracle, aeToCCAHandler, StateT.run, hreq, Bool.false_eq_true, ↓reduceIte,
      Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaOracle,
      unframe_frame_append, dropFrame_frame_append, List.length_replicate, beq_self_eq_true,
      Bool.and_true]
    by_cases hlen : (request.2.length == n) = true
    · simp only [hlen, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
        PMF.pure_map, Prod.map_apply, id_eq]
      apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ (beq_iff_eq.mp hlen) ct hct)]
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
        List.take_nil, Prod.map_apply, id_eq]
  · simp only [aeRealOracle, aeToCCAHandler, StateT.run, hreq, ↓reduceIte, Functor.map_map,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaOracle]
    by_cases hc : queried.contains request.2 = true
    · simp only [hc, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map, List.take_nil, Prod.map_apply,
        id_eq]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
        Prod.map_apply, id_eq, List.take_of_length_le (hdecBound request.2)]

/-- When `ctBound n` and `decBound n` bound the ciphertext and decryption-reply lengths, running
`aeToCCAAdversary ctBound decBound adversary` in `ccaGame` with challenge bit `false` has the same
output distribution as running `adversary` in the real world. -/
theorem eval_ccaGame_aeToCCAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (decBound : ℕ → List Bool → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (hdecBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (E.ccaGame (aeToCCAAdversary ctBound decBound adversary) false n) =
      ProbComp.eval (E.aeRealGame adversary n) := by
  simp only [ccaGame, aeRealGame, aeToCCAAdversary, runWith_norm, pmf_norm]
  peel_binds k
  have hsim := ProbOracleComp.runWith_map_state
    (fun request queried => ProbComp.eval (E.aeRealOracle n k request queried))
    (fun request state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
          ((aeToCCAHandler n (ctBound n) decBound request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => ((), queried))
    (fun request queried =>
      map_aeRealOracle_eq_runWith_aeToCCAHandler E ctBound decBound n k (hctBound k k_mem)
        (hdecBound k k_mem) request queried)
    (adversary n []) []
  rw [← hsim]
  simp only [pmf_norm]

/-- One step of `aeToCCAHandler` against the all-reject CCA oracle with challenge bit `true`, after
forgetting all state, is one step of the ideal oracle. -/
private theorem map_runWith_aeToCCAHandler_eq_aeIdealOracle (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ) (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (request : Bool × List Bool) (state : Unit × List (List Bool)) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaRejectOracle n k true q s))
        ((aeToCCAHandler n (ctBound n) decBound request).run state.1) state.2).map
      (fun result => (result.1.1, result.1.2, result.2))).map (fun x => (x.1, ())) =
      ProbComp.eval (E.aeIdealOracle n k request ()) := by
  cases hreq : request.1
  · simp only [aeIdealOracle, aeToCCAHandler, StateT.run, hreq, Bool.false_eq_true, ↓reduceIte,
      Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaRejectOracle,
      unframe_frame_append, dropFrame_frame_append, List.length_replicate, beq_self_eq_true,
      Bool.and_true]
    by_cases hlen : (request.2.length == n) = true
    · simp only [hlen, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
        PMF.pure_map, Prod.map_apply, id_eq]
      apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ (by simp) ct hct)]
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
        List.take_nil, Prod.map_apply, id_eq]
  · simp only [aeIdealOracle, aeToCCAHandler, StateT.run, hreq, ↓reduceIte, Functor.map_map,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaRejectOracle,
      ProbComp.eval_pure, PMF.pure_map, List.take_nil, Prod.map_apply, id_eq]

/-- When `ctBound n` bounds the ciphertext lengths of `n`-bit messages, running
`aeToCCAAdversary ctBound decBound adversary` in `ccaRejectGame` with challenge bit `true` has the
same output distribution as running `adversary` in the ideal world. -/
theorem eval_ccaRejectGame_aeToCCAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (decBound : ℕ → List Bool → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.ccaRejectGame (aeToCCAAdversary ctBound decBound adversary) true n) =
      ProbComp.eval (E.aeIdealGame adversary n) := by
  simp only [ccaRejectGame, aeIdealGame, aeToCCAAdversary, runWith_norm, pmf_norm]
  peel_binds k
  have hsim := ProbOracleComp.runWith_map_state
    (fun request state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaRejectOracle n k true q s))
          ((aeToCCAHandler n (ctBound n) decBound request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun request u => ProbComp.eval (E.aeIdealOracle n k request u))
    (fun _ : Unit × List (List Bool) => ())
    (fun request state =>
      map_runWith_aeToCCAHandler_eq_aeIdealOracle E ctBound decBound n k (hctBound k k_mem)
        request state)
    (adversary n []) ((), [])
  rw [← hsim]
  simp only [pmf_norm]

/-- **Real/ideal advantage bound.** If `aeToCCAAdversary ctBound decBound adversary` makes at most
`Q n` queries, and `ctBound n` and `decBound n` bound the ciphertext and decryption-reply lengths,
then the real/ideal advantage of `adversary` is at most the CCA advantage of that reduction plus
`dyadicSize (Q n)` times the CI winning probability of `ccaToCIAdversary` built from it. -/
theorem advantage_aeRealGame_aeIdealGame_le (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (decBound : ℕ → List Bool → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (hq : (aeToCCAAdversary ctBound decBound adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (hdecBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    (Game.advantage (ProbComp.eval (E.aeRealGame adversary n))
        (ProbComp.eval (E.aeIdealGame adversary n)) : ℝ) ≤
      (Game.advantage
          (ProbComp.eval (E.ccaGame (aeToCCAAdversary ctBound decBound adversary) false n))
          (ProbComp.eval (E.ccaGame (aeToCCAAdversary ctBound decBound adversary) true n)) : ℝ) +
        (dyadicSize (Q n) : ℝ) *
          (Game.succProbability (ProbComp.eval (E.ciGame
            (ccaToCIAdversary ctBound Q true (aeToCCAAdversary ctBound decBound adversary)) n)) :
            ℝ) := by
  have hhop := (advantage_ccaGame_ccaRejectGame_le_sum E ctBound Q
    (aeToCCAAdversary ctBound decBound adversary) true n hq hctBound).trans
    (sum_succProbability_ccaToCIAtIndexAdversary_le E ctBound Q true
      (aeToCCAAdversary ctBound decBound adversary) n)
  game_trans
    [ProbComp.eval (E.ccaGame (aeToCCAAdversary ctBound decBound adversary) false n),
     ProbComp.eval (E.ccaGame (aeToCCAAdversary ctBound decBound adversary) true n),
     ProbComp.eval (E.ccaRejectGame (aeToCCAAdversary ctBound decBound adversary) true n)]
    using [eval_ccaGame_aeToCCAAdversary E ctBound decBound adversary n hctBound hdecBound,
           le_rfl,
           hhop,
           eval_ccaRejectGame_aeToCCAAdversary E ctBound decBound adversary n hctBound]

/-- **CCA security and ciphertext integrity imply real/ideal security**: the reverse direction of
[KatzLindell2020] Theorem 5.5, with `CiphertextIntegrity` in place of unforgeability. -/
theorem realIdealAE_of_indcca_of_ciphertextIntegrity {E : SymmetricCipher} (hcca : E.INDCCA)
    (hci : E.CiphertextIntegrity) : E.RealIdealAE := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := E.exists_decryption_length_bound
  have hred := isOraclePPT_aeToCCAAdversary hctBoundPoly hdecBoundPoly hadversary
  obtain ⟨cq, dq, hqbounds⟩ := hred.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hq (n : ℕ) : (aeToCCAAdversary ctBound decBound adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hccaNeg := hcca _ hred
  have hciNeg := hci.negligible
    (ccaToCIAdversary ctBound Q true (aeToCCAAdversary ctBound decBound adversary))
    (isOraclePPT_ccaToCIAdversary hctBoundPoly hQPoly true hred)
  negligible using fun n =>
    advantage_aeRealGame_aeIdealGame_le E ctBound Q decBound adversary n (hq n) (hctBound n)
      (hdecBound n)

/-! ### The equivalences -/

/-- Real/ideal security implies the library's `AuthenticatedEncryption`
(`INDCPA ∧ CiphertextIntegrity`). -/
theorem RealIdealAE.authenticatedEncryption {E : SymmetricCipher} (h : E.RealIdealAE) :
    E.AuthenticatedEncryption :=
  ⟨h.indcpa, h.ciphertextIntegrity⟩

/-- Real/ideal security implies CCA security: with `RealIdealAE.ciphertextIntegrity`, this is the
forward direction of [KatzLindell2020] Theorem 5.5. -/
theorem RealIdealAE.indcca {E : SymmetricCipher} (h : E.RealIdealAE) : E.INDCCA :=
  h.authenticatedEncryption.indcca

/-- The library's `AuthenticatedEncryption` implies real/ideal security. -/
theorem AuthenticatedEncryption.realIdealAE {E : SymmetricCipher}
    (hAE : E.AuthenticatedEncryption) : E.RealIdealAE :=
  realIdealAE_of_indcca_of_ciphertextIntegrity hAE.indcca hAE.2

/-- **Katz–Lindell Theorem 5.5**, in the form used by this library: a cipher is secure in the
real/ideal sense if and only if it is CCA secure and has ciphertext integrity. -/
theorem realIdealAE_iff_indcca_and_ciphertextIntegrity (E : SymmetricCipher) :
    E.RealIdealAE ↔ E.INDCCA ∧ E.CiphertextIntegrity :=
  ⟨fun h => ⟨h.indcca, h.ciphertextIntegrity⟩,
    fun h => realIdealAE_of_indcca_of_ciphertextIntegrity h.1 h.2⟩

/-- Real/ideal security is equivalent to the library's `AuthenticatedEncryption`. -/
theorem realIdealAE_iff_authenticatedEncryption (E : SymmetricCipher) :
    E.RealIdealAE ↔ E.AuthenticatedEncryption :=
  ⟨RealIdealAE.authenticatedEncryption, AuthenticatedEncryption.realIdealAE⟩

end SymmetricCipher

end Cslib.Crypto
