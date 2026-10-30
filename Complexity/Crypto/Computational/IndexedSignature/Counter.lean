/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.IndexedSignature
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Languages.Probabilistic.Oracle.Support
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Counter-stateful signatures from indexed signatures

An indexed signature scheme becomes an ordinary many-time signature scheme once the signer
chooses the indices itself: it keeps a counter `j`, signs its `j`-th message at index `j`, and
publishes `j` with the signature. This is [BonehShoup2023], Section 14.6.4, with the counter as
the nonce, and it is how Merkle's tree signature is used ([Merkle1989], Sections 6–7). The signer is
stateful, so the construction is not a `SignatureScheme`, whose signer is a function of the secret
key alone. Instead, the state lives in the signing oracle of a dedicated security game.

The counter signing oracle (`counterSigningOracle`) at security parameter `n` holds the counter and
the signed messages. While `j < capacity n` it signs the request at index `j`, answers with the word
`encPair encUnary encBits (j, σ)` and advances; once the capacity is exhausted it answers the empty
word and records nothing. A signature word is verified by `counterVerify`, which reads `(u, σ)` and
runs the indexed verifier at `u`. The game `counterEufCmaGame` is the EUF-CMA experiment with this
oracle; the forger wins with a valid signature on any message it never had signed, of any length.
This is stronger than `SignatureScheme.eufCmaGame`, which only counts `n`-bit forgeries.

The security reduction is exact. `counterForger` runs a counter forger, answering its `j`-th
signing query through the indexed signing oracle at index `j` and forwarding the forgery with its
index. Indices never repeat, so the indexed oracle never refuses, and the simulation is perfect:
the counter forger's success is at most the indexed forger's
(`succProbability_counterEufCmaGame_le`).
Replies are truncated to a bound on the signing length, which the honest oracle never exceeds, so
that the reduction is strict oracle PPT for every external oracle (`isOraclePPT_counterForger`).

## Main definitions

* `Cslib.Crypto.IndexedSignatureScheme.counterSigningOracle`,
  `Cslib.Crypto.IndexedSignatureScheme.counterVerify`,
  `Cslib.Crypto.IndexedSignatureScheme.counterEufCmaGame`,
  `Cslib.Crypto.IndexedSignatureScheme.CounterEUFCMA`: the counter-stateful game and predicate.
* `Cslib.Crypto.IndexedSignatureScheme.counterHandler`,
  `Cslib.Crypto.IndexedSignatureScheme.counterForger`: the reduction to indexed forgery.

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.counterVerify_sign`,
  `Cslib.Crypto.IndexedSignatureScheme.counterVerify_of_mem_support_counterSigningOracle`:
  completeness of the first `capacity n` signatures.
* `Cslib.Crypto.IndexedSignatureScheme.isPPTOn_run_counterSigningOracle`,
  `Cslib.Crypto.IndexedSignatureScheme.isPPTOn_counterEufCmaGame`: strict PPT certificates for
  the game.
* `Cslib.Crypto.IndexedSignatureScheme.succProbability_counterEufCmaGame_le`: the exact bound.
* `Cslib.Crypto.IndexedSignatureScheme.isOraclePPT_counterForger`: the reduction is efficient.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.counterEUFCMA`: indexed EUF-CMA security
  gives counter EUF-CMA security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.4.
* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Sections 6–7.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace IndexedSignatureScheme

variable (S : IndexedSignatureScheme)

/-! ### The counter signing oracle and its game -/

/-- The counter signing oracle at security parameter `n`. Its state is the number `j` of
signatures issued so far and the signed messages, most recent first. While `j < capacity n`, the
requested message is signed at index `j`, the reply is the word `encPair encUnary encBits (j, σ)`,
and the state advances; afterwards every request receives the empty word and changes nothing. -/
def counterSigningOracle (n : ℕ) (sk : List Bool) (request : Unit × List Bool) :
    StateT (ℕ × List (List Bool)) ProbComp (List Bool) := fun state =>
  if state.1 < S.capacity n then do
    let sig ← S.sign sk state.1 request.2
    return (encPair encUnary encBits (state.1, sig), (state.1 + 1, request.2 :: state.2))
  else
    return ([], state)

/-- Verify a counter signature word on `msg` under `pk`: read the index `u` and the indexed
signature `σ` from the word `encPair encUnary encBits (u, σ)` (with `requestDecoder`, which reads
every word) and check `verify pk u msg σ`. -/
def counterVerify (pk msg sig : List Bool) : Bool :=
  S.verify pk (requestDecoder.decode sig).1 msg (requestDecoder.decode sig).2

/-- The counter EUF-CMA experiment: sample `(pk, sk) ← keyGen n`, run the forger on `(n, pk)` with
the counter signing oracle started at `(0, [])`, and accept a valid counter signature on a message
that was never signed, of any length. -/
def counterEufCmaGame (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.counterSigningOracle n keys.2)) (adversary n keys.1)).run (0, [])
  return !out.2.2.contains out.1.1 && S.counterVerify keys.1 out.1.1 out.1.2

variable {S}

/-- **Completeness**: the counter signature word of an indexed signature at an index below the
capacity verifies. -/
theorem counterVerify_sign (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support) {u : ℕ} (hu : u < S.capacity n)
    (msg sig : List Bool) (hsig : sig ∈ (ProbComp.eval (S.sign keys.2 u msg)).support) :
    S.counterVerify keys.1 msg (encPair encUnary encBits (u, sig)) = true := by
  simp only [counterVerify, requestDecoder.decode_enc]
  exact S.verify_sign n keys hkeys u hu msg sig hsig

/-- Every reply of the counter signing oracle below the capacity verifies on the requested
message, and the oracle advances its counter and logs the message. -/
theorem counterVerify_of_mem_support_counterSigningOracle (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support) (request : Unit × List Bool)
    {j : ℕ} (hj : j < S.capacity n) (signed : List (List Bool))
    {result : List Bool × ℕ × List (List Bool)}
    (hresult :
      result ∈ (ProbComp.eval (S.counterSigningOracle n keys.2 request (j, signed))).support) :
    S.counterVerify keys.1 request.2 result.1 = true ∧ result.2 = (j + 1, request.2 :: signed) := by
  simp only [counterSigningOracle, hj, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
  obtain ⟨sig, hsig, rfl⟩ := hresult
  exact ⟨counterVerify_sign n keys hkeys hj request.2 sig hsig, rfl⟩

/-! ### Efficiency of the game -/

/-- Running an oracle-PPT forger against `counterSigningOracle` is uniformly strict PPT in the
unary security parameter, the public key and the secret key. -/
@[program_certificate]
theorem isPPTOn_run_counterSigningOracle {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encPair encUnary (encList encBits)))
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.counterSigningOracle caller.1 caller.2.2)) (adversary caller.1 caller.2.1)).run
          (0, [])) := by
  obtain ⟨c, d, hlen⟩ := S.sign_ppt.length_le
  have hcap := S.capacity_polyTime
  have hhandler : IsPPTOn
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair (encFinEnum Unit) encBits) (encPair encUnary (encList encBits))))
      (encPair encBits (encPair encUnary (encList encBits)))
      (fun pair : (ℕ × (List Bool × List Bool)) ×
          ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        S.counterSigningOracle pair.1.1 pair.1.2.2 pair.2.1 pair.2.2) := by
    unfold counterSigningOracle
    apply IsPPTOn.ite
    · polytime
    · refine (S.sign_ppt.preprocess (prepare := fun pair :
          (ℕ × (List Bool × List Bool)) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
          (pair.1.2.2, pair.2.2.1, pair.2.1.2)) ?_).bind_with ?_
      · polytime
      · apply ComputableInPolyTime.isPPTOn
        polytime
    · ppt
  have hresources : ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × List Bool =>
        c * (2 * pair.1.2.2.length + 2 * S.capacity pair.1.1 + pair.2.length + 3) ^ d +
          2 * S.capacity pair.1.1 + 2 * pair.2.length + 4)
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) encUnary := by
    polytime
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ((0, []) : ℕ × List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + 2 * S.capacity caller.1 + query.length + 3) ^ d +
        2 * S.capacity caller.1 + 2 * query.length + 4)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) hresources.tidy
  intro caller request state _ result hresult
  obtain ⟨j, signed⟩ := state
  unfold counterSigningOracle at hresult
  dsimp only at hresult
  split_ifs at hresult with hj
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, j, request.2) sig hsig
    simp only [encBits_apply, encUnary_apply, length_encPair, List.length_replicate] at hsigLen
    have hpow : c * (2 * caller.2.2.length + 1 + (2 * j + 1 + request.2.length) + 1) ^ d ≤
        c * (2 * caller.2.2.length + 2 * S.capacity caller.1 + request.2.length + 3) ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
    refine ⟨trivial, ?_, ?_⟩
    · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
      omega
    · simp only [length_encPair, encUnary_apply, encList_cons, List.length_append, length_frame,
        encBits_apply, List.length_replicate]
      omega
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst hresult
    exact ⟨trivial, by simp, by lia⟩

/-- The whole counter EUF-CMA experiment is uniformly strict PPT in its unary security parameter
for every oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_counterEufCmaGame {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.counterEufCmaGame adversary) := by
  have hrun := S.isPPTOn_run_counterSigningOracle hadversary
  have hverify := S.verify_polyTime
  have hdecode := requestDecoder.computableInPolyTime
  have hpost : ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) ×
          ((List Bool × List Bool) × (ℕ × List (List Bool))) =>
        !pair.2.2.2.contains pair.2.1.1 && S.counterVerify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary (encPair encBits encBits))
        (encPair (encPair encBits encBits) (encPair encUnary (encList encBits)))) encBool := by
    unfold counterVerify
    polytime
  exact S.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-! ### The security predicate -/

variable (S) in
/-- Existential unforgeability of the counter-stateful use of an indexed scheme under adaptive
chosen-message attack ([BonehShoup2023], Section 14.6.4, with the counter as the nonce) against
uniform strict oracle-PPT forgers. A forgery on any never-signed message counts, whatever its
length. -/
def CounterEUFCMA : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.counterEufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Counter EUF-CMA security gives negligible forging probability for every oracle-PPT forger. -/
theorem CounterEUFCMA.negligible (h : S.CounterEUFCMA) (adversary : Forger)
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n =>
      Game.succProbability (ProbComp.eval (S.counterEufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish counter EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem CounterEUFCMA.of_negligible
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval (S.counterEufCmaGame adversary n)))) :
    S.CounterEUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### The reduction to indexed forgery -/

variable (S) in
/-- The indexed forger's answer to a counter forger's signing request, with the counter `j` as its
state: below the capacity, sign the message at index `j` by one external query to the indexed
signing oracle, truncate the reply to `bound n msg.length` bits, answer with the counter signature
word and advance; otherwise answer the empty word. -/
def counterHandler (n : ℕ) (bound : ℕ → ℕ → ℕ) (request : Unit × List Bool) :
    StateT ℕ (WordOracleComp Unit) (List Bool) := fun j =>
  if j < S.capacity n then
    (fun sig => (encPair encUnary encBits (j, sig), j + 1)) <$>
      (List.take (bound n request.2.length) <$>
        ProbOracleComp.query ((), encPair encUnary encBits (j, request.2)))
  else
    pure ([], j)

variable (S) in
/-- The indexed forger built from a counter forger: run it with `counterHandler` from counter `0`,
and forward its forgery `(msg, encPair encUnary encBits (u, σ))` as `(u, msg, σ)`. -/
def counterForger (bound : ℕ → ℕ → ℕ) (adversary : Forger) : IndexedForger := fun n pk => do
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (S.counterHandler n bound)) (adversary n pk)).run 0
  return ((requestDecoder.decode out.1.2).1, out.1.1, (requestDecoder.decode out.1.2).2)

/-! ### Exact simulation -/

variable (S) in
/-- The joint handler of `counterForger`'s run: the counter handler on the counter, followed by
the indexed signing oracle on the indexed log. -/
private noncomputable def jointOracle (n : ℕ) (sk : List Bool) (bound : ℕ → ℕ → ℕ)
    (q : Unit × List Bool) (state : ℕ × List (ℕ × List Bool)) :
    PMF (List Bool × ℕ × List (ℕ × List Bool)) :=
  ((OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
      (fun q s => ProbComp.eval (S.indexedSigningOracle n sk q s)))
    ((S.counterHandler n bound q).run state.1)).run state.2).map
      (fun result => (result.1.1, result.1.2, result.2))

/-- Below the capacity, on a log of smaller indices, the joint handler signs at the counter. -/
private theorem jointOracle_of_lt {n : ℕ} {sk : List Bool} {bound : ℕ → ℕ → ℕ} {w : List Bool}
    {j : ℕ} {signed : List (ℕ × List Bool)} (hj : j < S.capacity n)
    (hinv : ∀ e ∈ signed, e.1 < j) :
    jointOracle S n sk bound ((), w) (j, signed) =
      (ProbComp.eval (S.sign sk j w)).bind fun σ =>
        PMF.pure (encPair encUnary encBits (j, List.take (bound n w.length) σ), j + 1,
          (j, w) :: signed) := by
  have hmapApply : ∀ {σ β γ : Type} (f : β → γ) (p : StateT σ PMF β) (state : σ),
      (f <$> p) state = (p state).map (fun r => (f r.1, r.2)) := fun _ _ _ => rfl
  have hnot : j ∉ signed.map Prod.fst := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun e he heq => (hinv e he).ne heq
  simp only [jointOracle, counterHandler, StateT.run, hj, ↓reduceIte, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, hmapApply, indexedSigningOracle, requestDecoder.decode_enc,
    hnot, not_false_eq_true, and_self, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
    PMF.pure_map]

/-- At or above the capacity the joint handler answers the empty word and changes nothing. -/
private theorem jointOracle_of_le {n : ℕ} {sk : List Bool} {bound : ℕ → ℕ → ℕ} {w : List Bool}
    {j : ℕ} {signed : List (ℕ × List Bool)} (hj : ¬ j < S.capacity n) :
    jointOracle S n sk bound ((), w) (j, signed) = PMF.pure ([], j, signed) := by
  simp only [jointOracle, counterHandler, StateT.run, hj, ↓reduceIte, OracleComp.interpret_pure]
  exact PMF.pure_map _ _

/-- The counter handler, followed by the indexed signing oracle, is the counter signing oracle:
the joint run, with the counter kept and the indexed log projected to its messages, is the counter
oracle's run. The bound must cover every signature at an index below the capacity. -/
private theorem map_run_jointOracle {n : ℕ} {sk : List Bool} {bound : ℕ → ℕ → ℕ}
    (hbound : ∀ j < S.capacity n, ∀ msg, ∀ σ ∈ (ProbComp.eval (S.sign sk j msg)).support,
      σ.length ≤ bound n msg.length)
    {α : Type} (program : WordOracleComp Unit α) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (jointOracle S n sk bound)) program).run (0, [])).map
          (fun r => (r.1, r.2.1, r.2.2.map Prod.snd)) =
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.counterSigningOracle n sk)) program).run (0, [])) := by
  rw [ProbOracleComp.eval_run_interpret]
  refine ProbOracleComp.run_interpret_map_state_of_invariant _ _
    (fun state : ℕ × List (ℕ × List Bool) => (state.1, state.2.map Prod.snd))
    (fun state : ℕ × List (ℕ × List Bool) => ∀ e ∈ state.2, e.1 < state.1) ?_ ?_ program (0, [])
    (by simp)
  · rintro ⟨⟨⟩, w⟩ ⟨j, signed⟩ hinv a ⟨j', signed'⟩ hmem
    by_cases hj : j < S.capacity n
    · rw [jointOracle_of_lt hj hinv] at hmem
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨σ, -, -, rfl, rfl⟩ := hmem
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Nat.lt_succ_self _
      · exact (hinv e he).trans (Nat.lt_succ_self _)
    · rw [jointOracle_of_le hj] at hmem
      simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨-, rfl, rfl⟩ := hmem
      exact hinv
  · rintro ⟨⟨⟩, w⟩ ⟨j, signed⟩ hinv
    by_cases hj : j < S.capacity n
    · rw [jointOracle_of_lt hj hinv]
      simp only [counterSigningOracle, hj, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.map_bind, PMF.pure_map, List.map_cons]
      refine PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
      rw [List.take_of_length_le (hbound j hj w σ hσ)]
    · rw [jointOracle_of_le hj]
      simp only [counterSigningOracle, hj, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map]

variable (S) in
/-- The indexed forger's win, read off the joint run. -/
private def indexedWin (pk : List Bool)
    (r : (List Bool × List Bool) × ℕ × List (ℕ × List Bool)) : Bool :=
  !r.2.2.contains ((requestDecoder.decode r.1.2).1, r.1.1) &&
    S.verify pk (requestDecoder.decode r.1.2).1 r.1.1 (requestDecoder.decode r.1.2).2

/-- The indexed game against `counterForger` is the joint run, judged by `indexedWin`. -/
private theorem eval_indexedEufCmaGame_counterForger (bound : ℕ → ℕ → ℕ) (adversary : Forger)
    (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame (S.counterForger bound adversary) n) =
      (ProbComp.eval (S.keyGen n)).bind fun keys =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
            (jointOracle S n keys.2 bound)) (adversary n keys.1)).run (0, [])).map
              (indexedWin S keys.1) := by
  simp only [indexedEufCmaGame, counterForger, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret, OracleComp.interpret_bind, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure, ProbOracleComp.run_interpret_run_interpret, PMF.bind_map,
    PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  rfl

/-- The counter game is the joint run, judged by the counter forger's win on the projected
state. -/
private theorem eval_counterEufCmaGame_eq {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ j < S.capacity n, ∀ msg,
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 j msg)).support, σ.length ≤ bound n msg.length)
    (adversary : Forger) :
    ProbComp.eval (S.counterEufCmaGame adversary n) =
      (ProbComp.eval (S.keyGen n)).bind fun keys =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
            (jointOracle S n keys.2 bound)) (adversary n keys.1)).run (0, [])).map
              (fun r => !(r.2.2.map Prod.snd).contains r.1.1 &&
                S.counterVerify keys.1 r.1.1 r.1.2) := by
  simp only [counterEufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  rw [← map_run_jointOracle (hbound keys hkeys), PMF.bind_map]
  rfl

/-! ### The exact bound -/

/-- **Counter forgery reduces to indexed forgery without loss.** For every forger and every
security parameter `n`, the forging probability in the counter game is at most the forging
probability of `counterForger` in the indexed game. The bound `bound n L` must cover the length of
every indexed signature on an `L`-bit message at an index below the capacity under a supported key;
the indexed forger truncates replies to it. -/
theorem succProbability_counterEufCmaGame_le {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ j < S.capacity n, ∀ msg,
      ∀ σ ∈ (ProbComp.eval (S.sign x.2 j msg)).support, σ.length ≤ bound n msg.length)
    (adversary : Forger) :
    Game.succProbability (ProbComp.eval (S.counterEufCmaGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (S.indexedEufCmaGame (S.counterForger bound adversary) n)) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rw [eval_counterEufCmaGame_eq hbound adversary, eval_indexedEufCmaGame_counterForger,
    PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun keys => mul_le_mul_right ?_ _
  refine PMF.map_true_mono _ fun r _ hwin => ?_
  simp only [indexedWin, counterVerify, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hwin ⊢
  obtain ⟨hfresh, hverify⟩ := hwin
  refine ⟨?_, hverify⟩
  rw [← Bool.not_eq_true, List.contains_iff_mem] at hfresh ⊢
  exact fun hmem => hfresh (List.mem_map.mpr ⟨_, hmem, rfl⟩)

/-! ### Efficiency of the reduction -/

/-- `counterHandler` is strict oracle PPT in the caller `(n, pk)`, the request and the counter,
for every polynomial-time bound. -/
private theorem isOraclePPTOn_counterHandler {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encPair (encPair (encFinEnum Unit) encBits) encUnary))
      (encPair encBits encUnary)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × ℕ) =>
        S.counterHandler pair.1.1 bound pair.2.1 pair.2.2) := by
  have hcap := S.capacity_polyTime
  have hb : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × ℕ) => bound pair.1.1 pair.2.1.2.length)
      (encPair (encPair encUnary encBits) (encPair (encPair (encFinEnum Unit) encBits) encUnary))
      encUnary :=
    hboundPoly.comp (g := fun pair : (ℕ × List Bool) × ((Unit × List Bool) × ℕ) =>
      (pair.1.1, pair.2.1.2.length)) (by polytime)
  have heq : (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × ℕ) =>
      S.counterHandler pair.1.1 bound pair.2.1 pair.2.2) =
    fun pair => if pair.2.2 < S.capacity pair.1.1 then
      (fun sig => (encPair encUnary encBits (pair.2.2, sig), pair.2.2 + 1)) <$>
        (List.take (bound pair.1.1 pair.2.1.2.length) <$>
          ProbOracleComp.query ((), encPair encUnary encBits (pair.2.2, pair.2.1.2)))
    else
      pure ([], pair.2.2) := rfl
  rw [heq]
  refine IsOraclePPTOn.ite' ?_ ?_ ?_
  · polytime
  · refine (IsOraclePPTOn.query_take' () ?_ hb).map_with' ?_
    · polytime
    · polytime
  · exact ComputableInPolyTime.isOraclePPTOn (by polytime)

/-- The counter handler's reply and counter growth are bounded by the truncation bound and the
capacity, whatever the external oracle answers. -/
private theorem counterHandler_bound {bound : ℕ → ℕ → ℕ} (c : ℕ × List Bool)
    (request : Unit × List Bool) (j : ℕ) {result : List Bool × ℕ}
    (hresult : result ∈ OracleComp.support (S.counterHandler c.1 bound request j)) :
    result.1.length ≤ bound c.1 request.2.length + 2 * S.capacity c.1 + 1 ∧
      (encUnary result.2).length ≤
        (encUnary j).length + (bound c.1 request.2.length + 2 * S.capacity c.1 + 1) := by
  unfold counterHandler at hresult
  split_ifs at hresult with hj
  · obtain ⟨sig, hsig, rfl⟩ := ProbOracleComp.mem_support_map hresult
    obtain ⟨raw, -, rfl⟩ := ProbOracleComp.mem_support_map hsig
    have htake := List.length_take_le (bound c.1 request.2.length) raw
    simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    omega
  · have h := ProbOracleComp.eq_of_mem_support_pure hresult
    subst h
    simp only [List.length_nil, encUnary_apply, List.length_replicate]
    omega

/-- The counter forger's reduction is uniformly strict oracle PPT for every oracle-PPT forger and
every polynomial-time truncation bound. -/
theorem isOraclePPT_counterForger {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits)) (S.counterForger bound adversary) := by
  have hcap := S.capacity_polyTime
  have hb : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => bound pair.1.1 pair.2.length)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    hboundPoly.comp (g := fun pair : (ℕ × List Bool) × List Bool => (pair.1.1, pair.2.length))
      (by polytime)
  have hresources : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool =>
        bound pair.1.1 pair.2.length + 2 * S.capacity pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    polytime
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) encUnary)
      (fun c : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (S.counterHandler c.1 bound)) (adversary c.1 c.2)).run 0) :=
    hadversary.run_interpret_preprocess_open' (prepare := fun c => c)
      (initial := fun _ => (0 : ℕ))
      (resources := fun c w => bound c.1 w.length + 2 * S.capacity c.1 + 1)
      ComputableInPolyTime.id' (isOraclePPTOn_counterHandler hboundPoly)
      (ComputableInPolyTime.const 0) (fun _ _ => True) (fun _ => trivial) hresources
      (fun c request j _ result hresult => ⟨trivial, counterHandler_bound c request j hresult⟩)
  have hdecode := requestDecoder.computableInPolyTime
  have hpost : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × ℕ) =>
        ((requestDecoder.decode pair.2.1.2).1, pair.2.1.1, (requestDecoder.decode pair.2.1.2).2))
      (encPair (encPair encUnary encBits) (encPair (encPair encBits encBits) encUnary))
      (encPair encUnary (encPair encBits encBits)) := by
    polytime
  exact hrun.bind_with
    (second := fun (_ : ℕ × List Bool) (out : (List Bool × List Bool) × ℕ) =>
      (pure ((requestDecoder.decode out.1.2).1, out.1.1, (requestDecoder.decode out.1.2).2) :
        WordOracleComp Unit (ℕ × List Bool × List Bool)))
    (hpost.isOraclePPTOn (Operation := Unit))

/-! ### Security -/

/-- **Indexed EUF-CMA security gives counter EUF-CMA security** ([BonehShoup2023],
Section 14.6.4): the signer of an indexed EUF-CMA secure scheme may choose its indices with a
counter. The reduction is `counterForger`, with loss `1`
(`succProbability_counterEufCmaGame_le`). -/
theorem IndexedEUFCMA.counterEUFCMA (h : S.IndexedEUFCMA) : S.CounterEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  have hcap := S.capacity_polyTime
  obtain ⟨bound, hboundPoly, hbound⟩ : ∃ bound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2) (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ x ∈ (ProbComp.eval (S.keyGen n)).support, ∀ j < S.capacity n, ∀ msg,
        ∀ σ ∈ (ProbComp.eval (S.sign x.2 j msg)).support, σ.length ≤ bound n msg.length := by
    refine ⟨fun n L => cs * (2 * (ck * (n + 1) ^ dk) + 2 * S.capacity n + L + 3) ^ ds,
      by polytime, fun n x hx j hj msg σ hσ => ?_⟩
    have hkeyLen := hlenk n x hx
    simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeyLen
    have hσLen := hlens (x.2, j, msg) σ hσ
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hσLen
    refine hσLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
    omega
  apply CounterEUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le
    (h.negligible (S.counterForger bound adversary)
      (isOraclePPT_counterForger hboundPoly hadversary))
    fun n => succProbability_counterEufCmaGame_le (hbound n) adversary

end IndexedSignatureScheme

end Cslib.Crypto
