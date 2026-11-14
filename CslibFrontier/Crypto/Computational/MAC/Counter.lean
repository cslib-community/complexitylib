/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Counter-stateful MACs from nonce-based MACs

A nonce-based MAC becomes a stateful MAC once the signer chooses the nonces itself. It keeps a
counter `j`, tags its `j`-th message under the nonce `BitString.lowBits L j`, the `L`-bit
little-endian binary representation of `j` for `L = M.nonceLen n`, and returns that nonce with the
tag. The nonces stay distinct as long as the signer tags at most `2 ^ L` messages, so it refuses
every request after that. This is how [BonehShoup2023], Section 7.5, suggests implementing nonces
when the signer can keep state, and the remark after Theorem 7.10 (p. 274) says that for
Carter–Wegman the only requirement is that the signer tags at most as many messages as there are
nonces. The signer is stateful, so the construction is not a `NonceMACScheme`. Its state lives in
the signing oracle of a dedicated game, as for `IndexedSignatureScheme.counterEufCmaGame`.

The counter signing oracle (`counterSigningOracle`) at security parameter `n` holds the counter
and the issued triples. While `j < 2 ^ L`, it tags the requested message under the `j`-th nonce,
answers with the word `encPair encBits encBits (nonce, tag)`, records `((msg, nonce), tag)` and
advances. Afterwards it answers the empty word and records nothing. In `counterSufCmaGame`, the
forger outputs a nonce-tagged message `((msg, nonce), tag)` and wins when the lengths are right,
the triple was never issued, and the nonce-based verifier accepts it. This is strong
unforgeability, as in Attack Game 7.4; a nonce word of length `L` stands for the counter it
encodes.

The reduction is exact. `counterForger` runs a counter forger and answers its `j`-th request with
one query `(msg, lowBits L j)` to the nonce-based signing oracle. Distinct counters give distinct
nonces, so the nonce-respecting condition of `NonceMACScheme.sufCmaGame` always holds, and the
simulation is perfect: the counter forger's success is at most the nonce forger's
(`succProbability_counterSufCmaGame_le`). Replies are truncated to a bound on the tag length, which
honest tags never exceed, so that the reduction is strict oracle PPT for every external oracle
(`isOraclePPT_counterForger`).

## Main definitions

* `Cslib.Crypto.NonceMACScheme.counterSigningOracle`,
  `Cslib.Crypto.NonceMACScheme.counterSufCmaGame`,
  `Cslib.Crypto.NonceMACScheme.CounterSUFCMA`: the counter-stateful game and predicate.
* `Cslib.Crypto.NonceMACScheme.counterHandler`,
  `Cslib.Crypto.NonceMACScheme.counterForger`: the reduction to nonce-based forgery.

## Main results

* `Cslib.Crypto.NonceMACScheme.exists_sign_length_bound`: tags have polynomially bounded length.
* `Cslib.Crypto.NonceMACScheme.succProbability_counterSufCmaGame_le`: the exact bound.
* `Cslib.Crypto.NonceMACScheme.isOraclePPT_counterForger`: the reduction is efficient.
* `Cslib.Crypto.NonceMACScheme.SUFCMA.counterSufCma`: nonce-based SUF-CMA security gives
  counter SUF-CMA security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 7.5 and Theorem 7.10.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace NonceMACScheme

/-- Tags have polynomially bounded length: some plain polynomial-time `bound n ℓ` bounds every tag
on an `ℓ`-bit message under a `M.nonceLen n`-bit nonce and a key sampled at parameter `n`. -/
theorem exists_sign_length_bound (M : NonceMACScheme) :
    ∃ bound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2) (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg nonce,
        nonce.length = M.nonceLen n → ∀ tag ∈ (ProbComp.eval (M.sign sk msg nonce)).support,
          tag.length ≤ bound n msg.length := by
  obtain ⟨ck, dk, hlenk⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := M.sign_ppt.length_le
  have hnonce := M.nonceLen_polyTime
  refine ⟨fun n ℓ => cs * (2 * (ck * (n + 1) ^ dk) + 2 * ℓ + M.nonceLen n + 4) ^ ds,
    by fun_prop, fun n sk hsk msg nonce hnonceLen tag htag => ?_⟩
  have hkeyLen := hlenk n sk hsk
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkeyLen
  have htagLen := hlens (sk, msg, nonce) tag htag
  simp only [length_encPair, encBits_apply] at htagLen
  exact htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))

variable (M : NonceMACScheme)

/-! ### The counter signing oracle and its game -/

/-- The counter signing oracle at security parameter `n`. Its state is the number `j` of tags
issued so far and the issued triples `((msg, nonce), tag)`, most recent first. While
`j < 2 ^ M.nonceLen n`, the requested message is tagged under the nonce
`BitString.lowBits (M.nonceLen n) j`, the reply is the word `encPair encBits encBits (nonce, tag)`,
and the state advances. Afterwards every request receives the empty word and changes nothing. -/
@[expose] def counterSigningOracle (n : ℕ) (sk : List Bool) (request : Unit × List Bool) :
    StateT (ℕ × List ((List Bool × List Bool) × List Bool)) ProbComp (List Bool) := fun state =>
  if state.1 < 2 ^ M.nonceLen n then do
    let nonce := BitString.lowBits (M.nonceLen n) state.1
    let tag ← M.sign sk request.2 nonce
    return (encPair encBits encBits (nonce, tag),
      (state.1 + 1, ((request.2, nonce), tag) :: state.2))
  else
    return ([], state)

/-- The counter SUF-CMA experiment: sample `sk ← keyGen n`, run the forger on `(n, [])` with the
counter signing oracle started at `(0, [])`, and accept a candidate `((msg, nonce), tag)` with a
`M.msgLen n`-bit message and a `M.nonceLen n`-bit nonce that was never issued and that the
nonce-based verifier accepts. -/
@[expose] def counterSufCmaGame (adversary : NonceMACForger) (n : ℕ) : ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.counterSigningOracle n sk)) (adversary n [])).run (0, [])
  let (((msg, nonce), tag), _, issued) := out
  return (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
    !issued.contains ((msg, nonce), tag) && M.verify sk msg nonce tag

/-- Strong existential unforgeability of the counter-stateful use of a nonce-based MAC under
adaptive chosen-message attack ([BonehShoup2023], Section 7.5, with a counter as the nonce)
against uniform strict oracle-PPT forgers. -/
@[expose] def CounterSUFCMA : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.counterSufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encNonceTaggedMessage)

variable {M}

/-- Counter SUF-CMA security gives negligible forging probability for every oracle-PPT forger. -/
theorem CounterSUFCMA.negligible (h : M.CounterSUFCMA) (adversary : NonceMACForger)
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    Negligible (fun n =>
      Game.succProbability (ProbComp.eval (M.counterSufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish counter SUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem CounterSUFCMA.of_negligible
    (h : ∀ adversary, IsOraclePPT encNonceTaggedMessage adversary →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval (M.counterSufCmaGame adversary n)))) :
    M.CounterSUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### The reduction to nonce-based forgery -/

variable (M) in
/-- The nonce forger's answer to a counter forger's signing request, with the counter `j` as its
state: below `2 ^ M.nonceLen n`, tag the message under the `j`-th nonce by one external query,
truncate the reply to `bound n msg.length` bits, answer with the word
`encPair encBits encBits (nonce, tag)` and advance; otherwise answer the empty word. -/
def counterHandler (n : ℕ) (bound : ℕ → ℕ → ℕ) (request : Unit × List Bool) :
    StateT ℕ (WordOracleComp Unit) (List Bool) := fun j =>
  if j < 2 ^ M.nonceLen n then
    (fun tag => (encPair encBits encBits (BitString.lowBits (M.nonceLen n) j, tag), j + 1)) <$>
      (List.take (bound n request.2.length) <$>
        ProbOracleComp.query
          ((), encPair encBits encBits (request.2, BitString.lowBits (M.nonceLen n) j)))
  else
    pure ([], j)

variable (M) in
/-- The nonce forger built from a counter forger: run it with `counterHandler` from counter `0`
and forward its forgery unchanged. -/
def counterForger (bound : ℕ → ℕ → ℕ) (adversary : NonceMACForger) : NonceMACForger :=
  fun n aux => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (M.counterHandler n bound)) (adversary n aux)).run 0
    return out.1

/-! ### Exact simulation -/

variable (M) in
/-- The joint handler of `counterForger`'s run: the counter handler on the counter, followed by
the nonce-based signing oracle on its log. -/
private noncomputable def jointOracle (n : ℕ) (sk : List Bool) (bound : ℕ → ℕ → ℕ)
    (q : Unit × List Bool) (state : ℕ × List ((List Bool × List Bool) × List Bool)) :
    PMF (List Bool × ℕ × List ((List Bool × List Bool) × List Bool)) :=
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
      (fun q s => ProbComp.eval (M.signingPairOracle sk q s)))
    ((M.counterHandler n bound q).run state.1)).run state.2).map
      (fun ((reply, counter), log) => (reply, counter, log))

/-- When the bound covers every tag under `sk`, the counter handler followed by the nonce-based
signing oracle is the counter signing oracle. -/
private theorem jointOracle_eq {n : ℕ} {sk : List Bool} {bound : ℕ → ℕ → ℕ}
    (hbound : ∀ msg nonce, nonce.length = M.nonceLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg nonce)).support, tag.length ≤ bound n msg.length) :
    jointOracle M n sk bound =
      fun q state => ProbComp.eval (M.counterSigningOracle n sk q state) := by
  have hmapApply : ∀ {σ β γ : Type} (f : β → γ) (p : StateT σ PMF β) (state : σ),
      (f <$> p) state = (p state).map (fun r => (f r.1, r.2)) := fun _ _ _ => rfl
  funext q state
  obtain ⟨⟨⟩, w⟩ := q
  obtain ⟨j, issued⟩ := state
  by_cases hj : j < 2 ^ M.nonceLen n
  · simp only [jointOracle, counterHandler, counterSigningOracle, StateT.run, hj, ↓reduceIte,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, hmapApply, signingPairOracle,
      encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
    rw [List.take_of_length_le (hbound w _ (BitString.length_lowBits _ _) tag htag)]
  · simp only [jointOracle, counterHandler, counterSigningOracle, StateT.run, hj, ↓reduceIte,
      OracleComp.interpret_pure, ProbComp.eval_pure]
    exact PMF.pure_map _ _

variable (M) in
/-- The counter forger's win on a final run of the counter signing oracle. -/
private def counterWin (n : ℕ) (sk : List Bool) :
    ((List Bool × List Bool) × List Bool) × ℕ × List ((List Bool × List Bool) × List Bool) →
      Bool
  | (((msg, nonce), tag), _, issued) =>
    (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
      !issued.contains ((msg, nonce), tag) && M.verify sk msg nonce tag

variable (M) in
/-- The nonce forger's win on the same run: it also needs pairwise distinct issued nonces. -/
private def nonceWin (n : ℕ) (sk : List Bool) :
    ((List Bool × List Bool) × List Bool) × ℕ × List ((List Bool × List Bool) × List Bool) →
      Bool
  | (((msg, nonce), tag), _, issued) =>
    (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
      decide (issued.map (fun ((_, issuedNonce), _) => issuedNonce)).Nodup &&
      !issued.contains ((msg, nonce), tag) && M.verify sk msg nonce tag

/-- The counter game is the run of the counter signing oracle, judged by `counterWin`. -/
private theorem eval_counterSufCmaGame (adversary : NonceMACForger) (n : ℕ) :
    ProbComp.eval (M.counterSufCmaGame adversary n) =
      (ProbComp.eval (M.keyGen n)).bind fun sk =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (fun q state => ProbComp.eval (M.counterSigningOracle n sk q state)))
              (adversary n [])).run (0, [])).map (counterWin M n sk) := by
  simp only [counterSufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  rfl

/-- The nonce game against `counterForger` is the same run, judged by `nonceWin`, when the bound
covers every honest tag. -/
private theorem eval_sufCmaGame_counterForger {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg nonce,
      nonce.length = M.nonceLen n → ∀ tag ∈ (ProbComp.eval (M.sign sk msg nonce)).support,
        tag.length ≤ bound n msg.length)
    (adversary : NonceMACForger) :
    ProbComp.eval (M.sufCmaGame (M.counterForger bound adversary) n) =
      (ProbComp.eval (M.keyGen n)).bind fun sk =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (fun q state => ProbComp.eval (M.counterSigningOracle n sk q state)))
              (adversary n [])).run (0, [])).map (nonceWin M n sk) := by
  have hfused : ProbComp.eval (M.sufCmaGame (M.counterForger bound adversary) n) =
      (ProbComp.eval (M.keyGen n)).bind fun sk =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (jointOracle M n sk bound)) (adversary n [])).run (0, [])).map (nonceWin M n sk) := by
    simp only [sufCmaGame, counterForger, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, OracleComp.interpret_bind, OracleComp.interpret_pure,
      StateT.run_bind, StateT.run_pure, ProbOracleComp.run_interpret_run_interpret, PMF.bind_map,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    rfl
  rw [hfused]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [jointOracle_eq (hbound sk hsk)]

/-- The issued nonces of every run of the counter signing oracle are the nonces of the counters
issued so far, and the counter never passes `2 ^ M.nonceLen n`; so they are pairwise distinct. -/
private theorem nodup_of_mem_support_run_counterSigningOracle {n : ℕ} {sk : List Bool}
    (adversary : NonceMACForger) {result : (List Bool × List Bool) × List Bool} {counter : ℕ}
    {issued : List ((List Bool × List Bool) × List Bool)}
    (hr : (result, counter, issued) ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q state => ProbComp.eval (M.counterSigningOracle n sk q state)))
          (adversary n [])).run (0, [])).support) :
    (issued.map (fun ((_, issuedNonce), _) => issuedNonce)).Nodup := by
  have hinv : counter ≤ 2 ^ M.nonceLen n ∧
      issued.map (fun ((_, issuedNonce), _) => issuedNonce) =
        ((List.range counter).map (BitString.lowBits (M.nonceLen n))).reverse := by
    refine ProbOracleComp.runWith_invariant
      (fun q state => ProbComp.eval (M.counterSigningOracle n sk q state))
      (fun (counter, issued) => counter ≤ 2 ^ M.nonceLen n ∧
        issued.map (fun ((_, issuedNonce), _) => issuedNonce) =
          ((List.range counter).map (BitString.lowBits (M.nonceLen n))).reverse)
      ?_ (adversary n []) (0, []) (by simp) result (counter, issued) hr
    rintro ⟨⟨⟩, w⟩ ⟨j, issued⟩ ⟨hjle, hissued⟩ a ⟨j', issued'⟩ hmem
    by_cases hj : j < 2 ^ M.nonceLen n
    · simp only [counterSigningOracle, hj, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨tag, -, -, rfl, rfl⟩ := hmem
      refine ⟨hj, ?_⟩
      simp [hissued, List.range_succ]
    · simp only [counterSigningOracle, hj, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨-, rfl, rfl⟩ := hmem
      exact ⟨hjle, hissued⟩
  rw [hinv.2]
  refine List.nodup_reverse.mpr (List.nodup_range.map_on fun a ha b hb hab => ?_)
  exact BitString.lowBits_injective_of_lt
    ((List.mem_range.mp ha).trans_le hinv.1) ((List.mem_range.mp hb).trans_le hinv.1) hab

/-! ### The exact bound -/

/-- **Counter forgery reduces to nonce-based forgery without loss.** For every forger and every
security parameter `n`, the forging probability in the counter game is at most the forging
probability of `counterForger` in the nonce-based SUF-CMA game. The bound `bound n ℓ` must cover
the length of every tag on an `ℓ`-bit message under a `M.nonceLen n`-bit nonce and a supported
key; the nonce forger truncates replies to it. -/
theorem succProbability_counterSufCmaGame_le {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg nonce,
      nonce.length = M.nonceLen n → ∀ tag ∈ (ProbComp.eval (M.sign sk msg nonce)).support,
        tag.length ≤ bound n msg.length)
    (adversary : NonceMACForger) :
    Game.succProbability (ProbComp.eval (M.counterSufCmaGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (M.sufCmaGame (M.counterForger bound adversary) n)) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rw [eval_counterSufCmaGame, eval_sufCmaGame_counterForger hbound, PMF.bind_apply,
    PMF.bind_apply]
  refine tsum_le_tsum fun sk => mul_le_mul_right ?_ _
  refine PMF.map_true_mono _ fun r hr hwin => ?_
  obtain ⟨⟨⟨msg, nonce⟩, tag⟩, counter, issued⟩ := r
  have hnodup := nodup_of_mem_support_run_counterSigningOracle adversary hr
  simp only [counterWin, nonceWin, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  exact ⟨⟨⟨hwin.1.1, hnodup⟩, hwin.1.2⟩, hwin.2⟩

/-! ### Efficiency of the reduction -/

/-- `counterHandler` is strict oracle PPT in the caller `(n, aux)`, the request and the counter,
for every polynomial-time bound. -/
private theorem isOraclePPTOn_counterHandler {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encPair (encPair (encFinEnum Unit) encBits) encUnary))
      (encPair encBits encUnary)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × ℕ) =>
        M.counterHandler pair.1.1 bound pair.2.1 pair.2.2) := by
  have hnonce := M.nonceLen_polyTime
  unfold counterHandler
  exact IsOraclePPTOn.ite' (by fun_prop)
    ((IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)).map_with' (by fun_prop))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop))

/-- The counter handler's reply and counter growth are bounded by the truncation bound and the
nonce length, whatever the external oracle answers. -/
private theorem counterHandler_bound {bound : ℕ → ℕ → ℕ} (c : ℕ × List Bool)
    (request : Unit × List Bool) (j : ℕ) {result : List Bool × ℕ}
    (hresult : result ∈ OracleComp.support (M.counterHandler c.1 bound request j)) :
    result.1.length ≤ bound c.1 request.2.length + 2 * M.nonceLen c.1 + 2 ∧
      (encUnary result.2).length ≤
        (encUnary j).length + (bound c.1 request.2.length + 2 * M.nonceLen c.1 + 2) := by
  unfold counterHandler at hresult
  split_ifs at hresult with hj
  · obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
    have htake := List.length_take_le (bound c.1 request.2.length) raw
    simp only [length_encPair, encBits_apply, BitString.length_lowBits, encUnary_apply,
      List.length_replicate]
    omega
  · have h := OracleComp.eq_of_mem_supportWith_pure hresult
    subst h
    simp only [List.length_nil, encUnary_apply, List.length_replicate]
    omega

/-- The counter forger's reduction is uniformly strict oracle PPT for every oracle-PPT forger and
every polynomial-time truncation bound. -/
theorem isOraclePPT_counterForger {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : NonceMACForger} (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsOraclePPT encNonceTaggedMessage (M.counterForger bound adversary) := by
  have hnonce := M.nonceLen_polyTime
  refine ((hadversary.run_interpret_preprocess_open' (prepare := fun c => c)
      (initial := fun _ => (0 : ℕ))
      (resources := fun c w => bound c.1 w.length + 2 * M.nonceLen c.1 + 2)
      ComputableInPolyTime.id' (isOraclePPTOn_counterHandler hboundPoly)
      (ComputableInPolyTime.const 0) (fun _ _ => True) (fun _ => trivial) (by fun_prop)
      (fun c request j _ result hresult =>
        ⟨trivial, counterHandler_bound c request j hresult⟩)).bind
    ((ComputableInPolyTime.isOraclePPTOn (Operation := Unit)) (by fun_prop))).isOraclePPT

/-! ### Security -/

/-- **Nonce-based SUF-CMA security gives counter SUF-CMA security** ([BonehShoup2023],
Section 7.5): the signer of a SUF-CMA nonce-based MAC may choose its nonces with an `L`-bit
counter, tagging at most `2 ^ L` messages. The reduction is `counterForger`, with loss `1`
(`succProbability_counterSufCmaGame_le`). -/
theorem SUFCMA.counterSufCma (h : M.SUFCMA) : M.CounterSUFCMA := by
  obtain ⟨bound, hboundPoly, hbound⟩ := M.exists_sign_length_bound
  apply CounterSUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le
    (h.negligible (M.counterForger bound adversary)
      (isOraclePPT_counterForger hboundPoly hadversary))
    fun n => succProbability_counterSufCmaGame_le (hbound n) adversary

end NonceMACScheme

end Cslib.Crypto
