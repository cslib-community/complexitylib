/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.CoinTape
import Complexity.Languages.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Probability.PMF.Bind

/-!
# Saved tapes for the link guessing stage

The replay decodes the original saved state and preserves its public keys and the challenge.
Its parameter-only coin law applies to valid active contexts or to the rejected context.
Support of the original choice sampler supplies the validity conditions.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.guessLinkCoins`: deterministic replay of the original guess.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.chooseLinkAt_support`: supported choices retain valid keys
  and a valid selected secret bit, or are the original rejection.
* `Cslib.Crypto.Homomorphic.Scheme.eval_guessLink_active_eq_map_coins`: the active guess law.
* `Cslib.Crypto.Homomorphic.Scheme.computableInPolyTime_guessLinkCoins`: total native replay.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- Every original choice is rejected or records the sampled keys and a genuine secret bit.
In particular, validity is derived from the sampler rather than assumed of every decoded word. -/
theorem chooseLinkAt_support (E : Scheme) (n beforeCount afterCount cut : ℕ)
    (challengePk : List Bool) (choice : (Bool × Bool) × List Bool)
    (hchoice : choice ∈ (ProbComp.eval
      (E.chooseLinkAt n beforeCount afterCount cut challengePk)).support) :
    choice = rejectLinkChoice ∨ ∃ before predecessor after,
      before.length = beforeCount ∧ after.length = afterCount ∧
      (∀ key ∈ before ++ predecessor :: after, key ∈ (ProbComp.eval (E.keyGen n)).support) ∧
      cut < predecessor.2.length ∧
      choice = ((predecessor.2.getD cut false, false),
        activeLinkState before predecessor challengePk after cut) := by
  simp only [chooseLinkAt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hchoice
  obtain ⟨before, hbefore, predecessor, hpredecessor, after, hafter, hchoice⟩ := hchoice
  obtain ⟨hbeforeLength, hbeforeKeys⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hbefore
  obtain ⟨hafterLength, hafterKeys⟩ :=
    (ProbComp.mem_support_replicate_iff _ _ _).mp hafter
  split at hchoice
  · rename_i hcut
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hchoice
    refine Or.inr ⟨before, predecessor, after, hbeforeLength, hafterLength, ?_, hcut, hchoice⟩
    intro key hkey
    simp only [List.mem_append, List.mem_cons] at hkey
    rcases hkey with h | rfl | h
    · exact hbeforeKeys _ h
    · exact hpredecessor
    · exact hafterKeys _ h
  · simpa only [ProbComp.eval_pure, PMF.mem_support_pure_iff] using Or.inl hchoice

/-- Replay the actual guess, including total saved-state decoding and the inactive branch.
The test receives the original public artifact and its own independent suffix of the tape. -/
@[expose] def guessLinkCoins
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateTest : (ℕ × List (List Bool) × List (List (List Bool))) → List Bool → Bool)
    (n encCoins capacity : ℕ) (state challenge tape : List Bool) : Bool :=
  let context := linkStateDecoder.decode state
  if context.1 then
    let (before, predecessor, targetKey, after, cut) := context.2
    let target := (targetKey, List.replicate predecessor.2.length false)
    let linkCoins := ((before.length + after.length + 1) * capacity - 1) * encCoins
    let links := spliceEncryptedKeyLinkCoins evaluateEncrypt n encCoins capacity
      before predecessor target after cut challenge (tape.take linkCoins)
    evaluateTest (n, (before ++ predecessor :: target :: after).map Prod.fst, links)
      (tape.drop linkCoins)
  else false

/-- Exact replay on a valid active context. The test law is required only on public artifacts
that can arise from the actual splice, with no simulation conclusion among the hypotheses. -/
theorem eval_guessLink_active_eq_map_coins (E : Scheme)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateTest : (ℕ × List (List Bool) × List (List (List Bool))) → List Bool → Bool)
    (n encCoins testCoins capacity : ℕ) (before : List (List Bool × List Bool))
    (predecessor : List Bool × List Bool) (targetKey : List Bool)
    (after : List (List Bool × List Bool)) (cut : ℕ) (challenge : List Bool)
    (hcut : cut < predecessor.2.length)
    (hwidth : ∀ key ∈ before ++ predecessor :: after, key.2.length ≤ capacity)
    (hencrypt : ∀ pk ∈ targetKey :: (before ++ predecessor :: after).map Prod.fst, ∀ bit,
      ProbComp.eval (E.encrypt n pk bit) =
        (BitString.uniformList encCoins).map (evaluateEncrypt (n, pk, bit)))
    (htest : ∀ links ∈ (ProbComp.eval (E.spliceEncryptedKeyLink n before predecessor
        (targetKey, List.replicate predecessor.2.length false) after cut challenge)).support,
      ProbComp.eval (test n
        ((before ++ predecessor :: (targetKey, List.replicate predecessor.2.length false) ::
          after).map Prod.fst, links)) = (BitString.uniformList testCoins).map
        (evaluateTest (n, (before ++ predecessor ::
          (targetKey, List.replicate predecessor.2.length false) :: after).map Prod.fst, links))) :
    ProbComp.eval (E.guessLink test n
      (activeLinkState before predecessor targetKey after cut) challenge) =
      (BitString.uniformList
        (((before.length + after.length + 1) * capacity - 1) * encCoins + testCoins)).map
        (guessLinkCoins evaluateEncrypt evaluateTest n encCoins capacity
          (activeLinkState before predecessor targetKey after cut) challenge) := by
  let target := (targetKey, List.replicate predecessor.2.length false)
  have hsplice := E.eval_spliceEncryptedKeyLink_eq_map_coins evaluateEncrypt n encCoins
    capacity before predecessor target after cut challenge hcut
    (fun key hkey => by
      simp only [List.mem_append, List.mem_cons] at hkey
      rcases hkey with h | rfl | rfl | h
      · exact hwidth _ (by simp [h])
      · exact hwidth _ (by simp)
      · simpa [target] using hwidth predecessor (by simp)
      · exact hwidth _ (by simp [h]))
    (fun key hkey bit => hencrypt key.1 (by
      simp only [List.mem_append, List.mem_cons] at hkey
      rcases hkey with h | rfl | rfl | h
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key, by simp [h], rfl⟩)
      · simp
      · simp [target]
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key, by simp [h], rfl⟩)) bit)
  rw [guessLink_active, ProbComp.eval_bind]
  trans (ProbComp.eval (E.spliceEncryptedKeyLink n before predecessor target after cut
    challenge)).bind (fun links => (BitString.uniformList testCoins).map
      (evaluateTest (n, (before ++ predecessor :: target :: after).map Prod.fst, links)))
  · exact PMF.bind_congr_on_support _ _ _ htest
  rw [hsplice, PMF.bind_map]
  simp only [PMF.map, Function.comp_def, guessLinkCoins, linkStateDecoder_decode_active, ↓reduceIte]
  exact (BitString.uniformList_bind_split _ _ (fun first second => PMF.pure
    (evaluateTest (n, (before ++ predecessor :: target :: after).map Prod.fst,
      spliceEncryptedKeyLinkCoins evaluateEncrypt n encCoins capacity before predecessor
        target after cut challenge first) second))).symm

/-- Rejected coordinates ignore every tape and the supplied challenge. -/
@[simp] theorem guessLinkCoins_reject
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateTest : (ℕ × List (List Bool) × List (List (List Bool))) → List Bool → Bool)
    (n encCoins capacity : ℕ) (challenge tape : List Bool) :
    guessLinkCoins evaluateEncrypt evaluateTest n encCoins capacity rejectLinkState
      challenge tape = false := by
  simp [guessLinkCoins]

/-- Deterministic replay is native polynomial time in the entire saved word, challenge, tape,
and unary budgets. This total certificate does not assume that the saved context is valid. -/
@[fun_prop] theorem computableInPolyTime_guessLinkCoins
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateTest : (ℕ × List (List Bool) × List (List (List Bool))) → List Bool → Bool}
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    (htest : ComputableInPolyTime (fun (input, tape) => evaluateTest input tape)
      (encPair (encPair encUnary (encPair (encList encBits) (encList (encList encBits))))
        encBits) encBool)
    {α : Type} {input : α ↪ List Bool} {n encCoins capacity : α → ℕ}
    {state challenge tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hstate : ComputableInPolyTime state input encBits)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => guessLinkCoins evaluateEncrypt evaluateTest (n a)
      (encCoins a) (capacity a) (state a) (challenge a) (tape a)) input encBool := by
  have hcontext := linkStateDecoder.computableInPolyTime.comp hstate
  dsimp only [encLinkState] at hcontext
  have hbefore := hcontext.snd'.fst'
  have hpredecessor := hcontext.snd'.snd'.fst'
  have hpk := hcontext.snd'.snd'.snd'.fst'
  have hafter := hcontext.snd'.snd'.snd'.snd'.fst'
  have hindex := hcontext.snd'.snd'.snd'.snd'.snd'
  have htarget := hpk.prod ((ComputableInPolyTime.bitsReplicate false).comp
    (ComputableInPolyTime.length_bits.comp hpredecessor.snd'))
  unfold guessLinkCoins
  apply ComputableInPolyTime.ite (by fun_prop)
  · let context := fun a => linkStateDecoder.decode (state a)
    let size := fun a => ((context a).2.1.length + (context a).2.2.2.2.1.length + 1) *
      capacity a - 1
    exact htest.comp (show ComputableInPolyTime (fun a =>
      ((n a, ((context a).2.1 ++ (context a).2.2.1 ::
        ((context a).2.2.2.1, List.replicate (context a).2.2.1.2.length false) ::
        (context a).2.2.2.2.1).map Prod.fst,
        spliceEncryptedKeyLinkCoins evaluateEncrypt (n a) (encCoins a) (capacity a)
          (context a).2.1 (context a).2.2.1
          ((context a).2.2.2.1, List.replicate (context a).2.2.1.2.length false)
          (context a).2.2.2.2.1 (context a).2.2.2.2.2 (challenge a)
          ((tape a).take (size a * encCoins a))),
        (tape a).drop (size a * encCoins a))) input
      (encPair (encPair encUnary (encPair (encList encBits) (encList (encList encBits))))
        encBits) by
      dsimp only [context, size]
      fun_prop)
  · fun_prop

end Cslib.Crypto.Homomorphic.Scheme
