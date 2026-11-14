/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrSignature.ForkPass
public import CslibFrontier.Crypto.Computational.SchnorrSignature.StatisticalROM
public import CslibFrontier.Crypto.Computational.SchnorrEavesdrop
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Interactive.Security.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Schnorr signatures are EUF-CMA secure under discrete log

This module proves that Schnorr signatures are EUF-CMA secure in the random-oracle model under the
discrete-logarithm assumption ([BonehShoup2023], Theorem 19.7 and Lemma 19.8;
[PointchevalStern2000]; [BellareNeven2006]):

```
theorem DiscreteLog.eufCma_schnorrNativeROMScheme
    (hDL : F.DiscreteLog fun n => PMF.pure (description n)) … :
    ROMSignature.EUFCMA (fun n => encBitString (width n))
      (fun n => F.schnorrNativeROMScheme n (description n) (width n))
```

`schnorrNativeROMScheme` is the scheme as its native algorithms run it, with the actual key
generator `schnorrSigKeyGen` and nonce sampler `sampleExp`. `ROMSignature.EUFCMA` says that every
uniform oracle-PPT word forger wins its EUF-CMA game `ROMSignature.wordEufCmaGame` (adaptive
signing queries, hash queries on arbitrary words, final-message freshness) with negligible
probability. The other premises fix a group family, one description per security parameter with
encoded descriptions of polynomial length, and a challenge width `w` computable in polynomial time
with `2 ^ w ≤ q` and negligible `2⁻ʷ`.

The discrete-logarithm adversary is the explicit program `schnorrForkingAdversary`. It samples the
forger's tape, `2B` strict-PPT simulated transcripts (`schnorrSimulatedTranscript`) and two banks of
`B + 1` uniform answers, where `B` is the forger's saved-coin call budget. It then runs the native
pass `schnorrForkPass` on the first bank, runs it again with the answers from the named index on
taken from the second bank, and outputs `extractNat` of the two forgeries when the fork succeeds.
`isPPTOn_schnorrForkingAdversary` certifies it as strict PPT from the forger's certificate, so
`F.DiscreteLog` applies to it.

The proof chains four steps, each about existing objects:

1. `exists_closeTo_wordEufCmaGame_schnorrNativeROMScheme` moves from the actual samplers to the
   typed word game within `(B + 1) / 2 ^ n`;
2. `succProbability_eufCmaGame_schnorrWordROMScheme_le` bounds the typed game by the one-way
   success of the typed forking reduction `schnorrWordROMSchemeReduction`;
3. `succProbability_oneWayGame_schnorrWordROMSchemeReduction_le` replaces its perfect simulator by
   the law of the strict-PPT simulator (`schnorrSampledSimulate`) within `2B / 2 ^ n`;
4. `discreteLogGame_schnorrForkingAdversary` identifies that one-way game with the discrete-log game
   of the native adversary, through `map_eval_schnorrForkingAdversary` and the exact pass agreement
   `eval_schnorrForkPass`.

The group family fixes one description per security parameter. It need not be computable: the
discrete-logarithm game gives the description to the reduction, and the saved-coin budget needs only
its encoded length to be polynomial. Random setups are not covered, because the existing game gives
the forger only the public key.

## Main definitions

* `schnorrForkingAdversary`: the native two-pass forking discrete-logarithm adversary.
* `schnorrForkOutput`: its extraction step.
* `schnorrSampledSimulate`: the law of the strict-PPT Schnorr simulator at a typed challenge.

## Main results

* `isPPTOn_schnorrForkingAdversary`: the adversary is uniform strict PPT.
* `map_eval_schnorrForkingAdversary`: its output law is that of `FiatShamir.reduction` with the
  sampled simulator.
* `succProbability_oneWayGame_schnorrWordROMSchemeReduction_le`: the statistical simulator step.
* `discreteLogGame_schnorrForkingAdversary`: its discrete-log game is that typed one-way game.
* `DiscreteLog.eufCma_schnorrNativeROMScheme`: EUF-CMA security under `F.DiscreteLog`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.2.2 (Theorem 19.7 and Lemma 19.8).
* [D. Pointcheval, J. Stern, *Security Arguments for Digital Signatures and Blind
  Signatures*][PointchevalStern2000].
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General Forking
  Lemma*][BellareNeven2006], Lemma 1.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- The output of the forking adversary from two native passes: when the first pass names a
query `j`, the second pass on answers spliced at `j` names `j` too, and the two answers at `j`
differ, the witness `extractNat` computed from the two challenges and responses; otherwise the
empty word. -/
@[expose] def schnorrForkOutput (d : F.Desc) (answers answers' : List (List Bool))
    (first second : ℕ × List Bool × List Bool) : List Bool :=
  let (index, challenge, response) := first
  let (index', challenge', response') := second
  if index ≠ 0 ∧ index' = index ∧ answers.getD (index - 1) [] ≠ answers'.getD (index - 1) [] then
    (extractNat (F.order d) (ofBits challenge) (ofBits response) (ofBits challenge')
      (ofBits response')).bits
  else []

/-- **The native forking discrete-logarithm adversary** built from a native forger's guarded
saved-coin replay ([BonehShoup2023], Lemma 19.8; [BellareNeven2006], Lemma 1). On the group
description `d` and an encoded public key, it samples the forger's tape, `2B` simulated
transcripts and two banks of `B + 1` uniform `w n`-bit answers, where `B` is the saved-coin
budget. It runs `schnorrForkPass` once, runs it again with the answers from the named index on
replaced, and extracts a discrete logarithm from the two forgeries. -/
noncomputable def schnorrForkingAdversary {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (width : ℕ → ℕ) (n : ℕ) (input : F.Desc × List Bool) : ProbComp (List Bool) := do
  let (d, pk) := input
  let budget := savedCoinBudget c e keyC keyD n
  let tape ← BitString.sampleList budget
  let transcripts ← OracleComp.replicate (budget + budget)
    (F.schnorrSimulatedTranscript n d pk (width n))
  let answers ← OracleComp.replicate (budget + 1) (BitString.sampleList (width n))
  let answers' ← OracleComp.replicate (budget + 1) (BitString.sampleList (width n))
  let first ← F.schnorrForkPass machine c e keyC keyD d ⟨n, pk, tape, ⟨transcripts, answers⟩⟩
  let second ← F.schnorrForkPass machine c e keyC keyD d
    ⟨n, pk, tape, ⟨transcripts, answers.take (first.1 - 1) ++ answers'.drop (first.1 - 1)⟩⟩
  return F.schnorrForkOutput d answers answers' first second

/-! ### Efficiency of the forking adversary -/

/-- `schnorrForkOutput` in projection form. -/
private def forkOutputProj (x : F.Desc × List (List Bool) × List (List Bool) ×
    (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool)) : List Bool :=
  if x.2.2.2.1.1 ≠ 0 ∧ x.2.2.2.2.1 = x.2.2.2.1.1 ∧
      x.2.1.getD (x.2.2.2.1.1 - 1) [] ≠ x.2.2.1.getD (x.2.2.2.1.1 - 1) [] then
    (extractNat (F.order x.1) (ofBits x.2.2.2.1.2.1) (ofBits x.2.2.2.1.2.2)
      (ofBits x.2.2.2.2.2.1) (ofBits x.2.2.2.2.2.2)).bits
  else []

/-- The output step of the forking adversary is computable in polynomial time. -/
theorem computableInPolyTime_schnorrForkOutput :
    ComputableInPolyTime
      (fun (d, answers, answers', first, second) =>
        F.schnorrForkOutput d answers answers' first second)
      (encPair F.encDesc (encPair (encList encBits) (encPair (encList encBits)
        (encPair (encPair encUnary (encPair encBits encBits))
          (encPair encUnary (encPair encBits encBits))))))
      encBits := by
  let E := encPair F.encDesc (encPair (encList encBits) (encPair (encList encBits)
    (encPair (encPair encUnary (encPair encBits encBits))
      (encPair encUnary (encPair encBits encBits)))))
  have h : (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) =>
      match x with
      | (d, answers, answers', first, second) =>
        F.schnorrForkOutput d answers answers' first second) = forkOutputProj F := by
    funext ⟨d, answers, answers', ⟨i, ch, z⟩, ⟨i', ch', z'⟩⟩
    rfl
  change ComputableInPolyTime _ E encBits
  rw [h]
  unfold forkOutputProj
  have hd : ComputableInPolyTime (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) => x.1) E F.encDesc := by
    fun_prop
  have hnat {f : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) → List Bool}
      (hf : ComputableInPolyTime f E encBits) :
      ComputableInPolyTime (fun x => ofBits (f x)) E encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hf.tidy)
  have hextract := computableInPolyTime_extractNat hd
    (hnat (f := fun x => x.2.2.2.1.2.1) (by fun_prop))
    (hnat (f := fun x => x.2.2.2.1.2.2) (by fun_prop))
    (hnat (f := fun x => x.2.2.2.2.2.1) (by fun_prop))
    (hnat (f := fun x => x.2.2.2.2.2.2) (by fun_prop))
  have hbits := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.natBits.comp hextract.tidy)
  have hi : ComputableInPolyTime (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) => x.2.2.2.1.1 - 1)
      E encUnary := by
    fun_prop
  have hget : ComputableInPolyTime (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) =>
        x.2.1.getD (x.2.2.2.1.1 - 1) []) E encBits :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) hi []
  have hget' : ComputableInPolyTime (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) =>
        x.2.2.1.getD (x.2.2.2.1.1 - 1) []) E encBits :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) hi []
  fun_prop

/-- **The forking adversary is uniform strict PPT** whenever the challenge width is computable in
polynomial time. The forger enters only through its replay machine, whose full-input certificate
`isPPTOn_schnorrForkPass` is part of the native pass. -/
theorem isPPTOn_schnorrForkingAdversary {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    {width : ℕ → ℕ} (hwidth : ComputableInPolyTime width encUnary encUnary) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => F.schnorrForkingAdversary machine c e keyC keyD width input.1 input.2) := by
  let E := encPair encUnary (encPair F.encDesc encBits)
  have hn : ComputableInPolyTime (fun a : ℕ × F.Desc × List Bool => a.1) E encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun a : ℕ × F.Desc × List Bool => a.2.1) E F.encDesc := by
    fun_prop
  have hpk : ComputableInPolyTime (fun a : ℕ × F.Desc × List Bool => a.2.2) E encBits := by
    fun_prop
  have hB : ComputableInPolyTime (fun n => savedCoinBudget c e keyC keyD n) encUnary encUnary := by
    unfold savedCoinBudget
    fun_prop
  have hbudget : ComputableInPolyTime
      (fun a : ℕ × F.Desc × List Bool => savedCoinBudget c e keyC keyD a.1) E encUnary :=
    hB.comp hn
  have hm : ComputableInPolyTime (fun a : ℕ × F.Desc × List Bool => width a.1) E encUnary :=
    hwidth.comp hn
  have hfun : (fun input : ℕ × F.Desc × List Bool =>
      F.schnorrForkingAdversary machine c e keyC keyD width input.1 input.2) = fun a =>
    BitString.sampleList (savedCoinBudget c e keyC keyD a.1) >>= fun tape =>
    OracleComp.replicate (savedCoinBudget c e keyC keyD a.1 + savedCoinBudget c e keyC keyD a.1)
      (F.schnorrSimulatedTranscript a.1 a.2.1 a.2.2 (width a.1)) >>= fun transcripts =>
    OracleComp.replicate (savedCoinBudget c e keyC keyD a.1 + 1)
      (BitString.sampleList (width a.1)) >>= fun answers =>
    OracleComp.replicate (savedCoinBudget c e keyC keyD a.1 + 1)
      (BitString.sampleList (width a.1)) >>= fun answers' =>
    F.schnorrForkPass machine c e keyC keyD a.2.1 ⟨a.1, a.2.2, tape, ⟨transcripts, answers⟩⟩ >>=
      fun first =>
    F.schnorrForkPass machine c e keyC keyD a.2.1 ⟨a.1, a.2.2, tape, ⟨transcripts,
      answers.take (first.1 - 1) ++ answers'.drop (first.1 - 1)⟩⟩ >>= fun second =>
    pure (F.schnorrForkOutput a.2.1 answers answers' first second) := by
    funext ⟨n, d, pk⟩
    rfl
  rw [hfun]
  refine hbudget.sampleList.bind_with ?_
  have htr := (F.isPPTOn_schnorrSimulatedTranscript (hn.comp (.fst E encBits))
    (hd.comp (.fst E encBits)) (hpk.comp (.fst E encBits)) (hm.comp (.fst E encBits))).replicate
    (count := fun p : (ℕ × F.Desc × List Bool) × List Bool =>
      savedCoinBudget c e keyC keyD p.1.1 + savedCoinBudget c e keyC keyD p.1.1)
    (by have := hbudget.comp (.fst E encBits); fun_prop)
  refine htr.bind_with ?_
  let E₂ := encPair (encPair E encBits) (encList encTranscript)
  have hfst₂ : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool) => p.1.1) E₂ E := by fun_prop
  have hans := (ComputableInPolyTime.sampleList (hm.comp hfst₂)).replicate
    (count := fun p => savedCoinBudget c e keyC keyD p.1.1.1 + 1)
    (by have := hbudget.comp hfst₂; fun_prop)
  refine hans.bind_with ?_
  let E₃ := encPair E₂ (encList encBits)
  have hfst₃ : ComputableInPolyTime
      (fun p : (((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool) => p.1.1.1) E₃ E := by
    fun_prop
  have hans' := (ComputableInPolyTime.sampleList (hm.comp hfst₃)).replicate
    (count := fun p => savedCoinBudget c e keyC keyD p.1.1.1.1 + 1)
    (by have := hbudget.comp hfst₃; fun_prop)
  refine hans'.bind_with ?_
  have hpass : IsPPTOn (encPair F.encDesc encSchnorrForkPassInput)
      (encPair encUnary (encPair encBits encBits))
      (fun x : F.Desc × SchnorrForkPassInput => F.schnorrForkPass machine c e keyC keyD x.1 x.2) :=
    (F.isPPTOn_schnorrForkPass machine c e keyC keyD).congr fun _ => rfl
  let E₄ := encPair E₃ (encList encBits)
  have hprep₁ : ComputableInPolyTime
      (fun p : ((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool) =>
        (p.1.1.1.1.2.1, (⟨p.1.1.1.1.1, p.1.1.1.1.2.2, p.1.1.1.2, ⟨p.1.1.2, p.1.2⟩⟩ :
          SchnorrForkPassInput)))
      E₄ (encPair F.encDesc encSchnorrForkPassInput) := by fun_prop
  refine (hpass.preprocess hprep₁).bind_with ?_
  let E₅ := encPair E₄ (encPair encUnary (encPair encBits encBits))
  have hindex : ComputableInPolyTime
      (fun p : (((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool)) ×
          (ℕ × List Bool × List Bool) => p.2.1 - 1) E₅ encUnary := by fun_prop
  have htake : ComputableInPolyTime
      (fun p : (((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool)) ×
          (ℕ × List Bool × List Bool) => p.1.1.2.take (p.2.1 - 1)) E₅ (encList encBits) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput (by fun_prop) hindex.tidy)
  have hdrop : ComputableInPolyTime
      (fun p : (((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool)) ×
          (ℕ × List Bool × List Bool) => p.1.2.drop (p.2.1 - 1)) E₅ (encList encBits) :=
    .of_tidy (ComputableTidilyInPolyTime.listDropWithInput (by fun_prop) hindex.tidy)
  have hprep₂ : ComputableInPolyTime
      (fun p : (((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool)) ×
          (ℕ × List Bool × List Bool) =>
        (p.1.1.1.1.1.2.1, (⟨p.1.1.1.1.1.1, p.1.1.1.1.1.2.2, p.1.1.1.1.2, ⟨p.1.1.1.2,
          p.1.1.2.take (p.2.1 - 1) ++ p.1.2.drop (p.2.1 - 1)⟩⟩ : SchnorrForkPassInput)))
      E₅ (encPair F.encDesc encSchnorrForkPassInput) := by fun_prop
  refine (hpass.preprocess hprep₂).bind_with ?_
  have hout := F.computableInPolyTime_schnorrForkOutput
  have hshape : (fun x : F.Desc × List (List Bool) × List (List Bool) ×
      (ℕ × List Bool × List Bool) × (ℕ × List Bool × List Bool) =>
      match x with
      | (d, answers, answers', first, second) =>
        F.schnorrForkOutput d answers answers' first second) =
      fun x => F.schnorrForkOutput x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
    funext ⟨_, _, _, _, _⟩
    rfl
  rw [hshape] at hout
  have hprep₃ : ComputableInPolyTime
      (fun p : ((((((ℕ × F.Desc × List Bool) × List Bool) ×
        List (List Bool × List Bool × List Bool)) × List (List Bool)) × List (List Bool)) ×
          (ℕ × List Bool × List Bool)) × (ℕ × List Bool × List Bool) =>
        (p.1.1.1.1.1.1.2.1, p.1.1.1.2, p.1.1.2, p.1.2, p.2))
      (encPair E₅ (encPair encUnary (encPair encBits encBits)))
      (encPair F.encDesc (encPair (encList encBits) (encPair (encList encBits)
        (encPair (encPair encUnary (encPair encBits encBits))
          (encPair encUnary (encPair encBits encBits)))))) := by fun_prop
  have hf := hout.comp hprep₃
  simp only [Function.comp_def] at hf
  exact hf.isPPTOn

/-! ### The adversary's law -/

section Law

variable {F}

/-- The law of the strict-PPT Schnorr simulator at a typed challenge: a sampled scalar response `z`
and the commitment `z • g - c • u`, with the challenge read as a binary number. -/
noncomputable def schnorrSampledSimulate (n : ℕ) (d : F.Desc) {m : ℕ} (u : F.Carrier d)
    (c : BitString m) : PMF (List Bool × List Bool) :=
  ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map fun z =>
    (F.encode d (z • F.generator d - (ofBits (List.ofFn c) : ZMod (F.order d)) • u), z.val.bits)

/-- A strict-PPT simulated transcript is a typed simulated conversation, written as words. -/
theorem eval_schnorrSimulatedTranscript_eq_map (n : ℕ) (d : F.Desc) (m : ℕ) (u : F.Carrier d) :
    ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d u) m) =
      (simulateConversation (schnorrSampledSimulate n d (m := m)) u).map transcriptWords := by
  rw [eval_schnorrSimulatedTranscript, BitString.uniformList, PMF.bind_map]
  simp only [simulateConversation, schnorrSampledSimulate, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def]
  congr 1 with c : 1
  rw [← PMF.bind_pure_comp, PMF.bind_map]
  rfl

/-- `k` strict-PPT simulated transcripts are `k` typed simulated conversations, written as
words. -/
theorem eval_replicate_schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (m k : ℕ)
    (u : F.Carrier d) :
    ProbComp.eval (OracleComp.replicate k (F.schnorrSimulatedTranscript n d (F.encode d u) m)) =
      (PMF.iid (simulateConversation (schnorrSampledSimulate n d (m := m)) u) k).map
        fun transcripts => (List.ofFn transcripts).map transcriptWords := by
  rw [ProbComp.eval_replicate_iid, eval_schnorrSimulatedTranscript_eq_map, PMF.iid_map,
    PMF.map_comp]
  congr 1 with transcripts : 1
  simp [List.map_ofFn, Function.comp_def]

/-- A query named by the typed forking algorithm was answered with the forgery's challenge. -/
private theorem forkingAlgorithm_challenge {m q : ℕ} (d : F.Desc) (hm : 2 ^ m ≤ F.order d)
    (A : Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) (BitString m))
    (s : F.Carrier d × A.Coins × List (List Bool × BitString m × List Bool))
    (answers : Fin q → BitString m) (default : BitString m) {j : Fin q}
    (hj : (OracleComp.forkingAlgorithm default q (FiatShamir.forkingProgram
      (encPair encBits encBits) (F.schnorrWordSigma d hm) A) s answers).1 = some j) :
    (OracleComp.forkingAlgorithm default q (FiatShamir.forkingProgram
      (encPair encBits encBits) (F.schnorrWordSigma d hm) A) s answers).2.1.2.challenge =
      answers j := by
  obtain ⟨y, coins, transcripts⟩ := s
  simp only [OracleComp.forkingAlgorithm] at hj ⊢
  generalize hrun : OracleComp.runWithAnswers default (FiatShamir.forkingProgram
    (encPair encBits encBits) (F.schnorrWordSigma d hm) A (y, coins, transcripts))
    (List.ofFn answers) = run at hj ⊢
  obtain ⟨⟨position, outcome⟩, queries⟩ := run
  obtain ⟨hposition, -⟩ := OracleComp.validIndex_eq_some hj
  have h := (ForkingReduction.runWithAnswers_program default
    (FiatShamir.signer (Z := List Bool) (encPair encBits encBits))
    (FiatShamir.check (encPair encBits encBits) (F.schnorrWordSigma d hm) y)
    (FiatShamir.rejectsProgrammed (encPair encBits encBits) _ y) (A.forge y coins) transcripts
    (List.ofFn answers) hrun).2 j hposition
  rw [← h.2.1, List.getD_ofFn]

private theorem forkRunWords_eq {q m : ℕ}
    (r : Option (Fin q) × ((Option ℕ × ForkingReduction.Outcome (List Bool) (List Bool)
      (BitString m) (List Bool)) × List (List Bool))) :
    forkRunWords r = (forkIndexCode r.1, List.ofFn r.2.1.2.challenge, r.2.1.2.response) := by
  obtain ⟨_, ⟨_, _⟩, _⟩ := r
  rfl

/-- The second pass's answers are the two banks spliced at the index that the first pass names. -/
private theorem take_append_drop_forkRunWords {q m : ℕ}
    (r : Option (Fin (q + 1)) × ((Option ℕ × ForkingReduction.Outcome (List Bool) (List Bool)
      (BitString m) (List Bool)) × List (List Bool)))
    (answers answers' : Fin (q + 1) → BitString m) :
    ((List.ofFn answers).map List.ofFn).take ((forkRunWords r).1 - 1) ++
        ((List.ofFn answers').map List.ofFn).drop ((forkRunWords r).1 - 1) =
      (List.ofFn (Probability.Forking.splice (r.1.getD 0) answers answers')).map List.ofFn := by
  obtain ⟨index, _, _⟩ := r
  rw [Probability.Forking.ofFn_splice, List.map_append, List.map_take, List.map_drop]
  cases index <;> simp [forkRunWords, forkIndexCode]

/-- **The native forking adversary realizes the typed forking reduction** with the sampled
simulator: on a canonical public key, its output read as a scalar has exactly the law of
`FiatShamir.reduction` for `schnorrWordROMScheme`, the decoded saved-coin forger and
`schnorrSampledSimulate`, with call budgets `B` and `B`. -/
theorem map_eval_schnorrForkingAdversary {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (width : ℕ → ℕ) (n : ℕ) (d : F.Desc) (hm : 2 ^ width n ≤ F.order d) (u : F.Carrier d) :
    (ProbComp.eval (F.schnorrForkingAdversary machine c e keyC keyD width n (d, F.encode d u))).map
        (fun guess => (ofBits guess : ZMod (F.order d))) =
      FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma d hm)
        (schnorrSampledSimulate n d) (F.schnorrWordExtract d hm) 0
        (F.schnorrDecodedForger d (savedCoinForger machine (encBitString (width n))
          c e keyC keyD n))
        (savedCoinBudget c e keyC keyD n) (savedCoinBudget c e keyC keyD n) u := by
  simp only [schnorrForkingAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, eval_replicate_schnorrSimulatedTranscript,
    ProbComp.eval_replicate_sampleList, PMF.bind_map]
  simp only [FiatShamir.reduction, Probability.Forking.fork, FiatShamir.coins,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
    PMF.bind_map, PMF.pure_map, Function.comp_def]
  refine congrArg _ (funext fun tape => congrArg _ (funext fun transcripts =>
    congrArg _ (funext fun answers => congrArg _ (funext fun answers' => ?_))))
  have hlen : savedCoinBudget c e keyC keyD n ≤ (List.ofFn transcripts).length := by simp
  rw [eval_schnorrForkPass F machine c e keyC keyD n d hm u tape (List.ofFn transcripts) hlen
    answers (Classical.arbitrary _), PMF.pure_bind, take_append_drop_forkRunWords,
    eval_schnorrForkPass F machine c e keyC keyD n d hm u tape (List.ofFn transcripts) hlen
    _ (Classical.arbitrary _), PMF.pure_bind]
  congr 1
  have hchal := fun (a : Fin (savedCoinBudget c e keyC keyD n + 1) → BitString (width n)) j hj =>
    forkingAlgorithm_challenge d hm (F.schnorrDecodedForger d
    (savedCoinForger machine (encBitString (width n)) c e keyC keyD n))
    (u, tape, List.ofFn transcripts) a (Classical.arbitrary _) (j := j) hj
  simp only [forkRunWords_eq, schnorrForkOutput]
  set A := F.schnorrDecodedForger d
    (savedCoinForger machine (encBitString (width n)) c e keyC keyD n) with hA
  rcases hidx : (OracleComp.forkingAlgorithm (Classical.arbitrary (BitString (width n)))
      (savedCoinBudget c e keyC keyD n + 1) (FiatShamir.forkingProgram (encPair encBits encBits)
        (F.schnorrWordSigma d hm) A) (u, tape, List.ofFn transcripts) answers).1 with _ | j
  · simp [forkIndexCode, ofBits]
  · have hc₁ := hchal answers j hidx
    rw [Option.getD_some]
    have hget (a : Fin (savedCoinBudget c e keyC keyD n + 1) → BitString (width n)) :
        ((List.ofFn a).map List.ofFn).getD (forkIndexCode (some j) - 1) [] = List.ofFn (a j) := by
      simp only [forkIndexCode, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_ofFn, j.isLt, dite_true, Option.map_some,
        Option.getD_some]
    simp only [hget]
    rcases hidx₂ : (OracleComp.forkingAlgorithm (Classical.arbitrary (BitString (width n)))
        (savedCoinBudget c e keyC keyD n + 1) (FiatShamir.forkingProgram (encPair encBits encBits)
          (F.schnorrWordSigma d hm) A) (u, tape, List.ofFn transcripts)
          (Probability.Forking.splice j answers answers')).1 with _ | j'
    · simp [forkIndexCode, ofBits]
    · by_cases hcond : j' = j ∧ answers j ≠ answers' j
      · obtain ⟨rfl, hne⟩ := hcond
        have hc₂ := hchal _ j' hidx₂
        have hsj : Probability.Forking.splice j' answers answers' j' = answers' j' := by
          simp [Probability.Forking.splice]
        rw [hsj] at hc₂
        have hne' : List.ofFn (answers j') ≠ List.ofFn (answers' j') :=
          fun h => hne (List.ofFn_injective h)
        have hlhs : forkIndexCode (some j') ≠ 0 ∧
            forkIndexCode (some j') = forkIndexCode (some j') ∧
            List.ofFn (answers j') ≠ List.ofFn (answers' j') := ⟨by simp [forkIndexCode], rfl, hne'⟩
        have hrhs : some j' = some j' ∧ answers j' ≠ answers' j' := ⟨rfl, hne⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlhs), ite_eq_left_of_eq_true _ _ (eq_true hrhs)]
        simp only [ofBits_bits]
        generalize OracleComp.forkingAlgorithm (Classical.arbitrary (BitString (width n)))
          (savedCoinBudget c e keyC keyD n + 1) (FiatShamir.forkingProgram (encPair encBits encBits)
            (F.schnorrWordSigma d hm) A) (u, tape, List.ofFn transcripts) answers = r₁ at hc₁ ⊢
        generalize OracleComp.forkingAlgorithm (Classical.arbitrary (BitString (width n)))
          (savedCoinBudget c e keyC keyD n + 1) (FiatShamir.forkingProgram (encPair encBits encBits)
            (F.schnorrWordSigma d hm) A) (u, tape, List.ofFn transcripts)
            (Probability.Forking.splice j' answers answers') = r₂ at hc₂ ⊢
        obtain ⟨_, ⟨_, outcome₁⟩, _⟩ := r₁
        obtain ⟨_, ⟨_, outcome₂⟩, _⟩ := r₂
        dsimp only at hc₁ hc₂ ⊢
        have hdiff : ((ofBits (List.ofFn outcome₁.challenge) : ℕ) : ZMod (F.order d)) ≠
            ofBits (List.ofFn outcome₂.challenge) := by
          have := (F.challengeEmbedding d hm).injective.ne
            (show outcome₁.challenge ≠ outcome₂.challenge by rw [hc₁, hc₂]; exact hne)
          exact this
        rw [extractNat_cast hdiff]
        simp only [schnorrWordExtract, linearExtract, smul_eq_mul]
        rfl
      · have hl : ¬(forkIndexCode (some j) ≠ 0 ∧ forkIndexCode (some j') = forkIndexCode (some j) ∧
            List.ofFn (answers j) ≠ List.ofFn (answers' j)) := fun ⟨_, h₂, h₃⟩ =>
          hcond ⟨Fin.ext (by simpa [forkIndexCode] using h₂), fun h => h₃ (by rw [h])⟩
        have hr : ¬(some j' = some j ∧ answers j ≠ answers' j) := fun ⟨h₁, h₂⟩ =>
          hcond ⟨Option.some_injective _ h₁, h₂⟩
        simp only [hl, hr, ite_false]
        simp [ofBits]

/-! ### The statistical step -/

/-- The strict-PPT simulator's conversations are within `2⁻ⁿ` of the perfect simulator's. -/
theorem closeTo_simulateConversation_schnorrSampledSimulate (n : ℕ) (d : F.Desc) {m : ℕ}
    (hm : 2 ^ m ≤ F.order d) (u : F.Carrier d) :
    CloseTo (simulateConversation (F.schnorrWordSimulate d hm) u)
      (simulateConversation (schnorrSampledSimulate n d (m := m)) u) (1 / 2 ^ n : ℝ≥0) := by
  unfold simulateConversation
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine CloseTo.bind_right _ fun c _ => CloseTo.bind_left ?_ _
  have h := (F.closeTo_uniform_sampleExp n d).map fun z : ZMod (F.order d) =>
    (F.encode d (z • F.generator d - (ofBits (List.ofFn c) : ZMod (F.order d)) • u), z.val.bits)
  simp only [schnorrWordSimulate, linearSimulate, schnorrSampledSimulate, PMF.map_comp,
    Function.comp_def] at h ⊢
  exact h

/-- Replacing the perfect simulator by the strict-PPT simulator's law in the typed forking
reduction costs at most `2⁻ⁿ` per presampled transcript. -/
theorem closeTo_schnorrWordROMSchemeReduction (n : ℕ) (d : F.Desc) {m : ℕ}
    (hm : 2 ^ m ≤ F.order d)
    (A : Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) (BitString m))
    (Qs Qro : ℕ) (u : F.Carrier d) :
    CloseTo (F.schnorrWordROMSchemeReduction d hm A Qs Qro u)
      (FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma d hm)
        (schnorrSampledSimulate n d) (F.schnorrWordExtract d hm) 0 A Qs Qro u)
      ((Qs + Qro : ℕ) * (1 / 2 ^ n : ℝ≥0)) := by
  unfold schnorrWordROMSchemeReduction FiatShamir.reduction Probability.Forking.fork
    FiatShamir.coins
  refine CloseTo.map ?_ _
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine CloseTo.bind_left ?_ _
  refine CloseTo.bind_right _ fun s _ => CloseTo.bind_left ?_ _
  exact ((closeTo_simulateConversation_schnorrSampledSimulate n d hm u).iid _).map _

/-- **The statistical step.** The typed forking reduction with the perfect simulator wins the
one-way game at most `(Qs + Qro) / 2 ^ n` more often than with the strict-PPT simulator's law. -/
theorem succProbability_oneWayGame_schnorrWordROMSchemeReduction_le (n : ℕ) (d : F.Desc)
    {m : ℕ} (hm : 2 ^ m ≤ F.order d)
    (A : Forger (F.Carrier d) (List Bool) (List Bool × List Bool) (List Bool) (BitString m))
    (Qs Qro : ℕ) :
    (Game.succProbability (oneWayGame (schnorrKeyGen (F.generator d))
        (fun α u => α • F.generator d = u) (F.schnorrWordROMSchemeReduction d hm A Qs Qro)) : ℝ) ≤
      Game.succProbability (oneWayGame (schnorrKeyGen (F.generator d))
        (fun α u => α • F.generator d = u)
        (FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma d hm)
          (schnorrSampledSimulate n d) (F.schnorrWordExtract d hm) 0 A Qs Qro)) +
        (Qs + Qro) / 2 ^ n := by
  have h : CloseTo (oneWayGame (schnorrKeyGen (F.generator d))
      (fun α u => α • F.generator d = u) (F.schnorrWordROMSchemeReduction d hm A Qs Qro))
      (oneWayGame (schnorrKeyGen (F.generator d)) (fun α u => α • F.generator d = u)
        (FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma d hm)
          (schnorrSampledSimulate n d) (F.schnorrWordExtract d hm) 0 A Qs Qro))
      ((((Qs + Qro : ℕ) : ℝ≥0) * (1 / 2 ^ n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    unfold oneWayGame
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    refine CloseTo.bind_right _ fun key _ => CloseTo.bind_left ?_ _
    have := closeTo_schnorrWordROMSchemeReduction n d hm A Qs Qro key.2
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using this
  have hle := Game.coe_succProbability_le_add_of_advantage_le
    (NNReal.coe_le_coe.mpr (Game.closeTo_iff_advantage_le.mp h))
  have hδ : ((((Qs + Qro : ℕ) : ℝ≥0) * (1 / 2 ^ n : ℝ≥0) : ℝ≥0) : ℝ) = (Qs + Qro) / 2 ^ n := by
    push_cast
    ring
  rwa [hδ] at hle

/-- **The native adversary's discrete-log game is the typed one-way game** of the forking
reduction with the strict-PPT simulator's law, at a deterministic group description. -/
theorem discreteLogGame_schnorrForkingAdversary {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (width : ℕ → ℕ) (description : ℕ → F.Desc) (n : ℕ)
    (hm : 2 ^ width n ≤ F.order (description n)) :
    F.discreteLogGame (fun n => PMF.pure (description n))
        (F.schnorrForkingAdversary machine c e keyC keyD width) n =
      oneWayGame (schnorrKeyGen (F.generator (description n)))
        (fun α u => α • F.generator (description n) = u)
        (FiatShamir.reduction (encPair encBits encBits) (F.schnorrWordSigma (description n) hm)
          (schnorrSampledSimulate n (description n)) (F.schnorrWordExtract (description n) hm) 0
          (F.schnorrDecodedForger (description n)
            (savedCoinForger machine (encBitString (width n)) c e keyC keyD n))
          (savedCoinBudget c e keyC keyD n) (savedCoinBudget c e keyC keyD n)) := by
  rw [oneWayGame_schnorrKeyGen_eq]
  simp only [discreteLogGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
  refine congrArg _ (funext fun α => ?_)
  rw [← map_eval_schnorrForkingAdversary machine c e keyC keyD width n (description n) hm,
    PMF.map_comp, ← PMF.bind_pure_comp]
  rfl

end Law

/-! ### Security under the discrete-logarithm assumption -/

variable {F} in
/-- **Schnorr signatures are EUF-CMA secure in the random-oracle model under the
discrete-logarithm assumption** ([BonehShoup2023], Theorem 19.7 and Lemma 19.8;
[PointchevalStern2000]; [BellareNeven2006]). Fix a group family `description`, one description
per security parameter with encoded length polynomial in `n`, and a challenge width `w` computable
in polynomial time with `2 ^ w n ≤ q` and negligible `1 / 2 ^ w n`. If discrete logarithms are
hard for the setup `fun n => PMF.pure (description n)`, then the native Schnorr scheme with
`w n`-bit challenges is EUF-CMA secure in the random-oracle model: every uniform oracle-PPT word
forger wins `ROMSignature.wordEufCmaGame` with negligible probability. The game uses the actual key
generator `schnorrSigKeyGen` and nonce sampler `sampleExp`, adaptive signing queries, hash queries
on arbitrary words, and final-message freshness.

The premises are the discrete-logarithm assumption and the parameter side conditions; the
forger's certificate is part of `ROMSignature.EUFCMA`. The proof applies `F.DiscreteLog` to the
explicit two-pass adversary `schnorrForkingAdversary`, whose certificate
`isPPTOn_schnorrForkingAdversary` is derived from the forger's. The family need not be computable,
because the discrete-logarithm game gives the description to the reduction. Random setups are not
covered: the game gives the forger only the public key. -/
theorem DiscreteLog.eufCma_schnorrNativeROMScheme {description : ℕ → F.Desc}
    (hDL : F.DiscreteLog fun n => PMF.pure (description n))
    (hdescription : PolynomiallyBounded fun n => (F.encDesc (description n)).length)
    {width : ℕ → ℕ} (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hwq : ∀ n, 2 ^ width n ≤ F.order (description n))
    (hchallenge : Negligible fun n => (1 / 2 ^ width n : ℝ≥0)) :
    ROMSignature.EUFCMA (fun n => encBitString (width n))
      (fun n => F.schnorrNativeROMScheme n (description n) (width n)) := by
  refine ROMSignature.EUFCMA.of_negligible fun program hprogram => ?_
  obtain ⟨k, Control, hfinite, machine, c, e, keyC, keyD, -, hgame⟩ :=
    F.exists_closeTo_wordEufCmaGame_schnorrNativeROMScheme description hdescription width hwq
      hprogram
  have hadversary := F.isPPTOn_schnorrForkingAdversary machine c e keyC keyD hwidth
  have hbreak := hDL _ hadversary
  have hbudget := polynomiallyBounded_savedCoinBudget c e keyC keyD
  have hbound : ∀ n, (Game.succProbability (wordEufCmaGame (encBitString (width n))
      (F.schnorrNativeROMScheme n (description n) (width n)) (program n)) : ℝ) ≤
      savedCoinBudget c e keyC keyD n *
          (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n) / 2 ^ width n +
        (savedCoinBudget c e keyC keyD n + 1) / 2 ^ width n +
        √((savedCoinBudget c e keyC keyD n + 1) *
          (Game.succProbability (F.discreteLogGame (fun n => PMF.pure (description n))
            (F.schnorrForkingAdversary machine c e keyC keyD width) n) +
            (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n) / 2 ^ n)) +
        (savedCoinBudget c e keyC keyD n + 1) / 2 ^ n := by
    intro n
    obtain ⟨hcall, hclose⟩ := hgame n
    have hworld := Game.coe_succProbability_le_add_of_advantage_le
      (NNReal.coe_le_coe.mpr (Game.closeTo_iff_advantage_le.mp hclose))
    have hforgery := F.succProbability_eufCmaGame_schnorrWordROMScheme_le (description n) (hwq n)
      _ (F.callBounded_schnorrDecodedForger (description n) hcall)
    have hstat := succProbability_oneWayGame_schnorrWordROMSchemeReduction_le n (description n)
      (hwq n) (F.schnorrDecodedForger (description n)
        (savedCoinForger machine (encBitString (width n)) c e keyC keyD n))
      (savedCoinBudget c e keyC keyD n) (savedCoinBudget c e keyC keyD n)
    rw [← discreteLogGame_schnorrForkingAdversary machine c e keyC keyD width description n
      (hwq n)] at hstat
    have hq : (savedCoinBudget c e keyC keyD n *
        (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n) : ℝ) /
          F.order (description n) ≤
        savedCoinBudget c e keyC keyD n *
          (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n) / 2 ^ width n := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast hwq n
    have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hstat
      (by positivity : (0 : ℝ) ≤ savedCoinBudget c e keyC keyD n + 1))
    have hδ : ((((savedCoinBudget c e keyC keyD n + 1 : ℕ) : ℝ≥0) * (1 / 2 ^ n : ℝ≥0) : ℝ≥0) : ℝ) =
        (savedCoinBudget c e keyC keyD n + 1) / 2 ^ n := by
      push_cast
      ring
    rw [hδ] at hworld
    linarith
  negligible using hbound

end Cslib.Crypto.PrimeOrderGroupFamily
