/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Native runtime of the chosen-message experiment

The actual experiment composes key generation, message selection, encryption and guessing.
Native certificates charge the complete sampled public key, saved adversary state and challenge
ciphertext; no independent bound on those intermediate values is assumed.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_gameOn`, `Cslib.Crypto.Encryption.isPPTOn_game`: the
  experiments are uniform strict PPT when their inputs are efficiently computed, the admissibility
  predicate is computable in polynomial time, and the honest algorithms and adversary have native
  certificates.
* `Cslib.Crypto.Encryption.AdversaryOf.IsPPT.restrict`: restricting a uniform strict PPT adversary
  by a polynomial-time admissibility predicate keeps it uniform strict PPT.
* `Cslib.Crypto.Encryption.INDCPAOf.indcpaOn`, `Cslib.Crypto.Encryption.INDCPAOf.wordINDCPA`:
  unrestricted IND-CPA implies IND-CPA under every polynomial-time admissibility predicate, in
  particular `WordINDCPA` for bit-word encryption.
* `Cslib.Crypto.Encryption.exists_keyLength_bound`: key generation supplies an executable unary
  polynomial bounding all supported public and secret keys.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2, Attack Game 11.1, p. 436.
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The chosen-message experiment `gameOn valid` has a strict clock in the full encoded caller input
when `valid` is computable in polynomial time. -/
@[fun_prop]
theorem isPPTOn_gameOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => gameOn valid keyGen encrypt adversary (bit a) (n a)) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold gameOn
  ppt

/-- The unrestricted chosen-message experiment has a strict clock in the full encoded caller
input. -/
@[fun_prop]
theorem isPPTOn_game {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => game keyGen encrypt adversary (bit a) (n a)) :=
  isPPTOn_gameOn (ComputableInPolyTime.const true) hkeyGen hencrypt
    hadversary hn hbit

/-- Restricting a uniform strict PPT adversary by a polynomial-time admissibility predicate keeps
it uniform strict PPT: `choose` additionally evaluates `valid` and prepends one bit to the saved
state, and `guess` branches on that bit. -/
theorem AdversaryOf.IsPPT.restrict {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary) :
    AdversaryOf.IsPPT encMsg (adversary.restrict valid) where
  choose := by
    have hchoose := hadversary.choose
    unfold Probability.IsPPT AdversaryOf.restrict
    ppt
  guess := by
    have hguess := hadversary.guess
    unfold AdversaryOf.restrict
    ppt

/-- Unrestricted IND-CPA implies IND-CPA under every polynomial-time admissibility predicate. -/
theorem INDCPAOf.indcpaOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAOf encMsg keyGen encrypt)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool) :
    INDCPAOn valid encMsg keyGen encrypt := by
  intro adversary hadversary
  simpa only [eval_game_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

/-- Unrestricted bit-word IND-CPA implies `WordINDCPA`. -/
theorem INDCPAOf.wordINDCPA
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (h : INDCPAOf encBits keyGen encrypt) :
    WordINDCPA keyGen encrypt :=
  h.indcpaOn (ComputableInPolyTime.of_tidy (by polytime))

/-- Strict PPT key generation supplies an executable unary polynomial bounding the total public
and secret key material on every supported execution. No width function is assumed computable. -/
theorem exists_keyLength_bound {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen) :
    ∃ c d : ℕ,
      ComputableInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary ∧
      ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
        keys.1.length + keys.2.length ≤ c * (n + 1) ^ d := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  obtain ⟨c, d, hlength⟩ := hkeyGen.length_le
  refine ⟨c, d, by fun_prop, fun n keys hkeys => ?_⟩
  have hbound := hlength n keys hkeys
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hbound
  omega

end Cslib.Crypto.Encryption
