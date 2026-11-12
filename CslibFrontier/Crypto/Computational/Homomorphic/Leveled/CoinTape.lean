/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
public import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Saved tapes for the encrypted-link reduction

The deterministic evaluator below executes the existing reduction's choice stage from an
explicit tape. Disjoint blocks supply each generated key and the two modular indices. The
distribution laws allocate one block per component call in an active branch; rejected branches
may ignore blocks. They include rejected coordinates and zero depth. Modular selection keeps its
original distribution, rather than replacing it
by an ideal uniform index.

This is an execution-level coin bound for one stage of the reduction. It does not assert the
full multiplicative Turing-machine runtime bound of [Gentry2009, Section 2, Theorem 4].

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.chooseLinkAtCoins`: replay known-key generation and choice.
* `Cslib.Crypto.Homomorphic.Scheme.chooseModLinkCoins`: replay modular selection and choice.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_chooseLinkAt_eq_map_coins`: exact fixed-coordinate law.
* `Cslib.Crypto.Homomorphic.Scheme.eval_modLinkAdversary_choose_eq_map_coins`: exact modular law.
* `Cslib.Crypto.Homomorphic.Scheme.exists_modLinkAdversary_choose_coin_evaluator`: native replay
  and an explicit polynomial seed budget from strict-PPT key generation.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- Replay the choice at supplied coordinates. Every key gets its own `keyCoins`-bit block;
the caller's total evaluator determines the behavior on short or malformed tapes. -/
@[expose] def chooseLinkAtCoins (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (n keyCoins beforeCount afterCount bitIndex : ℕ) (challengePk tape : List Bool) :
    (Bool × Bool) × List Bool :=
  let before := (BitString.listRows beforeCount keyCoins
    (tape.take (beforeCount * keyCoins))).map (evaluateKey n)
  let remaining := tape.drop (beforeCount * keyCoins)
  let predecessor := evaluateKey n (remaining.take keyCoins)
  let after := (BitString.listRows afterCount keyCoins (remaining.drop keyCoins)).map
    (evaluateKey n)
  if bitIndex < predecessor.2.length then
    ((predecessor.2.getD bitIndex false, false),
      activeLinkState before predecessor challengePk after bitIndex)
  else rejectLinkChoice

/-- Replay the existing modular link selection. The first two blocks supply the reverse-link
and bit indices; the remaining blocks supply all `depth` known keys in an active branch. -/
@[expose] def chooseModLinkCoins (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (n indexCoins keyCoins depth capacity : ℕ) (challengePk tape : List Bool) :
    (Bool × Bool) × List Bool :=
  let reverseIndex := min depth (BitString.binaryValue (tape.take indexCoins) % depth)
  let remaining := tape.drop indexCoins
  let bitIndex := min capacity (BitString.binaryValue (remaining.take indexCoins) % capacity)
  if reverseIndex < depth then
    if bitIndex < capacity then
      chooseLinkAtCoins evaluateKey n keyCoins (depth - reverseIndex - 1) reverseIndex bitIndex
        challengePk (remaining.drop indexCoins)
    else rejectLinkChoice
  else rejectLinkChoice

/-- The original fixed-coordinate choice is realized from one independent component seed per
generated key. No fixed key width, security, or correctness assumption is needed. -/
theorem eval_chooseLinkAt_eq_map_coins (E : Scheme)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (n keyCoins beforeCount afterCount bitIndex : ℕ) (challengePk : List Bool)
    (hkey : ProbComp.eval (E.keyGen n) =
      (BitString.uniformList keyCoins).map (evaluateKey n)) :
    ProbComp.eval (E.chooseLinkAt n beforeCount afterCount bitIndex challengePk) =
      (BitString.uniformList ((beforeCount + afterCount + 1) * keyCoins)).map
        (chooseLinkAtCoins evaluateKey n keyCoins beforeCount afterCount bitIndex challengePk) := by
  have hsize : (beforeCount + afterCount + 1) * keyCoins =
      beforeCount * keyCoins + (keyCoins + afterCount * keyCoins) := by ring
  let finish (before : List (List Bool × List Bool))
      (predecessor : List Bool × List Bool) (after : List (List Bool × List Bool)) :=
    if bitIndex < predecessor.2.length then
      ((predecessor.2.getD bitIndex false, false),
        activeLinkState before predecessor challengePk after bitIndex)
    else rejectLinkChoice
  rw [hsize, PMF.map]
  change _ = (BitString.uniformList (beforeCount * keyCoins +
    (keyCoins + afterCount * keyCoins))).bind (fun tape =>
      PMF.pure (finish
        ((BitString.listRows beforeCount keyCoins (tape.take (beforeCount * keyCoins))).map
          (evaluateKey n))
        (evaluateKey n ((tape.drop (beforeCount * keyCoins)).take keyCoins))
        ((BitString.listRows afterCount keyCoins
          ((tape.drop (beforeCount * keyCoins)).drop keyCoins)).map (evaluateKey n))))
  rw [BitString.uniformList_bind_split _ _ (fun front rest =>
    PMF.pure (finish ((BitString.listRows beforeCount keyCoins front).map (evaluateKey n))
      (evaluateKey n (rest.take keyCoins))
      ((BitString.listRows afterCount keyCoins (rest.drop keyCoins)).map (evaluateKey n))))]
  simp only [pmf_norm, chooseLinkAt,
    ProbComp.eval_replicate_of_uniformList beforeCount keyCoins _ _ hkey,
    ProbComp.eval_replicate_of_uniformList afterCount keyCoins _ _ hkey, hkey]
  congr 1 with front : 1
  rw [BitString.uniformList_bind_split _ _ (fun middle back =>
    PMF.pure (finish ((BitString.listRows beforeCount keyCoins front).map (evaluateKey n))
      (evaluateKey n middle) ((BitString.listRows afterCount keyCoins back).map (evaluateKey n))))]
  congr 1 with middle : 1
  congr 1 with back : 1
  dsimp only [finish]
  split <;> rfl

/-- The original modular choice is realized by two index blocks and one key block per level.
This includes zero ranges and preserves the bias of modular reduction for every modulus. -/
theorem eval_modLinkAdversary_choose_eq_map_coins (E : Scheme)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (coins depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n keyCoins : ℕ) (challengePk : List Bool)
    (hkey : ProbComp.eval (E.keyGen n) =
      (BitString.uniformList keyCoins).map (evaluateKey n)) :
    ProbComp.eval ((E.modLinkAdversary coins depth capacity test).choose n challengePk) =
      (BitString.uniformList (2 * coins n + depth n * keyCoins)).map
        (chooseModLinkCoins evaluateKey n (coins n) keyCoins (depth n) (capacity n)
          challengePk) := by
  rw [show 2 * coins n + depth n * keyCoins =
    coins n + (coins n + depth n * keyCoins) by omega, PMF.map]
  let index (bound : ℕ) (tape : List Bool) := min bound (BitString.binaryValue tape % bound)
  let finish (first second rest : List Bool) :=
    let i := index (depth n) first
    let j := index (capacity n) second
    if i < depth n then
      if j < capacity n then
        chooseLinkAtCoins evaluateKey n keyCoins (depth n - i - 1) i j challengePk rest
      else rejectLinkChoice
    else rejectLinkChoice
  change _ = (BitString.uniformList (coins n + (coins n + depth n * keyCoins))).bind
    (fun tape => PMF.pure (finish (tape.take (coins n))
      ((tape.drop (coins n)).take (coins n)) ((tape.drop (coins n)).drop (coins n))))
  rw [BitString.uniformList_bind_split _ _ (fun first rest =>
    PMF.pure (finish first (rest.take (coins n)) (rest.drop (coins n))))]
  simp only [pmf_norm, modLinkAdversary, sampleModIndex, ProbComp.sampleModNat,
    ProbComp.sampleBinaryNat, BitString.eval_sampleList]
  congr 1 with first : 1
  rw [BitString.uniformList_bind_split _ _ (fun second rest => PMF.pure (finish first second rest))]
  congr 1 with second : 1
  dsimp only [finish, index]
  split_ifs with hi hj
  · have hsize : depth n - index (depth n) first - 1 + index (depth n) first + 1 =
        depth n := by dsimp only [index]; omega
    simpa only [hsize, PMF.map, Function.comp_def, index] using
      E.eval_chooseLinkAt_eq_map_coins evaluateKey n keyCoins
        (depth n - index (depth n) first - 1) (index (depth n) first)
        (index (capacity n) second) challengePk hkey
  · simp [ProbComp.eval_pure, PMF.bind_const]
  · simp [ProbComp.eval_pure, PMF.bind_const]

/-- Replay is polynomial time in unary coordinates and key budget, the challenge word, and the
supplied tape whenever the component key evaluator is polynomial time. -/
@[fun_prop] theorem computableInPolyTime_chooseLinkAtCoins
    {evaluateKey : ℕ → List Bool → List Bool × List Bool}
    (hevaluate : ComputableInPolyTime (fun (n, tape) => evaluateKey n tape)
      (encPair encUnary encBits) (encPair encBits encBits))
    {α : Type} {input : α ↪ List Bool}
    {n keyCoins beforeCount afterCount bitIndex : α → ℕ}
    {challengePk tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hkeyCoins : ComputableInPolyTime keyCoins input encUnary)
    (hbefore : ComputableInPolyTime beforeCount input encUnary)
    (hafter : ComputableInPolyTime afterCount input encUnary)
    (hindex : ComputableInPolyTime bitIndex input encUnary)
    (hpk : ComputableInPolyTime challengePk input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => chooseLinkAtCoins evaluateKey (n a) (keyCoins a)
      (beforeCount a) (afterCount a) (bitIndex a) (challengePk a) (tape a))
      input (Encryption.encChoiceOut encBool) := by
  have hstep : ComputableInPolyTime (fun (a, row) => evaluateKey (n a) row)
      (encPair input encBits) (encPair encBits encBits) :=
    hevaluate.comp ((hn.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))
  have hfront := ComputableInPolyTime.mapWithInput (f := fun a row => evaluateKey (n a) row)
    (show ComputableInPolyTime (fun a => BitString.listRows (beforeCount a) (keyCoins a)
      ((tape a).take (beforeCount a * keyCoins a))) input (encList encBits) by fun_prop) hstep
  have hback := ComputableInPolyTime.mapWithInput (f := fun a row => evaluateKey (n a) row)
    (show ComputableInPolyTime (fun a => BitString.listRows (afterCount a) (keyCoins a)
      (((tape a).drop (beforeCount a * keyCoins a)).drop (keyCoins a)))
      input (encList encBits) by fun_prop) hstep
  have hpredecessor := hevaluate.comp (hn.prod
    (show ComputableInPolyTime (fun a =>
      ((tape a).drop (beforeCount a * keyCoins a)).take (keyCoins a))
      input encBits by fun_prop))
  have hstate : ComputableInPolyTime (fun a =>
      (true, (BitString.listRows (beforeCount a) (keyCoins a)
        ((tape a).take (beforeCount a * keyCoins a))).map (evaluateKey (n a)),
        evaluateKey (n a) (((tape a).drop (beforeCount a * keyCoins a)).take (keyCoins a)),
        challengePk a,
        (BitString.listRows (afterCount a) (keyCoins a)
          (((tape a).drop (beforeCount a * keyCoins a)).drop (keyCoins a))).map
          (evaluateKey (n a)), bitIndex a)) input encLinkState := by
    unfold encLinkState
    fun_prop
  unfold chooseLinkAtCoins
  apply ComputableInPolyTime.ite_decide
  · polytime
  · exact (show ComputableInPolyTime (fun a =>
      ((evaluateKey (n a) (((tape a).drop (beforeCount a * keyCoins a)).take
        (keyCoins a))).2.getD (bitIndex a) false, false))
      input (encPair encBool encBool) by fun_prop).prod
        (hstate.of_enc_eq fun _ => rfl)
  · exact .const _

/-- Modular replay uses binary division followed by a unary cap; its clock is polynomial in
all supplied unary parameters and words, including for a zero depth or capacity. -/
@[fun_prop] theorem computableInPolyTime_chooseModLinkCoins
    {evaluateKey : ℕ → List Bool → List Bool × List Bool}
    (hevaluate : ComputableInPolyTime (fun (n, tape) => evaluateKey n tape)
      (encPair encUnary encBits) (encPair encBits encBits))
    {α : Type} {input : α ↪ List Bool}
    {n indexCoins keyCoins depth capacity : α → ℕ}
    {challengePk tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hindexCoins : ComputableInPolyTime indexCoins input encUnary)
    (hkeyCoins : ComputableInPolyTime keyCoins input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hpk : ComputableInPolyTime challengePk input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => chooseModLinkCoins evaluateKey (n a) (indexCoins a)
      (keyCoins a) (depth a) (capacity a) (challengePk a) (tape a))
      input (Encryption.encChoiceOut encBool) := by
  have hfirstBits := ComputableInPolyTime.bitsBinaryValue.comp
    (htape.bitsTakeWithInput hindexCoins)
  have hsecondBits := ComputableInPolyTime.bitsBinaryValue.comp
    ((htape.bitsDropWithInput hindexCoins).bitsTakeWithInput hindexCoins)
  have hfirst := ComputableInPolyTime.binary_min_unary' hdepth
    (ComputableInPolyTime.binary_mod.comp (hfirstBits.prod
      (ComputableInPolyTime.unary_to_binary.comp hdepth)))
  have hsecond := ComputableInPolyTime.binary_min_unary' hcapacity
    (ComputableInPolyTime.binary_mod.comp (hsecondBits.prod
      (ComputableInPolyTime.unary_to_binary.comp hcapacity)))
  unfold chooseModLinkCoins
  apply ComputableInPolyTime.ite_decide
  · exact ComputableInPolyTime.unary_lt.comp (hfirst.prod hdepth)
  · apply ComputableInPolyTime.ite_decide
    · exact ComputableInPolyTime.unary_lt.comp (hsecond.prod hcapacity)
    · apply computableInPolyTime_chooseLinkAtCoins hevaluate <;> fun_prop
    · exact .const _
  · exact .const _

/-- A strict-PPT key generator supplies a concrete polynomial component budget. The resulting
native evaluator realizes the original modular choice from a tape of
`2 * coins n + depth n * (c * (n + 1) ^ d)` fair bits. This is a coin-realization theorem, not
an explicit multiplicative machine-time comparison with the adversary. -/
theorem exists_modLinkAdversary_choose_coin_evaluator {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    {coins depth capacity : ℕ → ℕ}
    (hcoins : ComputableInPolyTime coins encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    ∃ (c d : ℕ) (evaluateKey : ℕ → List Bool → List Bool × List Bool),
      ComputableInPolyTime (fun ((n, pk), tape) =>
        chooseModLinkCoins evaluateKey n (coins n) (c * (n + 1) ^ d) (depth n) (capacity n)
          pk tape)
        (encPair (encPair encUnary encBits) encBits) (Encryption.encChoiceOut encBool) ∧
      ∀ n pk,
        ProbComp.eval ((E.modLinkAdversary coins depth capacity test).choose n pk) =
          (BitString.uniformList (2 * coins n + depth n * (c * (n + 1) ^ d))).map
            (chooseModLinkCoins evaluateKey n (coins n) (c * (n + 1) ^ d)
              (depth n) (capacity n) pk) := by
  obtain ⟨c, d, evaluateKey, hevaluate, _, hlaw⟩ := hkeyGen.exists_total_seeded_evaluator
  refine ⟨c, d, evaluateKey, ?_, fun n pk => ?_⟩
  · apply computableInPolyTime_chooseModLinkCoins hevaluate <;> fun_prop
  · apply E.eval_modLinkAdversary_choose_eq_map_coins
    exact hlaw n _ (by simp)

end Cslib.Crypto.Homomorphic.Scheme
