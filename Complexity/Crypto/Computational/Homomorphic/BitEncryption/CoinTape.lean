/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.BitEncryption
public import Complexity.Languages.Probabilistic.Traverse.CoinTape
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Probability.PMF.Bind

/-!
# Saved tapes for bit encryption and a challenge splice

Each bit encryption receives a separate fixed-width seed. Splicing keeps the supplied challenge
ciphertext unchanged and consumes no encryption seed for it. These are execution laws for the
existing programs, with native deterministic replay certificates stated separately.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.encryptBitsCoins`: replay independent bit encryptions.
* `Cslib.Crypto.Homomorphic.Scheme.spliceEncryptedBitCoins`: replay the encrypted surroundings
  of a supplied challenge.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_encryptBits_eq_map_coins`: exact bit-encryption law.
* `Cslib.Crypto.Homomorphic.Scheme.eval_spliceEncryptedBit_eq_map_coins`: exact splice law.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- Give each plaintext bit its own component seed, retaining the original bit order. -/
@[expose] def encryptBitsCoins
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins : ℕ) (pk bits tape : List Bool) : List (List Bool) :=
  List.zipWith (fun bit seed => evaluate (n, pk, bit) seed) bits
    (BitString.listRows bits.length encCoins tape)

/-- Replay the zero prefix and original suffix from disjoint seed blocks. The supplied
challenge is inserted as-is between them. -/
@[expose] def spliceEncryptedBitCoins
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins : ℕ) (pk : List Bool) (before : ℕ) (after challenge tape : List Bool) :
    List (List Bool) :=
  let front := encryptBitsCoins evaluate n encCoins pk (List.replicate before false)
    (tape.take (before * encCoins))
  let back := encryptBitsCoins evaluate n encCoins pk after (tape.drop (before * encCoins))
  front ++ challenge :: back

/-- The component realization is needed only for the bits actually encrypted. -/
theorem eval_encryptBits_eq_map_coins (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins : ℕ) (pk bits : List Bool)
    (hencrypt : ∀ bit ∈ bits, ProbComp.eval (E.encrypt n pk bit) =
      (BitString.uniformList encCoins).map (evaluate (n, pk, bit))) :
    ProbComp.eval (E.encryptBits n pk bits) =
      (BitString.uniformList (bits.length * encCoins)).map
        (encryptBitsCoins evaluate n encCoins pk bits) :=
  ProbComp.eval_mapM_of_uniformList (E.encrypt n pk)
    (fun bit => evaluate (n, pk, bit)) encCoins bits hencrypt

/-- A longer seed can supply the same encryptions by discarding its unused suffix. -/
theorem eval_encryptBits_eq_map_coins_of_le (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins budget : ℕ) (pk bits : List Bool)
    (hencrypt : ∀ bit ∈ bits, ProbComp.eval (E.encrypt n pk bit) =
      (BitString.uniformList encCoins).map (evaluate (n, pk, bit)))
    (hbudget : bits.length * encCoins ≤ budget) :
    ProbComp.eval (E.encryptBits n pk bits) =
      (BitString.uniformList budget).map (fun tape =>
        encryptBitsCoins evaluate n encCoins pk bits (tape.take (bits.length * encCoins))) := by
  rw [E.eval_encryptBits_eq_map_coins evaluate n encCoins pk bits hencrypt,
    ← BitString.uniformList_take hbudget, PMF.map_comp]
  rfl

/-- The splice allocates seeds only for the zero prefix and suffix, not for the challenge. -/
theorem eval_spliceEncryptedBit_eq_map_coins (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins : ℕ) (pk : List Bool) (before : ℕ) (after challenge : List Bool)
    (hencrypt : ∀ bit, ProbComp.eval (E.encrypt n pk bit) =
      (BitString.uniformList encCoins).map (evaluate (n, pk, bit))) :
    ProbComp.eval (E.spliceEncryptedBit n pk before after challenge) =
      (BitString.uniformList ((before + after.length) * encCoins)).map
        (spliceEncryptedBitCoins evaluate n encCoins pk before after challenge) := by
  rw [Nat.add_mul, PMF.map]
  change _ = (BitString.uniformList (before * encCoins + after.length * encCoins)).bind
    (fun tape => PMF.pure
      (encryptBitsCoins evaluate n encCoins pk (List.replicate before false)
        (tape.take (before * encCoins)) ++ challenge ::
        encryptBitsCoins evaluate n encCoins pk after (tape.drop (before * encCoins))))
  rw [BitString.uniformList_bind_split _ _ (fun front back => PMF.pure
    (encryptBitsCoins evaluate n encCoins pk (List.replicate before false) front ++
      challenge :: encryptBitsCoins evaluate n encCoins pk after back))]
  simp only [spliceEncryptedBit, ProbComp.eval_bind, ProbComp.eval_pure,
    E.eval_encryptBits_eq_map_coins evaluate n encCoins pk (List.replicate before false)
      (fun bit _ => hencrypt bit),
    E.eval_encryptBits_eq_map_coins evaluate n encCoins pk after (fun bit _ => hencrypt bit),
    List.length_replicate, PMF.bind_map, Function.comp_def]

/-- Padding the complete splice tape preserves its exact law. -/
theorem eval_spliceEncryptedBit_eq_map_coins_of_le (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins budget : ℕ) (pk : List Bool) (before : ℕ) (after challenge : List Bool)
    (hencrypt : ∀ bit, ProbComp.eval (E.encrypt n pk bit) =
      (BitString.uniformList encCoins).map (evaluate (n, pk, bit)))
    (hbudget : (before + after.length) * encCoins ≤ budget) :
    ProbComp.eval (E.spliceEncryptedBit n pk before after challenge) =
      (BitString.uniformList budget).map (fun tape =>
        spliceEncryptedBitCoins evaluate n encCoins pk before after challenge
          (tape.take ((before + after.length) * encCoins))) := by
  rw [E.eval_spliceEncryptedBit_eq_map_coins evaluate n encCoins pk before after challenge hencrypt,
    ← BitString.uniformList_take hbudget, PMF.map_comp]
  rfl

/-- Native replay charges all supplied words and the unary component budget. -/
@[fun_prop] theorem computableInPolyTime_encryptBitsCoins
    {evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool}
    (hevaluate : ComputableInPolyTime (fun (input, tape) => evaluate input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n encCoins : α → ℕ}
    {pk bits tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => encryptBitsCoins evaluate (n a) (encCoins a)
      (pk a) (bits a) (tape a)) input (encList encBits) := by
  have hrows : ComputableInPolyTime (fun a =>
      BitString.listRows (bits a).length (encCoins a) (tape a)) input (encList encBits) := by
    fun_prop
  have hpairs := (ComputableInPolyTime.zip encBool encBits).comp
    ((ComputableInPolyTime.bitsToList.comp hbits).prod hrows)
  have hstep : ComputableInPolyTime
      (fun p : α × Bool × List Bool => evaluate (n p.1, pk p.1, p.2.1) p.2.2)
      (encPair input (encPair encBool encBits)) encBits :=
    hevaluate.comp (show ComputableInPolyTime
      (fun p : α × Bool × List Bool => ((n p.1, pk p.1, p.2.1), p.2.2))
      (encPair input (encPair encBool encBits))
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) by fun_prop)
  have hmap := ComputableInPolyTime.mapWithInput
    (f := fun a pair => evaluate (n a, pk a, pair.1) pair.2) hpairs hstep
  convert hmap using 1
  funext a
  exact List.map_uncurry_zip_eq_zipWith.symm

/-- Native splice replay retains the actual supplied challenge and charges its full length. -/
@[fun_prop] theorem computableInPolyTime_spliceEncryptedBitCoins
    {evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool}
    (hevaluate : ComputableInPolyTime (fun (input, tape) => evaluate input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n encCoins before : α → ℕ}
    {pk after challenge tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbefore : ComputableInPolyTime before input encUnary)
    (hafter : ComputableInPolyTime after input encBits)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => spliceEncryptedBitCoins evaluate (n a) (encCoins a)
      (pk a) (before a) (after a) (challenge a) (tape a)) input (encList encBits) := by
  have hfront : ComputableInPolyTime (fun a => encryptBitsCoins evaluate (n a) (encCoins a)
      (pk a) (List.replicate (before a) false) ((tape a).take (before a * encCoins a)))
      input (encList encBits) := by
    apply computableInPolyTime_encryptBitsCoins hevaluate <;> fun_prop
  have hback : ComputableInPolyTime (fun a => encryptBitsCoins evaluate (n a) (encCoins a)
      (pk a) (after a) ((tape a).drop (before a * encCoins a))) input (encList encBits) := by
    apply computableInPolyTime_encryptBitsCoins hevaluate <;> fun_prop
  unfold spliceEncryptedBitCoins
  fun_prop

end Cslib.Crypto.Homomorphic.Scheme
