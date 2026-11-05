/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction
public import Complexity.Crypto.Computational.Homomorphic.BitEncryption.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Probability.PMF.Bind

/-!
# Saved tapes for encrypted key links

Each surrounding link reserves `capacity` independent encryption seeds. Its actual secret
width can be smaller, in which case unused bits are discarded. The boundary splice reserves
one fewer seed because its challenge ciphertext is supplied by the caller.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.encryptKeyLinksCoins`: replay real or zero encrypted links.
* `Cslib.Crypto.Homomorphic.Scheme.spliceEncryptedKeyLinkCoins`: replay the active boundary.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_encryptKeyLinks_eq_map_coins`: exact padded link law.
* `Cslib.Crypto.Homomorphic.Scheme.eval_spliceEncryptedKeyLink_eq_map_coins`: one fewer
  component seed at the challenge.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- Replay real (`zero = false`) or zero (`zero = true`) links. Each adjacent key pair gets
one `capacity * encCoins`-bit row, including repeated keys and repeated plaintexts. -/
@[expose] def encryptKeyLinksCoins
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins capacity : ℕ) (zero : Bool) (keys : List (List Bool × List Bool))
    (tape : List Bool) : List (List (List Bool)) :=
  List.zipWith (fun adjacent row =>
    let bits := if zero then List.replicate adjacent.1.2.length false else adjacent.1.2
    encryptBitsCoins evaluate n encCoins adjacent.2.1 bits (row.take (bits.length * encCoins)))
    (keys.zip keys.tail) (BitString.listRows (keys.zip keys.tail).length (capacity * encCoins) tape)

/-- Every surrounding link uses an independent padded row. Component laws are required only
at the supplied keys, and only their secret lengths need fit the capacity. -/
theorem eval_encryptKeyLinks_eq_map_coins (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins capacity : ℕ) (zero : Bool) (keys : List (List Bool × List Bool))
    (hwidth : ∀ key ∈ keys, key.2.length ≤ capacity)
    (hencrypt : ∀ key ∈ keys, ∀ bit, ProbComp.eval (E.encrypt n key.1 bit) =
      (BitString.uniformList encCoins).map (evaluate (n, key.1, bit))) :
    ProbComp.eval (if zero then E.encryptZeroKeyLinks n keys else E.encryptKeyLinks n keys) =
      (BitString.uniformList ((keys.zip keys.tail).length * (capacity * encCoins))).map
        (encryptKeyLinksCoins evaluate n encCoins capacity zero keys) := by
  have hprogram : (if zero then E.encryptZeroKeyLinks n keys else E.encryptKeyLinks n keys) =
      (keys.zip keys.tail).mapM (fun adjacent => E.encryptBits n adjacent.2.1
        (if zero then List.replicate adjacent.1.2.length false else adjacent.1.2)) := by
    cases zero <;> rfl
  rw [hprogram]
  apply ProbComp.eval_mapM_of_uniformList
  intro adjacent hadjacent
  obtain ⟨hprev, hnext⟩ := List.of_mem_zip hadjacent
  apply E.eval_encryptBits_eq_map_coins_of_le
  · intro bit _
    exact hencrypt adjacent.2 (List.mem_of_mem_tail hnext) bit
  · apply Nat.mul_le_mul_right encCoins
    cases zero <;> simpa using hwidth adjacent.1 hprev

/-- Replay the surrounding links and the active boundary splice. The middle row reserves one
fewer component seed; extra capacity within any row is ignored. -/
@[expose] def spliceEncryptedKeyLinkCoins
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins capacity : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (challenge tape : List Bool) : List (List (List Bool)) :=
  let frontSize := before.length * (capacity * encCoins)
  let middleSize := (capacity - 1) * encCoins
  let remaining := tape.drop frontSize
  let front := encryptKeyLinksCoins evaluate n encCoins capacity false (before ++ [predecessor])
    (tape.take frontSize)
  let suffix := predecessor.2.drop (cut + 1)
  let middle := spliceEncryptedBitCoins evaluate n encCoins next.1 cut suffix challenge
    ((remaining.take middleSize).take ((cut + suffix.length) * encCoins))
  let back := encryptKeyLinksCoins evaluate n encCoins capacity true (next :: after)
    (remaining.drop middleSize)
  front ++ middle :: back

/-- The actual splice fits one fewer encryption block than the complete padded chain. The
challenge ciphertext is retained verbatim, and the selected bit must be a real secret bit. -/
theorem eval_spliceEncryptedKeyLink_eq_map_coins (E : Scheme)
    (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (n encCoins capacity : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (challenge : List Bool)
    (hcut : cut < predecessor.2.length)
    (hwidth : ∀ key ∈ before ++ predecessor :: next :: after, key.2.length ≤ capacity)
    (hencrypt : ∀ key ∈ before ++ predecessor :: next :: after, ∀ bit,
      ProbComp.eval (E.encrypt n key.1 bit) =
        (BitString.uniformList encCoins).map (evaluate (n, key.1, bit))) :
    ProbComp.eval (E.spliceEncryptedKeyLink n before predecessor next after cut challenge) =
      (BitString.uniformList (((before.length + after.length + 1) * capacity - 1) * encCoins)).map
        (spliceEncryptedKeyLinkCoins evaluate n encCoins capacity before predecessor next after
          cut challenge) := by
  have hpred := hwidth predecessor (by simp)
  have hpos : 0 < capacity := by omega
  have hfrontLength : ((before ++ [predecessor]).zip (before ++ [predecessor]).tail).length =
      before.length := by simp
  have hbackLength : ((next :: after).zip (next :: after).tail).length = after.length := by simp
  have hfront := E.eval_encryptKeyLinks_eq_map_coins evaluate n encCoins capacity false
    (before ++ [predecessor])
    (fun key hkey => hwidth key (by
      simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hkey ⊢
      rcases hkey with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)))
    (fun key hkey => hencrypt key (by
      simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hkey ⊢
      rcases hkey with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)))
  have hback := E.eval_encryptKeyLinks_eq_map_coins evaluate n encCoins capacity true
    (next :: after)
    (fun key hkey => hwidth key (by
      simp only [List.mem_append, List.mem_cons] at hkey ⊢
      exact Or.inr (Or.inr hkey)))
    (fun key hkey => hencrypt key (by
      simp only [List.mem_append, List.mem_cons] at hkey ⊢
      exact Or.inr (Or.inr hkey)))
  simp only [Bool.false_eq_true, ↓reduceIte, hfrontLength] at hfront
  simp only [↓reduceIte, hbackLength] at hback
  have hmiddle := E.eval_spliceEncryptedBit_eq_map_coins_of_le evaluate n encCoins
    ((capacity - 1) * encCoins) next.1 cut (predecessor.2.drop (cut + 1)) challenge
    (hencrypt next (by simp)) (Nat.mul_le_mul_right encCoins (by
      simp only [List.length_drop]
      omega))
  have hsize : ((before.length + after.length + 1) * capacity - 1) * encCoins =
      before.length * (capacity * encCoins) +
        ((capacity - 1) * encCoins + after.length * (capacity * encCoins)) := by
    have heq : (before.length + after.length + 1) * capacity =
        before.length * capacity + after.length * capacity + capacity := by ring
    have hsub : (before.length + after.length + 1) * capacity - 1 =
        before.length * capacity + (capacity - 1) + after.length * capacity := by omega
    rw [hsub]
    ring
  let front := encryptKeyLinksCoins evaluate n encCoins capacity false (before ++ [predecessor])
  let middle := fun row : List Bool => spliceEncryptedBitCoins evaluate n encCoins next.1 cut
    (predecessor.2.drop (cut + 1)) challenge
    (row.take ((cut + (predecessor.2.drop (cut + 1)).length) * encCoins))
  let back := encryptKeyLinksCoins evaluate n encCoins capacity true (next :: after)
  rw [hsize, PMF.map]
  change _ = (BitString.uniformList (before.length * (capacity * encCoins) +
    ((capacity - 1) * encCoins + after.length * (capacity * encCoins)))).bind (fun tape =>
      PMF.pure (front (tape.take (before.length * (capacity * encCoins))) ++
        middle ((tape.drop (before.length * (capacity * encCoins))).take
          ((capacity - 1) * encCoins)) ::
        back ((tape.drop (before.length * (capacity * encCoins))).drop
          ((capacity - 1) * encCoins))))
  rw [BitString.uniformList_bind_split _ _ (fun first rest => PMF.pure
    (front first ++ middle (rest.take ((capacity - 1) * encCoins)) ::
      back (rest.drop ((capacity - 1) * encCoins))))]
  simp only [spliceEncryptedKeyLink, ProbComp.eval_bind, ProbComp.eval_pure,
    hfront, hmiddle, hback, PMF.bind_map, Function.comp_def]
  congr 1
  funext first
  rw [BitString.uniformList_bind_split _ _ (fun second third =>
    PMF.pure (front first ++ middle second :: back third))]

/-- Real and zero link replay is native polynomial time in the keys, tape, unary capacity,
and unary per-encryption seed budget. -/
@[fun_prop] theorem computableInPolyTime_encryptKeyLinksCoins
    {evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool}
    (hevaluate : ComputableInPolyTime (fun (input, tape) => evaluate input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n encCoins capacity : α → ℕ}
    (zero : Bool) {keys : α → List (List Bool × List Bool)} {tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList (encPair encBits encBits)))
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => encryptKeyLinksCoins evaluate (n a) (encCoins a)
      (capacity a) zero (keys a) (tape a)) input (encList (encList encBits)) := by
  have hadjacent : ComputableInPolyTime (fun a => (keys a).zip (keys a).tail)
      input (encList (encPair (encPair encBits encBits) (encPair encBits encBits))) :=
    (ComputableInPolyTime.zip (encPair encBits encBits) (encPair encBits encBits)).comp
      (hkeys.prod ((ListEncoding.tail (enc₁ := encPair encBits encBits)
        (enc := encList (encPair encBits encBits))).computableInPolyTime.comp hkeys))
  have hrows : ComputableInPolyTime (fun a =>
      BitString.listRows ((keys a).zip (keys a).tail).length (capacity a * encCoins a) (tape a))
      input (encList encBits) := by fun_prop
  have hpairs := (ComputableInPolyTime.zip
    (encPair (encPair encBits encBits) (encPair encBits encBits)) encBits).comp
      (hadjacent.prod hrows)
  have hstep : ComputableInPolyTime
      (fun p : α × ((List Bool × List Bool) × (List Bool × List Bool)) × List Bool =>
        let bits := if zero then List.replicate p.2.1.1.2.length false else p.2.1.1.2
        encryptBitsCoins evaluate (n p.1) (encCoins p.1) p.2.1.2.1 bits
          (p.2.2.take (bits.length * encCoins p.1)))
      (encPair input (encPair (encPair (encPair encBits encBits) (encPair encBits encBits))
        encBits)) (encList encBits) := by
    apply computableInPolyTime_encryptBitsCoins hevaluate <;> cases zero <;> fun_prop
  have hmap := ComputableInPolyTime.mapWithInput (f := fun a pair =>
    let bits := if zero then List.replicate pair.1.1.2.length false else pair.1.1.2
    encryptBitsCoins evaluate (n a) (encCoins a) pair.1.2.1 bits
      (pair.2.take (bits.length * encCoins a))) hpairs hstep
  convert hmap using 1
  funext a
  exact List.map_uncurry_zip_eq_zipWith.symm

/-- Native boundary replay charges every saved key and the full supplied challenge ciphertext.
The certificate holds on every input; the smaller seed law additionally needs a valid bit index. -/
@[fun_prop] theorem computableInPolyTime_spliceEncryptedKeyLinkCoins
    {evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool}
    (hevaluate : ComputableInPolyTime (fun (input, tape) => evaluate input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n encCoins capacity cut : α → ℕ}
    {before after : α → List (List Bool × List Bool)}
    {predecessor next : α → List Bool × List Bool} {challenge tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hbefore : ComputableInPolyTime before input (encList (encPair encBits encBits)))
    (hpredecessor : ComputableInPolyTime predecessor input (encPair encBits encBits))
    (hnext : ComputableInPolyTime next input (encPair encBits encBits))
    (hafter : ComputableInPolyTime after input (encList (encPair encBits encBits)))
    (hcut : ComputableInPolyTime cut input encUnary)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => spliceEncryptedKeyLinkCoins evaluate (n a) (encCoins a)
      (capacity a) (before a) (predecessor a) (next a) (after a) (cut a) (challenge a) (tape a))
      input (encList (encList encBits)) := by
  unfold spliceEncryptedKeyLinkCoins
  fun_prop

end Cslib.Crypto.Homomorphic.Scheme
