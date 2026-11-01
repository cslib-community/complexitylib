/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain
public import Complexity.Crypto.Computational.Homomorphic.BitEncryption
import Complexity.Probability.PMF.Bind
import Complexity.Foundations.Data.List.Append
import Complexity.Probability.PMF

/-!
# Hybrids for an acyclic encrypted-key chain

The link hybrid retains real secret-key encryptions before a boundary and encrypts zero words
after it. Moving the boundary towards the initial key erases links from the end of the chain.
This order is essential: when a reduction embeds a challenge public key, the outgoing link
that would contain its unknown secret has already been replaced by an encryption of zeros.

These are actual sampling programs and exact distributional identities. They do not assume or
establish computational indistinguishability on their own.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.encryptZeroKeyLinks`: encrypt equal-length zero words.
* `Cslib.Crypto.Homomorphic.Scheme.encryptKeyLinksHybrid`: retain a prefix of real links.
* `Cslib.Crypto.Homomorphic.Scheme.publicKeyChainHybrid`: sample the complete public artifact.
* `Cslib.Crypto.Homomorphic.Scheme.publicKeyLinkHybrid`: refine one boundary link bit by bit.
* `Cslib.Crypto.Homomorphic.Scheme.spliceEncryptedKeyLink`: insert the base challenge ciphertext.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_generateKeys_splice`: sampling the challenge key first
  preserves the complete joint key distribution.
* `Cslib.Crypto.Homomorphic.Scheme.eval_spliceEncryptedKeyLink_original`,
  `.eval_spliceEncryptedKeyLink_zero`: exact laws for the two challenge worlds.
* `Cslib.Crypto.Homomorphic.Scheme.eval_publicKeyLinkHybrid_zero`,
  `.eval_publicKeyLinkHybrid_length`: bit-hybrid endpoints are the adjacent link hybrids.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

variable (E : Scheme)

/-- Draw the target key first, then independently draw the keys before and after its
predecessor. Splicing them restores the complete original key-generation distribution. -/
theorem eval_generateKeys_splice (n beforeCount afterCount : ℕ) :
    ProbComp.eval (do
      let next ← E.keyGen n
      let before ← OracleComp.replicate beforeCount (E.keyGen n)
      let predecessor ← E.keyGen n
      let after ← OracleComp.replicate afterCount (E.keyGen n)
      pure (before ++ predecessor :: next :: after)) =
        ProbComp.eval (E.generateKeys n (beforeCount + afterCount + 1)) := by
  calc
    _ = ProbComp.eval (do
        let next ← E.keyGen n
        let front ← OracleComp.replicate (beforeCount + 1) (E.keyGen n)
        let after ← OracleComp.replicate afterCount (E.keyGen n)
        pure (front ++ next :: after)) := by
      simp [OracleComp.replicate_snoc, bind_assoc, List.append_assoc]
    _ = _ := by
      have hcount : beforeCount + 1 + (afterCount + 1) = (beforeCount + afterCount + 1) + 1 := by
        omega
      simpa only [generateKeys, hcount] using
        ProbComp.eval_replicate_splice (E.keyGen n) (beforeCount + 1) afterCount

/-- Replace every secret-key plaintext by a zero word of the same length. The public keys,
number of links and number of bit encryptions in each link are retained. -/
def encryptZeroKeyLinks (n : ℕ) (keys : List (List Bool × List Bool)) :
    ProbComp (List (List (List Bool))) :=
  (keys.zip keys.tail).mapM (fun adjacent =>
    let prev := adjacent.1
    let next := adjacent.2
    E.encryptBits n next.1 (List.replicate prev.2.length false))

/-- Encrypt real secrets in the first `cut` links, and zero words in the remaining links.
The two key segments overlap at their boundary key; each link is sampled exactly once. -/
def encryptKeyLinksHybrid (n cut : ℕ) (keys : List (List Bool × List Bool)) :
    ProbComp (List (List (List Bool))) := do
  let front ← E.encryptKeyLinks n (keys.take (cut + 1))
  let back ← E.encryptZeroKeyLinks n (keys.drop cut)
  pure (front ++ back)

/-- Splitting a real-link traversal keeps its shared boundary key in both segments. -/
theorem encryptKeyLinks_append_cons (n : ℕ) (before : List (List Bool × List Bool))
    (middle : List Bool × List Bool) (after : List (List Bool × List Bool)) :
    E.encryptKeyLinks n (before ++ middle :: after) = (do
      let front ← E.encryptKeyLinks n (before ++ [middle])
      let back ← E.encryptKeyLinks n (middle :: after)
      pure (front ++ back)) := by
  simp only [encryptKeyLinks]
  rw [List.zip_tail_append_cons, List.mapM_append, List.tail_cons]

/-- Splitting a zero-link traversal also keeps the shared boundary key. -/
theorem encryptZeroKeyLinks_append_cons (n : ℕ) (before : List (List Bool × List Bool))
    (middle : List Bool × List Bool) (after : List (List Bool × List Bool)) :
    E.encryptZeroKeyLinks n (before ++ middle :: after) = (do
      let front ← E.encryptZeroKeyLinks n (before ++ [middle])
      let back ← E.encryptZeroKeyLinks n (middle :: after)
      pure (front ++ back)) := by
  simp only [encryptZeroKeyLinks]
  rw [List.zip_tail_append_cons, List.mapM_append, List.tail_cons]

@[simp] theorem encryptZeroKeyLinks_nil (n : ℕ) :
    E.encryptZeroKeyLinks n [] = pure [] := rfl

@[simp] theorem encryptZeroKeyLinks_singleton (n : ℕ) (key : List Bool × List Bool) :
    E.encryptZeroKeyLinks n [key] = pure [] := rfl

/-- Expose the first zero link, retaining ordinary independent bit encryption. -/
theorem encryptZeroKeyLinks_cons_cons (n : ℕ) (first second : List Bool × List Bool)
    (rest : List (List Bool × List Bool)) :
    E.encryptZeroKeyLinks n (first :: second :: rest) = (do
      let link ← E.encryptBits n second.1 (List.replicate first.2.length false)
      List.cons link <$> E.encryptZeroKeyLinks n (second :: rest)) := by
  simp [encryptZeroKeyLinks, List.mapM_cons, bind_pure_comp]

/-- The first zero link uses only the length of the first secret. Its public key is unused. -/
theorem encryptZeroKeyLinks_cons_congr (n : ℕ) (first replacement : List Bool × List Bool)
    (rest : List (List Bool × List Bool)) (hlength : first.2.length = replacement.2.length) :
    E.encryptZeroKeyLinks n (first :: rest) =
      E.encryptZeroKeyLinks n (replacement :: rest) := by
  cases rest with
  | nil => simp
  | cons second rest => rw [encryptZeroKeyLinks_cons_cons, encryptZeroKeyLinks_cons_cons, hlength]

/-- A boundary at zero erases every secret-key plaintext. -/
@[simp] theorem encryptKeyLinksHybrid_zero (n : ℕ) (keys : List (List Bool × List Bool)) :
    E.encryptKeyLinksHybrid n 0 keys = E.encryptZeroKeyLinks n keys := by
  cases keys <;> simp [encryptKeyLinksHybrid, encryptKeyLinks]

/-- A boundary after the last link also retains every original link. -/
theorem encryptKeyLinksHybrid_of_length_le_succ (n cut : ℕ)
    (keys : List (List Bool × List Bool)) (hcut : keys.length ≤ cut + 1) :
    E.encryptKeyLinksHybrid n cut keys = E.encryptKeyLinks n keys := by
  have htail : (keys.drop cut).length ≤ 1 := by
    rw [List.length_drop]
    omega
  have hzero : E.encryptZeroKeyLinks n (keys.drop cut) = pure [] := by
    generalize keys.drop cut = rest at *
    cases rest with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest => simp only [List.length_cons] at htail; omega
  simp [encryptKeyLinksHybrid, List.take_of_length_le hcut, hzero]

/-- Sample the independent keys and a link hybrid, returning only public data. -/
def publicKeyChainHybrid (n depth cut : ℕ) :
    ProbComp (List (List Bool) × List (List (List Bool))) := do
  let keys ← E.generateKeys n depth
  let links ← E.encryptKeyLinksHybrid n cut keys
  pure (keys.map Prod.fst, links)

/-- The final boundary is the exact public marginal of the original key-chain sampler. -/
theorem eval_publicKeyChainHybrid_depth (n depth : ℕ) :
    ProbComp.eval (E.publicKeyChainHybrid n depth depth) =
      (ProbComp.eval (E.generateKeyChain n depth)).map
        (fun chain => (chain.1.map Prod.fst, chain.2)) := by
  simp only [publicKeyChainHybrid, generateKeyChain, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.map_bind, PMF.pure_map]
  apply Probability.PMF.bind_congr_on_support
  intro keys hkeys
  have hlength := ((E.mem_support_generateKeys_iff n depth keys).mp hkeys).1
  rw [E.encryptKeyLinksHybrid_of_length_le_succ n depth keys (by omega)]

/-- The initial boundary samples the same public keys with zero plaintexts in every link. -/
theorem publicKeyChainHybrid_zero (n depth : ℕ) :
    E.publicKeyChainHybrid n depth 0 = (do
      let keys ← E.generateKeys n depth
      let links ← E.encryptZeroKeyLinks n keys
      pure (keys.map Prod.fst, links)) := by
  simp only [publicKeyChainHybrid, encryptKeyLinksHybrid_zero]

/-- Refine the boundary link bit by bit, leaving earlier links real and later links zeroed.
`predecessor` is the key whose secret is encrypted under `next.1`. -/
def encryptKeyLinkHybrid (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) : ProbComp (List (List (List Bool))) := do
  let front ← E.encryptKeyLinks n (before ++ [predecessor])
  let middle ← E.encryptBitsHybrid n next.1 predecessor.2 cut
  let back ← E.encryptZeroKeyLinks n (next :: after)
  pure (front ++ middle :: back)

/-- Before erasing any bit, the boundary link is still real. -/
theorem encryptKeyLinkHybrid_zero (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool)) :
    E.encryptKeyLinkHybrid n before predecessor next after 0 =
      E.encryptKeyLinksHybrid n (before.length + 1) (before ++ predecessor :: next :: after) := by
  simp only [encryptKeyLinksHybrid, Nat.add_assoc, List.take_length_add_append,
    List.take_succ_cons, List.take_zero, List.drop_length_add_append, List.drop_succ_cons,
    List.drop_zero]
  rw [E.encryptKeyLinks_append_cons n before predecessor [next]]
  have happend (front : List (List (List Bool))) (middle : List (List Bool)) :
      (fun back => front ++ middle :: back) = HAppend.hAppend (front ++ [middle]) := by
    funext back
    simp
  simp [encryptKeyLinkHybrid, encryptKeyLinks, List.mapM_cons, bind_assoc,
    happend]

/-- After erasing every bit, the boundary link is part of the zeroed suffix. -/
theorem encryptKeyLinkHybrid_length (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool)) :
    E.encryptKeyLinkHybrid n before predecessor next after predecessor.2.length =
      E.encryptKeyLinksHybrid n before.length (before ++ predecessor :: next :: after) := by
  simp only [encryptKeyLinksHybrid, List.take_length_add_append, List.take_succ_cons,
    List.take_zero, List.drop_append_length, encryptZeroKeyLinks_cons_cons]
  simp [encryptKeyLinkHybrid, encryptBitsHybrid_length]

/-- Once its outgoing link is zeroed, replacing the target key's secret by an equal-length
word does not change the intermediate sampler. Its public key is retained. -/
theorem encryptKeyLinkHybrid_secret_congr (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor : List Bool × List Bool) (pk secret replacement : List Bool)
    (after : List (List Bool × List Bool)) (cut : ℕ)
    (hlength : secret.length = replacement.length) :
    E.encryptKeyLinkHybrid n before predecessor (pk, secret) after cut =
      E.encryptKeyLinkHybrid n before predecessor (pk, replacement) after cut := by
  simp only [encryptKeyLinkHybrid]
  rw [E.encryptZeroKeyLinks_cons_congr n (pk, secret) (pk, replacement) after hlength]

/-- Sample the surrounding encrypted links and insert one ciphertext into the boundary link. -/
def spliceEncryptedKeyLink (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (challenge : List Bool) : ProbComp (List (List (List Bool))) := do
  let front ← E.encryptKeyLinks n (before ++ [predecessor])
  let middle ← E.spliceEncryptedBit n next.1 cut (predecessor.2.drop (cut + 1)) challenge
  let back ← E.encryptZeroKeyLinks n (next :: after)
  pure (front ++ middle :: back)

/-- The bit challenge is sampled independently of every surrounding link. An original-bit
challenge recovers the full earlier hybrid distribution. -/
theorem eval_spliceEncryptedKeyLink_original (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (hcut : cut < predecessor.2.length) :
    ProbComp.eval (do
      let challenge ← E.encrypt n next.1 (predecessor.2.getD cut false)
      E.spliceEncryptedKeyLink n before predecessor next after cut challenge) =
        ProbComp.eval (E.encryptKeyLinkHybrid n before predecessor next after cut) := by
  have hmiddle := E.eval_spliceEncryptedBit_original n next.1 predecessor.2 cut hcut
  simp only [ProbComp.eval_bind] at hmiddle
  simp only [spliceEncryptedKeyLink, encryptKeyLinkHybrid, ProbComp.eval_bind,
    ProbComp.eval_pure]
  rw [PMF.bind_comm]
  congr 1
  funext front
  rw [← PMF.bind_bind, hmiddle]

/-- A zero-bit challenge recovers the full next hybrid distribution, retaining all other
encrypted links and their randomness. -/
theorem eval_spliceEncryptedKeyLink_zero (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (hcut : cut < predecessor.2.length) :
    ProbComp.eval (do
      let challenge ← E.encrypt n next.1 false
      E.spliceEncryptedKeyLink n before predecessor next after cut challenge) =
        ProbComp.eval (E.encryptKeyLinkHybrid n before predecessor next after (cut + 1)) := by
  have hmiddle := E.eval_spliceEncryptedBit_zero n next.1 predecessor.2 cut hcut
  simp only [ProbComp.eval_bind] at hmiddle
  simp only [spliceEncryptedKeyLink, encryptKeyLinkHybrid, ProbComp.eval_bind,
    ProbComp.eval_pure]
  rw [PMF.bind_comm]
  congr 1
  funext front
  rw [← PMF.bind_bind, hmiddle]

/-- Sample an intermediate bit hybrid with the target key drawn first. Only public keys and
encrypted links are returned. This sampling order matches the single-challenge reduction. -/
def publicKeyLinkHybrid (n beforeCount afterCount cut : ℕ) :
    ProbComp (List (List Bool) × List (List (List Bool))) := do
  let next ← E.keyGen n
  let before ← OracleComp.replicate beforeCount (E.keyGen n)
  let predecessor ← E.keyGen n
  let after ← OracleComp.replicate afterCount (E.keyGen n)
  let links ← E.encryptKeyLinkHybrid n before predecessor next after cut
  pure ((before ++ predecessor :: next :: after).map Prod.fst, links)

/-- The initial bit boundary is the corresponding real-link boundary in the original key
sampling order. This is an equality of complete public distributions. -/
theorem eval_publicKeyLinkHybrid_zero (n beforeCount afterCount : ℕ) :
    ProbComp.eval (E.publicKeyLinkHybrid n beforeCount afterCount 0) =
      ProbComp.eval (E.publicKeyChainHybrid n (beforeCount + afterCount + 1)
        (beforeCount + 1)) := by
  simp only [publicKeyLinkHybrid, publicKeyChainHybrid, ProbComp.eval_bind]
  rw [← E.eval_generateKeys_splice n beforeCount afterCount]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext next
  apply Probability.PMF.bind_congr_on_support
  intro before hbefore
  have hlength := ((ProbComp.mem_support_replicate_iff beforeCount (E.keyGen n) before).mp
    hbefore).1
  congr 1
  funext predecessor
  congr 1
  funext after
  rw [← hlength, ← E.encryptKeyLinkHybrid_zero]

/-- With a fixed supported secret length, the final bit boundary is the preceding link
boundary. No efficiency or ciphertext-width assumption is needed for this exact law. -/
theorem eval_publicKeyLinkHybrid_length (n beforeCount afterCount width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (E.publicKeyLinkHybrid n beforeCount afterCount width) =
      ProbComp.eval (E.publicKeyChainHybrid n (beforeCount + afterCount + 1) beforeCount) := by
  simp only [publicKeyLinkHybrid, publicKeyChainHybrid, ProbComp.eval_bind]
  rw [← E.eval_generateKeys_splice n beforeCount afterCount]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext next
  apply Probability.PMF.bind_congr_on_support
  intro before hbefore
  have hlength := ((ProbComp.mem_support_replicate_iff beforeCount (E.keyGen n) before).mp
    hbefore).1
  apply Probability.PMF.bind_congr_on_support
  intro predecessor hpredecessor
  congr 1
  funext after
  rw [← hlength, ← hwidth predecessor hpredecessor, ← E.encryptKeyLinkHybrid_length]

end Cslib.Crypto.Homomorphic.Scheme
