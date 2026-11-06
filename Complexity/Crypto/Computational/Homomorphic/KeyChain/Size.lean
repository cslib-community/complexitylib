/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid
public import Complexity.Crypto.Computational.Homomorphic.BitEncryption.Size
import Complexity.Probability.PMF.Bind

/-!
# Supported encrypted-link sizes

Real links, zero links and an active splice retain their exact table dimensions. Bounds on the
participating secrets, supported ciphertexts and supplied challenge bound every table entry.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.length_and_mem_of_mem_support_encryptKeyLinks`: real links.
* `Cslib.Crypto.Homomorphic.Scheme.length_and_mem_of_mem_support_encryptZeroKeyLinks`: zero links.
* `Cslib.Crypto.Homomorphic.Scheme.length_and_mem_of_mem_support_spliceEncryptedKeyLink`: the
  actual splice, with an explicit challenge-length premise.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

/-- A real link table has one entry per adjacent key pair, bounded by the preceding secret
width and the component ciphertext bound at the following public key. -/
theorem length_and_mem_of_mem_support_encryptKeyLinks {E : Scheme} {n width ctBound : ℕ}
    {keys : List (List Bool × List Bool)} {links : List (List (List Bool))}
    (hkeys : ∀ k ∈ keys, k.2.length ≤ width ∧
      ∀ b ct, ct ∈ (ProbComp.eval (E.encrypt n k.1 b)).support → ct.length ≤ ctBound)
    (hlinks : links ∈ (ProbComp.eval (E.encryptKeyLinks n keys)).support) :
    links.length = keys.length - 1 ∧
      ∀ link ∈ links, link.length ≤ width ∧ ∀ ct ∈ link, ct.length ≤ ctBound := by
  simp only [encryptKeyLinks, ProbComp.mem_support_mapM_iff] at hlinks
  have hlen := hlinks.length_eq.symm
  refine ⟨by simpa using hlen, ?_⟩
  intro link hlink
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hlink
  have hi : i.val < (keys.zip keys.tail).length := by rw [hlinks.length_eq]; exact i.isLt
  let adjacent := (keys.zip keys.tail).get ⟨i.val, hi⟩
  have hadjacent : adjacent ∈ keys.zip keys.tail := List.get_mem _ _
  obtain ⟨hprev, hnext⟩ := List.of_mem_zip hadjacent
  have hinfo := length_and_mem_of_mem_support_encryptBits
    (fun bit _ => (hkeys adjacent.2 (List.mem_of_mem_tail hnext)).2 bit) (hlinks.get hi i.isLt)
  exact ⟨hinfo.1.trans_le (hkeys adjacent.1 hprev).1, hinfo.2⟩

/-- Zeroing each secret preserves its width and the same component ciphertext bound. -/
theorem length_and_mem_of_mem_support_encryptZeroKeyLinks {E : Scheme}
    {n width ctBound : ℕ}
    {keys : List (List Bool × List Bool)} {links : List (List (List Bool))}
    (hkeys : ∀ k ∈ keys, k.2.length ≤ width ∧
      ∀ b ct, ct ∈ (ProbComp.eval (E.encrypt n k.1 b)).support → ct.length ≤ ctBound)
    (hlinks : links ∈ (ProbComp.eval (E.encryptZeroKeyLinks n keys)).support) :
    links.length = keys.length - 1 ∧
      ∀ link ∈ links, link.length ≤ width ∧ ∀ ct ∈ link, ct.length ≤ ctBound := by
  simp only [encryptZeroKeyLinks, ProbComp.mem_support_mapM_iff] at hlinks
  have hlen := hlinks.length_eq.symm
  refine ⟨by simpa using hlen, ?_⟩
  intro link hlink
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hlink
  have hi : i.val < (keys.zip keys.tail).length := by rw [hlinks.length_eq]; exact i.isLt
  let adjacent := (keys.zip keys.tail).get ⟨i.val, hi⟩
  have hadjacent : adjacent ∈ keys.zip keys.tail := List.get_mem _ _
  obtain ⟨hprev, hnext⟩ := List.of_mem_zip hadjacent
  have hinfo := length_and_mem_of_mem_support_encryptBits
    (fun bit _ => (hkeys adjacent.2 (List.mem_of_mem_tail hnext)).2 bit) (hlinks.get hi i.isLt)
  have hlinkLength : (links.get i).length = adjacent.1.2.length := by
    simpa only [List.length_replicate] using hinfo.1
  exact ⟨hlinkLength.trans_le (hkeys adjacent.1 hprev).1, hinfo.2⟩

/-- Every actual splice has the original number of links and stays within the supplied
secret/ciphertext bounds. A valid selected bit is needed to retain the boundary link's width. -/
theorem length_and_mem_of_mem_support_spliceEncryptedKeyLink {E : Scheme}
    {n width ctBound cut : ℕ} {before after : List (List Bool × List Bool)}
    {predecessor next : List Bool × List Bool} {challenge : List Bool}
    {links : List (List (List Bool))}
    (hcut : cut < predecessor.2.length)
    (hkeys : ∀ k ∈ before ++ predecessor :: next :: after, k.2.length ≤ width ∧
      ∀ b ct, ct ∈ (ProbComp.eval (E.encrypt n k.1 b)).support → ct.length ≤ ctBound)
    (hchallenge : challenge.length ≤ ctBound)
    (hlinks : links ∈ (ProbComp.eval
      (E.spliceEncryptedKeyLink n before predecessor next after cut challenge)).support) :
    links.length = before.length + after.length + 1 ∧
      ∀ link ∈ links, link.length ≤ width ∧ ∀ ct ∈ link, ct.length ≤ ctBound := by
  simp only [spliceEncryptedKeyLink, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hlinks
  obtain ⟨front, hfront, middle, hmiddle, back, hback, rfl⟩ := hlinks
  have hf := length_and_mem_of_mem_support_encryptKeyLinks
    (fun k hk => hkeys k (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))) hfront
  have hm := length_and_mem_of_mem_support_spliceEncryptedBit
    (hkeys next (by simp)).2 hchallenge hmiddle
  have hb := length_and_mem_of_mem_support_encryptZeroKeyLinks
    (fun k hk => hkeys k (by
      simp only [List.mem_append, List.mem_cons] at hk ⊢
      exact Or.inr (Or.inr hk))) hback
  have hmiddleWidth : middle.length ≤ width := by
    have hp := (hkeys predecessor (by simp)).1
    rw [hm.1, List.length_drop]
    omega
  have hfLength : front.length = before.length := by simpa using hf.1
  have hbLength : back.length = after.length := by simpa using hb.1
  refine ⟨by
    simp only [List.length_append, List.length_cons, hfLength, hbLength]
    omega, ?_⟩
  intro link hlink
  simp only [List.mem_append, List.mem_cons] at hlink
  rcases hlink with h | rfl | h
  · exact hf.2 _ h
  · exact ⟨hmiddleWidth, hm.2⟩
  · exact hb.2 _ h

end Cslib.Crypto.Homomorphic.Scheme
