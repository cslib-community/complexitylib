/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.BitEncryption
import CslibFrontier.Probability.PMF.Bind

/-!
# Supported bit-encryption sizes

These bounds charge each ciphertext that can occur under a participating public key. A splice
also charges the supplied challenge explicitly; no claim is made for arbitrary-size challenges.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.length_and_mem_of_mem_support_encryptBits`: one bounded
  ciphertext per input bit.
* `Cslib.Crypto.Homomorphic.Scheme.length_and_mem_of_mem_support_spliceEncryptedBit`: the
  inserted challenge and every sampled ciphertext obey the supplied bound.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

/-- The supported bit vector has exactly one ciphertext per plaintext, each obeying the
component bound. Only the actual input bits need satisfy that bound. -/
theorem length_and_mem_of_mem_support_encryptBits {E : Scheme} {n ctBound : ℕ}
    {pk bits : List Bool} {ciphertexts : List (List Bool)}
    (henc : ∀ bit ∈ bits, ∀ ct ∈ (ProbComp.eval (E.encrypt n pk bit)).support,
      ct.length ≤ ctBound)
    (hciphertexts : ciphertexts ∈ (ProbComp.eval (E.encryptBits n pk bits)).support) :
    ciphertexts.length = bits.length ∧ ∀ ct ∈ ciphertexts, ct.length ≤ ctBound := by
  have h := (E.mem_support_encryptBits_iff n pk bits ciphertexts).mp hciphertexts
  refine ⟨h.length_eq.symm, ?_⟩
  intro ct hct
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hct
  have hi : i.val < bits.length := by rw [h.length_eq]; exact i.isLt
  exact henc (bits.get ⟨i.val, hi⟩) (List.get_mem _ _) _ (h.get hi i.isLt)

/-- The splice contains the zero prefix, the supplied challenge, and the original suffix.
Every one of those ciphertexts is charged by `ctBound`. -/
theorem length_and_mem_of_mem_support_spliceEncryptedBit {E : Scheme} {n before ctBound : ℕ}
    {pk after challenge : List Bool} {ciphertexts : List (List Bool)}
    (henc : ∀ bit ct, ct ∈ (ProbComp.eval (E.encrypt n pk bit)).support → ct.length ≤ ctBound)
    (hchallenge : challenge.length ≤ ctBound)
    (hciphertexts : ciphertexts ∈
      (ProbComp.eval (E.spliceEncryptedBit n pk before after challenge)).support) :
    ciphertexts.length = before + 1 + after.length ∧
      ∀ ct ∈ ciphertexts, ct.length ≤ ctBound := by
  simp only [spliceEncryptedBit, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hciphertexts
  obtain ⟨front, hfront, back, hback, rfl⟩ := hciphertexts
  have hf := length_and_mem_of_mem_support_encryptBits (fun bit _ => henc bit) hfront
  have hb := length_and_mem_of_mem_support_encryptBits (fun bit _ => henc bit) hback
  refine ⟨by
    simp only [List.length_append, List.length_cons, hf.1, hb.1, List.length_replicate]
    omega, ?_⟩
  intro ct hct
  simp only [List.mem_append, List.mem_cons] at hct
  rcases hct with h | rfl | h
  · exact hf.2 _ h
  · exact hchallenge
  · exact hb.2 _ h

end Cslib.Crypto.Homomorphic.Scheme
