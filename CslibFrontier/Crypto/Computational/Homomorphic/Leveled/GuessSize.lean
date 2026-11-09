/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.Size
public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Size

/-!
# Public-artifact sizes for the actual link splice

The bound applies to the public artifact that the guessing stage actually passes to its test.
The external challenge has an explicit size premise; a supported challenge encryption supplies
that premise in the native strict-PPT application.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.length_encPublicKey_support_splice_le`: the actual splice
  fits the existing serialized-public-key bound.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

/-- A valid splice exposes the original number of public keys and links. The supplied challenge
and every supported component ciphertext must obey the same ciphertext bound. -/
theorem length_encPublicKey_support_splice_le {E : Scheme}
    {n capacity pkBound ctBound cut : ℕ} {before after : List (List Bool × List Bool)}
    {predecessor next : List Bool × List Bool} {challenge : List Bool}
    {links : List (List (List Bool))}
    (hcut : cut < predecessor.2.length)
    (hkeys : ∀ key ∈ before ++ predecessor :: next :: after,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity)
    (hencrypt : ∀ key ∈ before ++ predecessor :: next :: after, ∀ bit ct,
      ct ∈ (ProbComp.eval (E.encrypt n key.1 bit)).support → ct.length ≤ ctBound)
    (hchallenge : challenge.length ≤ ctBound)
    (hlinks : links ∈ (ProbComp.eval
      (E.spliceEncryptedKeyLink n before predecessor next after cut challenge)).support) :
    (encPublicKey ((before ++ predecessor :: next :: after).map Prod.fst, links)).length ≤
      publicKeyLengthBound (before.length + after.length + 1) capacity pkBound ctBound := by
  have htable := Scheme.length_and_mem_of_mem_support_spliceEncryptedKeyLink hcut
    (fun key hkey => ⟨(hkeys key hkey).2, hencrypt key hkey⟩) hchallenge hlinks
  apply length_encPublicKey_le
  · simp only [List.length_map, List.length_append, List.length_cons]
    omega
  · intro pk hpk
    obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hpk
    exact (hkeys key hkey).1
  · exact htable.1.le
  · exact htable.2

end Cslib.Crypto.Homomorphic.Leveled
