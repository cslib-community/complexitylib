/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Crypto.Computational.WordSignature
import CslibFrontier.Crypto.Computational.MerkleDamgard
import CslibFrontier.Crypto.Computational.Rompel
import CslibFrontier.Crypto.Negligible
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.Guessing.Leakage
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Probability.PMF.Finiteness

/-!
# One-way functions from collision-resistant hash families

A collision-resistant hash family yields a one-way function ([KatzLindell2020], Exercise 8.4).
The function `CollisionResistantToOneWay.keyDigest H` reads its input as a key `k` (the first
third) followed by a message `x` (the rest), and outputs `k ++ H k x`. Publishing the key turns the
keyed family into the single function on bit strings that `OneWay` asks for.

On inputs of length `3 n + r` with `r < 3`, the key has `n` bits and the message `2 n + r` bits.
An inverter that finds a preimage of `k ++ H k x` returns a message `x'` with `H k x' = H k x`.
Either `x' ≠ x`, which is a collision under the uniform key `k`, or `x' = x`. The inverter sees `x`
only through its `n`-bit digest, so it returns `x` itself with probability at most
`2 ^ n / 2 ^ (2 n + r) ≤ (1 / 2) ^ n`. The bound is
`CollisionResistantToOneWay.succProbability_inversionGame_le`; one collision finder for each
residue `r` covers every input length.

With Rompel's theorem (`OneWay.exists_wordEUFCMA`), collision-resistant hashing therefore gives
stateless signatures that are existentially unforgeable under adaptive chosen-message attacks
([KatzLindell2020], Theorem 14.16; this also covers the one-time schemes of Lemma 14.13).
Merkle–Damgård domain extension gives the same conclusions for `2 n → n` compression families,
the setting of Exercise 8.4. No converse is claimed: one-way functions are not known to give
collision-resistant hash families.

## Main definitions

* `Cslib.Crypto.CollisionResistantToOneWay.keyDigest`: output the key and the message's digest.
* `Cslib.Crypto.CollisionResistantToOneWay.finder`: the collision finder built from an inverter.

## Main results

* `Cslib.Crypto.CollisionResistantToOneWay.succProbability_inversionGame_le`: inverting at length
  `3 n + r` succeeds at most as often as finding a collision at parameter `n`, plus `(1 / 2) ^ n`.
* `Cslib.Crypto.HashFamily.oneWay_keyDigest`, `Cslib.Crypto.HashFamily.exists_oneWay`:
  collision-resistant hash families give one-way functions.
* `Cslib.Crypto.HashFamily.exists_eufCMA`, `Cslib.Crypto.HashFamily.exists_wordEUFCMA`: they also
  give EUF-CMA secure stateless signatures.
* `Cslib.Crypto.CompressionFamily.exists_oneWay`,
  `Cslib.Crypto.CompressionFamily.exists_wordEUFCMA`: the same for collision-resistant
  compression families.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Exercise 8.4, Lemma 14.13 and Theorem 14.16.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace CollisionResistantToOneWay

/-- Read a word as a key (its first third) followed by a message, and output the key followed by
the message's digest under that key. -/
def keyDigest (H : List Bool → List Bool → List Bool) (word : List Bool) : List Bool :=
  let split := word.length / 3
  word.take split ++ H (word.take split) (word.drop split)

/-- The construction makes one call to the hash family and otherwise only slices words. -/
@[fun_prop]
theorem polyTime_keyDigest {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (keyDigest H) encBits encBits := by
  unfold keyDigest
  polytime

/-- The collision finder built from an inverter. On key `k` at parameter `n`, it samples a message
`x` of length `2 n + r`, asks the inverter for a preimage of `k ++ H k x` at parameter `3 n + r`,
and pairs `x` with the message part of the answer. -/
noncomputable def finder (H : List Bool → List Bool → List Bool) (adversary : Inverter) (r : ℕ) :
    CollisionFinder := fun n key => do
  let message ← BitString.sampleList (2 * n + r)
  let candidate ← adversary (3 * n + r) (key ++ H key message)
  return (message, candidate.drop (candidate.length / 3))

/-- Sampling, parameter rescaling, one hash call and one captured inverter call are uniformly
strict PPT. -/
@[program_certificate]
theorem isPPT_finder {H : List Bool → List Bool → List Bool} {adversary : Inverter}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hadversary : IsPPT encBits adversary) (r : ℕ) :
    IsPPT (encPair encBits encBits) (finder H adversary r) := by
  have hHt := hH.tidy
  unfold finder
  ppt

/-- On a key followed by a message of length `2 |k| + r` with `r < 3`, the construction outputs
the key followed by the message's digest. -/
theorem keyDigest_append (H : List Bool → List Bool → List Bool) {key message : List Bool}
    {r : ℕ} (hmessage : message.length = 2 * key.length + r) (hr : r < 3) :
    keyDigest H (key ++ message) = key ++ H key message := by
  have hsplit : (key ++ message).length / 3 = key.length := by
    rw [List.length_append, hmessage]
    omega
  simp only [keyDigest, hsplit, List.take_left, List.drop_left]

/-- If a candidate's image is `k ++ H k x` for a length-preserving family, its message part either
collides with `x` under `k` or is `x` itself. -/
theorem isCollision_or_eq_of_keyDigest_eq {H : List Bool → List Bool → List Bool}
    (hlen : ∀ key message, (H key message).length = key.length) (n : ℕ)
    {candidate key message : List Bool} (h : keyDigest H candidate = key ++ H key message) :
    isCollision H (fun _ _ => true) n key message (candidate.drop (candidate.length / 3)) = true ∨
      candidate.drop (candidate.length / 3) = message := by
  simp only [keyDigest] at h
  generalize candidate.take (candidate.length / 3) = key' at h
  generalize candidate.drop (candidate.length / 3) = message' at h ⊢
  have hlength := congrArg List.length h
  simp only [List.length_append, hlen] at hlength
  obtain ⟨rfl, hdigest⟩ := List.append_inj h (by omega)
  by_cases hmessage : message' = message
  · exact Or.inr hmessage
  · exact Or.inl (isCollision_eq_true_iff.2 ⟨rfl, rfl, Ne.symm hmessage, hdigest.symm⟩)

/-- Comparing a function of a sample with a fixed word accepts with the probability that the image
distribution gives that word. -/
private theorem bind_pure_beq_apply (P : PMF (List Bool)) (φ : List Bool → List Bool)
    (x : List Bool) : (P.bind fun c => PMF.pure (φ c == x)) true = (P.map φ) x := by
  rw [PMF.bind_apply, PMF.map_apply]
  refine tsum_congr fun c => ?_
  by_cases h : φ c = x
  · simp [h]
  · simp [h, Ne.symm h]

/-- Every word of length `n` is the list of some function `Fin n → Bool`. -/
private theorem mem_image_ofFn {n : ℕ} {word : List Bool} (h : word.length = n) :
    word ∈ (Finset.univ : Finset (Fin n → Bool)).image List.ofFn := by
  subst h
  exact Finset.mem_image.2 ⟨word.get, Finset.mem_univ _, List.ofFn_get word⟩

/-- `2 ^ n` guesses at a `(2 n + r)`-bit word succeed with probability at most `(1 / 2) ^ n`. -/
private theorem two_pow_mul_one_div_two_pow_le (n r : ℕ) :
    (2 : ℝ≥0∞) ^ n * (1 / 2 ^ (2 * n + r)) ≤ ((1 / 2 : ℝ≥0) ^ n : ℝ≥0) := by
  have h2 : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hright : (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [ENNReal.coe_pow, one_div, ENNReal.coe_inv_two, ENNReal.inv_pow]
  rw [hright, show 2 * n + r = n + (n + r) by ring, pow_add, one_div,
    ENNReal.mul_inv (Or.inl h2) (Or.inl h2'), ← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two (by omega))

/-- **The reduction.** Inverting the construction at length `3 n + r` with `r < 3` succeeds at most
as often as the collision finder built from the inverter succeeds at parameter `n`, plus
`(1 / 2) ^ n`: a successful inverter either finds a collision under the uniform key or recovers the
`(2 n + r)`-bit message, of which it sees only an `n`-bit digest. -/
theorem succProbability_inversionGame_le {H : List Bool → List Bool → List Bool}
    (hlen : ∀ key message, (H key message).length = key.length) (adversary : Inverter)
    (n r : ℕ) (hr : r < 3) :
    Game.succProbability (ProbComp.eval (inversionGame (keyDigest H) adversary (3 * n + r))) ≤
      Game.succProbability
          (ProbComp.eval (collisionGame H (fun _ _ => true) (finder H adversary r) n)) +
        (1 / 2) ^ n := by
  have hsplit : BitString.uniformList (3 * n + r) = (BitString.uniformList n).bind
      (fun key => (BitString.uniformList (2 * n + r)).map (key ++ ·)) := by
    rw [show 3 * n + r = n + (2 * n + r) by ring]
    exact BitString.uniformList_add n (2 * n + r)
  have hguess : ∀ key ∈ (BitString.uniformList n).support,
      (BitString.uniformList (2 * n + r)).bind (fun message =>
        (ProbComp.eval (adversary (3 * n + r) (key ++ H key message))).bind fun candidate =>
          PMF.pure (candidate.drop (candidate.length / 3) == message)) true ≤
        ((1 / 2 : ℝ≥0) ^ n : ℝ≥0) := by
    intro key hkey
    have hklen := BitString.length_of_mem_support_uniformList hkey
    rw [PMF.bind_apply]
    simp only [bind_pure_beq_apply]
    refine (PMF.tsum_mul_apply_le_card_mul _ (BitString.uniformList_apply_le _) (H key)
      ((Finset.univ : Finset (Fin n → Bool)).image List.ofFn)
      (fun message => mem_image_ofFn ((hlen key message).trans hklen))
      (fun digest => (ProbComp.eval (adversary (3 * n + r) (key ++ digest))).map
        fun candidate => candidate.drop (candidate.length / 3))).trans ?_
    refine le_trans ?_ (two_pow_mul_one_div_two_pow_le n r)
    gcongr
    have hcard : ((Finset.univ : Finset (Fin n → Bool)).image List.ofFn).card ≤ 2 ^ n :=
      Finset.card_image_le.trans (by simp)
    exact_mod_cast hcard
  have key : ProbComp.eval (inversionGame (keyDigest H) adversary (3 * n + r)) true ≤
      ProbComp.eval (collisionGame H (fun _ _ => true) (finder H adversary r) n) true +
        ((1 / 2 : ℝ≥0) ^ n : ℝ≥0) := by
    simp only [inversionGame, collisionGame, finder, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, hsplit, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
      Function.comp_def]
    refine (PMF.bind_apply_le_add_on_support _ true fun key hkey => ?_).trans
      (add_le_add le_rfl (PMF.bind_apply_le_on_support _ hguess))
    refine PMF.bind_apply_le_add_on_support _ true fun message hmessage => ?_
    have hklen := BitString.length_of_mem_support_uniformList hkey
    have hmlen := BitString.length_of_mem_support_uniformList hmessage
    rw [keyDigest_append H (by rw [hmlen, hklen]) hr]
    refine PMF.bind_apply_le_add_on_support _ true fun candidate _ => ?_
    cases hwin : (keyDigest H candidate == key ++ H key message)
    · simp
    · rcases isCollision_or_eq_of_keyDigest_eq hlen n (beq_iff_eq.1 hwin) with hcol | hguess
      · rw [hcol]
        exact le_add_right le_rfl
      · rw [hguess, beq_self_eq_true]
        exact le_add_left le_rfl
  unfold Game.succProbability
  refine (ENNReal.toNNReal_mono (by finiteness) key).trans_eq ?_
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe]

end CollisionResistantToOneWay

open CollisionResistantToOneWay

/-- **Collision-resistant hashing gives a one-way function** ([KatzLindell2020], Exercise 8.4).
For a collision-resistant hash family `H`, the map `k ++ x ↦ k ++ H k x`, whose key `k` is the first
third of the input, is one-way. At input length `3 n + r`, `succProbability_inversionGame_le`
reduces inversion to the collision finder for the residue `r`; the three finders cover every
length. -/
theorem HashFamily.oneWay_keyDigest {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    OneWay (keyDigest H) := by
  refine OneWay.of_inversion_negligible (polyTime_keyDigest hH.polyTime)
    fun adversary hadversary => ?_
  have hcol (r : ℕ) := CollisionResistantOn.negligible hH.collisionResistant _
    (isPPT_finder hH.polyTime hadversary r)
  have hε := (((hcol 0).add_fun ((hcol 1).add_fun (hcol 2))).add_fun
    (negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1))).div_const (by norm_num : 0 < 3)
  refine negligible_of_le hε fun N => ?_
  obtain ⟨n, r, hr, rfl⟩ : ∃ n r, r < 3 ∧ N = 3 * n + r :=
    ⟨N / 3, N % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod N 3).symm⟩
  rw [show (3 * n + r) / 3 = n by omega]
  refine (succProbability_inversionGame_le hH.length_eq adversary n r hr).trans ?_
  gcongr
  interval_cases r
  · exact le_add_right le_rfl
  · exact le_add_left (le_add_right le_rfl)
  · exact le_add_left (le_add_left le_rfl)

/-- **Collision-resistant hash families yield one-way functions** ([KatzLindell2020],
Exercise 8.4). -/
theorem HashFamily.exists_oneWay {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ f, OneWay f :=
  ⟨_, hH.oneWay_keyDigest⟩

/-- A collision-resistant hash family yields a stateless EUF-CMA secure `SignatureScheme` on
`n`-bit messages, through `HashFamily.oneWay_keyDigest` and Rompel's theorem. -/
theorem HashFamily.exists_eufCMA {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ S : SignatureScheme, S.EUFCMA :=
  hH.oneWay_keyDigest.exists_eufCMA

/-- **Signatures from collision-resistant hashing** ([KatzLindell2020], Theorem 14.16): a
collision-resistant hash family yields a stateless EUF-CMA secure `WordSignatureScheme` on messages
of arbitrary length. Many-time security includes the one-time security of Lemma 14.13. -/
theorem HashFamily.exists_wordEUFCMA {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) : ∃ S : WordSignatureScheme, S.EUFCMA :=
  hH.oneWay_keyDigest.exists_wordEUFCMA

/-- A collision-resistant `2 n → n` compression family yields a one-way function, the setting of
[KatzLindell2020], Exercise 8.4: Merkle–Damgård extends it to a hash family on all bit strings. -/
theorem CompressionFamily.exists_oneWay {h : List Bool → List Bool → List Bool}
    (hh : CompressionFamily h) : ∃ f, OneWay f :=
  hh.hashFamily_merkleDamgard.exists_oneWay

/-- A collision-resistant `2 n → n` compression family yields a stateless EUF-CMA secure
`WordSignatureScheme` on messages of arbitrary length ([KatzLindell2020], Theorem 14.16). -/
theorem CompressionFamily.exists_wordEUFCMA {h : List Bool → List Bool → List Bool}
    (hh : CompressionFamily h) : ∃ S : WordSignatureScheme, S.EUFCMA :=
  hh.hashFamily_merkleDamgard.exists_wordEUFCMA

end Cslib.Crypto
