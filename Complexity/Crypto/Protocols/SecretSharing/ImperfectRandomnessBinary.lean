/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness
public import Mathlib.FieldTheory.Finite.GaloisField
import Complexity.Probability.PMF.Map

/-!
# Binary-size imperfect-randomness sharing

The Galois fields `GaloisField 2 b` instantiate the source-class separation for every `b ≥ 2`.
Thus the finite-field hypotheses are satisfiable at every message size, rather than an extra
assumption. The message, key, and share alphabets have respectively `2^b`, `2^(b+2)`, and
`2^(b+1)` elements. `binary_field_separation` gives cardinal-size statements.
`binary_string_separation`
transports the actual scheme and source laws through fixed bijections onto literal bit strings,
including every positive extractor output length. The bijections are chosen noncomputably;
no bit-level running-time claim is made.

This is the information-theoretic endpoint of [Aggarwal2026], Theorem 1.1, Sections 3–3.2.

## Main results

* `binary_field_separation`: the explicit `GaloisField 2 b` source-class separation for every
  `b ≥ 2`, with exact alphabet cardinalities.
* `binary_string_separation`: literal bit alphabets, flat support-size bounds, entropy,
  correctness, privacy and nonextractability for every positive output length.

## References

* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026], Theorem 1.1.
-/

public section

open Cslib.Probability
open scoped Cslib.Probability.PMF

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

open scoped Classical in
/-- Every binary message size at least two has a perfect source-class sharing scheme even though
no deterministic bit extractor has error below `1/6` on the whole source class. -/
theorem binary_field_separation (b : ℕ) (hb : 2 ≤ b) :
    let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
    Fintype.card (PaddedKey (GaloisField 2 b)) = 2 ^ (b + 2) ∧
      Fintype.card (Share (GaloisField 2 b)) = 2 ^ (b + 1) ∧
      ∃ α : GaloisField 2 b,
        (∀ m k, reconstruct α (paddedFirst m k) (paddedSecond α m k) = m) ∧
        (∀ T m m', (paddedSource T).map (paddedFirst m) =
          (paddedSource T).map (paddedFirst m') ∧
          (paddedSource T).map (paddedSecond α m) =
            (paddedSource T).map (paddedSecond α m')) ∧
        (∀ T : Finset (GaloisField 2 b), (b : ℝ) ≤ PMF.minEntropy (paddedSource T)) ∧
        (∀ ext : PaddedKey (GaloisField 2 b) → Bool, ∃ T, (1 : ℝ) / 6 ≤
          dist ((paddedSource T).map ext) (PMF.uniformOfFintype Bool)) := by
  classical
  let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 b) = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b (by omega)]
  exact sharing_at_bit_size hb hcard

/-- Theorem 1.1 on literal bit-string alphabets, including extractors of every positive
output length and flat source supports of the claimed size. The encodings are fixed
bijections; this theorem does not assert a bit-level running time for these bijections. -/
theorem binary_string_separation (b : ℕ) (hb : 2 ≤ b) :
    ∃ (sources : Finset (GaloisField 2 b) → PMF (Fin (b + 2) → Bool))
      (shr₁ shr₂ : (Fin b → Bool) → (Fin (b + 2) → Bool) → (Fin (b + 1) → Bool))
      (rec : (Fin (b + 1) → Bool) → (Fin (b + 1) → Bool) → (Fin b → Bool)),
      (∀ m k, rec (shr₁ m k) (shr₂ m k) = m) ∧
      (∀ T m m', (sources T).map (shr₁ m) = (sources T).map (shr₁ m') ∧
        (sources T).map (shr₂ m) = (sources T).map (shr₂ m')) ∧
      (∀ T, ∃ (K : Finset (Fin (b + 2) → Bool)) (hK : K.Nonempty),
        sources T = PMF.uniformOfFinset K hK ∧ 2 ^ b ≤ K.card ∧ K.card ≤ 2 ^ (b + 1)) ∧
      (∀ T, (b : ℝ) ≤ PMF.minEntropy (sources T)) ∧
      (∀ ℓ : ℕ, 0 < ℓ → ∀ ext : (Fin (b + 2) → Bool) → (Fin ℓ → Bool),
        ∃ T, (1 : ℝ) / 6 ≤ dist ((sources T).map ext)
          (PMF.uniformOfFintype (Fin ℓ → Bool))) := by
  classical
  let V := GaloisField 2 b
  let : Fintype V := Fintype.ofFinite _
  have hcard : Fintype.card V = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b (by omega)]
  obtain ⟨hk, hs, α, hrec, hprivacy, hent, _⟩ := sharing_at_bit_size hb hcard
  let em : V ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simpa using hcard)
  let ek : PaddedKey V ≃ (Fin (b + 2) → Bool) :=
    Fintype.equivOfCardEq (by simpa using hk)
  let es : Share V ≃ (Fin (b + 1) → Bool) :=
    Fintype.equivOfCardEq (by simpa using hs)
  let sources (T : Finset V) := (paddedSource T).map ek
  let shr₁ (m : Fin b → Bool) (k : Fin (b + 2) → Bool) :=
    es (paddedFirst (em.symm m) (ek.symm k))
  let shr₂ (m : Fin b → Bool) (k : Fin (b + 2) → Bool) :=
    es (paddedSecond α (em.symm m) (ek.symm k))
  let decode (s t : Fin (b + 1) → Bool) := em (reconstruct α (es.symm s) (es.symm t))
  refine ⟨sources, shr₁, shr₂, decode, ?_, ?_, ?_, ?_, ?_⟩
  · intro m k
    simp only [decode, shr₁, shr₂, Equiv.symm_apply_apply, hrec, Equiv.apply_symm_apply]
  · intro T m m'
    obtain ⟨h₁, h₂⟩ := hprivacy T (em.symm m) (em.symm m')
    constructor
    · simpa only [sources, shr₁, PMF.map_comp, Function.comp_def,
        Equiv.symm_apply_apply] using congrArg (fun p => p.map es) h₁
    · simpa only [sources, shr₂, PMF.map_comp, Function.comp_def,
        Equiv.symm_apply_apply] using congrArg (fun p => p.map es) h₂
  · intro T
    let K := (paddedKeys T).image ek
    have hK : K.Nonempty := (paddedKeys_nonempty T).image ek
    refine ⟨K, hK, ?_, ?_, ?_⟩
    · ext w
      simp only [sources, PMF.map_equiv_apply, paddedSource_apply, PMF.uniformOfFinset_apply,
        K, Finset.card_image_of_injective _ ek.injective]
      have hmem : w ∈ Finset.image ek (paddedKeys T) ↔ ek.symm w ∈ paddedKeys T := by
        constructor
        · intro h
          obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
          simpa only [← heq, Equiv.symm_apply_apply] using hk
        · intro h
          exact Finset.mem_image.mpr ⟨ek.symm w, h, ek.apply_symm_apply w⟩
      simp only [hmem]
    · change 2 ^ b ≤ ((paddedKeys T).image ek).card
      rw [Finset.card_image_of_injective _ ek.injective, card_paddedKeys, hcard]
      have ht := Finset.card_le_univ T
      rw [hcard] at ht
      omega
    · change ((paddedKeys T).image ek).card ≤ 2 ^ (b + 1)
      rw [Finset.card_image_of_injective _ ek.injective, card_paddedKeys, hcard, pow_succ]
      omega
  · intro T
    apply (PMF.le_minEntropy_iff _).mpr
    intro w
    rw [show sources T w = paddedSource T (ek.symm w) from PMF.map_equiv_apply _ _ _]
    exact (PMF.le_minEntropy_iff _).mp (hent T) _
  · intro ℓ hℓ ext
    let e : (Fin ℓ → Bool) ≃ Bool × (Fin (ℓ - 1) → Bool) :=
      (Equiv.cast (congrArg (fun n => Fin n → Bool) (by omega : ℓ = (ℓ - 1) + 1))).trans
        (Fin.consEquiv (fun _ : Fin ((ℓ - 1) + 1) => Bool)).symm
    obtain ⟨T, hT⟩ := padded_no_product_extractor (fun k : PaddedKey V => e (ext (ek k)))
    have hm := PMF.dist_map_le ((sources T).map ext)
      (PMF.uniformOfFintype (Fin ℓ → Bool)) e
    rw [PMF.uniformOfFintype_map_equiv] at hm
    refine ⟨T, ?_⟩
    have hT' : (1 : ℝ) / 6 ≤ dist (((sources T).map ext).map e)
        (PMF.uniformOfFintype (Bool × (Fin (ℓ - 1) → Bool))) := by
      simpa only [sources, PMF.map_comp, Function.comp_def] using hT
    exact hT'.trans hm

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
