/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.ModulusSwitch.Correctness
public import Complexity.Probability.Product.Event
public import Complexity.Probability.PMF.Event

/-!
# Randomized correctness after Module-LWE modulus switching

The experiment retains the same secret that generates its public key. Supported bounds on
the secret and ephemeral laws reduce decryption failure to a bad noise polynomial among the
`k` key errors, `k` encryption errors and one final error. These are original sufficient
correctness bounds for the supplied laws, with no security or complete native-runtime claim.

## Main results

* `moduleLWEDecrypt_modulusSwitch_encrypt_eq_of_bounds`: component bounds imply correctness.
* `toOuterMeasure_moduleLWEModulusSwitch_failure_le`: the actual sampled experiment's bound.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Uniform component bounds supply the phase budget used by the honest-encryption theorem. -/
theorem moduleLWEDecrypt_modulusSwitch_encrypt_eq_of_bounds
    {k n q p Bs Br Be Bp : ℕ} (hq : 0 < q) (hp : 4 * Bp + 2 < p)
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    {s r e e₁ : Fin k → Fin n → ZMod q} {e₂ : Fin n → ZMod q}
    (hs : ModuleSIS.inInfNormBound Bs s) (hr : ModuleSIS.inInfNormBound Br r)
    (he : ModuleSIS.inInfNormBound Be e) (he₁ : ModuleSIS.inInfNormBound Be e₁)
    (he₂ : GeneralSIS.inInfNormBound Be e₂) (m : Fin n → Bool)
    (hbudget : (p : ℚ) / q * (k * n * Be * Br + k * n * Be * Bs + Be : ℕ) +
      (1 + k * n * Bs) / 2 + |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    moduleLWEDecrypt (fun j i => (GeneralSIS.liftCentered (s j) i : ZMod p))
      (moduleLWEModulusSwitch p (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m)) = m := by
  apply moduleLWEDecrypt_modulusSwitch_encrypt_eq hq hp A s r e e₁ e₂ m
    (abs_moduleLWEErrorPoly_le hs hr he he₁ he₂)
  have hsum : (∑ j, ∑ i, |(GeneralSIS.liftCentered (s j) i : ℚ)|) ≤ k * n * Bs := by
    calc
      _ ≤ ∑ _j : Fin k, ∑ _i : Fin n, (Bs : ℚ) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast hs j i
      _ = _ := by simp [mul_assoc]
  linarith

/-- In the retained-secret experiment, switching fails only if one of the `2*k+1` independently
sampled noise polynomials exceeds the good radius. The secret bounds hold on their actual
supports; no source decryption conclusion or source decoding margin is assumed. -/
theorem toOuterMeasure_moduleLWEModulusSwitch_failure_le
    {k n q p Bs Br Be Bp : ℕ} [NeZero q]
    (hp : 4 * Bp + 2 < p) (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool)
    (secretLaw ephemeralLaw : PMF (Fin k → Fin n → ZMod q))
    (hs : ∀ s ∈ secretLaw.support, ModuleSIS.inInfNormBound Bs s)
    (hr : ∀ r ∈ ephemeralLaw.support, ModuleSIS.inInfNormBound Br r)
    (hbudget : (p : ℚ) / q * (k * n * Be * Br + k * n * Be * Bs + Be : ℕ) +
      (1 + k * n * Bs) / 2 + |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    (do
      let s ← secretLaw
      let view ← encryptionViewOfKeyLaw (moduleLWEPublicKeyLaw k n q noise (PMF.pure s))
        noise m ephemeralLaw
      pure (s, view)).toOuterMeasure
        {out | moduleLWEDecrypt
          (fun j i => (GeneralSIS.liftCentered (out.1 j) i : ZMod p))
          (moduleLWEModulusSwitch p out.2.2) ≠ m} ≤
      (2 * k + 1) * noise.toOuterMeasure {e | ¬ GeneralSIS.inInfNormBound Be e} := by
  classical
  let δ := noise.toOuterMeasure {e | ¬ GeneralSIS.inInfNormBound Be e}
  let μ := PMF.pi (fun _ : Fin k => noise)
  let bad : Set ((Fin k → Fin n → ZMod q) ×
      (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q)) :=
    {out | moduleLWEDecrypt
      (fun j i => (GeneralSIS.liftCentered (out.1 j) i : ZMod p))
      (moduleLWEModulusSwitch p out.2.2) ≠ m}
  have hμ : μ.toOuterMeasure {e | ¬ ModuleSIS.inInfNormBound Be e} ≤ k * δ := by
    simpa [μ, ModuleSIS.inInfNormBound, δ, GeneralSIS.inInfNormBound, not_forall,
      Finset.sum_const, nsmul_eq_mul] using
      PMF.toOuterMeasure_pi_exists_le (fun _ : Fin k => noise)
        (fun _ => {e | ¬ GeneralSIS.inInfNormBound Be e})
  have hlast (s r e : Fin k → Fin n → ZMod q)
      (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
      (hs' : ModuleSIS.inInfNormBound Bs s) (hr' : ModuleSIS.inInfNormBound Br r)
      (he : ModuleSIS.inInfNormBound Be e) :
      (do
        let e₂ ← noise
        let e₁ ← μ
        pure (s, (moduleLWEKeyGen A s e,
          moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m))).toOuterMeasure bad ≤
        δ + k * δ := by
    refine (PMF.toOuterMeasure_bind_failure_le noise _
      {e₂ | GeneralSIS.inInfNormBound Be e₂} bad (k * δ) ?_).trans ?_
    · intro e₂ _ he₂
      refine (PMF.toOuterMeasure_bind_failure_le μ _
        {e₁ | ModuleSIS.inInfNormBound Be e₁} bad 0 ?_).trans ?_
      · intro e₁ _ he₁
        have hcorrect := moduleLWEDecrypt_modulusSwitch_encrypt_eq_of_bounds
          (NeZero.pos q) hp A hs' hr' he he₁ he₂ m hbudget
        rw [nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff]
        change Disjoint (PMF.pure _).support bad
        rw [PMF.support_pure, Set.disjoint_singleton_left]
        exact fun h => h hcorrect
      · simpa only [Set.compl_ofPred, add_zero] using hμ
    · exact le_rfl
  simp only [encryptionViewOfKeyLaw, moduleLWEPublicKeyLaw, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind]
  change (secretLaw.bind _).toOuterMeasure bad ≤ (2 * k + 1) * δ
  refine (PMF.toOuterMeasure_bind_failure_le secretLaw _ Set.univ bad
    ((2 * k + 1) * δ) ?_).trans ?_
  · intro s hss _
    refine (PMF.toOuterMeasure_bind_failure_le (PMF.uniformOfFintype _) _ Set.univ bad
      ((2 * k + 1) * δ) ?_).trans ?_
    · intro A _ _
      refine (PMF.toOuterMeasure_bind_failure_le μ _
        {e | ModuleSIS.inInfNormBound Be e} bad (δ + k * δ) ?_).trans ?_
      · intro e _ he
        refine (PMF.toOuterMeasure_bind_failure_le ephemeralLaw _ Set.univ bad
          (δ + k * δ) ?_).trans ?_
        · intro r hrr _
          exact hlast s r e A (hs s hss) (hr r hrr) he
        · simp
      · calc
          _ ≤ k * δ + (δ + k * δ) := add_le_add hμ le_rfl
          _ = _ := by ring
    · simp
  · simp

end Cslib.Crypto
