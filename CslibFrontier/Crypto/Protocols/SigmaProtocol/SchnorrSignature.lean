/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.FiatShamir
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF

/-!
# Schnorr signatures

Schnorr signatures ([BonehShoup2023], Section 19.2) are the Fiat–Shamir signatures of Schnorr's
Sigma protocol. Over a vector space of prime order `q` with a nonzero base `g`, the commitment
`r • g` of a uniform `r` takes each value with probability at most `1 / q`
(`schnorr_commit_map_fst_le`). The Fiat–Shamir theorem then bounds the success of a forger making
at most `Qs` signing calls and `Qro` hash calls by

`Qs · (Qs + Qro) / q + (Qro + 1) / N + √((Qro + 1) · ε')`,

where `N` is the number of challenges and `ε'` the probability that the forking reduction computes
a discrete logarithm of the public key (`schnorr_succProbability_eufCmaGame_le`,
[BonehShoup2023], Theorem 19.7 with Equation 19.21). These are exact laws for one group and one
forger; the computational statement under the discrete-logarithm assumption is separate.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.schnorrROMScheme`: the Schnorr random-oracle signature
  scheme `fiatShamir (Function.Embedding.refl _) (schnorr ι g) (schnorrKeyGen g)`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.schnorrROMScheme_correct`: honest Schnorr signatures verify.
* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_commit_map_fst_le`: Schnorr commitments are
  `1 / q`-unpredictable.
* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_succProbability_eufCmaGame_le`: the security
  bound for Schnorr signatures in the random-oracle model.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.2.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability ROMSignature
open scoped ENNReal NNReal

variable {q : ℕ} [Fact q.Prime] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  {ι : C ↪ ZMod q} {g : G}

/-- **Unpredictable Schnorr commitments** ([BonehShoup2023], Definition 19.7): with a nonzero base,
the commitment `r • g` of a uniform `r` takes each value with probability at most `1 / q`. -/
theorem schnorr_commit_map_fst_le (hg : g ≠ 0) (x : ZMod q) (y t : G) :
    ((schnorr ι g).commit x y).map Prod.fst t ≤ (q : ℝ≥0∞)⁻¹ := by
  classical
  have hinj : Function.Injective fun r : ZMod q => r • g := fun r r' h => by
    have h' : (r - r') • g = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hg)
  have hmap : ((schnorr ι g).commit x y).map Prod.fst =
      (PMF.uniformOfFintype (ZMod q)).map fun r => r • g := by
    simp only [schnorr, linear, PMF.map_comp]
    rfl
  rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_uniformOfFintype, ZMod.card]
  calc ((Finset.univ.filter (· ∈ (fun r : ZMod q => r • g) ⁻¹' {t})).card : ℝ≥0∞) *
        (q : ℝ≥0∞)⁻¹
      ≤ 1 * (q : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast Finset.card_le_one.mpr fun a ha b hb =>
          hinj (by simp_all)
    _ = (q : ℝ≥0∞)⁻¹ := one_mul _

variable {M : Type}

/-- The Schnorr signature scheme in the random-oracle model ([BonehShoup2023], Section 19.2): the
Fiat–Shamir transform of `schnorr ι g` with key generator `schnorrKeyGen g`. -/
noncomputable abbrev schnorrROMScheme (ι : C ↪ ZMod q) (g : G) :
    Scheme G (ZMod q × G) M (G × ZMod q) (M × G) C :=
  fiatShamir (Function.Embedding.refl _) (schnorr ι g) (schnorrKeyGen g)

variable [Fintype C] [Nonempty C] [DecidableEq M]

/-- **Completeness of Schnorr signatures**: every honest signature produced by
`schnorrROMScheme ι g` verifies under the shared random oracle. -/
theorem schnorrROMScheme_correct (ι : C ↪ ZMod q) (g : G) :
    (schnorrROMScheme (M := M) ι g).Correct :=
  fiatShamir_correct (Function.Embedding.refl _) schnorr_complete fun _ h =>
    mem_support_schnorrKeyGen h

variable [DecidableEq C]

/-- **Security of Schnorr signatures** ([BonehShoup2023], Theorem 19.7 with Equation 19.21, exact
form): with a nonzero base, a forger making at most `Qs` signing calls and `Qro` hash calls
succeeds with probability at most `Qs · (Qs + Qro) / q + (Qro + 1) / N + √((Qro + 1) · ε')`, where
`N` is the number of challenges and `ε'` the probability that the forking reduction computes a
discrete logarithm of the public key, returning zero on a failed fork. -/
theorem schnorr_succProbability_eufCmaGame_le (hg : g ≠ 0)
    (A : Forger G M (G × ZMod q) (M × G) C) {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (eufCmaGame (fiatShamir (Function.Embedding.refl _) (schnorr ι g)
      (schnorrKeyGen g)) A) : ℝ) ≤
      Qs * (Qs + Qro) / q + (Qro + 1) / Fintype.card C +
        √((Qro + 1) * Game.succProbability (oneWayGame (schnorrKeyGen g)
          (fun α u => α • g = u) (FiatShamir.reduction (Function.Embedding.refl _) (schnorr ι g)
            (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)
            (linearExtract ι) 0 A Qs Qro))) := by
  have hq : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have h := succProbability_eufCmaGame_le (P := schnorr ι g) (δ := (q : ℝ≥0)⁻¹)
    (Function.Embedding.refl _)
    (fun _ h => mem_support_schnorrKeyGen h)
    (schnorr_specialSoundness.specialSoundOn (schnorrKeyGen g)) schnorr_specialHVZK
    (fun key _ t => by
      rw [ENNReal.coe_inv hq, ENNReal.coe_natCast]
      exact schnorr_commit_map_fst_le (ι := ι) hg key.1 key.2 t) 0 A hA
  rwa [NNReal.coe_inv, NNReal.coe_natCast, ← div_eq_mul_inv] at h

end Cslib.Crypto.Protocols.SigmaProtocol
