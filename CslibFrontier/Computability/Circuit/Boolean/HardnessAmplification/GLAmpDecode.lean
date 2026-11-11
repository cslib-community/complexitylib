/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmp
public import CslibFrontier.Crypto.Computational.GoldreichLevin.Nonuniform
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Goldreich–Levin decoding of the amplified function

Let `h` be a predictor for `glAmp f k = (f^k)^GL`. For a tuple `y` of `k` blocks, the
Goldreich–Levin candidate for `r ↦ h (y, r)`, with `K` fixed masks and a guess of their
parities, is a guess for `f^k (y) = (f (y i))ᵢ` (`Cslib.Circuits.Boolean.glAmpCandidate`). With
the true guess for `h = glAmp f k` it is exactly `f^k`
(`Cslib.Circuits.Boolean.glAmpCandidate_glAmp`).

**Claim 4.4 in library form** (`Cslib.Circuits.Boolean.dens_filter_glAmpCandidate_agree`). Suppose
`h` agrees with `glAmp f k` on a `1 / 2 + γ` fraction of the inputs, and
`k ≤ 2 * (γ / 2) ^ 2 * (2 ^ K - 1)`. Then for at least a `γ / 2 ^ (K + 3)` fraction of the masks
and guesses, the candidate equals `f^k` on at least a `γ / 2 ^ (K + 3)` fraction of the tuples
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Claim 4.4, pp. 10:15–10:16]
[CarmosinoImpagliazzoKabanetsKolokolova2016]. The proof follows the source: by averaging, a
`γ / 2` fraction of the tuples have agreement `1 / 2 + γ / 2` over the masks `r`
(`Cslib.Crypto.GoldreichLevin.dens_filter_agreement_ge`), and Goldreich–Levin decoding is applied
to each of them (`Cslib.Crypto.GoldreichLevin.dens_filter_candidate_eq_ge`).

Two deviations from the source are labelled here:

* **List loss.** The source uses the Goldreich–Rubinfeld–Sudan decoder [Thm 4.2, p. 10:15], with a
  list of size `O(1 / γ²)`. The library's decoder is the corrected-majority decoder of
  [GoldreichLevin1989], which decodes the `k` coordinates separately. It needs `2 ^ K` guesses with
  `2 ^ K - 1 ≥ 2 k / γ²`, a list of size `O(k / γ²)`.
* **A deterministic circuit per seed.** The source outputs a random element of the list and gets
  expected agreement `Ω(γ³)`. Here each choice of masks and guess gives a fixed function, and the
  statement is a fraction `δ₀ = γ / 2 ^ (K + 3)` of seeds with agreement `δ₀`. That is at least
  `γ³ / (36 k)` for the least admissible `K` when `γ ≤ 1 / 2`.

Only the decoded functions are certified; running time is not. Their circuit complexity is a
separate result.

## Main definitions

* `Cslib.Circuits.Boolean.glAmpCandidate`: the Goldreich–Levin candidate for `f^k` at a tuple of
  blocks.

## Main results

* `Cslib.Circuits.Boolean.glAmpCandidate_glAmp`: the true guess recovers `f^k` exactly.
* `Cslib.Circuits.Boolean.dens_filter_glAmpCandidate_agree`: Claim 4.4 in library form.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n k K : ℕ}

/-- **The Goldreich–Levin candidate for `f^k`.** At a tuple `y` of `k` blocks of `n` bits, the
corrected-majority candidate for the parities predicted by `r ↦ h (y, r)`, with the masks `masks`
and the guess `guess` of their parities. -/
def glAmpCandidate (h : BooleanFunction (k * n + k)) (masks : Fin K → BitString k)
    (guess : BitString K) (y : Fin k → BitString n) : BitString k :=
  Crypto.GoldreichLevin.candidate (fun r => h (Fin.append (BitString.blocksEquiv.symm y) r))
    masks guess

/-- For the exact predictor `glAmp f k` and the true guess, the candidate is `f^k`. -/
theorem glAmpCandidate_glAmp (f : BooleanFunction n) (hK : 0 < K) (masks : Fin K → BitString k)
    (y : Fin k → BitString n) :
    glAmpCandidate (glAmp f k) masks (fun j => (fun i => f (y i)) ⬝ᵥ masks j) y =
      fun i => f (y i) := by
  have hpred : (fun r => glAmp f k (Fin.append (BitString.blocksEquiv.symm y) r)) =
      fun r => (fun i => f (y i)) ⬝ᵥ r := by
    funext r
    rw [glAmp_append, BitString.block_blocksEquiv_symm]
  rw [glAmpCandidate, hpred]
  exact Crypto.GoldreichLevin.candidate_parity _ masks hK

/-- **Claim 4.4 of Carmosino, Impagliazzo, Kabanets and Kolokolova, in library form.** If `h`
agrees with `glAmp f k` on a `1 / 2 + γ` fraction of the inputs, `K ≥ 1` and
`k ≤ 2 * (γ / 2) ^ 2 * (2 ^ K - 1)`, then for at least a `γ / 2 ^ (K + 3)` fraction of the masks
and guesses, the candidate equals `f^k` on at least a `γ / 2 ^ (K + 3)` fraction of the tuples.
The list has `2 ^ K = O(k / γ²)` entries instead of the source's `O(1 / γ²)`, and the statement is
per seed rather than for a random list element; see the module docstring. -/
theorem dens_filter_glAmpCandidate_agree (f : BooleanFunction n) (h : BooleanFunction (k * n + k))
    {γ : ℝ} (hγ : 0 < γ) (hagree : (1 / 2 + γ) * 2 ^ (k * n + k) ≤ #{y | h y = glAmp f k y})
    (hK : 0 < K) (hsize : (k : ℝ) ≤ 2 * (γ / 2) ^ 2 * (2 ^ K - 1 : ℕ)) :
    γ / 2 ^ (K + 3) ≤ (dens {mg : (Fin K → BitString k) × BitString K |
      γ / 2 ^ (K + 3) * 2 ^ (k * n) ≤
        #{y : Fin k → BitString n | ∀ i, glAmpCandidate h mg.1 mg.2 y i = f (y i)}} : ℝ) := by
  classical
  let pred : BitString (k * n) → BitString k → Bool := fun x r => h (Fin.append x r)
  let target : BitString (k * n) → BitString k := fun x i => f (BitString.block x i)
  have hcard : (Fintype.card (BitString (k * n)) : ℝ) = 2 ^ (k * n) := by
    rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat]
  -- the agreement as a count of pairs
  have hpairs : #{y | h y = glAmp f k y} =
      #{xr : BitString (k * n) × BitString k | pred xr.1 xr.2 = target xr.1 ⬝ᵥ xr.2} :=
    card_equiv (Fin.appendEquiv (k * n) k).symm fun y => by
      simp [pred, target, Fin.append_castAdd_natAdd, ← glAmp_append]
  -- by averaging, a `γ / 2` fraction of the tuples have agreement `1 / 2 + γ / 2`
  set good := (univ : Finset (BitString (k * n))).filter fun x =>
    1 / 2 + γ / 2 ≤ Crypto.GoldreichLevin.agreement (pred x) (target x)
  have hgood : γ / 2 * 2 ^ (k * n) ≤ #good := by
    have hdens := Crypto.GoldreichLevin.dens_filter_agreement_ge pred target hγ.le (by
      rw [← hpairs, hcard, ← mul_assoc, mul_assoc (1 / 2 + γ), ← pow_add]
      exact hagree)
    rw [nnratCast_dens, hcard, le_div_iff₀ (by positivity)] at hdens
    exact hdens
  -- Goldreich–Levin decoding on the good tuples
  have hgl := Crypto.GoldreichLevin.dens_filter_candidate_eq_ge pred target (γ / 2)
    (by positivity) hK hsize good fun x hx => (mem_filter.1 hx).2
  -- the candidate agrees with `target` at `x` exactly when it agrees with `f^k` at its blocks
  have hcount (mg : (Fin K → BitString k) × BitString K) :
      #{y : Fin k → BitString n | ∀ i, glAmpCandidate h mg.1 mg.2 y i = f (y i)} =
        #{x | Crypto.GoldreichLevin.candidate (pred x) mg.1 mg.2 = target x} :=
    card_equiv BitString.blocksEquiv.symm fun y => by
      simp only [mem_filter, mem_univ, true_and]
      simp [glAmpCandidate, pred, target, funext_iff]
  have hfrac :
      γ / 2 ^ (K + 3) ≤ (#good : ℝ) / (2 ^ (K + 2) * Fintype.card (BitString (k * n))) := by
    rw [hcard, le_div_iff₀ (by positivity)]
    calc γ / 2 ^ (K + 3) * (2 ^ (K + 2) * 2 ^ (k * n)) = γ / 2 * 2 ^ (k * n) := by
          rw [pow_succ]
          field_simp
      _ ≤ #good := hgood
  refine hfrac.trans (hgl.trans ?_)
  gcongr with mg
  intro hmg
  rw [hcount]
  have hmg' : (#good : ℝ) ≤ 2 ^ (K + 2) *
      #{x | Crypto.GoldreichLevin.candidate (pred x) mg.1 mg.2 = target x} := by
    exact_mod_cast hmg
  calc γ / 2 ^ (K + 3) * 2 ^ (k * n) = γ / 2 * 2 ^ (k * n) / 2 ^ (K + 2) := by
        rw [pow_succ]
        field_simp
    _ ≤ #good / 2 ^ (K + 2) := by gcongr
    _ ≤ _ := by
        rw [div_le_iff₀ (by positivity)]
        linarith

end Cslib.Circuits.Boolean
