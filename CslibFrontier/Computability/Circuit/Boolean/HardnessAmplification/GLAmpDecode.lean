/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmp
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLSynthesis
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

Each output bit of the candidate, as a function of the flat input `x` read in blocks
(`BitString.block x`), has a De Morgan circuit with at most
`(2 ^ K - 1) * (s + 1) + (4 + 2 * (2 ^ K - 1) * (2 ^ K + 1))` gates when `h` has one with `s`
(`Cslib.Circuits.Boolean.complexity_glAmpCandidate_apply_le`). The same bound holds when `h` is
computed from `q` answer bits and its input by a circuit with `s` gates, and the candidate reads
those answer bits as inputs too
(`Cslib.Circuits.Boolean.complexity_glAmpCandidate_answers_apply_le`). Running time is not
certified.

## Main definitions

* `Cslib.Circuits.Boolean.glAmpCandidate`: the Goldreich–Levin candidate for `f^k` at a tuple of
  blocks.

## Main results

* `Cslib.Circuits.Boolean.glAmpCandidate_apply`, `Cslib.Circuits.Boolean.glAmpCandidate_block`:
  unfolding the candidate, at a tuple and at the blocks of a flat input.
* `Cslib.Circuits.Boolean.glAmpCandidate_glAmp`: the true guess recovers `f^k` exactly.
* `Cslib.Circuits.Boolean.dens_filter_glAmpCandidate_agree`: Claim 4.4 in library form.
* `Cslib.Circuits.Boolean.complexity_glAmpCandidate_apply_le`: the circuit complexity of each
  output bit.
* `Cslib.Circuits.Boolean.complexity_glAmpCandidate_answers_apply_le`: the same bound with the
  predictor's answer bits as inputs.

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

/-- Unfolding `glAmpCandidate`, whose body is not exposed. -/
theorem glAmpCandidate_apply (h : BooleanFunction (k * n + k)) (masks : Fin K → BitString k)
    (guess : BitString K) (y : Fin k → BitString n) :
    glAmpCandidate h masks guess y =
      Crypto.GoldreichLevin.candidate (fun r => h (Fin.append (BitString.blocksEquiv.symm y) r))
        masks guess := by
  rw [glAmpCandidate]

/-- For the exact predictor `glAmp f k` and the true guess, the candidate is `f^k`. -/
theorem glAmpCandidate_glAmp (f : BooleanFunction n) (hK : 0 < K) (masks : Fin K → BitString k)
    (y : Fin k → BitString n) :
    glAmpCandidate (glAmp f k) masks (fun j => (fun i => f (y i)) ⬝ᵥ masks j) y =
      fun i => f (y i) := by
  have hpred : (fun r => glAmp f k (Fin.append (BitString.blocksEquiv.symm y) r)) =
      fun r => (fun i => f (y i)) ⬝ᵥ r := by
    funext r
    rw [glAmp_append, BitString.block_blocksEquiv_symm]
  rw [glAmpCandidate_apply, hpred]
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
    have hcount := Crypto.GoldreichLevin.card_filter_agreement_ge pred target hγ.le (by
      rw [← hpairs, hcard, ← mul_assoc, mul_assoc (1 / 2 + γ), ← pow_add]
      exact hagree)
    rwa [hcard] at hcount
  -- Goldreich–Levin decoding on the good tuples
  have hgl := Crypto.GoldreichLevin.dens_filter_candidate_eq_ge pred target (γ / 2)
    (by positivity) hK hsize good fun x hx => (mem_filter.1 hx).2
  -- the candidate agrees with `target` at `x` exactly when it agrees with `f^k` at its blocks
  have hcount (mg : (Fin K → BitString k) × BitString K) :
      #{y : Fin k → BitString n | ∀ i, glAmpCandidate h mg.1 mg.2 y i = f (y i)} =
        #{x | Crypto.GoldreichLevin.candidate (pred x) mg.1 mg.2 = target x} :=
    card_equiv BitString.blocksEquiv.symm fun y => by
      simp only [mem_filter, mem_univ, true_and]
      simp [glAmpCandidate_apply, pred, target, funext_iff]
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

/-- The candidate at the blocks of a flat input `x` is the Goldreich–Levin candidate for
`r ↦ h (x, r)`. -/
theorem glAmpCandidate_block (h : BooleanFunction (k * n + k)) (masks : Fin K → BitString k)
    (guess : BitString K) (x : BitString (k * n)) :
    glAmpCandidate h masks guess (BitString.block x) =
      Crypto.GoldreichLevin.candidate (fun r => h (Fin.append x r)) masks guess := by
  rw [glAmpCandidate_apply, BitString.blocksEquiv_symm_block]

/-- **The circuit complexity of the candidate.** If `h` has a De Morgan circuit with at most `s`
gates, each output bit of the candidate, as a function of the flat input read in blocks, has one
with at most `(2 ^ K - 1) * (s + 1) + (4 + 2 * (2 ^ K - 1) * (2 ^ K + 1))` gates: two constants,
`2 ^ K - 1` copies of `h`, each with at most one negation, and a strict majority. -/
theorem complexity_glAmpCandidate_apply_le {h : BooleanFunction (k * n + k)} {s : ℕ}
    (hh : complexity interpretation (single h) ≤ s) (masks : Fin K → BitString k)
    (guess : BitString K) (j : Fin k) :
    complexity interpretation
        (single fun x : BitString (k * n) => glAmpCandidate h masks guess (BitString.block x) j) ≤
      (2 ^ K - 1) * (s + 1) + (4 + 2 * (2 ^ K - 1) * (2 ^ K + 1)) := by
  simp only [glAmpCandidate_block]
  refine (complexity_candidate_apply_le hh masks guess j).trans_eq ?_
  have hK : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  rw [glBitCost, show 2 ^ K - 1 + 2 = 2 ^ K + 1 by omega]
  ring

/-- **The candidate with the predictor's answers as inputs.** Let the predictor be computed by a
De Morgan circuit `F` from `q` answer bits `w` and its input, so that it is
`y ↦ F (w ++ y)`. Then each output bit of the candidate, as a function of `w` and the flat
tuple read in blocks, has the bound of `complexity_glAmpCandidate_apply_le` with `s` gates for
`F`. Reordering the inputs of `F` costs no gates. -/
theorem complexity_glAmpCandidate_answers_apply_le {q : ℕ} {F : BooleanFunction (q + (k * n + k))}
    {s : ℕ} (hF : complexity interpretation (single F) ≤ s) (masks : Fin K → BitString k)
    (guess : BitString K) (j : Fin k) :
    complexity interpretation (single fun wx : BitString (q + k * n) =>
      glAmpCandidate (fun y => F (Fin.append (fun i => wx (Fin.castAdd (k * n) i)) y)) masks guess
        (BitString.block fun i => wx (Fin.natAdd q i)) j) ≤
      (2 ^ K - 1) * (s + 1) + (4 + 2 * (2 ^ K - 1) * (2 ^ K + 1)) := by
  -- reassociate the inputs of `F` by wiring, which costs no gates
  let sel : Fin (q + (k * n + k)) → Fin (q + k * n + k) :=
    Fin.append (fun i => Fin.castAdd k (Fin.castAdd (k * n) i))
      (Fin.append (fun i => Fin.castAdd k (Fin.natAdd q i)) (Fin.natAdd (q + k * n)))
  let C : BooleanFunction (q + k * n + k) := fun u => F (u ∘ sel)
  have hC : complexity interpretation (single C) ≤ s := by
    have e : single C = single F ∘ fun u => u ∘ sel := rfl
    rw [e]
    refine (complexity_comp_le _ _).trans ?_
    rw [complexity_wiring, zero_add]
    exact hF
  have e : (fun wx : BitString (q + k * n) =>
      glAmpCandidate (fun y => F (Fin.append (fun i => wx (Fin.castAdd (k * n) i)) y)) masks guess
        (BitString.block fun i => wx (Fin.natAdd q i)) j) =
      fun wx => Crypto.GoldreichLevin.candidate (fun r => C (Fin.append wx r)) masks guess j := by
    funext wx
    simp only [glAmpCandidate_block]
    refine congrArg (fun p => Crypto.GoldreichLevin.candidate p masks guess j) (funext fun r => ?_)
    simp only [C]
    congr 1
    funext p
    refine Fin.addCases (fun i => ?_) (fun i => ?_) p
    · simp [sel]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [sel]
  rw [e]
  refine (complexity_candidate_apply_le hC masks guess j).trans_eq ?_
  have hK : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  rw [glBitCost, show 2 ^ K - 1 + 2 = 2 ^ K + 1 by omega]
  ring

end Cslib.Circuits.Boolean
