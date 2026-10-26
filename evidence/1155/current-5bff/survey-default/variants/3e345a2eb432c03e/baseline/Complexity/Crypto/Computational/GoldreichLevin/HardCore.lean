/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.WordReduction
public import Complexity.Crypto.Computational.HardCore
import Complexity.Probability.PMF.Bind
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# The Goldreich–Levin hard-core predicate

Split a seed into two equal halves and an optional spare bit. Apply the one-way function to
the first half and retain the rest. The inner product of the two halves is a hard-core predicate.
Keeping the spare bit extends the construction to every seed length.

`OneWayPermutation.pseudorandomGenerator` completes the one-bit PRG construction, including
deterministic polynomial time and security against uniform PPT adversaries.

## Main definitions

* `paddedFunction`, `paddedPredicate`: the length-total Goldreich–Levin construction.
* `generator`: append the hard-core bit to the padded image.

## Main results

* `padded_hardCore`: every one-way function gives a hard-core predicate for its padded function.
* `OneWayPermutation.pseudorandomGenerator`: a uniform polynomial-time one-bit PRG.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.

Adapted from Crypto/Computational/GoldreichLevin/HardCore.lean on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared game API and tidy TM calculus.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability BitString Turing.MultiTapeTM

/-- Apply a function to the first half of a word and retain the remaining bits. -/
def paddedFunction (f : List Bool → List Bool) (seed : List Bool) : List Bool :=
  let half := seed.length / 2
  f (seed.take half) ++ seed.drop half

/-- The inner product of the first two equal halves, ignoring an optional final bit. -/
def paddedPredicate (seed : List Bool) : Bool :=
  let half := seed.length / 2
  ((seed.take half).zipWith Bool.and ((seed.drop half).take half)).foldl Bool.xor false

/-- The padded function uses ordinary slicing and one call to the supplied function. -/
@[fun_prop]
theorem polyTime_paddedFunction {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime (paddedFunction f) encBits encBits := by
  unfold paddedFunction
  polytime

/-- The hard-core predicate is an efficient dot product of the two halves. -/
@[fun_prop]
theorem polyTime_paddedPredicate :
    ComputableInPolyTime paddedPredicate encBits encBool := by
  unfold paddedPredicate
  polytime

/-- On two equal chunks and at most one spare bit, only the first chunk is transformed. -/
theorem paddedFunction_chunks (f : List Bool → List Bool) {n : ℕ} (x r : BitString n)
    (extra : List Bool) (hextra : extra.length ≤ 1) :
    paddedFunction f (List.ofFn x ++ List.ofFn r ++ extra) =
      f (List.ofFn x) ++ List.ofFn r ++ extra := by
  have hhalf : (n + (n + extra.length)) / 2 = n := by lia
  simp [paddedFunction, hhalf, List.append_assoc]

/-- The spare bit is retained by the function but does not enter the parity. -/
theorem paddedPredicate_chunks {n : ℕ} (x r : BitString n)
    (extra : List Bool) (hextra : extra.length ≤ 1) :
    paddedPredicate (List.ofFn x ++ List.ofFn r ++ extra) = x ⬝ᵥ r := by
  have hhalf : (n + (n + extra.length)) / 2 = n := by lia
  simp [paddedPredicate, hhalf, List.append_assoc, dotProduct_eq_foldl]

/-- A length-preserving function leaves the complete padded seed length unchanged. -/
theorem paddedFunction_length {f : List Bool → List Bool}
    (hlen : ∀ word, (f word).length = word.length) (seed : List Bool) :
    (paddedFunction f seed).length = seed.length := by
  simp only [paddedFunction, List.length_append, hlen, List.length_take, List.length_drop]
  lia

/-- Permuting the first half preserves uniform seeds of every length. -/
theorem paddedFunction_uniform {f : List Bool → List Bool}
    (hf : ∀ n, (uniformList n).map f = uniformList n) (n : ℕ) :
    (uniformList n).map (paddedFunction f) = uniformList n := by
  have hsplit : uniformList n = (uniformList (n / 2)).bind
      (fun left => (uniformList (n - n / 2)).map (left ++ ·)) := by
    convert uniformList_add (n / 2) (n - n / 2) using 1
    congr 1
    lia
  rw [hsplit, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  trans ((uniformList (n / 2)).map f).bind
    (fun left => (uniformList (n - n / 2)).map (left ++ ·))
  · rw [PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro left hleft
    simp only [PMF.map, Function.comp_def]
    apply PMF.bind_congr_on_support
    intro right hright
    congr 1
    have hleft := length_of_mem_support_uniformList hleft
    have hright := length_of_mem_support_uniformList hright
    have hlen : (left ++ right).length = n := by
      simp only [List.length_append, hleft, hright]
      lia
    simp [paddedFunction, hlen, ← hleft]
  · rw [hf]

/-- Translate a predictor for a padded seed to a parity predictor, sampling its spare bits. -/
noncomputable def paddedPredictor (adversary : Distinguisher) (spare : ℕ) : Distinguisher :=
  fun n input => do
    let extra ← BitString.sampleList spare
    adversary (2 * n + spare) (input ++ extra)

/-- Parameter rescaling, sampling, and captured adversary calls have a uniform PPT certificate. -/
@[program_certificate]
theorem isPPT_paddedPredictor {adversary : Distinguisher}
    (hPPT : IsPPT encBool adversary) (spare : ℕ) :
    IsPPT encBool (paddedPredictor adversary spare) := by
  unfold paddedPredictor
  ppt

/-- The padded prediction experiment is the parity experiment, for either possible spare length. -/
theorem eval_paddedPrediction (f : List Bool → List Bool) (adversary : Distinguisher)
    (n spare : ℕ) (hspare : spare ≤ 1) :
    ProbComp.eval (predictionGame (paddedFunction f) paddedPredicate adversary (2 * n + spare)) =
      ProbComp.eval (parityPredictionGame f (paddedPredictor adversary spare) n) := by
  simp only [predictionGame, parityPredictionGame, paddedPredictor, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbComp.eval_pure, two_mul]
  rw [uniformList_add (n + n) spare, uniformList_add n n]
  simp only [uniformList, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext x
  congr 1
  funext r
  congr 1
  funext extra
  rw [paddedFunction_chunks f x r (List.ofFn extra) (by simpa using hspare),
    paddedPredicate_chunks x r (List.ofFn extra) (by simpa using hspare), dotProduct_eq_foldl]

/-- Goldreich–Levin supplies an efficient hard-core predicate for the padded function. Two fixed
PPT reductions handle even and odd seed lengths; no length-dependent adversary is chosen. -/
theorem padded_hardCore {f : List Bool → List Bool} (hf : OneWay f) :
    HardCore (paddedFunction f) paddedPredicate := by
  apply HardCore.of_unpredictable polyTime_paddedPredicate
  intro adversary hPPT
  have heven := negligible_parityPrediction hf _ (isPPT_paddedPredictor hPPT 0)
  have hodd := negligible_parityPrediction hf _ (isPPT_paddedPredictor hPPT 1)
  apply negligible_of_le ((heven.add hodd).div_const two_pos)
  intro n
  have hgame := eval_paddedPrediction f adversary (n / 2) (n % 2) (by lia)
  have hlen : 2 * (n / 2) + n % 2 = n := by lia
  rw [hlen] at hgame
  simp only [predictionAdvantage, hgame]
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [heven]
    exact le_add_of_nonneg_right zero_le
  · rw [hodd]
    exact le_add_of_nonneg_left zero_le

/-- The one-bit generator: permute the first half, retain the rest, and append the parity. -/
def generator (f : List Bool → List Bool) (seed : List Bool) : List Bool :=
  paddedFunction f seed ++ [paddedPredicate seed]

end Cslib.Crypto.GoldreichLevin

namespace Cslib.Crypto

open GoldreichLevin

/-- One-way permutations imply uniform polynomial-time pseudorandom generators with one-bit
stretch. Goldreich–Levin supplies the hard-core predicate; uniformity supplies the ideal hybrid. -/
theorem OneWayPermutation.pseudorandomGenerator {f : List Bool → List Bool}
    (hf : OneWayPermutation f) :
    PseudorandomGenerator (generator f) (fun n => n + 1) :=
  (padded_hardCore hf.oneWay).pseudorandomGenerator
    (polyTime_paddedFunction hf.oneWay.polyTime) (paddedFunction_length hf.length_eq)
    (paddedFunction_uniform hf.uniformList_map)

end Cslib.Crypto
