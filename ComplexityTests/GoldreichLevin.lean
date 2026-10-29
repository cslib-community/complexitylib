/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GoldreichLevin.HardCore
import Complexity.Probability.PMF.Expect
import Complexity.Tactic.PPT

/-! Decoder checks with imperfect and perfect predictors, overlapping masks, and boundary cases. -/

namespace ComplexityTests.GoldreichLevin

open Cslib Cslib.Crypto.GoldreichLevin Cslib.Probability
open Finset
open scoped ENNReal

-- Ties, including the empty vote, are false in the shared majority operation.
example : BitString.strictMajorityOn (∅ : Finset (Fin 2)) (fun _ => true) = false := by decide
example : BitString.strictMajorityOn Finset.univ (fun i : Fin 2 => decide (i = 0)) = false := by
  decide

-- The two subsets overlap; their sums are still independent and uniform.
example (n : ℕ) :
    (PMF.uniformOfFintype (Fin 2 → BitString n)).map (fun masks => (masks 0, masks 0 + masks 1)) =
      PMF.uniformOfFintype (BitString n × BitString n) := by
  simpa using PMF.uniformOfFintype_map_sum_pair (G := BitString n)
    ({0} : Finset (Fin 2)) {0, 1} (by simp) (by simp) (by decide)

private def noisy (r : BitString 2) : Bool := r 0 && r 1
private def target : BitString 2 := ![true, false]

-- A genuinely imperfect predictor agrees with a parity on three of the four queries.
private theorem noisy_agreement : agreement noisy target = 3 / 4 := by
  rw [agreement_eq_probability, PMF.toReal_uniformOfFintype_map_apply_true]
  have hcount : #{r : BitString 2 | (noisy r == target ⬝ᵥ r) = true} = 3 := by decide
  rw [Finset.dens_eq_card_div_card, hcount]
  norm_num [BitString]

-- The concentration hypotheses are instantiated without assuming a perfect predictor.
example : (decode noisy 5).toOuterMeasure {list | target ∉ list} ≤ 1 / 2 := by
  apply decode_failure_le_half noisy target (1 / 4) (by norm_num) (by decide)
  · rw [noisy_agreement]
    norm_num
  · norm_num

-- Perfect prediction retains the target with a fixed all-zero mask.
example : target ∈ candidates (fun r => target ⬝ᵥ r)
    (fun _ : Fin 1 => (![false, false] : BitString 2)) := by decide

-- Zero target length is valid; positive mask count is still an explicit theorem hypothesis.
example : (decode (fun _ : BitString 0 => false) 1).toOuterMeasure {list | 0 ∉ list} ≤ 1 / 2 := by
  apply decode_failure_le_half _ 0 (1 / 2) (by norm_num) (by decide)
  · norm_num [agreement, score, dotProduct, Bool.zero_eq_false]
    rfl
  · norm_num

-- Enumeration is executable, complete, and fixes the expected binary order.
example : BitString.enum 0 = [Fin.elim0] := rfl
example : (BitString.enum 2).map List.ofFn =
    [[false, false], [true, false], [false, true], [true, true]] := by decide

-- A different preimage is accepted, and first-match order is preserved.
example : checkCandidates (fun x : BitString 2 => x 0) true
    [![true, true], ![true, false]] = ![true, true] := by decide
example {n : ℕ} (f : BitString n → Bool) (image : Bool) : checkCandidates f image [] = 0 := rfl

-- The seed type can depend on the image, including images of different weights.
private noncomputable def seedLaw {n : ℕ} (image : BitString n) :
    PMF (BitString (n + BitString.weight image)) :=
  PMF.uniformOfFintype _

private theorem negative_prediction (n : ℕ) :
    predictionExperiment (id : BitString n → BitString n)
      (fun image _ query => !(image ⬝ᵥ query)) seedLaw = PMF.pure false := by
  simp only [predictionExperiment, id_eq, Bool.not_beq_self, PMF.monad_bind_eq_bind,
    PMF.bind_const]
  exact PMF.map_const _ _

-- Perfectly negative bias is handled by the same random-sign inverter, with dependent seeds.
example (n : ℕ) :
    1 / 16 ≤ (inversionExperiment (id : BitString n → BitString n)
      (invertSigned id (fun image _ query => !(image ⬝ᵥ query)) seedLaw (maskCount n 2))
      true).toReal := by
  have h := invertSigned_success_ge (id : BitString n → BitString n)
    (fun image _ query => !(image ⬝ᵥ query)) seedLaw (1 / 2) (by norm_num)
    (maskCount_pos n 2) (by rw [negative_prediction]; norm_num)
    (maskCount_sufficient n 2 (by decide))
  norm_num at h ⊢
  exact h

-- Even degree zero and dimension zero have valid, nonempty parameter choices.
example : precision 0 0 = 1 ∧ maskCount 0 1 = 1 := by decide

open Turing.MultiTapeTM

-- The complete decoder has a closed uniform certificate with an input-dependent parity predictor.
example (degree : ℕ) : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool =>
      wordDecode id (fun query => (p.2.1.zipWith Bool.and query).foldl Bool.xor false)
        degree p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) encBits := by polytime

-- Runtime fallback and captured-predicate search compose without exposing a machine.
example : ComputableInPolyTime
    (fun p : ℕ × List (List Bool) =>
      (p.2.find? (fun word => word.length == p.1)).getD (List.replicate p.1 false))
    (encPair encUnary (encList encBits)) encBits := by fun_prop

-- Output-size bounds cannot be silently discarded to certify exponential enumeration.
example : True := by
  fail_if_success
    have : ComputableInPolyTime BitString.enumList encUnary (encList encBits) := by polytime
  trivial

-- The total word algorithms cover ties, short selectors, short rows and out-of-range coordinates.
example : BitString.listStrictMajority [] = false ∧
    BitString.listStrictMajority [true, false] = false := by decide
example : BitString.listSingle 2 5 = [false, false] := by decide
example : BitString.listXorSelected 3 [true] [[true, false], [false, true, true]] =
    [true, false] := by decide
example : wordCheckCandidates (fun _ => []) 3 [] [[true], [false, true]] = [true] := by decide
example (f : List Bool → List Bool) (image : List Bool) :
    wordCheckCandidates f 3 image [] = [false, false, false] := rfl

-- A one-bit mask tape is padded to the requested matrix; the perfect predictor still recovers x.
example : wordDecode id (fun query => (query.zipWith Bool.and [true, false]).foldl Bool.xor false)
    0 2 [true, false] [true] = [true, false] := by decide
example : wordDecode id (fun _ => false) 0 0 [] [] = [] := by decide

-- A closed randomized inverter certificate includes captured input and saved-seed processing.
example (c d degree : ℕ) : IsPPT encBits
    (wordInverter id
      (fun input coins => (input.2.zipWith Bool.and coins).foldl Bool.xor false) c d degree) := by
  ppt

-- The budget uses the actual framing, including the unary parameter and arbitrary image length.
example (c d n : ℕ) (image : List Bool) (query : BitString n) :
    c * ((encPair encUnary encBits (n, image ++ List.ofFn query)).length + 1) ^ d =
      coinBudget c d n image.length := by
  congr 2
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
    List.length_append, List.length_ofFn]
  lia

-- Even empty inputs have a concrete game law; zero saved coins are valid for a constant evaluator.
example (degree : ℕ) :
    ProbComp.eval (wordInverter id (fun _ _ => false) 0 0 degree 0 []) = PMF.pure [] := by
  rw [wordInverter_eval]
  exact PMF.map_const _ []

-- Odd lengths preserve the spare bit without including it in the inner product.
example : paddedPredicate [true, true, false] = true ∧
    paddedPredicate [true, true, true] = true := by decide
example : paddedFunction (fun word => word ++ [true]) [false, true, false] =
    [false, true, true, false] := by decide
example : generator id [] = [false] ∧ generator id [true] = [true, false] := by decide

-- Uniform preservation is independent of the cryptographic one-wayness hypothesis.
example (n : ℕ) : (BitString.uniformList n).map (paddedFunction id) = BitString.uniformList n :=
  paddedFunction_uniform (fun _ => PMF.map_id _) n

end ComplexityTests.GoldreichLevin
