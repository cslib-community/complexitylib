/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.OneWay
import Complexity.Tactic.PPT

/-! Complete hashed-parity observations, ordinary program clients and encoded tape budgets. -/

namespace ComplexityTests.HashedParity

open Cslib Cslib.BitString Cslib.Probability Cslib.Crypto Cslib.Crypto.Pseudoentropy
open Cslib.Crypto.Pseudoentropy.HashPair Turing.MultiTapeTM
open Cslib.Probability.PMF

-- The sampler contract is inhabited even for a maximally noninjective function.
-- This supplies no one-wayness assumption and makes no security claim about that function.
private noncomputable def constantPair : SamplablePair :=
  pair (fun _ => []) (by fun_prop) (fun _ _ => ())
    (fun _ => ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩) (fun _ _ => rfl)

example : IsPPTOn encUnary (encPair encBits encBool) constantPair.sample := constantPair.efficient

-- Named programs compose with computed parameters under an alternative caller encoding.
example : IsPPTOn (encPair (encList encBool) encUnary) (encPair encBits encBool)
    (fun input : List Bool × ℕ => sample List.reverse (input.2 + input.1.length)) := by ppt

-- The five-sample inverter accepts a typed Boolean callback and an unbounded auxiliary word.
example : IsPPT encBits
    (wordInverter List.reverse (fun input coins => input.2 == coins) 2 3 3) := by ppt

-- No hidden parity remains in dimension zero, despite the nontrivial sampled hash length.
example : (ProbComp.eval (sample id 0)).map Prod.snd = PMF.pure false := by
  simp [sample, sampleList, ProbComp.eval_map, Function.comp_def, PMF.map,
    PMF.bind_const]

-- Distinguish retained fields, even when the function image and digest agree.
example : wordObservation [] 0 [true] [false] [false] ≠
    wordObservation [] 0 [true] [false] [true] := by decide

example : wordObservation [] 0 [false] [false] [true] ≠
    wordObservation [] 0 [true] [false] [true] := by decide

-- At dimension 8 the maximal index is 15. The old 2*n allowance misses four cells;
-- small dimensions could hide this error in the additive slack.
example : (encPair encUnary encBits (8,
    wordObservation [] 15 (List.replicate 128 false) (List.replicate 16 false)
      (List.replicate 8 false))).length + 1 = 348 := by
  simp only [wordObservation, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  norm_num

example : coinBudget 1 1 8 0 = 352 := by decide

example : ¬ (encPair encUnary encBits (8,
    wordObservation [] 15 (List.replicate 128 false) (List.replicate 16 false)
      (List.replicate 8 false))).length + 1 ≤
      2 * (hashCount 8 * 8) + 4 * hashCount 8 + 2 * 8 + 8 := by
  simp only [wordObservation, length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
    show hashCount 8 = 16 from by decide]
  norm_num

-- The actual bound also covers arbitrary images and every supported digest length.
example (c d n : ℕ) (image : List Bool) (index : Fin (hashCount n))
    (matrix : BitString (hashCount n * n)) (digest : BitString (index.val + 1))
    (query : BitString n) :
    c * ((encPair encUnary encBits (n, wordObservation image index.val (List.ofFn matrix)
      (List.ofFn digest) (List.ofFn query))).length + 1) ^ d ≤
        coinBudget c d n image.length :=
  observation_coinBudget_le c d n image index matrix digest query

-- Dot notation works outside the construction namespace, with an empty hash prefix.
example (precision : ℕ) (hp : 0 < precision) :
    (∑ x : BitString 1, (PMF.uniformOfFintype (BitString 1) x).toReal *
      (2 * GoldreichLevin.agreement (fun _ => false) x - 1)) ≤
      1 / (precision : ℝ) + 2 * Real.sqrt (1 * collisionProbability
        (PMF.uniformOfFintype (BitString 1))) +
      2 * (((guessInverter (fun _ : BitString 1 => ())
        (fun _ : Unit => fun _ : BitString 0 × Unit => fun _ => false)
        (PMF.pure ()) precision ()).map (fun _ => true)) true).toReal := by
  have hhash : IsTwoUniversal (PMF.pure ())
      (fun _ : Unit => fun _ : BitString 1 => (0 : BitString 0)) := by
    intro x y hxy
    simp
  simpa using hhash.correlation_le_guessInverter (hash := fun _ _ => (0, ()))
    (fun _ : BitString 1 => ()) ()
    (PMF.uniformOfFintype (BitString 1)) (by intros; rfl)
    (fun _ : Unit => fun _ : BitString 0 × Unit => fun _ => false) precision hp

end ComplexityTests.HashedParity
