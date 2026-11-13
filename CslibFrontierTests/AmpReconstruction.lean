/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmpDecode
import CslibFrontier.MachineLearning.UniformLearning.Reduction

/-! Checks of pieces of the amplification reconstruction of Carmosino, Impagliazzo, Kabanets and
Kolokolova: Goldreich–Levin decoding of `glAmp` (Claim 4.4) on concrete parameters, the circuit
size of the decoded candidates, and black-box reductions between membership-query learners. -/

namespace CslibFrontierTests.AmpReconstruction

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MachineLearning
  Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.UniformLearning.QueryLearner Finset

/-! ### Goldreich–Levin decoding of `glAmp` -/

/-- With the true guess, the candidate for the amplified parity recovers the parities `0` and `1`
of the blocks `11` and `10`, for any single mask. -/
example (masks : Fin 1 → BitString 2) :
    glAmpCandidate (glAmp (parity 2) 2) masks
        (fun j => (fun i => parity 2 (![![true, true], ![true, false]] i)) ⬝ᵥ masks j)
        ![![true, true], ![true, false]] =
      ![false, true] := by
  rw [glAmpCandidate_glAmp _ (by norm_num)]
  decide

/-- Claim 4.4 for the exact predictor with `γ = 1/2` and one block: `K = 4` masks satisfy the
size condition `1 ≤ 2 (γ/2)² (2⁴ - 1)`, so a `1/256` fraction of the masks and guesses decode
`f` on a `1/256` fraction of the inputs. -/
example {n : ℕ} (f : BooleanFunction n) :
    (1 / 2 : ℝ) / 2 ^ (4 + 3) ≤ (dens {mg : (Fin 4 → BitString 1) × BitString 4 |
      (1 / 2 : ℝ) / 2 ^ (4 + 3) * 2 ^ (1 * n) ≤
        #{y : Fin 1 → BitString n | ∀ i, glAmpCandidate (glAmp f 1) mg.1 mg.2 y i = f (y i)}} :
      ℝ) :=
  dens_filter_glAmpCandidate_agree f (glAmp f 1) (by norm_num)
    (by simp [BitString]; norm_num) (by norm_num) (by norm_num)

/-- With one mask, each output bit of the candidate costs `s + 11` gates over a predictor of
size `s`: two constants, one copy of the predictor with a negation, and a majority of one vote. -/
example {k n s : ℕ} {h : BooleanFunction (k * n + k)}
    (hh : complexity interpretation (single h) ≤ s) (masks : Fin 1 → BitString k)
    (guess : BitString 1) (j : Fin k) :
    complexity interpretation
        (single fun x : BitString (k * n) => glAmpCandidate h masks guess (BitString.block x) j) ≤
      s + 11 :=
  (complexity_glAmpCandidate_apply_le hh masks guess j).trans_eq (by norm_num)

/-- The same bound when the predictor is computed from `q` answer bits and its input, and the
candidate reads the answer bits as inputs too. -/
example {k n q s : ℕ} {F : BooleanFunction (q + (k * n + k))}
    (hF : complexity interpretation (single F) ≤ s) (masks : Fin 1 → BitString k)
    (guess : BitString 1) (j : Fin k) :
    complexity interpretation (single fun wx : BitString (q + k * n) =>
      glAmpCandidate (fun y => F (Fin.append (fun i => wx (Fin.castAdd (k * n) i)) y)) masks guess
        (BitString.block fun i => wx (Fin.natAdd q i)) j) ≤ s + 11 :=
  (complexity_glAmpCandidate_answers_apply_le hF masks guess j).trans_eq (by norm_num)

/-! ### Black-box reductions -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The query tree for `f y`: query `y` and output the answer. -/
def queryTree (y : ι → Bool) : DecisionTree (ι → Bool) Bool :=
  .node y (.leaf false) (.leaf true)

/-- The trivial reduction, which answers each query by asking it and keeps the hypothesis, has the
success probability of the learner. -/
example {Ω : Type*} {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε p : ℝ} (hA : A.Learns μ C ε (1 - p))
    (hp : p ≤ 1) :
    (reduce A queryTree fun h (_ : Unit) => h).Learns (reduceSeed μ Unit) C ε (1 - p * 1) := by
  refine learns_reduce (amp := id) (fun f _ y => ?_) (by simpa using hA) hp zero_le_one
    fun f _ h hh => ?_
  · cases hfy : f y <;> simp [queryTree, DecisionTree.eval, hfy]
  · have hh' : uniformError f h ≤ ε := hh
    simp [hh']

/-- The trivial reduction makes as many queries as the learner. -/
example {Ω : Type*} {A : QueryLearner ι Ω} {q : ℕ} (hA : A.QueriesAtMost q) :
    (reduce A queryTree fun h (_ : Unit) => h).QueriesAtMost (q * 1) :=
  queriesAtMost_reduce _ hA fun _ => by simp [queryTree, DecisionTree.depth]

end CslibFrontierTests.AmpReconstruction
