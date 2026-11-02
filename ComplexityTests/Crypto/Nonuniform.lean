/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Nonuniform.ZeroKnowledge
import Complexity.Crypto.Computational.Stretch
import Complexity.Crypto.Computational.Pseudoentropy.OneWay
import Complexity.Crypto.Computational.Pseudoentropy.LabelExtraction
import Complexity.Languages.Probabilistic.Notation

/-! Checked clients of the nonuniform security notions. Existence of a nonuniform one-way
function or generator is open, so these checks show that the notions are not trivially true
(constant functions, fixed words and length-wise constant generators fail them) and that the
indistinguishability notion is not trivially false. They do not separate the nonuniform notions
from the uniform ones. -/

namespace ComplexityTests.Crypto.Nonuniform

open Cslib Cslib.Crypto Probability

/-- A constant function is not nonuniformly one-way, because it is not even uniformly one-way. -/
example (word : List Bool) : ¬ NonuniformOneWay (fun _ => word) :=
  fun h => not_oneWay_const word h.toOneWay

/-- Inverting a constant function is not hard even with empty advice: by
`oneWay_iff_inversionHardWithAdvice_nil` that would make it uniformly one-way. -/
example (word : List Bool) : ¬ InversionHardWithAdvice (fun _ => word) (fun _ => []) :=
  fun h => not_oneWay_const word (oneWay_iff_inversionHardWithAdvice_nil.mpr
    ⟨Turing.MultiTapeTM.ComputableInPolyTime.const word, h⟩)

/-- The nonuniform indistinguishability relation holds between equal ensembles. -/
example : NonuniformlyIndistinguishable (fun n => BitString.uniformList n)
    (fun n => BitString.uniformList n) :=
  NonuniformlyIndistinguishable.refl _

/-- The all-`true` words are distinguishable from uniform words of each positive length. -/
example : ¬ NonuniformlyIndistinguishable (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) :=
  not_nonuniformlyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)

/-- A generator that, at each seed length, outputs one fixed word of the right length is not a
nonuniform PRG (nor a uniform one): its output's first bit is constant. -/
example : ¬ NonuniformPRG (fun seed => List.replicate (seed.length + 1) false) (· + 1) := by
  intro h
  refine not_nonuniformlyIndistinguishable_pure_uniformList (fun n => List.replicate (n + 1) false)
    (.of_forall fun n => Nat.le_add_left 1 n) ?_
  have hensemble :
      generatorEnsemble (fun seed => List.replicate (seed.length + 1) false) =
        fun n => PMF.pure (List.replicate (n + 1) false) := by
    funext n
    rw [generatorEnsemble_postprocess (fun _ => []) (fun n _ => List.replicate (n + 1) false)]
    simp only [generatorEnsemble, PMF.map_comp]
    exact PMF.map_const _ _
  have hsecure := h.secure
  rw [hensemble] at hsecure
  exact hsecure

/-- The nonuniform generator premise gives the GMW advice premise for CNF instances. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) :
    GMW.AdvicePRG Complexity.encCNF generator length :=
  h.advicePRG _

/-- With empty advice, indistinguishability with advice is uniform indistinguishability, so the
uniform first-bit separation transfers. -/
example : ¬ IndistinguishableWithAdvice (fun _ => []) (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) := fun h =>
  not_computationallyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)
    (computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr h)

/-- Stretching a nonuniform one-bit PRG to `3 * n + 1` bits, the GMW length, and feeding it to the
auxiliary-input GMW theorem. -/
example {generator : List Bool → List Bool} (h : NonuniformPRG generator (fun n => n + 1))
    {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ Complexity.NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge :=
  (h.amplify (fun n => 3 * n + 1) (by fun_prop) (fun n => by omega))
    |>.exists_auxiliaryInputZeroKnowledge_of_mem_NP (fun _ => le_rfl) hA

/-- A pair with a prediction gap against predictors given any advice family satisfies the
fair-coin bound directly via `HasGapWithAdvice.eventually_entropy_add_gap_le_one`. -/
example {pair : Pseudoentropy.SamplablePair} {gap : ℕ → ℝ} {advice : ℕ → List Bool}
    (h : pair.HasGapWithAdvice gap advice) :
    ∀ᶠ n in Filter.atTop, Probability.PMF.conditionalEntropy (pair.joint n) + gap n ≤ 1 :=
  h.eventually_entropy_add_gap_le_one

/-- Every advised sequence test eventually admits a dense soft mask with small distinguishing
advantage under `HasGapWithAdvice`. -/
example {pair : Pseudoentropy.SamplablePair} {gap : ℕ → ℝ} {advice : ℕ → List Bool}
    (h : pair.HasGapWithAdvice gap advice)
    (test : ℕ × List Bool → List (List Bool × Bool) → ProbComp Bool)
    (htest : Probability.IsPPTOn
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)
        (Turing.MultiTapeTM.encList
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool)))
      Turing.MultiTapeTM.encBool (fun input => test input.1 input.2)) :
    ∀ᶠ n in Filter.atTop, 0 < 1 → 1 ≤ dyadicSize 1 →
      ((1 : ℕ) : ℝ) / dyadicSize 1 ≤ Probability.PMF.conditionalEntropy (pair.joint n) + gap n →
      ∃ mask : pair.Observation n × Bool → ProbComp Bool,
        ((1 : ℕ) : ℝ) / dyadicSize 1 ≤ Pr[pair.latentSample n >>= mask] ∧
        (∀ value, 0 < Pr[mask value] →
          1 / (dyadicSize (2 * 1 * dyadicSize 1) : ℝ) ≤ Pr[mask value]) ∧
        (Game.advantage
          (ProbComp.eval (OracleComp.replicate 1 (pair.sample n) >>= test (n, advice n)))
          (ProbComp.eval (OracleComp.replicate 1
            (Pseudoentropy.maskedSample (pair.latentSample n)
              (fun value => pair.encode n value.1) Prod.snd mask) >>=
                test (n, advice n))) : ℝ) < (dyadicSize 1 : ℝ) / (1 : ℕ) :=
  h.eventually_exists_mask test htest
    (count := fun _ => 1) (numerator := fun _ => 1) (densityBound := fun _ => 1)
    (inverseGap := fun _ => 1)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => Nat.one_pos)

end ComplexityTests.Crypto.Nonuniform
