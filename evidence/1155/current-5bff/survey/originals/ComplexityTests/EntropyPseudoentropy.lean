/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Basic
import Complexity.Tactic.PPT

/-! Finite entropy, dependent alphabets and nonvacuous pseudoentropy sampler contracts. -/

namespace ComplexityTests.EntropyPseudoentropy

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto Cslib.Crypto.Pseudoentropy
open Turing.MultiTapeTM

-- Null outcomes receive the documented totalized surprisal, not an infinite real value.
example : surprisal (PMF.pure false) true = 0 := by simp [surprisal]

-- Revealing the complete sampled bit leaves no conditional entropy.
example (p : PMF Bool) : conditionalEntropy (p.map (fun b => (b, b))) = 0 := by
  rw [conditionalEntropy, entropy_map_of_injective p (fun _ _ h => congrArg Prod.fst h)]
  rw [PMF.map_comp]
  change entropy p - entropy (p.map id) = 0
  rw [PMF.map_id, sub_self]

-- An independent hidden bit retains one bit of entropy.
example : conditionalEntropy ((uniformOfFintype Bool).bind
    (fun b => (uniformOfFintype Bool).map (b, ·))) = 1 := by
  rw [conditionalEntropy_bind_pair]
  simp

private noncomputable def branch : (b : Bool) → PMF (Fin (if b then 2 else 1))
  | false => uniformOfFintype (Fin 1)
  | true => uniformOfFintype (Fin 2)

-- One fair branch bit plus average remaining entropy (0 + 1)/2.
example : entropy ((uniformOfFintype Bool).bind
    (fun b => (branch b).map (Sigma.mk b))) = 3 / 2 := by
  rw [entropy_bind_sigma]
  simp only [Fintype.sum_bool, branch]
  rw [entropy_uniform, entropy_uniform (α := Fin 2), entropy_uniform (α := Fin 1)]
  norm_num [PMF.uniformOfFintype_apply]

private noncomputable def deterministicPair : SamplablePair where
  Observation _ := Unit
  finite _ := inferInstance
  encode _ := ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := PMF.pure ((), false)
  sample _ := pure ([], false)
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_pure, PMF.pure_map]
    rfl

-- The interface has a concrete instance, and zero gap does not assert unpredictability.
example : deterministicPair.HasGap (fun _ => 0) := by
  intro adversary _
  apply Filter.Eventually.of_forall
  intro n
  change _ ≤ 1 - conditionalEntropy (PMF.pure ((), false)) - 0
  norm_num [conditionalEntropy]
  exact Game.succProbability_le_one _

-- A completely predictable pair cannot be assigned a positive prediction gap.
example : ¬ deterministicPair.HasGap (fun _ => 1 / 10) := by
  intro hgap
  have h := hgap (fun _ _ => pure false) (by ppt)
  obtain ⟨n, hn⟩ := h.exists
  change _ ≤ 1 - conditionalEntropy (PMF.pure ((), false)) - 1 / 10 at hn
  norm_num [deterministicPair, predictionGame, conditionalEntropy, Game.succProbability] at hn

example {sample : ℕ → ProbComp (List Bool × Bool)}
    (hsample : IsPPTOn encUnary (encPair encBits encBool) sample) {adversary : Distinguisher}
    (hadversary : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (predictionGame sample adversary) := by ppt

-- The same functional program also works as an explicit sequence of binds.
example {sample : ℕ → ProbComp (List Bool × Bool)}
    (hsample : IsPPTOn encUnary (encPair encBits encBool) sample) {adversary : Distinguisher}
    (hadversary : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (fun n => sample n >>= fun pair =>
      adversary n pair.1 >>= fun guess => pure (guess == pair.2)) := by ppt

end ComplexityTests.EntropyPseudoentropy
