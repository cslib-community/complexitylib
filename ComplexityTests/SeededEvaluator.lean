/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PPT

/-! Typed saved-coin evaluation, arbitrary seeds, and one shared tape for distinct inputs. -/

namespace ComplexityTests.SeededEvaluator

open Cslib Cslib.Probability Turing.MultiTapeTM

private noncomputable def markedSample (n : ℕ) : ProbComp (List Bool) := do
  let word ← BitString.sampleList n
  return true :: word

-- A nontrivial support invariant survives every supplied seed, including the empty seed.
example : ∃ evaluate : ℕ → List Bool → List Bool,
    ComputableInPolyTime (fun p : ℕ × List Bool => evaluate p.1 p.2)
      (encPair encUnary encBits) encBits ∧
    ∀ n coins, (evaluate n coins).length = n + 1 ∧ (evaluate n coins).headD false = true := by
  have hp : IsPPTOn encUnary encBits markedSample := by unfold markedSample; ppt
  obtain ⟨_, _, evaluate, hefficient, hsupported, _⟩ := hp.exists_total_seeded_evaluator
  refine ⟨evaluate, .of_tidy hefficient, fun n coins => ?_⟩
  have hs := hsupported n coins
  simp only [markedSample, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure] at hs
  obtain ⟨word, hw, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  rw [← heq]
  simp [BitString.length_of_mem_support_uniformList hw]

-- A unary output encoding is not a decoder for arbitrary words. The evaluator still returns
-- a valid natural number on every seed, and preserves the entire distribution for longer seeds.
example : ∃ (c d : ℕ) (evaluate : ℕ → List Bool → ℕ),
    ComputableInPolyTime (fun p : ℕ × List Bool => evaluate p.1 p.2)
      (encPair encUnary encBits) encUnary ∧
    (∀ n coins, evaluate n coins = n ∨ evaluate n coins = n + 1) ∧
    ∀ n extra, ProbComp.eval (do
      let bit ← ProbComp.uniform Bool
      return if bit then n else n + 1) =
        (BitString.uniformList (c * (n + 1) ^ d + extra)).map (evaluate n) := by
  let program (n : ℕ) : ProbComp ℕ := do
    let bit ← ProbComp.uniform Bool
    return if bit then n else n + 1
  have hp : IsPPTOn encUnary encUnary program := by dsimp only [program]; ppt
  obtain ⟨c, d, evaluate, hefficient, hsupported, hlaw⟩ := hp.exists_total_seeded_evaluator
  refine ⟨c, d, evaluate, .of_tidy hefficient, ?_, ?_⟩
  · intro n coins
    have hs := hsupported n coins
    simp only [program, ProbComp.eval_bind, ProbComp.eval_pure] at hs
    obtain ⟨bit, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    cases bit with
    | false => exact Or.inr heq.symm
    | true => exact Or.inl heq.symm
  · intro n extra
    simpa only [encUnary_apply, List.length_replicate] using
      hlaw n (c * (n + 1) ^ d + extra) (by simp)

-- The same efficient raw predictor can use a common tape for two different input lengths.
-- This asserts the two marginal laws; it does not assert independence when coins are reused.
example : ∃ (c d : ℕ) (evaluate : List Bool → List Bool → List Bool),
    ComputableInPolyTime (fun p : List Bool × List Bool => evaluate p.1 p.2)
      (encPair encBits encBits) encBits ∧
    ∀ (a b : List Bool) length,
      c * (a.length + 1) ^ d ≤ length → c * (b.length + 1) ^ d ≤ length →
      (BitString.uniformList length).map (fun coins => (evaluate coins a).headD false) =
        ProbComp.eval (ProbComp.uniform Bool) ∧
      (BitString.uniformList length).map (fun coins => (evaluate coins b).headD false) =
        ProbComp.eval (ProbComp.uniform Bool) := by
  obtain ⟨c, d, evaluate, hefficient, hlaw⟩ :=
    (isPPTOn_uniform_bool encBits).exists_padded_bool_coin_evaluator
  exact ⟨c, d, evaluate, .of_tidy hefficient, fun a b length ha hb =>
    ⟨(hlaw a length ha).symm, (hlaw b length hb).symm⟩⟩

end ComplexityTests.SeededEvaluator
