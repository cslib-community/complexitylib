/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.Sampling

/-! Output patterns: exact coin and Bell probabilities, destructive interference, invalid
patterns, and terminal NOTs that preserve untouched wires. -/

namespace ComplexityTests.QuantumOutput

open Cslib Cslib.Quantum Cslib.Complexity.QuantumContraction

-- Distinct NOT gates flip exactly their wires, including nonconsecutive wire numbers.
example : List.ofFn (GateCode.classicalRun (GateCode.flipCodes [3, 0])
    (inputState 5 [false, true, false, true, true])) = [true, true, false, false, true] := by
  decide

-- Contradictory requirements on the same wire cannot be met.
example : patternAt 1 [(0, false), (0, true)] = ∅ := by
  ext y
  constructor
  · intro hy
    have h := mem_patternAt.mp hy
    have hf := (h (0, false) (by simp)).2
    have ht := (h (0, true) (by simp)).2
    have : false = true := hf.symm.trans ht
    contradiction
  · intro hy
    simp at hy

example : ¬(patternWires [(0, false), (0, true)]).Nodup := by decide

/-- A single Hadamard gives either bit with probability exactly one half. -/
theorem coin_pattern (b : Bool) :
    patternProb 1 [(true, 0, [])] [(0, b)] [false] = 1 / 2 := by
  have hgap : onesGap (patternWires [(0, b)])
      ([(true, 0, [])] ++ GateCode.flipCodes (patternZeros [(0, b)])) [false] = 1 := by
    cases b <;> decide
  rw [patternProb_eq_onesGap _ (by decide) (by simp [patternWires]) (by simp),
    show List.ofFn (inputState 1 [false]) = [false] by decide, hgap]
  norm_num [hadamardCount]

-- The pattern event is the actual marginal measurement law, including the zero outcome.
example : ((Circuit.measure (Circuit.ofCodes 1 [(true, 0, [])]) (inputState 1 [false])).map
    (fun y => [0].map (readBit y))) [false] = 1 / 2 := by
  rw [measure_map_readBit_apply _ _ (by decide) (by decide)]
  change ENNReal.ofReal (patternProb 1 [(true, 0, [])] [(0, false)] [false]) = _
  rw [coin_pattern, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The Bell circuit applies Hadamard to wire zero, then copies it to wire one. -/
def bellCodes : List GateCode := [(true, 0, []), (false, 1, [0])]

/-- All four joint probabilities of the Bell circuit. The mixed outcomes have zero mass. -/
theorem bell_pattern (a b : Bool) :
    patternProb 2 bellCodes [(0, a), (1, b)] [false, false] =
      if a = b then 1 / 2 else 0 := by
  have hgap : onesGap (patternWires [(0, a), (1, b)])
      (bellCodes ++ GateCode.flipCodes (patternZeros [(0, a), (1, b)])) [false, false] =
        if a = b then 1 else 0 := by
    cases a <;> cases b <;> decide
  rw [patternProb_eq_onesGap _ (by decide) (by simp [patternWires]) (by simp),
    show List.ofFn (inputState 2 [false, false]) = [false, false] by decide, hgap]
  by_cases h : a = b <;> simp [h, bellCodes, hadamardCount]

-- Two Hadamards destructively interfere: the output zero has mass one.
theorem twice_pattern_false :
    patternProb 1 [(true, 0, []), (true, 0, [])] [(0, false)] [false] = 1 := by
  rw [patternProb_eq_onesGap _ (by decide) (by decide) (by decide),
    show List.ofFn (inputState 1 [false]) = [false] by decide,
    show onesGap (patternWires [(0, false)])
      ([(true, 0, []), (true, 0, [])] ++ GateCode.flipCodes (patternZeros [(0, false)]))
        [false] = 4 by decide]
  norm_num [hadamardCount]

-- The zero-gate, zero-width case is still a normalized measurement.
example : patternProb 0 [] [] [] = 1 := by simp

-- An untouched wire nineteen remains true while wire zero is sampled fairly.
example : patternProb 20 [(true, 0, [])] [(0, false), (19, true)]
    (List.replicate 19 false ++ [true]) = 1 / 2 := by
  rw [patternProb_eq_onesGap _ (by decide) (by decide) (by decide),
    show List.ofFn (inputState 20 (List.replicate 19 false ++ [true])) =
      List.replicate 19 false ++ [true] by decide,
    show onesGap (patternWires [(0, false), (19, true)])
      ([(true, 0, [])] ++ GateCode.flipCodes (patternZeros [(0, false), (19, true)]))
        (List.replicate 19 false ++ [true]) = 1 by decide]
  norm_num [hadamardCount]

/-! ### The actual sampling program -/

private theorem sampleOutput_apply {gs : List GateCode} {X word : List Bool}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) (hlen : word.length = X.length) :
    ProbComp.eval (sampleOutput gs X) word =
      ENNReal.ofReal (patternProb X.length gs ((List.range X.length).zip word) X) := by
  have hread (y : Fin X.length → Bool) :
      (List.range X.length).map (readBit y) = List.ofFn y := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact readBit_of_lt y (by simpa using hj')
  rw [eval_sampleOutput hgs]
  have h := measure_map_readBit_apply gs X (S := List.range X.length) (bs := word)
    (fun j hj => List.mem_range.mp hj) (by simpa using hlen)
  simpa only [hread] using h

-- Both actual output probabilities of the single-Hadamard sampler.
example (b : Bool) :
    ProbComp.eval (sampleOutput [(true, 0, [])] [false]) [b] = 1 / 2 := by
  rw [sampleOutput_apply (X := [false]) (word := [b]) (by decide) rfl]
  change ENNReal.ofReal (patternProb 1 [(true, 0, [])] [(0, b)] [false]) = _
  rw [coin_pattern, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

-- The sampler preserves the Bell correlation: it produces 00 and 11, never 01 or 10.
example (a b : Bool) :
    ProbComp.eval (sampleOutput bellCodes [false, false]) [a, b] =
      if a = b then 1 / 2 else 0 := by
  rw [sampleOutput_apply (X := [false, false]) (word := [a, b]) (by decide) rfl]
  change ENNReal.ofReal (patternProb 2 bellCodes [(0, a), (1, b)] [false, false]) = _
  rw [bell_pattern]
  by_cases h : a = b
  · simp only [h, ite_true]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · simp [h]

-- Although the program draws two seed bits, interference makes its output deterministic.
example : ProbComp.eval (sampleOutput [(true, 0, []), (true, 0, [])] [false]) [false] = 1 := by
  rw [sampleOutput_apply (by decide) rfl]
  change ENNReal.ofReal (patternProb 1 [(true, 0, []), (true, 0, [])] [(0, false)] [false]) = _
  rw [twice_pattern_false]
  simp

-- No gates means no sampled bits, and the complete input register is returned.
example : ProbComp.eval (sampleOutput [] [false, true, false]) =
    PMF.pure [false, true, false] := by
  simp [sampleOutput, hadamardCount, BitString.sampleList]

example : decodeOutput [] [false, true, false] [] = [false, true, false] := by simp

-- One target among twenty wires: the full output, including untouched true wire nineteen,
-- has the expected half probability.
example : ProbComp.eval (sampleOutput [(true, 0, [])] (List.replicate 19 false ++ [true]))
    (List.replicate 19 false ++ [true]) = 1 / 2 := by
  rw [sampleOutput_apply (by decide) rfl]
  have hpattern : patternProb 20 [(true, 0, [])]
      ((List.range 20).zip (List.replicate 19 false ++ [true]))
      (List.replicate 19 false ++ [true]) = 1 / 2 := by
    rw [patternProb_eq_onesGap _ (by decide) (by decide) (by decide),
      show List.ofFn (inputState 20 (List.replicate 19 false ++ [true])) =
        List.replicate 19 false ++ [true] by decide,
      show onesGap (patternWires ((List.range 20).zip (List.replicate 19 false ++ [true])))
        ([(true, 0, [])] ++ GateCode.flipCodes
          (patternZeros ((List.range 20).zip (List.replicate 19 false ++ [true]))))
            (List.replicate 19 false ++ [true]) = 1 by decide]
    norm_num [hadamardCount]
  change ENNReal.ofReal (patternProb 20 [(true, 0, [])]
    ((List.range 20).zip (List.replicate 19 false ++ [true]))
    (List.replicate 19 false ++ [true])) = _
  rw [hpattern, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end ComplexityTests.QuantumOutput
