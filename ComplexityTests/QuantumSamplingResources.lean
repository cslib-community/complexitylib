/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.Sampling.Seeded

/-! A runtime family with `n` Hadamards: variable gate count, exactly `n` seed bits, and native
decoder bounds in the original unary input length rather than the enlarged input/seed pair. -/

namespace ComplexityTests.QuantumSamplingResources

open Cslib Cslib.Quantum Cslib.BitString Cslib.Complexity.QuantumContraction
open Turing.MultiTapeTM

private def repeatedH (n : ℕ) : List GateCode := List.replicate n (true, 0, [])

private theorem repeatedH_polyTime :
    ComputableInPolyTime repeatedH encUnary (encList encGateCode) := by
  unfold repeatedH
  fun_prop

private theorem repeatedH_wellFormed (n : ℕ) :
    ∀ g ∈ repeatedH n, g.WellFormed ([false] : List Bool).length := by
  intro g hg
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hg
  decide

private theorem length_repeatedH (n : ℕ) : (repeatedH n).length = n := by
  simp [repeatedH]

private theorem hadamardCount_repeatedH (n : ℕ) : hadamardCount (repeatedH n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [repeatedH, List.replicate_succ, hadamardCount_cons_true] using
      congrArg (fun x => x + 1) ih

-- The certified native seed generator is uniform for an unbounded runtime seed length.
example : Probability.IsPPTOn encUnary encBits (fun n => sampleList n) := by
  simpa only [hadamardCount_repeatedH] using isPPTOn_outputSeed repeatedH_polyTime

-- All valid seeds have the runtime number of bits; no fixed-seed or fixed-circuit premise is used.
example (p : SeededInput repeatedH) : p.seed.length = p.input := by
  simpa only [hadamardCount_repeatedH] using p.seed_length

-- Pair framing and the n-bit seed enlarge the physical input from n bits to exactly 3n+1 bits.
example (p : SeededInput repeatedH) :
    (SeededInput.encoding encUnary repeatedH p).length = 3 * p.input + 1 := by
  rw [SeededInput.length_encoding, hadamardCount_repeatedH, encUnary_apply, List.length_replicate]
  omega

-- The resource theorem nevertheless charges the original n, uniformly over every n-bit seed.
example : ∃ A e : ℕ, ComputableInO
    (fun p : SeededInput repeatedH => decodeOutput (repeatedH p.input) [false] p.seed)
    (SeededInput.encoding encUnary repeatedH) encBits
    (fun p => 2 ^ (A * (p.input + 1) / Nat.sqrt (Nat.log 2 (p.input + 2))) *
      (p.input + 1) ^ e)
    (fun p => (p.input + 1) ^ e) := by
  have h := exists_computableInO_decodeOutput_seeded repeatedH_polyTime
    (ComputableInPolyTime.const [false]) repeatedH_wellFormed
  simpa only [length_repeatedH, encUnary_apply, List.length_replicate] using h

-- Concrete seeds witness nonempty domains both without Hadamards and with several Hadamards.
private def zeroSeed : SeededInput repeatedH := ⟨(0, []), rfl⟩
private def threeSeed : SeededInput repeatedH := ⟨(3, [false, true, false]), by decide⟩

example : (SeededInput.encoding encUnary repeatedH zeroSeed).length = 1 := by decide
example : (SeededInput.encoding encUnary repeatedH threeSeed).length = 10 := by decide
example : decodeOutput (repeatedH zeroSeed.input) [false] zeroSeed.seed = [false] := by
  change decodeOutput [] [false] [] = [false]
  simp

end ComplexityTests.QuantumSamplingResources
