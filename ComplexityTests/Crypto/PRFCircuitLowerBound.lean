/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

import Complexity.Crypto.Computational.OneWayToPRF
import Complexity.Crypto.Computational.PseudorandomFunction.CircuitLowerBound
import Complexity.Crypto.Negligible.Basic

/-!
# Tests for the `2n - 2` `B₂`-circuit lower bound on pseudorandom functions

This file exercises the critical-path API (`Complexity/Computability/Circuit/CriticalPath.lean` and
`Complexity/Computability/Circuit/Boolean/CriticalPath.lean`) and the unconditional `2n - 2`
`B₂`-circuit lower bound for pseudorandom functions
(`Complexity/Crypto/Computational/PseudorandomFunction/CircuitLowerBound.lean`):

1. **Tightness of Lemma 7.4 at `2n - 2`**: an explicit `2`-gate `NoDeadGates` `B₂` circuit on `2`
   inputs with no isolated variables and disjoint critical paths of size `2 = 2 * 2 - 2`.
2. **Concrete completeness of both distinguishers**:
   * `isolatedVarDistinguisher` accepts `x ↦ x 0` on `BitString 2` with probability `1`;
   * `criticalPathDistinguisher` accepts `x ↦ x 0 ^^ x 1` on `BitString 2` (computed by a `1`-gate
     `NoDeadGates` circuit without isolated variables whose critical paths intersect at gate `0`)
     with probability `1`.
3. **Refuting an insecure candidate via Theorem 7.5**: the one-time-pad XOR family
   `key, query ↦ List.zipWith xor key query` has `B₂`-complexity at most `1` on its first output
   bit for every key, so `PseudorandomFunction.eventually_exists_key_two_mul_sub_two_le_complexity`
   rules out `PseudorandomFunction xorFamily`.
4. **Unconditional and conditional non-vacuity**:
   * `booleanPRF_uniform` verifies that `fun n => PMF.uniformOfFintype (BooleanFunction n)`
     satisfies `BooleanPRF` unconditionally, giving the `2 * n - 2` gate lower bound for random
     Boolean functions with no cryptographic assumption;
   * composing `OneWay.exists_pseudorandomFunction` with Theorem 7.5 yields a
     `PseudorandomFunction` family whose keys achieve `B₂`-complexity at least `2 * n - 2` with
     overwhelming probability under any uniform one-way function.
-/

namespace ComplexityTests.Crypto.PRFCircuitLowerBound

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto Cslib.Probability

/-! ### 1. Tightness of Lemma 7.4 (`2 * n - 2` gates at `n = 2`, `m = 1`) -/

/-- Binary AND operation in `fullSignature 2 Bool`. -/
def opAnd : (fullSignature 2 Bool).Op :=
  .fn fun v => v 0 && v 1

/-- Binary XOR operation in `fullSignature 2 Bool`. -/
def opXor : (fullSignature 2 Bool).Op :=
  .fn fun v => v 0 ^^ v 1

/-- Explicit `2`-gate `B₂` circuit on `2` inputs: gate `0` computes `x 0 && x 1`, gate `1`
computes `x 0 ^^ gate 0`, and output `0` reads `gate 1`. -/
abbrev tightCircuit : Circuit (fullSignature 2 Bool) 2 1 where
  program :=
    (Program.empty.gate ⟨opAnd, ![.input 0, .input 1]⟩).gate
      ⟨opXor, ![.input 0, .gate 0]⟩
  outputs := fun _ => .gate 1

example : tightCircuit.NoDeadGates := by decide
example : ¬ tightCircuit.HasIsolatedVar := by decide
example : tightCircuit.criticalPath 0 = [.input 0] := by decide
example : tightCircuit.criticalPath 1 = [.input 1, .gate 0, .gate 1] := by decide
example : Disjoint (tightCircuit.criticalPath 0).toFinset
    (tightCircuit.criticalPath 1).toFinset := by decide

/-- Lemma 7.4 is tight on `tightCircuit`: `2 * 2 - 2 * 1 = 2 = tightCircuit.size`. -/
theorem tightCircuit_attains_lower_bound :
    2 * 2 - 2 * 1 = tightCircuit.size ∧
      2 * 2 - 2 * 1 ≤ tightCircuit.size := by
  refine ⟨rfl, tightCircuit.two_mul_sub_two_mul_le_size (by decide) (by decide) (by decide) ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · decide
  · decide
  · exact absurd rfl hij

/-! ### 2. Concrete completeness of `isolatedVarDistinguisher` and `criticalPathDistinguisher` -/

/-- Two-input projection `x ↦ x 0`, leaving coordinate `1` isolated. -/
def proj0 (x : BitString 2) : Bool := x 0

/-- Wiring circuit on `2` inputs outputting `.input 0` (leaving `.input 1` isolated). -/
def proj0Circuit : Circuit (fullSignature 2 Bool) 2 1 :=
  Circuit.wiring (fullSignature 2 Bool) (fun _ => 0)

theorem proj0Circuit_hasIsolatedVar : proj0Circuit.HasIsolatedVar := by decide

theorem succProbability_isolatedVarDistinguisher_proj0 :
    Game.succProbability (evalBooleanOracle isolatedVarDistinguisher 2 proj0) = 1 := by
  refine succProbability_isolatedVarDistinguisher_of_hasIsolatedVar (by decide) ?_
    proj0Circuit_hasIsolatedVar
  rw [Circuit.computes_single_iff]
  intro x
  rfl

/-- Two-input parity `x ↦ x 0 ^^ x 1`. -/
def parity2 (x : BitString 2) : Bool := x 0 ^^ x 1

/-- Single-gate `NoDeadGates` `B₂` circuit computing `parity2`. -/
abbrev xorCircuit : Circuit (fullSignature 2 Bool) 2 1 where
  program := Program.empty.gate ⟨opXor, ![.input 0, .input 1]⟩
  outputs := fun _ => .gate 0

example : xorCircuit.NoDeadGates := by decide
example : ¬ xorCircuit.HasIsolatedVar := by decide
example : xorCircuit.criticalPath 0 = [.input 0, .gate 0] := by decide
example : xorCircuit.criticalPath 1 = [.input 1, .gate 0] := by decide

theorem succProbability_criticalPathDistinguisher_parity2 :
    Game.succProbability (evalBooleanOracle criticalPathDistinguisher 2 parity2) = 1 := by
  refine succProbability_criticalPathDistinguisher_of_not_disjoint_criticalPath
    (C := xorCircuit) (by decide) ?_ (by decide) ?_
  · rw [Circuit.computes_single_iff]
    intro x
    rfl
  · intro hpair
    have hd : Disjoint (xorCircuit.criticalPath 0).toFinset
        (xorCircuit.criticalPath 1).toFinset := hpair (by decide : (0 : Fin 2) ≠ 1)
    exact absurd hd (by decide)

/-! ### 3. Refuting one-time-pad XOR as a `PseudorandomFunction` via Theorem 7.5 -/

/-- Keyed bitwise XOR (`key, query ↦ List.zipWith xor key query`). -/
def xorFamily (key query : List Bool) : List Bool :=
  List.zipWith xor key query

/-- Every unary Boolean operation on `1` input is computed by a `1`-gate `B₂` circuit. -/
theorem complexity_unary_one_le_one (b : Bool) :
    complexity (fullInterpretation (k := 2)) (single fun y : BitString 1 => b ^^ y 0) ≤ 1 := by
  let c : Circuit (fullSignature 2 Bool) 1 1 :=
    { program := Program.empty.gate ⟨.fn fun v => b ^^ v 0, ![.input 0, .input 0]⟩
      outputs := fun _ => .gate 0 }
  have hc : c.Computes (fullInterpretation (k := 2)) (single fun y : BitString 1 => b ^^ y 0) := by
    rw [Circuit.computes_single_iff]
    intro y
    rfl
  exact complexity_le_of_computes c hc

/-- For `1 ≤ n` and any `key : BitString n`, the first-bit restriction of `xorFamily` has `B₂`
circuit complexity at most `1`. -/
theorem complexity_restriction_xorFamily_le_one {n : ℕ} (hn : 1 ≤ n) (key : BitString n) :
    complexity (fullInterpretation (k := 2))
      (single (KabanetsCai.restriction (xorFamily (List.ofFn key)) n n)) ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hrestr : KabanetsCai.restriction (xorFamily (List.ofFn key)) (m + 1) (m + 1) =
      fun z : BitString (m + 1) => key 0 ^^ z 0 := by
    funext z
    simp [KabanetsCai.restriction, xorFamily, List.ofFn_succ]
  rw [hrestr]
  have hle := complexity_single_unary_le (I := fullInterpretation (k := 2))
    (fun bit => key 0 ^^ bit) (fun z : BitString (m + 1) => z 0)
  rw [complexity_single_proj, Nat.zero_add] at hle
  exact hle.trans (complexity_unary_one_le_one (key 0))

/-- Theorem 7.5 refutes `PseudorandomFunction xorFamily`: every key has `B₂`-circuit complexity
at most `1 < 2 * n - 2` for `n ≥ 3`. -/
theorem not_pseudorandomFunction_xorFamily : ¬ PseudorandomFunction xorFamily := by
  intro hprf
  have hev := hprf.eventually_exists_key_two_mul_sub_two_le_complexity.and
    (Filter.eventually_ge_atTop 3)
  obtain ⟨n, ⟨key, hlow⟩, hn3⟩ := hev.exists
  have hup := complexity_restriction_xorFamily_le_one (by omega : 1 ≤ n) key
  omega

/-! ### 4. Unconditional `BooleanPRF` instance and conditional `OneWay` instance -/

/-- Because `BooleanPRF` imposes no efficient sampling or evaluation condition, the uniform random
Boolean function ensemble satisfies it unconditionally. -/
theorem booleanPRF_uniform : BooleanPRF (fun n => PMF.uniformOfFintype (BooleanFunction n)) := by
  intro adversary _
  simp only [booleanPRFRealGame, booleanPRFIdealGame, Game.advantage_self]
  exact negligible_zero

/-- Unconditional consequence of Theorem 7.5 on `booleanPRF_uniform`: a uniformly random `n`-bit
Boolean function has `B₂`-circuit complexity below `2 * n - 2` with negligible probability. -/
theorem negligible_uniform_complexity_lt_two_mul_sub_two :
    Negligible (fun n =>
      ((PMF.uniformOfFintype (BooleanFunction n)).map (fun f =>
        decide (complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2))
        true).toNNReal) :=
  booleanPRF_uniform.negligible_complexity_lt_two_mul_sub_two

/-- Any uniform `OneWay` function yields a `PseudorandomFunction` family satisfying both forms of
Fan–Li–Yang Theorem 7.5. -/
theorem exists_prf_with_two_mul_sub_two_lower_bound_of_oneWay {f : List Bool → List Bool}
    (hf : OneWay f) :
    ∃ family : List Bool → List Bool → List Bool,
      PseudorandomFunction family ∧
      Negligible (fun n =>
        ((BitString.uniformList n).map (fun key =>
          decide (complexity (fullInterpretation (k := 2))
            (fun x : BitString n => BitString.ofList n (family key (List.ofFn x))) <
              2 * n - 2)) true).toNNReal) ∧
      (∀ᶠ n in Filter.atTop,
        ∃ key : BitString n,
          2 * n - 2 ≤ complexity (fullInterpretation (k := 2))
            (single (KabanetsCai.restriction (family (List.ofFn key)) n n))) := by
  obtain ⟨family, hF⟩ := hf.exists_pseudorandomFunction
  exact ⟨family, hF, hF.negligible_complexity_lt_two_mul_sub_two,
    hF.eventually_exists_key_two_mul_sub_two_le_complexity⟩

end ComplexityTests.Crypto.PRFCircuitLowerBound
