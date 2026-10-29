/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CircuitCounting
import Complexity.Computability.Complexity.FineGrained.CountingScaleBounds

/-!
# Tests for `#Circuit-SAT` frontier compilation and subexponential counting

Exercises `Complexity.Computability.Circuit.Frontier.Compiler.CNF`,
`Complexity.Computability.Complexity.FineGrained.CountingScaleBounds`, and
`Complexity.Computability.Complexity.FineGrained.CircuitCounting` on concrete circuits:

1. A 3-ary non-De-Morgan Boolean signature (`constTrue`, `maj3`, `xor3`, `mux`) on `n = 5` inputs
   with fan-out `> 1`, an unreachable internal gate reading two otherwise-unread inputs, and
   `satFreeShift = 2`, checking `numVars = 4 ≤ 3 * 2 + 1`, clause widths `≤ 4`, `modelCount = 4`,
   and `satCount = 2 ^ 2 * 4 = 16` by kernel reduction (`decide`), plus a 3-gate `mux`-of-`maj3`
   circuit with `fan-out = 2` on inputs `0` and `2`.
2. Edge cases: zero-gate pure wiring (`size = 0`, `n = 4`), zero-input constant circuit (`n = 0`),
   unsatisfiable De Morgan circuit (`satCount = 0`), and a 2-output circuit combining an unread
   input with an unconstrained output wire (`acc 1 = fun _ => true`).
3. Nonvacuous instantiations of `exists_circuitSatCounter`, `exists_booleanCircuitSatCounter`,
   `exists_linearSizeBooleanCircuitSatCounter`, `decidableInSubexpTime_CircuitSAT_size`, and
   `decidableInSubexpTime_linearSizeCircuitSAT`.
-/

@[expose] public section

namespace ComplexityTests.CircuitCounting

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Complexity
open Cslib.Complexity.CircuitCounting Cslib.Complexity.SubexponentialSAT
open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Custom 3-ary Boolean signature -/

/-- A 4-operation Boolean basis with arity up to `3`: constant `true`, ternary majority, ternary
parity, and a multiplexer `if x 0 then x 1 else x 2`. -/
inductive TernaryOp where
  | constTrue
  | maj3
  | xor3
  | mux
  deriving DecidableEq

instance : Fintype TernaryOp :=
  ⟨{.constTrue, .maj3, .xor3, .mux}, by rintro (_ | _ | _ | _) <;> decide⟩

/-- Signature of `TernaryOp`. -/
abbrev ternarySig : Signature where
  Op := TernaryOp
  Arity
    | .constTrue => 0
    | .maj3 | .xor3 | .mux => 3

/-- Boolean interpretation of `TernaryOp`. -/
def ternaryInterp : Interpretation ternarySig Bool
  | .constTrue, _ => true
  | .maj3, x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
  | .xor3, x => xor (xor (x 0) (x 1)) (x 2)
  | .mux, x => if x 0 then x 1 else x 2

/-- Fixed 2-bit injection `TernaryOp ↪ List Bool`. -/
private def encTernaryOp : TernaryOp ↪ List Bool where
  toFun
    | .constTrue => [false, false]
    | .maj3 => [false, true]
    | .xor3 => [true, false]
    | .mux => [true, true]
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp at h <;> rfl

/-- Concrete 5-input, 2-gate circuit over `ternarySig`:
* Gate `0` (wire `5`, output): `maj3(x₀, x₁, x₂)`
* Gate `1` (wire `6`, unreachable!): `xor3(x₀, x₃, x₄)` (input `0` has fan-out `2` in the raw DAG,
  while inputs `3` and `4` are read only by this dead gate). -/
private def sampleTernaryCircuit : Circuit ternarySig 5 1 :=
  ⟨(Program.empty.gate ⟨TernaryOp.maj3, ![Wire.input 0, Wire.input 1, Wire.input 2]⟩).gate
      ⟨TernaryOp.xor3, ![Wire.input 0, Wire.input 3, Wire.input 4]⟩,
    fun _ => Wire.gate 0⟩

private theorem sampleTernaryCircuit_fanIn : sampleTernaryCircuit.FanInAtMost 3 := by
  decide

/-- Multi-gate fan-out check on `n = 3` inputs: Gate `0` (`maj3(x₀, x₁, x₂)`) feeds Gate `1`
(`mux(gate₀, x₀, x₁)`), giving `x₀` and `x₁` reachable fan-out `2`. -/
private def fanOutMuxCircuit : Circuit ternarySig 3 1 :=
  ⟨(Program.empty.gate ⟨TernaryOp.maj3, ![Wire.input 0, Wire.input 1, Wire.input 2]⟩).gate
      ⟨TernaryOp.mux, ![Wire.gate 0, Wire.input 0, Wire.input 1]⟩,
    fun _ => Wire.gate 1⟩

/-- Dead gate `1` (wire `6`) and its exclusively-read inputs `3, 4` are pruned from `toCSP` and
`toSatCNF`, leaving `2` CSP constraints (`1` reachable gate + `1` output) on the `4` reachable
wires `{0, 1, 2, 5}`; both `sampleTernaryCircuit` and `fanOutMuxCircuit` satisfy
`satCount_eq_two_pow_satFreeShift_mul_modelCount`. -/
example :
    sampleTernaryCircuit.size = 2 ∧
      (Compiler.toCSP sampleTernaryCircuit).length = 2 ∧
      (Compiler.toSatCNF sampleTernaryCircuit ternaryInterp).numVars = 4 ∧
      (∀ cl ∈ Compiler.toSatCNF sampleTernaryCircuit ternaryInterp, cl.length ≤ 4) ∧
      Compiler.satFreeShift sampleTernaryCircuit ternaryInterp = 2 ∧
      (Compiler.toSatCNF sampleTernaryCircuit ternaryInterp).modelCount = 4 ∧
      sampleTernaryCircuit.satCount ternaryInterp = 16 ∧
      sampleTernaryCircuit.satCount ternaryInterp =
        2 ^ Compiler.satFreeShift sampleTernaryCircuit ternaryInterp *
          (Compiler.toSatCNF sampleTernaryCircuit ternaryInterp).modelCount ∧
      fanOutMuxCircuit.satCount ternaryInterp = 4 ∧
      fanOutMuxCircuit.satCount ternaryInterp =
        2 ^ Compiler.satFreeShift fanOutMuxCircuit ternaryInterp *
          (Compiler.toSatCNF fanOutMuxCircuit ternaryInterp).modelCount :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    Compiler.satCount_eq_two_pow_satFreeShift_mul_modelCount sampleTernaryCircuit ternaryInterp,
    by decide,
    Compiler.satCount_eq_two_pow_satFreeShift_mul_modelCount fanOutMuxCircuit ternaryInterp⟩

/-! ### Edge cases: pure wiring, zero inputs, unsatisfiable circuit, unconstrained output -/

/-- Pure 0-gate wiring circuit on `4` inputs selecting input `2`: `numVars = 1 ≤ 3 * 0 + 1` and
`satFreeShift = 3`. -/
private def wiringProj : Circuit ternarySig 4 1 :=
  Circuit.wiring ternarySig (fun _ => ⟨2, by decide⟩)

/-- Zero-input (`n = 0`) constant-`true` circuit: the unique empty input satisfies it
(`satCount = 1`). -/
private def zeroInputTrue : Circuit ternarySig 0 1 :=
  ⟨Program.empty.gate ⟨TernaryOp.constTrue, ![]⟩, fun _ => Wire.gate 0⟩

/-- Unsatisfiable De Morgan circuit `x₀ ∧ ¬x₀` on `n = 2` inputs (input `1` unread):
`satCount = 0` and `(toSatCNF).modelCount = 0`. -/
private def unsatDeMorgan : Circuit Boolean.signature 2 1 :=
  ⟨(Program.empty.gate ⟨Boolean.Op.not, ![Wire.input 0]⟩).gate
      ⟨Boolean.Op.and, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

/-- Two-output De Morgan circuit on `n = 3` inputs (`outputs = [0, 1]`, input `2` unread) where
output `0` must be `true` and output `1` is unconstrained (`fun _ => true`):
`R = {0, 1}`, `numVars = 1` (only wire `0` appears in `toCNF`), `freeShift = 3 + 0 - 1 = 2`,
`modelCount = 1`, and `acceptCount = 4`. -/
private def twoOutCircuit : Circuit Boolean.signature 3 2 :=
  Circuit.wiring Boolean.signature ![⟨0, by decide⟩, ⟨1, by decide⟩]

private def firstTrueSecondAny : Fin 2 → Bool → Bool
  | ⟨0, _⟩, b => b
  | ⟨1, _⟩, _ => true

example :
    (Compiler.toSatCNF wiringProj ternaryInterp).numVars = 1 ∧
      Compiler.satFreeShift wiringProj ternaryInterp = 3 ∧
      wiringProj.satCount ternaryInterp = 8 ∧
      zeroInputTrue.satCount ternaryInterp = 1 ∧
      (Compiler.toSatCNF zeroInputTrue ternaryInterp).modelCount = 1 ∧
      unsatDeMorgan.satCount Boolean.interpretation = 0 ∧
      (Compiler.toSatCNF unsatDeMorgan Boolean.interpretation).modelCount = 0 ∧
      (⟨2, unsatDeMorgan⟩ : Σ n, Circuit Boolean.signature n 1) ∉ CircuitSAT ∧
      Compiler.freeShift twoOutCircuit Boolean.interpretation firstTrueSecondAny = 2 ∧
      (Compiler.toCNF twoOutCircuit Boolean.interpretation firstTrueSecondAny).modelCount = 1 ∧
      twoOutCircuit.acceptCount Boolean.interpretation firstTrueSecondAny = 4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_,
    by decide, by decide, by decide⟩
  rw [← signatureCircuitSAT_boolean, ← Compiler.satisfiable_toSatCNF_iff,
    ← CNF.modelCount_pos_iff]
  decide

/-! ### Scale-bound sanity checks and nonvacuous endpoint instantiations -/

example :
    interpolationScale 0 = 0 ∧
      interpolationScale 4 ≤ interpolationScale 5 :=
  ⟨interpolationScale_zero, interpolationScale_mono (by decide)⟩

example :
    ∃ (count : (Σ n, Circuit ternarySig n 1) → ℕ) (A e b : ℕ),
      count ⟨5, sampleTernaryCircuit⟩ = 16 ∧
      ComputableInO count (Circuit.encCircuit encTernaryOp 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.2.size)⌉₊ *
          ((Circuit.encCircuit encTernaryOp 1 c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encTernaryOp 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    exists_circuitSatCounter (σ := ternarySig) encTernaryOp ternaryInterp 3
  refine ⟨count, A, e, b, ?_, hinO⟩
  rw [hspec ⟨5, sampleTernaryCircuit⟩ sampleTernaryCircuit_fanIn]
  decide

example :
    ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
      count ⟨2, unsatDeMorgan⟩ = 0 ∧
      ComputableInO count (Boolean.encCircuit 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.2.size)⌉₊ *
          ((Boolean.encCircuit 1 c).length + 1) ^ e)
        (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_booleanCircuitSatCounter
  refine ⟨count, A, e, b, ?_, hinO⟩
  rw [hspec ⟨2, unsatDeMorgan⟩]
  decide

example :
    ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
      count ⟨2, unsatDeMorgan⟩ = 0 ∧
      ComputableInO count (Boolean.encCircuit 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.1)⌉₊ *
          ((Boolean.encCircuit 1 c).length + 1) ^ e)
        (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_linearSizeBooleanCircuitSatCounter 1
  refine ⟨count, A, e, b, ?_, hinO⟩
  rw [hspec ⟨2, unsatDeMorgan⟩ (by decide)]
  decide

example :
    DecidableInSubexpTime CircuitSAT (Boolean.encCircuit 1) (fun c => c.2.size) ∧
    DecidableInSubexpTime
      {c : Σ n, Circuit Boolean.signature n 1 | c.2.size ≤ 4 * c.1 + 4 ∧ c ∈ CircuitSAT}
      (Boolean.encCircuit 1) Sigma.fst :=
  ⟨decidableInSubexpTime_CircuitSAT_size, decidableInSubexpTime_linearSizeCircuitSAT 4⟩

end ComplexityTests.CircuitCounting
