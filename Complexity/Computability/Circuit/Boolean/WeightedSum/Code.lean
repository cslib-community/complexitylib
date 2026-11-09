/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedSum.Joint
public import Complexity.Computability.Circuit.Boolean.EncodingSize
import all Complexity.Computability.Circuit.Boolean.WeightedSum.Comparisons
import all Complexity.Computability.Circuit.Boolean.PopulationCount.ThresholdPolyTime

/-!
# Actual binary gate-list generation for weighted comparisons

Construct the proved circuits directly as gate lists, avoiding materialization of their typed
wire functions. Every stage agrees exactly with its typed circuit. These executable constructors
accept the original weights/polarities/target, not circuit or output advice. Polynomial binary
construction-time certification and the complete Corollary A.2 counting/distribution composition
remain separate from this gate-for-gate correspondence and the proved linear auxiliary budget.

## Main definitions

* `sumCode`, `testCode`, `jointCode`: actual full code generation from original comparison data.
* `writeTest`, `writeJoint`: actual full functional 3-CNF writing from generated code.

## Main results

* `sumCode_eq`, `testCode_eq`, `jointCode_eq`: exact agreement with the proved typed constructions.
* `writeTest_eq`, `writeJoint_eq`: every actually written clause is the reviewed functional clause.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open BitString

/-- Code of one signed input literal, retaining positive literals as zero-gate wires. -/
@[expose] def literalCode (n i : ℕ) (positive : Bool) : List (Op × List ℕ) × List ℕ :=
  if positive then ([], [i]) else ([(.not, [i])], [n])

private theorem literalCode_eq {n : ℕ} (i : Fin n) (positive : Bool) :
    literalCode n i.val positive =
      (if positive then (Formula.input i) else (Formula.input i).not).toCircuit.code := by
  cases positive <;> rfl

/-- Actual signed-literal code traversal, sharing the declared original inputs. -/
@[expose] def literalsCode {n : ℕ} (positive : Fin n → Bool) (is : List (Fin n)) :
    List (Op × List ℕ) × List ℕ :=
  appendCodes n (is.map fun i => literalCode n i.val (positive i))

private theorem literalsCode_eq {n : ℕ} (positive : Fin n → Bool) (is : List (Fin n)) :
    literalsCode positive is = (literals positive is).code := by
  unfold literalsCode literals
  rw [← appendCodes_code]
  congr 1
  simp only [← literalCode_eq]
  exact (List.ofFn_getElem_eq_map is (fun i => literalCode n i.val (positive i))).symm

/-- Complete native group-count code, including polarity, population counting and widening. -/
@[expose] def groupCountCode {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P a q w : ℕ) : List (Op × List ℕ) × List ℕ :=
  let is := group weights P a q
  compCode n (PopulationCount.pad (Nat.clog 2 (is.length + 1) + 1) w).code
    (compCode n (populationCountCircuit is.length).code (literalsCode positive is))

private theorem groupCountCode_eq {n : ℕ} (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (P a q w : ℕ) :
    groupCountCode weights positive P a q w = (groupCount weights positive P a q w).code := by
  simp only [groupCountCode, literalsCode_eq, compCode_code, groupCount]

private theorem numeralCode_eq (n w q : ℕ) :
    PopulationCount.numeralCode n w q =
      (wordConstCircuit n ((equivFin w).symm
        ⟨q % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)).code := by
  rw [← PopulationCount.numeralCode_eq]
  unfold PopulationCount.numeralCode
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < w := List.mem_range.mp hi
  rw [Nat.testBit_mod_two_pow]
  simp [hi']

/-- One actual group contribution, with every multiplier and constant gate retained. -/
@[expose] def contributionCode {n : ℕ} (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (P a q w : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode n (Modular.multiplyCode w)
    (appendCode n (groupCountCode weights positive P a q w)
      (PopulationCount.numeralCode n w (P ^ a * q)))

private theorem contributionCode_eq {n : ℕ} (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (P a q w : ℕ) :
    contributionCode weights positive P a q w = (contribution weights positive P a q w).code := by
  simp only [contributionCode, Modular.multiplyCode_eq_code, groupCountCode_eq,
    numeralCode_eq, appendCode_code, compCode_code, contribution]

/-- Generate the complete weighted arithmetic code from actual groups and original literals. -/
@[expose] def sumCode {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P d w : ℕ) : List (Op × List ℕ) × List ℕ :=
  sumPairsCode n w ((List.range d).flatMap fun a =>
    (List.finRange P).map fun q : Fin P =>
      pairWithZeroCode n w (contributionCode weights positive P a q.val w))

/-- Exact code, not just equivalent input/output behavior. -/
theorem sumCode_eq {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P d w : ℕ) : sumCode weights positive P d w = (sumCircuit weights positive P d w).code := by
  unfold sumCode sumCircuit
  rw [← sumPairsCode_eq_code]
  congr 1
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    contributionCode_eq, pairWithZeroCode_eq_code]

/-- Constant upper-comparison branches avoid decoding an out-of-range integer as a unary loop. -/
@[expose] def upperCode {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : List (Op × List ℕ) × List ℕ :=
  if target < 0 then ([(.const false, [])], [n])
  else if target.toNat < 2 ^ width n c then
    compCode n (Boolean.leCircuit (width n c)).code
      (appendCode n (sumCode weights positive (radix n) (positions c) (width n c))
        (PopulationCount.numeralCode n (width n c) target.toNat))
  else ([(.const true, [])], [n])

private theorem upperCode_eq {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    upperCode c weights positive target = (leCircuit c weights positive target).code := by
  unfold upperCode leCircuit
  split_ifs with ht hfit
  · rfl
  · simp only [sumCode_eq, numeralCode_eq, Nat.mod_eq_of_lt hfit,
      appendCode_code, compCode_code]
  · rfl

/-- Actual code for all comparison modes; tests share original bits, not copied inputs. -/
@[expose] def testCode {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : List (Op × List ℕ) × List ℕ :=
  let neg (code : List (Op × List ℕ) × List ℕ) :=
    compCode n ([(.not, [0])], [1]) code
  match op with
  | .le => upperCode c weights positive target
  | .ge => neg (upperCode c weights positive (target - 1))
  | .eq => compCode n ([(.and, [0, 1])], [2])
      (appendCode n (upperCode c weights positive target)
        (neg (upperCode c weights positive (target - 1))))
  | .lt => upperCode c weights positive (target - 1)
  | .gt => neg (upperCode c weights positive target)

/-- The actual binary code is the functional comparison already proved correct. -/
theorem testCode_eq {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    testCode op c weights positive target = (test op c weights positive target).code := by
  cases op <;> simp only [testCode, upperCode_eq, test]
  all_goals first
    | change compCode n (Circuit.oneGate (σ := signature) Op.not (fun _ => (0 : Fin 1))).code
        (leCircuit c weights positive _).code = _
      rw [compCode_code]
      rfl
    | change compCode n (((Formula.input (0 : Fin 2)).and (Formula.input 1)).toCircuit).code
        (appendCode n (leCircuit c weights positive target).code
          (compCode n (Circuit.oneGate (σ := signature) Op.not (fun _ => (0 : Fin 1))).code
            (leCircuit c weights positive (target - 1)).code)) = _
      rw [compCode_code, appendCode_code, compCode_code]
      rfl

/-- Actual fixed-family code, with separate gates and shared original inputs. -/
@[expose] def jointCode {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) : List (Op × List ℕ) × List ℕ :=
  appendCodes n (List.ofFn fun j => testCode (op j) c (weights j) (positive j) (target j))

/-- All actual family gates/outputs coincide with the original simultaneous circuit. -/
theorem jointCode_eq {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) : jointCode op c weights positive target =
      (joint op c weights positive target).code := by
  simp only [jointCode, testCode_eq, appendCodes_code, joint]

/-- Write the actual generated code with the required true output bit. -/
@[expose] def writeTest {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : Logic.PL.CNF ℕ :=
  FunctionalCNF.write (n, testCode op c weights positive target, [true])

/-- Every serialized literal agrees with the proved functional encoding. -/
theorem writeTest_eq {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    writeTest op c weights positive target = formula op c weights positive target := by
  rw [writeTest, testCode_eq]
  rfl

/-- Write all actual generated tests, requiring every output to be true. -/
@[expose] def writeJoint {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) : Logic.PL.CNF ℕ :=
  FunctionalCNF.write (n, jointCode op c weights positive target, List.replicate r true)

/-- Complete joint writing, including output units and every full gate truth table. -/
theorem writeJoint_eq {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) :
    writeJoint op c weights positive target = jointFormula op c weights positive target := by
  rw [writeJoint, jointCode_eq]
  simp only [jointFormula, FunctionalCNF.ofCircuit, List.ofFn_const]

/-- Complete binary circuit output, including every gate tag/reference/output delimiter. This
storage/output-volume bound is separate from the missing generator-time certificate. -/
theorem testCode_bits_le {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    (encCode (testCode op c weights positive target)).length ≤
      2 * (comparisonBudget c * (n + 1)) *
        (23 + 8 * (n + comparisonBudget c * (n + 1))) + 1 +
          (2 * (n + comparisonBudget c * (n + 1)) + 1) := by
  rw [testCode_eq]
  have h := length_encCode_le (test op c weights positive target)
  have hs := size_test_linear op c weights positive target
  simp only [one_mul] at h
  exact h.trans (by gcongr)

end Cslib.Circuits.Boolean.WeightedSum
