/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.NP
import Complexity.Computability.Complexity.Problems.CircuitSAT
import Complexity.Computability.Complexity.Problems.CircuitValue

/-!
# Tests for circuits as data

Concrete codes, decoding boundaries, evaluation, certificates, the circuit value problem, circuit
satisfiability, the circuit of a formula and MCSP, with axiom checks for the headline results.
-/

namespace Cslib.Complexity.Tests.CircuitCode

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Codes and decoding -/

/-- The circuit `x₀ ∧ ¬x₁` on two inputs. -/
def andNot : Circuit signature 2 1 :=
  ⟨(Program.empty.gate ⟨Op.not, ![Wire.input 1]⟩).gate ⟨Op.and, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

example :
    andNot.code = ([(.not, [1]), (.and, [0, 2])], [3]) ∧
      (Circuit.ofCode 2 1 andNot.code : Option (Circuit signature 2 1)) = some andNot ∧
      (Circuit.ofCode 2 1 ([(.not, [2])], [2]) : Option (Circuit signature 2 1)) = none ∧
      (Circuit.ofCode 2 1 ([(.not, [1])], [3]) : Option (Circuit signature 2 1)) = none ∧
      (Circuit.ofCode 2 1 ([(.not, [0, 1])], [2]) : Option (Circuit signature 2 1)) = none ∧
      (Circuit.ofCode 2 1 ([(.not, [1])], []) : Option (Circuit signature 2 1)) = none ∧
      Program.IsCodeFrom signature 2 0 andNot.code.1 ∧
      ¬Program.IsCodeFrom signature 2 0 [(Op.and, [0, 3])] ∧
      (encCircuit 1 ⟨2, andNot⟩).take 5 = [true, true, true, true, false] :=
  ⟨by decide, Circuit.ofCode_code andNot, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-! ### Evaluation -/

example :
    evalCode interpretation false [true, false] andNot.code.1 = [true, false, true, true] ∧
      andNot.eval interpretation ![true, false] 0 = true ∧
      andNot.eval interpretation ![true, true] 0 = false ∧
      evalCode interpretation false [true] [(.and, [0]), (.or, [5, 0])] = [true, false, true] ∧
      evalCode interpretation true [false] [(.and, [7, 7])] = [false, true] :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ### Certificates -/

example :
    readCertificate 2 3 (certificate 2 3 andNot.code.1 3 ++ [true, true]) = (andNot.code.1, 3) ∧
      (certificate 2 3 andNot.code.1 3).length = certLength 2 3 ∧
      readCertificate 2 0 [true, true, true] = ([], 2) :=
  ⟨readCertificate_certificate_append (by decide) (by decide) (by decide) _,
    by decide, by decide⟩

/-! ### The circuit value problem -/

example :
    (⟨2, andNot, ![true, false]⟩ : Σ n, Circuit signature n 1 × BitString n) ∈ CircuitValue ∧
      (⟨2, andNot, ![false, false]⟩ : Σ n, Circuit signature n 1 × BitString n) ∉ CircuitValue :=
  ⟨mem_CircuitValue.2 (by decide), fun h => absurd (mem_CircuitValue.1 h) (by decide)⟩

/-! ### Circuit satisfiability -/

example : (⟨2, andNot⟩ : Σ n, Circuit signature n 1) ∈ CircuitSAT := ⟨![true, false], by decide⟩

/-- The unsatisfiable circuit `x₀ ∧ ¬x₀`. -/
def contradiction : Circuit signature 1 1 :=
  ⟨(Program.empty.gate ⟨Op.not, ![Wire.input 0]⟩).gate ⟨Op.and, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

example : (⟨1, contradiction⟩ : Σ n, Circuit signature n 1) ∉ CircuitSAT := by
  rintro ⟨x, hx⟩
  have : ∀ y : BitString 1, contradiction.eval interpretation y 0 = false := by decide
  exact absurd hx (by rw [this x]; decide)

-- A circuit with no inputs is satisfiable exactly when it outputs true.
example : (⟨0, ⟨Program.empty.gate ⟨Op.const true, ![]⟩, fun _ => Wire.gate 0⟩⟩ :
    Σ n, Circuit signature n 1) ∈ CircuitSAT := ⟨![], rfl⟩

/-! ### The circuit of a formula -/

open Cslib.Logic.PL in
/-- `(x₃ ∨ ¬x₇) ∧ x₇`, with arbitrary variable numbers. -/
def φ : CNF ℕ := [[(3, true), (7, false)], [(7, true)]]

example :
    (SAT.toCircuit φ).1 = 3 ∧
      (SAT.circuitGates φ).length = 18 ∧
      (SAT.toCircuit φ).2.eval interpretation (fun i => [true, true, false].getD i false) 0 =
        true ∧
      (SAT.toCircuit φ).2.eval interpretation (fun i => [false, true, true].getD i false) 0 =
        false ∧
      (SAT.toCircuit []).2.eval interpretation (fun _ => false) 0 = true ∧
      (SAT.toCircuit [[]]).2.eval interpretation (fun _ => false) 0 = false :=
  ⟨rfl, by decide,
    by rw [SAT.eval_toCircuit]; decide,
    by rw [SAT.eval_toCircuit]; decide,
    by rw [SAT.eval_toCircuit]; rfl,
    by rw [SAT.eval_toCircuit]; rfl⟩

/-! ### MCSP -/

-- Verifier evaluations and positive MCSP instances for the zero-gate identity and one-gate
-- negation circuits on one input.
example :
    MCSP.verifier (⟨1, ![false, true], 0⟩, certificate 1 0 [] 0) = true ∧
      MCSP.verifier (⟨1, ![true, false], 0⟩, certificate 1 0 [] 0) = false ∧
      MCSP.verifier (⟨1, ![true, false], 1⟩, certificate 1 1 [(.not, [0])] 1) = true ∧
      MCSP.verifier (⟨1, ![true, false], 1⟩, certificate 1 1 [(.not, [1])] 1) = false ∧
      (⟨1, ![false, true], 0⟩ : MCSP.Instance) ∈ MCSP ∧
      (⟨1, ![true, false], 1⟩ : MCSP.Instance) ∈ MCSP :=
  ⟨by decide, by decide, by decide, by decide,
    MCSP.mem_of_verifier_eq_true (w := certificate 1 0 [] 0) (by decide),
    MCSP.mem_of_verifier_eq_true (w := certificate 1 1 [(.not, [0])] 1) (by decide)⟩

example : (⟨1, ![true, false], 0⟩ : MCSP.Instance) ∉ MCSP := by
  intro hx
  obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := MCSP.exists_verifier_append hx
  · revert hu; decide
  · have := hV []; revert this; cases b <;> decide
  · simp [certLength, MCSP.budget] at hu

example : [false, true] ∈ (GapMCSP (fun _ => 0) (fun _ => 0) fun _ => le_rfl).yes :=
  (GapMCSP.ofFn_mem_yesSet_iff_mem_MCSP (n := 1) (T := ![false, true])).mpr
    (MCSP.mem_of_verifier_eq_true (x := ⟨1, ![false, true], 0⟩) (w := certificate 1 0 [] 0)
      (by decide))

example : [true, false] ∈ (GapMCSP (fun _ => 0) (fun _ => 0) fun _ => le_rfl).no := by
  refine (GapMCSP.ofFn_mem_noSet_iff_notMem_MCSP (n := 1) (T := ![true, false])).mpr ?_
  intro hx
  obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := MCSP.exists_verifier_append hx
  · revert hu; decide
  · have := hV []; revert this; cases b <;> decide
  · simp [certLength, MCSP.budget] at hu

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Circuit.ofCode_code' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.ofCode_code

/--
info: 'Cslib.Circuits.Circuit.code_of_ofCode_eq_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.code_of_ofCode_eq_some

end Cslib.Complexity.Tests.CircuitCode
