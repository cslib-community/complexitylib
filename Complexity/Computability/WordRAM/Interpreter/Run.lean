/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Interpreter.Refinement
public import Complexity.Computability.GenericRAM.Native.Combinators
import all Complexity.Computability.WordRAM.Interpreter.Step
import all Complexity.Computability.WordRAM.Interpreter.Refinement
import all Complexity.Computability.WordRAM.ProgramLiterals.Encoding
import all Complexity.Computability.GenericRAM.Simulation.Run
import all Complexity.Computability.GenericRAM.Simulation.Turing
import all Complexity.Computability.WordRAM.Basis

/-!
# One binary-tape interpreter for runtime native programs

The program, physical width and binary clock are input data. A fixed opcode
machine is iterated with an actual binary countdown; faults and returns absorb
remaining rounds. The resource certificate charges all encoded program/state
copying, sparse-list scans, control and counter work. Its workspace uses maxima
over all prefixes, rather than total allocation or native live support.
-/

public section

namespace Cslib.WordRAM.Interpreter

open Cslib.GenericRAM Turing.MultiTapeTM
open NativeCertificate

/-- Program and width are runtime parameters of the finite-state interpreter. -/
abbrev Parameters (r : ℕ) := ℕ × Program .standard r
/-- Complete runtime instruction fields, including arbitrarily large labels and literals. -/
noncomputable abbrev parametersEncoding (r : ℕ) : Parameters r ↪ List Bool :=
  encPair encUnary (ProgramLiterals.programEncoding r)
/-- Runtime program/width and the finite machine state. -/
abbrev NativeInput (r : ℕ) := Parameters r × FiniteState Basis.standard.genericModel r
/-- No program is hidden in the control of this encoding. -/
noncomputable abbrev nativeInputEncoding (r : ℕ) : NativeInput r ↪ List Bool :=
  encPair (parametersEncoding r) (FiniteState.encoding Basis.standard.encoding)

/-- The typed interface of the actual encoded-row instruction interpreter. -/
noncomputable def stepCertificate {r : ℕ} : NativeCertificate
    (fun x : NativeInput r => FiniteState.step x.1.1 x.1.2.toGeneric x.2)
    (nativeInputEncoding r) (FiniteState.resultEncoding Basis.standard.encoding) := by
  let prepare : NativeCertificate
      (fun x : NativeInput r => ((x.1.1, ProgramLiterals.serialize x.1.2), toTuple x.2))
      (nativeInputEncoding r) (inputEncoding r) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  let c := (NativeCertificate.ofPolyTime (step_polyTime (r := r))).comp prepare
  exact ⟨c.time, c.space, c.computes.of_enc_eq (fun x => by
    rw [Function.comp_apply, step_serialize]
    cases FiniteState.step x.1.1 x.1.2.toGeneric x.2 with
    | none => rfl
    | some out => cases out <;> rfl)⟩

/-- The same one-step machine is polynomial uniformly in the entire runtime input wire. -/
theorem stepCertificate_isPolynomial {r : ℕ} :
    (stepCertificate (r := r)).IsPolynomial := by
  let prepare : NativeCertificate
      (fun x : NativeInput r => ((x.1.1, ProgramLiterals.serialize x.1.2), toTuple x.2))
      (nativeInputEncoding r) (inputEncoding r) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  have h := NativeCertificate.comp_isPolynomial
    (NativeCertificate.ofPolyTime (step_polyTime (r := r))) prepare
    (NativeCertificate.ofPolyTime_isPolynomial step_polyTime) ⟨.self, .self⟩
  exact h

/-- Interpreter loop state; the complete runtime program remains on tape. -/
abbrev Loop (r : ℕ) := Parameters r × FiniteState.Result Basis.standard.genericModel r
/-- Every loop state includes the whole encoded program and all sparse bindings. -/
noncomputable abbrev loopEncoding (r : ℕ) : Loop r ↪ List Bool :=
  encPair (parametersEncoding r) (FiniteState.resultEncoding Basis.standard.encoding)

/-- Advance one step, retaining program/width and absorbing fault/return. -/
def round {r : ℕ} (x : Loop r) : Loop r :=
  (x.1, FiniteState.stepResult x.1.1 x.1.2.toGeneric x.2)

/-- A single finite machine implements a round for every runtime program. -/
noncomputable def roundCertificate {r : ℕ} :
    NativeCertificate (round (r := r)) (loopEncoding r) (loopEncoding r) := by
  let hid : NativeCertificate (id : Loop r → Loop r) (loopEncoding r) (loopEncoding r) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  let hbody : NativeCertificate (id : Loop r × FiniteState Basis.standard.genericModel r → _)
      (encPair (loopEncoding r) (FiniteState.encoding Basis.standard.encoding))
      (encPair (loopEncoding r) (FiniteState.encoding Basis.standard.encoding)) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  let result := option ((FiniteState.continuingCertificate Basis.standard.encoding).comp
      (snd hid)) (snd hid) (stepCertificate.comp (prod (fst (fst hbody)) (snd hbody)))
  exact congr (prod (fst hid) result) (fun x => by
    simp only [round, FiniteState.stepResult_eq, Function.comp_apply]
    rfl)

/-- Full rounds, including retaining/copying the executable and absorbing outcomes, are
uniformly polynomial in their complete input wire. -/
theorem roundCertificate_isPolynomial {r : ℕ} :
    (roundCertificate (r := r)).IsPolynomial := by
  dsimp only [roundCertificate]
  apply congr_isPolynomial
  apply prod_isPolynomial
  · exact ⟨.self, .self⟩
  · apply option_isPolynomial
    · exact comp_isPolynomial _ _ ⟨.self, .self⟩ ⟨.self, .self⟩
    · exact ⟨.self, .self⟩
    · apply comp_isPolynomial _ _ stepCertificate_isPolynomial
      exact prod_isPolynomial _ _ ⟨.self, .self⟩ ⟨.self, .self⟩

/-- The explicit runtime-program loop agrees with the actual native clocked execution. -/
theorem iterate_round {r : ℕ} (k : ℕ) (p : Program .standard r)
    (out : FiniteState.Result Basis.standard.genericModel r) (n : ℕ) :
    round^[n] ((k, p), out) = ((k, p), (FiniteState.stepResult k p.toGeneric)^[n] out) := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, round, ih, ← Function.iterate_succ_apply]

/-- Clock, runtime program/width and full initial finite state. -/
abbrev RunInput (r : ℕ) := ℕ × NativeInput r
/-- Clock digits are binary, physical width unary, all instruction fields explicit. -/
noncomputable abbrev runInputEncoding (r : ℕ) : RunInput r ↪ List Bool :=
  encPair encNat (nativeInputEncoding r)

/-- Initial interpreter loop value, retaining all runtime parameters. -/
@[expose] def initial {r : ℕ} (x : RunInput r) : Loop r := (x.2.1, Option.some (.inl x.2.2))

/-- One binary-clocked loop, retaining the complete program at every prefix. -/
@[expose] noncomputable def clockedCertificate {r : ℕ} : NativeCertificate
    (fun x : RunInput r => round^[x.1] (initial x)) (runInputEncoding r) (loopEncoding r) := by
  let hid : NativeCertificate (id : RunInput r → RunInput r)
      (runInputEncoding r) (runInputEncoding r) := linear (ComputableInO.of_eq fun _ => rfl)
  exact iterate (fst hid) (prod (fst (snd hid))
    (NativeCertificate.some (NativeCertificate.inl (snd (snd hid)) encNat))) roundCertificate

/-- Maximum complete encoded loop state over every prefix, including parked program fields,
all registers, physical width and retained sparse zero bindings. -/
noncomputable def trajectoryLength {r : ℕ} (x : RunInput r) : ℕ :=
  maxStateLength (loopEncoding r) round x.1 (initial x)

/-- Time charges binary countdown control, full-state copying and maximum charged step cost.
The existential machine constant is uniform in program, width and clock. -/
theorem clocked_time {r : ℕ} (x : RunInput r) : clockedCertificate.time x =
    3 * (runInputEncoding r x).length + (x.1 + 1) *
      (maxRoundTime roundCertificate x.1 (initial x) + trajectoryLength x +
        ((encNat x.1).length + 1) ^ 2) := by
  dsimp only [clockedCertificate, NativeCertificate.iterate, NativeCertificate.fst,
    NativeCertificate.snd, NativeCertificate.prod, NativeCertificate.some,
    NativeCertificate.inl, NativeCertificate.linear, NativeCertificate.post, trajectoryLength]
  omega

/-- Simultaneous workspace uses prefix maxima, without multiplying workspace by the clock. -/
theorem clocked_space {r : ℕ} (x : RunInput r) : clockedCertificate.space x =
    3 * (runInputEncoding r x).length +
      maxRoundSpace roundCertificate x.1 (initial x) + trajectoryLength x +
        (encNat x.1).length := by
  dsimp only [clockedCertificate, NativeCertificate.iterate, NativeCertificate.fst,
    NativeCertificate.snd, NativeCertificate.prod, NativeCertificate.some,
    NativeCertificate.inl, NativeCertificate.linear, NativeCertificate.post, trajectoryLength]
  omega

/-- A single pair of polynomial constants bounds each charged round at every prefix. The
parameter is actual full encoded trajectory length, not the smaller native live support. -/
theorem prefix_resources (r : ℕ) : ∃ C d : ℕ, ∀ (x : RunInput r) (j : ℕ), j ≤ x.1 →
    roundCertificate.time (round^[j] (initial x)) ≤ C * (trajectoryLength x + 1) ^ d ∧
    roundCertificate.space (round^[j] (initial x)) ≤ C * (trajectoryLength x + 1) ^ d := by
  have hp := roundCertificate_isPolynomial (r := r)
  obtain ⟨C, d, hb⟩ := (hp.1.add hp.2).exists_le
  refine ⟨C, d, fun x j hj => ?_⟩
  have bound := hb (round^[j] (initial x))
  have len := le_maxStateLength (loopEncoding r) round hj (initial x)
  have mono := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right len 1) d)
  dsimp only [trajectoryLength]
  constructor <;> omega

/-- Uniform interpreter overhead in binary clock `T` and actual prefix encoding maximum `M`:
time is `O(T * poly(M) + preparation + binary control)` and peak workspace has no factor `T`.
The exponents/constants depend only on register count and the fixed instruction set. -/
theorem clocked_resources (r : ℕ) : ∃ C d : ℕ, ∀ x : RunInput r,
    clockedCertificate.time x ≤ 3 * (runInputEncoding r x).length + (x.1 + 1) *
      (C * (trajectoryLength x + 1) ^ d + trajectoryLength x +
        ((encNat x.1).length + 1) ^ 2) ∧
    clockedCertificate.space x ≤ 3 * (runInputEncoding r x).length +
      C * (trajectoryLength x + 1) ^ d + trajectoryLength x + (encNat x.1).length := by
  obtain ⟨C, d, h⟩ := prefix_resources r
  refine ⟨C, d, fun x => ?_⟩
  have ht := maxRoundTime_le roundCertificate x.1 (initial x)
    (fun j hj => (h x j hj).1)
  have hs := maxRoundSpace_le roundCertificate x.1 (initial x)
    (fun j hj => (h x j hj).2)
  constructor
  · rw [clocked_time]
    gcongr
  · rw [clocked_space]
    omega

/-- One machine executes every supplied program for the supplied binary clock. -/
noncomputable def runCertificate {r : ℕ} : NativeCertificate
    (fun x : RunInput r => FiniteState.run x.2.1.1 x.2.1.2.toGeneric x.1 x.2.2)
    (runInputEncoding r) (FiniteState.resultEncoding Basis.standard.encoding) :=
  congr (snd clockedCertificate) (fun x => by
    rw [initial, iterate_round, ← FiniteState.run_eq_iterate_stepResult])

end Cslib.WordRAM.Interpreter
