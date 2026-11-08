/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORGeneratedRunInput
public import Complexity.Computability.WordRAM.Interpreter.Output
import all Complexity.Cryptanalysis.AddXNORGeneratedRunInput
import all Complexity.Cryptanalysis.AddXNORBitExecution
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Computability.WordRAM.Interpreter.Run
import all Complexity.Computability.WordRAM.Interpreter.Output
import all Complexity.Computability.GenericRAM.Simulation.Run
import all Complexity.Computability.GenericRAM.Simulation.Turing

/-!
# One uniform bit machine executes generated dissection packets

One machine consumes the runtime encoded program, unary physical width, binary
clock and finite state. It materializes halt parking, executes the uniform
interpreter, reads the runtime output array and applies the actual witness decoder.
Composing it with packet preparation gives one multitape machine on original
inputs, with exhaustive misses and sound original-chain witnesses.

This is a concrete computability/resource bridge, not the sharp source theorem.
The certified profiles charge preparation, program copying, binary control,
association-list scans (including retained zero bindings), prefix trajectory
maxima and output materialization. No bound on native live support is substituted
for full sparse encoding length. The specialized sorted-list simulation and sharp
source asymptotics, source seed/zero-target specialization and the other ALL-main
objectives remain open. See [WangLvShenZhang2027], PDF p. 6 and Lemma 8/Theorem 7,
pp. 21–22; this general runtime interpreter is an original construction.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.UniformExecution

open Cslib.WordRAM Cslib.GenericRAM Turing.MultiTapeTM
open NativeCertificate GeneratedRunInput ProgramGeneration Native.Driver

/-- Materialize runtime halt parking and arrange the runtime width/program/clock/state interface. -/
def executionInput (x : Packet) : Interpreter.RunInput 40 :=
  (x.1.2.2, (x.1.2.1, x.1.1.parkHalts), x.2)

/-- Packet rearrangement includes actual parking generation; no executable is a premise. -/
noncomputable def executionInputCertificate : NativeCertificate executionInput packetEncoding
    (Interpreter.runInputEncoding 40) := by
  let hid : NativeCertificate (id : Packet → Packet) packetEncoding packetEncoding :=
    linear (ComputableInO.of_eq fun _ => rfl)
  exact prod (snd (snd (fst hid)))
    (prod (prod (fst (snd (fst hid)))
      (Interpreter.parkingCertificate.comp (fst (fst hid)))) (snd hid))

/-- One program-input simulator, with constants independent of every runtime program field. -/
noncomputable def finiteRunCertificate : NativeCertificate
    (fun x : Packet => FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2)
    packetEncoding (FiniteState.resultEncoding Basis.standard.encoding) :=
  Interpreter.runCertificate.comp executionInputCertificate

/-- Actual output state, using the same fault/return fallback as the native endpoint. -/
def finalState (x : Packet) : FiniteState Basis.standard.genericModel 40 :=
  (FiniteState.continuing
    (FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2)).getD
      (initState .standard 40 [])

/-- Extract the real final finite state, without assuming successful execution. -/
noncomputable def finalStateCertificate : NativeCertificate finalState packetEncoding
    (FiniteState.encoding Basis.standard.encoding) :=
  post ((FiniteState.continuingCertificate Basis.standard.encoding).comp finiteRunCertificate)
    (ComputableInDegree.getD (enc₁ := FiniteState.encoding Basis.standard.encoding)
      (enc := encOption (FiniteState.encoding Basis.standard.encoding))
      (initState .standard 40 [])).inO_one

/-- Runtime program length, read from the full executable wire. -/
theorem programLength_polyTime : ComputableInPolyTime (fun x : Packet => x.1.1.length)
    packetEncoding encNat := by
  have rows : ComputableTidilyInPolyTime
      (fun x : Packet => ProgramLiterals.serialize x.1.1) packetEncoding
      (encList (encList encNat)) :=
    (ComputableTidilyInPolyTime.fst
      (ProgramLiterals.programEncoding 40) (encPair encUnary encNat)).comp
      (ComputableTidilyInPolyTime.fst _ _)
  exact .of_tidy ((ComputableTidilyInPolyTime.unary_to_binary.comp
    ((ComputableTidilyInPolyTime.length_list (encList encNat)).comp rows)).of_enc_eq
      (fun x => by simp [ProgramLiterals.serialize]))

/-- One machine executes every typed packet, reads its actual output and decodes its witness. -/
noncomputable def packetExecutionCertificate : NativeCertificate GeneratedRunInput.run
    packetEncoding encBits := by
  let c := post (Interpreter.outputCertificate.comp
    (prod (NativeCertificate.ofPolyTime programLength_polyTime) finalStateCertificate))
    BitExecution.decodeWords_inO
  exact ⟨c.time, c.space, c.computes.of_enc_eq (fun _ => rfl)⟩

/-- One fixed multitape machine, from original arrays/parameters through generated executable
and actual uniform execution to encoded optional original-chain witnesses. -/
@[expose] noncomputable def sourceCertificate : NativeCertificate
    (GeneratedRunInput.run ∘ GeneratedRunInput.packet) sourceEncoding encBits :=
  packetExecutionCertificate.comp packetCertificate

/-- Preparation and execution time are charged in sequence, including all bit-level overhead. -/
theorem source_time (x : Source) : sourceCertificate.time x =
    packetCertificate.time x + packetExecutionCertificate.time (packet x) := rfl

/-- Simultaneous workspace is charged by composition, with the interpreter's prefix maxima
and the full materialized output; it is not a count of distinct allocated native cells. -/
theorem source_space (x : Source) : sourceCertificate.space x =
    packetCertificate.space x + packetExecutionCertificate.space (packet x) := rfl

/-- Uniform execution has no supplied simulation, executable, trace or semantic witness premise. -/
theorem original_correct {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    ∃ out : Option (List Bool),
      (GeneratedRunInput.run ∘ GeneratedRunInput.packet)
        (originalSource p as bs cs ds s t) = encOption encBits out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = Option.some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  simpa only [Function.comp_apply] using
    GeneratedRunInput.original_correct hp as bs cs ds s t

/-- One actual bit-machine certificate includes both generated input preparation and execution,
with constants uniform over all source fields and original operand arrays. -/
theorem uniform_execution : ComputableInO
    (GeneratedRunInput.run ∘ GeneratedRunInput.packet) sourceEncoding encBits
    sourceCertificate.time sourceCertificate.space := sourceCertificate.computes

/-- A single finite-control binary multitape machine works for all original inputs. Neither
its number of tapes, state space nor resource constant depends on runtime input parameters. -/
theorem original_machine : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q)
    (machine : Turing.MultiTapeTM k Bool Q),
    ∀ (m p : ℕ), p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s t : BitVec m),
    ∃ out : Option (List Bool),
      machine.ComputesInTimeAndSpace
        (sourceEncoding (originalSource p as bs cs ds s t)) (encOption encBits out)
        (c * (sourceCertificate.time (originalSource p as bs cs ds s t) + 1))
        (c * (sourceCertificate.space (originalSource p as bs cs ds s t) + 1)) ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = Option.some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) := by
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := uniform_execution
  refine ⟨c, k, Q, hQ, machine, fun m p hp as bs cs ds s t => ?_⟩
  obtain ⟨out, encoding, miss, sound⟩ := original_correct hp as bs cs ds s t
  refine ⟨out, ?_, miss, sound⟩
  simpa only [encBits_apply, encoding] using computes (originalSource p as bs cs ds s t)

end Cslib.Cryptanalysis.AddXNOR.UniformExecution
