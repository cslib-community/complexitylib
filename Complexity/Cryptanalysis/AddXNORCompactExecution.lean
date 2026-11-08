/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORUniformExecution
public import Complexity.Computability.WordRAM.Interpreter.CompactBounds
import all Complexity.Cryptanalysis.AddXNORUniformExecution
import all Complexity.Cryptanalysis.AddXNORGeneratedRunInput
import all Complexity.Cryptanalysis.AddXNORBitExecution
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNORNativeOutputResources
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Computability.WordRAM.Interpreter.Compact
import all Complexity.Computability.WordRAM.Interpreter.CompactRun
import all Complexity.Computability.WordRAM.Interpreter.CompactBounds
import all Complexity.Computability.WordRAM.Turing.ListOutput
import all Complexity.Computability.GenericRAM.Simulation.Run
import all Complexity.Computability.GenericRAM.Simulation.Turing
import all Complexity.Computability.WordRAM.Turing
import all Complexity.Computability.WordRAM.Defs

/-!
# Uniform dissection bit execution with actual default deletion

The approved interpreter/preparation are reused, with a real compacting scan at
initialization and after every native round. Original output bits and witness
correctness are preserved. Every retained prefix encoding is bounded using the
proved simultaneous native computed-balance support and physical word/address
widths. Historical zero writes no longer accumulate stored bindings.

This removes one concrete obstruction to sharp source resources. Association-list
scans and polynomial interpreter workspace still prevent claiming the source's
sharp bit time/peak space. No sharp simulator or sorting bound is assumed.
See [WangLvShenZhang2027], PDF p. 6, Lemma 8/Theorem 7, pp. 21–22.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CompactExecution
open Cslib.WordRAM Cslib.GenericRAM Turing.MultiTapeTM
open NativeCertificate Native.Driver GeneratedRunInput ProgramGeneration

/-- One runtime-program machine executes the actual compacting loop. -/
noncomputable def finiteRunCertificate : NativeCertificate
    (fun x : Packet => Interpreter.compactResult
      (FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2))
    packetEncoding (FiniteState.resultEncoding Basis.standard.encoding) :=
  Interpreter.compactRunCertificate.comp UniformExecution.executionInputCertificate

/-- The actual compacted final state, with the same total fallback on faults/returns. -/
def finalState (x : Packet) : FiniteState Basis.standard.genericModel 40 :=
  (FiniteState.continuing (Interpreter.compactResult
    (FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2))).getD
      (initState .standard 40 [])

/-- Compaction leaves the parked output register unchanged. -/
theorem parkedRegister_compact {r : ℕ} (L : ℕ)
    (s : FiniteState Basis.standard.genericModel r) (is : List (Fin r)) :
    parkedRegister L (Interpreter.compactState s) is = parkedRegister L s is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [parkedRegister, Interpreter.compactState] at ih ⊢
    rw [ih]
    rfl

/-- Actual output memory is unchanged at every address, including implicit zero cells. -/
theorem parkedOutput_compact {r : ℕ} (L : ℕ)
    (s : FiniteState Basis.standard.genericModel r) :
    parkedOutput L (Interpreter.compactState s) = parkedOutput L s := by
  unfold parkedOutput
  rw [parkedRegister_compact]
  simp only [Interpreter.compactState, SparseMemory.read_compact]

/-- Bit readback/decoding from the compacted run agrees with the approved packet semantics. -/
theorem readback_eq (x : Packet) :
    BitExecution.decodeWords (parkedOutput x.1.1.length (finalState x)) =
      GeneratedRunInput.run x := by
  unfold finalState GeneratedRunInput.run
  cases h : FiniteState.run x.1.2.1 x.1.1.parkHalts.toGeneric x.1.2.2 x.2 with
  | none => rfl
  | some out =>
    cases out with
    | inr v => rfl
    | inl s => exact congrArg BitExecution.decodeWords (parkedOutput_compact x.1.1.length s)

/-- Final state extraction is a real bit computation, without successful-run premises. -/
noncomputable def finalStateCertificate : NativeCertificate finalState packetEncoding
    (FiniteState.encoding Basis.standard.encoding) :=
  post ((FiniteState.continuingCertificate Basis.standard.encoding).comp finiteRunCertificate)
    (ComputableInDegree.getD (enc₁ := FiniteState.encoding Basis.standard.encoding)
      (enc := encOption (FiniteState.encoding Basis.standard.encoding))
      (initState .standard 40 [])).inO_one

/-- The compacting machine reads actual output cells and applies the actual witness decoder. -/
noncomputable def packetExecutionCertificate : NativeCertificate GeneratedRunInput.run
    packetEncoding encBits := by
  let c := post (Interpreter.outputCertificate.comp
    (prod (NativeCertificate.ofPolyTime UniformExecution.programLength_polyTime)
      finalStateCertificate)) BitExecution.decodeWords_inO
  exact NativeCertificate.congr c readback_eq

/-- One machine composes original-input preparation, runtime compacting execution and readback. -/
noncomputable def sourceCertificate : NativeCertificate
    (GeneratedRunInput.run ∘ GeneratedRunInput.packet) sourceEncoding encBits :=
  packetExecutionCertificate.comp packetCertificate

/-- One finite-control binary multitape machine realizes the compacting implementation for
all original inputs. Its resource profiles include all scans and filter temporaries. -/
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
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := sourceCertificate.computes
  refine ⟨c, k, Q, hQ, machine, fun m p hp as bs cs ds s t => ?_⟩
  obtain ⟨out, encoding, miss, sound⟩ := UniformExecution.original_correct hp as bs cs ds s t
  refine ⟨out, ?_, miss, sound⟩
  simpa only [encBits_apply, encoding] using computes (originalSource p as bs cs ds s t)

/-- The proved native peak allowance, including the actual witness serializer. -/
def peak (p a b c d mu : ℕ) : ℕ := peakCells p a b c d mu + outputTime a b c d

/-- Every native prefix, including arbitrarily long parking after early exit, has an actual
continuing finite state and the source algorithm's derived simultaneous support allowance. -/
theorem original_prefix {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (j : ℕ) :
    let P := BitExecution.program p as.length bs.length cs.length ds.length s t
    let W := globalWidth m p as.length bs.length cs.length ds.length
    ∃ u : FiniteState Basis.standard.genericModel 40,
      FiniteState.run W P.parkHalts.toGeneric j (initState .standard 40
        (quarterInput as bs cs ds)) = Option.some (.inl u) ∧
      u.default = 0 ∧ WordBounded W u ∧ u.pc ≤ labelBound P.parkHalts.toGeneric ∧
      (Interpreter.observedData u).SupportLe (peak p as.length bs.length cs.length ds.length
        (computedBalance (p := p) as bs cs ds s t)) := by
  dsimp only
  obtain ⟨out, y, n, ts, _, _, he, _, _, _, _, support, _, _⟩ :=
    original_output_resources hp as bs cs ds s t
  obtain ⟨v, hv, hsupport⟩ := he.parked_prefix
    (P := fun d => d.SupportLe (peak p as.length bs.length cs.length ds.length
      (computedBalance (p := p) as bs cs ds s t)))
    (fun k u hk hu => (support k u hk hu).1) j
  have hg := runs_toGeneric_iff.mpr hv
  change GenericRAM.Runs _ _ ((State.init (quarterInput as bs cs ds) : State 40).toGeneric
    Basis.standard) _ j at hg
  rw [← denote_initState] at hg
  obtain ⟨u, hu, hd⟩ := FiniteState.exists_run_eq_inl_of_runs hg
  have hw := (wordBounded_initState (B := Basis.standard) (r := 40)
    (quarterInput_fits (p := p) as bs cs ds)).run (p :=
      (BitExecution.program p as.length bs.length cs.length ds.length s t).parkHalts.toGeneric)
      (by simp [initState_pc]) j
  refine ⟨u, hu, FiniteState.default_run hu, (hw.1 u hu).1, (hw.1 u hu).2, ?_⟩
  have hdata : Interpreter.observedData u = v.data := by
    have hregs := congrArg (fun z => z.data.regs) hd
    have hmem := congrArg (fun z => z.data.mem) hd
    exact Data.ext hregs hmem
  exact hdata ▸ hsupport

/-- Every retained prefix of the implemented compacting execution has bit encoding bounded
by computed balance and physical word/address widths, not historical writes or total allocation.
This is a representation bound; scan time and machine workspace remain separately charged. -/
theorem original_compact_encoding {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (j : ℕ) :
    let P := BitExecution.program p as.length bs.length cs.length ds.length s t
    let W := globalWidth m p as.length bs.length cs.length ds.length
    (FiniteState.resultEncoding Basis.standard.encoding
      (Interpreter.compactResult (FiniteState.run W P.parkHalts.toGeneric j
        (initState .standard 40 (quarterInput as bs cs ds))))).length ≤
      stateBound 40 (labelBound P.parkHalts.toGeneric) W
        (peak p as.length bs.length cs.length ds.length
          (computedBalance (p := p) as bs cs ds s t)) := by
  dsimp only
  obtain ⟨u, hu, hz, hw, hpc, hs⟩ := original_prefix hp as bs cs ds s t j
  rw [hu]
  exact Interpreter.compact_encoding_le u hz hs hw hpc

/-- The actual compacting loop includes the runtime executable and width in every retained
prefix. Its complete wire is bounded by derived computed balance, without a space premise. -/
theorem original_compact_loop_encoding {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (j : ℕ) :
    let P := BitExecution.program p as.length bs.length cs.length ds.length s t
    let W := globalWidth m p as.length bs.length cs.length ds.length
    let x : Interpreter.RunInput 40 := (j, (W, P.parkHalts),
      initState .standard 40 (quarterInput as bs cs ds))
    (Interpreter.loopEncoding 40
      (Interpreter.compactRound^[j] (Interpreter.compactLoop (Interpreter.initial x)))).length ≤
      2 * (Interpreter.parametersEncoding 40 (W, P.parkHalts)).length + 1 +
        stateBound 40 (labelBound P.parkHalts.toGeneric) W
          (peak p as.length bs.length cs.length ds.length
            (computedBalance (p := p) as bs cs ds s t)) := by
  dsimp only
  have h := original_compact_encoding hp as bs cs ds s t j
  rw [Interpreter.iterate_compactRound, Interpreter.initial, Interpreter.iterate_round,
    ← FiniteState.run_eq_iterate_stepResult]
  simp only [Interpreter.compactLoop, Interpreter.loopEncoding, length_encPair]
  omega

/-- The maximum used by the compacting machine's actual resource certificate has the same
derived bound, including every prefix and arbitrarily long parked execution. The round-machine
workspace is still charged separately and is not asserted linear in this maximum. -/
theorem original_compact_trajectory {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (T : ℕ) :
    let P := BitExecution.program p as.length bs.length cs.length ds.length s t
    let W := globalWidth m p as.length bs.length cs.length ds.length
    Interpreter.compactTrajectoryLength (T, (W, P.parkHalts),
      initState .standard 40 (quarterInput as bs cs ds)) ≤
      2 * (Interpreter.parametersEncoding 40 (W, P.parkHalts)).length + 1 +
        stateBound 40 (labelBound P.parkHalts.toGeneric) W
          (peak p as.length bs.length cs.length ds.length
            (computedBalance (p := p) as bs cs ds s t)) := by
  apply NativeCertificate.maxStateLength_le
  intro j _
  exact original_compact_loop_encoding hp as bs cs ds s t j

end Cslib.Cryptanalysis.AddXNOR.CompactExecution
