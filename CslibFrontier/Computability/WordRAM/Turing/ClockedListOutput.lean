/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Turing.ListOutput
import all CslibFrontier.Computability.WordRAM.Turing.ListOutput
import all CslibFrontier.Computability.WordRAM.Turing
import all CslibFrontier.Computability.GenericRAM.Simulation.Run

/-!
# Charged clocked bit-machine execution with memory-list readback

For a fixed standard word-RAM program, compose the concrete finite-state
simulator with the parked-output reader. Initialization, control dispatch,
checked arithmetic, sparse-memory scans and output extraction all occur in the
implementing multitape machine. No halting, efficiency or output oracle is
needed to construct the certificate. A halting RAM execution subsequently proves
that its result is the returned list.

The bounds expose the actual simulator and reader profiles. In particular,
sparse stores may retain zero bindings: live nonzero support is not a bound on
the encoded simulator state. Programs are fixed parameters of the construction;
this is not a runtime interpreter of an encoded program or a charged compiler
from program-generating input headers.
-/

public section

namespace Cslib.WordRAM.Program

open Turing.MultiTapeTM Cslib.GenericRAM FiniteState NativeCertificate

variable {r : ℕ}

/-- Run a parked program for a finite budget, using the empty initial state on fault.
For a valid halting run, parking ensures that this fallback is never taken. -/
def clockedState (p : Program .standard r) (w n : ℕ) (input : List ℕ) :
    FiniteState Basis.standard.genericModel r :=
  (continuing (FiniteState.run w p.parkHalts.toGeneric n
    (initState .standard r input))).getD (initState .standard r [])

/-- Extract an actual represented list from the clocked state by consecutive memory reads. -/
def clockedList (p : Program .standard r) (w n : ℕ) (input : List ℕ) : List ℕ :=
  parkedOutput p.length (p.clockedState w n input)

/-- Charged finite-state materialization on the framed original word-list input. -/
noncomputable def clockedInitialCertificate : NativeCertificate
    (initState .standard r) (encList encNat) (FiniteState.encoding Basis.standard.encoding) :=
  FiniteState.initConstCertificate Basis.standard.encoding (const 0) (const 0)
    (.ofPolyTime initMemory_polyTime)

/-- One fixed program's actual clocked bit-machine simulation, including initialization. -/
noncomputable def clockedRunCertificate (p : Program .standard r) (w n : ℕ) :
    NativeCertificate (fun input => FiniteState.run w p.parkHalts.toGeneric n
      (initState .standard r input)) (encList encNat)
      (resultEncoding Basis.standard.encoding) :=
  runCertificateOf Basis.standard.encoding Basis.standard.nativePrimitives p.parkHalts.toGeneric
    (const n) (const w) clockedInitialCertificate

/-- Select the parked state using only linear tagged-output processing. -/
noncomputable def clockedStateCertificate (p : Program .standard r) (w n : ℕ) :
    NativeCertificate (p.clockedState w n) (encList encNat)
      (FiniteState.encoding Basis.standard.encoding) :=
  post (post (p.clockedRunCertificate w n)
    (continuingCertificate Basis.standard.encoding).computes)
    (ComputableInDegree.getD (enc₁ := FiniteState.encoding Basis.standard.encoding)
      (enc := encOption (FiniteState.encoding Basis.standard.encoding))
      (initState .standard r [])).inO_one

/-- A standalone reader, so the simulation is performed once before output extraction. -/
noncomputable def clockedReaderCertificate (p : Program .standard r) :
    NativeCertificate (parkedOutput (B := .standard) (r := r) p.length)
      (FiniteState.encoding Basis.standard.encoding) (encList encNat) :=
  parkedOutputCertificate p.length (linear (ComputableInO.of_eq fun _ => rfl))

/-- Concrete clocked execution and list readback on encoded input, with no simulation premise. -/
noncomputable def clockedListCertificate (p : Program .standard r) (w n : ℕ) :
    NativeCertificate (p.clockedList w n) (encList encNat) (encList encNat) :=
  p.clockedReaderCertificate.comp (p.clockedStateCertificate w n)

/-- Explicit charged time profile. Constants for dispatch and literals may depend on `p`;
`runTime` retains the sparse scans and all checked word/address operations. -/
theorem clockedListCertificate_time (p : Program .standard r) (w n : ℕ) (input : List ℕ) :
    (p.clockedListCertificate w n).time input =
      2 * (encList encNat input).length + (clockedInitialCertificate (r := r)).time input +
      runTime Basis.standard.encoding Basis.standard.nativePrimitives p.parkHalts.toGeneric
        (n, (w, initState .standard r input)) +
      p.clockedReaderCertificate.time (p.clockedState w n input) := by
  change _ + (_ + _) + _ + _ = _
  simp only [NativeCertificate.const_time, runTime]
  omega

/-- Conservative simultaneous workspace profile, including encoded intermediate outputs.
This is not a sum of native live cells nor a sharp random-access simulation bound. -/
theorem clockedListCertificate_space (p : Program .standard r) (w n : ℕ) (input : List ℕ) :
    (p.clockedListCertificate w n).space input =
      2 * (encList encNat input).length + (clockedInitialCertificate (r := r)).space input +
      runSpace Basis.standard.encoding Basis.standard.nativePrimitives p.parkHalts.toGeneric
        (n, (w, initState .standard r input)) +
      p.clockedReaderCertificate.space (p.clockedState w n input) := by
  change _ + (_ + _) + _ + _ = _
  simp only [NativeCertificate.const_space, runSpace]
  omega

/-- A genuine halting RAM list execution determines the concrete simulator's readback. -/
theorem clockedList_eq {p : Program .standard r} {w n k : ℕ} {input output : List ℕ}
    (h : ExecutesList w p (State.init input) output k) (hk : k ≤ n) :
    p.clockedList w n input = output := by
  obtain ⟨i, x, hr, hout⟩ := h.runs_parkHalts hk
  have hg := runs_toGeneric_iff.2 hr
  rw [← denote_initState] at hg
  obtain ⟨s, hs, hd⟩ := exists_run_eq_inl_of_runs hg
  have state : p.clockedState w n input = s := by
    rw [clockedState, hs]
    rfl
  have pc : s.pc = p.length + i := congrArg GenericRAM.State.pc hd
  have regs : s.regs = x.regs := congrArg (fun g => g.data.regs) hd
  have mem : (fun a => SparseMemory.read s.default a s.memory) = x.mem :=
    congrArg (fun g => g.data.mem) hd
  rw [clockedList, state, parkedOutput_eq pc, regs, mem]
  exact hout

/-- The physical word bound holds throughout the finite simulation. Stored entries grow
with the instruction budget even when the native program clears cells to zero. -/
theorem clocked_encoding_bound (p : Program .standard r) {w : ℕ} {input : List ℕ}
    (hi : InputFits w input) (j : ℕ) :
    (resultEncoding Basis.standard.encoding
      (FiniteState.run w p.parkHalts.toGeneric j (initState .standard r input))).length ≤
      stateBound r (labelBound p.parkHalts.toGeneric) w (input.length + 1 + j) := by
  have h := (wordBounded_initState (B := .standard) (r := r) hi).length_resultEncoding_run_le
    (p := p.parkHalts.toGeneric) (by simp) j
  change _ ≤ stateBound r (labelBound p.parkHalts.toGeneric) w
    ((SparseMemory.entries (initState .standard r input).memory).length + j) at h
  rw [length_entries_initState] at h
  exact h

end Cslib.WordRAM.Program
