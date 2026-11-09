/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Interpreter.CompactRun
public import CslibFrontier.Computability.WordRAM.ListOutput.Prefixes
public import CslibFrontier.Computability.WordRAM.SupportTrace
import all CslibFrontier.Computability.WordRAM.Interpreter.Compact
import all CslibFrontier.Computability.GenericRAM.Simulation.Finite
import all CslibFrontier.Computability.GenericRAM.Simulation.Turing
import all CslibFrontier.Computability.WordRAM.Turing
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.WordRAM.Defs

/-!
# Live-support bounds for actually compacted encodings

The normalizing machine has been implemented separately. Only for that changed
execution may its retained entry count now be bounded by total-memory support.
This module charges the encoded program counter, all registers, default and
physical address/value widths. It bounds representations, not the interpreter's
internal scanning time or workspace.
-/

public section
namespace Cslib.WordRAM.Interpreter
open Cslib.GenericRAM Turing.MultiTapeTM

/-- The concrete word-RAM data denoted by the finite sparse state. -/
def observedData {r : ℕ} (s : FiniteState Basis.standard.genericModel r) : Data r :=
  ⟨s.regs, fun a => SparseMemory.read s.default a s.memory⟩

/-- Actual deletion turns support into a stored-entry bound, including after zero writes. -/
theorem length_entries_compactState {r M : ℕ}
    (s : FiniteState Basis.standard.genericModel r) (hzero : s.default = 0)
    (hs : (observedData s).SupportLe M) :
    (SparseMemory.entries (compactState s).memory).length ≤ M := by
  obtain ⟨S, hcard, hcover⟩ := hs
  change (SparseMemory.entries (SparseMemory.compact s.default s.memory)).length ≤ M
  rw [hzero]
  exact (SparseMemory.length_compact_le 0 s.memory S
    (fun a ha => hcover a (by simpa only [observedData, hzero] using ha))).trans hcard

/-- Encoded normalized outcomes are bounded by actual support and physical word/address widths.
No historical stored-entry count occurs; no bit-machine workspace bound is inferred from this. -/
theorem compact_encoding_le {r W L M : ℕ}
    (s : FiniteState Basis.standard.genericModel r) (hzero : s.default = 0)
    (hs : (observedData s).SupportLe M) (hw : WordBounded W s) (hpc : s.pc ≤ L) :
    (FiniteState.resultEncoding Basis.standard.encoding
      (Option.some (.inl (compactState s)))).length ≤ stateBound r L W M := by
  have hE := length_entries_compactState s hzero hs
  have hc : WordBounded W (compactState s) :=
    ⟨hw.regs_lt, hw.default_lt, fun e he =>
      hw.entries_lt e (SparseMemory.mem_entries_compact.mp he).1⟩
  have hlen := FiniteState.length_encoding_le Basis.standard.encoding (compactState s)
    (bound := W) (fun i => length_encNat_le_of_lt_two_pow (hc.regs_lt i))
  have hpcl : (encNat s.pc).length ≤ (encNat L).length := by
    simp only [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le_size hpc
  have hdef : (Basis.standard.encoding.value (compactState s).default).length ≤ W :=
    length_encNat_le_of_lt_two_pow hc.default_lt
  have hkey : SparseMemory.maxKeyLength Basis.standard.encoding.address
      (compactState s).memory ≤ W :=
    listMax_le (fun e he => length_encNat_le_of_lt_two_pow (hc.entries_lt e he).1)
  have hval : SparseMemory.maxValueLength Basis.standard.encoding.value
      (compactState s).memory ≤ W :=
    listMax_le (fun e he => length_encNat_le_of_lt_two_pow (hc.entries_lt e he).2)
  have hmul := Nat.mul_le_mul hE
    (show 4 * SparseMemory.maxKeyLength Basis.standard.encoding.address (compactState s).memory +
      2 * SparseMemory.maxValueLength Basis.standard.encoding.value (compactState s).memory + 3 ≤
        6 * W + 3 by omega)
  dsimp only [compactState] at hE hdef hkey hval hmul
  simp only [FiniteState.resultEncoding, encOption_some, encSum_inl, List.length_cons,
    stateBound, compactState] at hlen ⊢
  omega

end Cslib.WordRAM.Interpreter
