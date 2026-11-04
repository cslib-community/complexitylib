/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.ReadMachine.VirtualWord.Native

/-!
# Existing native framing machine on virtual input

The client is the existing two-output-symbol framing transducer's native machine, including
its pending-output and EOF-flush states.
-/

public section

namespace Cslib.Complexity.VirtualWordNativeTest

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal VirtualWord

/-- The native framing machine's finite control is numbered injectively. -/
noncomputable def control : (Unit × Option Bool × Bool) ↪ ℕ :=
  (Fintype.equivFin _).toEmbedding.trans Fin.valEmbedding

/-- Feed the existing native framing machine through the full substitution compiler. The
result frames the virtual word with no virtual word or output history stored in workspace. -/
theorem native_frame : ∃ time c, ComputableInTimeAndSpace
    (fun p : Simulation.Input => frame (word p.val.2 p.val.1.1 p.val.1.2.1))
    Simulation.encInput encBits time
    (fun p => c * (Native.budget control Encodings.frameT.toTM
      (word p.val.2 p.val.1.1 p.val.1.2.1).length 0 +
        (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  apply Native.computableInSpace_of_computes control Encodings.frameT.toTM encBits _ (fun _ => 0)
  · intro p
    have h := (Encodings.frameT.computesInTimeAndSpace_toTM
      (word p.val.2 p.val.1.1 p.val.1.2.1)).1
    change Encodings.frameT.toTM.Computes _ (Encodings.frameT.run () _) at h
    simpa only [Encodings.frameT_run, encBits_apply] using h
  · intro p
    exact (Encodings.frameT.computesInTimeAndSpace_toTM _).2.2

/-- The unchanged ordinary logspace certificate also suffices, without an exposed native
machine, component certificates or a first-halt clock supplied by the client. -/
theorem ordinary_logspace_client : ∃ time c a C, ComputableInTimeAndSpace
    (fun p : Simulation.Input => frame (word p.val.2 p.val.1.1 p.val.1.2.1))
    Simulation.encInput encBits time
    (fun p => c * (C * (a * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1) +
      Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1) +
      (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  apply Native.of_logSpace
  exact Encodings.frameT.computableInLogSpace (fun w => (Encodings.frameT_run w).symm)

/-- The existing framing machine actually halts and emits its nonconstant framed word. -/
theorem framing_run (w : List Bool) : ∃ t,
    (Native.machine (desc control eBit Encodings.frameT.toTM)).output w t = frame w ∧
    (Native.machine (desc control eBit Encodings.frameT.toTM)).halted
      ((Native.machine (desc control eBit Encodings.frameT.toTM)).run w t) = true := by
  obtain ⟨t, ht, ho⟩ := (Encodings.frameT.computesInTimeAndSpace_toTM w).1
  refine ⟨t, ?_, ?_⟩
  · rw [Native.output_native, ho]
    exact Encodings.frameT_run w
  · rw [Native.halted_native, ht]
    rfl

example : ∃ t, (Native.machine (desc control eBit Encodings.frameT.toTM)).output
    [false, true] t = [true, false, true, true, false] := (framing_run _).imp fun _ h => h.1
example : ∃ t, (Native.machine (desc control eBit Encodings.frameT.toTM)).output
    [] t = [false] := (framing_run _).imp fun _ h => h.1

-- The left boundary discards a fetched physical bit, but can move right again.
example : Native.input ⟨some 0, 0, []⟩ (some true) = none := rfl
example : moveInput 0 none .pos = 1 := rfl
-- Right EOF blocks outward movement; a present false is not EOF.
example : moveInput 3 none .pos = 3 := rfl
example : Native.input ⟨some 0, 3, []⟩ (some false) = some 0 := rfl
example : moveInput 3 (some 0) .pos = 4 := rfl

-- A native-shaped description emits a false symbol on the left boundary and returns right.
private def leftBoundary : Desc := ⟨0, 0,
  [(⟨0, none, []⟩, ⟨.pos, [], some 0, none⟩)]⟩

example : (Native.machine leftBoundary).step [true] ⟨some 0, 0, []⟩ =
    ⟨none, 1, []⟩ := rfl
example : (Native.machine leftBoundary).emit (⟨some 0, 0, []⟩, some true) = [false] := by decide
example : (Native.machine leftBoundary).step [] ⟨none, 1, []⟩ = ⟨none, 1, []⟩ := rfl

-- Nonempty and empty virtual words frame differently, retaining the final false terminator.
example : frame (word [false, true, false] 1 [true]) = [true, false, true, true, false] := rfl
example : frame (word [true] 0 []) = [false] := rfl

end Cslib.Complexity.VirtualWordNativeTest
