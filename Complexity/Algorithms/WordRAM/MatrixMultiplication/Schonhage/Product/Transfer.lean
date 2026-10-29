/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Memory

/-!
# Protected original-input and coordinate transfers

## Main results

* `QueriedProduct.exec_saveInput`: snapshot the complete original input by actual native copying.
* `QueriedProduct.exec_prepareQueries`: adapt real coordinates to the router's input convention.

These internal execution interfaces derive copy separation and arithmetic fits from the
original numerical parameters. Their memory conclusions describe the actual executed state.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Original input, its protected copy and the coordinate adaptation all fit the allocation. -/
public theorem transfer_bounds (L m N Q : ℕ) :
    inputEnd m N Q ≤ snapshotBase L m N Q ∧
      snapshotBase L m N Q + inputEnd m N Q ≤ memoryEnd L m N Q ∧
      5 + 2 * Q ≤ snapshotBase L m N Q + queryInputBase m N ∧
      snapshotBase L m N Q + queryInputBase m N + 2 * Q ≤ memoryEnd L m N Q := by
  have h10 := Nat.zero_le (10 ^ L)
  unfold memoryEnd stampBase scratchBase outputBase groupedBase originalBase codeBase
    offsetBase snapshotBase queryInputBase inputEnd
  omega

/-- Any allocated endpoint fits without assumptions about intermediate machine states. -/
public theorem allocated_fits {w L m N Q a : ℕ} (hfit : Fits w (wordBudget L m N Q))
    (ha : a ≤ memoryEnd L m N Q + 16) : Fits w a := by
  apply (caller_fits hfit).of_le
  omega

/-- The actual input snapshot uses three argument instructions and the native copy loop. -/
public theorem exec_saveInput {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w saveInput x y (7 * inputEnd m N Q + 10) ∧
      Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem 0 (snapshotBase L m N Q) (inputEnd m N Q) := by
  let z := ((x.set source 0).set destination (snapshotBase L m N Q)).set length (inputEnd m N Q)
  have hz : ExecWithin (B := .standard) w (ram[
      source ← zero; destination ← snapshot; length ← inputSize ]) x z 3 := by
    ram_eval [z, hp.zero, hp.snapshot, hp.inputSize, source, destination, length,
      zero, snapshot, inputSize]
  have zp : Parameters L m N Q z :=
    ((hp.set_work source (by decide) 0).set_work destination (by decide) _).set_work
      length (by decide) _
  have hb := transfer_bounds L m N Q
  have hi : Fits w (inputEnd m N Q) := allocated_fits hfit (by omega)
  have hs : Fits w (snapshotBase L m N Q + inputEnd m N Q) :=
    allocated_fits hfit (by omega)
  obtain ⟨y, he, hm, hf⟩ := exec_copyCall z (allocated_fits hfit (by omega))
    (by simpa [z, source, destination, length] using hi)
    (by simpa [z, source, destination, length] using hs)
    (Or.inl (by simpa [z, source, destination, length] using hb.1))
  refine ⟨y, ?_, zp.reframe (fun i hi => hf i (by omega)), ?_⟩
  · have hlen : z.regs length = inputEnd m N Q := by simp [z]
    rw [hlen] at he
    exact (hz.seq he).mono (by omega)
  · simpa [z, source, destination, length] using hm

/-- Real coordinate words are copied from the protected original input to address five.
The caller's original prefix remains protected in its snapshot for final restoration. -/
public theorem exec_prepareQueries {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prepareQueries x y (14 * Q + 10) ∧ Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem
        (snapshotBase L m N Q + queryInputBase m N) 5 (2 * Q) := by
  let z := ((x.set source (snapshotBase L m N Q + queryInputBase m N)).set destination 5).set
    length (Q * 2)
  have hb := transfer_bounds L m N Q
  have hs : Fits w (snapshotBase L m N Q + queryInputBase m N) :=
    allocated_fits hfit (by omega)
  have hn : Fits w (Q * 2) := allocated_fits hfit (by
    have h10 := Nat.zero_le (10 ^ L)
    unfold memoryEnd stampBase scratchBase outputBase groupedBase originalBase codeBase
      offsetBase snapshotBase inputEnd
    omega)
  have hz : ExecWithin (B := .standard) w (ram[
      source ← snapshot + queryOffset; destination ← five; length ← queryCount * two ])
      x z 3 := by
    ram_eval [z, hp.snapshot, hp.queryOffset, hp.five, hp.queryCount, hp.two, hs, hn,
      source, destination, length, snapshot, queryOffset, five, queryCount, two]
  have zp : Parameters L m N Q z :=
    ((hp.set_work source (by decide) _).set_work destination (by decide) _).set_work
      length (by decide) _
  obtain ⟨y, he, hm, hf⟩ := exec_copyCall z (allocated_fits hfit (by omega))
    (by simpa [z, source, destination, length, Nat.mul_comm] using
      allocated_fits hfit (show snapshotBase L m N Q + queryInputBase m N + 2 * Q ≤
        memoryEnd L m N Q + 16 by omega))
    (by simpa [z, source, destination, length, Nat.mul_comm] using
      allocated_fits hfit (show 5 + 2 * Q ≤ memoryEnd L m N Q + 16 by omega))
    (Or.inr (Or.inl (by
      simpa [z, source, destination, length, Nat.mul_comm] using hb.2.2.1)))
  refine ⟨y, ?_, zp.reframe (fun i hi => hf i (by omega)), ?_⟩
  · have hlen : z.regs length = Q * 2 := by simp [z]
    rw [hlen] at he
    exact (hz.seq he).mono (by omega)
  · simpa [z, source, destination, length, Nat.mul_comm] using hm

/-- Restore the entire original prefix through the same actual copy routine. Answers and
all memory outside the prefix remain unchanged. -/
public theorem exec_restoreInput {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w restoreInput x y (7 * inputEnd m N Q + 10) ∧
      Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem (snapshotBase L m N Q) 0 (inputEnd m N Q) := by
  let z := ((x.set source (snapshotBase L m N Q)).set destination 0).set length (inputEnd m N Q)
  have hz : ExecWithin (B := .standard) w (ram[
      source ← snapshot; destination ← zero; length ← inputSize ]) x z 3 := by
    ram_eval [z, hp.zero, hp.snapshot, hp.inputSize, source, destination, length,
      zero, snapshot, inputSize]
  have zp : Parameters L m N Q z :=
    ((hp.set_work source (by decide) _).set_work destination (by decide) 0).set_work
      length (by decide) _
  have hb := transfer_bounds L m N Q
  have hi : Fits w (inputEnd m N Q) := allocated_fits hfit (by omega)
  have hs : Fits w (snapshotBase L m N Q + inputEnd m N Q) :=
    allocated_fits hfit (by omega)
  obtain ⟨y, he, hm, hf⟩ := exec_copyCall z (allocated_fits hfit (by omega))
    (by simpa [z, source, destination, length] using hs)
    (by simpa [z, source, destination, length] using hi)
    (Or.inr (Or.inl (by simpa [z, source, destination, length] using hb.1)))
  refine ⟨y, ?_, zp.reframe (fun i hi => hf i (by omega)), ?_⟩
  · have hlen : z.regs length = inputEnd m N Q := by simp [z]
    rw [hlen] at he
    exact (hz.seq he).mono (by omega)
  · simpa [z, source, destination, length] using hm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
