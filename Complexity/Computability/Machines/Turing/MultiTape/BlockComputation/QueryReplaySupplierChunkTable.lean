/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunkCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAssignmentsCorrect

/-!
# Numeric table answers for the existing packed block gate

On the actual packed interpolation grid, native assignment slices are the existing unpacked
child values, and the checked native parser is the existing checked Boolean gate decoder.
Thus one completed local call returns exactly the requested packed chunk of `codeGate`, without
constructing its truth table or a parallel gate definition.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

open MultiTapeTM Cslib.BitString Cslib.TreeEval.Ary

variable {k s : ℕ} {Q : Type}

/-- A native table call at a grid assignment returns the requested chunk of the existing
Boolean `codeGate`. The actual assignment limit pays all padded child words. -/
theorem answer_grid_eq_codeGate {q r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (counter : ℕ) (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r) :
    let children := fun child : Fin (k * 3 + 1) =>
      Packed.unpackBits hb (blocksEquiv (fun j : Fin ((k * 3 + 1) * r) =>
        (⟨Packed.gridDigit (2 ^ m) counter j, Nat.mod_lt _ (by positivity)⟩ :
          Fin (2 ^ m))) child)
    answer M e ((machine M e).runFrom w
      (prepare e ((m, chunk), (w.length, b, σ, i,
        (2 ^ m) ^ ((k * 3 + 1) * r), counter, r * m))) b) =
      (Packed.packBits hb
        (codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
          (Encoding.encode e) (Encoding.decode e) (i.val + 1) children) chunk).val := by
  have hcapacity := Packed.AssignmentLabels.capacity hb (0 : Fin (k * 3 + 1))
  simp only [Fin.val_zero, zero_mul, zero_add] at hcapacity
  have hf := answer_runFrom_prepare M e w b σ i
    ((2 ^ m) ^ ((k * 3 + 1) * r)) counter (r * m) hb chunk hcapacity
  dsimp only at hf
  rw [Assignments.labels_eq_unpackBits hb hm counter] at hf
  simp only [Encoding.NativeChecked.parse_ofFn] at hf
  simpa only [codeGate, intervalGate, i.isLt, ↓reduceDIte] using hf

end Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk
