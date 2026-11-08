/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Initialized
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Bounds
public import Complexity.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Initialized batch execution at every admitted physical width

The prefix and charged halt share one final state containing all wanted answers.
The halt returns the exclusive end of the answer array, including for an empty batch.
The program never reads width. The original-input admission run therefore controls
every wider successful prefix, including its words and memory support.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One shared preparation, all sparse queries and one charged halt. -/
@[expose] def timeBound {L : ℕ} (m t : ℕ) (qs : List (OutStr L)) : ℕ :=
  preparationTime L m t + queryTime m t qs + 1

/-- The complete fixed native code has at most this many slots, including its final halt. -/
theorem program_size_le : program.size + 1 ≤ 4096 := by decide

/-- The original-input batch is independent of physical width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by decide

/-- Original-input execution, ordered answer memory and charged halt at every admitted width.
The returned scalar is the exclusive answer-array end, while signed answers remain in memory. -/
theorem runs_wide {W L m t A B : ℕ} (hmL : m ≤ L) (qs : List (OutStr L))
    (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t qs.length A B ≤ W) :
    InputFits W (input m t qs a b) ∧
    ∃ y n, n + 1 ≤ timeBound m t qs ∧
      Runs W (program.program Reg.output) (State.init (input m t qs a b))
        ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.output) (State.init (input m t qs a b))
        (memoryEnd L m t qs.length) (n + 1) ∧
      y.Bounded W ∧ y.regs Reg.output = memoryEnd L m t qs.length ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m t qs.length + i.val) =
        Signed.encode (BoxQuery.queryValue m t (qs.get i)
          (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)))) ∧
      BoxQuery.Readback m t (directoryBase L qs.length) (valueBase L m t qs.length)
        5 (5 + 10 ^ L) (fun τ => a (Encoding.leafIndex τ))
          (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L qs.length ≤ p ∧ p < memoryEnd L m t qs.length) →
        y.mem p = (State.init (input m t qs a b) : State registers).data.mem p) := by
  obtain ⟨_, haddr, hmag⟩ := admission_bounds hW
  have hwidth : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  obtain ⟨hi, y, ⟨n, hn, he⟩, hy, _, _, _, ho, hvalues, hr, hf⟩ :=
    exec_input hmL qs hη a b ha hb (by simpa only [hwidth] using haddr) hmag
  refine ⟨by simpa only [hwidth] using hi, y, n, ?_, ?_, ?_,
    by simpa only [hwidth] using hy, ho, hvalues, hr, hf⟩
  · unfold timeBound
    omega
  · simpa only [hwidth, Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program Reg.output) (Program.Contains.self _).append_left
  · simpa only [hwidth, ho, State.init] using he.executes Reg.output

/-- Every actual wider prefix has bounded original-input words and zero memory above
the same support bound, independently of the larger physical width. -/
theorem prefix_bounded {W L m t A B : ℕ} (hmL : m ≤ L) (qs : List (OutStr L))
    (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t qs.length A B ≤ W) (s : State registers) (steps : ℕ)
    (hr : Runs W (program.program Reg.output) (State.init (input m t qs a b)) s steps) :
    (∀ i, s.data.regs i < wordBound L m t qs.length A B) ∧
      (∀ p, s.data.mem p < wordBound L m t qs.length A B) ∧
      ∀ p, wordBound L m t qs.length A B ≤ p → s.data.mem p = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_wide hmL qs hη a b ha hb le_rfl
  exact hr.prefix_bounds_init (Code.not_readsWidth_program program_not_readsWidth Reg.output)
    hW hi halt (pow_admissionWidth_lt_wordBound L m t qs.length A B).le

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
