/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic
public import Complexity.DataStructure.Queue.WordRAM.Model
import Complexity.Tactic.Realize

/-!
# A physical transfer step with explicit queue count words

The input words are front count, rear count, base, capacity and payload. The source step reads
one rear-array cell, writes the next front cell, and returns updated counts as values. No count
is stored in physical memory. The shared realization judgment certifies every native arithmetic
and staging instruction while retaining literal whole-memory semantics.

## Main definitions

* `Input`, `counts`: five input words and two faithfully encoded returned counts.
* `move`, `domain`: one physical step and the original two-array capacity/room domain.

## Main results

* `realizes_move`: one uniform emitter before runtime values and register layouts.
* `runClient_move`, `valid_move`, `move_modifies`: exact history, validity and physical frame.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Five live input words: front count, rear count, base, capacity, reserved payload. -/
abbrev Input := Fin 5 → ℕ

/-- One exact source transfer step; the counts are values, not cells. -/
def move (d : Input) : Memory.Prog (ℕ × ℕ) := do
  let v ← Memory.read (d 2 + d 3 + (d 1 - 1))
  Memory.write (d 2 + d 0) v
  pure (d 0 + 1, d 1 - 1)

/-- The old capacity and allocation envelope, without extra count cells or zero memory. -/
def domain (_w : ℕ) (d : Input) (s : Memory.State) : Prop :=
  0 < d 1 ∧ d 0 + d 1 ≤ d 3 ∧ d 2 + 2 * d 3 ≤ s.frontier

/-- The two returned count words. -/
def counts : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  appendWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- One emitter precedes every count, layout, width and initial memory. All native arithmetic
and vector staging are charged by the memory-query budget; the body performs two queries. -/
theorem realizes_move : Realizes .exact move (.refl Input) counts
    domain (fun _ _ => 0) := by
  change Realizes .exact move (.refl (Fin 5 → ℕ)) counts _ _
  realize
  · exact h.1
  · exact hmem.fits_of_lt_frontier (by rcases h with ⟨hb, hc, hf⟩; omega)
  · exact hmem.fits_of_lt_frontier (by rcases h with ⟨hb, hc, hf⟩; omega)
  · exact (show Fits w (d 3) from hwords 3).of_le (by rcases h with ⟨hb, hc, hf⟩; omega)

/-- The exact source history, including the physical read and write. -/
theorem runClient_move (w : ℕ) (d : Input) (s : Memory.State) :
    (Memory.spec w).runClient s (move d) =
      ((d 0 + 1, d 1 - 1),
        ⟨Function.update s.mem (d 2 + d 0) (s.mem (d 2 + d 3 + (d 1 - 1))), s.frontier⟩,
        [.read (d 2 + d 3 + (d 1 - 1)),
          .write (d 2 + d 0) (s.mem (d 2 + d 3 + (d 1 - 1)))]) := rfl

/-- Every access is within the original two arrays, including the written value's fit. -/
theorem valid_move {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (h : domain w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (move d)) := by
  change (d 2 + d 3 + (d 1 - 1) < s.frontier) ∧
    (d 2 + d 0 < s.frontier ∧ Fits w (s.mem (d 2 + d 3 + (d 1 - 1)))) ∧ True
  exact ⟨by rcases h with ⟨hb, hc, hf⟩; omega,
    ⟨by rcases h with ⟨hb, hc, hf⟩; omega, hw.mem_fits _⟩, trivial⟩

/-- The literal physical-memory frame remains the old `2*C` block. -/
theorem move_modifies {w : ℕ} {d : Input} {s : Memory.State} (h : domain w d s) :
    Modifies (Block.mk (d 2) (2 * d 3)).footprint s.mem
      ((Memory.spec w).clientState s (move d)).mem := by
  exact Modifies.write_of_owns ⟨by omega, by rcases h with ⟨hb, hc, hf⟩; omega⟩ _

end Cslib.DataStructure.Queue.WordRAM.RegisterMetadata
