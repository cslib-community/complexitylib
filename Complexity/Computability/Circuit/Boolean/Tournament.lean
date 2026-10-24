/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Balanced
public import Complexity.Computability.Circuit.Boolean.Comparison

/-!
# Tournaments: selecting a record with the least key

Records made of a key of `k` bits, read as a number with the least significant bit first, and a
payload of `p` bits are compared by their keys. A *tournament* plays keyed minimums
(`keyedMinCircuit k p`) along a balanced binary tree (`Circuit.balanced`): the winner of each match,
the record with the smaller key, meets the winner of the neighbouring match. On `m + 1` records it
outputs one of them whose key is the least (`exists_eval_tournamentCircuit`), with `m` keyed
minimums, that is `m (8 k + 3 p + 2)` gates beyond those computing the records
(`size_tournamentCircuit`), and depth at most `(4 k + 4) ⌈log₂ (m + 1)⌉` above them
(`depth_tournamentCircuit_le`).

The records may be computed by any circuits on shared inputs, or read from the inputs, packed one
after the other (`packedTournamentCircuit`). There is always at least one record; `m = 0`
returns the sole leaf circuit, and the packed version uses wiring alone. The least-key theorem
does not specify which tied record wins.

## Main definitions

* `Cslib.Circuits.Boolean.tournamentCircuit`: the tournament among records computed by circuits.
* `Cslib.Circuits.Boolean.packedTournamentCircuit`: the tournament among records given as inputs via
  `Cslib.BitString.packRecords`.

## Main results

* `Cslib.Circuits.Boolean.exists_eval_tournamentCircuit`,
  `Cslib.Circuits.Boolean.exists_eval_packedTournamentCircuit`: the winner is a record with the
  least key.
* `Cslib.Circuits.Boolean.size_tournamentCircuit`,
  `Cslib.Circuits.Boolean.size_packedTournamentCircuit`: `m` keyed minimums for `m + 1` records.
* `Cslib.Circuits.Boolean.depth_tournamentCircuit_le`,
  `Cslib.Circuits.Boolean.depth_packedTournamentCircuit_le`: logarithmic depth.

## References

Adapted from Samuel Schlesinger's earlier Complexitylib module
`Circuits/KeyedMinimumTournament`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset BitString

variable {k p n m : ℕ}

/-- The tournament among the records computed by the circuits `leaves`: keyed minimums along a
balanced binary tree. -/
def tournamentCircuit (k p : ℕ) (leaves : Fin (m + 1) → Circuit signature n (k + p)) :
    Circuit signature n (k + p) :=
  Circuit.balanced (keyedMinCircuit k p) (leaves 0) (List.ofFn leaves)

/-- Keyed minimums along a balanced tree select a value of a leaf whose key is the least. -/
private theorem balancedFold_keyedMinFn {α : Type*} (f : α → BitString (k + p))
    (e : BitString (k + p)) {l : List α} (hl : l ≠ []) :
    (∃ a ∈ l, l.balancedFold keyedMinFn e f = f a) ∧
      ∀ a ∈ l, BitString.equivFin k (recordKey (l.balancedFold keyedMinFn e f)) ≤
        BitString.equivFin k (recordKey (f a)) := by
  refine List.balancedFold_induction (p := fun l v => l ≠ [] → (∃ a ∈ l, v = f a) ∧
      ∀ a ∈ l, BitString.equivFin k (recordKey v) ≤ BitString.equivFin k (recordKey (f a)))
    (fun h => absurd rfl h) (fun a _ => ⟨⟨a, by simp⟩, fun b hb => by simp_all⟩)
    (fun l₁ l₂ u v h₁ h₂ hu hv _ => ?_) l hl
  obtain ⟨⟨a, ha, rfl⟩, hu⟩ := hu h₁
  obtain ⟨⟨b, hb, rfl⟩, hv⟩ := hv h₂
  refine ⟨?_, fun c hc => ?_⟩
  · rcases keyedMinFn_eq_or_eq (f a) (f b) with h | h
    · exact ⟨a, List.mem_append_left _ ha, h⟩
    · exact ⟨b, List.mem_append_right _ hb, h⟩
  · rcases List.mem_append.1 hc with hc | hc
    · exact (equivFin_recordKey_keyedMinFn_le_left _ _).trans (hu c hc)
    · exact (equivFin_recordKey_keyedMinFn_le_right _ _).trans (hv c hc)

/-- **The tournament selects a least key.** Its output is the record computed by one of the
circuits, whose key is at most the key of every record. -/
theorem exists_eval_tournamentCircuit (leaves : Fin (m + 1) → Circuit signature n (k + p))
    (x : BitString n) :
    ∃ i, (tournamentCircuit k p leaves).eval interpretation x = (leaves i).eval interpretation x ∧
      ∀ j, BitString.equivFin k (recordKey ((leaves i).eval interpretation x)) ≤
        BitString.equivFin k (recordKey ((leaves j).eval interpretation x)) := by
  obtain ⟨⟨C, hC, hwin⟩, hle⟩ := balancedFold_keyedMinFn (fun C => C.eval interpretation x)
    ((leaves 0).eval interpretation x) (l := List.ofFn leaves) (by simp)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hC
  have heval : (tournamentCircuit k p leaves).eval interpretation x =
      (List.ofFn leaves).balancedFold keyedMinFn ((leaves 0).eval interpretation x)
        fun C => C.eval interpretation x := by
    rw [tournamentCircuit, Circuit.eval_balanced]
    congr 1
    funext u v
    exact eval_keyedMinCircuit u v
  refine ⟨i, heval.trans hwin, fun j => ?_⟩
  rw [← hwin]
  exact hle _ (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- A tournament among `m + 1` records uses `m` keyed minimums beyond the circuits computing the
records. -/
@[simp] theorem size_tournamentCircuit (leaves : Fin (m + 1) → Circuit signature n (k + p)) :
    (tournamentCircuit k p leaves).size =
      ∑ i, (leaves i).size + m * (8 * k + 3 * p + 2) := by
  rw [tournamentCircuit, Circuit.size_balanced _ _ (by simp), List.length_ofFn, List.map_ofFn,
    List.sum_ofFn, size_keyedMinCircuit, Nat.add_sub_cancel]
  rfl

/-- **A tournament has logarithmic depth.** Among `m + 1` records computed by circuits of depth at
most `D`, it has depth at most `D + (4 k + 4) ⌈log₂ (m + 1)⌉`. -/
theorem depth_tournamentCircuit_le (leaves : Fin (m + 1) → Circuit signature n (k + p)) {D : ℕ}
    (h : ∀ i, (leaves i).depth ≤ D) :
    (tournamentCircuit k p leaves).depth ≤ D + (4 * k + 4) * Nat.clog 2 (m + 1) := by
  refine (Circuit.depth_balanced_le _ _ (D := D) (fun C hC => ?_) (by simp)).trans ?_
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hC
    exact h i
  · rw [List.length_ofFn]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (depth_keyedMinCircuit_le k p)) D

/-! ### Records given as inputs -/

/-- The tournament among `m + 1` records given as inputs, packed one after the other. -/
def packedTournamentCircuit (k p m : ℕ) : Circuit signature ((m + 1) * (k + p)) (k + p) :=
  tournamentCircuit k p fun i => Circuit.wiring signature fun j => finProdFinEquiv (i, j)

/-- **The packed tournament selects a least key.** -/
theorem exists_eval_packedTournamentCircuit (records : Fin (m + 1) → BitString (k + p)) :
    ∃ i, (packedTournamentCircuit k p m).eval interpretation (packRecords records) = records i ∧
      ∀ j, BitString.equivFin k (recordKey (records i)) ≤
        BitString.equivFin k (recordKey (records j)) := by
  obtain ⟨i, hi, hle⟩ := exists_eval_tournamentCircuit
    (fun i => Circuit.wiring signature fun j => finProdFinEquiv (i, j)) (packRecords records)
  simp only [Circuit.eval_wiring, packRecords_comp] at hi hle
  exact ⟨i, hi, hle⟩

/-- The packed tournament among `m + 1` records of key width `k` and payload width `p` has size
`m * (8 * k + 3 * p + 2)`. -/
@[simp] theorem size_packedTournamentCircuit (k p m : ℕ) :
    (packedTournamentCircuit k p m).size = m * (8 * k + 3 * p + 2) := by
  simp [packedTournamentCircuit]

/-- **The packed tournament has logarithmic depth**: `(4 k + 4) ⌈log₂ (m + 1)⌉`. -/
theorem depth_packedTournamentCircuit_le (k p m : ℕ) :
    (packedTournamentCircuit k p m).depth ≤ (4 * k + 4) * Nat.clog 2 (m + 1) := by
  simpa [packedTournamentCircuit] using depth_tournamentCircuit_le (k := k) (p := p) (D := 0)
    (fun i => Circuit.wiring signature fun j => finProdFinEquiv (i, j)) fun i => by simp

end Cslib.Circuits.Boolean
