/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Balanced
public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import Cslib.Computability.Circuit.Boolean.Complexity

/-!
# Tournaments: selecting a record with the least key

Records made of a key of `k` bits, read as a number with the least significant bit first, and a
payload of `p` bits are compared by their keys. A *tournament* plays keyed minimums
(`keyedMinCircuit k p`) along a balanced binary tree (`Circuit.balanced`): the winner of each match,
the record with the smaller key, meets the winner of the neighbouring match. On `m + 1` records it
outputs one of them whose key is the least (`exists_eval_tournamentCircuit`), the first such record
(`eval_tournamentCircuit_of_first`), with `m` keyed minimums, that is `m (8 k + 3 p + 2)` gates
beyond those computing the records (`size_tournamentCircuit`), and depth at most
`(4 k + 4) ⌈log₂ (m + 1)⌉` above them (`depth_tournamentCircuit_le`). In terms of circuit
complexity, the first least-key record among `m + 1` functions costs at most their complexities plus
`m (8 k + 3 p + 2)` (`exists_complexity_tournament_le`).

The records may be computed by any circuits on shared inputs, or read from the inputs, packed one
after the other (`packedTournamentCircuit`). There is always at least one record; `m = 0`
returns the sole leaf circuit, and the packed version uses wiring alone.

## Main definitions

* `Cslib.Circuits.Boolean.tournamentCircuit`: the tournament among records computed by circuits.
* `Cslib.Circuits.Boolean.packedTournamentCircuit`: the tournament among records given as inputs via
  `Cslib.BitString.packRecords`.

## Main results

* `Cslib.Circuits.Boolean.exists_eval_tournamentCircuit`,
  `Cslib.Circuits.Boolean.exists_eval_packedTournamentCircuit`: the winner is a record with the
  least key.
* `Cslib.Circuits.Boolean.eval_tournamentCircuit_of_first`: ties go to the first record.
* `Cslib.Circuits.Boolean.exists_complexity_tournament_le`: the first least-key record among
  functions costs their complexities plus `m` keyed minimums.
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

/-- Keyed minimums along a balanced tree select the value of the first leaf whose key is the least:
every earlier leaf has a larger key, and no later leaf has a smaller one. -/
private theorem balancedFold_keyedMinFn_first {α : Type*} (f : α → BitString (k + p))
    (e : BitString (k + p)) {l : List α} (hl : l ≠ []) :
    ∃ pre a post, l = pre ++ a :: post ∧ l.balancedFold keyedMinFn e f = f a ∧
      (∀ b ∈ pre, equivFin k (recordKey (f a)) < equivFin k (recordKey (f b))) ∧
      ∀ b ∈ post, equivFin k (recordKey (f a)) ≤ equivFin k (recordKey (f b)) := by
  refine List.balancedFold_induction (p := fun l v => l ≠ [] → ∃ pre a post, l = pre ++ a :: post ∧
      v = f a ∧ (∀ b ∈ pre, equivFin k (recordKey (f a)) < equivFin k (recordKey (f b))) ∧
      ∀ b ∈ post, equivFin k (recordKey (f a)) ≤ equivFin k (recordKey (f b)))
    (fun h => absurd rfl h) (fun a _ => ⟨[], a, [], rfl, rfl, by simp, by simp⟩)
    (fun l₁ l₂ u v h₁ h₂ hu hv _ => ?_) l hl
  obtain ⟨pre₁, a₁, post₁, rfl, rfl, hpre₁, hpost₁⟩ := hu h₁
  obtain ⟨pre₂, a₂, post₂, rfl, rfl, hpre₂, hpost₂⟩ := hv h₂
  by_cases h : BitString.equivFin k (recordKey (f a₁)) ≤ BitString.equivFin k (recordKey (f a₂))
  · refine ⟨pre₁, a₁, post₁ ++ pre₂ ++ a₂ :: post₂, by simp, by rw [keyedMinFn, ite_eq_left h],
      hpre₁, fun b hb => ?_⟩
    simp only [List.mem_append, List.mem_cons] at hb
    rcases hb with (hb | hb) | hb | hb
    · exact hpost₁ b hb
    · exact h.trans (hpre₂ b hb).le
    · rw [hb]
      exact h
    · exact h.trans (hpost₂ b hb)
  · have h' := not_le.1 h
    refine ⟨pre₁ ++ a₁ :: post₁ ++ pre₂, a₂, post₂, by simp, by rw [keyedMinFn, ite_eq_right h],
      fun b hb => ?_, hpost₂⟩
    simp only [List.mem_append, List.mem_cons] at hb
    rcases hb with (hb | hb | hb) | hb
    · exact h'.trans (hpre₁ b hb)
    · rw [hb]
      exact h'
    · exact h'.trans_le (hpost₁ b hb)
    · exact hpre₂ b hb

/-- Keyed minimums along a balanced tree select a value of a leaf whose key is the least. -/
private theorem balancedFold_keyedMinFn {α : Type*} (f : α → BitString (k + p))
    (e : BitString (k + p)) {l : List α} (hl : l ≠ []) :
    (∃ a ∈ l, l.balancedFold keyedMinFn e f = f a) ∧
      ∀ a ∈ l, BitString.equivFin k (recordKey (l.balancedFold keyedMinFn e f)) ≤
        BitString.equivFin k (recordKey (f a)) := by
  obtain ⟨pre, a, post, rfl, hfold, hpre, hpost⟩ := balancedFold_keyedMinFn_first f e hl
  refine ⟨⟨a, by simp, hfold⟩, fun b hb => ?_⟩
  rw [hfold]
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | hb | hb
  · exact (hpre b hb).le
  · rw [hb]
  · exact hpost b hb

/-- A balanced fold of a mapped list is the balanced fold of the list with the composite map. -/
private theorem balancedFold_map {α β γ : Type*} (op : α → α → α) (e : α) (f : β → α)
    (g : γ → β) (l : List γ) : (l.map g).balancedFold op e f = l.balancedFold op e (f ∘ g) := by
  induction l using List.balancedFold.induct with
  | case1 => simp
  | case2 b => simp
  | case3 b b' l ih₁ ih₂ =>
    rw [List.balancedFold_of_two_le (l := (b :: b' :: l).map g) (by simp),
      List.balancedFold_of_two_le (l := b :: b' :: l) (by simp), List.length_map, ← List.map_take,
      ← List.map_drop, ih₁, ih₂]

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
    congr 1 with u v : 2
    exact eval_keyedMinCircuit u v
  refine ⟨i, heval.trans hwin, fun j => ?_⟩
  rw [← hwin]
  exact hle _ (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- **Ties go to the first record.** If record `i` has the least key and every earlier record has a
larger key, the tournament outputs record `i`. -/
theorem eval_tournamentCircuit_of_first (leaves : Fin (m + 1) → Circuit signature n (k + p))
    (x : BitString n) (i : Fin (m + 1))
    (hle : ∀ j, BitString.equivFin k (recordKey ((leaves i).eval interpretation x)) ≤
      BitString.equivFin k (recordKey ((leaves j).eval interpretation x)))
    (hlt : ∀ j < i, BitString.equivFin k (recordKey ((leaves i).eval interpretation x)) <
      BitString.equivFin k (recordKey ((leaves j).eval interpretation x))) :
    (tournamentCircuit k p leaves).eval interpretation x = (leaves i).eval interpretation x := by
  have hop : (fun u v => (keyedMinCircuit k p).eval interpretation (Fin.append u v)) =
      keyedMinFn := by
    funext u v
    exact eval_keyedMinCircuit u v
  rw [tournamentCircuit, Circuit.eval_balanced, hop, List.ofFn_eq_map, balancedFold_map]
  obtain ⟨pre, q, post, hl, hfold, hpre, hpost⟩ := balancedFold_keyedMinFn_first
    ((fun C => C.eval interpretation x) ∘ leaves) ((leaves 0).eval interpretation x)
    (l := List.finRange (m + 1)) (by simp)
  rw [hfold]
  have hsort := List.pairwise_lt_finRange (m + 1)
  rw [hl, List.pairwise_append, List.pairwise_cons] at hsort
  have hmem := List.mem_finRange i
  rw [hl] at hmem
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hi | rfl | hi
  · exact absurd (hle q) (not_le.2 (hpre i hi))
  · rfl
  · exact absurd (hpost i hi) (not_le.2 (hlt q (hsort.2.1.1 i hi)))

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

/-! ### Circuit complexity -/

/-- **A tournament among functions.** Given `m + 1` functions computing records, some function
computed with their gates plus `m` keyed minimums outputs, on every input, the first record whose
key is the least. -/
theorem exists_complexity_tournament_le (r : Fin (m + 1) → BitString n → BitString (k + p)) :
    ∃ g : BitString n → BitString (k + p),
      complexity interpretation g ≤
        ∑ i, complexity interpretation (r i) + m * (8 * k + 3 * p + 2) ∧
      ∀ x i, (∀ j, equivFin k (recordKey (r i x)) ≤ equivFin k (recordKey (r j x))) →
        (∀ j < i, equivFin k (recordKey (r i x)) < equivFin k (recordKey (r j x))) →
          g x = r i x := by
  choose C hC hsize using fun i =>
    exists_computes_size_eq_complexity (I := interpretation) (f := r i)
  refine ⟨(tournamentCircuit k p C).eval interpretation, ?_, fun x i hle hlt => ?_⟩
  · refine (complexity_le_of_computes _ fun _ => rfl).trans (le_of_eq ?_)
    simp only [size_tournamentCircuit, hsize]
  · have hCx : ∀ j, (C j).eval interpretation x = r j x := fun j => hC j x
    rw [eval_tournamentCircuit_of_first C x i (by simpa only [hCx] using hle)
      (by simpa only [hCx] using hlt), hCx]

end Cslib.Circuits.Boolean
