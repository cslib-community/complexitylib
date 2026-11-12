/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Lookup
import CslibFrontier.Computability.Circuit.Complexity.Composition
import Mathlib.Tactic.GCongr

/-!
# Lookup tables, local maps and composition with retained inputs

These clients bound a two-bit table with three output bits, the adjacent exclusive ors of a word
(each output reads two inputs), an answer bit selected by an input bit, and the unmasking
`x ↦ x ⊕ (m(x), …, m(x))` of a word by a computed mask bit: computing `m` costs its own
complexity, and the unmasking layer reads the retained input next to `m(x)`.
-/

namespace CslibFrontierTests.CircuitLookup

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

/-- A two-bit table with outputs `x₀ ∧ x₁`, `x₀ ∨ x₁` and `x₀ ⊕ x₁`. -/
private def gates (x : Fin 2 → Bool) : Fin 3 → Bool := ![x 0 && x 1, x 0 || x 1, x 0 ^^ x 1]

-- The shared decoder: four minterms of five gates, and three disjunctions of at most five gates.
example : complexity interpretation gates ≤ 35 :=
  complexity_le_lookup gates

-- Output `i` of the adjacent exclusive ors reads inputs `i` and `i + 1`, so the map costs at most
-- `29` gates per output.
example (n : ℕ) :
    complexity interpretation (fun (x : Fin (n + 1) → Bool) (i : Fin n) =>
      x i.castSucc ^^ x i.succ) ≤ n * 29 :=
  complexity_le_mul_of_forall_dependsOn (t := 2) _ fun i =>
    ⟨{i.castSucc, i.succ}, card_le_two, fun x y h => by
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      simp only [h _ (Or.inl rfl), h _ (Or.inr rfl)]⟩

-- One selector bit chooses between two answer bits: a multiplexer of at most `11` gates.
example : complexity interpretation (single fun zx : Fin (2 + 1) → Bool =>
    zx (Fin.castAdd 1 (if zx (Fin.natAdd 2 0) then 1 else 0))) ≤ 11 :=
  (complexity_select_le (q := 2) (univ : Finset (Fin 1))
    fun y => if y ⟨0, mem_univ 0⟩ then 1 else 0).trans (by simp)

/-- Exclusive or of each of the first `n` inputs with the last one. -/
private def unmask {n : ℕ} (y : Fin (n + 1) → Bool) (i : Fin n) : Bool :=
  y (Fin.castAdd 1 i) ^^ y (Fin.natAdd n 0)

-- Unmasking by a computed bit costs the mask plus `29` gates per output.
example {n : ℕ} (m : BooleanFunction n) :
    complexity interpretation (fun x : Fin n → Bool => fun i => x i ^^ m x) ≤
      complexity interpretation (single m) + n * 29 := by
  have hu : complexity interpretation (unmask (n := n)) ≤ n * 29 :=
    complexity_le_mul_of_forall_dependsOn (t := 2) _ fun i =>
      ⟨{Fin.castAdd 1 i, Fin.natAdd n 0}, card_le_two, fun x y h => by
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at h
        simp only [unmask, h _ (Or.inl rfl), h _ (Or.inr rfl)]⟩
  have heq : (fun x : Fin n → Bool => fun i => x i ^^ m x) =
      fun x => unmask (Fin.append x (single m x)) := by
    funext x i
    simp [unmask, Fin.append_left, Fin.append_right]
  rw [heq]
  exact (complexity_comp_append_le (single m) unmask).trans (Nat.add_le_add_left hu _)

end CslibFrontierTests.CircuitLookup
