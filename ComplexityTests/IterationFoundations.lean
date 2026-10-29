/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Iteration
import Complexity.Foundations.Combinatorics.FunctionalGraph.Checkpoints
import Complexity.Foundations.Combinatorics.FunctionalGraph.Cycle
import Complexity.Foundations.Combinatorics.FunctionalGraph.Powers

/-!
# Iteration foundation clients

Exercise the orbit structure on concrete maps (an identity, a constant map, the empty type),
checkpoint packing on a finite invariant subset of an infinite type and its `L > 0` boundary,
and circuit iteration and retained orbits over a non-Boolean signature, including zero steps.
-/

namespace ComplexityTests.IterationFoundations

open Cslib Cslib.Circuits Cslib.FunctionalGraph Function

/-! ### Orbit structure -/

-- The identity map: every state is periodic of period one, with one distinct power.
example (x : Fin 3) : transientDepth id x = 0 ∧ cycleLength id x = 1 := by
  have hx : x ∈ periodicPts (id : Fin 3 → Fin 3) := mk_mem_periodicPts one_pos rfl
  refine ⟨transientDepth_eq_zero_of_mem_periodicPts _ hx, ?_⟩
  simp [cycleLength_eq_minimalPeriod_of_mem_periodicPts _ hx]

-- The constant map onto `0` on `Fin 2`: state `1` has transient depth one.
private def toZero : Fin 2 → Fin 2 := fun _ => 0

private theorem toZero_iterate_succ (k : ℕ) (x : Fin 2) : toZero^[k + 1] x = 0 := by
  rw [iterate_succ_apply']; rfl

example : transientDepth toZero 1 = 1 := by
  have h0 : toZero^[1] 1 ∈ periodicPts toZero := mk_mem_periodicPts one_pos rfl
  have h1 : (1 : Fin 2) ∉ periodicPts toZero := by
    rintro ⟨p, hp, hper⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have := hper.eq
    rw [toZero_iterate_succ] at this
    exact absurd this (by decide)
  have hle := (iterate_mem_periodicPts_iff toZero 1 1).mp h0
  have hpos : transientDepth toZero 1 ≠ 0 := fun h => h1 ((transientDepth_eq_zero_iff _ _).mp h)
  omega

-- On an empty type the only power is the empty function: `μ + λ = 0 + 1`.
example (f : Empty → Empty) : Nat.card (Set.range fun T : ℕ => f^[T]) = 1 := by
  rw [card_range_iterate]
  simp [maxTransientDepth, cyclePeriod]

-- Distinct small powers differ (`iterate_injective_below`); a repeat on `toZero` bounds the
-- transient depth plus cycle length; and the canonical cycle label lies on the cycle.
example (f : Fin 4 → Fin 4) (i j : Fin (maxTransientDepth f + cyclePeriod f)) (h : i ≠ j) :
    f^[i.val] ≠ f^[j.val] ∧
    transientDepth toZero 1 + cycleLength toZero 1 ≤ 2 ∧
    canonicalCycle (id : Fin 3 → Fin 3) 2 ∈ cycleSet id 2 :=
  ⟨fun he => h (iterate_injective_below f he),
   transientDepth_add_cycleLength_le_of_iterate_eq toZero 1 (i := 1) (j := 2) (by decide) rfl,
   canonicalCycle_mem _ _⟩

/-! ### Checkpoints -/

-- Halving on `ℕ` maps `{0, …, 7}` into itself; the ambient type is infinite.
example : ∃ H : Finset ℕ, H ⊆ Finset.range 8 ∧ H.card * 2 ≤ (Finset.range 8).card ∧
    ∀ x ∈ Finset.range 8, Repeats (· / 2) x 2 ∨ ∃ d < 2 * 2, (· / 2)^[d] x ∈ H :=
  exists_checkpoints _ (Finset.range 8)
    (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)) (by decide)

-- States may live in any universe; the empty invariant set needs no checkpoints.
example {α : Type 2} (f : α → α) : ∃ H : Finset α, H ⊆ ∅ ∧ H.card * 3 ≤ (∅ : Finset α).card ∧
    ∀ x ∈ (∅ : Finset α), Repeats f x 3 ∨ ∃ d < 2 * 3, f^[d] x ∈ H :=
  exists_checkpoints f ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (by decide)

-- The hypothesis `0 < L` is necessary: with `L = 0` no state satisfies the conclusion.
example (f : ℕ → ℕ) (H : Finset ℕ) (x : ℕ) :
    ¬(Repeats f x 0 ∨ ∃ d < 2 * 0, f^[d] x ∈ H) := by
  rintro (⟨i, j, _, hj, _⟩ | ⟨d, hd, _⟩) <;> omega

-- On a finite type: at most `card α / L` checkpoints.
example (f : Fin 6 → Fin 6) : ∃ H : Finset (Fin 6), H.card ≤ 3 ∧
    ∀ x, Repeats f x 2 ∨ ∃ d < 2 * 2, f^[d] x ∈ H := by
  simpa using exists_checkpoints_finite f (L := 2) (by decide)

/-! ### Circuit iteration over a non-Boolean signature -/

/-- One unary operation, interpreted as the successor on `ℕ`. -/
private abbrev succSignature : Signature where
  Op := Unit
  Arity _ := 1

private def succInterpretation : Interpretation succSignature ℕ := fun _ x => x 0 + 1

/-- One successor gate on the single wire. -/
private def succCircuit : Circuit succSignature 1 1 :=
  ⟨.gate .empty ⟨(), fun _ => .input 0⟩, fun _ => .gate 0⟩

-- Evaluation, exact weighted cost, size (including zero steps), and retained orbit prefixes.
example (t : ℕ) :
    (succCircuit.iterate 3).eval succInterpretation ![4] = ![7] ∧
    (succCircuit.iterate 5).program.cost (fun _ => 7) = 35 ∧
    ((succCircuit.iterate 0).size = 0 ∧ (succCircuit.iterate 4).size = 4) ∧
    Synthesis succInterpretation (inputs 1)
      (Synthesis.stages (fun j => Set.range fun i (x : Fin 1 → ℕ) =>
        (succCircuit.eval succInterpretation)^[j] x i) t) (t * succCircuit.size) :=
  ⟨by rw [Circuit.eval_iterate]; decide,
   by rw [Circuit.cost_program_iterate]; rfl,
   by simp [succCircuit],
   Synthesis.orbit (s := inputs 1) succCircuit (fun x => x) (fun i => Set.mem_range_self i) t⟩

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Circuit.cost_program_iterate' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Circuit.cost_program_iterate

end ComplexityTests.IterationFoundations
