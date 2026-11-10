/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Callbacks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
import Mathlib.Tactic.Linarith

/-!
# Native nondeterministic space complementation

Inductive counting constructs a new finite-state nondeterministic multi-tape machine for the
complement of the language recognized by a machine within space `c₁ * s n + c₂`, for any bound
`s` with `Nat.log2 n ≤ s n`. The construction first counts the input length, then scans compact
configuration graphs of growing radices with the small-register controller, and compiles its
binary choices and read-only input queries to native instructions. The radix grows only after a
certified overflow, so no constructibility of `s` is needed [Immerman1988].

The output machine halts on every branch and obeys an every-prefix work-space bound. The
source need only recognize its language: its branches may run forever. Input and write-only
output are uncharged, exactly as in the existing native `RunsInSpace` convention.

## Main results

* `Turing.MultiTapeNTM.exists_decidesInSpace_compl`: a native recognizer within space
  `c₁ * s n + c₂` has an all-branches-halting native complement decider within space
  `c * (s n + 1)`.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeNTM.ConfigurationGraph Turing.InductiveCounting

variable {α State : Type} {k c₁ c₂ : ℕ} [Finite State]
  {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool} {A : Set α} {s : ℕ → ℕ}

/-- **Immerman–Szelepcsényi, with native machines.** Every language recognized within space
`c₁ * s n + c₂`, for a bound with `Nat.log2 n ≤ s n`, has a complement decider within space
`c * (s n + 1)` whose every branch halts. Both the input encoding and the original all-prefix
work-space convention are preserved, and `s` need not be constructible [Immerman1988]. -/
theorem exists_decidesInSpace_compl
    (hA : ntm.RecognizesInSpace enc A fun a => c₁ * s (enc a).length + c₂)
    (hs : ∀ n, Nat.log2 n ≤ s n) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State')
      (ntm' : MultiTapeNTM k' Bool State') (c : ℕ),
      ntm'.DecidesInSpace enc Aᶜ fun a => c * (s (enc a).length + 1) := by
  classical
  let : Fintype State := Fintype.ofFinite State
  -- a closed round, from the source's space bound
  let J₀ : α → ℕ := fun a => 4 * (c₁ * s (enc a).length + c₂) + 1
  have hJ₀ (a : α) : Closed ntm (roundRadix State (enc a).length (J₀ a)) (enc a) := by
    have hstart := le_startRadix (State := State) (enc a).length
    have hcard := card_lt_startRadix (State := State) (enc a).length
    have hle := startRadix_le_roundRadix (State := State) (enc a).length (J₀ a)
    refine closed_of_runsInSpace (hA a).1 (by omega) (by omega) ?_
    calc 3 ^ (4 * (c₁ * s (enc a).length + c₂) + 1) ≤ 4 ^ J₀ a :=
          Nat.pow_le_pow_left (by omega) _
      _ ≤ roundRadix State (enc a).length (J₀ a) :=
          Nat.le_mul_of_pos_right _ (by omega)
  refine (queryMachine ntm).exists_decidesInSpace query_inSpace (next_inSpace ntm)
    halted_inSpace accept_inSpace (fun _ => (queryMachine ntm).init)
    (fun a => abstractTime k State (J₀ a) (enc a).length)
    (fun a => queryMachine_haltsWithin (hJ₀ a)) (A := Aᶜ) (fun a => ?_)
    (fun a => s (enc a).length + 1) (fun a => Nat.add_le_add_right (hs _) 1)
    ((MultiTapeTM.ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _)
    ⟨(40 * Fintype.card (Register k) + 4) * (8 * c₁ + 8 * c₂ + Fintype.card (Option State) + 7) +
      172, fun a choices => (length_run_le (hJ₀ a) choices).trans ?_⟩
  · exact (not_congr (hA a).2).trans
      (queryMachine_accepts_iff_not_accepts ⟨J₀ a, hJ₀ a⟩).symm
  · have hl := hs (enc a).length
    unfold InductiveCounting.storageBound
    simp only [J₀]
    set x := s (enc a).length
    set L := Nat.log2 (enc a).length
    set q := Fintype.card (Option State)
    set r := 40 * Fintype.card (Register k) + 4
    have h1 : 2 * (4 * (c₁ * x + c₂) + 1) + L + q + 4 ≤ (8 * c₁ + 8 * c₂ + q + 7) * (x + 1) := by
      nlinarith
    have h2 := Nat.mul_le_mul_left r h1
    nlinarith

end Turing.MultiTapeNTM
