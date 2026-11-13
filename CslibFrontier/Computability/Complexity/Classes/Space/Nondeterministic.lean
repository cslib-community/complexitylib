/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Nondeterministic space classes and their complements

`Cslib.Complexity.NSPACE enc s` consists of the problems that one finite-state binary
nondeterministic multi-tape machine decides within space `c₁ * s n + c₂`, for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`. As for `Cslib.Complexity.NL`, the
space bound holds along every computation prefix, including rejecting branches; every branch
halts, and on each input some finite time bounds all computation paths; the input tape is
read-only and the output tape write-only. `Cslib.Complexity.coNSPACE enc s` consists of the
complements of the problems in `NSPACE enc s`, under the same encoding.

The Immerman–Szelepcsényi theorem says that `NSPACE(s) = coNSPACE(s)` whenever
`log₂ n ≤ s n` [Immerman1988] [Szelepcsenyi1987]
(`Cslib.Complexity.NSPACE_eq_coNSPACE`). No constructibility of `s` is assumed, following
Immerman's remark after his Theorem 1: the standard space measure bounds every sequence of
choices, so the space may be increased as needed. The complement machines come from
`Turing.MultiTapeNTM.exists_decidesInSpace_compl`, which generalizes Erik Demaine's
inductive-counting construction for logarithmic space.

## Main definitions

* `Cslib.Complexity.NSPACE`: nondeterministic space classes.
* `Cslib.Complexity.coNSPACE`: their complements.

## Main results

* `Cslib.Complexity.NSPACE_mono_of_le_mul_add`: `NSPACE` absorbs constant factors.
* `Cslib.Complexity.NSPACE_mono`, `Cslib.Complexity.NSPACE_mono_of_eventually_le`: monotonicity;
  only the eventual values of the bound matter.
* `Cslib.Complexity.compl_mem_NSPACE_of_recognizesInSpace`, `Cslib.Complexity.compl_mem_NSPACE`:
  closure under complement.
* `Cslib.Complexity.mem_NSPACE_of_recognizesInSpace`: recognizers and deciders give the same class.
* `Cslib.Complexity.NSPACE_eq_coNSPACE`: the Immerman–Szelepcsényi theorem.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*, Theorem 1][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {s : ℕ → ℕ}

/-- The problems decided within space `O(s n)`, that is `c₁ * s n + c₂`, by one finite-state
binary nondeterministic machine, along every computation prefix and with every branch halting,
on instances whose encoding under `enc` has length `n`. -/
def NSPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State)
    (c₁ c₂ : ℕ), ntm.DecidesInSpace enc A fun a => c₁ * s (enc a).length + c₂}

/-- The complements of the problems in `NSPACE enc s`, with the same encoding. -/
def coNSPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) := {A | Aᶜ ∈ NSPACE enc s}

/-- A problem belongs to `coNSPACE` exactly when its complement belongs to `NSPACE`. -/
theorem mem_coNSPACE : A ∈ coNSPACE enc s ↔ Aᶜ ∈ NSPACE enc s := Iff.rfl

/-- `NSPACE` absorbs constant factors: a bound `s₁ n ≤ C * s₂ n + C` puts `NSPACE enc s₁` inside
`NSPACE enc s₂`. -/
theorem NSPACE_mono_of_le_mul_add {s₁ s₂ : ℕ → ℕ} {C : ℕ} (h : ∀ n, s₁ n ≤ C * s₂ n + C) :
    NSPACE enc s₁ ⊆ NSPACE enc s₂ := by
  rintro A ⟨k, State, hfin, ntm, c₁, c₂, hA⟩
  exact ⟨k, State, hfin, ntm, c₁ * C, c₁ * C + c₂,
    hA.mono fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (h _) c₁ c₂⟩

/-- `NSPACE` is monotone in the space bound. -/
theorem NSPACE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : NSPACE enc s₁ ⊆ NSPACE enc s₂ :=
  NSPACE_mono_of_le_mul_add (C := 1) fun n => by have := h n; omega

/-- `NSPACE` only depends on the space bound eventually: the finitely many other values are
absorbed by the additive constant. -/
theorem NSPACE_mono_of_eventually_le {s₁ s₂ : ℕ → ℕ} (h : ∀ᶠ n in Filter.atTop, s₁ n ≤ s₂ n) :
    NSPACE enc s₁ ⊆ NSPACE enc s₂ :=
  let ⟨_, hC⟩ := Nat.exists_le_mul_add_of_eventually_le h
  NSPACE_mono_of_le_mul_add hC

/-- **The complement of a problem recognized within space `O(s)` is decided within space `O(s)`**,
every branch halting, when `log₂ n ≤ s n`. The recognizer's branches may run forever. -/
theorem compl_mem_NSPACE_of_recognizesInSpace (hs : ∀ n, Nat.log2 n ≤ s n) {k c₁ c₂ : ℕ}
    {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
    (h : ntm.RecognizesInSpace enc A fun a => c₁ * s (enc a).length + c₂) :
    Aᶜ ∈ NSPACE enc s := by
  obtain ⟨k', State', hfin, ntm', c, h'⟩ := MultiTapeNTM.exists_decidesInSpace_compl h hs
  exact ⟨k', State', hfin, ntm', c, c, h'.mono fun a => by rw [Nat.mul_add, Nat.mul_one]⟩

/-- **Nondeterministic space is closed under complement**, when `log₂ n ≤ s n`. -/
theorem compl_mem_NSPACE (hs : ∀ n, Nat.log2 n ≤ s n) (h : A ∈ NSPACE enc s) :
    Aᶜ ∈ NSPACE enc s := by
  obtain ⟨k, State, _, ntm, c₁, c₂, hA⟩ := h
  exact compl_mem_NSPACE_of_recognizesInSpace hs hA.recognizesInSpace

/-- **A recognizer within space `O(s)` gives a decider**, every branch halting, when
`log₂ n ≤ s n`. Its branches may run forever. -/
theorem mem_NSPACE_of_recognizesInSpace (hs : ∀ n, Nat.log2 n ≤ s n) {k c₁ c₂ : ℕ}
    {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
    (h : ntm.RecognizesInSpace enc A fun a => c₁ * s (enc a).length + c₂) : A ∈ NSPACE enc s := by
  simpa only [compl_compl] using compl_mem_NSPACE hs (compl_mem_NSPACE_of_recognizesInSpace hs h)

/-- Complementation preserves membership in nondeterministic space. -/
theorem compl_mem_NSPACE_iff (hs : ∀ n, Nat.log2 n ≤ s n) :
    Aᶜ ∈ NSPACE enc s ↔ A ∈ NSPACE enc s := by
  constructor
  · intro h
    simpa only [compl_compl] using compl_mem_NSPACE hs h
  · exact compl_mem_NSPACE hs

/-- **The Immerman–Szelepcsényi theorem**: `NSPACE(s) = coNSPACE(s)` for every bound with
`log₂ n ≤ s n`, constructible or not [Immerman, Theorem 1][Immerman1988], for the library's native
machines and arbitrary injective instance encodings. -/
theorem NSPACE_eq_coNSPACE (hs : ∀ n, Nat.log2 n ≤ s n) : NSPACE enc s = coNSPACE enc s := by
  ext A
  exact (compl_mem_NSPACE_iff hs).symm

end Cslib.Complexity
