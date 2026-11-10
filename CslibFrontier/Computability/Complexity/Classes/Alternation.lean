/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Alternating time and space classes

The parametric classes of alternating machines (`Turing.MultiTapeATM`, in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating`) with a binary alphabet and
finitely many states [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]. They are relative to an encoding `enc : α ↪ List Bool` of
instances, with a bound of the length `n` of the encoded instance, up to constants
`c₁ * t n + c₂`, like `Cslib.Complexity.NTIME` and `Cslib.Complexity.NSPACE`:

* `Cslib.Complexity.ATIME enc t`: decided within time `O(t n)`
  (`Turing.MultiTapeATM.DecidesInTime`): every computation path of that length has halted, and the
  instance is a member exactly when the machine accepts it. Acceptance is the least fixed point
  of the labelling (`Turing.MultiTapeATM.Accepts`).
* `Cslib.Complexity.ASPACE enc s`: decided within space `O(s n)`
  (`Turing.MultiTapeATM.DecidesInSpace`): every computation path visits at most that many
  work-tape cells, and every branch halts.

Space counts visited work-tape cells: the input tape is read-only and the output tape write-only.
A time bound gives a space bound, so `ATIME t ⊆ ASPACE t` (`Cslib.Complexity.ATIME_subset_ASPACE`).

The input head moves one cell per step, as for the deterministic and nondeterministic machines. A
machine running within time `t n < n` therefore reads only a prefix of its input, and `ATIME` below
linear time is not the alternating logarithmic time of machines with random access to their input.

Alternating polynomial time `Cslib.Complexity.AP` is the union of the classes `ATIME (n ^ k)`
(`Cslib.Complexity.mem_AP_iff_exists_mem_ATIME`). It is `PSPACE` (`Cslib.Complexity.AP_eq_PSPACE`,
in `CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch`). The space classes
`Cslib.Complexity.APSPACE` and `Cslib.Complexity.AL` are in
`CslibFrontier.Computability.Complexity.Classes.Alternation.Space`.

## Main definitions

* `Cslib.Complexity.ATIME`, `Cslib.Complexity.ASPACE`: alternating time and space classes.
* `Cslib.Complexity.AP`: alternating polynomial time.

## Main results

* `Cslib.Complexity.ATIME_subset_of_le_mul_add`, `Cslib.Complexity.ASPACE_subset_of_le_mul_add`:
  constant factors and additive constants are absorbed.
* `Cslib.Complexity.ATIME_mono`, `Cslib.Complexity.ASPACE_mono`: monotonicity.
* `Cslib.Complexity.ATIME_subset_ASPACE`: alternating time is within alternating space.
* `Cslib.Complexity.mem_AP_iff_exists_mem_ATIME`: `AP` is the union of the classes
  `ATIME (n ^ k)`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Alternating polynomial time** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09]: the problems decided within polynomial time by an
alternating machine with a binary alphabet and finitely many states, with respect to the encoding
`enc` of instances. -/
def AP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | MultiTapeATM.DecidableInPolyTime A enc}

/-- **Alternating time** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: the problems decided within time `O(t n)`, that is
`c₁ * t n + c₂`, by an alternating machine with a binary alphabet and finitely many states, on
instances whose encoding under `enc` has length `n`. -/
def ATIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, MultiTapeATM.DecidableInTime A enc fun a => c₁ * t (enc a).length + c₂}

/-- **Alternating space** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: the problems decided within space `O(s n)`, that is
`c₁ * s n + c₂`, by one alternating machine with a binary alphabet and finitely many states, along
every computation path and with every branch halting, on instances whose encoding under `enc` has
length `n`. -/
def ASPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State)
    (c₁ c₂ : ℕ), atm.DecidesInSpace enc A fun a => c₁ * s (enc a).length + c₂}

/-- A bound `t₁ ≤ c * t₂ + d` turns `c₁ * t₁ + c₂` into a bound of the same shape in `t₂`. -/
private theorem mul_add_le_mul_add {t₁ t₂ c d : ℕ} (h : t₁ ≤ c * t₂ + d) (c₁ c₂ : ℕ) :
    c₁ * t₁ + c₂ ≤ c₁ * c * t₂ + (c₁ * d + c₂) := by
  have := Nat.mul_le_mul_left c₁ h
  rw [Nat.mul_add, ← Nat.mul_assoc] at this
  omega

/-- `ATIME` depends on the time bound only up to a constant factor and an additive constant. -/
theorem ATIME_subset_of_le_mul_add {t₁ t₂ : ℕ → ℕ} (c d : ℕ) (h : ∀ n, t₁ n ≤ c * t₂ n + d) :
    ATIME enc t₁ ⊆ ATIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfin, atm, hA⟩
  exact ⟨c₁ * c, c₁ * d + c₂, k, State, hfin, atm,
    hA.mono fun a => mul_add_le_mul_add (h _) c₁ c₂⟩

/-- `ASPACE` depends on the space bound only up to a constant factor and an additive constant. -/
theorem ASPACE_subset_of_le_mul_add {s₁ s₂ : ℕ → ℕ} (c d : ℕ) (h : ∀ n, s₁ n ≤ c * s₂ n + d) :
    ASPACE enc s₁ ⊆ ASPACE enc s₂ := by
  rintro A ⟨k, State, hfin, atm, c₁, c₂, hA⟩
  exact ⟨k, State, hfin, atm, c₁ * c, c₁ * d + c₂,
    hA.mono fun a => mul_add_le_mul_add (h _) c₁ c₂⟩

/-- `ATIME` is monotone in the time bound. -/
theorem ATIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) : ATIME enc t₁ ⊆ ATIME enc t₂ :=
  ATIME_subset_of_le_mul_add 1 0 fun n => by simpa using h n

/-- `ASPACE` is monotone in the space bound. -/
theorem ASPACE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : ASPACE enc s₁ ⊆ ASPACE enc s₂ :=
  ASPACE_subset_of_le_mul_add 1 0 fun n => by simpa using h n

/-- **Alternating time is within alternating space**: a decider within time `c₁ * t n + c₂` with
`k` work tapes decides within space `k * (c₁ * t n + c₂ + 1)`. -/
theorem ATIME_subset_ASPACE {t : ℕ → ℕ} : ATIME enc t ⊆ ASPACE enc t := by
  rintro A ⟨c₁, c₂, k, State, hfin, atm, hA⟩
  refine ⟨k, State, hfin, atm, k * c₁, k * (c₂ + 1), hA.decidesInSpace.mono fun a => ?_⟩
  rw [Nat.mul_assoc, ← Nat.mul_add, Nat.add_assoc]

/-- **`AP` is the union of the classes `ATIME (n ^ k)`** [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981]. -/
theorem mem_AP_iff_exists_mem_ATIME : A ∈ AP enc ↔ ∃ k, A ∈ ATIME enc (· ^ k) := by
  constructor
  · rintro ⟨t, ht, hA⟩
    obtain ⟨c, d, hle⟩ := ht.exists_le
    obtain ⟨k, State, hfin, atm, hA⟩ := hA
    exact ⟨d, c * 2 ^ d, c, k, State, hfin, atm,
      hA.mono fun a => (hle a).trans (Nat.mul_add_one_pow_le_two_pow c d _)⟩
  · rintro ⟨d, c₁, c₂, hA⟩
    exact ⟨_, by growth_poly, hA⟩

end Cslib.Complexity
