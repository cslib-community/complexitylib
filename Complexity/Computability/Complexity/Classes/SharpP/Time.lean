/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Machine
import Complexity.Computability.Complexity.Classes.SharpP.Characterization
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Time-bounded accepting-path counting

`SharpTIME enc t` consists of the natural-valued functions counting the accepting terminal
branches of one fixed finite-control binary native List-choice machine. Every branch halts by
`c₁ * t n + c₂` on instances whose encoding has length `n`; the constants and machine are fixed
before the input. Transition occurrences, including repeated identical actions, are separate
choices. Acceptance means the terminal output is exactly `[true]`.

This reuses the native counting model of `SharpP.Machine`. The machine is globally nonblocking,
as in the existing native characterization of `SharpP`; all-branch halting is required on the
image of the instance encoding. Increasing a sufficient clock does not multiply the count:
a terminal branch is counted once, with no extra choices after its first halt. Thus `SharpTIME`
is distinct from a count of freely padded fair-coin strings.

## Main definitions

* `Cslib.Complexity.SharpTIME`: time-bounded accepting terminal-path counting.

## Main results

* `Cslib.Complexity.mem_SharpTIME`: the fixed-machine and exact terminal-count contract.
* `Cslib.Complexity.SharpTIME_mono`: larger sufficient clocks preserve membership and counts.
* `Cslib.Complexity.SharpTIME.subset_SharpP`: every polynomial-time slice belongs to `SharpP`.
* `Cslib.Complexity.mem_SharpP_iff_exists_mem_SharpTIME`: their union is exactly `SharpP`.

## References

The occurrence-labelled counting model and its verifier correspondence are developed in
`MultiTape.Counting` and `Classes.SharpP.Machine`, with the source references recorded there.
-/

public section

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type}

/-- Exact accepting terminal-branch counts of fixed nonblocking finite-control native machines
whose every branch halts within time `c₁ * t n + c₂`. Repeated transition occurrences retain
multiplicity, while post-halting padding contributes no new branch. -/
@[expose] def SharpTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (α → ℕ) :=
  {f | ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (machine : MultiTapeCTM k Bool State), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (c₁ * t (enc a).length + c₂) (Cfg.init machine.initial (enc a)) ∧
        machine.acceptCount (c₁ * t (enc a).length + c₂)
          (Cfg.init machine.initial (enc a)) = f a}

variable {enc : α ↪ List Bool} {t : ℕ → ℕ} {f : α → ℕ}

/-- The native machine, its constants and finite control are chosen before the input; the count
is the accepting terminal-path count at the all-branches clock. -/
theorem mem_SharpTIME : f ∈ SharpTIME enc t ↔
    ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (machine : MultiTapeCTM k Bool State), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (c₁ * t (enc a).length + c₂) (Cfg.init machine.initial (enc a)) ∧
        machine.acceptCount (c₁ * t (enc a).length + c₂)
          (Cfg.init machine.initial (enc a)) = f a :=
  Iff.rfl

/-- Monotonicity uses stability of terminal counts after a sufficient all-branches clock, rather
than freely padding accepting coin strings. -/
theorem SharpTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    SharpTIME enc t₁ ⊆ SharpTIME enc t₂ := by
  rintro f ⟨c₁, c₂, k, State, hfinite, machine, hnon, hm⟩
  refine ⟨c₁, c₂, k, State, hfinite, machine, hnon, fun a => ?_⟩
  obtain ⟨hhalt, hcount⟩ := hm a
  have hle : c₁ * t₁ (enc a).length + c₂ ≤ c₁ * t₂ (enc a).length + c₂ :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _
  refine ⟨hhalt.mono hle, ?_⟩
  change machine.branchCount (· == [true]) _ _ = f a
  rw [hhalt.branchCount_eq hle]
  exact hcount

/-- A polynomial-time accepting-path counter belongs to the existing verifier-defined `#P`.
This is the forward native-machine correspondence, with its affine polynomial clock. -/
theorem SharpTIME.subset_SharpP (d : ℕ) : SharpTIME enc (· ^ d) ⊆ SharpP enc := by
  rintro f ⟨c₁, c₂, k, State, hfinite, machine, _, hm⟩
  let p : Polynomial ℕ := Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂
  have hp (n : ℕ) : p.eval n = c₁ * n ^ d + c₂ := by simp [p]
  have heq : f = fun a => machine.acceptCount (p.eval (enc a).length)
      (Cfg.init machine.initial (enc a)) := by
    funext a
    rw [hp]
    exact (hm a).2.symm
  rw [heq]
  exact machine.acceptCount_mem_SharpP enc p

/-- The existing verifier-defined `#P` is the union of the polynomial-time native counting
classes. The all-branches clock can be enlarged to an affine power without changing the count. -/
theorem mem_SharpP_iff_exists_mem_SharpTIME :
    f ∈ SharpP enc ↔ ∃ d, f ∈ SharpTIME enc (· ^ d) := by
  constructor
  · intro hf
    obtain ⟨k, State, hfinite, machine, p, hnon, hm⟩ :=
      mem_SharpP_iff_exists_machine.mp hf
    obtain ⟨c, d, hbound⟩ :=
      polynomiallyBounded_iff_le.mp (PolynomiallyBounded.polynomial_eval p)
    refine ⟨d, c * 2 ^ d, c, k, State, hfinite, machine, hnon, fun a => ?_⟩
    obtain ⟨hhalt, hcount⟩ := hm a
    have hle : p.eval (enc a).length ≤ c * 2 ^ d * (enc a).length ^ d + c :=
      (hbound _).trans (Nat.mul_add_one_pow_le_two_pow c d _)
    refine ⟨hhalt.mono hle, ?_⟩
    change machine.branchCount (· == [true]) _ _ = f a
    rw [hhalt.branchCount_eq hle]
    exact hcount
  · rintro ⟨d, hf⟩
    exact SharpTIME.subset_SharpP d hf

end Cslib.Complexity
