/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal machine normal forms for plain resource bounds

These witness operations normalize a single plain realizing machine. They do not introduce a
second computability calculus or register bridges for automation. The degree operation preserves
the time/workspace degree, including zero; the caller retains its independent output-degree proof.
The charged asymptotic operation preserves independent time and workspace functions and the full
encoded-output charge, using the same machine's space bound together with its time-derived bound.

## Main results

* `Turing.MultiTapeTM.Internal.NormalForm.polyTime`: one polynomial machine bound.
* `Turing.MultiTapeTM.Internal.NormalForm.degree`: degree-preserving machine witnesses.
* `Turing.MultiTapeTM.Internal.NormalForm.inO`: independent charged asymptotic witnesses.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Internal.NormalForm

open Cslib

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Absorb an additive constant into the factor of `n + 1`. -/
theorem le_mul_succ {u A B C n : ℕ} (h : u ≤ A * (n + 1) + B) (hC : A + B ≤ C) :
    u ≤ C * (n + 1) := by
  have hB : B ≤ B * (n + 1) := Nat.le_mul_of_pos_right B (Nat.succ_pos n)
  have : A * (n + 1) + B ≤ (A + B) * (n + 1) := by rw [Nat.add_mul]; omega
  exact h.trans (this.trans (Nat.mul_le_mul_right _ hC))

/-- A polynomial certificate gives one normalized realizing machine at a common polynomial bound. -/
theorem polyTime {f : α → β} (h : ComputableInPolyTime f encIn encMid) :
    ∃ c d : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a))
        (c * ((encIn a).length + 1) ^ d) (c * ((encIn a).length + 1) ^ d) := by
  obtain ⟨t, s, ht, hs, k, State, hfin, tm, htm⟩ := h
  have hp : PolynomiallyBounded fun n => (2 * t n + 3 * s n + 2 * k + 4) +
      (2 * s n + 2 * k * (3 * s n + 2 * k + 3)) := by fun_prop
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp hp
  refine ⟨c, d, k + k, _, inferInstance, tidy false true tm, fun a => ?_⟩
  have hb := hcd (encIn a).length
  exact ((htm a).computesTidily_tidy Bool.false_ne_true).mono
    ((Nat.le_add_right _ _).trans hb) ((Nat.le_add_left _ _).trans hb)

/-- Normalization preserves the cost degree; the original encoded-output degree is separate. -/
theorem degree {f : α → β} {d e : ℕ}
    (h : ComputableInDegree f encIn encMid d e) :
    ∃ t s : α → ℕ, DegreeBounded (fun a => (encIn a).length) t d ∧
      DegreeBounded (fun a => (encIn a).length) s d ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (t a) (s a) := by
  obtain ⟨⟨t, s, ht, hs, k, State, hfin, tm, htm⟩, -⟩ := h
  exact ⟨fun a => 2 * t a + 3 * s a + 2 * k + 4,
    fun a => 2 * s a + 2 * k * (3 * s a + 2 * k + 3),
    (((ht.smul 2).add (hs.smul 3)).add_const _).add_const _,
    (hs.smul 2).add (((hs.smul 3).add_const _).add_const _ |>.smul _),
    k + k, _, inferInstance, tidy false true tm,
    fun a => (htm a).computesTidily_tidy Bool.false_ne_true⟩

/-- Normalize one machine at independent time/workspace bounds, preserving both bounds. -/
private theorem independentBounds {f : α → β} {T S : α → ℕ}
    (c : ℕ)
    (h : ComputableInTimeAndSpace f encIn encMid
      (fun a => c * (T a + 1)) (fun a => c * (S a + 1))) :
    ∃ C, (c ≤ C) ∧ (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (C * (T a + 1))
        (C * (S a + 1))) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  refine ⟨(2 + 3 * k) * c + (5 * k + 4) + ((2 + 6 * k) * c + 2 * k * (2 * k + 3)) + c,
    by omega, ⟨k + k, _, inferInstance, tidy false true tm, fun a => ?_⟩⟩
  · -- the space of the run is at most the smaller of the two space bounds
    set t := c * (T a + 1) with ht
    set s := min (c * (S a + 1)) (k * t + k) with hs
    have hrun : tm.ComputesInTimeAndSpace (encIn a) (encMid (f a)) t s := by
      rcases min_cases (c * (S a + 1)) (k * t + k) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hs, he]
      exacts [htm a, (htm a).space_linear]
    refine (hrun.computesTidily_tidy Bool.false_ne_true).mono ?_ ?_
    · -- time: `2 t + 3 s + O(1)` with `s ≤ k t + k`
      have h₁ : s ≤ k * t + k := min_le_right _ _
      have e : (2 + 3 * k) * c * (T a + 1) = 2 * t + 3 * (k * t) := by rw [ht]; ring
      exact le_mul_succ (A := (2 + 3 * k) * c) (B := 5 * k + 4) (by omega) (by omega)
    · -- space: `O(s + 1)` with `s ≤ c (S + 1)`
      have h₁ : s ≤ c * (S a + 1) := min_le_left _ _
      have h₂ := Nat.mul_le_mul_left k h₁
      have e₁ : 2 * k * (3 * s + 2 * k + 3) = 6 * (k * s) + 2 * k * (2 * k + 3) := by ring
      have e₂ : (2 + 6 * k) * c * (S a + 1) = 2 * (c * (S a + 1)) + 6 * (k * (c * (S a + 1))) := by
        ring
      exact le_mul_succ (A := (2 + 6 * k) * c) (B := 2 * k * (2 * k + 3)) (by omega) (by omega)

/-- Independent asymptotic time/workspace bounds normalize without an output-length premise. -/
theorem bigO {f : α → β} {T S : α → ℕ}
    (h : ComputableInBigO f encIn encMid T S) :
    ∃ c, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (c * (T a + 1))
        (c * (S a + 1)) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨C, _, hC⟩ := independentBounds c hc
  exact ⟨C, hC⟩

/-- Normalize charged bounds, retaining their existing encoded-output bound. -/
theorem inO {f : α → β} {T S : α → ℕ}
    (h : ComputableInO f encIn encMid T S) :
    ∃ c, (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (c * (T a + 1))
        (c * (S a + 1))) ∧ ∀ a, (encMid (f a)).length ≤ c * (S a + 1) := by
  obtain ⟨c, hc, hl⟩ := h
  obtain ⟨C, hle, hC⟩ := independentBounds c hc
  exact ⟨C, hC, fun a => (hl a).trans (Nat.mul_le_mul_right _ hle)⟩

/-- Linear certificates normalize at a common linear bound without changing the encoding. -/
theorem linear {f : α → β} (h : ComputableInLinearTimeAndSpace f encIn encMid) :
    ∃ c, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a))
        (c * ((encIn a).length + 1)) (c * ((encIn a).length + 1)) := bigO h

end Turing.MultiTapeTM.Internal.NormalForm
