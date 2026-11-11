/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Data.Nat.Log
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Walks of bounded length and the midpoint recursion

This file extends upstream `Relation.RelatesInSteps` and `Relation.RelatesWithinSteps` (a walk of
exactly, or at most, `n` steps of a relation `r`) with the facts behind Savitch's theorem.

A walk of at most `n` steps of `r` is a walk of exactly `n` steps of the reflexive closure
`Relation.ReflGen r`, which may stay put. In that form a walk of at most `m + n` steps is exactly
a walk of at most `m` steps to a midpoint followed by a walk of at most `n` steps from it, so a
bound of `2 ^ (i + 1)` reduces to two independent bounds of `2 ^ i`: the recursion that Savitch's
algorithm runs, storing one midpoint per level. On a finite type with `N` elements, everything
reachable is reachable within `N - 1` steps, hence within `2 ^ ⌈log₂ N⌉` steps, which fixes the
recursion depth at `⌈log₂ N⌉`.

Nothing here mentions a machine: these are the facts about the configuration graph that Savitch's
algorithm relies on.

## Main results

* `Relation.relatesWithinSteps_iff_relatesInSteps_reflGen`: a walk of at most `n` steps is a walk
  of exactly `n` steps that may stay put.
* `Relation.RelatesWithinSteps.succ_iff`: one more step of breadth-first search.
* `Relation.RelatesInSteps.add_iff`, `Relation.RelatesWithinSteps.add_iff`: walks split at any
  point; the second is the midpoint recursion.
* `Relation.RelatesInSteps.add_mul_of_cycle`: pumping a cycle any number of times.
* `Relation.RelatesWithinSteps.two_mul_iff`, `Relation.RelatesWithinSteps.two_pow_succ_iff`,
  `Relation.RelatesWithinSteps.one_iff`: the recursion of Savitch's algorithm and its base case.
* `Relation.ReflTransGen.relatesWithinSteps_of_encard_le`,
  `Relation.reflTransGen_iff_relatesWithinSteps`: reachability is reachability within one step
  fewer than the number of elements.
* `Relation.reflTransGen_iff_relatesWithinSteps_two_pow_clog`: the bound Savitch's recursion
  starts from.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.1][Sipser2013]
* [C. H. Papadimitriou, *Computational Complexity*, Section 7.3][Papadimitriou94]
-/

@[expose] public section

namespace Relation

variable {α : Type*} {r : α → α → Prop} {a b c : α} {m n N : ℕ}

/-! ### Walks that may stay put -/

/-- A reflexive relation relates every element to itself in any number of steps. -/
theorem relatesInSteps_self [Std.Refl r] (a : α) : ∀ n, RelatesInSteps r a a n
  | 0 => .refl a
  | n + 1 => .tail a a a n (relatesInSteps_self a n) (refl a)

/-- A walk of at most `n` steps is a walk. -/
theorem RelatesWithinSteps.reflTransGen (h : RelatesWithinSteps r a b n) :
    ReflTransGen r a b := by
  obtain ⟨_, _, h⟩ := h
  exact h.reflTransGen

/-- **A walk of at most `n` steps is a walk of exactly `n` steps that may stay put.** This is how
a walk of bounded length is guessed and checked one step at a time. -/
theorem relatesWithinSteps_iff_relatesInSteps_reflGen :
    RelatesWithinSteps r a b n ↔ RelatesInSteps (ReflGen r) a b n := by
  constructor
  · rintro ⟨m, hm, h⟩
    have h' := (h.map id fun _ _ => ReflGen.single).trans (relatesInSteps_self b (n - m))
    rwa [Nat.add_sub_cancel' hm] at h'
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ _ n _ hstep ih =>
      cases hstep with
      | refl => exact ih.mono n.le_succ
      | single hstep => exact ih.trans (.single hstep)

/-- **One more step of breadth-first search.** An element is reached within `n + 1` steps exactly
when it is reached in at most one step from an element reached within `n` steps. -/
theorem RelatesWithinSteps.succ_iff :
    RelatesWithinSteps r a c (n + 1) ↔ ∃ b, RelatesWithinSteps r a b n ∧ ReflGen r b c := by
  simp only [relatesWithinSteps_iff_relatesInSteps_reflGen]
  exact RelatesInSteps.succ_iff

/-- A walk of at most one step is a step of the reflexive closure. -/
@[simp]
theorem RelatesWithinSteps.one_iff : RelatesWithinSteps r a b 1 ↔ ReflGen r a b := by
  rw [← Nat.zero_add 1, RelatesWithinSteps.succ_iff]
  simp

/-! ### Splitting walks -/

/-- **Walks split at any point.** A walk of `m + n` steps passes through a midpoint after exactly
`m` of them. -/
theorem RelatesInSteps.add_iff :
    RelatesInSteps r a c (m + n) ↔ ∃ b, RelatesInSteps r a b m ∧ RelatesInSteps r b c n := by
  refine ⟨fun h => ?_, fun ⟨_, h₁, h₂⟩ => h₁.trans h₂⟩
  induction n generalizing c with
  | zero => exact ⟨c, h, .refl c⟩
  | succ n ih =>
    rw [← Nat.add_assoc] at h
    obtain ⟨c', h, hstep⟩ := h.succ
    obtain ⟨b, h₁, h₂⟩ := ih h
    exact ⟨b, h₁, .tail b c' c n h₂ hstep⟩

/-- **Pumping a cycle.** A walk of `i` steps to `b` followed by `rounds` rounds of a cycle of `m`
steps at `b` is a walk of `i + rounds * m` steps. -/
theorem RelatesInSteps.add_mul_of_cycle {i : ℕ} (h : RelatesInSteps r a b i)
    (hcycle : RelatesInSteps r b b m) (rounds : ℕ) : RelatesInSteps r a b (i + rounds * m) := by
  induction rounds with
  | zero => simpa using h
  | succ rounds ih =>
    have := ih.trans hcycle
    rwa [Nat.add_assoc, ← Nat.succ_mul] at this

/-- **The midpoint recursion.** A walk of at most `m + n` steps is exactly a walk of at most `m`
steps to some midpoint followed by a walk of at most `n` steps from it. The midpoint is all a
recursive search has to remember. -/
theorem RelatesWithinSteps.add_iff :
    RelatesWithinSteps r a c (m + n) ↔
      ∃ b, RelatesWithinSteps r a b m ∧ RelatesWithinSteps r b c n := by
  simp only [relatesWithinSteps_iff_relatesInSteps_reflGen]
  exact RelatesInSteps.add_iff

/-- The halving form of the midpoint recursion: a bound of `2 n` splits into two independent
bounds of `n`. -/
theorem RelatesWithinSteps.two_mul_iff :
    RelatesWithinSteps r a c (2 * n) ↔
      ∃ b, RelatesWithinSteps r a b n ∧ RelatesWithinSteps r b c n := by
  rw [Nat.two_mul, RelatesWithinSteps.add_iff]

/-- **The recursion of Savitch's algorithm.** A bound of `2 ^ (i + 1)` splits into two
subproblems with bound `2 ^ i`, so the recursion from a bound of `2 ^ i` has depth `i` and each
level stores one midpoint; its base case is `Relation.RelatesWithinSteps.one_iff`
[Sipser, Theorem 8.5][Sipser2013]. -/
theorem RelatesWithinSteps.two_pow_succ_iff {i : ℕ} :
    RelatesWithinSteps r a c (2 ^ (i + 1)) ↔
      ∃ b, RelatesWithinSteps r a b (2 ^ i) ∧ RelatesWithinSteps r b c (2 ^ i) := by
  rw [Nat.pow_succ', RelatesWithinSteps.two_mul_iff]

/-! ### Walks on few elements are short -/

/-- **Everything reachable is reachable within one step fewer than the number of reachable
elements.** A longer walk repeats an element, and the loop between the repetitions can be cut
out (upstream `Relation.ReflTransGen.relatesInSteps_lt_encard`). -/
theorem ReflTransGen.relatesWithinSteps_of_encard_le (h : ReflTransGen r a b)
    (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) : RelatesWithinSteps r a b N := by
  obtain ⟨n, hn, hlt⟩ := h.relatesInSteps_lt_encard
  have : (n : ℕ∞) < (N + 1 : ℕ) := by
    push_cast
    exact hlt.trans_le hN
  exact ⟨n, Nat.lt_succ_iff.mp (by exact_mod_cast this), hn⟩

/-- Reachability is reachability within `N` steps once at most `N + 1` elements are
reachable. -/
theorem reflTransGen_iff_relatesWithinSteps_of_encard_le
    (hN : {x | ReflTransGen r a x}.encard ≤ N + 1) :
    ReflTransGen r a b ↔ RelatesWithinSteps r a b N :=
  ⟨fun h => h.relatesWithinSteps_of_encard_le hN, RelatesWithinSteps.reflTransGen⟩

/-- **On a finite type, reachability is reachability within one step fewer than the number of
elements.** -/
theorem reflTransGen_iff_relatesWithinSteps [Finite α] (hN : Nat.card α ≤ N + 1) :
    ReflTransGen r a b ↔ RelatesWithinSteps r a b N :=
  reflTransGen_iff_relatesWithinSteps_of_encard_le <|
    calc {x | ReflTransGen r a x}.encard ≤ ENat.card α := Set.encard_le_card
      _ = Nat.card α := ENat.card_eq_coe_natCard α
      _ ≤ N + 1 := by exact_mod_cast hN

/-- **The bound Savitch's recursion starts from.** On a finite type with `N` elements, reachability
is reachability within `2 ^ ⌈log₂ N⌉` steps, so the recursion of
`Relation.RelatesWithinSteps.two_pow_succ_iff` decides it at depth `⌈log₂ N⌉`
[Sipser, Theorem 8.5][Sipser2013]. -/
theorem reflTransGen_iff_relatesWithinSteps_two_pow_clog [Finite α] :
    ReflTransGen r a b ↔ RelatesWithinSteps r a b (2 ^ Nat.clog 2 (Nat.card α)) :=
  reflTransGen_iff_relatesWithinSteps ((Nat.le_pow_clog one_lt_two _).trans (Nat.le_succ _))

end Relation
