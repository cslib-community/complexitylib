/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Savitch
import Mathlib.Tactic.Linarith

/-!
# Savitch's theorem: `NSPACE(s) ⊆ DSPACE(s²)`

A problem decided, or only recognized, by a nondeterministic machine within space `O(s)` is
decided by a deterministic machine within space `O(s ^ 2)`, whenever `log₂ n ≤ s n`
[Savitch1970]. No constructibility of `s` is assumed: the simulating machine
(`Turing.MultiTapeNTM.exists_decidableInTimeAndSpace_sq`) tries growing radices for the
configuration graph and detects when the simulated machine leaves the current radix, as
Immerman's inductive counting does for `Cslib.Complexity.NSPACE_eq_coNSPACE`.

Sipser's Theorem 8.5 assumes `f(n) ≥ n`; the final paragraph of his Section 8.4 (3rd edition,
p. 351) extends it to sublinear bounds `f(n) ≥ log n`. Arora and Barak's Theorem 4.14 assumes a
space-constructible bound `S(n) ≥ log n`. The sources are about deciders on strings; the
statements here also cover nonhalting recognizers and arbitrary encoded instances.

## Main results

* `Cslib.Complexity.mem_DSPACE_sq_of_recognizesInSpace`: a recognizer within space `O(s)`, whose
  branches need not halt, places its problem in `DSPACE(s²)`.
* `Cslib.Complexity.NSPACE_subset_DSPACE_sq`: **Savitch's theorem**, `NSPACE(s) ⊆ DSPACE(s²)`
  for `log₂ n ≤ s n`.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Theorem 8.5 and the final
  paragraph of Section 8.4 (p. 351)][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.14][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {s : ℕ → ℕ}

/-- **Savitch's theorem for recognizers**: a problem recognized by a nondeterministic machine
within space `c₁ * s n + c₂`, whose branches need not halt, is in `DSPACE(s²)` when
`log₂ n ≤ s n` [Savitch1970]. -/
theorem mem_DSPACE_sq_of_recognizesInSpace (hs : ∀ n, Nat.log2 n ≤ s n) {k c₁ c₂ : ℕ}
    {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
    (h : ntm.RecognizesInSpace enc A fun a => c₁ * s (enc a).length + c₂) :
    A ∈ DSPACE enc fun n => s n ^ 2 := by
  obtain ⟨t, c, h'⟩ := MultiTapeNTM.exists_decidableInTimeAndSpace_sq h
  refine mem_DSPACE_iff.mpr ⟨2 * c * (c₁ + 1) ^ 2, 2 * c * (c₂ + 1) ^ 2, t,
    ComputableInTimeAndSpace.mono h' (fun _ => le_rfl) fun a => ?_⟩
  have hl := hs (enc a).length
  generalize s (enc a).length = x at hl ⊢
  have hx : c₁ * x + c₂ + Nat.log2 (enc a).length + 1 ≤ (c₁ + 1) * x + (c₂ + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hsq : (c₁ * x + c₂ + Nat.log2 (enc a).length + 1) ^ 2 ≤
      2 * ((c₁ + 1) ^ 2 * x ^ 2) + 2 * (c₂ + 1) ^ 2 := by
    refine (Nat.pow_le_pow_left hx 2).trans ?_
    nlinarith [two_mul_le_add_sq ((c₁ + 1) * x) (c₂ + 1)]
  calc c * (c₁ * x + c₂ + Nat.log2 (enc a).length + 1) ^ 2
      ≤ c * (2 * ((c₁ + 1) ^ 2 * x ^ 2) + 2 * (c₂ + 1) ^ 2) := Nat.mul_le_mul_left c hsq
    _ = 2 * c * (c₁ + 1) ^ 2 * x ^ 2 + 2 * c * (c₂ + 1) ^ 2 := by ring

/-- **Savitch's theorem**: `NSPACE(s) ⊆ DSPACE(s²)` for every bound with `log₂ n ≤ s n`,
constructible or not [Savitch1970], for the library's native machines and arbitrary injective
instance encodings. -/
theorem NSPACE_subset_DSPACE_sq (hs : ∀ n, Nat.log2 n ≤ s n) :
    NSPACE enc s ⊆ DSPACE enc fun n => s n ^ 2 := by
  rintro A ⟨k, State, _, ntm, c₁, c₂, h⟩
  exact mem_DSPACE_sq_of_recognizesInSpace hs h.recognizesInSpace

end Cslib.Complexity
