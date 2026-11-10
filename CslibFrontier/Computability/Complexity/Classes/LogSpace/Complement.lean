/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic

/-!
# Complementary nondeterministic logarithmic space

`coNL enc` consists of the complements of problems in the native machine class `NL enc`.
It uses exactly the same encoding, every-prefix work-space measure and all-branches halting
convention as `NL`.

`NL` is the nondeterministic space class of the bound `Nat.log2`
(`Cslib.Complexity.NL_eq_NSPACE`), so the Immerman–Szelepcsényi theorem for nondeterministic
space (`Cslib.Complexity.NSPACE_eq_coNSPACE`) gives `NL = coNL`. Its source machine may even be a
recognizer with nonterminating branches; the constructed machine halts on every branch.

## Main definitions

* `Cslib.Complexity.coNL`: complements of nondeterministic logarithmic-space problems.

## Main results

* `Cslib.Complexity.mem_coNL`: membership is membership of the complement in `NL`.
* `Cslib.Complexity.compl_mem_coNL_iff`: the corresponding double-complement equivalence.
* `Cslib.Complexity.NL_eq_NSPACE`: `NL` is `NSPACE(log₂ n)`.
* `Cslib.Complexity.compl_mem_NL`: native nondeterministic logarithmic-space complement closure.
* `Cslib.Complexity.NL_eq_coNL`: the Immerman–Szelepcsényi theorem.
* `Cslib.Complexity.mem_NL_of_recognizesInSpace`: recognizers and deciders give the same class.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The problems whose complements belong to native nondeterministic logarithmic space
[Sipser, Section 8.6][Sipser2013]. -/
def coNL (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NL enc}

/-- A problem belongs to `coNL` exactly when its complement belongs to `NL`. -/
theorem mem_coNL : A ∈ coNL enc ↔ Aᶜ ∈ NL enc := Iff.rfl

/-- Complementing a problem in `NL` gives a problem in `coNL`, and conversely. -/
theorem compl_mem_coNL_iff : Aᶜ ∈ coNL enc ↔ A ∈ NL enc := by
  rw [mem_coNL, compl_compl]

/-- **`NL` is `NSPACE(log₂ n)`**: the bounds `c * (log₂ n + 1)` and `c₁ * log₂ n + c₂` give the
same problems. -/
theorem NL_eq_NSPACE : NL enc = NSPACE enc Nat.log2 := by
  ext A
  constructor
  · rintro ⟨k, State, hfin, ntm, c, hA⟩
    exact ⟨k, State, hfin, ntm, c, c, hA.mono fun a => by rw [Nat.mul_add, Nat.mul_one]⟩
  · rintro ⟨k, State, hfin, ntm, c₁, c₂, hA⟩
    exact ⟨k, State, hfin, ntm, c₁ + c₂, hA.mono fun a => by nlinarith⟩

/-- **Native nondeterministic logarithmic space is closed under complement.** The constructed
machine halts on every branch and obeys the same input/output space convention. -/
theorem compl_mem_NL (h : A ∈ NL enc) : Aᶜ ∈ NL enc := by
  rw [NL_eq_NSPACE] at h ⊢
  exact compl_mem_NSPACE (fun _ => le_rfl) h

/-- Complementation preserves membership in native nondeterministic logarithmic space. -/
theorem compl_mem_NL_iff : Aᶜ ∈ NL enc ↔ A ∈ NL enc := by
  constructor
  · intro h
    simpa only [compl_compl] using compl_mem_NL h
  · exact compl_mem_NL

/-- **`NL = coNL`**, the Immerman–Szelepcsényi theorem for the library's native machines and
arbitrary injective instance encodings: the case `s = log₂` of
`Cslib.Complexity.NSPACE_eq_coNSPACE`. -/
theorem NL_eq_coNL : NL enc = coNL enc := by
  ext A
  rw [mem_coNL, NL_eq_NSPACE]
  conv_lhs => rw [NSPACE_eq_coNSPACE (fun _ => le_rfl)]
  exact mem_coNSPACE

/-- A logarithmic-space recognizer, even with nonterminating branches, recognizes a problem
decidable within logarithmic space with every branch halting. -/
theorem mem_NL_of_recognizesInSpace {k c : ℕ} {State : Type} [Finite State]
    {ntm : Turing.MultiTapeNTM k Bool State}
    (h : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    A ∈ NL enc := by
  rw [NL_eq_NSPACE]
  exact mem_NSPACE_of_recognizesInSpace (fun _ => le_rfl) (c₁ := c) (c₂ := c)
    (h.mono fun a => by rw [Nat.mul_add, Nat.mul_one])

end Cslib.Complexity
