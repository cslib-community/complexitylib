/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Advice
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Countable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Set.Image

/-!
# One bit of advice decides some undecidable languages

Every bit language whose membership depends only on input length is decidable in polynomial
time with one advice bit: at length `n`, the bit gives membership of all words of that length.
There are more such languages than native machine deciders, so some are undecidable.

This is the undecidability endpoint of Goldreich's January 2007 draft Theorem 3.7 (`r2.pdf`,
PDF p. 6/printed p. 122) [Goldreich2007DraftR2]. Advice is arbitrary, not uniformly computable.
This does not prove
the arbitrary advice-length hierarchy or strict containment of one-bit advice in P/poly.

## Main results

* `Cslib.Complexity.length_preimage_mem_PWithAdvice_one`: one bit suffices for any set of lengths.
* `Cslib.Complexity.exists_mem_PWithAdvice_one_not_isDecidable`: an undecidable, length-dependent
  bit language with one bit of advice.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Any set of input lengths is decided with one bit of advice, read from the advice head. -/
theorem length_preimage_mem_PWithAdvice_one (A : Set ℕ) :
    List.length ⁻¹' A ∈ PWithAdvice (fun _ => 1) := by
  classical
  refine ⟨fun n => [decide (n ∈ A)], fun _ => rfl,
    {p | p.1.headD false = true}, ?_, ?_⟩
  · exact ⟨fun p => p.1.headD false, by fun_prop, fun _ => Iff.rfl⟩
  · intro x
    simp

private theorem exists_not_isDecidable_length_preimage :
    ∃ A : Set ℕ, ¬ IsDecidable (List.length ⁻¹' A : Set (List Bool)) encBits := by
  classical
  by_contra! h
  let C := {L : Set (List Bool) // IsDecidable L encBits}
  have : Countable C := (countable_setOf_isDecidable encBits).to_subtype
  let f : Set ℕ → C := fun A => ⟨List.length ⁻¹' A, h A⟩
  have hlen : Function.Surjective (List.length : List Bool → ℕ) :=
    fun n => ⟨List.replicate n false, by simp⟩
  have hf : Function.Injective f := fun A B hAB =>
    Set.preimage_injective.mpr hlen (congrArg Subtype.val hAB)
  obtain ⟨code, hcode⟩ := exists_injective_nat C
  exact Function.cantor_injective (code ∘ f) (hcode.comp hf)

/-- One bit of advice decides a length-dependent language with no native machine decider. -/
theorem exists_mem_PWithAdvice_one_not_isDecidable :
    ∃ L ∈ PWithAdvice (fun _ => 1), ¬ IsDecidable L encBits ∧
      ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L) := by
  obtain ⟨A, hA⟩ := exists_not_isDecidable_length_preimage
  refine ⟨List.length ⁻¹' A, length_preimage_mem_PWithAdvice_one A, hA, ?_⟩
  intro x y hlen
  simp only [Set.mem_preimage, hlen]

end Cslib.Complexity
