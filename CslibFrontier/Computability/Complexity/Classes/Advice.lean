/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial time with an exact advice length

`PWithAdvice length` consists of bit languages decided in polynomial time given an advice
string of exactly `length n` bits at input length `n`. The advice family is arbitrary and need
not be computable. Advice and input are encoded by `encPair encBits encBits`, with framed
advice first; the decider's time is polynomial in that complete encoded pair length.

This is the exact-length advice convention of Goldreich's January 2007 draft Definition 3.5
(`r2.pdf`, PDF p. 4/printed p. 120) [Goldreich2007DraftR2]. For constant advice lengths the
complete input length
differs from the ordinary input length by a constant. This module has no circuit dependency.

## Main definitions

* `Cslib.Complexity.PWithAdvice`: polynomial time with a specified exact advice length.

## Main results

* `Cslib.Complexity.PWithAdvice_zero_eq_P`: no advice recovers P.
* `Cslib.Complexity.P_subset_PWithAdvice`: ignoring advice includes P at every length bound.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Polynomial time with an arbitrary advice family of exactly `length n` bits at length `n`.
The decider reads the framed advice/input pair; the advice family need not be computable. -/
@[expose] def PWithAdvice (length : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ advice : ℕ → List Bool, (∀ n, (advice n).length = length n) ∧
    ∃ A ∈ P (encPair encBits encBits), ∀ x, x ∈ L ↔ (advice x.length, x) ∈ A}

/-- A polynomial-time decider may ignore advice of any specified length. -/
theorem P_subset_PWithAdvice (length : ℕ → ℕ) : P encBits ⊆ PWithAdvice length := by
  rintro L ⟨v, hv, hvL⟩
  refine ⟨fun n => List.replicate (length n) false, ?_,
    {p | v p.2 = true}, ?_, fun x => hvL x⟩
  · intro n
    exact List.length_replicate
  · exact ⟨fun p => v p.2, hv.comp (by fun_prop), fun _ => Iff.rfl⟩

/-- Zero advice is exactly ordinary polynomial time on bit languages. -/
theorem PWithAdvice_zero_eq_P : PWithAdvice (fun _ => 0) = P encBits := by
  ext L
  constructor
  · rintro ⟨advice, hlen, A, ⟨v, hv, hvA⟩, hL⟩
    refine ⟨fun x => v ([], x), hv.comp (by fun_prop), fun x => ?_⟩
    have hempty : advice x.length = [] := List.length_eq_zero_iff.mp (hlen x.length)
    rw [hL x, hempty, hvA]
  · exact fun hL => P_subset_PWithAdvice (fun _ => 0) hL

end Cslib.Complexity
