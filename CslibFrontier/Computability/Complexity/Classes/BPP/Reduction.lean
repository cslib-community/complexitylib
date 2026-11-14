/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.TruncatedVerifier

/-!
# BPP is closed under polynomial-time reductions

If `A` reduces to `B` in polynomial time and `B` is in `BPP`, then so is `A`
(`Cslib.Complexity.PolyTimeReducible.mem_BPP`): run the decider of `B` on the reduced instance.
The random string for an instance `a` of `A` must have a length fixed by the length of `a` alone,
so it is taken polynomially long enough for the reduced instance, and the decider reads only the
prefix it expects (`Cslib.Complexity.exists_truncated_verifier`). Every prefix is extended by the
same number of strings, so the fractions of right answers are unchanged
(`Cslib.BitString.mul_two_pow_le_mul_card_filter_take`).

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_BPP`: `BPP` is closed under polynomial-time reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **`BPP` is closed under polynomial-time reductions.** The decider of `A` runs the decider of
`B` on the reduced instance and on the prefix of the random string that this decider expects. -/
theorem PolyTimeReducible.mem_BPP (h : PolyTimeReducible enc encB A B) (hB : B ∈ BPP encB) :
    A ∈ BPP enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := hB
  obtain ⟨P, V, hV, hle, hVW⟩ := exists_truncated_verifier hf q hW
  have key (a : α) (b : Bool) (hb : BoundedErrorAt encB q W (f a) b) :
      BoundedErrorAt enc P V a b := by
    simp only [BoundedErrorAt, hVW]
    exact BitString.mul_two_pow_le_mul_card_filter_take (hle a) (fun w => W (f a, w) = b) hb
  exact ⟨P, V, hV, fun a => ⟨fun ha => key a true ((hWB (f a)).1 ((hAB a).1 ha)),
    fun ha => key a false ((hWB (f a)).2 fun hb => ha ((hAB a).2 hb))⟩⟩

end Cslib.Complexity
