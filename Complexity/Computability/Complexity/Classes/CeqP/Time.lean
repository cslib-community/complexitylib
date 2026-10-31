/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CeqP
public import Complexity.Computability.Complexity.Classes.SharpP.Time

/-!
# Time-bounded exact counting

`Cslib.Complexity.CeqTIME enc t` is a time-parameterized counterpart of `Cslib.Complexity.CeqP`.
Its members are the problems decided by equality of two counts in
`Cslib.Complexity.SharpTIME enc t`. Each count is the number of accepting terminal branches of a
fixed nonblocking native counting machine whose branches all halt within time `O(t n)`. This
follows the two-count characterization of `C=P`
(`Cslib.Complexity.mem_CeqP_iff_exists_SharpP`).

At polynomial clocks this is `CeqP`: `Cslib.Complexity.mem_CeqP_iff_exists_mem_CeqTIME`, by the
equality of `Cslib.Complexity.SharpP` with the union of the classes `SharpTIME (n ^ d)`. The two
counts may first need different polynomial clocks; the larger clock serves both
(`Cslib.Complexity.SharpTIME_pow_mono`).

## Main definitions

* `Cslib.Complexity.CeqTIME`: equality of two terminal-path counts within time `O(t n)`.

## Main results

* `Cslib.Complexity.CeqTIME_mono`: monotonicity in the clock.
* `Cslib.Complexity.mem_CeqP_iff_exists_mem_CeqTIME`: `C=P` is the union of the classes
  `CeqTIME (n ^ d)`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {t : ℕ → ℕ}

/-- `C₌TIME[t]`: the problems whose members are the instances where two counts in
`SharpTIME enc t` agree. -/
def CeqTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ f ∈ SharpTIME enc t, ∃ g ∈ SharpTIME enc t, ∀ a, a ∈ A ↔ f a = g a}

/-- `CeqTIME` is monotone in the clock. -/
theorem CeqTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    CeqTIME enc t₁ ⊆ CeqTIME enc t₂ := fun _ ⟨f, hf, g, hg, hA⟩ =>
  ⟨f, SharpTIME_mono h hf, g, SharpTIME_mono h hg, hA⟩

/-- **`C=P` is the union of the classes `CeqTIME (n ^ d)`.** -/
theorem mem_CeqP_iff_exists_mem_CeqTIME : A ∈ CeqP enc ↔ ∃ d, A ∈ CeqTIME enc (· ^ d) := by
  rw [mem_CeqP_iff_exists_SharpP]
  constructor
  · rintro ⟨f, hf, g, hg, hA⟩
    obtain ⟨d₁, hd₁⟩ := mem_SharpP_iff_exists_mem_SharpTIME.mp hf
    obtain ⟨d₂, hd₂⟩ := mem_SharpP_iff_exists_mem_SharpTIME.mp hg
    exact ⟨max d₁ d₂, f, SharpTIME_pow_mono (le_max_left _ _) hd₁,
      g, SharpTIME_pow_mono (le_max_right _ _) hd₂, hA⟩
  · rintro ⟨d, f, hf, g, hg, hA⟩
    exact ⟨f, SharpTIME.subset_SharpP d hf, g, SharpTIME.subset_SharpP d hg, hA⟩

end Cslib.Complexity
