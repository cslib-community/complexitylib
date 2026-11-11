/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Counting.Space
public import CslibFrontier.Computability.Complexity.Classes.Oracle.CountingEquivalence
import CslibFrontier.Computability.Complexity.Classes.SharpP.Characterization

/-!
# Counting oracles within polynomial space

An arbitrarily encoded #P function extends to a #P function on all words: use the finite native
counting machine supplied by its machine characterization and count the branches halted by its
polynomial clock. On valid codes this is the original function; on other words no halting claim
is needed. Thresholding the extension gives the corresponding extension for PP languages.

The definitions of `P^PP` and `P^#P` require a single oracle program to work for every oracle
agreeing on valid encodings. Choosing the total PP extension therefore puts these classes within
PSPACE. In particular, this argument does not assume that an encoding's image is decidable.

## Main results

* `Cslib.Complexity.SharpP.exists_extension`: a total word extension of a counting function.
* `Cslib.Complexity.exists_PP_extension`: a PP word language agreeing on valid encodings.
* `Cslib.Complexity.PWithPPOracle_subset_PSPACE`.
* `Cslib.Complexity.PWithSharpPOracle_subset_PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A #P function on an arbitrary encoded type extends to a #P function on all words. The
extension counts branches halted by the machine's polynomial clock even on malformed codes. -/
theorem SharpP.exists_extension {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ g ∈ SharpP encBits, ∀ a, g (enc a) = f a := by
  obtain ⟨k, State, hfinite, machine, clock, _, hm⟩ := mem_SharpP_iff_exists_machine.mp hf
  exact ⟨_, machine.acceptCount_mem_SharpP encBits clock, fun a => (hm a).2⟩

/-- An arbitrarily encoded PP language has a total PP extension on words. No recognition of
valid encodings is required: the clocked count is thresholded on every word. -/
theorem exists_PP_extension {A : Set α} (hA : A ∈ PP enc) :
    ∃ B ∈ PP encBits, ∀ a, enc a ∈ B ↔ a ∈ A := by
  obtain ⟨f, hf, p, hA⟩ := mem_PP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hext⟩ := SharpP.exists_extension hf
  refine ⟨{w | 2 ^ p.eval w.length < 2 * g w},
    mem_PP_iff_exists_SharpP.mpr ⟨g, hg, p, fun _ => Iff.rfl⟩, fun a => ?_⟩
  simp only [Set.mem_ofPred_eq, hext, hA a]

/-- Polynomial time with a PP oracle is contained in polynomial space, including arbitrary
oracle-instance encodings and arbitrary answers outside their image. -/
theorem PWithPPOracle_subset_PSPACE : PWithPPOracle enc ⊆ PSPACE enc := by
  rintro L ⟨β, encβ, B, hB, hL⟩
  obtain ⟨A, hA, hext⟩ := exists_PP_extension hB
  exact PWithOracle_subset_PSPACE_of_mem_PP hA (hL.exists_computableInPolyTimeWithOracle hext)

/-- Polynomial time with a bit-by-bit #P oracle is contained in polynomial space. -/
theorem PWithSharpPOracle_subset_PSPACE : PWithSharpPOracle enc ⊆ PSPACE enc :=
  PWithSharpPOracle_subset_PWithPPOracle.trans PWithPPOracle_subset_PSPACE

end Cslib.Complexity
