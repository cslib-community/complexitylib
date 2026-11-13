/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Lattice

/-!
# Nearest-codeword decoding

A decoder chooses a message whose encoded word is closest to the received word in Hamming
distance. No injectivity is required; when the encoder is injective this is ordinary decoding
of its image code. `nearestMessages` keeps all minimizers, including ties.

The decoder predicate, existence theorem and left-inverse theorem were extracted unchanged
from `CslibFrontier.Probability.BitString.BinarySymmetricChannel`.

## Main definitions

* `Cslib.BitString.IsNearestDecoder`: a deterministic nearest-codeword decoder.
* `Cslib.BitString.nearestMessages`: the finite set of minimizing messages.

## Main results

* `Cslib.BitString.exists_isNearestDecoder`: finite nonempty message sets admit a decoder.
* `Cslib.BitString.IsNearestDecoder.leftInverse`: injective codewords decode correctly.
* `Cslib.BitString.IsNearestDecoder.mem_nearestMessages`: the chosen message is a minimizer.
-/

public section

namespace Cslib.BitString

variable {ι M : Type*} [Fintype ι]

/-- `D` decodes `E` to a nearest codeword: the codeword of the decoded message is at least as close
to the received word as every other codeword. -/
@[expose] def IsNearestDecoder (E : M → ι → Bool) (D : (ι → Bool) → M) : Prop :=
  ∀ y m, hammingDist (E (D y)) y ≤ hammingDist (E m) y

/-- Every code with finitely many messages has a nearest-codeword decoder. -/
theorem exists_isNearestDecoder [Finite M] [Nonempty M] (E : M → ι → Bool) :
    ∃ D, IsNearestDecoder E D := by
  choose D hD using fun y : ι → Bool => Finite.exists_min fun m => hammingDist (E m) y
  exact ⟨D, hD⟩

/-- A nearest-codeword decoder of an injective code decodes every codeword correctly. -/
theorem IsNearestDecoder.leftInverse {E : M → ι → Bool} {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) (hE : Function.Injective E) : Function.LeftInverse D E :=
  fun m => hE (hammingDist_eq_zero.mp (Nat.le_zero.mp ((hD (E m) m).trans_eq (hammingDist_self _))))

variable [Fintype M]

open Classical in
/-- Messages whose encoded words minimize the distance to the received word. -/
@[expose] noncomputable def nearestMessages (E : M → ι → Bool) (y : ι → Bool) : Finset M :=
  Finset.univ.filter fun m => ∀ m', hammingDist (E m) y ≤ hammingDist (E m') y

/-- Membership means that no encoded message is closer. -/
@[simp] theorem mem_nearestMessages {E : M → ι → Bool} {y : ι → Bool} {m : M} :
    m ∈ nearestMessages E y ↔ ∀ m', hammingDist (E m) y ≤ hammingDist (E m') y := by
  classical
  simp [nearestMessages]

/-- The deterministic decoder chooses a member of the complete tie set. -/
theorem IsNearestDecoder.mem_nearestMessages {E : M → ι → Bool} {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) (y : ι → Bool) : D y ∈ nearestMessages E y :=
  BitString.mem_nearestMessages.mpr (hD y)

/-- All nearest messages are at the same distance. -/
theorem hammingDist_eq_of_mem_nearestMessages {E : M → ι → Bool} {y : ι → Bool} {m m' : M}
    (hm : m ∈ nearestMessages E y) (hm' : m' ∈ nearestMessages E y) :
    hammingDist (E m) y = hammingDist (E m') y :=
  le_antisymm (mem_nearestMessages.mp hm m') (mem_nearestMessages.mp hm' m)

end Cslib.BitString
