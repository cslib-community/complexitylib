/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SBP
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.PP.Characterization

/-!
# Bounded-error postselected polynomial time

`BPPpath` was introduced by [Han, Hemaspaandra and Thierauf][HanHemaspaandraThierauf1997] as the
class of languages accepted by polynomial-time nondeterministic threshold machines, with computation
paths of possibly different lengths, whose fraction of accepting paths is bounded away from one
half. We fix the ratio gap at three quarters; by their error reduction any fixed gap gives the same
class, which is not proved here. We state it through its path counts: there are #P functions `acc`
and `rej` counting the accepting and rejecting paths, with at least one path on every input, such
that `acc ≥ 3 rej` on members and `rej ≥ 3 acc` on nonmembers. As for `SBP`
(`Cslib.Complexity.SBP`), these are verifier counts; the equivalence with the machine definition is
not proved here.

SBP lies between BPP and BPPpath [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]: an SBP
count `f` with an FP threshold `k` and an amplified gap is turned into the path counts `3f` and
`k`. With PP it gives the chain `BPP ⊆ SBP ⊆ BPPpath ⊆ PP`.

## Main definitions

* `Cslib.Complexity.BPPpath`: bounded-error postselected polynomial time via path counts.

## Main results

* `Cslib.Complexity.SBP_subset_BPPpath`: SBP is contained in BPPpath.
* `Cslib.Complexity.BPP_subset_BPPpath`, `Cslib.Complexity.BPPpath_subset_PP`.

## References

* [Y. Han, L. A. Hemaspaandra, T. Thierauf, *Threshold computation and cryptographic
  security*][HanHemaspaandraThierauf1997]
* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The languages with #P path counts `acc` (accepting) and `rej` (rejecting), at least one path
on every input, where at least three quarters of the paths accept on members and at least three
quarters reject on nonmembers [Han, Hemaspaandra and Thierauf][HanHemaspaandraThierauf1997]. -/
def BPPpath (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ acc ∈ SharpP enc, ∃ rej ∈ SharpP enc, ∀ a, 0 < acc a + rej a ∧
    (a ∈ A → 3 * rej a ≤ acc a) ∧ (a ∉ A → 3 * acc a ≤ rej a)}

theorem mem_BPPpath : A ∈ BPPpath enc ↔ ∃ acc ∈ SharpP enc, ∃ rej ∈ SharpP enc, ∀ a,
    0 < acc a + rej a ∧ (a ∈ A → 3 * rej a ≤ acc a) ∧ (a ∉ A → 3 * acc a ≤ rej a) :=
  Iff.rfl

/-- **SBP ⊆ BPPpath** [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]. Amplify the SBP
gap to sixteen; then `3f` accepting paths against `k` rejecting paths give the ratio three on
both sides. -/
theorem SBP_subset_BPPpath : SBP enc ⊆ BPPpath enc := by
  intro A hA
  obtain ⟨f, hf, k, hk, hkpos, hgap⟩ := exists_SBP_gap_pow hA (m := 4) (by decide)
  refine ⟨fun a => 3 * f a, SharpP.mul_mem (SharpP.natCast_mem 3) hf, k,
    mem_SharpP_of_polyTime hk, fun a => ⟨?_, fun ha => ?_, fun ha => ?_⟩⟩
  · have := hkpos a
    omega
  · have := (hgap a).1 ha
    dsimp only
    omega
  · have := (hgap a).2 ha
    dsimp only
    omega

/-- **BPP ⊆ BPPpath**, through `BPP ⊆ SBP`
[Han, Hemaspaandra and Thierauf][HanHemaspaandraThierauf1997]. -/
theorem BPP_subset_BPPpath : BPP enc ⊆ BPPpath enc :=
  BPP_subset_SBP.trans SBP_subset_BPPpath

/-- **BPPpath ⊆ PP**: the integer gap `acc - rej` is positive exactly on members. -/
theorem BPPpath_subset_PP : BPPpath enc ⊆ PP enc := by
  rintro A ⟨acc, hacc, rej, hrej, h⟩
  refine mem_PP_iff_exists_GapP.mpr ⟨_, GapP.sub_mem' (SharpP.natCast_mem_GapP hacc)
    (SharpP.natCast_mem_GapP hrej), fun a => ?_⟩
  obtain ⟨hpos, hmem, hnot⟩ := h a
  change a ∈ A ↔ 0 < (acc a : ℤ) - rej a
  by_cases ha : a ∈ A
  · have := hmem ha
    simp only [ha, true_iff]
    omega
  · have := hnot ha
    simp only [ha, false_iff]
    omega

end Cslib.Complexity
