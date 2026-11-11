/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PairwiseIndependentHash
import CslibFrontier.Foundations.Combinatorics.FiniteCover.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Covering a target set with a few hash functions

Seeds `seeds i` of a family of functions `h i : X → Y` *cover* `Y` from a finite set `S ⊆ X` if
every `y : Y` is the image of an element of `S` under one of the functions `h (seeds i)`
(`Cslib.Probability.Covers`). Covering is a two-sided size test for `S`:

* if `h` is pairwise independent, `q |Y| ≤ #S` and `|Y| < q ^ p`, then some `p` seeds cover `Y`
  (`Cslib.Probability.IsPairwiseIndependentHash.exists_covers_of_card`): by the second moment
  bound, at most a `1 / q` fraction of the seeds miss a given target, and a union bound over the
  targets finds `p` seeds that miss none
  (`Cslib.exists_cover_of_scaled_card_lt`);
* if `p` seeds cover `Y`, then `|Y| ≤ p #S` (`Cslib.Probability.Covers.card_le_mul`), whatever the
  family.

With `Y` the strings of `u` bits, `q = 2` and `p = u + 1`, covering holds when `#S ≥ 2 ^ (u + 1)`
and fails when `(u + 1) #S < 2 ^ u`: a test that separates sizes a factor `2 (u + 1)` apart. Like
the hashing analysis of the set lower bound protocol of Goldwasser and Sipser
[Arora and Barak, Section 8.2][AroraBarak09], covering certifies a lower bound on a size. The
union bound over the targets is that of Lautemann's covering lemma [Lautemann1983]
(`Cslib.exists_forall_exists_mul_mem_of_mul_card_compl_le`), with the seeds of a pairwise
independent family in place of shifts.

## Main definitions

* `Cslib.Probability.Covers`: `p` seeds cover the target from a finite set.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.exists_covers_of_card`: large sets are covered by
  few seeds of a pairwise independent family.
* `Cslib.Probability.Covers.card_le_mul`: covered targets are at most `p` times the set.
* `Cslib.Probability.covers_iff_nonempty`: a one-point target is covered exactly by a nonempty set.

## References

* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Probability

open Finset

variable {ι X Y : Type*} [DecidableEq Y]

/-- The seeds `seeds i` *cover* `Y` from `S` if every `y : Y` is the image of an element of `S`
under one of the functions `h (seeds i)`. -/
@[expose] def Covers (h : ι → X → Y) (S : Finset X) {p : ℕ} (seeds : Fin p → ι) : Prop :=
  ∀ y, ∃ i, y ∈ S.image (h (seeds i))

/-- Covering a finite target is decidable. -/
instance [Fintype Y] (h : ι → X → Y) (S : Finset X) {p : ℕ} (seeds : Fin p → ι) :
    Decidable (Covers h S seeds) :=
  inferInstanceAs (Decidable (∀ y, ∃ i, y ∈ S.image (h (seeds i))))

/-- **Covered targets are few**: if `p` seeds cover `Y` from `S`, then `|Y| ≤ p #S`. -/
theorem Covers.card_le_mul [Fintype Y] {h : ι → X → Y} {S : Finset X} {p : ℕ}
    {seeds : Fin p → ι} (hc : Covers h S seeds) : Fintype.card Y ≤ p * #S :=
  calc Fintype.card Y = #(univ : Finset Y) := card_univ.symm
    _ ≤ #(univ.biUnion fun i : Fin p => S.image (h (seeds i))) :=
      card_le_card fun y _ => by
        obtain ⟨i, hi⟩ := hc y
        exact mem_biUnion.2 ⟨i, mem_univ i, hi⟩
    _ ≤ ∑ i : Fin p, #(S.image (h (seeds i))) := card_biUnion_le
    _ ≤ ∑ _i : Fin p, #S := sum_le_sum fun i _ => card_image_le
    _ = p * #S := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **A one-point target is covered exactly by a nonempty set**, with at least one seed. -/
theorem covers_iff_nonempty [Unique Y] {h : ι → X → Y} {S : Finset X} {p : ℕ}
    {seeds : Fin p → ι} (hp : 0 < p) : Covers h S seeds ↔ S.Nonempty := by
  refine ⟨fun hc => ?_, fun hS y => ⟨⟨0, hp⟩, ?_⟩⟩
  · obtain ⟨i, hi⟩ := hc default
    exact (mem_image.1 hi).imp fun _ hx => hx.1
  · obtain ⟨x, hx⟩ := hS
    exact mem_image.2 ⟨x, hx, Subsingleton.elim _ _⟩

namespace IsPairwiseIndependentHash

variable [Fintype ι] [Fintype Y] {h : ι → X → Y}

/-- **Large sets are covered by few seeds**: if `h` is pairwise independent, `q |Y| ≤ #S` and
`|Y| < q ^ p`, then some `p` seeds cover `Y` from `S`. At most a `1 / q` fraction of the seeds
miss a given target (`IsPairwiseIndependentHash.card_filter_notMem_image_mul_le`), and the union
bound over the targets (`Cslib.exists_cover_of_scaled_card_lt`) finds `p` seeds that miss none. -/
theorem exists_covers_of_card (hh : IsPairwiseIndependentHash h) [Nonempty Y] {S : Finset X}
    {q p : ℕ} (hS : q * Fintype.card Y ≤ #S) (hp : Fintype.card Y < q ^ p) :
    ∃ seeds : Fin p → ι, Covers h S seeds := by
  have hY : 0 < Fintype.card Y := Fintype.card_pos
  have hq : 0 < q := by
    refine Nat.pos_of_ne_zero fun hq0 => ?_
    subst hq0
    rcases p with _ | p
    · rw [pow_zero] at hp
      omega
    · rw [zero_pow (Nat.succ_ne_zero p)] at hp
      omega
  have hSne : S.Nonempty := card_pos.1 ((Nat.mul_pos hq hY).trans_le hS)
  obtain ⟨x, hx⟩ := hSne
  have : Nonempty ι := hh.nonempty x (Classical.arbitrary Y)
  refine exists_cover_of_scaled_card_lt (fun i y => y ∈ S.image (h i)) 1 q p (fun y => ?_)
    (by rwa [one_pow, mul_one])
  have hmiss := hh.card_filter_notMem_image_mul_le ⟨x, hx⟩ y
  rw [Fintype.card_subtype, one_mul]
  refine Nat.le_of_mul_le_mul_right ?_ hY
  calc q * #{i | y ∉ S.image (h i)} * Fintype.card Y
      = #{i | y ∉ S.image (h i)} * (q * Fintype.card Y) := by ring
    _ ≤ #{i | y ∉ S.image (h i)} * #S := Nat.mul_le_mul_left _ hS
    _ ≤ Fintype.card Y * Fintype.card ι := hmiss
    _ = Fintype.card ι * Fintype.card Y := mul_comm _ _

end IsPairwiseIndependentHash

end Cslib.Probability
