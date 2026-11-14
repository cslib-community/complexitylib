/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.AdjacentPair.Local
public import CslibFrontier.Computability.QueryComplexity.OrBlocks

/-!
# Adjacent-pair predicates on unequal consecutive blocks

The function in [AroraBarak07], Chapter 11 Exercise 2, is the OR of the local adjacent-pair
predicate `adjacentPair` over disjoint contiguous blocks. This module permits arbitrary, possibly
unequal block sizes laid out by `Cslib.BitString.orBlocks`. Every adjacent pair of a block is
accepted, including overlapping choices; the block-sensitivity witness family uses only the
disjoint pairs starting at even local positions.

## Main definitions

* `Cslib.BitString.adjacentPairBlocks`: the OR of `adjacentPair` over the given block sizes.
* `Cslib.BitString.adjacentPairWitness`: one designated pair used for the lower bound.
* `Cslib.BitString.adjacentPairSensitiveFamily`: all these disjoint pair witnesses.

## Main results

* `Cslib.BitString.sensitivity_adjacentPairBlocks_le`: with `k` blocks of size at most `M`,
  `s(f) ≤ max (3 * k) M`.
* `Cslib.BitString.le_sensitivity_adjacentPairBlocks`: every block of size at least two gives
  `sizes b ≤ s(f)`.
* `Cslib.BitString.sum_half_le_blockSensitivity_adjacentPairBlocks`:
  `∑ b, sizes b / 2 ≤ bs(f)`.
* `Cslib.BitString.card_le_three_mul_blockSensitivity_adjacentPairBlocks`: `n ≤ 3 bs(f)` when
  every block has at least two coordinates.
-/

public section

namespace Cslib.BitString

open Finset QueryComplexity

variable {k n : ℕ} {sizes : Fin k → ℕ}

/-- An input is accepted when some block has exactly two adjacent true positions. The blocks
are consecutive in block-index order and may have different sizes. -/
@[expose] def adjacentPairBlocks (h : ∑ b, sizes b = n) : BooleanFunction n :=
  orBlocks h fun b => adjacentPair (sizes b)

/-- The block function accepts exactly when one of its local predicates accepts. -/
theorem adjacentPairBlocks_eq_true_iff {h : ∑ b, sizes b = n} {x : BitString n} :
    adjacentPairBlocks h x = true ↔ ∃ b, adjacentPair (sizes b) (blockOf h x b) = true :=
  orBlocks_eq_true_iff

/-- No block of the all-false word is accepted. -/
@[simp] theorem adjacentPairBlocks_zero (h : ∑ b, sizes b = n) :
    adjacentPairBlocks h (fun _ => false) = false := by
  cases hx : adjacentPairBlocks h (fun _ => false) with
  | false => rfl
  | true =>
    obtain ⟨b, hb⟩ := adjacentPairBlocks_eq_true_iff.mp hx
    have hz : blockOf h (fun _ => false) b = fun _ => false := rfl
    rw [hz, adjacentPair_zero] at hb
    exact absurd hb (by decide)

/-- **Sensitivity upper bound.** A rejected block has local sensitivity at most three and an
accepted block of size at most `M` has local sensitivity at most `M`. -/
theorem sensitivity_adjacentPairBlocks_le (h : ∑ b, sizes b = n) {M : ℕ}
    (hM : ∀ b, sizes b ≤ M) : sensitivity (adjacentPairBlocks h) ≤ max (3 * k) M := by
  have h' := sensitivity_orBlocks_le h (fun b => adjacentPair (sizes b)) (S₀ := 3) (S₁ := M)
    (fun _ _ hx => sensitivityAt_adjacentPair_le_three hx)
    (fun b _ hx => (sensitivityAt_adjacentPair_of_true hx).trans_le (hM b))
  rwa [mul_comm] at h'

/-- The input whose only true bits are the first two positions of block `b`. -/
@[expose] def adjacentPairStart (h : ∑ b, sizes b = n) (b : Fin k) : BitString n :=
  fun i => decide (((blockEquiv h).symm i).1 = b ∧ ((blockEquiv h).symm i).2.val < 2)

/-- **Sensitivity lower bound.** Every block with room for a pair has all of its coordinates
sensitive at the input accepting only in that block. -/
theorem le_sensitivity_adjacentPairBlocks (h : ∑ b, sizes b = n) {b : Fin k}
    (hb : 2 ≤ sizes b) : sizes b ≤ sensitivity (adjacentPairBlocks h) := by
  have hblock (c : Fin k) :
      blockOf h (adjacentPairStart h b) c = fun j => decide (c = b ∧ j.val < 2) := by
    funext j
    simp only [blockOf, adjacentPairStart]
    rw [Equiv.symm_apply_apply]
  have hacc : adjacentPair (sizes b) (blockOf h (adjacentPairStart h b) b) = true := by
    rw [hblock]
    refine adjacentPair_eq_true_iff.mpr ⟨⟨0, by omega⟩, ⟨1, by omega⟩, rfl, fun i => ?_⟩
    simp only [true_and, Fin.ext_iff, decide_eq_decide]
    omega
  have hrej (c : Fin k) (hc : c ≠ b) :
      adjacentPair (sizes c) (blockOf h (adjacentPairStart h b) c) = false := by
    rw [hblock]
    simp [hc]
  calc
    sizes b = sensitivityAt (adjacentPairBlocks h) (adjacentPairStart h b) := by
      rw [adjacentPairBlocks, sensitivityAt_orBlocks_of_unique h _ hacc hrej,
        sensitivityAt_adjacentPair_of_true hacc]
    _ ≤ _ := sensitivityAt_le_sensitivity _ _

/-- The `j`-th disjoint pair in block `b` consists of local positions `2 * j` and `2 * j + 1`.
These are witnesses for block sensitivity; the function itself also accepts overlapping
pairs. -/
@[expose] def adjacentPairWitness (h : ∑ b, sizes b = n)
    (p : (b : Fin k) × Fin (sizes b / 2)) : Block n :=
  {blockEquiv h ⟨p.1, ⟨2 * p.2.val, by have := p.2.isLt; omega⟩⟩,
    blockEquiv h ⟨p.1, ⟨2 * p.2.val + 1, by have := p.2.isLt; omega⟩⟩}

/-- Flipping a designated pair at zero creates an accepted local adjacent pair. -/
theorem isSensitiveBlock_adjacentPairWitness (h : ∑ b, sizes b = n)
    (p : (b : Fin k) × Fin (sizes b / 2)) :
    IsSensitiveBlock (adjacentPairBlocks h) (fun _ => false) (adjacentPairWitness h p) := by
  rw [IsSensitiveBlock, adjacentPairBlocks_zero]
  have ht : adjacentPairBlocks h (flipBlock (adjacentPairWitness h p) (fun _ => false)) =
      true := by
    refine adjacentPairBlocks_eq_true_iff.mpr ⟨p.1, adjacentPair_eq_true_iff.mpr
      ⟨⟨2 * p.2.val, by have := p.2.isLt; omega⟩,
        ⟨2 * p.2.val + 1, by have := p.2.isLt; omega⟩, rfl, fun i => ?_⟩⟩
    simp [blockOf, flipBlock, adjacentPairWitness]
  rw [ht]
  decide

/-- Witnesses with distinct indices are disjoint, within a block and across blocks. -/
theorem pairwise_disjoint_adjacentPairWitness (h : ∑ b, sizes b = n) :
    Pairwise fun p q : (b : Fin k) × Fin (sizes b / 2) =>
      Disjoint (adjacentPairWitness h p) (adjacentPairWitness h q) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ hne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [adjacentPairWitness, mem_insert, mem_singleton] at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  all_goals
    have he := (blockEquiv h).injective (hz.symm.trans hz')
    have hb := congrArg Sigma.fst he
    have hv := congrArg (fun p : (b : Fin k) × Fin (sizes b) => p.2.val) he
    dsimp only at hb hv
    apply hne
    cases hb
    congr 1
    apply Fin.ext
    omega

/-- Different witness indices give different blocks. -/
theorem adjacentPairWitness_injective (h : ∑ b, sizes b = n) :
    Function.Injective (adjacentPairWitness h) := by
  intro p q hpq
  by_contra hne
  exact Disjoint.ne (by simp [adjacentPairWitness])
    (pairwise_disjoint_adjacentPairWitness h hne) hpq

/-- All disjoint even-starting pairs across all the blocks. -/
@[expose] def adjacentPairSensitiveFamily (h : ∑ b, sizes b = n) : Finset (Block n) :=
  univ.image (adjacentPairWitness h)

/-- The concrete family is sensitive at zero and pairwise disjoint. -/
theorem isSensitiveFamily_adjacentPairSensitiveFamily (h : ∑ b, sizes b = n) :
    IsSensitiveFamily (adjacentPairBlocks h) (fun _ => false)
      (adjacentPairSensitiveFamily h) := by
  constructor
  · intro B hB
    obtain ⟨p, _, rfl⟩ := mem_image.mp hB
    exact isSensitiveBlock_adjacentPairWitness h p
  · change (↑(adjacentPairSensitiveFamily h) : Set (Block n)).Pairwise Disjoint
    have hp : (Set.univ : Set ((b : Fin k) × Fin (sizes b / 2))).Pairwise
        (fun p q => Disjoint (adjacentPairWitness h p) (adjacentPairWitness h q)) :=
      fun _ _ _ _ hne => pairwise_disjoint_adjacentPairWitness h hne
    simpa only [adjacentPairSensitiveFamily, Finset.coe_image, Finset.coe_univ] using hp.image

/-- There are exactly as many designated disjoint pairs as the sum of the half block sizes. -/
theorem card_adjacentPairSensitiveFamily (h : ∑ b, sizes b = n) :
    (adjacentPairSensitiveFamily h).card = ∑ b, sizes b / 2 := by
  simp only [adjacentPairSensitiveFamily,
    card_image_of_injective _ (adjacentPairWitness_injective h), card_univ,
    Fintype.card_sigma, Fintype.card_fin]

/-- **Block-sensitivity lower bound.** The disjoint pair family at zero gives
`∑ b, sizes b / 2 ≤ bs(f)`. -/
theorem sum_half_le_blockSensitivity_adjacentPairBlocks (h : ∑ b, sizes b = n) :
    (∑ b, sizes b / 2) ≤ blockSensitivity (adjacentPairBlocks h) := by
  rw [← card_adjacentPairSensitiveFamily h]
  exact card_le_blockSensitivity (isSensitiveFamily_adjacentPairSensitiveFamily h)

/-- If every block has at least two coordinates, three times block sensitivity covers every
input coordinate. Odd and unequal block sizes are permitted. -/
theorem card_le_three_mul_blockSensitivity_adjacentPairBlocks (h : ∑ b, sizes b = n)
    (hsizes : ∀ b, 2 ≤ sizes b) : n ≤ 3 * blockSensitivity (adjacentPairBlocks h) := by
  calc
    n = ∑ b, sizes b := h.symm
    _ ≤ ∑ b, 3 * (sizes b / 2) := Finset.sum_le_sum fun b _ => by
      have hb := hsizes b
      omega
    _ = 3 * ∑ b, sizes b / 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left 3 (sum_half_le_blockSensitivity_adjacentPairBlocks h)

end Cslib.BitString
