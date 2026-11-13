/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sensitivity of a disjunction of blocks

A disjunction over disjoint blocks of input bits changes value under a single-bit flip only when
the flip changes the block containing the bit and that block change changes the disjunction.
When some block accepts, only that block can change the disjunction; when every block rejects,
every block can. `sum_le_max_of_or` is this count-level argument, independent of how blocks are
laid out or how their local sensitivities are measured. It is shared by the homogeneous
`QueryComplexity.SensitivitySeparation.Internal.sensitivity_orCopies_le` and by the dependent,
unequal-size native layout below.

The native layout `orBlocks` puts blocks of sizes `sizes b` consecutively in block order using
Mathlib's `finSigmaFinEquiv`, transported along a length equation `∑ b, sizes b = n`.

## Main definitions

* `Cslib.BitString.blockEquiv`: the consecutive layout of unequal blocks inside `Fin n`.
* `Cslib.BitString.blockOf`: the restriction of an input to one block.
* `Cslib.BitString.orBlocks`: the OR of local Boolean functions on the blocks.

## Main results

* `Cslib.BitString.sum_le_max_of_or`: the shared dependent-OR counting argument.
* `Cslib.BitString.sensitivityAt_orBlocks`: sensitivity at an input is the sum of local
  sensitivities over the blocks whose flip changes the disjunction.
* `Cslib.BitString.sensitivity_orBlocks_le`: rejected-block bound `S₀` and accepted-block bound
  `S₁` give `s(orBlocks g) ≤ max (k * S₀) S₁`.
-/

public section

namespace Cslib.BitString

open Finset

/-- **Dependent-OR counting.** Let `y k` be the value of block `k`, `T` the blocks whose change
changes the disjunction, and `s k` a count attached to block `k` (for instance its local
sensitivity). If every accepting block `j` forces `T ⊆ {j}`, rejected blocks have count at most
`S₀` and accepted blocks at most `S₁`, then the counts over `T` sum to at most
`max (card K * S₀) S₁`. -/
theorem sum_le_max_of_or {K : Type*} [Fintype K] (y : K → Bool) (T : Finset K) (s : K → ℕ)
    {S₀ S₁ : ℕ} (hT : ∀ j, y j = true → T ⊆ {j})
    (h₀ : ∀ k, y k = false → s k ≤ S₀) (h₁ : ∀ k, y k = true → s k ≤ S₁) :
    ∑ k ∈ T, s k ≤ max (Fintype.card K * S₀) S₁ := by
  by_cases hy : ∃ j, y j = true
  · obtain ⟨j, hj⟩ := hy
    calc
      _ ≤ ∑ k ∈ ({j} : Finset K), s k := sum_le_sum_of_subset_of_nonneg (hT j hj) (by simp)
      _ = s j := sum_singleton _ _
      _ ≤ S₁ := h₁ j hj
      _ ≤ _ := le_max_right _ _
  · have hall (k : K) : y k = false := by simpa using fun h => hy ⟨k, h⟩
    calc
      _ ≤ ∑ _k ∈ T, S₀ := sum_le_sum fun k _ => h₀ k (hall k)
      _ = T.card * S₀ := by simp
      _ ≤ Fintype.card K * S₀ := Nat.mul_le_mul_right _ (card_le_univ _)
      _ ≤ _ := le_max_left _ _

variable {k n : ℕ} {sizes : Fin k → ℕ}

/-- The consecutive layout of blocks of the given sizes in block-index order. -/
@[expose] def blockEquiv (h : ∑ b, sizes b = n) : (Σ b, Fin (sizes b)) ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr h)

/-- The restriction of an input to block `b` of the consecutive layout. -/
@[expose] def blockOf (h : ∑ b, sizes b = n) (x : BitString n) (b : Fin k) :
    BitString (sizes b) :=
  fun j => x (blockEquiv h ⟨b, j⟩)

/-- Changing a coordinate of block `b` changes only that coordinate of block `b`. -/
theorem blockOf_update_self (h : ∑ b, sizes b = n) (x : BitString n) (b : Fin k)
    (j : Fin (sizes b)) (v : Bool) :
    blockOf h (Function.update x (blockEquiv h ⟨b, j⟩) v) b =
      Function.update (blockOf h x b) j v := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [blockOf]
  · rw [Function.update_of_ne hi]
    simp only [blockOf]
    rw [Function.update_of_ne]
    intro he
    exact hi (by simpa using (blockEquiv h).injective he)

/-- Changing a coordinate of block `b` leaves every other block unchanged. -/
theorem blockOf_update_of_ne (h : ∑ b, sizes b = n) (x : BitString n) {b c : Fin k}
    (hc : c ≠ b) (j : Fin (sizes b)) (v : Bool) :
    blockOf h (Function.update x (blockEquiv h ⟨b, j⟩) v) c = blockOf h x c := by
  funext i
  simp only [blockOf]
  rw [Function.update_of_ne]
  intro he
  exact hc (congrArg Sigma.fst ((blockEquiv h).injective he))

/-- The OR of the local functions `g b` on the blocks of the consecutive layout. -/
@[expose] def orBlocks (h : ∑ b, sizes b = n) (g : ∀ b, BooleanFunction (sizes b)) :
    BooleanFunction n :=
  fun x => decide (∃ b, g b (blockOf h x b) = true)

/-- The disjunction accepts exactly when some block accepts. -/
theorem orBlocks_eq_true_iff {h : ∑ b, sizes b = n} {g : ∀ b, BooleanFunction (sizes b)}
    {x : BitString n} : orBlocks h g x = true ↔ ∃ b, g b (blockOf h x b) = true := by
  simp [orBlocks]

/-- The blocks whose value flip changes the disjunction at `x`. -/
@[expose] def orSensitiveBlocks (h : ∑ b, sizes b = n) (g : ∀ b, BooleanFunction (sizes b))
    (x : BitString n) : Finset (Fin k) :=
  univ.filter fun b =>
    decide (∃ c, Function.update (fun c => g c (blockOf h x c)) b (!g b (blockOf h x b)) c =
      true) ≠ decide (∃ c, g c (blockOf h x c) = true)

/-- If block `j` accepts, then no other block can change the disjunction. -/
theorem orSensitiveBlocks_subset {h : ∑ b, sizes b = n} {g : ∀ b, BooleanFunction (sizes b)}
    {x : BitString n} {j : Fin k} (hj : g j (blockOf h x j) = true) :
    orSensitiveBlocks h g x ⊆ {j} := by
  intro b hb
  rw [mem_singleton]
  by_contra hbj
  simp only [orSensitiveBlocks, mem_filter, mem_univ, true_and] at hb
  apply hb
  have h₁ : ∃ c, Function.update (fun c => g c (blockOf h x c)) b (!g b (blockOf h x b)) c =
      true := ⟨j, by rw [Function.update_of_ne (Ne.symm hbj)]; exact hj⟩
  simp only [h₁, decide_true]
  exact (decide_eq_true ⟨j, hj⟩).symm

/-- A coordinate is sensitive for the disjunction iff it is sensitive for its block and that
block is one whose flip changes the disjunction. -/
theorem isSensitiveCoord_orBlocks_iff {h : ∑ b, sizes b = n}
    {g : ∀ b, BooleanFunction (sizes b)} {x : BitString n} {b : Fin k} {j : Fin (sizes b)} :
    IsSensitiveCoord (orBlocks h g) x (blockEquiv h ⟨b, j⟩) ↔
      IsSensitiveCoord (g b) (blockOf h x b) j ∧ b ∈ orSensitiveBlocks h g x := by
  set i := blockEquiv h ⟨b, j⟩
  set x' := Function.update x i (!x i)
  have hb : blockOf h x' b = Function.update (blockOf h x b) j (!blockOf h x b j) :=
    blockOf_update_self h x b j _
  have hc (c : Fin k) (hc : c ≠ b) : blockOf h x' c = blockOf h x c :=
    blockOf_update_of_ne h x hc j _
  simp only [IsSensitiveCoord, orSensitiveBlocks, mem_filter, mem_univ, true_and]
  by_cases hl : g b (Function.update (blockOf h x b) j (!blockOf h x b j)) = g b (blockOf h x b)
  · have he : (fun c => g c (blockOf h x' c)) = fun c => g c (blockOf h x c) := by
      funext c
      by_cases hcb : c = b
      · subst c
        rw [hb, hl]
      · rw [hc c hcb]
    simp only [hl, ne_eq, not_true_eq_false, false_and, iff_false, not_not]
    have he' (c : Fin k) : g c (blockOf h x' c) = g c (blockOf h x c) := congrFun he c
    change decide (∃ c, g c (blockOf h x' c) = true) = decide (∃ c, g c (blockOf h x c) = true)
    simp only [he']
  · have hn : g b (Function.update (blockOf h x b) j (!blockOf h x b j)) =
        !g b (blockOf h x b) := by
      cases h₁ : g b (Function.update (blockOf h x b) j (!blockOf h x b j)) <;>
        cases h₂ : g b (blockOf h x b) <;> simp_all
    have he : (fun c => g c (blockOf h x' c)) =
        Function.update (fun c => g c (blockOf h x c)) b (!g b (blockOf h x b)) := by
      funext c
      by_cases hcb : c = b
      · subst c
        rw [hb, hn, Function.update_self]
      · rw [hc c hcb, Function.update_of_ne hcb]
    simp only [hl, ne_eq, not_false_eq_true, true_and]
    have he' (c : Fin k) : g c (blockOf h x' c) =
        Function.update (fun c => g c (blockOf h x c)) b (!g b (blockOf h x b)) c :=
      congrFun he c
    change decide (∃ c, g c (blockOf h x' c) = true) ≠ decide (∃ c, g c (blockOf h x c) = true) ↔
      _
    simp only [he', ne_eq]

/-- The sensitive coordinates of the disjunction are the sensitive coordinates of the blocks
whose flip changes the disjunction, placed by the layout. -/
theorem sensitiveCoords_orBlocks (h : ∑ b, sizes b = n) (g : ∀ b, BooleanFunction (sizes b))
    (x : BitString n) :
    sensitiveCoords (orBlocks h g) x =
      ((orSensitiveBlocks h g x).sigma fun b => sensitiveCoords (g b) (blockOf h x b)).map
        (blockEquiv h).toEmbedding := by
  ext i
  obtain ⟨⟨b, j⟩, rfl⟩ := (blockEquiv h).surjective i
  simp only [mem_sensitiveCoords, mem_map_equiv, Equiv.symm_apply_apply, mem_sigma,
    isSensitiveCoord_orBlocks_iff, and_comm]

/-- **Sensitivity of a disjunction of blocks.** The sensitivity at `x` is the sum of the local
sensitivities over the blocks whose flip changes the disjunction. -/
theorem sensitivityAt_orBlocks (h : ∑ b, sizes b = n) (g : ∀ b, BooleanFunction (sizes b))
    (x : BitString n) :
    sensitivityAt (orBlocks h g) x =
      ∑ b ∈ orSensitiveBlocks h g x, sensitivityAt (g b) (blockOf h x b) := by
  rw [sensitivityAt, sensitiveCoords_orBlocks, card_map, card_sigma]
  rfl

/-- If rejected blocks have local sensitivity at most `S₀` and accepted blocks at most `S₁`,
then the disjunction of `k` blocks has sensitivity at most `max (k * S₀) S₁`. -/
theorem sensitivity_orBlocks_le (h : ∑ b, sizes b = n) (g : ∀ b, BooleanFunction (sizes b))
    {S₀ S₁ : ℕ} (h₀ : ∀ b x, g b x = false → sensitivityAt (g b) x ≤ S₀)
    (h₁ : ∀ b x, g b x = true → sensitivityAt (g b) x ≤ S₁) :
    sensitivity (orBlocks h g) ≤ max (k * S₀) S₁ := by
  refine Finset.sup_le fun x _ => ?_
  rw [sensitivityAt_orBlocks]
  simpa only [Fintype.card_fin] using
    sum_le_max_of_or (fun b => g b (blockOf h x b)) (orSensitiveBlocks h g x)
      (fun b => sensitivityAt (g b) (blockOf h x b)) (fun j hj => orSensitiveBlocks_subset hj)
      (fun b hb => h₀ b _ hb) (fun b hb => h₁ b _ hb)

/-- If exactly block `b` accepts, the disjunction has the local sensitivity of block `b`. -/
theorem sensitivityAt_orBlocks_of_unique (h : ∑ b, sizes b = n)
    (g : ∀ b, BooleanFunction (sizes b)) {x : BitString n} {b : Fin k}
    (hb : g b (blockOf h x b) = true) (hother : ∀ c, c ≠ b → g c (blockOf h x c) = false) :
    sensitivityAt (orBlocks h g) x = sensitivityAt (g b) (blockOf h x b) := by
  have hT : orSensitiveBlocks h g x = {b} := by
    refine subset_antisymm (orSensitiveBlocks_subset hb) (singleton_subset_iff.mpr ?_)
    simp only [orSensitiveBlocks, mem_filter, mem_univ, true_and]
    have hnone : ¬∃ c, Function.update (fun c => g c (blockOf h x c)) b
        (!g b (blockOf h x b)) c = true := by
      rintro ⟨c, hc⟩
      by_cases hcb : c = b
      · subst c
        simp [hb] at hc
      · rw [Function.update_of_ne hcb, hother c hcb] at hc
        exact Bool.false_ne_true hc
    simp only [hnone, decide_false]
    exact fun he => Bool.false_ne_true (he.trans (decide_eq_true ⟨b, hb⟩))
  rw [sensitivityAt_orBlocks, hT, sum_singleton]

end Cslib.BitString
