/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Unate grid functions cut corners of few border squares

A function `g : ℕ → ℕ → Bool` **cuts a corner** of the unit square with lower-left corner `(i, j)`
if its mixed difference there is nonzero (`CutsCorner`):
`g i j + g (i + 1) (j + 1) ≠ g (i + 1) j + g i (j + 1)`, as `0/1` values. A function of two bits
has zero mixed difference exactly when it is the sum of a function of the first bit and a
function of the second. A threshold function of two bits cuts the corner exactly when it is not
constant and not a literal.

**Ring lemma** (`card_filter_cutsCorner_gridBorder_le`): if `g` is monotone or antitone in each
coordinate, uniformly in the other one, then it cuts a corner of at most `4` of the `4 (m - 1)`
squares on the border of the grid `{0, …, m} ^ 2` (`gridBorder`, `le_card_gridBorder`).

After reflecting coordinates, `g` is monotone in both. Then a cut square `(i, j)` has
`g i j = false`, `g (i + 1) (j + 1) = true` and `g (i + 1) j = g i (j + 1)`; it is an *outer* or
an *inner* corner of the boundary of the up-set `{g = true}` according to this common value. Two
distinct cut squares of the same kind are incomparable in the product order
(`eq_of_cutsCorner_of_le`), so a chain contains at most two cut squares
(`card_filter_cutsCorner_le_two`). The border is the union of the two chains
`{i = 0} ∪ {j = m - 1}` and `{j = 0} ∪ {i = m - 1}`.

This is the combinatorial step of the lower bound for Andreev's function with two address blocks
in [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640), there
phrased as "the boundary of a monotone region in the grid cuts corners of at most four border
squares".

## Main definitions

* `Cslib.Combinatorics.CutsCorner`: nonzero mixed difference on a unit square.
* `Cslib.Combinatorics.gridBorder`: the border squares of the `m × m` grid of unit squares.

## Main results

* `Cslib.Combinatorics.card_filter_cutsCorner_le_two`: a monotone grid function cuts a corner of
  at most two squares of a chain.
* `Cslib.Combinatorics.card_filter_cutsCorner_gridBorder_le`: the ring lemma.
* `Cslib.Combinatorics.le_card_gridBorder`: the border has at least `4 (m - 1)` squares.
-/

public section

namespace Cslib.Combinatorics

open Finset

/-- `g` **cuts a corner** of the unit square with lower-left corner `(i, j)`: its mixed difference
`g i j + g (i + 1) (j + 1) - g (i + 1) j - g i (j + 1)` there is nonzero. -/
@[expose] def CutsCorner (g : ℕ → ℕ → Bool) (i j : ℕ) : Prop :=
  (g i j).toNat + (g (i + 1) (j + 1)).toNat ≠ (g (i + 1) j).toNat + (g i (j + 1)).toNat

instance (g : ℕ → ℕ → Bool) (i j : ℕ) : Decidable (CutsCorner g i j) :=
  decidable_of_iff (¬(g i j).toNat + (g (i + 1) (j + 1)).toNat =
    (g (i + 1) j).toNat + (g i (j + 1)).toNat) Iff.rfl

/-- The unit squares `(i, j)`, `i, j < m`, on the border of the grid `{0, …, m} ^ 2`. -/
def gridBorder (m : ℕ) : Finset (ℕ × ℕ) :=
  (range m ×ˢ range m).filter fun p => p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = m ∨ p.2 + 1 = m

theorem mem_gridBorder {m : ℕ} {p : ℕ × ℕ} :
    p ∈ gridBorder m ↔ p.1 < m ∧ p.2 < m ∧ (p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = m ∨ p.2 + 1 = m) := by
  simp [gridBorder, and_assoc]

/-- The border of the `m × m` grid of unit squares has at least `4 (m - 1)` squares (exactly
`4 (m - 1)` for `m ≥ 2`). -/
theorem le_card_gridBorder (m : ℕ) : 4 * (m - 1) ≤ #(gridBorder m) := by
  obtain hm | ⟨k, rfl⟩ : m < 2 ∨ ∃ k, m = k + 2 := by
    rcases lt_or_ge m 2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨m - 2, by omega⟩
  · have : m - 1 = 0 := by omega
    simp [this]
  have hsplit := card_filter_add_card_filter_not (s := range (k + 2) ×ˢ range (k + 2))
    fun p : ℕ × ℕ => p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = k + 2 ∨ p.2 + 1 = k + 2
  have hint : #((range (k + 2) ×ˢ range (k + 2)).filter fun p : ℕ × ℕ =>
      ¬(p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = k + 2 ∨ p.2 + 1 = k + 2)) ≤ k * k := by
    refine (card_le_card (t := Ioo 0 (k + 1) ×ˢ Ioo 0 (k + 1)) fun p hp => ?_).trans ?_
    · simp only [mem_filter, mem_product, mem_range] at hp
      simp only [mem_product, mem_Ioo]
      omega
    · simp
  rw [card_product, card_range] at hsplit
  have hk : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by ring
  simp only [gridBorder]
  omega

variable {g : ℕ → ℕ → Bool}

/-- On a grid function monotone in both coordinates, a cut square `(i, j)` has `g i j = false`,
`g (i + 1) (j + 1) = true` and `g (i + 1) j = g i (j + 1)`. -/
theorem CutsCorner.of_monotone (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    {i j : ℕ} (h : CutsCorner g i j) :
    g i j = false ∧ g (i + 1) (j + 1) = true ∧ g (i + 1) j = g i (j + 1) := by
  have h1 : g i j ≤ g (i + 1) j := hg (Nat.le_succ i) le_rfl
  have h2 : g i j ≤ g i (j + 1) := hg le_rfl (Nat.le_succ j)
  have h3 : g (i + 1) j ≤ g (i + 1) (j + 1) := hg le_rfl (Nat.le_succ j)
  have h4 : g i (j + 1) ≤ g (i + 1) (j + 1) := hg (Nat.le_succ i) le_rfl
  unfold CutsCorner at h
  revert h h1 h2 h3 h4
  generalize g i j = a
  generalize g (i + 1) j = b
  generalize g i (j + 1) = c
  generalize g (i + 1) (j + 1) = d
  revert a b c d
  decide

/-- **Cut squares of the same kind are incomparable**: for a grid function monotone in both
coordinates, two cut squares `p ≤ q` with the same value `g (· + 1) ·` at their lower-right corners
are equal. -/
theorem eq_of_cutsCorner_of_le (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    {p q : ℕ × ℕ} (hp : CutsCorner g p.1 p.2) (hq : CutsCorner g q.1 q.2) (hpq : p ≤ q)
    (hv : g (p.1 + 1) p.2 = g (q.1 + 1) q.2) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  obtain ⟨hac, hbd⟩ := Prod.mk_le_mk.mp hpq
  obtain ⟨hp0, hp1, hp2⟩ := hp.of_monotone hg
  obtain ⟨hq0, hq1, hq2⟩ := hq.of_monotone hg
  dsimp only at *
  by_contra hne
  have hlt : a < c ∨ (a = c ∧ b < d) := by
    by_contra h
    exact hne (by rw [show a = c by omega, show b = d by omega])
  have hF : ∀ {u v : Bool}, u ≤ v → u = true → v = false → False := by decide
  cases hval : g (a + 1) b
  · -- outer corners: `g (a + 1) (b + 1) = true` lies below a `false` corner of `q`
    rcases hlt with h | ⟨rfl, h⟩
    · exact hF (hg (show a + 1 ≤ c by omega) (show b + 1 ≤ d + 1 by omega)) hp1
        (by rw [← hq2, ← hv, hval])
    · exact hF (hg le_rfl (show b + 1 ≤ d by omega)) hp1 (by rw [← hv, hval])
  · -- inner corners: a `true` corner of `p` lies below `g c d = false`
    rcases hlt with h | ⟨rfl, h⟩
    · exact hF (hg (show a + 1 ≤ c by omega) hbd) hval hq0
    · exact hF (hg le_rfl (show b + 1 ≤ d by omega)) (by rw [← hp2, hval]) hq0

/-- **Chains**: a grid function monotone in both coordinates cuts a corner of at most two squares
of any chain of the product order. -/
theorem card_filter_cutsCorner_le_two (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ∀ q ∈ s, p ≤ q ∨ q ≤ p) :
    #(s.filter fun p => CutsCorner g p.1 p.2) ≤ 2 := by
  refine (card_le_card_of_injOn (t := (univ : Finset Bool)) (fun p => g (p.1 + 1) p.2)
    (fun _ _ => mem_coe.mpr (mem_univ _)) fun p hp q hq hv => ?_).trans_eq rfl
  rw [mem_coe, mem_filter] at hp hq
  rcases hs p hp.1 q hq.1 with h | h
  · exact eq_of_cutsCorner_of_le hg hp.2 hq.2 h hv
  · exact (eq_of_cutsCorner_of_le hg hq.2 hp.2 h hv.symm).symm

/-- The ring lemma for a grid function monotone in both coordinates. -/
theorem card_filter_cutsCorner_gridBorder_le_of_monotone
    (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j') (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) ≤ 4 := by
  set A := (gridBorder m).filter fun p => p.1 = 0 ∨ p.2 + 1 = m
  set B := (gridBorder m).filter fun p => p.2 = 0 ∨ p.1 + 1 = m
  have hchain (s : Finset (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P]
      (hP : ∀ p q, p.1 < m → p.2 < m → q.1 < m → q.2 < m → P p → P q → p ≤ q ∨ q ≤ p)
      (hs : s = (gridBorder m).filter P) :
      #(s.filter fun p => CutsCorner g p.1 p.2) ≤ 2 :=
    card_filter_cutsCorner_le_two hg s fun p hp q hq => by
      rw [hs, mem_filter, mem_gridBorder] at hp hq
      exact hP p q hp.1.1 hp.1.2.1 hq.1.1 hq.1.2.1 hp.2 hq.2
  have hA := hchain A (fun p => p.1 = 0 ∨ p.2 + 1 = m) (fun p q _ _ _ _ hp hq => by
    simp only [Prod.le_def]; omega) rfl
  have hB := hchain B (fun p => p.2 = 0 ∨ p.1 + 1 = m) (fun p q _ _ _ _ hp hq => by
    simp only [Prod.le_def]; omega) rfl
  calc #((gridBorder m).filter fun p => CutsCorner g p.1 p.2)
      ≤ #((A.filter fun p => CutsCorner g p.1 p.2) ∪ B.filter fun p => CutsCorner g p.1 p.2) :=
        card_le_card fun p hp => by
          rw [mem_filter, mem_gridBorder] at hp
          obtain ⟨⟨h1, h2, h3⟩, hc⟩ := hp
          simp only [A, B, mem_union, mem_filter, mem_gridBorder]
          by_cases hA : p.1 = 0 ∨ p.2 + 1 = m
          · exact Or.inl ⟨⟨⟨h1, h2, h3⟩, hA⟩, hc⟩
          · exact Or.inr ⟨⟨⟨h1, h2, h3⟩, by omega⟩, hc⟩
    _ ≤ 2 + 2 := (card_union_le _ _).trans (add_le_add hA hB)

/-- Reflecting the first coordinate, `i ↦ m - i`, maps cut squares to cut squares. -/
theorem cutsCorner_reflect_fst {m i j : ℕ} (hi : i < m) :
    CutsCorner (fun i j => g (m - i) j) i j ↔ CutsCorner g (m - 1 - i) j := by
  unfold CutsCorner
  dsimp only
  rw [show m - i = m - 1 - i + 1 by omega, show m - (i + 1) = m - 1 - i by omega]
  omega

/-- Reflecting the second coordinate, `j ↦ m - j`, maps cut squares to cut squares. -/
theorem cutsCorner_reflect_snd {m i j : ℕ} (hj : j < m) :
    CutsCorner (fun i j => g i (m - j)) i j ↔ CutsCorner g i (m - 1 - j) := by
  unfold CutsCorner
  dsimp only
  rw [show m - j = m - 1 - j + 1 by omega, show m - (j + 1) = m - 1 - j by omega]
  omega

theorem card_filter_cutsCorner_gridBorder_reflect_fst (g : ℕ → ℕ → Bool) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner (fun i j => g (m - i) j) p.1 p.2) =
      #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) := by
  refine card_nbij' (fun p => (m - 1 - p.1, p.2)) (fun p => (m - 1 - p.1, p.2)) ?_ ?_ ?_ ?_ <;>
    intro p hp <;> rw [mem_coe, mem_filter, mem_gridBorder] at hp <;> dsimp only
  · rw [mem_coe, mem_filter, mem_gridBorder, ← cutsCorner_reflect_fst hp.1.1]
    exact ⟨by omega, hp.2⟩
  · rw [mem_coe, mem_filter, mem_gridBorder, cutsCorner_reflect_fst (by omega),
      show m - 1 - (m - 1 - p.1) = p.1 by omega]
    exact ⟨by omega, hp.2⟩
  · exact Prod.ext (by dsimp only; omega) rfl
  · exact Prod.ext (by dsimp only; omega) rfl

theorem card_filter_cutsCorner_gridBorder_reflect_snd (g : ℕ → ℕ → Bool) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner (fun i j => g i (m - j)) p.1 p.2) =
      #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) := by
  refine card_nbij' (fun p => (p.1, m - 1 - p.2)) (fun p => (p.1, m - 1 - p.2)) ?_ ?_ ?_ ?_ <;>
    intro p hp <;> rw [mem_coe, mem_filter, mem_gridBorder] at hp <;> dsimp only
  · rw [mem_coe, mem_filter, mem_gridBorder, ← cutsCorner_reflect_snd hp.1.2.1]
    exact ⟨by omega, hp.2⟩
  · rw [mem_coe, mem_filter, mem_gridBorder, cutsCorner_reflect_snd (by omega),
      show m - 1 - (m - 1 - p.2) = p.2 by omega]
    exact ⟨by omega, hp.2⟩
  · exact Prod.ext rfl (by dsimp only; omega)
  · exact Prod.ext rfl (by dsimp only; omega)

/-- **Ring lemma**: if `g` is monotone or antitone in each coordinate, uniformly in the other
coordinate, then `g` cuts a corner of at most `4` border squares of the `m × m` grid. -/
theorem card_filter_cutsCorner_gridBorder_le
    (h₁ : (∀ j, Monotone fun i => g i j) ∨ ∀ j, Antitone fun i => g i j)
    (h₂ : (∀ i, Monotone (g i)) ∨ ∀ i, Antitone (g i)) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) ≤ 4 := by
  have hsub : ∀ {i i' : ℕ}, i ≤ i' → m - i' ≤ m - i := fun h => Nat.sub_le_sub_left h m
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ hi).trans (h₂ _ hj)) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_snd]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ hi).trans (h₂ _ (hsub hj))) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_fst]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ (hsub hi)).trans (h₂ _ hj)) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_snd,
      ← card_filter_cutsCorner_gridBorder_reflect_fst]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ (hsub hi)).trans (h₂ _ (hsub hj))) m

end Cslib.Combinatorics
