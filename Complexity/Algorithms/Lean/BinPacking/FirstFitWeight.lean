/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.FirstFit
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor

/-!
# First Fit uses at most `17/10 * OPT + 4/5` bins

This file proves the `17/10` bound for First Fit (`Cslib.Algorithms.Lean.BinPacking.firstFit`)
with an explicit additive constant: against any packing `Q` of the same items,
`10 * FF ≤ 17 * Q.length + 8` (`ten_mul_length_firstFit_le`), that is
`FF ≤ 17/10 * OPT + 4/5` for the optimum `OPT`. As `FF` is an integer this implies
`FF ≤ ⌈17/10 * OPT⌉` (`length_firstFit_le_ceil`), the bound of
[Garey, Graham, Johnson and Yao][GareyGrahamJohnsonYao1976] as reported by
[Dósa and Sgall, Section 1.1][DosaSgall2013], and the earlier `FF ≤ 17/10 * OPT + 2` of
[Johnson, Demers, Ullman, Garey and Graham][JohnsonDemersUllmanGareyGraham1974].

The proof is the amortized weighting argument of [Dósa and Sgall, Section 1.2][DosaSgall2013],
with sizes in `ℕ` and bin capacity `C`, all weights scaled by `10 * C`. An item of size `a` has
weight `12 * a` (the scaled size `6/5 * a`) plus a bonus (`firstFitBonus`): `4 * C` if
`C < 2 * a`, `C` if `C ≤ 3 * a ≤ 3/2 * C`, `6 * a - C` if `C < 6 * a < 2 * C`, and `0` otherwise.
These are Dósa and Sgall's bonuses `0.4`, `0.1`, `3/5 * (a - 1/6)` and `0`.

* **Upper bound.** A bin of total size at most `C` has weight at most `17 * C`
  (`sum_map_firstFitWeight_le`): at most one item is larger than `C / 2`, and on items of size at
  most `C / 2` the bonus is superadditive. Summed over a packing `Q`, all items weigh at most
  `17 * C * Q.length` (`IsPacking.sum_map_le_mul_length`).
* **Lower bound.** First Fit's bins weigh `10 * C` each on average, up to `8 * C` in total. Every
  item of a later bin did not fit into an earlier one
  (`pairwise_forall_lt_sum_add_firstFit`). So if a bin `B` is at least `2/3` full and a later bin
  `B'` has two items, then `12 * B.sum` plus the bonus of `B'` is at least `10 * C`
  ([Dósa and Sgall, Lemma 1.1][DosaSgall2013]). Chaining this over the bins with at least two
  items, adding the bins holding one item larger than `C / 2`, and accounting for at most one
  bin with two or more items less than `2/3` full and at most one bin holding a single item of
  size at most `C / 2`, the total weight plus `8 * C` is at least `10 * C * FF`. The exception is
  a First Fit packing in which all bins but one hold a single item larger than `C / 2`; there
  `FF ≤ OPT + 1` directly, since no two such items share a bin.

Dósa and Sgall's sketch in their Section 1.2 leaves three bins unaccounted for and concludes
`FF ≤ 1.7 * OPT + 3`; they remark that examining those bins brings the constant down to `0.6`.
The case analysis of the remaining bins here, which gives `0.8`, is our own. Their main result,
the absolute bound `FF ≤ ⌊1.7 * OPT⌋` ([Dósa and Sgall, Theorem 3.13][DosaSgall2013]), is not
formalized here; neither is the matching lower-bound family of their Section 4.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.firstFitBonus`: the bonus of an item, scaled by `10 * C`.
* `Cslib.Algorithms.Lean.BinPacking.firstFitWeight`: the weight of an item, scaled by `10 * C`.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.sum_map_firstFitWeight_le`: a bin weighs at most `17 * C`.
* `Cslib.Algorithms.Lean.BinPacking.ten_mul_length_firstFit_le`: `10 * FF ≤ 17 * OPT + 8`.
* `Cslib.Algorithms.Lean.BinPacking.length_firstFit_le_ceil`: `FF ≤ ⌈17/10 * OPT⌉`.

## References

* [G. Dósa, J. Sgall, *First Fit bin packing: A tight analysis*][DosaSgall2013]
* [M. R. Garey, R. L. Graham, D. S. Johnson, A. C.-C. Yao, *Resource constrained scheduling as
  generalized bin packing*][GareyGrahamJohnsonYao1976]
* [D. S. Johnson, A. Demers, J. D. Ullman, M. R. Garey, R. L. Graham, *Worst-case performance
  bounds for simple one-dimensional packing algorithms*][JohnsonDemersUllmanGareyGraham1974]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open scoped List

/-- The bonus of an item of size `a` in bins of capacity `C`, scaled by `10 * C`. -/
@[expose] def firstFitBonus (C a : ℕ) : ℕ :=
  if C < 2 * a then 4 * C else if C ≤ 3 * a then C else if C < 6 * a then 6 * a - C else 0

/-- The weight of an item of size `a`, scaled by `10 * C`. -/
@[expose] def firstFitWeight (C a : ℕ) : ℕ := 12 * a + firstFitBonus C a

private theorem firstFitBonus_add_le {C a b : ℕ} (h : 2 * (a + b) ≤ C) :
    firstFitBonus C a + firstFitBonus C b ≤ firstFitBonus C (a + b) := by
  unfold firstFitBonus
  split_ifs <;> omega

private theorem sum_map_firstFitBonus_le {C : ℕ} :
    ∀ {l : List ℕ}, 2 * l.sum ≤ C → (l.map (firstFitBonus C)).sum ≤ firstFitBonus C l.sum
  | [], _ => by simp [firstFitBonus]
  | a :: l, h => by
    simp only [List.sum_cons, List.map_cons] at h ⊢
    have ih := sum_map_firstFitBonus_le (C := C) (l := l) (by omega)
    have := firstFitBonus_add_le (C := C) (a := a) (b := l.sum) (by omega)
    omega

private theorem firstFitBonus_le_three_mul {C a : ℕ} (h : 2 * a ≤ C) :
    firstFitBonus C a ≤ 3 * a := by
  unfold firstFitBonus
  split_ifs <;> omega

private theorem sum_map_firstFitBonus_le_three_mul {C : ℕ} :
    ∀ {l : List ℕ}, (∀ a ∈ l, 2 * a ≤ C) → (l.map (firstFitBonus C)).sum ≤ 3 * l.sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.sum_cons, List.map_cons]
    have ih := sum_map_firstFitBonus_le_three_mul (C := C) (l := l)
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have := firstFitBonus_le_three_mul (h a List.mem_cons_self)
    omega

private theorem sum_map_firstFitWeight (C : ℕ) :
    ∀ l : List ℕ, (l.map (firstFitWeight C)).sum = 12 * l.sum + (l.map (firstFitBonus C)).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_firstFitWeight C l, firstFitWeight]
    ring

/-- **The weight of a bin is at most `17/10`**: the items of a bin of capacity `C` have total
weight at most `17 * C`, that is `17/10` after scaling by `10 * C`. -/
theorem sum_map_firstFitWeight_le {C : ℕ} {b : List ℕ} (hb : b.sum ≤ C) :
    (b.map (firstFitWeight C)).sum ≤ 17 * C := by
  rw [sum_map_firstFitWeight]
  by_cases hL : ∃ L ∈ b, C < 2 * L
  · obtain ⟨L, hLb, hL⟩ := hL
    have hperm := List.perm_cons_erase hLb
    have hs := hperm.sum_eq
    have hm := (hperm.map (firstFitBonus C)).sum_eq
    simp only [List.sum_cons, List.map_cons] at hs hm
    have hrest := sum_map_firstFitBonus_le (C := C) (l := b.erase L) (by omega)
    have h1 : firstFitBonus C L = 4 * C := by simp [firstFitBonus, hL]
    have h2 : firstFitBonus C (b.erase L).sum ≤ C := by
      unfold firstFitBonus
      split_ifs <;> omega
    omega
  · push Not at hL
    have := sum_map_firstFitBonus_le_three_mul (C := C) (l := b) (fun a ha => by
      have := hL a ha; omega)
    omega

/-- The indicator of items larger than half a bin. -/
private def bigInd (C a : ℕ) : ℕ := if C < 2 * a then 1 else 0

private theorem add_one_mul_sum_map_bigInd_le (C : ℕ) :
    ∀ b : List ℕ, (C + 1) * (b.map (bigInd C)).sum ≤ 2 * b.sum
  | [] => by simp
  | a :: b => by
    have := add_one_mul_sum_map_bigInd_le C b
    simp only [List.map_cons, List.sum_cons, bigInd, Nat.mul_add]
    split_ifs <;> omega

private theorem sum_map_bigInd_le {C : ℕ} {b : List ℕ} (hb : b.sum ≤ C) :
    (b.map (bigInd C)).sum ≤ 1 := by
  by_contra hcon
  have h1 := add_one_mul_sum_map_bigInd_le C b
  have h2 := Nat.mul_le_mul_left (C + 1) (show 2 ≤ (b.map (bigInd C)).sum by omega)
  omega

/-! ### The amortized weight of First Fit bins -/

/-- The First Fit rule between two bins `b` and `b'`, where `b` was opened first: every item of
`b'` overflows `b`. -/
private def Later (C : ℕ) (b b' : List ℕ) : Prop := ∀ c ∈ b', C < b.sum + c

/-- The bonus of a bin. -/
private abbrev V (C : ℕ) (b : List ℕ) : ℕ := (b.map (firstFitBonus C)).sum

/-- The weight of a bin. -/
private abbrev W (C : ℕ) (b : List ℕ) : ℕ := (b.map (firstFitWeight C)).sum

private theorem W_eq (C : ℕ) (b : List ℕ) : W C b = 12 * b.sum + V C b :=
  sum_map_firstFitWeight C b

/-- An item `c` that overflows a bin of load `s ≥ 2/3 * C` has bonus at least `5 * C - 6 * s`. -/
private theorem five_mul_le {C s c : ℕ} (hc : C < s + c) (hs : 2 * C ≤ 3 * s) :
    5 * C ≤ 6 * s + firstFitBonus C c := by
  unfold firstFitBonus
  split_ifs <;> omega

/-- **[Dósa and Sgall, Lemma 1.1][DosaSgall2013]**: if a bin `b` is at least `2/3` full and two
items of a later bin `b'` overflow it, then `12 * b.sum` plus the bonus of `b'` is at least
`10 * C`. -/
private theorem pair {C : ℕ} {b b' : List ℕ} (hR : Later C b b') (hs : 2 * C ≤ 3 * b.sum)
    (h2 : 2 ≤ b'.length) : 10 * C ≤ 12 * b.sum + V C b' := by
  match b', h2 with
  | c :: c' :: r, _ =>
    have h1 := five_mul_le (hR c (by simp)) hs
    have h2 := five_mul_le (hR c' (by simp)) hs
    simp only [V, List.map_cons, List.sum_cons]
    omega

/-- If a bin `b0` is less than `2/3` full, then every item of a later bin is larger than `C / 3`,
so a later bin with two or more items weighs at least `24 * (C + 1 - b0.sum) + 2 * C`. -/
private theorem after_bad {C : ℕ} {b0 b : List ℕ} (hR : Later C b0 b) (hs : 3 * b0.sum < 2 * C)
    (h2 : 2 ≤ b.length) : 24 * (C + 1) + 2 * C ≤ W C b + 24 * b0.sum := by
  rw [W_eq]
  match b, h2 with
  | c :: c' :: r, _ =>
    have h1 := hR c (by simp)
    have h2 := hR c' (by simp)
    have hv1 : C ≤ firstFitBonus C c := by unfold firstFitBonus; split_ifs <;> omega
    have hv2 : C ≤ firstFitBonus C c' := by unfold firstFitBonus; split_ifs <;> omega
    simp only [V, List.map_cons, List.sum_cons]
    omega

/-- Chaining Lemma 1.1 over bins at least `2/3` full, each with two or more items after the first:
the last bin pays `t ≤ 12 * sum` from its own size. -/
private theorem chain_end {C t : ℕ} :
    ∀ (x : List ℕ) (A : List (List ℕ)), (x :: A).Pairwise (Later C) →
      (∀ b ∈ x :: A, 2 * C ≤ 3 * b.sum ∧ t ≤ 12 * b.sum) → (∀ b ∈ A, 2 ≤ b.length) →
      10 * C * A.length + t + V C x ≤ W C x + (A.map (W C)).sum
  | x, [], _, hg, _ => by
    have := (hg x List.mem_cons_self).2
    rw [W_eq]
    simp only [List.length_nil, Nat.mul_zero, List.map_nil, List.sum_nil]
    omega
  | x, y :: A, hp, hg, hl => by
    have hxy : Later C x y := List.rel_of_pairwise_cons hp List.mem_cons_self
    have ih := chain_end y A (List.Pairwise.of_cons hp)
      (fun b hb => hg b (List.mem_cons_of_mem _ hb)) (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    have hpair := pair hxy (hg x List.mem_cons_self).1 (hl y List.mem_cons_self)
    have hWx := W_eq C x
    have hWy := W_eq C y
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    omega

/-- Chaining Lemma 1.1 over bins at least `2/3` full, followed by any bin `z` with two or more
items, whose bonus pays for the last of them. -/
private theorem chain_to {C : ℕ} (z : List ℕ) (hz : 2 ≤ z.length) :
    ∀ (x : List ℕ) (A : List (List ℕ)), (x :: A ++ [z]).Pairwise (Later C) →
      (∀ b ∈ x :: A, 2 * C ≤ 3 * b.sum) → (∀ b ∈ A, 2 ≤ b.length) →
      10 * C * (A.length + 1) + V C x ≤ W C x + (A.map (W C)).sum + V C z
  | x, [], hp, hg, _ => by
    have hxz : Later C x z := List.rel_of_pairwise_cons hp (by simp)
    have := pair hxz (hg x List.mem_cons_self) hz
    rw [W_eq]
    simp only [List.length_nil, List.map_nil, List.sum_nil]
    omega
  | x, y :: A, hp, hg, hl => by
    have hxy : Later C x y := List.rel_of_pairwise_cons hp (by simp)
    have ih := chain_to z hz y A (List.Pairwise.of_cons hp)
      (fun b hb => hg b (List.mem_cons_of_mem _ hb)) (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    have hpair := pair hxy (hg x List.mem_cons_self) (hl y List.mem_cons_self)
    have hWx := W_eq C x
    have hWy := W_eq C y
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ] at ih ⊢
    omega

/-- If two items of a later bin `c0` overflow `b`, then `2 * C + 2 ≤ 2 * b.sum + c0.sum`. -/
private theorem two_mul_add_le_of_later {C : ℕ} {b c0 : List ℕ} (hR : Later C b c0)
    (h2 : 2 ≤ c0.length) : 2 * C + 2 ≤ 2 * b.sum + c0.sum := by
  match c0, h2 with
  | c :: c' :: r, _ =>
    have h1 := hR c (by simp)
    have h2 := hR c' (by simp)
    simp only [List.sum_cons]
    omega

/-- `chain_to` for a possibly empty chain, dropping the first bin's bonus. -/
private theorem chain_to' {C : ℕ} (z : List ℕ) (hz : 2 ≤ z.length) (A : List (List ℕ))
    (hp : (A ++ [z]).Pairwise (Later C)) (hg : ∀ b ∈ A, 2 * C ≤ 3 * b.sum)
    (hl : ∀ b ∈ A, 2 ≤ b.length) : 10 * C * A.length ≤ (A.map (W C)).sum + V C z := by
  match A, hp, hg, hl with
  | [], _, _, _ => simp
  | x :: A, hp, hg, hl =>
    have := chain_to z hz x A hp hg (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The number of items of a bin larger than half a bin. -/
private abbrev Big (C : ℕ) (b : List ℕ) : ℕ := (b.map (bigInd C)).sum

/-- Bins each holding one item larger than `C / 2` weigh more than `10 * C` each. -/
private theorem big_singletons {C : ℕ} :
    ∀ {D : List (List ℕ)}, (∀ b ∈ D, ∃ d, b = [d] ∧ C < 2 * d) →
      10 * C * D.length ≤ (D.map (W C)).sum ∧ D.length ≤ (D.map (Big C)).sum
  | [], _ => by simp
  | b :: D, h => by
    obtain ⟨d, rfl, hd⟩ := h b List.mem_cons_self
    have ih := big_singletons (C := C) (D := D) (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h1 : 10 * C ≤ W C [d] := by simp [W, firstFitWeight, firstFitBonus, hd]; omega
    have h2 : Big C [d] = 1 := by simp [Big, bigInd, hd]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- Two distinct members of a list that is pairwise related are related one way or the other. -/
private theorem rel_or_rel {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hx with hx | hx <;> rcases List.mem_cons.1 hy with hy | hy
    · exact absurd (hx.trans hy.symm) hne
    · exact Or.inl (hx ▸ h.1 y hy)
    · exact Or.inr (hy ▸ h.1 x hx)
    · exact rel_or_rel h.2 hx hy hne

/-- The single-item bins: all but at most one hold an item larger than half a bin. -/
private theorem singletons_cases {C : ℕ} {D : List (List ℕ)} (hDp : D.Pairwise (Later C))
    (hD1 : ∀ b ∈ D, ∃ d, b = [d]) :
    (10 * C * D.length ≤ (D.map (W C)).sum ∧ D.length ≤ (D.map (Big C)).sum) ∨
      ∃ d k, [d] ∈ D ∧ 2 * d ≤ C ∧ D.length = k + 1 ∧ 10 * C * k + 12 * d ≤ (D.map (W C)).sum ∧
        k ≤ (D.map (Big C)).sum := by
  cases hf : D.find? (fun b => decide (2 * b.sum ≤ C)) with
  | none =>
    left
    rw [List.find?_eq_none] at hf
    apply big_singletons
    intro b hb
    obtain ⟨d, rfl⟩ := hD1 b hb
    have := hf _ hb
    simp only [List.sum_singleton, decide_eq_true_eq, not_le] at this
    exact ⟨d, rfl, this⟩
  | some b0 =>
    right
    rw [List.find?_eq_some_iff_append] at hf
    obtain ⟨hb0, D1, D2, rfl, hD1'⟩ := hf
    obtain ⟨d, rfl⟩ := hD1 b0 (by simp)
    simp only [List.sum_singleton, decide_eq_true_eq] at hb0
    obtain ⟨-, hc, -⟩ := List.pairwise_append.1 hDp
    have hD2 := (List.pairwise_cons.1 (List.pairwise_append.1 hDp).2.1).1
    have hbig := big_singletons (C := C) (D := D1 ++ D2) (by
      intro b hb
      obtain ⟨d', rfl⟩ := hD1 b (by
        rcases List.mem_append.1 hb with hb | hb
        · exact List.mem_append_left _ hb
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hb))
      refine ⟨d', rfl, ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · have := hD1' _ hb
        simp only [List.sum_singleton, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at this
        exact this
      · have := hD2 _ hb d' (by simp)
        simp only [List.sum_singleton] at this
        omega)
    have hWd : 12 * d ≤ W C [d] := by simp [W, firstFitWeight]
    simp only [List.length_append, List.map_append, List.sum_append] at hbig
    refine ⟨d, D1.length + D2.length, by simp, hb0, by simp; omega, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega
    · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega

/-- The bins with at least two items: all but at most one are at least `2/3` full, and every
bin after a bin less than `2/3` full is at least `2/3` full. -/
private theorem multi_cases {C : ℕ} {G : List (List ℕ)} :
    (∀ g ∈ G, 2 * C ≤ 3 * g.sum) ∨
      ∃ A c0 B, G = A ++ c0 :: B ∧ 3 * c0.sum < 2 * C ∧ ∀ a ∈ A, 2 * C ≤ 3 * a.sum := by
  cases hf : G.find? (fun g => decide (3 * g.sum < 2 * C)) with
  | none =>
    left
    rw [List.find?_eq_none] at hf
    intro g hg
    have := hf g hg
    simp only [decide_eq_true_eq, not_lt] at this
    exact this
  | some c0 =>
    right
    rw [List.find?_eq_some_iff_append] at hf
    obtain ⟨h0, A, B, hAB, hA⟩ := hf
    refine ⟨A, c0, B, hAB, by simpa using h0, fun a ha => ?_⟩
    have := hA a ha
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at this
    exact this

/-- The amortized weight bound on bins split into those with at least two items and those with
one item. -/
private theorem core_split {C : ℕ} {G D : List (List ℕ)}
    (hGp : G.Pairwise (Later C)) (hG2 : ∀ g ∈ G, 2 ≤ g.length)
    (hDp : D.Pairwise (Later C)) (hD1 : ∀ b ∈ D, ∃ d, b = [d])
    (hcross : ∀ d, [d] ∈ D → 2 * d ≤ C → ∀ g ∈ G, C < g.sum + d) :
    10 * C * (G.length + D.length) ≤ (G.map (W C)).sum + (D.map (W C)).sum + 8 * C ∨
      G.length + D.length ≤ (G.map (Big C)).sum + (D.map (Big C)).sum + 1 := by
  have hD := singletons_cases hDp hD1
  rcases multi_cases (C := C) (G := G) with hgood | ⟨A, c0, B, rfl, hs0, hA⟩
  · -- every bin with two or more items is at least `2/3` full
    match G, hGp, hG2, hgood, hcross with
    | [], _, _, _, _ =>
      right
      rcases hD with ⟨-, h⟩ | ⟨d, k, -, -, hk, -, h⟩ <;> simp only [List.length_nil] <;> omega
    | x :: A', hGp, hG2, hgood, hcross =>
      left
      have hl : ∀ b ∈ A', 2 ≤ b.length := fun b hb => hG2 b (List.mem_cons_of_mem _ hb)
      rcases hD with ⟨hD, -⟩ | ⟨d, k, hd, hd2, hk, hD, -⟩
      · have := chain_end (t := 8 * C) x A' hGp (fun b hb => ⟨hgood b hb, by
          have := hgood b hb; omega⟩) hl
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        nlinarith
      · obtain ⟨t, ht⟩ : ∃ t, t + 12 * d = 12 * C + 12 := ⟨12 * C + 12 - 12 * d, by omega⟩
        have := chain_end (t := t) x A' hGp (fun b hb => ⟨hgood b hb, by
          have := hcross d hd hd2 b hb; omega⟩) hl
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        rw [hk]
        nlinarith
  · -- the bin `c0` is less than `2/3` full
    have hc0 : 2 ≤ c0.length := hG2 c0 (by simp)
    have hA2 : ∀ a ∈ A, 2 ≤ a.length := fun a ha => hG2 a (List.mem_append_left _ ha)
    have hAc : (A ++ [c0]).Pairwise (Later C) :=
      hGp.sublist ((List.cons_sublist_cons.2 (List.nil_sublist B)).append_left A)
    have hcB : ∀ b ∈ B, Later C c0 b :=
      (List.pairwise_cons.1 (List.pairwise_append.1 hGp).2.1).1
    have hAc0 : ∀ a ∈ A, Later C a c0 := fun a ha =>
      List.Pairwise.rel_of_mem_append hGp ha List.mem_cons_self
    have hWc0 := W_eq C c0
    match B, hcB with
    | b1 :: B', hcB =>
      -- a bin follows `c0`
      left
      have hchain := chain_to' c0 hc0 A hAc hA hA2
      have hb1 := after_bad (hcB b1 List.mem_cons_self) hs0 (hG2 b1 (by simp))
      have hB' : B'.length * (10 * C) ≤ (B'.map (W C)).sum := by
        simpa using List.length_nsmul_le_sum (B'.map (W C)) (10 * C) (by
          intro w hw
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hw
          have := after_bad (hcB b (List.mem_cons_of_mem _ hb)) hs0 (hG2 b (by simp [hb]))
          omega)
      simp only [List.length_append, List.length_cons, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons]
      rcases hD with ⟨hD, -⟩ | ⟨d, k, hd, hd2, hk, hD, -⟩
      · nlinarith
      · have := hcross d hd hd2 c0 (by simp)
        rw [hk]
        nlinarith
    | [], _ =>
      match A, hA, hA2, hAc, hAc0 with
      | x :: A', hA, hA2, hAc, hAc0 =>
        -- `c0` is the last bin with two or more items, after at least one other
        left
        simp only [List.length_append, List.length_cons, List.length_nil, List.map_append,
          List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
        rcases hD with ⟨hD, -⟩ | ⟨d, k, hd, hd2, hk, hD, -⟩
        · obtain ⟨t, ht⟩ : ∃ t, t + 6 * c0.sum = 12 * C + 12 :=
            ⟨12 * C + 12 - 6 * c0.sum, by omega⟩
          have := chain_end (t := t) x A' (hAc.sublist (List.sublist_append_left _ _))
            (fun b hb => ⟨hA b hb, by
              have := two_mul_add_le_of_later (hAc0 b hb) hc0; omega⟩)
            (fun b hb => hA2 b (List.mem_cons_of_mem _ hb))
          nlinarith
        · have := chain_to c0 hc0 x A' hAc hA (fun b hb => hA2 b (List.mem_cons_of_mem _ hb))
          have := hcross d hd hd2 c0 (by simp)
          rw [hk]
          nlinarith
      | [], _, _, _, _ =>
        -- `c0` is the only bin with two or more items
        simp only [List.nil_append, List.length_cons, List.length_nil, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        rcases hD with ⟨hD, hDb⟩ | ⟨d, k, hd, hd2, hk, hD, -⟩
        · right
          omega
        · left
          have := hcross d hd hd2 c0 (by simp)
          rw [hk]
          nlinarith

/-- The amortized weight bound for a list of nonempty bins satisfying the First Fit rule: they
weigh at least `10 * C` each up to `8 * C` in total, or all but one hold an item larger than
`C / 2`. -/
private theorem core {C : ℕ} {bins : List (List ℕ)} (hp : bins.Pairwise (Later C))
    (hne : ∀ b ∈ bins, b ≠ []) (hle : ∀ b ∈ bins, b.sum ≤ C) :
    10 * C * bins.length ≤ (bins.map (W C)).sum + 8 * C ∨
      bins.length ≤ (bins.map (Big C)).sum + 1 := by
  have hperm := List.filter_append_perm (fun b : List ℕ => decide (2 ≤ b.length)) bins
  have hlen := hperm.length_eq
  have hW := (hperm.map (W C)).sum_eq
  have hI := (hperm.map (Big C)).sum_eq
  simp only [List.length_append, List.map_append, List.sum_append] at hlen hW hI
  rw [← hlen, ← hW, ← hI]
  refine core_split (hp.filter _) (fun g hg => by simpa using (List.mem_filter.1 hg).2)
    (hp.filter _) (fun b hb => ?_) (fun d hd hd2 g hg => ?_)
  · rw [List.mem_filter] at hb
    have h1 := hne b hb.1
    have h2 : b.length < 2 := by simpa using hb.2
    match b, h1, h2 with
    | [], h1, _ => exact absurd rfl h1
    | [d], _, _ => exact ⟨d, rfl⟩
    | _ :: _ :: _, _, h2 => simp only [List.length_cons] at h2; omega
  · rw [List.mem_filter] at hd hg
    have hg2 : 2 ≤ g.length := by simpa using hg.2
    have hne' : g ≠ [d] := fun h => by simp [h] at hg2
    rcases rel_or_rel hp hg.1 hd.1 hne' with h | h
    · simpa using h d (by simp)
    · exfalso
      have hgle := hle g hg.1
      match g, hg2 with
      | c :: c' :: r, _ =>
        have h1 := h c (by simp)
        have h2 := h c' (by simp)
        simp only [List.sum_cons] at h1 h2 hgle
        simp only [List.sum_nil] at h1 h2
        omega

/-- A weight summed over the items of bins that hold exactly `l` is its sum over `l`. -/
private theorem sum_map_eq_of_perm {f : ℕ → ℕ} {l : List ℕ} {F : List (List ℕ)}
    (h : F.flatten ~ l) : (l.map f).sum = (F.map fun b => (b.map f).sum).sum := by
  rw [← (h.map f).sum_eq, List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- **First Fit uses at most `17/10 * OPT + 4/5` bins**: against any packing `Q` of the same
items, `10 * FF ≤ 17 * Q.length + 8`. This is the asymptotic `17/10` bound of
[Johnson, Demers, Ullman, Garey and Graham][JohnsonDemersUllmanGareyGraham1974] with the additive
constant `4/5`, by the weighting argument of [Dósa and Sgall, Section 1.2][DosaSgall2013]. The
constant is not tight: Dósa and Sgall prove `FF ≤ ⌊17/10 * OPT⌋`. -/
theorem ten_mul_length_firstFit_le {C : ℕ} {l : List ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking C l Q) : 10 * (firstFit C l).length ≤ 17 * Q.length + 8 := by
  have hF := isPacking_firstFit fun a ha => hQ.le_of_mem ha
  have key : (firstFit C l).length ≤ Q.length + 1 →
      10 * (firstFit C l).length ≤ 17 * Q.length + 8 := by
    intro h
    rcases l with _ | ⟨a, l⟩
    · simp [firstFit]
    · have := List.length_pos_iff.2 (hQ.ne_nil (List.cons_ne_nil a l))
      omega
  have hW := hQ.sum_map_le_mul_length (firstFitWeight C) fun b hb => sum_map_firstFitWeight_le hb
  have hB := hQ.sum_map_le_mul_length (bigInd C) fun b hb => sum_map_bigInd_le hb
  rw [sum_map_eq_of_perm hF.perm] at hW hB
  rcases core (pairwise_forall_lt_sum_add_firstFit C l) (fun b hb => ne_nil_of_mem_firstFit hb)
    hF.sum_le with h | h
  · rcases Nat.eq_zero_or_pos C with rfl | hC
    · apply key
      have hp0 := pairwise_firstFit 0 l
      have hs := hF.sum_le
      generalize firstFit 0 l = F at hp0 hs ⊢
      match F, hp0, hs with
      | [], _, _ => simp
      | [_], _, _ => simp
      | b :: b' :: _, hp0, hs =>
        have := List.rel_of_pairwise_cons hp0 List.mem_cons_self
        have h1 := hs b (by simp)
        have h2 := hs b' (by simp)
        omega
    · refine Nat.le_of_mul_le_mul_left ?_ hC
      have : (firstFit C l).map (W C) =
          (firstFit C l).map fun b => (b.map (firstFitWeight C)).sum := rfl
      rw [this] at h
      nlinarith
  · apply key
    have : (firstFit C l).map (Big C) = (firstFit C l).map fun b => (b.map (bigInd C)).sum := rfl
    rw [this] at h
    nlinarith

/-- **First Fit uses at most `⌈17/10 * OPT⌉` bins**, the bound of
[Garey, Graham, Johnson and Yao][GareyGrahamJohnsonYao1976] as reported by
[Dósa and Sgall, Section 1.1][DosaSgall2013]. -/
theorem length_firstFit_le_ceil {C : ℕ} {l : List ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking C l Q) : (firstFit C l).length ≤ ⌈(17 / 10 : ℚ) * Q.length⌉₊ := by
  have h := ten_mul_length_firstFit_le hQ
  rcases Nat.eq_zero_or_pos (firstFit C l).length with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · obtain ⟨n, hn⟩ : ∃ n, (firstFit C l).length = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hn] at h ⊢
    rw [Nat.add_one_le_iff, Nat.lt_ceil]
    have : (10 * (n + 1) : ℚ) ≤ 17 * Q.length + 8 := by exact_mod_cast h
    linarith

end Cslib.Algorithms.Lean.BinPacking
