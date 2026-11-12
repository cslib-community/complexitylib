/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TrimmedYates
public import CslibFrontier.Foundations.Combinatorics.BinomialZeta

/-!
# Selected entries of ranked convolution in `[r]^d`

Selected entries of the ranked convolution of vectors in `[r]^d` by trimmed binomial passes,
following [ChanItakuraMaYu2026], Lemma 3.2 and Theorem 3.3 (Section 3.1).

Vectors are functions `ι → ℕ`, processed in the order of a duplicate-free list `l` of all
coordinates; the cube `[r]^d` is the set of vectors with every coordinate below `r`, and the size
of a vector is the sum of its coordinates. The algorithm is the trimmed algorithm of
`CslibFrontier.Algorithms.Lean.TrimmedYates` for the scheme `vecPasses` of binomial passes
(`Cslib.binomPass`):

* **preprocessing** runs every stage of the binomial zeta transforms of `f` and `g`, and of the
  binomial Möbius transform of their pointwise product, on the vectors of the cube with size at
  most `s` (`lowCells`);
* **a query** `C` runs the same stages on the vectors below `C` with size at least `s`
  (`highCells`).

The paper obtains the same computation by viewing a vector as the multiplicity vector of subsets of
`[d r]` and storing one representative per multiplicity class (Lemma 3.2). Here the passes act on
multiplicity vectors directly: the zeta transform of a multiplicity-invariant function at a set
with multiplicities `x` is `binomTransform 1 F x`, and its trimmed passes read the `O(r)` values
`F x'` with `x'` equal to `x` except in one coordinate. See `Cslib.binomTransform`.

For `f` supported on vectors of size `t₁`, `g` on vectors of size `t₂` and queries of size
`t₁ + t₂`, the answers are the binomial convolution
`∑_{a ≤ C} (∏ i, (C i choose a i)) f a g (C - a)` (`ret_solveM`). Weighting the inputs by the
factorials of their coordinates gives `(∏ i, (C i)!) (f ⋆ g) C`, the vector convolution of
Problem 3.1 times a known nonzero factor (`ret_solveM_factorial`): the reduction of Theorem 3.3.

## Cost model

The unit-cost model of `CslibFrontier.Algorithms.Lean.TrimmedYates`, with a vector of the cube as
a dictionary key.

* **Charged:** `1` tick for reading an input at one vector or multiplying two transform values,
  and `r` ticks for one pass at one vector, which reads at most `r` table entries and takes as many
  products with binomial coefficients and additions.
* **Uncharged:** enumerating the cells (`boxList`), building dictionaries and loop control.

The count is exact (`time_solveM`): `3 (r d + 1)` ticks per vector of the cube with size at most
`s` and per vector below a query with size at least `s`, i.e.
`3 (r d + 1) (H_r(d, ≤ s) + ∑_C #{y ≤ C : s ≤ |y|})`. This is Lemma 3.2's
`(H_r(d, ≤ s) + |C| H_r(d, t, ≥ s)) (d r) ^ O(1)` without the term `n` for storing the inputs,
which are given as look-up functions.

## Main definitions

* `Cslib.Algorithms.Lean.VectorConvolution.boxList`: the vectors of a box, as a list.
* `Cslib.Algorithms.Lean.VectorConvolution.vecPasses`: the scheme of binomial passes.
* `Cslib.Algorithms.Lean.VectorConvolution.lowCells`, `highCells`, `solveM`: the algorithm.

## Main results

* `Cslib.Algorithms.Lean.VectorConvolution.ret_solveM`: ranked queries return the binomial
  convolution.
* `Cslib.Algorithms.Lean.VectorConvolution.ret_solveM_factorial`: with factorial weights, the
  vector convolution ([ChanItakuraMaYu2026], Theorem 3.3).
* `Cslib.Algorithms.Lean.VectorConvolution.time_solveM`: the exact tick count
  ([ChanItakuraMaYu2026], Lemma 3.2).

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.VectorConvolution

open Finset Cslib Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.TrimmedYates

universe u

variable {ι : Type u} [DecidableEq ι]

/-! ### Boxes -/

/-- The vectors `y` with `y i < n i` for the coordinates `i` of `l` and `y i = 0` elsewhere, as a
list. -/
@[expose] def boxList : List ι → (ι → ℕ) → List (ι → ℕ)
  | [], _ => [0]
  | i :: l, n =>
    (boxList l n).flatMap fun x => (List.range (n i)).map fun k => Function.update x i k

theorem mem_boxList {l : List ι} (hl : l.Nodup) (n : ι → ℕ) {y : ι → ℕ} :
    y ∈ boxList l n ↔ (∀ i ∈ l, y i < n i) ∧ ∀ i ∉ l, y i = 0 := by
  induction l generalizing y with
  | nil =>
    simp only [boxList, List.mem_singleton, List.not_mem_nil, false_imp_iff, implies_true,
      not_false_eq_true, forall_const, true_and]
    exact ⟨fun h i => by simp [h], fun h => funext h⟩
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    simp only [boxList, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
      forall_eq_or_imp, not_or]
    constructor
    · rintro ⟨x, hx, k, hk, rfl⟩
      obtain ⟨hx1, hx2⟩ := (ih (List.nodup_cons.mp hl).2).mp hx
      refine ⟨⟨by simpa using hk, fun j hj => ?_⟩, fun j ⟨hji, hjl⟩ => ?_⟩
      · rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
        exact hx1 j hj
      · rw [Function.update_of_ne hji]
        exact hx2 j hjl
    · rintro ⟨⟨hyi, hyl⟩, hy0⟩
      refine ⟨Function.update y i 0, (ih (List.nodup_cons.mp hl).2).mpr ⟨fun j hj => ?_,
        fun j hj => ?_⟩, y i, hyi, by simp⟩
      · rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
        exact hyl j hj
      · rcases eq_or_ne j i with rfl | hji
        · simp
        · rw [Function.update_of_ne hji]
          exact hy0 j ⟨hji, hj⟩

theorem nodup_boxList {l : List ι} (hl : l.Nodup) (n : ι → ℕ) : (boxList l n).Nodup := by
  induction l with
  | nil => simp [boxList]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    have hzero : ∀ x ∈ boxList l n, x i = 0 := fun x hx => ((mem_boxList hl' n).mp hx).2 i hi
    refine List.nodup_flatMap.mpr ⟨fun x _ => (List.nodup_range).map fun k k' h => ?_, ?_⟩
    · simpa using congrFun h i
    · refine (ih hl').imp_of_mem fun {x x'} hx hx' hne => ?_
      refine List.disjoint_left.mpr fun {z} hz hz' => hne ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hz
      obtain ⟨k', -, hkk⟩ := List.mem_map.mp hz'
      funext j
      rcases eq_or_ne j i with rfl | hji
      · rw [hzero x hx, hzero x' hx']
      · have := congrFun hkk j
        rwa [Function.update_of_ne hji, Function.update_of_ne hji, eq_comm] at this

/-- With every coordinate in `l`, the box is the product of the ranges `[0, n i)`. -/
theorem toFinset_boxList [Fintype ι] {l : List ι} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (n : ι → ℕ) : (boxList l n).toFinset = Fintype.piFinset fun i => range (n i) := by
  ext y
  simp only [List.mem_toFinset, mem_boxList hl, hall, true_imp_iff, not_true_eq_false,
    false_imp_iff, implies_true, and_true, Fintype.mem_piFinset, mem_range]

/-! ### The scheme of binomial passes -/

variable [Fintype ι] {R : Type u} [CommRing R]

/-- **Binomial passes** on vectors over the coordinates `l`, graded by size, at `r` ticks per
cell of a pass. -/
@[expose] def vecPasses (l : List ι) (r : ℕ) : Passes ι (ι → ℕ) R where
  coords := l
  zeta := binomPass 1
  mobius := binomPass (-1)
  size x := ∑ i, x i
  cost := r

/-- The vectors of the cube `[r]^d` with size at most `s`. -/
@[expose] def lowCells (l : List ι) (r s : ℕ) : List (ι → ℕ) :=
  (boxList l fun _ => r).filter fun x => ∑ i, x i ≤ s

/-- The vectors below `C` with size at least `s`. -/
@[expose] def highCells (l : List ι) (s : ℕ) (C : ι → ℕ) : List (ι → ℕ) :=
  (boxList l fun i => C i + 1).filter fun y => s ≤ ∑ i, y i

/-- **Selected entries of the ranked convolution in `[r]^d`**: preprocess the vectors of the cube
with size at most `s` once, then answer each query `C` on the vectors below it with size at least
`s`. -/
@[expose] def solveM (l : List ι) (r s : ℕ) (f g : (ι → ℕ) → R) (Cs : List (ι → ℕ)) :
    TimeM ℕ (List R) :=
  (vecPasses l r).solveM s (lowCells l r s) (highCells l s) f g Cs

/-- Binomial passes read only vectors below the cell, and the cube is closed downwards. -/
theorem vecPasses_local (l : List ι) (r : ℕ) :
    (vecPasses (R := R) l r).Local fun x => ∀ i, x i < r where
  zeta_congr i _ _ _ h := binomPass_congr 1 i h
  mobius_congr i _ _ _ h := binomPass_congr (-1) i h
  size_mono _ _ h := sum_le_sum fun i _ => h i
  closed h hX i := (h i).trans_lt (hX i)

variable {l : List ι}

theorem mem_lowCells (hl : l.Nodup) (hall : ∀ i, i ∈ l) (r s : ℕ) (y : ι → ℕ) :
    y ∈ lowCells l r s ↔ (∀ i, y i < r) ∧ ∑ i, y i ≤ s := by
  simp [lowCells, List.mem_filter, mem_boxList hl, hall]

theorem mem_highCells (hl : l.Nodup) (hall : ∀ i, i ∈ l) (s : ℕ) (C y : ι → ℕ) :
    y ∈ highCells l s C ↔ y ≤ C ∧ s ≤ ∑ i, y i := by
  simp [highCells, List.mem_filter, mem_boxList hl, hall, Pi.le_def]

/-- The full binomial passes are the binomial transforms. -/
private theorem vecPasses_mobiusAll (hl : l.Nodup) (hall : ∀ i, i ∈ l) (r : ℕ)
    (f g : (ι → ℕ) → R) :
    (vecPasses l r).mobiusAll (fun X => (vecPasses l r).zetaAll f X * (vecPasses l r).zetaAll g X) =
      binomTransform (-1) fun x => binomTransform 1 f x * binomTransform 1 g x := by
  simp only [Passes.mobiusAll, Passes.zetaAll, vecPasses, foldl_binomPass hl hall]

/-! ### Correctness -/

/-- **Ranked queries return the binomial convolution**: if `f` is supported on vectors of size
`t₁`, `g` on vectors of size `t₂`, and every query is a vector of the cube `[r]^d` of size
`t₁ + t₂`, the answers are `∑_{a ≤ C} (∏ i, (C i choose a i)) f a g (C - a)`, for every threshold
`s ≤ t₁ + t₂`. -/
theorem ret_solveM (hl : l.Nodup) (hall : ∀ i, i ∈ l) {r s t₁ t₂ : ℕ} {f g : (ι → ℕ) → R}
    (hf : ∀ a, f a ≠ 0 → ∑ i, a i = t₁) (hg : ∀ b, g b ≠ 0 → ∑ i, b i = t₂)
    {Cs : List (ι → ℕ)} (hCs : ∀ C ∈ Cs, (∀ i, C i < r) ∧ ∑ i, C i = t₁ + t₂)
    (hs : s ≤ t₁ + t₂) :
    (solveM l r s f g Cs).ret = Cs.map (binomConvolution f g) := by
  rw [solveM, Passes.ret_solveM (vecPasses_local l r) (mem_lowCells hl hall r s)
    (fun C hC => ⟨(hCs C hC).1, show s ≤ ∑ i, C i from (hCs C hC).2 ▸ hs,
      mem_highCells hl hall s C⟩), vecPasses_mobiusAll hl hall]
  exact List.map_congr_left fun C hC =>
    binomTransform_neg_one_mul_eq_binomConvolution hf hg (hCs C hC).2

/-- **Vector convolution** ([ChanItakuraMaYu2026], Theorem 3.3): weighting the inputs by the
factorials of their coordinates, the answers are `(∏ i, (C i)!) (f ⋆ g) C`. -/
theorem ret_solveM_factorial (hl : l.Nodup) (hall : ∀ i, i ∈ l) {r s t₁ t₂ : ℕ}
    {f g : (ι → ℕ) → R} (hf : ∀ a, f a ≠ 0 → ∑ i, a i = t₁)
    (hg : ∀ b, g b ≠ 0 → ∑ i, b i = t₂) {Cs : List (ι → ℕ)}
    (hCs : ∀ C ∈ Cs, (∀ i, C i < r) ∧ ∑ i, C i = t₁ + t₂) (hs : s ≤ t₁ + t₂) :
    (solveM l r s (fun a => (vecFactorial a : R) * f a) (fun b => (vecFactorial b : R) * g b)
      Cs).ret = Cs.map fun C => (vecFactorial C : R) * vecConvolution f g C := by
  rw [ret_solveM hl hall (fun a h => hf a (right_ne_zero_of_mul h))
    (fun b h => hg b (right_ne_zero_of_mul h)) hCs hs]
  exact List.map_congr_left fun C _ => binomConvolution_factorial f g C

/-! ### Cost -/

theorem length_lowCells (hl : l.Nodup) (hall : ∀ i, i ∈ l) (r s : ℕ) :
    (lowCells l r s).length =
      #((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) := by
  rw [lowCells, ← List.toFinset_card_of_nodup ((nodup_boxList hl _).filter _),
    List.toFinset_filter, toFinset_boxList hl hall]
  simp

theorem length_highCells (hl : l.Nodup) (hall : ∀ i, i ∈ l) (s : ℕ) (C : ι → ℕ) :
    (highCells l s C).length = #((Iic C).filter fun y => s ≤ ∑ i, y i) := by
  rw [highCells, ← List.toFinset_card_of_nodup ((nodup_boxList hl _).filter _),
    List.toFinset_filter, toFinset_boxList hl hall, Iic_eq_piFinset_range]
  simp

/-- **The cost of [ChanItakuraMaYu2026], Lemma 3.2**, exactly: for `d = l.length` coordinates,
`solveM` takes `3 (r d + 1)` ticks per vector of the cube `[r]^d` with size at most `s` and per
vector below each query with size at least `s`. -/
theorem time_solveM (hl : l.Nodup) (hall : ∀ i, i ∈ l) (r s : ℕ) (f g : (ι → ℕ) → R)
    (Cs : List (ι → ℕ)) :
    (solveM l r s f g Cs).time = 3 * (r * l.length + 1) *
      (#((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) +
        (Cs.map fun C => #((Iic C).filter fun y => s ≤ ∑ i, y i)).sum) := by
  rw [solveM, Passes.time_solveM, length_lowCells hl hall,
    List.map_congr_left fun C _ => length_highCells hl hall s C]
  rfl

end Cslib.Algorithms.Lean.VectorConvolution
