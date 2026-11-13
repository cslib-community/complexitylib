/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Packing
public import CslibFrontier.Privacy.DifferentialPrivacy.Sensitivity
import CslibFrontier.Foundations.Data.Code.HammingBound

/-!
# De's lower bound over a small universe

Answering `k` queries of sensitivity `1` with pure privacy needs noise `Ω(min (k, d) / ε)` even when
the universe has only `d` items [DworkRoth2014, Theorem 8.8], a theorem Dwork and Roth credit to
De (§8.3). For `ε ∈ (0, 1 / 40]` and databases of `n ≥ min (k, d) / ε` rows there is a query
`F` into `ℝ ^ k`, of sensitivity at most `1` in each coordinate, such that every
`(ε, 0)`-private mechanism adds noise of `ℓ∞` norm `Ω(min (k, d) / ε)` with probability at least
`1 / 2` on some database. The one-way marginals bound of
`CslibFrontier.Privacy.DifferentialPrivacy.Packing` [DworkRoth2014, Theorem 8.7] needs a universe of
`2 ^ k` items; this one does not.

Datasets are tuples `x : ι → X` of `n = |ι|` rows from a universe `X` of `d` items, compared by
`HammingAdjacent`. Dwork and Roth work with histograms in `ℕ ^ d`. A query of tuples is a query of
histograms exactly when reordering the rows does not change it, and the query `F` here has this
property. Without it the size of the universe would play no role, since a query could read
individual rows.

The construction:

* `rowCount x a` is the histogram of `x`, and `countExcess x y = ∑ a, (rowCount x a - rowCount y a)`
  counts the rows of `x` with no matching row of `y`. It depends only on the two histograms
  (`countExcess_comp_equiv_right`), is at most the Hamming distance
  (`countExcess_le_hammingDist`) and satisfies the triangle inequality (`countExcess_le_add`).
* McShane's extension `G y = min_h (g h + countExcess (D h) y)` of labels `g h` on datasets `D h`
  is invariant under reordering, `1`-Lipschitz in Hamming distance, and equal to `g h` on `D h` when
  `g h ≤ g h' + countExcess (D h') (D h)` (`exists_symmetric_lipschitz_extension`).
* A code of `2 ^ L` words of length `L` over `16` letters, any two at distance at least `L / 2`
  (`Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist`, by the Gilbert–Varshamov
  bound), becomes a family of datasets. The word `c` puts the item `(j, c j)` in `t` rows for each
  coordinate `j`, and a filler item in all other rows. Encodings of distinct words have excess at
  least `t L / 2` over each other, and all are within Hamming distance `t L` of the all-filler
  dataset. Label the words by the bit strings `w` of length `L ≤ k`, and let the `j`-th
  coordinate of `F` be the McShane extension of `± t L / 4`, signed by the bit `w j`. Then the
  `ℓ∞` balls of radius `t L / 4` around the answers on the encodings are disjoint, and the
  packing bound `DifferentiallyPrivate.card_mul_le_of_hammingDist_le_of_pure` gives
  `2 ^ L · p ≤ exp (t L ε)` (`exists_symmetric_query_two_pow_mul_le`).
* `L = min (k, ⌊(d - 1) / 16⌋)` and `t = ⌊1 / (6 ε)⌋` give Theorem 8.8 with the explicit noise bound
  `min (k, d) / (1024 ε)` (`exists_symmetric_query_forall_exists_half_lt`).

Dwork and Roth sketch the code without details and take `k` random `± 1` combinations of bump
functions around the codewords, with a Chernoff and a union bound to separate the answers. An
`ℓ∞` separation needs only one coordinate for each pair of codewords, so labelling the codewords by
`L ≤ k` bits makes the query deterministic, and McShane's extension replaces the bump functions.
This simplifies the proof; the theorem is theirs.

Scope, relative to [DworkRoth2014, Theorem 8.8]:

* Adjacency replaces one of exactly `n` rows. Dwork and Roth add or remove a row of a histogram of
  weight at most `n`. Replacing a row is removing one and adding one, so a mechanism that is
  `(ε, 0)`-private for their adjacency is `(2 ε, 0)`-private for this one. With `2 ε ≤ 1 / 18`
  this covers their range `ε ≤ 1 / 40`, with noise `min (k, d) / (2048 ε)`. The transfer also
  needs `F` extended from histograms of weight `n` to all of `ℕ ^ d`: on weight `n`, a query that
  is invariant under reordering and `1`-Lipschitz in Hamming distance is `1 / 2`-Lipschitz in
  `ℓ₁`, and McShane's extension keeps that constant. The transfer is not formalized here.
* The theorem needs `k ≥ 2` and `d ≥ 33`. Dwork and Roth's proof needs `min (k, d) ≥ 400` for its
  code to have more than one word. It assumes `ε ≤ 1 / 18`, which Dwork and Roth's `ε ≤ 1 / 40`
  implies.
* As everywhere in the library, mechanisms have discrete output laws (`PMF`).

## Main definitions

* `Cslib.Privacy.rowCount`: the histogram of a dataset.
* `Cslib.Privacy.countExcess`: the rows of one dataset with no matching row in another.

## Main results

* `Cslib.Privacy.countExcess_le_hammingDist`, `Cslib.Privacy.countExcess_le_add`: the excess is
  at most the Hamming distance and satisfies the triangle inequality.
* `Cslib.Privacy.exists_symmetric_lipschitz_extension`: McShane's extension for queries of
  histograms.
* `Cslib.Privacy.exists_symmetric_query_two_pow_mul_le`: the packing form of De's bound.
* `Cslib.Privacy.exists_symmetric_query_forall_exists_half_lt`: De's lower bound over a small
  universe [DworkRoth2014, Theorem 8.8].

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

open Finset

section Histogram

variable {ι X : Type*} [Fintype ι] [DecidableEq X]

/-- The number of rows of the dataset `x` equal to `a`: the histogram of `x` at `a`. -/
def rowCount (x : ι → X) (a : X) : ℕ :=
  #{i | x i = a}

/-- Unfolding `rowCount`. -/
theorem rowCount_apply (x : ι → X) (a : X) : rowCount x a = #{i | x i = a} := by
  rw [rowCount]

/-- Reindexing the rows does not change the histogram. -/
theorem rowCount_comp_equiv (x : ι → X) (σ : Equiv.Perm ι) (a : X) :
    rowCount (x ∘ σ) a = rowCount x a := by
  unfold rowCount
  exact card_equiv σ fun i => by simp

/-- The rows of `x` equal to `a` but not matched by the same row of `y`. -/
private theorem rowCount_sub_rowCount_le (x y : ι → X) (a : X) :
    rowCount x a - rowCount y a ≤ #{i | x i ≠ y i ∧ x i = a} := by
  classical
  unfold rowCount
  have : #{i | x i = a} ≤ #{i | y i = a} + #{i | x i ≠ y i ∧ x i = a} := by
    calc #{i | x i = a} ≤ #(({i | y i = a} : Finset ι) ∪
          ({i | x i ≠ y i ∧ x i = a} : Finset ι)) := by
          refine card_le_card fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
          by_cases h : x i = y i
          · exact Or.inl (h ▸ hi)
          · exact Or.inr ⟨h, hi⟩
      _ ≤ _ := card_union_le _ _
  omega

variable [Fintype X]

/-- The *histogram excess* of `x` over `y`: the number of rows of `x` that have no matching row
of `y`, `∑ a, (rowCount x a - rowCount y a)` with truncated subtraction. For datasets with the same
number of rows it is half the `ℓ₁` distance between their histograms. It depends only on the
histograms, so it is invariant under reordering the rows of either dataset. -/
def countExcess (x y : ι → X) : ℕ :=
  ∑ a, (rowCount x a - rowCount y a)

/-- Unfolding `countExcess`. -/
theorem countExcess_apply (x y : ι → X) :
    countExcess x y = ∑ a, (rowCount x a - rowCount y a) := by
  rw [countExcess]

/-- A dataset has no excess over itself. -/
@[simp]
theorem countExcess_self (x : ι → X) : countExcess x x = 0 := by
  simp [countExcess]

/-- Reordering the rows of the second dataset does not change the excess. -/
theorem countExcess_comp_equiv_right (x y : ι → X) (σ : Equiv.Perm ι) :
    countExcess x (y ∘ σ) = countExcess x y := by
  simp only [countExcess, rowCount_comp_equiv]

/-- The excess is at most the Hamming distance. -/
theorem countExcess_le_hammingDist (x y : ι → X) : countExcess x y ≤ hammingDist x y := by
  classical
  calc countExcess x y ≤ ∑ a, #{i | x i ≠ y i ∧ x i = a} :=
        sum_le_sum fun a _ => rowCount_sub_rowCount_le x y a
    _ = #{i | x i ≠ y i} := by
        rw [card_eq_sum_card_fiberwise (f := x) (t := univ) fun _ _ => mem_univ _]
        refine sum_congr rfl fun a _ => ?_
        rw [filter_filter]
    _ = hammingDist x y := rfl

/-- The triangle inequality for the excess. -/
theorem countExcess_le_add (x y z : ι → X) :
    countExcess x z ≤ countExcess x y + countExcess y z := by
  unfold countExcess
  rw [← sum_add_distrib]
  exact sum_le_sum fun a _ => by omega

/-- The excess over `z` is `1`-Lipschitz in the Hamming distance of `z`. -/
theorem countExcess_le_add_hammingDist (x y z : ι → X) :
    countExcess x z ≤ countExcess x y + hammingDist y z :=
  (countExcess_le_add x y z).trans (Nat.add_le_add_left (countExcess_le_hammingDist y z) _)

end Histogram

section Extension

variable {ι X H : Type*} [Fintype ι] [Fintype X] [DecidableEq X] [Finite H] [Nonempty H]

/-- **Symmetric Lipschitz extension.** Let `D h` (`h : H`) be finitely many datasets and `g h`
real labels with `g h ≤ g h' + countExcess (D h') (D h)`. Then some query `G` that depends only
on the histogram and is `1`-Lipschitz in Hamming distance takes the value `g h` on `D h`. It is
McShane's extension `G y = min_h (g h + countExcess (D h) y)`, the construction of Mathlib's
`LipschitzOnWith.extend_real` specialized to the excess, for which `ι → X` carries no metric
instance; the minimum also makes `G` invariant under reordering the rows. -/
theorem exists_symmetric_lipschitz_extension (D : H → ι → X) (g : H → ℝ)
    (hg : ∀ h h', g h ≤ g h' + countExcess (D h') (D h)) :
    ∃ G : (ι → X) → ℝ, (∀ (y : ι → X) (σ : Equiv.Perm ι), G (y ∘ σ) = G y) ∧
      (∀ y z : ι → X, |G y - G z| ≤ hammingDist y z) ∧ ∀ h, G (D h) = g h := by
  have := Fintype.ofFinite H
  let G : (ι → X) → ℝ := fun y => univ.inf' univ_nonempty fun h => g h + countExcess (D h) y
  -- one direction of the Lipschitz bound
  have hle : ∀ y z : ι → X, G y ≤ G z + hammingDist z y := by
    intro y z
    obtain ⟨h, -, hh⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
      fun h => g h + (countExcess (D h) z : ℝ)
    calc G y ≤ g h + countExcess (D h) y := inf'_le _ (mem_univ h)
      _ ≤ g h + countExcess (D h) z + hammingDist z y := by
          have := countExcess_le_add_hammingDist (D h) z y
          have : (countExcess (D h) y : ℝ) ≤ countExcess (D h) z + hammingDist z y := by
            exact_mod_cast this
          linarith
      _ = G z + hammingDist z y := by rw [← hh]
  refine ⟨G, fun y σ => ?_, fun y z => ?_, fun h => ?_⟩
  · simp only [G, countExcess_comp_equiv_right]
  · rw [abs_le]
    constructor
    · have := hle z y
      linarith
    · have := hle y z
      rw [hammingDist_comm] at this
      linarith
  · refine le_antisymm ?_ ?_
    · calc G (D h) ≤ g h + countExcess (D h) (D h) := inf'_le _ (mem_univ h)
        _ = g h := by simp
    · exact le_inf' _ _ fun h' _ => by exact_mod_cast hg h h'

end Extension

section Construction

variable {ι X : Type*} [Fintype ι] [DecidableEq X] {L t : ℕ}

/-- The dataset encoding a word `c` of length `L` over `16` letters with `t` rows per coordinate:
the rows `pos (j, s)` (`s < t`) hold the item `e (some (j, c j))`, and every other row holds the
filler item `e none`. -/
private noncomputable def codeDataset (e : Option (Fin L × Fin 16) ↪ X) (pos : Fin L × Fin t ↪ ι)
    (c : Fin L → Fin 16) : ι → X :=
  Function.extend pos (fun p => e (some (p.1, c p.1))) fun _ => e none

omit [Fintype ι] [DecidableEq X] in
private theorem codeDataset_pos (e : Option (Fin L × Fin 16) ↪ X) (pos : Fin L × Fin t ↪ ι)
    (c : Fin L → Fin 16) (p : Fin L × Fin t) :
    codeDataset e pos c (pos p) = e (some (p.1, c p.1)) :=
  pos.injective.extend_apply _ _ p

/-- Every encoded dataset is within Hamming distance `t L` of the all-filler dataset. -/
private theorem hammingDist_codeDataset_le (e : Option (Fin L × Fin 16) ↪ X)
    (pos : Fin L × Fin t ↪ ι) (c : Fin L → Fin 16) :
    hammingDist (codeDataset e pos c) (fun _ => e none) ≤ t * L := by
  classical
  unfold hammingDist
  calc #{i | codeDataset e pos c i ≠ e none} ≤ #(univ.map pos) := by
        refine card_le_card fun i hi => ?_
        simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_map, mem_univ, true_and]
        by_contra hne
        exact hi (Function.extend_apply' _ _ _ hne)
    _ = t * L := by rw [card_map, card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, mul_comm]

/-- The item of coordinate `j` occurs in at least `t` rows. -/
private theorem le_rowCount_codeDataset (e : Option (Fin L × Fin 16) ↪ X)
    (pos : Fin L × Fin t ↪ ι) (c : Fin L → Fin 16) (j : Fin L) :
    t ≤ rowCount (codeDataset e pos c) (e (some (j, c j))) := by
  classical
  unfold rowCount
  calc t = #((univ : Finset (Fin t)).map ⟨fun s => pos (j, s), fun s s' h => by
        simpa using pos.injective h⟩) := by rw [card_map, card_univ, Fintype.card_fin]
    _ ≤ _ := by
        refine card_le_card fun i hi => ?_
        simp only [mem_map, mem_univ, true_and] at hi
        obtain ⟨s, rfl⟩ := hi
        simp only [mem_filter, mem_univ, true_and]
        exact codeDataset_pos e pos c (j, s)

/-- The item of coordinate `j` of `c` does not occur in the encoding of `c'` when `c' j ≠ c j`. -/
private theorem rowCount_codeDataset_eq_zero (e : Option (Fin L × Fin 16) ↪ X)
    (pos : Fin L × Fin t ↪ ι) {c c' : Fin L → Fin 16} {j : Fin L} (hj : c j ≠ c' j) :
    rowCount (codeDataset e pos c') (e (some (j, c j))) = 0 := by
  classical
  unfold rowCount
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ hi => ?_)
  by_cases h : ∃ p, pos p = i
  · obtain ⟨p, rfl⟩ := h
    rw [codeDataset_pos] at hi
    have := e.injective hi
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    obtain ⟨rfl, h2⟩ := this
    exact hj h2.symm
  · rw [codeDataset, Function.extend_apply' _ _ _ h] at hi
    exact Option.some_ne_none _ (e.injective hi).symm

variable [Fintype X]

/-- Encodings of words at distance `δ` have excess at least `t δ`. -/
private theorem mul_hammingDist_le_countExcess (e : Option (Fin L × Fin 16) ↪ X)
    (pos : Fin L × Fin t ↪ ι) (c c' : Fin L → Fin 16) :
    t * hammingDist c c' ≤ countExcess (codeDataset e pos c) (codeDataset e pos c') := by
  classical
  unfold countExcess
  let item : Fin L → X := fun j => e (some (j, c j))
  have hf : Set.InjOn item ↑({j | c j ≠ c' j} : Finset (Fin L)) := fun j _ j' _ h => by
    have := e.injective h
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  calc t * hammingDist c c' = ∑ j ∈ ({j | c j ≠ c' j} : Finset (Fin L)), t := by
        rw [sum_const, smul_eq_mul, mul_comm]; rfl
    _ ≤ ∑ j ∈ ({j | c j ≠ c' j} : Finset (Fin L)),
          (rowCount (codeDataset e pos c) (item j) - rowCount (codeDataset e pos c') (item j)) :=
        sum_le_sum fun j hj => by
          simp only [mem_filter, mem_univ, true_and] at hj
          rw [rowCount_codeDataset_eq_zero e pos hj, Nat.sub_zero]
          exact le_rowCount_codeDataset e pos c j
    _ = ∑ a ∈ ({j | c j ≠ c' j} : Finset (Fin L)).image item,
          (rowCount (codeDataset e pos c) a - rowCount (codeDataset e pos c') a) := by
        rw [sum_image hf]
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

end Construction

section LowerBound

variable {ι X : Type*} [Fintype ι] [Fintype X]

/-- **De's lower bound over a small universe, packing form.** Let `L ≤ k`, let the universe `X`
have more than `16 L` items and let there be at least `t L` rows. Then some query
`F : (ι → X) → (Fin k → ℝ)` that depends only on the histogram of the dataset and changes by at
most `1` in each coordinate between Hamming-adjacent datasets has the following property. If an
`(ε, 0)`-private mechanism `M` answers `F` on every dataset with `ℓ∞` error less than `t L / 4`
with probability at least `p`, then `2 ^ L · p ≤ exp (t L ε)`. -/
theorem exists_symmetric_query_two_pow_mul_le {k L t : ℕ} (hLk : L ≤ k)
    (hX : 16 * L < Fintype.card X) (hι : t * L ≤ Fintype.card ι) :
    ∃ F : (ι → X) → Fin k → ℝ, (∀ (x : ι → X) (σ : Equiv.Perm ι), F (x ∘ σ) = F x) ∧
      PointwiseSensitivity HammingAdjacent F 1 ∧
      ∀ (M : (ι → X) → PMF (Fin k → ℝ)) (ε : ℝ) (p : ℝ≥0∞),
        DifferentiallyPrivate HammingAdjacent M ε 0 →
        (∀ x, p ≤ (M x).toOuterMeasure {a | ∀ j, |a j - F x j| < t * L / 4}) →
        2 ^ L * p ≤ ENNReal.ofReal (Real.exp (t * L * ε)) := by
  classical
  -- a code of `2 ^ L` words of length `L` over `16` letters with relative distance `1 / 2`
  obtain ⟨C, hCcard, hCdist⟩ := Code.exists_two_pow_le_card_and_le_two_mul_hammingDist L
  obtain ⟨c⟩ : Nonempty ((Fin L → Bool) ↪ C) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hCcard)
  have hc : ∀ w w', w ≠ w' → L ≤ 2 * hammingDist (c w : Fin L → Fin 16) (c w') :=
    fun w w' hww' => hCdist _ (c w).2 _ (c w').2 fun h => hww' (c.injective (Subtype.ext h))
  -- the items and rows used by the encoding
  obtain ⟨e⟩ : Nonempty (Option (Fin L × Fin 16) ↪ X) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]; omega)
  obtain ⟨pos⟩ : Nonempty (Fin L × Fin t ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin]; rw [mul_comm]; exact hι)
  let D : (Fin L → Bool) → ι → X := fun w => codeDataset e pos (c w)
  have hsep : ∀ w w', w ≠ w' → (t * L : ℝ) ≤ 2 * countExcess (D w) (D w') := by
    intro w w' hww'
    have h1 := mul_hammingDist_le_countExcess e pos (c w : Fin L → Fin 16) (c w')
    have h2 := Nat.mul_le_mul_left t (hc w w' hww')
    have : t * L ≤ 2 * countExcess (D w) (D w') := by nlinarith
    exact_mod_cast this
  -- the `j`-th coordinate is `± t L / 4` on the encodings, by the sign of the `j`-th bit
  let g : Fin L → (Fin L → Bool) → ℝ := fun j w => if w j then t * L / 4 else -(t * L / 4)
  have hg : ∀ j w w', g j w ≤ g j w' + countExcess (D w') (D w) := by
    intro j w w'
    by_cases hww' : w' = w
    · subst hww'; simp
    · have := hsep w' w hww'
      have hnn : (0 : ℝ) ≤ t * L := by positivity
      simp only [g]
      split_ifs <;> linarith
  choose G hGsymm hGlip hGval using fun j =>
    exists_symmetric_lipschitz_extension D (g j) (hg j)
  let F : (ι → X) → Fin k → ℝ := fun y j => if h : (j : ℕ) < L then G ⟨j, h⟩ y else 0
  refine ⟨F, fun y σ => funext fun j => ?_, fun y z hyz j => ?_, fun M ε p hM hp => ?_⟩
  · simp only [F]
    split_ifs
    · exact hGsymm _ y σ
    · rfl
  · simp only [F]
    split_ifs
    · exact (hGlip _ y z).trans (by exact_mod_cast hammingAdjacent_iff_hammingDist_le_one.1 hyz)
    · simp
  · -- pack the `2 ^ L` encodings, all within distance `t L` of the all-filler dataset
    have hpack := hM.card_mul_le_of_hammingDist_le_of_pure (univ : Finset (Fin L → Bool))
      (fun _ => e none) D (m := t * L) (fun w _ => hammingDist_codeDataset_le e pos (c w))
      (B := fun w => {a | ∀ j, |a j - F (D w) j| < t * L / 4}) ?_ (fun w _ => hp (D w))
    · simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hpack
    · intro w _ w' _ hww'
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hww'
      refine Set.disjoint_left.2 fun a ha ha' => ?_
      have h1 := ha (Fin.castLE hLk j)
      have h2 := ha' (Fin.castLE hLk j)
      have hF : ∀ w'', F (D w'') (Fin.castLE hLk j) = g j w'' := fun w'' => by
        simp only [F, Fin.val_castLE, j.isLt, dite_true, Fin.eta]
        exact hGval j w''
      rw [hF] at h1 h2
      have hnn : (0 : ℝ) ≤ t * L := by positivity
      simp only [g] at h1 h2
      cases hw : w j <;> cases hw' : w' j <;> simp only [hw, hw'] at h1 h2 hj <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, ne_eq, not_true_eq_false]
          at h1 h2 hj <;>
        rw [abs_lt] at h1 h2 <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **De's lower bound over a small universe, [DworkRoth2014, Theorem 8.8].** Let the universe `X`
have `d ≥ 33` items, let `k ≥ 2`, let `ε ∈ (0, 1 / 18]` and let there be `n ≥ min (k, d) / ε`
rows. Some query `F : (ι → X) → (Fin k → ℝ)` that depends only on the histogram and changes by at
most `1` in each coordinate between Hamming-adjacent datasets has the following property. Every
`(ε, 0)`-private mechanism `M` has, on some dataset, noise of `ℓ∞` norm at least
`min (k, d) / (1024 ε)` with probability more than `1 / 2`.

Dwork and Roth assume `ε ≤ 1 / 40` and compare histograms by adding or removing a row; see the
module docstring for the scope. -/
theorem exists_symmetric_query_forall_exists_half_lt {k : ℕ} (hk : 2 ≤ k)
    (hX : 33 ≤ Fintype.card X) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 18)
    (hι : min (k : ℝ) (Fintype.card X) / ε ≤ Fintype.card ι) :
    ∃ F : (ι → X) → Fin k → ℝ, (∀ (x : ι → X) (σ : Equiv.Perm ι), F (x ∘ σ) = F x) ∧
      PointwiseSensitivity HammingAdjacent F 1 ∧
      ∀ M : (ι → X) → PMF (Fin k → ℝ), DifferentiallyPrivate HammingAdjacent M ε 0 →
        ∃ x, 2⁻¹ < (M x).toOuterMeasure
          {a | ∃ j, min (k : ℝ) (Fintype.card X) / (1024 * ε) ≤ |a j - F x j|} := by
  set d := Fintype.card X
  set L := min k ((d - 1) / 16)
  set t := ⌊1 / (6 * ε)⌋₊
  have hL2 : 2 ≤ L := le_min hk (by omega)
  have hLk : L ≤ k := min_le_left _ _
  have hLd : 16 * L < d := by
    have : L ≤ (d - 1) / 16 := min_le_right _ _
    omega
  have hm : min (k : ℝ) d ≤ 32 * L := by
    have : min k d ≤ 32 * L := by omega
    rw [← Nat.cast_min]
    exact_mod_cast this
  have hLm : (L : ℝ) ≤ min (k : ℝ) d := by
    have : L ≤ min k d := by omega
    rw [← Nat.cast_min]
    exact_mod_cast this
  -- `1 / (8 ε) ≤ t ≤ 1 / (6 ε)`
  have ht_le : (t : ℝ) ≤ 1 / (6 * ε) := Nat.floor_le (by positivity)
  have ht_ge : 1 / (8 * ε) ≤ (t : ℝ) := by
    -- `⌊u⌋ ≥ 3 u / 4` for `u = 1 / (6 ε) ≥ 3`
    have h8 : 1 / (8 * ε) = 3 / 4 * (1 / (6 * ε)) := by
      field_simp
      ring
    have hu : 3 ≤ 1 / (6 * ε) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [h8]
    by_cases h4 : 4 ≤ 1 / (6 * ε)
    · have h := Nat.sub_one_lt_floor (1 / (6 * ε))
      linarith
    · have h3 : (3 : ℝ) ≤ t := by exact_mod_cast Nat.le_floor (by exact_mod_cast hu)
      linarith
  have htL : t * L ≤ Fintype.card ι := by
    have : (t * L : ℝ) ≤ Fintype.card ι := by
      calc (t * L : ℝ) ≤ 1 / (6 * ε) * min (k : ℝ) d := by gcongr
        _ ≤ min (k : ℝ) d / ε := by
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hε]
            have : (0 : ℝ) ≤ min (k : ℝ) d := by positivity
            nlinarith
        _ ≤ _ := hι
    exact_mod_cast this
  obtain ⟨F, hFsymm, hFsens, hF⟩ := exists_symmetric_query_two_pow_mul_le hLk hLd htL
  refine ⟨F, hFsymm, hFsens, fun M hM => ?_⟩
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  -- otherwise `M` is accurate to within `t L / 4` with probability at least `1 / 2` everywhere
  have hc : min (k : ℝ) d / (1024 * ε) ≤ t * L / 4 := by
    calc min (k : ℝ) d / (1024 * ε) ≤ 32 * L / (1024 * ε) := by gcongr
      _ = 1 / (8 * ε) * L / 4 := by field_simp; ring
      _ ≤ t * L / 4 := by gcongr
  have hacc : ∀ x, 2⁻¹ ≤ (M x).toOuterMeasure {a | ∀ j, |a j - F x j| < t * L / 4} := by
    intro x
    set S := {a : Fin k → ℝ | ∃ j, min (k : ℝ) d / (1024 * ε) ≤ |a j - F x j|}
    have hsum := Probability.PMF.toOuterMeasure_add_compl_ennreal (M x) S
    have hS : 2⁻¹ ≤ (M x).toOuterMeasure Sᶜ := by
      have hfin : (M x).toOuterMeasure S ≠ ⊤ := Probability.PMF.toOuterMeasure_ne_top _ _
      calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
        _ ≤ 1 - (M x).toOuterMeasure S := tsub_le_tsub_left (hcon x) _
        _ = (M x).toOuterMeasure Sᶜ := by
            rw [← hsum, ENNReal.add_sub_cancel_left hfin]
    refine hS.trans ((M x).toOuterMeasure.mono fun a ha j => ?_)
    simp only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le] at ha
    exact (ha j).trans_le hc
  have hlog := sub_one_mul_log_two_le_of_two_pow_mul_inv_two_le_ofReal_exp (hF M ε 2⁻¹ hM hacc)
  -- `(L - 1) ln 2 ≤ t L ε ≤ L / 6` contradicts `ln 2 ≥ 1 / 2` and `L ≥ 2`
  have hln2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) two_pos
    have h2 : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
    linarith
  have htε : (t : ℝ) * ε ≤ 1 / 6 := by
    calc (t : ℝ) * ε ≤ 1 / (6 * ε) * ε := by gcongr
      _ = 1 / 6 := by field_simp
  have hL2' : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have : ((L : ℝ) - 1) * (1 / 2) ≤ L / 6 := by
    calc ((L : ℝ) - 1) * (1 / 2) ≤ (L - 1) * Real.log 2 := by gcongr; linarith
      _ ≤ t * L * ε := by linarith
      _ = (t * ε) * L := by ring
      _ ≤ 1 / 6 * L := by gcongr
      _ = L / 6 := by ring
  linarith

end LowerBound

end Cslib.Privacy
