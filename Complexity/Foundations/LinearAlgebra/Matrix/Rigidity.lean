/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Matrix rigidity

The *rigidity* `Matrix.rigidity A r` of a matrix `A` over a field is the least number of entries
of `A` that must be changed to bring its rank down to *at most* `r`: the Hamming distance from `A`
to the set of matrices of rank at most `r`. This is [Lokam2009], Definition 2.1,
`R_A(r) = min {|C| : rank (A + C) ≤ r}`, where `|C|` is the number of nonzero entries of `C`. Here
`B = A + C` is the changed matrix, so `|C|` is the number of entries where `A` and `B` differ
(`Matrix.diffCount`). The target is rank at most `r`, as in [Lokam2009], not rank exactly `r`.
Valiant introduced rigidity [Valiant1977] to prove lower bounds on linear circuits: highly rigid
matrices have no linear circuits of linear size and logarithmic depth
(`Cslib.Circuits.Circuit.Computes.rigidity_le`).

Changing one entry changes the rank by at most one, so `A` must lose `rank A - r` rank and every
matrix needs at least `rank A - r` changes (`Matrix.rank_sub_le_rigidity`). For the identity matrix
of size `n` this is exact: `rigidity 1 r = n - r` (`Matrix.rigidity_one`).

## Main definitions

* `Matrix.diffCount A B`: the number of entries where `A` and `B` differ.
* `Matrix.rigidity A r`: the least `diffCount A B` over matrices `B` of rank at most `r`.

## Main results

* `Matrix.rigidity_le`: a matrix `B` of rank at most `r` bounds the rigidity by `diffCount A B`.
* `Matrix.exists_rigidity_eq`: some matrix of rank at most `r` attains the rigidity.
* `Matrix.rigidity_antitone`: rigidity decreases as the target rank grows.
* `Matrix.rigidity_eq_zero_iff`: rigidity is zero exactly when the rank is already at most `r`.
* `Matrix.rigidity_zero`: at target rank zero, rigidity counts the nonzero entries.
* `Matrix.rank_le_diffCount_zero`: the rank is at most the number of nonzero entries.
* `Matrix.rank_sub_diffCount_le_rank`, `Matrix.rank_sub_le_rigidity`: each change lowers the rank
  by at most one, so every matrix needs at least `rank A - r` changes.
* `Matrix.rigidity_one`: the identity matrix of size `n` has rigidity `n - r`.

## References

* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], Definition 2.1
* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
-/

public section

namespace Matrix

variable {m n K α : Type*}

/-- The number of entries where the matrices `A` and `B` differ.

When `m` is infinite (only `n` is required to be finite below), this counts with `Set.ncard`,
which is `0` on infinite sets. Then, at every target rank `r ≥ 1`, some matrix of rank at most one
differs from `A` in infinitely many entries, and the rigidity collapses to the junk value `0`; at
`r = 0` the rigidity is `diffCount A 0` (`Matrix.rigidity_zero`), which can be genuine. The results
relating rigidity to rank (`Matrix.rigidity_eq_zero_iff` and below) therefore assume
`[Finite m]`. -/
noncomputable def diffCount (A B : Matrix m n α) : ℕ :=
  {p : m × n | A p.1 p.2 ≠ B p.1 p.2}.ncard

theorem diffCount_comm (A B : Matrix m n α) : diffCount A B = diffCount B A := by
  simp only [diffCount, ne_comm]

@[simp] theorem diffCount_self (A : Matrix m n α) : diffCount A A = 0 := by
  simp [diffCount]

variable [Fintype n]

/-- Two matrices differ in at most all of their entries. -/
theorem diffCount_le_card [Fintype m] (A B : Matrix m n α) :
    diffCount A B ≤ Fintype.card m * Fintype.card n := by
  rw [diffCount, ← Fintype.card_prod, ← Nat.card_eq_fintype_card]
  exact Set.ncard_le_card _

/-- For finite matrices, `diffCount` is the size of a filtered `Finset` of positions. -/
theorem diffCount_eq_card_filter [Fintype m] [DecidableEq α] (A B : Matrix m n α) :
    diffCount A B = (Finset.univ.filter fun p : m × n => A p.1 p.2 ≠ B p.1 p.2).card := by
  rw [diffCount, ← Set.ncard_coe_finset]
  exact congrArg Set.ncard (by ext p; simp)

/-- The number of differing entries is the sum over the rows of the number of differing entries
in each row. -/
theorem diffCount_eq_sum [Fintype m] [DecidableEq α] (A B : Matrix m n α) :
    diffCount A B = ∑ i, (Finset.univ.filter fun j => A i j ≠ B i j).card := by
  classical
  rw [diffCount, Set.ncard_eq_toFinset_card', ← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) (by simp) ?_ ?_
  · rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    rw [h.1, h.2]
  · rintro ⟨i, j⟩ h
    exact ⟨(i, j), by simpa using h, rfl⟩

variable [Field K]

/-- **Matrix rigidity** ([Lokam2009], Definition 2.1): the least number of entries of `A` that must
be changed to make its rank at most `r`. -/
noncomputable def rigidity (A : Matrix m n K) (r : ℕ) : ℕ :=
  sInf (diffCount A '' {B | B.rank ≤ r})

private theorem nonempty_rigiditySet (A : Matrix m n K) (r : ℕ) :
    (diffCount A '' {B : Matrix m n K | B.rank ≤ r}).Nonempty :=
  ⟨_, 0, by simp, rfl⟩

/-- A matrix `B` of rank at most `r` that differs from `A` in `diffCount A B` entries bounds the
rigidity of `A`. -/
theorem rigidity_le {A B : Matrix m n K} {r : ℕ} (hB : B.rank ≤ r) :
    A.rigidity r ≤ diffCount A B :=
  Nat.sInf_le ⟨B, hB, rfl⟩

/-- Some matrix of rank at most `r` differs from `A` in exactly `A.rigidity r` entries. -/
theorem exists_rigidity_eq (A : Matrix m n K) (r : ℕ) :
    ∃ B : Matrix m n K, B.rank ≤ r ∧ diffCount A B = A.rigidity r := by
  obtain ⟨B, hB, h⟩ := Nat.sInf_mem (nonempty_rigiditySet A r)
  exact ⟨B, hB, h⟩

/-- `s ≤ A.rigidity r` exactly when every matrix of rank at most `r` differs from `A` in at least
`s` entries. -/
theorem le_rigidity_iff {A : Matrix m n K} {r s : ℕ} :
    s ≤ A.rigidity r ↔ ∀ B : Matrix m n K, B.rank ≤ r → s ≤ diffCount A B := by
  refine ⟨fun h B hB => h.trans (rigidity_le hB), fun h => ?_⟩
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  exact hAB ▸ h B hB

/-- Rigidity decreases as the target rank grows. -/
theorem rigidity_antitone (A : Matrix m n K) : Antitone A.rigidity := fun r r' hr => by
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  exact hAB ▸ rigidity_le (hB.trans hr)

/-- Rigidity is at most the number of entries. -/
theorem rigidity_le_card [Fintype m] (A : Matrix m n K) (r : ℕ) :
    A.rigidity r ≤ Fintype.card m * Fintype.card n :=
  (rigidity_le (B := 0) (by simp)).trans (diffCount_le_card _ _)

/-- At target rank zero, the rigidity is the number of nonzero entries. -/
theorem rigidity_zero (A : Matrix m n K) : A.rigidity 0 = diffCount A 0 := by
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A 0
  rw [rank_eq_zero_iff.1 (Nat.le_zero.1 hB)] at hAB
  exact hAB.symm

variable [Finite m]

/-- No changes are needed when the rank is already at most `r`. -/
theorem rigidity_eq_zero_iff {A : Matrix m n K} {r : ℕ} : A.rigidity r = 0 ↔ A.rank ≤ r := by
  refine ⟨fun h => ?_, fun h => Nat.eq_zero_of_le_zero (rigidity_le h |>.trans_eq (by simp))⟩
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  rw [h, diffCount, Set.ncard_eq_zero] at hAB
  have : A = B := by
    ext i j
    by_contra hij
    exact (Set.eq_empty_iff_forall_notMem.1 hAB) (i, j) hij
  exact this ▸ hB

/-- The rank of a matrix is at most the number of its nonzero entries. -/
theorem rank_le_diffCount_zero (C : Matrix m n K) : C.rank ≤ diffCount C 0 := by
  classical
  have := Fintype.ofFinite m
  let rows : Finset m :=
    (Finset.univ.filter fun p : m × n => C p.1 p.2 ≠ 0).image Prod.fst
  have hsupp : Function.support C.row ⊆ rows := by
    intro i hi
    obtain ⟨j, hj⟩ : ∃ j, C i j ≠ 0 := by
      by_contra h
      exact hi (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
    exact Finset.mem_image.2 ⟨(i, j), by simpa using hj, rfl⟩
  refine (rank_le_card_of_support_subset C rows hsupp).trans ?_
  refine Finset.card_image_le.trans ?_
  rw [diffCount, ← Set.ncard_coe_finset]
  exact le_of_eq (congrArg Set.ncard (by ext p; simp))

/-- **Each change lowers the rank by at most one**: the rank of `B` is at least the rank of `A`
minus the number of entries where they differ. -/
theorem rank_sub_diffCount_le_rank (A B : Matrix m n K) : A.rank - diffCount A B ≤ B.rank := by
  have h := rank_add_le B (A - B)
  rw [add_sub_cancel] at h
  have : diffCount (A - B) 0 = diffCount A B :=
    congrArg Set.ncard (Set.ext fun p => not_congr sub_eq_zero)
  have := rank_le_diffCount_zero (A - B)
  omega

/-- **Rigidity is at least the rank deficit**: at least `rank A - r` entries must be changed to
bring the rank of `A` down to `r`. -/
theorem rank_sub_le_rigidity (A : Matrix m n K) (r : ℕ) : A.rank - r ≤ A.rigidity r := by
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  have := rank_sub_diffCount_le_rank A B
  omega

section One

variable [DecidableEq n]

/-- **The identity matrix of size `n`** has rigidity exactly `n - r`: zeroing all but `r` diagonal
entries attains the lower bound `Matrix.rank_sub_le_rigidity`. -/
theorem rigidity_one (r : ℕ) : (1 : Matrix n n K).rigidity r = Fintype.card n - r := by
  classical
  refine le_antisymm ?_ (by simpa [rank_one] using rank_sub_le_rigidity (1 : Matrix n n K) r)
  rcases le_total (Fintype.card n) r with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    exact (rigidity_eq_zero_iff.2 (by rw [rank_one]; exact h)).le
  -- keep `r` diagonal entries and zero the others
  obtain ⟨S, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset n)) h
  let w : n → K := fun i => if i ∈ S then 1 else 0
  have hrank : (diagonal w).rank = r := by
    rw [rank_diagonal, Fintype.card_subtype, ← hS.2]
    congr 1
    ext i
    simp [w]
  refine (rigidity_le (B := diagonal w) hrank.le).trans_eq ?_
  have hset : {p : n × n | (1 : Matrix n n K) p.1 p.2 ≠ diagonal w p.1 p.2} =
      (fun i => (i, i)) '' ((Sᶜ : Finset n) : Set n) := by
    ext ⟨i, j⟩
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ S <;> simp [w, hi]
    · simp [one_apply_ne hij, hij, Ne.symm hij]
  rw [diffCount, hset, Set.ncard_image_of_injective _ (fun i j h => (Prod.ext_iff.1 h).1),
    Set.ncard_coe_finset, Finset.card_compl, hS.2]

end One

end Matrix
