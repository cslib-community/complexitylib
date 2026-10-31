/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.ExactlyOne
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm

/-!
# The `0/1` permanent as an exactly-one instance

The permanent of an `n × n` matrix with entries in `{0, 1}` counts the permutations supported by its
nonzero entries. The permanent instance `CSP.permanentInstance n r` of the matrix with entries
`r i j` has one Boolean variable `i * n + j` for each nonzero entry, and an exactly-one constraint
for each row and for each column on the variables of its nonzero entries. Its exactly-one
partition function is the permanent (`CSP.partitionFunction_permanentInstance`): the sets of
variables meeting every row and every column exactly once are the supports of the permutations.

Every variable occurs once in its row and once in its column (`CSP.count_vars_permanentInstance`),
and a row or column with `d` nonzero entries gives a constraint on `d` variables.

## Main definitions

* `Cslib.Logic.PL.CSP.permanentInstance`: the permanent instance of a `0/1` matrix.

## Main results

* `Cslib.Logic.PL.CSP.partitionFunction_permanentInstance`: its exactly-one partition function is
  the permanent.
* `Cslib.Logic.PL.CSP.mem_vars_permanentInstance`,
  `Cslib.Logic.PL.CSP.count_vars_permanentInstance`: its variables are the nonzero entries, and
  each occurs at most twice.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- The permanent instance of the `n × n` matrix with entries `r i j` in `{0, 1}`: a variable
`i * n + j` for every nonzero entry, and an exactly-one constraint for every row and every column
on the variables of its nonzero entries. -/
@[expose] def permanentInstance (n : ℕ) (r : ℕ → ℕ → Bool) : CSP Unit ℕ :=
  (List.range n).map (fun i => ((), ((List.range n).filter (r i)).map fun j => i * n + j)) ++
    (List.range n).map fun j => ((), ((List.range n).filter fun i => r i j).map fun i => i * n + j)

variable {n : ℕ} {r : ℕ → ℕ → Bool}

/-- The variables of the permanent instance are the positions `i * n + j` of the nonzero
entries. -/
theorem mem_vars_permanentInstance {x : ℕ} :
    x ∈ (permanentInstance n r).vars ↔ ∃ i < n, ∃ j < n, r i j = true ∧ i * n + j = x := by
  simp only [permanentInstance, vars, List.flatMap_append, List.flatMap_map, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro (⟨i, hi, j, ⟨hj, hr⟩, rfl⟩ | ⟨j, hj, i, ⟨hi, hr⟩, rfl⟩) <;> exact ⟨i, hi, j, hj, hr, rfl⟩
  · rintro ⟨i, hi, j, hj, hr, rfl⟩
    exact Or.inl ⟨i, hi, j, ⟨hj, hr⟩, rfl⟩

private theorem div_mod_mul_add {i j : ℕ} (hj : j < n) :
    (i * n + j) / n = i ∧ (i * n + j) % n = j :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by rw [Nat.mul_comm, Nat.add_comm], hj⟩

/-- The row constraints of the permanent instance. -/
private theorem nodup_rows (n : ℕ) (r : ℕ → ℕ → Bool) :
    ((List.range n).flatMap fun i =>
      ((List.range n).filter (r i)).map fun j => i * n + j).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ => (List.nodup_range.filter _).map fun j j' h => ?_,
    List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hne => ?_⟩
  · simpa using h
  · intro x hx hx'
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hx hx'
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hx
    obtain ⟨j', ⟨hj', -⟩, h⟩ := hx'
    exact hne ((div_mod_mul_add hj').1.symm.trans (h ▸ (div_mod_mul_add hj).1)).symm

/-- The column constraints of the permanent instance. -/
private theorem nodup_cols (n : ℕ) (r : ℕ → ℕ → Bool) :
    ((List.range n).flatMap fun j =>
      ((List.range n).filter fun i => r i j).map fun i => i * n + j).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun j hj => (List.nodup_range.filter _).map fun i i' h => ?_,
    List.nodup_range.pairwise_of_forall_ne fun j hj j' hj' hne => ?_⟩
  · have hn : 0 < n := by have := List.mem_range.mp hj; omega
    exact Nat.eq_of_mul_eq_mul_right hn (by simpa using h)
  · intro x hx hx'
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hx hx' hj hj'
    obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hx
    obtain ⟨i', ⟨hi', -⟩, h⟩ := hx'
    exact hne ((div_mod_mul_add hj').2.symm.trans (h ▸ (div_mod_mul_add hj).2)).symm

/-- Every variable occurs at most twice: once in its row and once in its column. -/
theorem count_vars_permanentInstance (n : ℕ) (r : ℕ → ℕ → Bool) (x : ℕ) :
    (permanentInstance n r).vars.count x ≤ 2 := by
  simp only [permanentInstance, vars, List.flatMap_append, List.flatMap_map, List.count_append]
  have h1 := List.nodup_iff_count_le_one.mp (nodup_rows n r) x
  have h2 := List.nodup_iff_count_le_one.mp (nodup_cols n r) x
  omega

private theorem length_filter_range_eq_one_iff {p : ℕ → Bool} :
    ((List.range n).filter p).length = 1 ↔ ∃! j, j < n ∧ p j = true := by
  have hmem : ∀ j, j ∈ (List.range n).filter p ↔ j < n ∧ p j = true := fun j => by
    simp only [List.mem_filter, List.mem_range]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
    refine ⟨a, (hmem a).mp (by simp [ha]), fun j hj => ?_⟩
    simpa [ha] using (hmem j).mpr hj
  · rintro ⟨a, ha, huniq⟩
    have hperm : ((List.range n).filter p).Perm [a] :=
      (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) (List.nodup_singleton a)).mpr
        fun j => by
          rw [hmem, List.mem_singleton]
          exact ⟨fun hj => huniq j hj, fun h => h ▸ ha⟩
    simpa using hperm.length_eq

/-- The exactly-one conditions of the permanent instance on a set `S` of `true` variables: every
row and every column has exactly one nonzero entry whose variable is in `S`. -/
private theorem forall_mem_permanentInstance_iff {S : Finset ℕ} :
    (∀ c ∈ permanentInstance n r, (c.2.filter fun v => v ∈ S).length = 1) ↔
      (∀ i < n, ∃! j, j < n ∧ r i j = true ∧ i * n + j ∈ S) ∧
        ∀ j < n, ∃! i, i < n ∧ r i j = true ∧ i * n + j ∈ S := by
  simp only [permanentInstance, List.forall_mem_append, List.forall_mem_map, List.mem_range,
    List.filter_map, List.length_map, List.filter_filter, length_filter_range_eq_one_iff,
    Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr (forall₂_congr fun i _ => ?_) (forall₂_congr fun j _ => ?_) <;>
    exact existsUnique_congr fun _ => by tauto

/-- The permutation of an exact cover `S` of the rows and columns: column `j` goes to the row of
its entry in `S`. -/
private noncomputable def coverPerm {S : Finset ℕ}
    (hrow : ∀ i < n, ∃! j, j < n ∧ r i j = true ∧ i * n + j ∈ S)
    (hcol : ∀ j < n, ∃! i, i < n ∧ r i j = true ∧ i * n + j ∈ S) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun j => ⟨(hcol j j.2).exists.choose, (hcol j j.2).exists.choose_spec.1⟩)
    (Finite.injective_iff_bijective.mp fun j j' h => by
      have h' := congrArg Fin.val h
      have hj := (hcol j j.2).exists.choose_spec
      have hj' := (hcol j' j'.2).exists.choose_spec
      simp only at h'
      rw [← h'] at hj'
      exact Fin.ext ((hrow _ hj.1).unique ⟨j.2, hj.2⟩ ⟨j'.2, hj'.2⟩))

private theorem coverPerm_spec {S : Finset ℕ}
    (hrow : ∀ i < n, ∃! j, j < n ∧ r i j = true ∧ i * n + j ∈ S)
    (hcol : ∀ j < n, ∃! i, i < n ∧ r i j = true ∧ i * n + j ∈ S) (j : Fin n) :
    r (coverPerm hrow hcol j) j = true ∧ (coverPerm hrow hcol j : ℕ) * n + j ∈ S :=
  (hcol j j.2).exists.choose_spec.2

private theorem coverPerm_unique {S : Finset ℕ}
    (hrow : ∀ i < n, ∃! j, j < n ∧ r i j = true ∧ i * n + j ∈ S)
    (hcol : ∀ j < n, ∃! i, i < n ∧ r i j = true ∧ i * n + j ∈ S) {i : ℕ} (j : Fin n)
    (hi : i < n) (h : r i j = true ∧ i * n + j ∈ S) : (coverPerm hrow hcol j : ℕ) = i :=
  (hcol j j.2).unique ⟨(coverPerm hrow hcol j).2, coverPerm_spec hrow hcol j⟩ ⟨hi, h⟩

/-- **The exactly-one partition function of the permanent instance is the permanent** of the
`n × n` matrix with entries `r i j` in `{0, 1}`. -/
theorem partitionFunction_permanentInstance (n : ℕ) (r : ℕ → ℕ → Bool) :
    (permanentInstance n r).partitionFunction exactlyOneWeight =
      (Matrix.of fun i j : Fin n => if r i j then 1 else 0 :
        Matrix (Fin n) (Fin n) ℕ).permanent := by
  classical
  rw [partitionFunction_exactlyOne, Matrix.permanent,
    Finset.filter_congr fun S _ => forall_mem_permanentInstance_iff]
  simp only [Matrix.of_apply, Finset.prod_boole, Finset.mem_univ, true_implies, Finset.sum_boole,
    Nat.cast_id]
  set X := (permanentInstance n r).vars.toFinset
  have hX : ∀ {x}, x ∈ X ↔ ∃ i < n, ∃ j < n, r i j = true ∧ i * n + j = x := fun {x} => by
    rw [List.mem_toFinset, mem_vars_permanentInstance]
  -- the support of a permutation: the variables `σ k * n + k`
  let supp (σ : Equiv.Perm (Fin n)) : Finset ℕ := Finset.univ.image fun k => (σ k : ℕ) * n + k
  have hsupp : ∀ (σ : Equiv.Perm (Fin n)) {i j : ℕ} (hi : i < n) (hj : j < n),
      i * n + j ∈ supp σ ↔ (σ ⟨j, hj⟩ : ℕ) = i := by
    intro σ i j hi hj
    simp only [supp, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk⟩
      have h1 := div_mod_mul_add (i := σ k) k.2
      have h2 := div_mod_mul_add (i := i) hj
      rw [hk] at h1
      have hkj : k = ⟨j, hj⟩ := Fin.ext (h1.2.symm.trans h2.2)
      rw [← hkj]
      exact h1.1.symm.trans h2.1
    · intro h
      exact ⟨⟨j, hj⟩, by rw [h]⟩
  symm
  refine Finset.card_bij' (fun σ _ => supp σ)
    (fun S hS => coverPerm (Finset.mem_filter.mp hS).2.1 (Finset.mem_filter.mp hS).2.2)
    (fun σ hσ => ?_) (fun S hS => ?_) (fun σ hσ => ?_) (fun S hS => ?_)
  · -- the support of a supported permutation is an exact cover
    have hσ : ∀ k, r (σ k) k = true := by simpa using hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun x hx => ?_, fun i hi => ?_,
      fun j hj => ?_⟩
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      exact hX.mpr ⟨σ k, (σ k).2, k, k.2, hσ k, rfl⟩
    · refine ⟨σ.symm ⟨i, hi⟩, ⟨(σ.symm ⟨i, hi⟩).2, ?_, (hsupp σ hi (σ.symm ⟨i, hi⟩).2).mpr
        (by simp)⟩, fun j ⟨hj, _, hjS⟩ => ?_⟩
      · simpa using hσ (σ.symm ⟨i, hi⟩)
      · have h := (hsupp σ hi hj).mp hjS
        have : σ ⟨j, hj⟩ = ⟨i, hi⟩ := Fin.ext h
        rw [← this, Equiv.symm_apply_apply]
    · refine ⟨σ ⟨j, hj⟩, ⟨(σ ⟨j, hj⟩).2, hσ ⟨j, hj⟩, (hsupp σ (σ ⟨j, hj⟩).2 hj).mpr rfl⟩,
        fun i ⟨hi, _, hiS⟩ => ((hsupp σ hi hj).mp hiS).symm⟩
  · -- the permutation of an exact cover is supported
    simpa using fun k => (coverPerm_spec _ _ k).1
  · -- the permutation of the support of `σ` is `σ`
    have hσ : ∀ k, r (σ k) k = true := by simpa using hσ
    exact Equiv.ext fun k => Fin.ext (coverPerm_unique _ _ k (σ k).2
      ⟨hσ k, (hsupp σ (σ k).2 k.2).mpr rfl⟩)
  · -- the support of the permutation of an exact cover is the cover
    obtain ⟨hSX, hrow, hcol⟩ := Finset.mem_filter.mp hS
    ext x
    constructor
    · intro hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      exact (coverPerm_spec hrow hcol k).2
    · intro hx
      obtain ⟨i, hi, j, hj, hr, rfl⟩ := hX.mp (Finset.mem_powerset.mp hSX hx)
      refine (hsupp _ hi hj).mpr (coverPerm_unique hrow hcol ⟨j, hj⟩ hi ⟨hr, hx⟩)

end Cslib.Logic.PL.CSP
