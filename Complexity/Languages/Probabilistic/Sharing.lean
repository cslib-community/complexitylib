/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Semantics
public import Complexity.Languages.Probabilistic.Vector
public import Complexity.Probability.Uniform

/-!
# Additive Secret Sharing over Finite Commutative Groups

This file defines generic additive secret sharing over any finite commutative group `G`
(`[AddCommGroup G] [Fintype G]`):
- `ProbComp.completeShares`: deterministically completes `m - 1` shares `init : Fin (m - 1) → G`
  to an `m`-tuple summing to `target : G` by setting the last coordinate (`(⊤ : Fin m)`) to
  `target - ∑ j : Fin (m - 1), init j`.
- `ProbComp.sampleAdditiveShares`: samples `m - 1` uniform coordinates in `G` and completes the
  last coordinate so that `∑ i : Fin m, s i = target`.
- `ProbComp.eval_restrict_sampleAdditiveShares`: for any proper coalition `I ≠ Finset.univ`, the
  marginal distribution of `I`'s shares is uniform on `(i : I) → G` and independent of `target`.
- `ProbComp.completeSharesErase` and `ProbComp.eq_eval_sampleAdditiveShares_of_sum_of_map_erase`:
  recovering all `m` shares from the `m - 1` coordinates outside any single party `j₀ : Fin m`,
  used when simulating protocols in which an honest party `j₀` sets its share from the remaining
  `m - 1` shares.

## Main definitions

- `Cslib.ProbComp.initOfShares`
- `Cslib.ProbComp.completeShares`
- `Cslib.ProbComp.sampleAdditiveShares`
- `Cslib.ProbComp.completeSharesErase`

## Main results

- `Cslib.ProbComp.sum_completeShares`
- `Cslib.ProbComp.completeShares_initOfShares`
- `Cslib.ProbComp.completeShares_add`
- `Cslib.ProbComp.sum_sampleAdditiveShares`
- `Cslib.ProbComp.mem_support_sampleAdditiveShares_iff`
- `Cslib.ProbComp.eq_eval_sampleAdditiveShares_of_sum_of_map_init`
- `Cslib.ProbComp.eval_restrict_sampleAdditiveShares`
- `Cslib.ProbComp.eval_sampleAdditiveShares_eq_map_completeSharesErase`
- `Cslib.ProbComp.eq_eval_sampleAdditiveShares_of_sum_of_map_erase`

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.2.3 (Construction 7.5.10, Step 1), print pp. 705–706.
-/

@[expose] public section

open Cslib.Probability

namespace Cslib.ProbComp

/-- Extract the first `m - 1` coordinates of an `m`-tuple via `Fin.castLE (Nat.sub_le m 1)`. -/
def initOfShares (m : ℕ) {G : Type} (s : Fin m → G) : Fin (m - 1) → G :=
  fun k => s (Fin.castLE (Nat.sub_le m 1) k)

/-- Deterministically complete `m - 1` shares `init : Fin (m - 1) → G` to `Fin m → G` summing
to `target`, setting the last coordinate to `target - ∑ j : Fin (m - 1), init j`. -/
def completeShares (m : ℕ) {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) : Fin m → G :=
  fun i =>
    if h : i.1 < m - 1 then
      init ⟨i.1, h⟩
    else
      target - ∑ j : Fin (m - 1), init j

@[simp] theorem completeShares_castLE (m : ℕ) {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) (k : Fin (m - 1)) :
    completeShares m target init (Fin.castLE (Nat.sub_le m 1) k) = init k := by
  simp [completeShares, k.2]

@[simp] theorem initOfShares_completeShares (m : ℕ) {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    initOfShares m (completeShares m target init) = init := by
  ext k
  exact completeShares_castLE m target init k

@[simp] theorem completeShares_top (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    completeShares m target init (⊤ : Fin m) = target - ∑ j : Fin (m - 1), init j := by
  simp [completeShares, Fin.val_top]

private theorem sum_univ_eq_add_top (m : ℕ) [NeZero m] {G : Type} [AddCommMonoid G]
    (f : Fin m → G) :
    ∑ i : Fin m, f i =
      (∑ k : Fin (m - 1), f (Fin.castLE (Nat.sub_le m 1) k)) + f (⊤ : Fin m) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⊤ : Fin m))]
  congr 1
  symm
  refine Finset.sum_bij (fun (k : Fin (m - 1)) _ => Fin.castLE (Nat.sub_le m 1) k) ?_ ?_ ?_ ?_
  · intro k _
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    exact ne_of_lt k.2 (congrArg Fin.val h)
  · intro k₁ _ k₂ _ h
    exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) h)
  · intro i hi
    rw [Finset.mem_erase] at hi
    have hne : i.1 ≠ m - 1 := fun h => hi.1 (Fin.ext h)
    have hlt : i.1 < m - 1 := Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt i.2) hne
    exact ⟨⟨i.1, hlt⟩, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

@[simp] theorem sum_completeShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    ∑ i : Fin m, completeShares m target init i = target := by
  rw [sum_univ_eq_add_top m (completeShares m target init)]
  simp [add_sub_cancel]

/-- Any `m`-tuple `s` summing to `target` is recovered from its first `m - 1` coordinates by
`completeShares m target`. -/
theorem completeShares_initOfShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    {target : G} {s : Fin m → G} (hs : ∑ i : Fin m, s i = target) :
    completeShares m target (initOfShares m s) = s := by
  ext i
  by_cases h : i.1 < m - 1
  · simp [completeShares, h, initOfShares]
  · have hi : i = (⊤ : Fin m) := by
      ext
      simp only [Fin.val_top]
      omega
    subst hi
    rw [completeShares_top, sub_eq_iff_eq_add', ← hs]
    exact sum_univ_eq_add_top m s

theorem completeShares_add (m : ℕ) {G : Type} [AddCommGroup G]
    (target₁ target₂ : G) (init₁ init₂ : Fin (m - 1) → G) :
    completeShares m (target₁ + target₂) (init₁ + init₂) =
      completeShares m target₁ init₁ + completeShares m target₂ init₂ := by
  ext i
  by_cases h : i.1 < m - 1
  · simp [completeShares, h]
  · simp [completeShares, h, Finset.sum_add_distrib, add_sub_add_comm]

/-- Sample uniform additive shares `s : Fin m → G` conditioned on `∑ i, s i = target`. -/
noncomputable def sampleAdditiveShares (m : ℕ)
    {G : Type} [AddCommGroup G] [Fintype G] (target : G) : ProbComp (Fin m → G) :=
  completeShares m target <$> ProbComp.uniform (Fin (m - 1) → G)

theorem sum_sampleAdditiveShares {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (target : G)
    {s : Fin m → G} (hs : s ∈ (ProbComp.eval (sampleAdditiveShares m target)).support) :
    ∑ i : Fin m, s i = target := by
  simp only [sampleAdditiveShares, eval_map, PMF.mem_support_map_iff] at hs
  obtain ⟨init, _, rfl⟩ := hs
  exact sum_completeShares m target init

theorem mem_support_sampleAdditiveShares_iff {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (target : G) (s : Fin m → G) :
    s ∈ (ProbComp.eval (sampleAdditiveShares m target)).support ↔ ∑ i : Fin m, s i = target := by
  constructor
  · exact sum_sampleAdditiveShares target
  · intro hs
    simp only [sampleAdditiveShares, eval_map, eval_uniform, PMF.mem_support_map_iff]
    refine ⟨initOfShares m s, ?_, completeShares_initOfShares m hs⟩
    simp [PMF.mem_support_iff]

/-- Any distribution `p` on `Fin m → G` supported on tuples summing to `target` whose first
`m - 1` coordinates are uniformly distributed equals `eval (sampleAdditiveShares m target)`. -/
theorem eq_eval_sampleAdditiveShares_of_sum_of_map_init {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] {target : G} {p : PMF (Fin m → G)}
    (hsum : ∀ s ∈ p.support, ∑ i : Fin m, s i = target)
    (hinit : p.map (initOfShares m) = PMF.uniformOfFintype (Fin (m - 1) → G)) :
    p = eval (sampleAdditiveShares m target) := by
  calc p = p.map id := (PMF.map_id p).symm
    _ = p.map (completeShares m target ∘ initOfShares m) := by
      refine PMF.map_congr_on_support p _ _ fun s hs => ?_
      exact (completeShares_initOfShares m (hsum s hs)).symm
    _ = (p.map (initOfShares m)).map (completeShares m target) := (PMF.map_comp _ _ _).symm
    _ = eval (sampleAdditiveShares m target) := by
      rw [hinit, sampleAdditiveShares, eval_map, eval_uniform]

/-- For any proper coalition `I ≠ Finset.univ`, the marginal distribution of `I`'s shares is
uniform on `(i : I) → G` and independent of `target`. -/
theorem eval_restrict_sampleAdditiveShares {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G]
    (I : Finset (Fin m)) (hI : I ≠ Finset.univ) (target : G) :
    (ProbComp.eval (sampleAdditiveShares m target)).map I.restrict =
      PMF.uniformOfFintype ((i : I) → G) := by
  classical
  rw [sampleAdditiveShares, eval_map, eval_uniform, PMF.map_comp]
  apply Cslib.Probability.PMF.uniformOfFintype_map_of_shift
  intro c
  have hex : ∃ j₀ : Fin m, j₀ ∉ I := by
    by_contra h
    apply hI
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨j₀, hj₀⟩ := hex
  let full : Fin m → G := fun i =>
    if hi : i ∈ I then c ⟨i, hi⟩
    else if i = j₀ then -∑ k : I, c k
    else 0
  have hsum : ∑ i : Fin m, full i = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert j₀ I))]
    · rw [Finset.sum_insert hj₀]
      have h1 : full j₀ = -∑ k : I, c k := by simp [full, hj₀]
      have h2 : ∑ i ∈ I, full i = ∑ k : I, c k := by
        rw [← Finset.sum_attach I]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [full, k.2]
      rw [h1, h2, neg_add_cancel]
    · intro i _ hi
      simp only [Finset.mem_insert, not_or] at hi
      simp [full, hi.1, hi.2]
  have hfull : completeShares m 0 (initOfShares m full) = full :=
    completeShares_initOfShares m hsum
  refine ⟨Equiv.addRight (initOfShares m full), fun init => ?_⟩
  ext ⟨i, hi⟩
  have hadd := congrFun (completeShares_add m target 0 init (initOfShares m full)) i
  change completeShares m target (init + initOfShares m full) i =
    completeShares m target init i + c ⟨i, hi⟩
  rw [add_zero] at hadd
  rw [hadd, Pi.add_apply, hfull]
  simp [full, hi]

/-- Deterministically complete shares on `Finset.univ.erase j₀` to `Fin m → G` summing to `target`,
setting coordinate `j₀` to `target - ∑ k : Finset.univ.erase j₀, sub k`. -/
def completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) : Fin m → G :=
  fun i =>
    if h : i = j₀ then
      target - ∑ k : Finset.univ.erase j₀, sub k
    else
      sub ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩

@[simp] theorem restrict_erase_completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) :
    (Finset.univ.erase j₀).restrict (completeSharesErase j₀ target sub) = sub := by
  ext ⟨i, hi⟩
  have hne : i ≠ j₀ := (Finset.mem_erase.mp hi).1
  simp [completeSharesErase, hne]

@[simp] theorem sum_completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) :
    ∑ i : Fin m, completeSharesErase j₀ target sub i = target := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have h1 : completeSharesErase j₀ target sub j₀ =
      target - ∑ k : Finset.univ.erase j₀, sub k := by
    simp [completeSharesErase]
  have h2 : ∑ i ∈ Finset.univ.erase j₀, completeSharesErase j₀ target sub i =
      ∑ k : Finset.univ.erase j₀, sub k := by
    rw [← Finset.sum_attach (Finset.univ.erase j₀)]
    refine Finset.sum_congr rfl fun ⟨i, hi⟩ _ => ?_
    have hne : i ≠ j₀ := (Finset.mem_erase.mp hi).1
    simp [completeSharesErase, hne]
  rw [h1, h2, sub_add_cancel]

theorem completeSharesErase_restrict_erase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) {target : G} {s : Fin m → G} (hs : ∑ i : Fin m, s i = target) :
    completeSharesErase j₀ target ((Finset.univ.erase j₀).restrict s) = s := by
  ext i
  by_cases h : i = j₀
  · subst h
    simp only [completeSharesErase, ↓reduceDIte]
    rw [sub_eq_iff_eq_add, ← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    rw [← Finset.sum_attach (Finset.univ.erase i)]
    rfl
  · simp [completeSharesErase, h]

/-- For any party `j₀ : Fin m`, `eval (sampleAdditiveShares m target)` is the image of the
uniform distribution on `(i : Finset.univ.erase j₀) → G` under `completeSharesErase j₀ target`. -/
theorem eval_sampleAdditiveShares_eq_map_completeSharesErase {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (j₀ : Fin m) (target : G) :
    eval (sampleAdditiveShares m target) =
      (PMF.uniformOfFintype ((i : Finset.univ.erase j₀) → G)).map
        (completeSharesErase j₀ target) := by
  have hI : Finset.univ.erase j₀ ≠ Finset.univ := by
    intro h
    have hj : j₀ ∈ Finset.univ.erase j₀ := h.symm ▸ Finset.mem_univ j₀
    exact (Finset.notMem_erase j₀ Finset.univ) hj
  rw [← eval_restrict_sampleAdditiveShares (Finset.univ.erase j₀) hI target, PMF.map_comp]
  conv_lhs => rw [← PMF.map_id (eval (sampleAdditiveShares m target))]
  refine PMF.map_congr_on_support _ _ _ fun s hs => ?_
  exact (completeSharesErase_restrict_erase j₀ (sum_sampleAdditiveShares target hs)).symm

/-- Any distribution `p` on `Fin m → G` supported on tuples summing to `target` whose marginal on
`Finset.univ.erase j₀` is uniform equals `eval (sampleAdditiveShares m target)`. -/
theorem eq_eval_sampleAdditiveShares_of_sum_of_map_erase {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (j₀ : Fin m) {target : G} {p : PMF (Fin m → G)}
    (hsum : ∀ s ∈ p.support, ∑ i : Fin m, s i = target)
    (herase : p.map (Finset.univ.erase j₀).restrict =
      PMF.uniformOfFintype ((i : Finset.univ.erase j₀) → G)) :
    p = eval (sampleAdditiveShares m target) := by
  rw [eval_sampleAdditiveShares_eq_map_completeSharesErase j₀ target, ← herase, PMF.map_comp]
  conv_lhs => rw [← PMF.map_id p]
  refine PMF.map_congr_on_support p _ _ fun s hs => ?_
  exact (completeSharesErase_restrict_erase j₀ (hsum s hs)).symm

end Cslib.ProbComp
