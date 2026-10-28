/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import Complexity.Init
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Sum

/-!
# Rectangular permanents and the Binet–Minc identity

For a matrix `b : Matrix m n R` with finite row type `m` and column type `n`, the rectangular
permanent `b.rectPerm` is the sum over all injections `σ : m ↪ n` of `∏ r, b r (σ r)`
[Forbes, Def. 11][Forbes2024]. For a set `Z` of columns, `b.rectPermSurj Z` keeps only the
injections whose image contains `Z` [Forbes, Def. 20][Forbes2024].

The main result is the Binet–Minc identity in permutation form, over any commutative ring:

`∑_{σ : m ↪ n} ∏_r b r (σ r) = ∑_{π ∈ Perm m} sgn π ∏_{q ∈ orbits π} ∑_j ∏_{r ∈ q} b r j`,

together with its inclusion–exclusion extension to `rectPermSurj`:

`∑_{σ, Z ⊆ im σ} ∏_r b r (σ r) =
  ∑_π sgn π ∑_{Y ⊆ Z} (-1)^{|Y|} ∏_{q ∈ orbits π} ∑_{j ∉ Y} ∏_{r ∈ q} b r j`.

Here `orbits π` is the quotient of `m` by `Equiv.Perm.SameCycle π`, so fixed points of `π` are
orbits of size one.

## Main definitions

* `Matrix.rectPerm`: the rectangular permanent [Forbes, Def. 11][Forbes2024].
* `Matrix.rectPermSurj`: the permanent restricted to injections whose image contains a given set
  of columns [Forbes, Def. 20][Forbes2024].

## Main results

* `Equiv.Perm.sum_sign_filter_apply_eq`: the signed count of the permutations that fix the fibres
  of `f : m → n` is `1` if `f` is injective and `0` otherwise.
* `Matrix.prod_quotient_sameCycle_sum_eq`: expanding the product over the orbits of `π` gives the
  sum over the functions that are constant on those orbits.
* `Matrix.sum_injective_eq_sum_sign_prod_sameCycle`: the Binet–Minc identity for injections into
  a given set of columns.
* `Matrix.rectPerm_eq_sum_sign_prod_sameCycle`: the Binet–Minc identity in permutation form.
* `Matrix.rectPermSurj_eq_sum_sign_prod_sameCycle`: its inclusion–exclusion extension.
* `Matrix.rectPerm_eq_permanent`: on square matrices `rectPerm` is Mathlib's `Matrix.permanent`.

## Implementation notes

The rows of `b : Matrix m n R` are indexed by `m` and the columns by `n`, following Mathlib. In
Forbes's notation the matrix is `n × m`, with rows `[n]` and columns `[m]`. The definitions need
no hypothesis `card m ≤ card n`: without it there are no injections and both sums are `0`
(`Matrix.rectPerm_eq_zero_of_card_lt`). Forbes's Def. 20 requires the image to contain `[k]`; here
any `Z : Finset n` is allowed.

[Forbes, Thm. 13][Forbes2024] states the Binet–Minc identity grouped by set partitions of the rows,
with coefficient `(-1)^{n - |F|} ∏_{S ∈ F} (|S| - 1)!`. The permutation form proved here groups
the same terms by permutation instead. The grouped form is not proved in this file. The
permutation form, its inclusion–exclusion extension and this proof are original. The proof expands
the product over orbits into a sum over functions constant on orbits, exchanges the two sums, and
evaluates the signed sum over the stabiliser of each function with a sign-reversing involution.

## References

* [M. A. Forbes, *Low-Depth Algebraic Circuit Lower Bounds over Any Field*][Forbes2024]
-/

@[expose] public section

open Finset Fintype

namespace Equiv.Perm

variable {m n : Type*}

/-- The signed count of the permutations that fix every fibre of `f` is `1` if `f` is injective
and `0` otherwise. A transposition of two rows with the same value pairs off the permutations
with opposite signs. -/
theorem sum_sign_filter_apply_eq [Fintype m] [DecidableEq m] [DecidableEq n] (f : m → n) :
    ∑ π : Perm m with ∀ r, f (π r) = f r, (sign π : ℤ) =
      if Function.Injective f then 1 else 0 := by
  split_ifs with hf
  · rw [sum_eq_single_of_mem 1 (by simp)]
    · simp
    · intro π hπ hne
      exact absurd (Perm.ext fun r => hf ((mem_filter.1 hπ).2 r)) hne
  · obtain ⟨r, r', hrr', hne⟩ : ∃ r r', f r = f r' ∧ r ≠ r' := by
      simpa [Function.Injective] using hf
    have hswap : ∀ x, f (swap r r' x) = f x := by
      intro x
      rcases eq_or_ne x r with rfl | h₁
      · simp [hrr']
      rcases eq_or_ne x r' with rfl | h₂
      · simp [hrr']
      rw [swap_apply_of_ne_of_ne h₁ h₂]
    refine sum_involution (fun π _ => π * swap r r') ?_ ?_ ?_ ?_
    · intro π _
      simp [sign_mul, sign_swap hne]
    · intro π _ _ h
      exact hne (swap_eq_one_iff.1 (mul_eq_left.1 h))
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      intro x
      rw [mul_apply, hπ, hswap]
    · intro π _
      simp [mul_assoc]

/-- A function that is invariant under `π` is constant on the orbits of `π`. -/
theorem apply_eq_of_sameCycle [Finite m] {π : Perm m} {f : m → n} (hf : ∀ r, f (π r) = f r)
    {x y : m} (h : π.SameCycle x y) : f x = f y := by
  obtain ⟨i, -, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => rfl
  | succ i ih => rw [ih, pow_succ', mul_apply, hf]

/-- The orbit relation of a permutation of a finite type is decidable, so the type of its orbits
is a `Fintype` with decidable equality. -/
instance instDecidableRelSameCycleSetoid [Fintype m] [DecidableEq m] (π : Perm m) :
    DecidableRel (SameCycle.setoid π).r :=
  inferInstanceAs (DecidableRel π.SameCycle)

end Equiv.Perm

namespace Matrix

open Equiv Equiv.Perm

variable {m n R : Type*} [Fintype m] [Fintype n]

section CommSemiring

variable [CommSemiring R]

/-- The rectangular permanent: the sum over all injections `σ : m ↪ n` of `∏ r, b r (σ r)`
[Forbes, Def. 11][Forbes2024]. It is `0` when `card n < card m`. -/
noncomputable def rectPerm (b : Matrix m n R) : R :=
  ∑ σ : m ↪ n, ∏ r, b r (σ r)

/-- The rectangular permanent restricted to the injections whose image contains the columns `Z`.
[Forbes, Def. 20][Forbes2024] is the case where `Z` is the set of the first `k` columns. -/
noncomputable def rectPermSurj [DecidableEq n] (Z : Finset n) (b : Matrix m n R) : R :=
  ∑ σ : m ↪ n with Z ⊆ univ.map σ, ∏ r, b r (σ r)

variable [DecidableEq m] [DecidableEq n]

/-- A filtered sum over embeddings is the sum over the injective functions. -/
private theorem sum_embedding_filter_eq (g : (m → n) → R) (p : (m → n) → Prop) [DecidablePred p] :
    ∑ σ ∈ univ.filter (fun σ : m ↪ n => p σ), g σ =
      ∑ f : m → n with Function.Injective f ∧ p f, g f := by
  refine sum_bij (fun σ _ => ⇑σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    exact ⟨σ.injective, hσ⟩
  · intro σ _ τ _ h
    exact DFunLike.coe_injective h
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    exact ⟨⟨f, hf.1⟩, by simpa using hf.2, rfl⟩
  · intro σ _
    rfl

/-- The rectangular permanent as a sum over injective functions. -/
theorem rectPerm_eq_sum_injective (b : Matrix m n R) :
    b.rectPerm = ∑ f : m → n with Function.Injective f, ∏ r, b r (f r) := by
  simpa [rectPerm] using sum_embedding_filter_eq (fun f => ∏ r, b r (f r)) (fun _ => True)

/-- `rectPermSurj` as a sum over injective functions. -/
theorem rectPermSurj_eq_sum_injective (Z : Finset n) (b : Matrix m n R) :
    b.rectPermSurj Z =
      ∑ f : m → n with Function.Injective f ∧ Z ⊆ univ.image f, ∏ r, b r (f r) := by
  simp_rw [rectPermSurj, map_eq_image]
  exact sum_embedding_filter_eq (fun f => ∏ r, b r (f r)) (fun f => Z ⊆ univ.image f)

omit [DecidableEq m] in
@[simp]
theorem rectPermSurj_empty (b : Matrix m n R) : b.rectPermSurj ∅ = b.rectPerm := by
  simp [rectPermSurj, rectPerm]

omit [DecidableEq n] in
/-- On square matrices the rectangular permanent is Mathlib's `Matrix.permanent`. -/
theorem rectPerm_eq_permanent (M : Matrix m m R) : M.rectPerm = M.permanent := by
  rw [← permanent_transpose, permanent, rectPerm]
  exact Fintype.sum_equiv (Equiv.embeddingEquivOfFinite m) _ _ fun σ => rfl

omit [DecidableEq m] [DecidableEq n] in
/-- The rectangular permanent vanishes when there are fewer columns than rows. -/
theorem rectPerm_eq_zero_of_card_lt (b : Matrix m n R) (h : card n < card m) :
    b.rectPerm = 0 := by
  have := Function.Embedding.isEmpty_of_card_lt h
  simp [rectPerm]

omit [DecidableEq m] in
/-- `rectPermSurj Z` vanishes when `Z` has more columns than there are rows. -/
theorem rectPermSurj_eq_zero_of_card_lt (Z : Finset n) (b : Matrix m n R) (h : card m < #Z) :
    b.rectPermSurj Z = 0 := by
  refine sum_eq_zero fun σ hσ => absurd (card_le_card (mem_filter.1 hσ).2) ?_
  simpa using h

omit [Fintype n] in
/-- Expanding the product over the orbits of `π` of the column sums over `T` gives the sum over
the functions into `T` that are constant on the orbits of `π`. -/
theorem prod_quotient_sameCycle_sum_eq (π : Perm m) (T : Finset n) (b : Matrix m n R) :
    ∏ q : Quotient (SameCycle.setoid π), ∑ j ∈ T, ∏ r with Quotient.mk _ r = q, b r j =
      ∑ f ∈ piFinset (fun _ : m => T) with ∀ r, f (π r) = f r, ∏ r, b r (f r) := by
  rw [prod_univ_sum]
  have key (x : Quotient (SameCycle.setoid π) → n) :
      ∏ q, ∏ r with Quotient.mk _ r = q, b r (x q) = ∏ r, b r (x (Quotient.mk _ r)) := by
    rw [← prod_fiberwise univ (Quotient.mk (SameCycle.setoid π))
      (fun r => b r (x (Quotient.mk _ r)))]
    refine prod_congr rfl fun q _ => prod_congr rfl fun r hr => ?_
    rw [(mem_filter.1 hr).2]
  simp_rw [key]
  refine sum_bij (fun x _ => x ∘ Quotient.mk _) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_piFinset, Function.comp_apply] at hx ⊢
    exact ⟨fun r => hx _, fun r => congrArg x (Quotient.sound (SameCycle.refl π r).apply_left)⟩
  · intro x _ y _ h
    exact Quotient.mk_surjective.injective_comp_right h
  · intro f hf
    simp only [mem_filter, mem_piFinset] at hf
    refine ⟨Quotient.lift f fun x y h => apply_eq_of_sameCycle hf.2 h, ?_, rfl⟩
    simp only [mem_piFinset]
    intro q
    induction q using Quotient.ind
    exact hf.1 _
  · intro x _
    rfl

end CommSemiring

section CommRing

variable [CommRing R] [DecidableEq m] [DecidableEq n]

omit [Fintype n] in
/-- **Binet–Minc identity for injections into `T`**, in permutation form: the sum over the
injective functions `f : m → n` with values in `T` of `∏ r, b r (f r)` is the signed sum over
permutations `π` of `m` of the product over the orbits `q` of `π` of `∑_{j ∈ T} ∏_{r ∈ q} b r j`.
Original; [Forbes, Thm. 13][Forbes2024] states the case `T = univ` grouped by set partitions. -/
theorem sum_injective_eq_sum_sign_prod_sameCycle (T : Finset n) (b : Matrix m n R) :
    ∑ f ∈ piFinset (fun _ : m => T) with Function.Injective f, ∏ r, b r (f r) =
      ∑ π : Perm m, sign π • ∏ q : Quotient (SameCycle.setoid π),
        ∑ j ∈ T, ∏ r with Quotient.mk _ r = q, b r j := by
  simp_rw [prod_quotient_sameCycle_sum_eq, smul_sum, sum_filter, Units.smul_def]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  rw [← sum_filter, ← sum_smul, sum_sign_filter_apply_eq, ite_smul, one_smul, zero_smul]

omit [DecidableEq n] in
/-- **Binet–Minc identity**, in permutation form: the rectangular permanent is the signed sum
over permutations `π` of the rows of the product over the orbits `q` of `π` of
`∑_j ∏_{r ∈ q} b r j`. Original form; [Forbes, Thm. 13][Forbes2024] states the identity grouped
by set partitions of the rows. -/
theorem rectPerm_eq_sum_sign_prod_sameCycle (b : Matrix m n R) :
    b.rectPerm = ∑ π : Perm m, sign π • ∏ q : Quotient (SameCycle.setoid π),
      ∑ j, ∏ r with Quotient.mk _ r = q, b r j := by
  classical
  rw [rectPerm_eq_sum_injective, ← sum_injective_eq_sum_sign_prod_sameCycle, piFinset_univ]

/-- **Binet–Minc identity with inclusion–exclusion** (original): the sum over the injections whose
image contains `Z` is the signed sum over permutations `π` of the rows of
`∑_{Y ⊆ Z} (-1)^{|Y|} ∏_{q ∈ orbits π} ∑_{j ∉ Y} ∏_{r ∈ q} b r j`. For `Z = ∅` this is
`Matrix.rectPerm_eq_sum_sign_prod_sameCycle`. -/
theorem rectPermSurj_eq_sum_sign_prod_sameCycle (Z : Finset n) (b : Matrix m n R) :
    b.rectPermSurj Z = ∑ π : Perm m, sign π • ∑ Y ∈ Z.powerset, (-1) ^ #Y *
      ∏ q : Quotient (SameCycle.setoid π), ∑ j ∈ Yᶜ, ∏ r with Quotient.mk _ r = q, b r j := by
  have h1 (Y : Finset n) :
      ∑ f ∈ piFinset (fun _ : m => Yᶜ) with Function.Injective f, ∏ r, b r (f r) =
        ∑ f : m → n with Function.Injective f, if ∀ r, f r ∉ Y then ∏ r, b r (f r) else 0 := by
    rw [show piFinset (fun _ : m => Yᶜ) = univ.filter (fun f : m → n => ∀ r, f r ∉ Y) by
        ext; simp,
      filter_filter, sum_filter, sum_filter]
    refine sum_congr rfl fun f _ => ?_
    by_cases hi : Function.Injective f <;> by_cases hY : ∀ r, f r ∉ Y <;> simp [hi, hY]
  have h2 (f : m → n) :
      ∑ Y ∈ Z.powerset with ∀ r, f r ∉ Y, (-1 : R) ^ #Y = if Z ⊆ univ.image f then 1 else 0 := by
    have hY : {Y ∈ Z.powerset | ∀ r, f r ∉ Y} = (Z \ univ.image f).powerset := by
      ext Y
      simp only [mem_filter, mem_powerset, subset_sdiff, disjoint_left, mem_image, mem_univ,
        true_and]
      constructor
      · rintro ⟨hZ, hf⟩
        exact ⟨hZ, fun j hj ⟨r, hr⟩ => hf r (hr ▸ hj)⟩
      · rintro ⟨hZ, hf⟩
        exact ⟨hZ, fun r hr => hf hr ⟨r, rfl⟩⟩
    have := congrArg (Int.cast : ℤ → R) (sum_powerset_neg_one_pow_card (x := Z \ univ.image f))
    push_cast at this
    rw [hY, this]
    exact if_congr sdiff_eq_empty_iff_subset rfl rfl
  simp_rw [smul_sum, ← mul_smul_comm]
  rw [sum_comm]
  simp_rw [← mul_sum, ← sum_injective_eq_sum_sign_prod_sameCycle, h1, mul_sum]
  rw [sum_comm, rectPermSurj_eq_sum_injective, ← filter_filter, sum_filter]
  refine sum_congr rfl fun f _ => ?_
  rw [← one_mul (∏ r, b r (f r)), ← ite_zero_mul, ← h2, sum_filter, sum_mul]
  refine sum_congr rfl fun Y _ => ?_
  split_ifs <;> simp

end CommRing

end Matrix
