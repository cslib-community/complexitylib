/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/{,Order/}BigOperators/Expect.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Fin

/-!
# Uniform averages of indicators and second moments

Over a finite type, the uniform average of the indicator of a predicate is the density of the set
where it holds (`Fintype.expect_boole`), the counterpart for `𝔼` of `Finset.sum_boole`: the
probability of an event under the uniform distribution is the expectation of its indicator. With
it, **Markov's inequality** bounds the density of the set where a nonnegative function is large
by its average (`Fintype.mul_dens_filter_le_expect`), and the **second moment method** bounds the
density of the set where a function does not vanish from below by the square of its average over
the average of its square (`Fintype.sq_expect_le_dens_mul_expect_sq`).

The square of an average is at most the average of the squares (`Finset.sq_expect_le_expect_sq`),
the form for `𝔼` of `sum_div_card_sq_le_sum_sq_div_card`; both inequalities of second moments are
cases of the Cauchy–Schwarz inequality `Finset.expect_mul_sq_le_sq_mul_sq`, which also gives its
form with square roots (`Real.expect_mul_le_sqrt_mul_sqrt`, the form for `𝔼` of
`Real.sum_mul_le_sqrt_mul_sqrt`) and the triangle inequality for `√(𝔼 f²)`
(`Fintype.expect_add_sq_le`).

The uniform average over a product is the iterated average (`Fintype.expect_prod_type`), so a
function of some of the coordinates has the same average on the product
(`Fintype.expect_comp_fst`, `Fintype.expect_comp_snd`), and a function on a product splits
orthogonally into its fiber averages and a part of average zero on every fiber
(`Fintype.exists_eq_add_expect_fiber_eq_zero`). The uniform average on a finite group is
translation invariant (`Fintype.expect_add_left`), and resampling one coordinate of a uniformly
random tuple leaves its average unchanged (`Fintype.expect_expect_update`).

## Main results

* `Finset.sq_expect_le_expect_sq`: the square of an average is at most the average of the squares.
* `Finset.prod_filter_mem_eq_prod_filter_notMem`: the sets containing an element are the sets
  avoiding it, with the element inserted.
* `Real.expect_mul_le_sqrt_mul_sqrt`: the Cauchy–Schwarz inequality for averages.
* `Fintype.expect_prod_type`, `Fin.expect_univ_cons`, `Fin.sum_univ_cons_bool`,
  `Fin.expect_univ_cons_bool`: the average or sum over a product or non-empty tuple type is the
  iterated average or sum.
* `Fintype.expect_comp_fst`, `Fintype.expect_comp_snd`, `Fintype.expect_comp_fst_snd_fst`: a
  function of some of the coordinates has the same average on the product.
* `Fintype.expect_unique`, `Fintype.expect_bool`, `Fintype.expect_unique_bool`: averages on
  `Unique` types and `Bool`.
* `Fintype.expect_add_left`, `Fintype.expect_expect_update`,
  `Fintype.expect_comp_arrowCongr`, `Fintype.expect_sumElim`,
  `Fintype.expect_restrict_coordinates`: translation, coordinate-resampling, coordinate-renaming,
  disjoint-union splitting, and coordinate-restriction invariance of uniform averages.
* `Fintype.expect_sub_expect_fiber`, `Fintype.expect_add_sq_of_expect_fiber_eq_zero`,
  `Fintype.exists_eq_add_expect_fiber_eq_zero`: orthogonal fiber decomposition of second moments on
  product types.
* `Fintype.expect_boole`, `Fintype.expect_boole_sq`, `Fintype.expect_boole_mem`,
  `Fintype.expect_boole_mem_sq`: the average of an indicator (or its square) is a density.
* `Fintype.mul_dens_filter_le_expect`: Markov's inequality for a uniform average.
* `Fintype.sq_expect_le_dens_mul_expect_sq`,
  `Fintype.sq_expect_le_dens_mul_expect_sq_of_eq_zero`: the second moment method for a uniform
  average.
* `Fintype.expect_add_sq_le`, `Fintype.expect_sq_le_of_expect_mul_le`: second-moment bounds from
  triangle and Cauchy–Schwarz inequalities.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

variable {ι R : Type*} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
  [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]

/-- The square of an average is at most the average of the squares. -/
theorem sq_expect_le_expect_sq (s : Finset ι) (f : ι → R) :
    (𝔼 i ∈ s, f i) ^ 2 ≤ 𝔼 i ∈ s, f i ^ 2 := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simpa [hs] using expect_mul_sq_le_sq_mul_sq s f fun _ ↦ 1

/-- The sets containing `i` are the sets avoiding `i`, with `i` inserted. -/
@[to_additive /-- The sets containing `i` are the sets avoiding `i`, with `i` inserted. -/]
theorem prod_filter_mem_eq_prod_filter_notMem {M : Type*} [CommMonoid M] [Fintype ι]
    [DecidableEq ι] (i : ι) (g : Finset ι → M) :
    ∏ S with i ∈ S, g S = ∏ T with i ∉ T, g (insert i T) :=
  prod_nbij' (·.erase i) (insert i) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ hS => insert_erase (mem_filter.1 hS).2) (fun _ hT => erase_insert (mem_filter.1 hT).2)
    fun _ hS => by rw [insert_erase (mem_filter.1 hS).2]

end Finset

namespace Real

open Finset

/-- **The Cauchy–Schwarz inequality** for averages, with square roots. -/
theorem expect_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    𝔼 i ∈ s, f i * g i ≤ √(𝔼 i ∈ s, f i ^ 2) * √(𝔼 i ∈ s, g i ^ 2) := by
  rw [← Real.sqrt_mul (expect_nonneg fun i _ ↦ sq_nonneg (f i))]
  exact Real.le_sqrt_of_sq_le (expect_mul_sq_le_sq_mul_sq _ _ _)

end Real

namespace Fintype

open Finset

variable {ι 𝕜 : Type*} [Fintype ι]

section Module

variable {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] [Module ℚ≥0 M]

/-- The uniform average over a product is the iterated average. -/
theorem expect_prod_type (f : α × β → M) : 𝔼 x, f x = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← univ_product_univ, expect_product]

/-- A function of the first coordinate has the same average on the product. -/
theorem expect_comp_fst [Nonempty β] (f : α → M) : 𝔼 p : α × β, f p.1 = 𝔼 a, f a := by
  simp only [expect_prod_type, Fintype.expect_const]

/-- A function of the second coordinate has the same average on the product. -/
theorem expect_comp_snd [Nonempty α] (f : β → M) : 𝔼 p : α × β, f p.2 = 𝔼 b, f b := by
  simp only [expect_prod_type, Fintype.expect_const]

/-- A function of the first two coordinates has the same average on the product of three. -/
theorem expect_comp_fst_snd_fst [Nonempty γ] (f : α × β → M) :
    𝔼 p : α × β × γ, f (p.1, p.2.1) = 𝔼 q, f q := by
  rw [expect_prod_type, expect_prod_type f]
  exact expect_congr rfl fun a _ ↦ expect_comp_fst fun b ↦ f (a, b)

/-- **Translation invariance**: adding a fixed element permutes a finite additive group, so the
uniform average is unchanged. -/
theorem expect_add_left {G : Type*} [AddGroup G] [Fintype G] (f : G → M) (x : G) :
    𝔼 y, f (x + y) = 𝔼 y, f y :=
  Fintype.expect_equiv (Equiv.addLeft x) _ _ fun _ ↦ rfl

/-- The uniform average over a type with a unique element is the value at `default`. -/
theorem expect_unique [Unique α] (f : α → M) : 𝔼 a, f a = f default := by
  rw [univ_unique, expect_singleton]

/-- Resampling one coordinate of a uniformly random function keeps it uniformly random. -/
theorem expect_expect_update [DecidableEq ι] [Nonempty α] (F : (ι → α) → M) (i : ι) :
    𝔼 s, 𝔼 a, F (Function.update s i a) = 𝔼 s, F s := by
  let e : Equiv.Perm ((ι → α) × α) :=
    Function.Involutive.toPerm (fun p ↦ (Function.update p.1 i p.2, p.1 i)) fun p ↦ by simp
  calc 𝔼 s, 𝔼 a, F (Function.update s i a) = 𝔼 p : (ι → α) × α, F (e p).1 :=
        (Fintype.expect_prod_type (fun p : (ι → α) × α ↦ F (e p).1)).symm
    _ = 𝔼 p : (ι → α) × α, F p.1 := Fintype.expect_equiv e _ _ fun _ ↦ rfl
    _ = 𝔼 s, F s := Fintype.expect_comp_fst F

/-- Renaming the coordinates preserves uniform averages over function types. -/
theorem expect_comp_arrowCongr {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (h : (κ → α) → M) : 𝔼 x : ι → α, h (fun j => x (e.symm j)) = 𝔼 y, h y :=
  Fintype.expect_equiv (e.arrowCongr (Equiv.refl α)) _ _ fun _ => rfl

/-- The uniform average on functions out of `ι ⊕ κ` is the iterated average over functions on `ι`
and functions on `κ`. -/
theorem expect_sumElim {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (h : (ι ⊕ κ → α) → M) :
    𝔼 x, h x = 𝔼 x₁ : ι → α, 𝔼 x₂ : κ → α, h (Sum.elim x₁ x₂) := by
  rw [← Fintype.expect_prod_type fun y : (ι → α) × (κ → α) => h (Sum.elim y.1 y.2)]
  exact Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ α) _ _ fun x =>
    congrArg h (Sum.elim_comp_inl_inr x).symm

/-- Restricting a uniformly random function on `ι` to a subtype of coordinates gives a uniformly
random function on the subtype. -/
theorem expect_restrict_coordinates [DecidableEq ι] [Nonempty α] {p : ι → Prop} [DecidablePred p]
    (f : ({i // p i} → α) → M) : (𝔼 x : ι → α, f (fun i => x i)) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => α)
  rw [← Fintype.expect_equiv e.symm (fun z => f (fun i => e.symm z i)) _ (fun _ => rfl)]
  rw [← univ_product_univ, expect_product]
  have he (a : {i // p i} → α) (b : {i // ¬ p i} → α) :
      (fun i : {i // p i} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  simp_rw [he, Fintype.expect_const]

end Module

/-- The uniform average on `Bool` is the midpoint of the two values. -/
theorem expect_bool [Semifield 𝕜] [CharZero 𝕜] (f : Bool → 𝕜) :
    𝔼 b, f b = (f false + f true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat,
    add_comm]

/-- The uniform average over functions from a `Unique` type to `Bool` is the midpoint of the two
constant functions. -/
theorem expect_unique_bool [Unique ι] [Semifield 𝕜] [CharZero 𝕜] (f : (ι → Bool) → 𝕜) :
    𝔼 x, f x = (f (fun _ => false) + f (fun _ => true)) / 2 := by
  rw [Fintype.expect_equiv (Equiv.funUnique ι Bool) f (fun b => f fun _ => b)
    fun x => congrArg f (funext fun i => congrArg x (Subsingleton.elim i default)),
    Fintype.expect_bool]

/-- Subtracting from a function its averages over the fibers `{a} × β` leaves averages zero over
the fibers. -/
theorem expect_sub_expect_fiber {α β M : Type*} [Fintype β] [AddCommGroup M] [Module ℚ≥0 M]
    (f : α × β → M) (a : α) :
    𝔼 b, (f (a, b) - 𝔼 b', f (a, b')) = 0 :=
  Fintype.expect_balance fun b ↦ f (a, b)

/-- **Pythagoras' theorem** for the splitting of a function on `α × β` into a function of the first
coordinate and a function of average zero over every fiber `{a} × β`. -/
theorem expect_add_sq_of_expect_fiber_eq_zero {α β : Type*} [Fintype α] [Fintype β] (φ : α → ℝ)
    {g : α × β → ℝ} (hg : ∀ a, 𝔼 b, g (a, b) = 0) :
    𝔼 p, (φ p.1 + g p) ^ 2 = 𝔼 p : α × β, φ p.1 ^ 2 + 𝔼 p, g p ^ 2 := by
  have h : 𝔼 p, φ p.1 * g p = 0 := by
    simp only [Fintype.expect_prod_type, ← mul_expect, hg, mul_zero, expect_const_zero]
  simp only [add_sq, expect_add_distrib, mul_assoc, ← mul_expect, h, mul_zero, add_zero]

/-- Every function on `α × β` is a function of the first coordinate, its averages over the fibers
`{a} × β`, plus a function of average zero over every fiber, and the second moments add up. -/
theorem exists_eq_add_expect_fiber_eq_zero {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ) :
    ∃ (f₁ : α → ℝ) (f₂ : α × β → ℝ), f = (fun p ↦ f₁ p.1 + f₂ p) ∧
      (∀ a, 𝔼 b, f₂ (a, b) = 0) ∧ 𝔼 a, f₁ a = 𝔼 p, f p ∧
      𝔼 p, f p ^ 2 = 𝔼 a, f₁ a ^ 2 + 𝔼 p, f₂ p ^ 2 := by
  have hf : f = fun p ↦ 𝔼 b, f (p.1, b) + (f p - 𝔼 b, f (p.1, b)) :=
    funext fun p ↦ (add_sub_cancel _ _).symm
  refine ⟨fun a ↦ 𝔼 b, f (a, b), fun p ↦ f p - 𝔼 b, f (p.1, b), hf, expect_sub_expect_fiber f,
    (Fintype.expect_prod_type f).symm, ?_⟩
  calc 𝔼 p, f p ^ 2 = 𝔼 p, (𝔼 b, f (p.1, b) + (f p - 𝔼 b, f (p.1, b))) ^ 2 := by
        simp only [add_sub_cancel]
    _ = 𝔼 p : α × β, (𝔼 b, f (p.1, b)) ^ 2 + 𝔼 p, (f p - 𝔼 b, f (p.1, b)) ^ 2 :=
        expect_add_sq_of_expect_fiber_eq_zero (fun a ↦ 𝔼 b, f (a, b)) (expect_sub_expect_fiber f)
    _ = _ := by rw [expect_comp_fst (fun a ↦ (𝔼 b, f (a, b)) ^ 2)]

/-- If `𝔼 u² ≤ c √(𝔼 u²) √(𝔼 w²)` then `𝔼 u² ≤ c² 𝔼 w²`. -/
theorem expect_sq_le_of_expect_mul_le {u w : ι → ℝ} {c : ℝ}
    (h : 𝔼 i, u i * u i ≤ c * (√(𝔼 i, u i ^ 2) * √(𝔼 i, w i ^ 2))) :
    𝔼 i, u i ^ 2 ≤ c ^ 2 * 𝔼 i, w i ^ 2 := by
  have hu : 0 ≤ 𝔼 i, u i ^ 2 := expect_nonneg fun i _ ↦ sq_nonneg (u i)
  have hw : 0 ≤ 𝔼 i, w i ^ 2 := expect_nonneg fun i _ ↦ sq_nonneg (w i)
  simp only [← sq] at h
  rw [← Real.sq_sqrt hu, ← Real.sq_sqrt hw, ← mul_pow]
  rcases (Real.sqrt_nonneg (𝔼 i, u i ^ 2)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow two_ne_zero]
    positivity
  · refine pow_le_pow_left₀ hpos.le ?_ 2
    refine le_of_mul_le_mul_left ?_ hpos
    calc √(𝔼 i, u i ^ 2) * √(𝔼 i, u i ^ 2) = 𝔼 i, u i ^ 2 := Real.mul_self_sqrt hu
      _ ≤ _ := h
      _ = _ := by ring

/-- The uniform average of the indicator of `p` is the density of the set where `p` holds. -/
theorem expect_boole [Semifield 𝕜] [CharZero 𝕜] (p : ι → Prop) [DecidablePred p] :
    𝔼 i, (if p i then 1 else 0 : 𝕜) = (dens {i | p i} : 𝕜) := by
  rw [Fintype.expect_eq_sum_div_card, sum_boole, nnratCast_dens]

/-- An indicator function is its own square, so the average of its square is the density of the
set where the predicate holds. -/
theorem expect_boole_sq [Semifield 𝕜] [CharZero 𝕜] (p : ι → Prop) [DecidablePred p] :
    𝔼 i, (if p i then (1 : 𝕜) else 0) ^ 2 = (dens {i : ι | p i} : 𝕜) := by
  simp only [ite_pow, one_pow, zero_pow two_ne_zero, expect_boole]

/-- The uniform average of the indicator of membership in `S` is the density of `S`. -/
theorem expect_boole_mem [DecidableEq ι] [Semifield 𝕜] [CharZero 𝕜] (S : Finset ι) :
    𝔼 i, (if i ∈ S then (1 : 𝕜) else 0) = (dens S : 𝕜) := by
  simp only [expect_boole, filter_mem_eq_inter, univ_inter]

/-- The uniform average of the squared indicator of membership in `S` is the density of `S`. -/
theorem expect_boole_mem_sq [DecidableEq ι] [Semifield 𝕜] [CharZero 𝕜] (S : Finset ι) :
    𝔼 i, (if i ∈ S then (1 : 𝕜) else 0) ^ 2 = (dens S : 𝕜) := by
  simp only [expect_boole_sq, filter_mem_eq_inter, univ_inter]

/-- **Markov's inequality** for a uniform average: a nonnegative function is at least `a` on a set
of density at most its average divided by `a`. -/
theorem mul_dens_filter_le_expect [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : ι → 𝕜} (hf : ∀ i, 0 ≤ f i) (a : 𝕜) :
    a * (dens {i | a ≤ f i} : 𝕜) ≤ 𝔼 i, f i := by
  rw [← expect_boole, mul_expect]
  refine expect_le_expect fun i _ => ?_
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]
    exact hf i

/-- **The second moment method** for a uniform average: the square of the average of `f` is at
most the density of the set where `f` does not vanish times the average of `f ^ 2`. So `f` does not
vanish on a set of density at least `(𝔼 f) ^ 2 / 𝔼 f ^ 2`. -/
theorem sq_expect_le_dens_mul_expect_sq [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [ExistsAddOfLE 𝕜] (f : ι → 𝕜) :
    (𝔼 i, f i) ^ 2 ≤ (dens {i | f i ≠ 0} : 𝕜) * 𝔼 i, f i ^ 2 := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun i ↦ if f i ≠ 0 then (1 : 𝕜) else 0) f
  have h₁ : 𝔼 i, (if f i ≠ 0 then (1 : 𝕜) else 0) * f i = 𝔼 i, f i :=
    expect_congr rfl fun i _ ↦ by split_ifs <;> simp_all
  rwa [h₁, expect_boole_sq] at h

/-- By the second moment method (`Fintype.sq_expect_le_dens_mul_expect_sq`), the squared average
of a function vanishing outside `C` is at most the density of `C` times its second moment. -/
theorem sq_expect_le_dens_mul_expect_sq_of_eq_zero [Semifield 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] {C : Finset ι} {f : ι → 𝕜}
    (hf : ∀ i ∉ C, f i = 0) :
    (𝔼 i, f i) ^ 2 ≤ (dens C : 𝕜) * 𝔼 i, f i ^ 2 := by
  classical
  refine (sq_expect_le_dens_mul_expect_sq f).trans ?_
  have hsub : ({i : ι | f i ≠ 0} : Finset ι) ⊆ C := fun i hi =>
    by_contra fun hiC => (mem_filter.mp hi).2 (hf i hiC)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast dens_le_dens hsub)
    (expect_nonneg fun _ _ => sq_nonneg _)

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A read that is correct with probability at least `1 - δ` whatever the first argument is wrong
with probability at most `δ` on average. -/
theorem expect_expect_one_sub_le {β : Type*} [Nonempty ι] [Fintype β] [Nonempty β]
    {c : ι → β → 𝕜} {δ : 𝕜} (h : ∀ i, 1 - δ ≤ 𝔼 j, c i j) : 𝔼 i, 𝔼 j, (1 - c i j) ≤ δ :=
  expect_le univ_nonempty fun i _ => by
    rw [expect_sub_distrib, Fintype.expect_const]
    linarith [h i]

/-- **The triangle inequality for `√(𝔼 f²)`**, squared: if `𝔼 X² ≤ α² A` and `𝔼 Y² ≤ β² A`, then
`𝔼 (a X + b Y)² ≤ (a α + b β)² A` for `a, b ≥ 0`. -/
theorem expect_add_sq_le {X Y : ι → 𝕜} {a b α β A : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hX : 𝔼 i, X i ^ 2 ≤ α ^ 2 * A) (hY : 𝔼 i, Y i ^ 2 ≤ β ^ 2 * A) :
    𝔼 i, (a * X i + b * Y i) ^ 2 ≤ (a * α + b * β) ^ 2 * A := by
  have hXY : 𝔼 i, X i * Y i ≤ α * β * A := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
    calc (𝔼 i, X i * Y i) ^ 2 ≤ (𝔼 i, X i ^ 2) * 𝔼 i, Y i ^ 2 := expect_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (α ^ 2 * A) * (β ^ 2 * A) :=
        mul_le_mul hX hY (expect_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ = (α * β * A) ^ 2 := by ring
  calc 𝔼 i, (a * X i + b * Y i) ^ 2
      = a ^ 2 * 𝔼 i, X i ^ 2 + 2 * a * b * 𝔼 i, X i * Y i + b ^ 2 * 𝔼 i, Y i ^ 2 := by
        simp only [mul_expect, ← expect_add_distrib]
        exact expect_congr rfl fun i _ ↦ by ring
    _ ≤ a ^ 2 * (α ^ 2 * A) + 2 * a * b * (α * β * A) + b ^ 2 * (β ^ 2 * A) := by gcongr
    _ = (a * α + b * β) ^ 2 * A := by ring

end LinearOrderedField

end Fintype

namespace Fin

open Finset

/-- Splitting off the first coordinate of a tuple on `Fin (n + 1)`: the uniform average over
`(i : Fin (n + 1)) → α i` is the iterated average over the head `α 0` and the tail. -/
theorem expect_univ_cons {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, Fintype (α i)]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (f : ((i : Fin (n + 1)) → α i) → M) :
    𝔼 x, f x = 𝔼 a, 𝔼 y, f (Fin.cons a y) := by
  rw [← Fintype.expect_equiv (Fin.consEquiv α) (fun p ↦ f (Fin.cons p.1 p.2)) f (fun _ ↦ rfl),
    Fintype.expect_prod_type]

/-- Splitting off the first bit of a tuple on `Fin (n + 1)`: the sum over `Fin (n + 1) → Bool`
is the sum with first bit `false` plus the sum with first bit `true`. -/
theorem sum_univ_cons_bool {n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (n + 1) → Bool) → M) :
    ∑ x, f x = (∑ y, f (Fin.cons false y)) + ∑ y, f (Fin.cons true y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f, Fintype.sum_prod_type,
    Fintype.sum_bool]
  exact add_comm _ _

/-- Splitting off the first bit of a tuple on `Fin (n + 1)`: the uniform average over
`Fin (n + 1) → Bool` is the midpoint of the averages with first bit `false` and `true`. -/
theorem expect_univ_cons_bool {n : ℕ} {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    (f : (Fin (n + 1) → Bool) → 𝕜) :
    𝔼 x, f x = ((𝔼 y, f (Fin.cons false y)) + 𝔼 y, f (Fin.cons true y)) / 2 := by
  rw [Fin.expect_univ_cons, Fintype.expect_bool]

end Fin
