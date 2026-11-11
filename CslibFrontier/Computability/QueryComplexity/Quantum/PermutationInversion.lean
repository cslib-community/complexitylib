/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Foundations.Quantum.Measurement.Overlap
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap

/-!
# Quantum query lower bound for inverting a permutation

This module proves [Ambainis2002], Theorem 7 (Section 6.2 of `arXiv:quant-ph/0002066v1`): any
bounded-error quantum query algorithm that inverts a permutation `π : Equiv.Perm ι` at a fixed
target element `target : ι` — finding the unique index `i = π.symm target` satisfying
`π i = target` via black-box value queries `(step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ]
EuclideanSpace ℂ V))` to `⇑π : ι → ι` — uses `Ω(√|ι|)` queries.

**The adversary relation.** Given disjoint index sets `I₀, I₁ : Finset ι`, let `permInvLeft I₀
target` be the permutations `π` with `π.symm target ∈ I₀`, and `permInvRight I₁ target` those with
`σ.symm target ∈ I₁`. The relation `permInvPermRel I₀ I₁ target` pairs `π ∈ permInvLeft I₀ target`
with `σ = π * Equiv.swap (π.symm target) j` for each `j ∈ I₁`:

* every `π ∈ permInvLeft I₀ target` has `#I₁` partners (`card_permInvPermRel_fst`), and every
  `σ ∈ permInvRight I₁ target` has `#I₀` partners (`card_permInvPermRel_snd`);
* if `(π, σ) ∈ permInvPermRel I₀ I₁ target` and `π k ≠ σ k`, then `k` is either `π.symm target`
  (where `l_{σ, k} = 1` and `l_{π, k} ≤ #I₁`) or `σ.symm target` (where `l_{π, k} = 1` and
  `l_{σ, k} ≤ #I₀`), so `l_{π, k} * l_{σ, k} ≤ max #I₀ #I₁` (`card_permInvPermRel_diff_mul_le`).

Applying `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value` with `m = #I₁`, `m' = #I₀`, and
`L = max #I₀ #I₁` and canceling `√(max #I₀ #I₁)` via `min_mul_max` gives
`(1 - δ) √(min #I₀ #I₁) ≤ 2 T` (`one_sub_mul_sqrt_min_le_of_permInversion_partition`). Splitting `ι`
into halves of sizes `⌊|ι| / 2⌋` and `|ι| - ⌊|ι| / 2⌋` yields:

* `(1 - 2√(ε(1-ε))) √⌊|ι| / 2⌋ ≤ 2 T` (`one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion`
  and its `measureOut` form, valid for every finite type `ι`);
* `(1 - 2√(ε(1-ε))) √(|ι| - 1) ≤ 2 √2 T`
  (`one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion`, sharp at `|ι| = 1` where `0`
  queries invert the unique permutation);
* `(1 - 2√(ε(1-ε))) √|ι| ≤ 2 √3 T` for `2 ≤ |ι|`
  (`one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion`);
* at error `ε = 1 / 3`, `|ι| / 2 ≤ 1296 T²` for all `ι` (`permInversion_div_two_lower_bound`), and
  `|ι| ≤ 3888 T²` for `2 ≤ |ι|` (`permInversion_lower_bound`,
  `permInversion_measureOut_lower_bound`).

## Main definitions

* `Cslib.Quantum.permInvLeft`, `Cslib.Quantum.permInvRight`: permutations placing `target` in `I₀`
  or `I₁`.
* `Cslib.Quantum.permInvPermRel`: Ambainis's transposition adversary relation on `Equiv.Perm ι`.

## Main results

* `Cslib.Quantum.card_permInvPermRel_fst`, `Cslib.Quantum.card_permInvPermRel_snd`,
  `Cslib.Quantum.card_permInvPermRel_diff_mul_le`: combinatorial parameters of `permInvPermRel`.
* `Cslib.Quantum.one_sub_mul_sqrt_min_le_of_permInversion_partition`,
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_min_le_of_permInversion_partition`: partition-form
  permutation-inversion bounds.
* `Cslib.Quantum.one_sub_mul_sqrt_div_two_le_of_permInversion`,
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion`,
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion_measureOut`,
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion`,
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion`: [Ambainis2002], Theorem 7.
* `Cslib.Quantum.permInversion_div_two_lower_bound`, `Cslib.Quantum.permInversion_lower_bound`,
  `Cslib.Quantum.permInversion_measureOut_lower_bound`: bounded-error (`ε = 1 / 3`) corollaries.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002], Section 6.2, Theorem 7
  (`arXiv:quant-ph/0002066v1`).
-/

public section

namespace Cslib.Quantum

open Finset

/-! ### Combinatorial adversary relation on permutations -/

section PermRelation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Permutations `π : Equiv.Perm ι` whose preimage `π.symm target` of `target` lies in `I₀`. -/
@[expose] def permInvLeft (I₀ : Finset ι) (target : ι) : Finset (Equiv.Perm ι) :=
  univ.filter fun π => π.symm target ∈ I₀

/-- Permutations `σ : Equiv.Perm ι` whose preimage `σ.symm target` of `target` lies in `I₁`. -/
@[expose] def permInvRight (I₁ : Finset ι) (target : ι) : Finset (Equiv.Perm ι) :=
  univ.filter fun σ => σ.symm target ∈ I₁

/-- Ambainis's transposition adversary relation ([Ambainis2002], Theorem 7): relates each
`π ∈ permInvLeft I₀ target` to `π * Equiv.swap (π.symm target) j` for `j ∈ I₁`. -/
@[expose] def permInvPermRel (I₀ I₁ : Finset ι) (target : ι) :
    Finset (Equiv.Perm ι × Equiv.Perm ι) :=
  (permInvLeft I₀ target).biUnion fun π =>
    I₁.image fun j => (π, π * Equiv.swap (π.symm target) j)

omit [Fintype ι] in
private theorem symm_mul_swap_self (π : Equiv.Perm ι) (j target : ι) :
    (π * Equiv.swap (π.symm target) j).symm target = j := by
  rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.apply_symm_apply]

omit [Fintype ι] in
private theorem eq_mul_swap_iff (π σ : Equiv.Perm ι) (i j : ι) :
    σ = π * Equiv.swap i j ↔ π = σ * Equiv.swap j i := by
  constructor <;> rintro rfl <;> ext k <;> simp [Equiv.swap_comm i j]

omit [Fintype ι] in
private theorem eq_mul_swap_symm_iff (π σ : Equiv.Perm ι) (target : ι) :
    σ = π * Equiv.swap (π.symm target) (σ.symm target) ↔
      π = σ * Equiv.swap (σ.symm target) (π.symm target) :=
  eq_mul_swap_iff π σ (π.symm target) (σ.symm target)

/-- Membership characterization of `permInvPermRel I₀ I₁ target`. -/
theorem mem_permInvPermRel {I₀ I₁ : Finset ι} {target : ι} {p : Equiv.Perm ι × Equiv.Perm ι} :
    p ∈ permInvPermRel I₀ I₁ target ↔
      p.1.symm target ∈ I₀ ∧ p.2.symm target ∈ I₁ ∧
        p.2 = p.1 * Equiv.swap (p.1.symm target) (p.2.symm target) := by
  obtain ⟨π, σ⟩ := p
  simp only [permInvPermRel, permInvLeft, mem_biUnion, mem_filter, mem_univ, true_and, mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨π', hπ', j, hj, rfl, rfl⟩
    have hsym := symm_mul_swap_self π' j target
    exact ⟨hπ', by rwa [hsym], by rw [hsym]⟩
  · rintro ⟨h₀, h₁, hσ⟩
    exact ⟨π, h₀, σ.symm target, h₁, rfl, hσ.symm⟩

/-- Swapping coordinates maps `permInvPermRel I₀ I₁ target` onto `permInvPermRel I₁ I₀ target`. -/
theorem permInvPermRel_swap (I₀ I₁ : Finset ι) (target : ι) :
    (permInvPermRel I₀ I₁ target).map (Equiv.prodComm _ _).toEmbedding =
      permInvPermRel I₁ I₀ target := by
  ext ⟨σ, π⟩
  simp only [mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, mem_permInvPermRel]
  exact ⟨fun ⟨h₀, h₁, h⟩ => ⟨h₁, h₀, (eq_mul_swap_symm_iff π σ target).1 h⟩,
    fun ⟨h₁, h₀, h⟩ => ⟨h₀, h₁, (eq_mul_swap_symm_iff π σ target).2 h⟩⟩

/-- When `I₀` and `I₁` are nonempty, `permInvPermRel I₀ I₁ target` is nonempty. -/
theorem permInvPermRel_nonempty {I₀ I₁ : Finset ι} (h₀ : I₀.Nonempty) (h₁ : I₁.Nonempty)
    (target : ι) : (permInvPermRel I₀ I₁ target).Nonempty := by
  obtain ⟨i₀, hi₀⟩ := h₀
  obtain ⟨j₁, hj₁⟩ := h₁
  let π : Equiv.Perm ι := Equiv.swap i₀ target
  have hπ : π.symm target = i₀ := by
    rw [Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_left i₀ target).symm
  refine ⟨(π, π * Equiv.swap i₀ j₁), mem_permInvPermRel.2 ?_⟩
  have hσ : (π * Equiv.swap i₀ j₁).symm target = j₁ := by
    simpa only [hπ] using symm_mul_swap_self π j₁ target
  exact ⟨by rwa [hπ], by rwa [hσ], by rw [hπ, hσ]⟩

/-- Every related pair across disjoint `I₀` and `I₁` has distinct target preimages. -/
theorem permInvPermRel_symm_ne {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁) {target : ι}
    {p : Equiv.Perm ι × Equiv.Perm ι} (hp : p ∈ permInvPermRel I₀ I₁ target) :
    p.1.symm target ≠ p.2.symm target := by
  obtain ⟨h₀, h₁, -⟩ := mem_permInvPermRel.1 hp
  exact fun heq => Finset.disjoint_left.1 hdisj h₀ (heq ▸ h₁)

/-- Every first permutation in `permInvPermRel I₀ I₁ target` has exactly `#I₁` partners. -/
theorem card_permInvPermRel_fst {I₀ I₁ : Finset ι} {target : ι}
    {p : Equiv.Perm ι × Equiv.Perm ι} (hp : p ∈ permInvPermRel I₀ I₁ target) :
    #{q ∈ permInvPermRel I₀ I₁ target | q.1 = p.1} = #I₁ := by
  obtain ⟨h₀, -, -⟩ := mem_permInvPermRel.1 hp
  have hf : {q ∈ permInvPermRel I₀ I₁ target | q.1 = p.1} =
      I₁.image fun j => (p.1, p.1 * Equiv.swap (p.1.symm target) j) := by
    ext ⟨π, σ⟩
    simp only [mem_filter, mem_permInvPermRel, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, h₁, hσ⟩, rfl⟩
      exact ⟨σ.symm target, h₁, rfl, hσ.symm⟩
    · rintro ⟨j, hj, hπ, rfl⟩
      subst hπ
      have hsym := symm_mul_swap_self p.1 j target
      exact ⟨⟨h₀, by rwa [hsym], by rw [hsym]⟩, rfl⟩
  rw [hf, card_image_of_injective]
  intro j₁ j₂ hj
  simp only [Prod.mk.injEq, true_and] at hj
  have := congrArg (fun τ : Equiv.Perm ι => τ.symm target) hj
  simpa only [symm_mul_swap_self] using this

/-- Every second permutation in `permInvPermRel I₀ I₁ target` has exactly `#I₀` partners. -/
theorem card_permInvPermRel_snd {I₀ I₁ : Finset ι} {target : ι}
    {p : Equiv.Perm ι × Equiv.Perm ι} (hp : p ∈ permInvPermRel I₀ I₁ target) :
    #{q ∈ permInvPermRel I₀ I₁ target | q.2 = p.2} = #I₀ := by
  have hp' : (p.2, p.1) ∈ permInvPermRel I₁ I₀ target := by
    rw [← permInvPermRel_swap I₀ I₁ target]
    exact mem_map.2 ⟨p, hp, rfl⟩
  have hcard := card_permInvPermRel_fst hp'
  rw [← hcard, ← permInvPermRel_swap I₀ I₁ target, filter_map, card_map]
  rfl

omit [Fintype ι] in
private theorem diff_coord_eq_or {π σ : Equiv.Perm ι} {target k : ι}
    (hσ : σ = π * Equiv.swap (π.symm target) (σ.symm target)) (hk : π k ≠ σ k) :
    k = π.symm target ∨ k = σ.symm target := by
  by_contra h
  rw [not_or] at h
  apply hk
  rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h.1 h.2]

private theorem card_permInvPermRel_diff_snd_le_one {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁)
    {target : ι} {π σ : Equiv.Perm ι} (hp : (π, σ) ∈ permInvPermRel I₀ I₁ target) :
    #{q ∈ permInvPermRel I₀ I₁ target |
      q.1 (π.symm target) ≠ q.2 (π.symm target) ∧ q.2 = σ} ≤ 1 := by
  refine card_le_one.2 fun ⟨π₁, σ₁⟩ h₁ ⟨π₂, σ₂⟩ h₂ => ?_
  simp only [mem_filter, mem_permInvPermRel] at h₁ h₂
  obtain ⟨⟨_, hσ₁₁, hσ₁⟩, hne₁, hσ₁_eq⟩ := h₁
  obtain ⟨⟨_, _, hσ₂⟩, hne₂, hσ₂_eq⟩ := h₂
  rw [hσ₁_eq] at hσ₁₁ hσ₁ hne₁ ⊢
  rw [hσ₂_eq] at hσ₂ hne₂ ⊢
  obtain ⟨hπ₀, _, _⟩ := mem_permInvPermRel.1 hp
  have hne_j : π.symm target ≠ σ.symm target :=
    fun heq => Finset.disjoint_left.1 hdisj hπ₀ (heq ▸ hσ₁₁)
  have hi₁ : π.symm target = π₁.symm target :=
    (diff_coord_eq_or hσ₁ hne₁).resolve_right hne_j
  have hi₂ : π.symm target = π₂.symm target :=
    (diff_coord_eq_or hσ₂ hne₂).resolve_right hne_j
  have he₁ := (eq_mul_swap_symm_iff π₁ σ target).1 hσ₁
  have he₂ := (eq_mul_swap_symm_iff π₂ σ target).1 hσ₂
  rw [← hi₁] at he₁
  rw [← hi₂] at he₂
  exact Prod.ext (he₁.trans he₂.symm) rfl

private theorem card_permInvPermRel_diff_mul_le_fst {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁)
    {target : ι} {π σ : Equiv.Perm ι} (hp : (π, σ) ∈ permInvPermRel I₀ I₁ target) :
    #{q ∈ permInvPermRel I₀ I₁ target |
        q.1 (π.symm target) ≠ q.2 (π.symm target) ∧ q.1 = π} *
      #{q ∈ permInvPermRel I₀ I₁ target |
        q.1 (π.symm target) ≠ q.2 (π.symm target) ∧ q.2 = σ} ≤ #I₁ := by
  have hsub : {q ∈ permInvPermRel I₀ I₁ target |
      q.1 (π.symm target) ≠ q.2 (π.symm target) ∧ q.1 = π} ⊆
      {q ∈ permInvPermRel I₀ I₁ target | q.1 = π} :=
    fun _ h => mem_filter.2 ⟨(mem_filter.1 h).1, (mem_filter.1 h).2.2⟩
  have h₁ := (card_le_card hsub).trans (card_permInvPermRel_fst hp).le
  have h₂ := card_permInvPermRel_diff_snd_le_one hdisj hp
  exact (Nat.mul_le_mul h₁ h₂).trans (Nat.mul_one _).le

/-- **Key product bound for permutation inversion** ([Ambainis2002], proof of Theorem 7): at any
differing coordinate `k` of `(π, σ) ∈ permInvPermRel I₀ I₁ target` (`Disjoint I₀ I₁`), one of the
two directional conflict counts is `1` and the other is at most `#I₁` or `#I₀`, so their product is
at most `max #I₀ #I₁`. -/
theorem card_permInvPermRel_diff_mul_le {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁) {target : ι}
    {p : Equiv.Perm ι × Equiv.Perm ι} (hp : p ∈ permInvPermRel I₀ I₁ target) {k : ι}
    (hk : p.1 k ≠ p.2 k) :
    #{q ∈ permInvPermRel I₀ I₁ target | q.1 k ≠ q.2 k ∧ q.1 = p.1} *
      #{q ∈ permInvPermRel I₀ I₁ target | q.1 k ≠ q.2 k ∧ q.2 = p.2} ≤
      max #I₀ #I₁ := by
  obtain ⟨π, σ⟩ := p
  obtain ⟨-, -, hσ⟩ := mem_permInvPermRel.1 hp
  rcases diff_coord_eq_or hσ hk with rfl | rfl
  · exact (card_permInvPermRel_diff_mul_le_fst hdisj hp).trans (Nat.le_max_right _ _)
  · have hp_swap : (σ, π) ∈ permInvPermRel I₁ I₀ target := by
      rw [← permInvPermRel_swap I₀ I₁ target]
      exact mem_map.2 ⟨(π, σ), hp, rfl⟩
    have hsw := (card_permInvPermRel_diff_mul_le_fst hdisj.symm hp_swap).trans
      (Nat.le_max_left #I₀ #I₁)
    refine (le_of_eq ?_).trans hsw
    rw [Nat.mul_comm]
    congr 1 <;>
      · symm
        rw [← permInvPermRel_swap I₀ I₁ target, filter_map, card_map]
        congr 1
        ext ⟨a, b⟩
        simp [Function.comp_def, ne_comm]

end PermRelation

/-! ### Quantum query lower bounds for inverting a permutation -/

section QuantumLowerBounds

private def permPairEmb (ι : Type*) : (Equiv.Perm ι × Equiv.Perm ι) ↪ ((ι → ι) × (ι → ι)) where
  toFun p := (⇑p.1, ⇑p.2)
  inj' p₁ p₂ h := by
    obtain ⟨a₁, b₁⟩ := p₁
    obtain ⟨a₂, b₂⟩ := p₂
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (DFunLike.coe_injective h.1) (DFunLike.coe_injective h.2)

@[simp] private theorem permPairEmb_apply {ι : Type*} (p : Equiv.Perm ι × Equiv.Perm ι) :
    permPairEmb ι p = (⇑p.1, ⇑p.2) :=
  rfl

/-- **Partition-form overlap bound for permutation inversion**: for disjoint `I₀, I₁ : Finset ι`,
if a `T`-query value-query algorithm `(step, U, ψ₀)` (`‖ψ₀‖ = 1`) ends with state overlap at most
`δ` on every pair `(π, σ) ∈ permInvPermRel I₀ I₁ target`, then
`(1 - δ) √(min #I₀ #I₁) ≤ 2 T`. -/
theorem one_sub_mul_sqrt_min_le_of_permInversion_partition {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁) (target : ι) {δ : ℝ}
    (hδ : ∀ p ∈ permInvPermRel I₀ I₁ target,
      ‖inner ℂ (runValue step U ψ₀ ⇑p.1 T) (runValue step U ψ₀ ⇑p.2 T)‖ ≤ δ) :
    (1 - δ) * √(min #I₀ #I₁ : ℕ) ≤ 2 * T := by
  by_cases hne₀ : I₀.Nonempty
  · by_cases hne₁ : I₁.Nonempty
    · let R := (permInvPermRel I₀ I₁ target).map (permPairEmb ι)
      have hR : R.Nonempty := (permInvPermRel_nonempty hne₀ hne₁ target).map
      have hadv := one_sub_mul_sqrt_le_two_mul_mul_sqrt_value step U hψ₀ T hR
        (δ := δ) (m := #I₁) (m' := #I₀) (L := max #I₀ #I₁)
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
          exact hδ q hq)
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
          rw [← card_permInvPermRel_fst hq, filter_map, card_map]
          refine le_of_eq (congrArg card (filter_congr fun r _ => ?_))
          simp [DFunLike.coe_fn_eq])
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
          rw [← card_permInvPermRel_snd hq, filter_map, card_map]
          refine le_of_eq (congrArg card (filter_congr fun r _ => ?_))
          simp [DFunLike.coe_fn_eq])
        (fun p hp k hk => by
          obtain ⟨q, hq, rfl⟩ := mem_map.1 hp
          have hqk : q.1 k ≠ q.2 k := hk
          refine (le_of_eq ?_).trans (card_permInvPermRel_diff_mul_le hdisj hq hqk)
          congr 1 <;>
            · rw [filter_map, card_map]
              refine congrArg card (filter_congr fun r _ => ?_)
              simp [DFunLike.coe_fn_eq])
      have hprod : ((#I₁ : ℝ) * (#I₀ : ℝ)) =
          ((min #I₀ #I₁ : ℕ) : ℝ) * ((max #I₀ #I₁ : ℕ) : ℝ) := by
        norm_cast
        rw [mul_comm, min_mul_max]
      have hmax_pos : (0 : ℝ) < √(max #I₀ #I₁ : ℕ) :=
        Real.sqrt_pos.2 (Nat.cast_pos.2 (lt_of_lt_of_le (card_pos.2 hne₀) (Nat.le_max_left _ _)))
      rw [hprod, Real.sqrt_mul (Nat.cast_nonneg _), ← mul_assoc] at hadv
      exact le_of_mul_le_mul_right hadv hmax_pos
    · rw [not_nonempty_iff_eq_empty.1 hne₁]
      simp
  · rw [not_nonempty_iff_eq_empty.1 hne₀]
    simp

/-- **Partition-form bounded-error bound for permutation inversion**: if a `T`-query value-query
algorithm outputs `π.symm target` via `out` with probability at least `1 - ε` (`2 * ε ≤ 1`) on
every `π ∈ permInvLeft I₀ target` and `σ ∈ permInvRight I₁ target` (`Disjoint I₀ I₁`), then
`(1 - 2√(ε(1-ε))) √(min #I₀ #I₁) ≤ 2 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_min_le_of_permInversion_partition {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) {I₀ I₁ : Finset ι} (hdisj : Disjoint I₀ I₁) (target : ι) {ε : ℝ}
    (h₀ : ∀ π ∈ permInvLeft I₀ target,
      1 - ε ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target})
    (h₁ : ∀ σ ∈ permInvRight I₁ target,
      1 - ε ≤ measureProb (runValue step U ψ₀ ⇑σ T) {q | out q = σ.symm target})
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(min #I₀ #I₁ : ℕ) ≤ 2 * T :=
  one_sub_mul_sqrt_min_le_of_permInversion_partition step U hψ₀ T hdisj target fun p hp => by
    obtain ⟨hp₀, hp₁, -⟩ := mem_permInvPermRel.1 hp
    exact norm_inner_le_two_mul_sqrt_of_readout_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out (permInvPermRel_symm_ne hdisj hp)
      (h₀ p.1 (mem_filter.2 ⟨mem_univ _, hp₀⟩))
      (h₁ p.2 (mem_filter.2 ⟨mem_univ _, hp₁⟩)) hε

/-- **Permutation inversion overlap bound** ([Ambainis2002], Theorem 7, overlap form): if on every
pair of permutations `π, σ : Equiv.Perm ι` with `π.symm target ≠ σ.symm target`, a `T`-query
value-query algorithm ends with state overlap at most `δ`, then `(1 - δ) √⌊|ι| / 2⌋ ≤ 2 T`. -/
theorem one_sub_mul_sqrt_div_two_le_of_permInversion {ι V W : Type*}
    [Fintype ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (target : ι) {δ : ℝ}
    (hδ : ∀ π σ : Equiv.Perm ι, π.symm target ≠ σ.symm target →
      ‖inner ℂ (runValue step U ψ₀ ⇑π T) (runValue step U ψ₀ ⇑σ T)‖ ≤ δ) :
    (1 - δ) * √(Fintype.card ι / 2 : ℕ) ≤ 2 * T := by
  classical
  set n := Fintype.card ι
  by_cases hn : 2 ≤ n
  · let e : ι ≃ Fin n := Fintype.equivFin ι
    let F₀ : Finset (Fin n) :=
      (Finset.range (n / 2)).attach.map
        ⟨fun ⟨k, hk⟩ => ⟨k, by have := mem_range.1 hk; omega⟩,
          fun ⟨a, _⟩ ⟨b, _⟩ h => by injection h with hab; ext; exact hab⟩
    let I₀ : Finset ι := F₀.map e.symm.toEmbedding
    let I₁ : Finset ι := I₀ᶜ
    have hI₀ : #I₀ = n / 2 := by simp [I₀, F₀]
    have hI₁ : #I₁ = n - n / 2 := by dsimp only [I₁]; rw [card_compl, hI₀]
    have hmin : min #I₀ #I₁ = n / 2 := by rw [hI₀, hI₁]; omega
    rw [← hmin]
    exact one_sub_mul_sqrt_min_le_of_permInversion_partition step U hψ₀ T
      disjoint_compl_right target fun p hp =>
        hδ p.1 p.2 (permInvPermRel_symm_ne disjoint_compl_right hp)
  · have hzero : n / 2 = 0 := by omega
    rw [hzero]
    simp

/-- **Ambainis's quantum query lower bound for inverting a permutation** ([Ambainis2002],
Section 6.2, Theorem 7): any `T`-query value-query algorithm that outputs `π.symm target` via `out`
with probability at least `1 - ε` (`2 * ε ≤ 1`) on every permutation `π : Equiv.Perm ι` satisfies
`(1 - 2√(ε(1-ε))) √⌊|ι| / 2⌋ ≤ 2 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι) {ε : ℝ}
    (hcorr : ∀ π : Equiv.Perm ι,
      1 - ε ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target})
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(Fintype.card ι / 2 : ℕ) ≤ 2 * T :=
  one_sub_mul_sqrt_div_two_le_of_permInversion step U hψ₀ T target fun π σ hne =>
    norm_inner_le_two_mul_sqrt_of_readout_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out hne (hcorr π) (hcorr σ) hε

/-- `PMF` (`measureOut`) form of `one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion`, not
requiring `[DecidableEq ι]`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion_measureOut {ι V W : Type*}
    [Fintype ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι) {ε : ℝ}
    (hcorr : ∀ π : Equiv.Perm ι,
      ENNReal.ofReal (1 - ε) ≤
        measureOut (runValue step U ψ₀ ⇑π T) (by rw [norm_runValue, hψ₀]) out (π.symm target))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(Fintype.card ι / 2 : ℕ) ≤ 2 * T :=
  one_sub_mul_sqrt_div_two_le_of_permInversion step U hψ₀ T target fun π σ hne =>
    norm_inner_le_two_mul_sqrt_of_measureOut_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out hne (hcorr π) (hcorr σ) hε

private theorem scale_sqrt_perm_bound {a b : ℕ} {c ε : ℝ} {T : ℕ}
    (hc : 0 ≤ c) (hle : (a : ℝ) ≤ c * (b : ℝ))
    (hbase : (1 - 2 * √(ε * (1 - ε))) * √(b : ℕ) ≤ 2 * T) :
    (1 - 2 * √(ε * (1 - ε))) * √(a : ℝ) ≤ 2 * √c * T := by
  have hsqrt : √(a : ℝ) ≤ √c * √(b : ℕ) :=
    (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_mul hc _)
  calc
    (1 - 2 * √(ε * (1 - ε))) * √(a : ℝ)
        ≤ (1 - 2 * √(ε * (1 - ε))) * (√c * √(b : ℕ)) :=
          mul_le_mul_of_nonneg_left hsqrt (one_sub_two_mul_sqrt_nonneg ε)
    _ = √c * ((1 - 2 * √(ε * (1 - ε))) * √(b : ℕ)) := by ring
    _ ≤ √c * (2 * T) := mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _)
    _ = 2 * √c * T := by ring

/-- Sharp `√(|ι| - 1)` form of Theorem 7 valid for every finite type `ι` (including `|ι| = 1`, where
`0` queries invert the unique permutation): `(1 - 2√(ε(1-ε))) √(|ι| - 1) ≤ 2 √2 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι) {ε : ℝ}
    (hcorr : ∀ π : Equiv.Perm ι,
      1 - ε ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target})
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(Fintype.card ι - 1 : ℕ) ≤ 2 * √2 * T :=
  scale_sqrt_perm_bound (by positivity)
    (by exact_mod_cast (by omega : Fintype.card ι - 1 ≤ 2 * (Fintype.card ι / 2)))
    (one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion step U hψ₀ T out target hcorr hε)

/-- `√|ι|` form of Theorem 7 for `2 ≤ |ι|`: `(1 - 2√(ε(1-ε))) √|ι| ≤ 2 √3 T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (hcard : 2 ≤ Fintype.card ι)
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι) {ε : ℝ}
    (hcorr : ∀ π : Equiv.Perm ι,
      1 - ε ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target})
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(Fintype.card ι : ℝ) ≤ 2 * √3 * T :=
  scale_sqrt_perm_bound (by positivity)
    (by exact_mod_cast (by omega : Fintype.card ι ≤ 3 * (Fintype.card ι / 2)))
    (one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion step U hψ₀ T out target hcorr hε)

/-- **Bounded-error (`ε = 1 / 3`) floor-half corollary**: `|ι| / 2 ≤ 1296 T²` for every finite type
`ι`. -/
theorem permInversion_div_two_lower_bound {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι)
    (hcorr : ∀ π : Equiv.Perm ι,
      2 / 3 ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target}) :
    Fintype.card ι / 2 ≤ 1296 * T ^ 2 := by
  have hbase := one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion
    step U hψ₀ T out target (ε := 1 / 3)
    (fun π => by linarith [hcorr π]) (by norm_num)
  have hlin : √(Fintype.card ι / 2 : ℕ) ≤ 36 * (T : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right one_eighteenth_le_one_sub_two_mul_sqrt
      (Real.sqrt_nonneg (Fintype.card ι / 2 : ℕ))
    linarith
  have hsq : ((Fintype.card ι / 2 : ℕ) : ℝ) ≤ ((1296 * T ^ 2 : ℕ) : ℝ) := by
    calc
      ((Fintype.card ι / 2 : ℕ) : ℝ)
          = √(Fintype.card ι / 2 : ℕ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
      _ ≤ (36 * (T : ℝ)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hlin 2
      _ = ((1296 * T ^ 2 : ℕ) : ℝ) := by push_cast; ring
  exact Nat.cast_le.1 hsq

/-- **Bounded-error (`ε = 1 / 3`) permutation-inversion lower bound** ([Ambainis2002], Theorem 7):
for `2 ≤ |ι|`, any `T`-query value-query algorithm that outputs `π.symm target` with probability at
least `2 / 3` on every `π : Equiv.Perm ι` satisfies `|ι| ≤ 3888 T²` (in particular `1 ≤ T`). -/
theorem permInversion_lower_bound {ι V W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]
    (hcard : 2 ≤ Fintype.card ι)
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι)
    (hcorr : ∀ π : Equiv.Perm ι,
      2 / 3 ≤ measureProb (runValue step U ψ₀ ⇑π T) {q | out q = π.symm target}) :
    Fintype.card ι ≤ 3888 * T ^ 2 := by
  have h := permInversion_div_two_lower_bound step U hψ₀ T out target hcorr
  omega

/-- `PMF` (`measureOut`) form of `permInversion_lower_bound`, not requiring `[DecidableEq ι]`. -/
theorem permInversion_measureOut_lower_bound {ι V W : Type*}
    [Fintype ι] [Fintype V] [Fintype W]
    (hcard : 2 ≤ Fintype.card ι)
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → ι) (target : ι)
    (hcorr : ∀ π : Equiv.Perm ι,
      ENNReal.ofReal (2 / 3) ≤
        measureOut (runValue step U ψ₀ ⇑π T) (by rw [norm_runValue, hψ₀]) out (π.symm target)) :
    Fintype.card ι ≤ 3888 * T ^ 2 := by
  classical
  exact permInversion_lower_bound hcard step U hψ₀ T out target fun π =>
    le_measureProb_of_le_measureOut_apply _ (by rw [norm_runValue, hψ₀]) out (π.symm target)
      (hcorr π)

end QuantumLowerBounds

end Cslib.Quantum
