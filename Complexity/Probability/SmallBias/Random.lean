/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.SmallBias
import Complexity.Foundations.Combinatorics.Hoeffding

/-!
# Short `ε`-biased lists exist

A list `s₁, …, s_d` of bit strings in `ι → Bool` is `ε`-biased when the uniform distribution over
the list is `ε`-biased (`Cslib.BitString.IsSmallBias`): for every nonempty set `S` of coordinates,
`|Σⱼ χ_S(sⱼ)| ≤ ε d`. If `ε ≥ 0`, `d ≥ 1` and `2 · 2^|ι| · exp(-ε² d / 2) < 1`, such a list exists
(`Cslib.BitString.exists_isSmallBias_map_of_exp_lt`). Unlike the explicit powering construction
(`Cslib.BitString.exists_isSmallBias_uniformOfFintype_map`), whose lists have length a power of
four, this gives every length `d` for which the bound holds, as [OpenAI2026ETH] needs for its
prescribed number of shifts.

The proof is the probabilistic method in counting form. For a fixed nonempty `S` the parities on
`S` of the `d` strings are `d` independent unbiased bits: a shear of the cube (`shear`), adding to
one coordinate `i₀ ∈ S` of each string the parity on `S \ {i₀}`, turns them into `d` coordinates of
a uniformly random bit string. Hoeffding's inequality
(`Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`) then bounds the number of lists
biased at `S` by a `2 exp(-ε² d / 2)` fraction (`Cslib.BitString.card_biased_le`), and a union bound
over the fewer than `2^|ι|` nonempty sets leaves an `ε`-biased list. This is the existence argument
for the `ε`-biased shifts in [OpenAI2026ETH, proof of Lemma 6.1, (6.2)]; such lists are the
generators of small-bias Cayley graphs [Naor and Naor][NaorNaor1993].

## Main results

* `Cslib.BitString.sum_chi_eq`: the sum of a character over a list counts the odd parities.
* `Cslib.BitString.card_biased_le`: few lists are biased at a fixed nonempty set.
* `Cslib.BitString.exists_isSmallBias_map_of_exp_lt`: short `ε`-biased lists exist.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1
* [J. Naor, M. Naor, *Small-bias probability spaces*][NaorNaor1993]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Real Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The sum of the character of `S` over a list is `d` minus twice the number of strings of the
list with odd parity on `S`. -/
theorem sum_chi_eq (S : Finset ι) (s : Fin d → ι → Bool) :
    ∑ j, chi ℝ S (s j) = d - 2 * #{j | parityOn S (s j) = true} := by
  have h : ∀ j, chi ℝ S (s j) = 1 - 2 * (if parityOn S (s j) = true then 1 else 0) := by
    intro j
    rw [chi_eq_neg_one_pow_parityOn]
    cases parityOn S (s j) <;> norm_num
  simp only [h, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum, card_filter]
  push_cast
  ring

/-- The shear of a list, flattened to a bit string on `Fin d × ι`, that replaces coordinate `i₀`
of each string by its parity on `S`. -/
private def shear (S : Finset ι) (i₀ : ι) (x : Fin d × ι → Bool) : Fin d × ι → Bool :=
  fun k => if k.2 = i₀ then parityOn S (fun i => x (k.1, i)) else x k

omit [Fintype ι] in
private theorem shear_apply_self (S : Finset ι) (i₀ : ι) (x : Fin d × ι → Bool) (j : Fin d) :
    shear S i₀ x (j, i₀) = parityOn S (fun i => x (j, i)) := by
  simp [shear]

omit [Fintype ι] in
private theorem shear_apply_of_ne (S : Finset ι) {i₀ i : ι} (h : i ≠ i₀) (x : Fin d × ι → Bool)
    (j : Fin d) : shear S i₀ x (j, i) = x (j, i) := by
  simp [shear, h]

omit [Fintype ι] in
/-- For `i₀ ∈ S` the shear is an involution. -/
private theorem shear_shear {S : Finset ι} {i₀ : ι} (hi : i₀ ∈ S) (x : Fin d × ι → Bool) :
    shear S i₀ (shear S i₀ x) = x := by
  funext ⟨j, i⟩
  by_cases h : i = i₀
  · subst h
    rw [shear_apply_self, parityOn_eq_xor_erase hi,
      parityOn_congr (y := fun i' => x (j, i')) fun i' hi' => shear_apply_of_ne S
        (ne_of_mem_erase hi') x j, shear_apply_self, parityOn_eq_xor_erase hi]
    cases x (j, i) <;> cases parityOn (S.erase i) (fun i' => x (j, i')) <;> rfl
  · exact (shear_apply_of_ne S h _ j).trans (shear_apply_of_ne S h x j)

/-- **Few lists are biased at a fixed nonempty set**: at most a `2 exp(-ε² d / 2)` fraction of the
lists of `d` bit strings have `|Σⱼ χ_S(sⱼ)| ≥ ε d`. -/
theorem card_biased_le {S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (#{s : Fin d → ι → Bool | ε * d ≤ |∑ j, chi ℝ S (s j)|} : ℝ) ≤
      2 * 2 ^ (d * Fintype.card ι) * exp (-(ε ^ 2 * d / 2)) := by
  obtain ⟨i₀, hi₀⟩ := hS
  set R : Finset (Fin d × ι) := univ ×ˢ {i₀}
  have hR : #R = d := by simp [R]
  have hcount : ∀ s : Fin d → ι → Bool, #{j | parityOn S (s j) = true} =
      #{k ∈ R | shear S i₀ (Function.uncurry s) k = true} := fun s => by
    refine Finset.card_bij (fun j _ => (j, i₀)) (fun j hj => ?_) (fun _ _ _ _ h => ?_)
      (fun k hk => ?_)
    · simp only [mem_filter, mem_univ, true_and] at hj
      simp [R, shear_apply_self, hj, Function.uncurry]
    · simpa using h
    · obtain ⟨j, i⟩ := k
      simp only [R, mem_filter, mem_product, mem_univ, mem_singleton, true_and] at hk
      obtain ⟨rfl, hk⟩ := hk
      refine ⟨j, ?_, rfl⟩
      simpa [shear_apply_self, Function.uncurry] using hk
  set e : (Fin d → ι → Bool) ≃ (Fin d × ι → Bool) :=
    (Equiv.curry (Fin d) ι Bool).symm.trans
      ⟨shear S i₀, shear S i₀, shear_shear hi₀, shear_shear hi₀⟩
  set t : ℝ := ε * d / 2
  have hcard : #{s : Fin d → ι → Bool | ε * d ≤ |∑ j, chi ℝ S (s j)|} =
      #{x : Fin d × ι → Bool | t ≤ |(#{k ∈ R | x k = true} : ℝ) - #R / 2|} := by
    refine Finset.card_equiv e fun s => ?_
    simp only [mem_filter, mem_univ, true_and, sum_chi_eq, hR, hcount]
    change _ ↔ t ≤ |(#{k ∈ R | shear S i₀ (Function.uncurry s) k = true} : ℝ) - d / 2|
    rw [show (d : ℝ) - 2 * (#{k ∈ R | shear S i₀ (Function.uncurry s) k = true} : ℝ) =
      -2 * ((#{k ∈ R | shear S i₀ (Function.uncurry s) k = true} : ℝ) - d / 2) by ring,
      abs_mul, abs_neg, abs_two]
    constructor <;> intro h <;> simp only [t] at * <;> linarith
  rw [hcard]
  refine (card_filter_le_abs_card_filter_sub_half_le R (by positivity)).trans (le_of_eq ?_)
  rw [Fintype.card_prod, Fintype.card_fin, hR]
  congr 2
  rcases Nat.eq_zero_or_pos d with hd | hd
  · simp [t, hd]
  · have : (d : ℝ) ≠ 0 := by positivity
    simp only [t]
    field_simp

/-- **Short `ε`-biased lists exist**: if `ε ≥ 0` and `2 · 2^|ι| · exp(-ε² d / 2) < 1`, some list
of `d ≥ 1` bit strings has, at every nonempty set `S`, `|Σⱼ χ_S(sⱼ)| < ε d`; so the uniform
distribution over it is `ε`-biased. -/
theorem exists_isSmallBias_map_of_exp_lt [NeZero d] {ε : ℝ} (hε : 0 ≤ ε)
    (h : 2 * 2 ^ Fintype.card ι * exp (-(ε ^ 2 * d / 2)) < 1) :
    ∃ s : Fin d → ι → Bool, IsSmallBias ε ((uniformOfFintype (Fin d)).map s) := by
  -- a list unbiased at every nonempty set
  obtain ⟨s, hs⟩ : ∃ s : Fin d → ι → Bool, ∀ S : Finset ι, S.Nonempty →
      |∑ j, chi ℝ S (s j)| < ε * d := by
    by_contra hne
    simp only [not_exists, not_forall, not_lt, exists_prop] at hne
    have hcover : (univ : Finset (Fin d → ι → Bool)) ⊆
        (univ.filter fun S : Finset ι => S.Nonempty).biUnion
          fun S => {s : Fin d → ι → Bool | ε * d ≤ |∑ j, chi ℝ S (s j)|} := by
      intro s _
      obtain ⟨S, hS, hle⟩ := hne s
      simp only [mem_biUnion, mem_filter, mem_univ, true_and]
      exact ⟨S, hS, hle⟩
    have h3 : ((univ : Finset (Fin d → ι → Bool)).card : ℝ) ≤
        ∑ S ∈ univ.filter fun S : Finset ι => S.Nonempty,
          (#{s : Fin d → ι → Bool | ε * d ≤ |∑ j, chi ℝ S (s j)|} : ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    have h4 : ∑ S ∈ univ.filter fun S : Finset ι => S.Nonempty,
          (#{s : Fin d → ι → Bool | ε * d ≤ |∑ j, chi ℝ S (s j)|} : ℝ) ≤
        2 ^ Fintype.card ι * (2 * 2 ^ (d * Fintype.card ι) * exp (-(ε ^ 2 * d / 2))) := by
      refine (sum_le_sum fun S hS => card_biased_le (mem_filter.mp hS).2 hε).trans ?_
      rw [sum_const, nsmul_eq_mul]
      gcongr
      calc ((univ.filter fun S : Finset ι => S.Nonempty).card : ℝ)
          ≤ (univ : Finset (Finset ι)).card := by exact_mod_cast card_filter_le _ _
        _ = 2 ^ Fintype.card ι := by simp
    rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h3
    have h5 : ((2 : ℝ) ^ Fintype.card ι) ^ d = 2 ^ (d * Fintype.card ι) := by
      rw [← pow_mul, mul_comm]
    push_cast at h3
    rw [h5] at h3
    have hpos : (0 : ℝ) < 2 ^ (d * Fintype.card ι) := by positivity
    nlinarith
  refine ⟨s, fun S hS => ?_⟩
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card, Fintype.card_fin, abs_div,
    abs_of_pos hd, div_le_iff₀ hd]
  exact (hs S hS).le

end Cslib.BitString
