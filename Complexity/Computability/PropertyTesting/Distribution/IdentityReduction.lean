/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PropertyTesting.Distribution.UniformityCollision
import Complexity.Probability.PMF

/-!
# Identity testing by reduction to uniformity

Testing identity to a fixed distribution `q` on a finite type of size `n` reduces to testing
uniformity on `4 n` points, with the same number of samples and a third of the proximity. This is
Goldreich's theorem that the uniform distribution is complete for testing identity
[Goldreich][Goldreich2016UniformComplete].

The reduction passes each sample through a randomized map, Goldreich's kernel
(`identityKernel q`). The kernel first replaces the sample by a uniform draw with probability
`1 / 2`. This lifts every mass of the target to at least `1 / (2 n)`. It then spreads the result
over a domain of `4 n` cells (`IdentityDomain q`):
- an element `a` owns a block of `⌊2 n q(a)⌋ + 2` cells (`identityBlock`);
- one leftover block of `2 n - ∑ a, ⌊2 n q(a)⌋` cells absorbs the rounding.

The kernel sends `q` exactly to the uniform distribution on these cells
(`bind_identityKernel_self`). It shrinks statistical distance by at most a factor `3`
(`dist_le_three_mul_dist_bind_identityKernel`), because each block size is at least two thirds of
`2 n` times the mixed mass. Hence a uniformity tester with proximity `ε / 3` on the cells, run on
the mapped samples, tests identity to `q` with proximity `ε` (`isTester_identity_of_uniform`).

With the collision tester this gives an explicit identity tester (`identityTester`) whenever
`720 √n ≤ (k - 1) ε²` (`isTester_identityTester`), so `k = O(√n / ε²)` samples suffice for every
fixed `q`. The block structure follows Goldreich's construction. The grain `1 / (4 n)` and the
constants `3` and `720` are the ones this proof gives; they are not taken from the source.

## Main definitions

* `Cslib.DistributionTesting.identityGrain`, `identityBlock`: the block sizes.
* `Cslib.DistributionTesting.IdentityDomain`: the `4 n` cells.
* `Cslib.DistributionTesting.identityKernel`: Goldreich's kernel.
* `Cslib.DistributionTesting.identityTester`: the collision tester run through the kernel.

## Main results

* `Cslib.DistributionTesting.card_identityDomain`: there are `4 n` cells.
* `Cslib.DistributionTesting.bind_identityKernel_self`: the kernel maps `q` to uniform.
* `Cslib.DistributionTesting.dist_le_three_mul_dist_bind_identityKernel`: distances shrink by at
  most a factor `3`.
* `Cslib.DistributionTesting.isTester_identity_of_uniform`,
  `exists_isTester_identity_of_uniform`: uniformity testing on `4 n` points gives identity testing
  with the same sample size.
* `Cslib.DistributionTesting.isTester_identityTester`: identity testing with `k = O(√n / ε²)`.

## References

* [O. Goldreich, *The uniform distribution is complete with respect to testing identity to a fixed
  distribution*][Goldreich2016UniformComplete]
* [C. L. Canonne, *A Survey on Distribution Testing: Your Data is Big. But is it
  Blue?*][Canonne2020]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

variable {α : Type*} [Fintype α] (q : PMF α)

/-- The grain of `a`: `⌊2 n q(a)⌋`, where `n` is the size of the domain. Element `a` owns
`identityGrain q a + 2` cells. -/
noncomputable def identityGrain (a : α) : ℕ :=
  ⌊2 * (Fintype.card α : ℝ) * (q a).toReal⌋₊

/-- The block sizes of Goldreich's kernel: `⌊2 n q(a)⌋ + 2` cells for each element `a` and
`2 n - ∑ a, ⌊2 n q(a)⌋` leftover cells. -/
noncomputable def identityBlock : Option α → ℕ
  | some a => identityGrain q a + 2
  | none => 2 * Fintype.card α - ∑ a, identityGrain q a

theorem identityBlock_some (a : α) : identityBlock q (some a) = identityGrain q a + 2 := by
  rw [identityBlock]

theorem identityBlock_none :
    identityBlock q none = 2 * Fintype.card α - ∑ a, identityGrain q a := by
  rw [identityBlock]

/-- The grains sum to at most `2 n`. -/
theorem sum_identityGrain_le : ∑ a, identityGrain q a ≤ 2 * Fintype.card α := by
  have h : (∑ a, identityGrain q a : ℝ) ≤ 2 * Fintype.card α :=
    calc ∑ a, (identityGrain q a : ℝ) ≤ ∑ a, 2 * (Fintype.card α : ℝ) * (q a).toReal :=
          sum_le_sum fun a _ => Nat.floor_le (by positivity)
      _ = 2 * Fintype.card α := by rw [← mul_sum, sum_toReal, mul_one]
  exact_mod_cast h

/-- The cells of Goldreich's kernel: a block of `identityBlock q (some a)` cells for each element
`a` and a leftover block of `identityBlock q none` cells. -/
abbrev IdentityDomain := Σ o : Option α, Fin (identityBlock q o)

instance : Nonempty (IdentityDomain q) := by
  obtain ⟨a, -⟩ := q.support_nonempty
  exact ⟨⟨some a, ⟨0, by rw [identityBlock_some]; omega⟩⟩⟩

/-- There are `4 n` cells. -/
theorem card_identityDomain : Fintype.card (IdentityDomain q) = 4 * Fintype.card α := by
  rw [Fintype.card_sigma, Fintype.sum_option]
  simp only [Fintype.card_fin]
  simp only [identityBlock, sum_add_distrib, sum_const, card_univ, smul_eq_mul]
  have := sum_identityGrain_le q
  omega

/-- The rounding error `2 n q(a) - ⌊2 n q(a)⌋ ∈ [0, 1)`. -/
private noncomputable def identityRemainder (a : α) : ℝ :=
  2 * (Fintype.card α : ℝ) * (q a).toReal - identityGrain q a

private theorem identityRemainder_nonneg (a : α) : 0 ≤ identityRemainder q a :=
  sub_nonneg.mpr (Nat.floor_le (by positivity))

private theorem sum_identityRemainder : ∑ a, identityRemainder q a = identityBlock q none := by
  rw [identityBlock_none, Nat.cast_sub (sum_identityGrain_le q)]
  simp only [identityRemainder]
  push_cast
  rw [sum_sub_distrib, ← mul_sum, sum_toReal, mul_one]

private theorem identityScale_pos (a : α) : 0 < 2 * (Fintype.card α : ℝ) * (q a).toReal + 2 := by
  positivity

variable [DecidableEq α]

/-- The probability `1 / 2 [a = y] + 1 / (2 n)` that the mixing step turns the sample `y` into
`a`. -/
private noncomputable def identityMix (y a : α) : ℝ :=
  (if a = y then 1 / 2 else 0) + 1 / (2 * Fintype.card α)

private theorem identityMix_nonneg (y a : α) : 0 ≤ identityMix y a := by
  unfold identityMix
  split_ifs <;> positivity

private theorem sum_identityMix (y : α) : ∑ b, identityMix y b = 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    have : Nonempty α := ⟨y⟩
    exact_mod_cast Fintype.card_ne_zero
  simp only [identityMix, sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
    nsmul_eq_mul]
  field_simp
  ring

private theorem sum_mul_identityMix (p : PMF α) (b : α) :
    ∑ y, (p y).toReal * identityMix y b = (p b).toReal / 2 + 1 / (2 * Fintype.card α) := by
  simp only [identityMix, mul_add, sum_add_distrib, ← sum_mul, sum_toReal, one_mul, mul_ite,
    mul_zero]
  rw [sum_ite_eq, ite_eq_left_iff.mpr fun h => absurd (mem_univ b) h]
  ring

/-- The probability that Goldreich's kernel sends the sample `y` to a given cell. After mixing,
`a` goes to each of its own cells with probability `1 / (2 n q(a) + 2)`, and its remaining
probability is spread evenly over the leftover cells. -/
private noncomputable def identityWeight (y : α) : IdentityDomain q → ℝ
  | ⟨some b, _⟩ => identityMix y b / (2 * Fintype.card α * (q b).toReal + 2)
  | ⟨none, _⟩ => (∑ b, identityMix y b * identityRemainder q b /
      (2 * Fintype.card α * (q b).toReal + 2)) / identityBlock q none

private theorem identityWeight_nonneg (y : α) (x : IdentityDomain q) :
    0 ≤ identityWeight q y x := by
  obtain ⟨_ | b, j⟩ := x
  · exact div_nonneg (sum_nonneg fun b _ =>
      div_nonneg (mul_nonneg (identityMix_nonneg y b) (identityRemainder_nonneg q b))
        (identityScale_pos q b).le) (Nat.cast_nonneg _)
  · exact div_nonneg (identityMix_nonneg y b) (identityScale_pos q b).le

private theorem sum_identityWeight (y : α) : ∑ x, identityWeight q y x = 1 := by
  rw [Fintype.sum_sigma, Fintype.sum_option]
  simp only [identityWeight, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_of_imp' (fun h => ?_), ← sum_add_distrib, ← sum_identityMix y]
  · refine sum_congr rfl fun b _ => ?_
    have hR := (identityScale_pos q b).ne'
    rw [identityBlock_some]
    simp only [identityRemainder]
    push_cast
    field_simp
    ring
  · have h0 : ∑ b, identityRemainder q b = 0 := by rw [sum_identityRemainder, h]
    rw [sum_eq_zero_iff_of_nonneg fun b _ => identityRemainder_nonneg q b] at h0
    exact sum_eq_zero fun b hb => by rw [h0 b hb, mul_zero, zero_div]

/-- **Goldreich's kernel** for identity testing to `q`. It keeps the sample with probability
`1 / 2` and replaces it by a uniform draw otherwise. An element `a` then goes to a uniformly random
cell of its own block with probability `(⌊2 n q(a)⌋ + 2) / (2 n q(a) + 2)`, and to a uniformly
random leftover cell otherwise. -/
noncomputable def identityKernel (y : α) : PMF (IdentityDomain q) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (identityWeight q y x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => identityWeight_nonneg q y x,
      sum_identityWeight, ENNReal.ofReal_one])

private theorem identityKernel_apply_toReal (y : α) (x : IdentityDomain q) :
    (identityKernel q y x).toReal = identityWeight q y x := by
  rw [identityKernel, PMF.ofFintype_apply, ENNReal.toReal_ofReal (identityWeight_nonneg q y x)]

/-- Through Goldreich's kernel, `p` gives each cell of the block of `b` the probability
`(p(b) / 2 + 1 / (2 n)) / (2 n q(b) + 2)`. -/
theorem bind_identityKernel_some (p : PMF α) (b : α) (j : Fin (identityBlock q (some b))) :
    (p.bind (identityKernel q) ⟨some b, j⟩).toReal =
      ((p b).toReal / 2 + 1 / (2 * Fintype.card α)) /
        (2 * Fintype.card α * (q b).toReal + 2) := by
  rw [bind_apply_toReal]
  simp only [identityKernel_apply_toReal, identityWeight, mul_div_assoc', ← sum_div,
    sum_mul_identityMix]

private theorem bind_identityKernel_none (p : PMF α) (j : Fin (identityBlock q none)) :
    (p.bind (identityKernel q) ⟨none, j⟩).toReal =
      (∑ b, ((p b).toReal / 2 + 1 / (2 * Fintype.card α)) * identityRemainder q b /
        (2 * Fintype.card α * (q b).toReal + 2)) / identityBlock q none := by
  rw [bind_apply_toReal]
  simp only [identityKernel_apply_toReal, identityWeight, mul_div_assoc', ← sum_div, mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul_identityMix p b, sum_mul, sum_div]
  refine sum_congr rfl fun y _ => ?_
  ring

/-- **Completeness of the reduction**: Goldreich's kernel maps `q` to the uniform distribution on
the cells. -/
theorem bind_identityKernel_self :
    q.bind (identityKernel q) = uniformOfFintype (IdentityDomain q) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    obtain ⟨a, -⟩ := q.support_nonempty
    have : Nonempty α := ⟨a⟩
    exact_mod_cast Fintype.card_ne_zero
  ext x
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, card_identityDomain]
  push_cast
  obtain ⟨_ | b, j⟩ := x
  · have hL : (identityBlock q none : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.pos.ne'
    rw [bind_identityKernel_none]
    have h (b : α) : ((q b).toReal / 2 + 1 / (2 * Fintype.card α)) * identityRemainder q b /
        (2 * Fintype.card α * (q b).toReal + 2) =
          identityRemainder q b / (4 * Fintype.card α) := by
      have hR := (identityScale_pos q b).ne'
      field_simp
      ring
    simp only [h]
    rw [← sum_div, sum_identityRemainder]
    field_simp
  · rw [bind_identityKernel_some]
    have hR := (identityScale_pos q b).ne'
    field_simp
    ring

/-- **Soundness of the reduction**: Goldreich's kernel shrinks the statistical distance from `q` by
at most a factor `3`. -/
theorem dist_le_three_mul_dist_bind_identityKernel (p : PMF α) :
    dist p q ≤ 3 * dist (p.bind (identityKernel q)) (q.bind (identityKernel q)) := by
  rw [dist_eq, dist_eq, Fintype.sum_sigma, Fintype.sum_option]
  have hnone : 0 ≤ ∑ j : Fin (identityBlock q none),
      |(p.bind (identityKernel q) ⟨none, j⟩).toReal -
        (q.bind (identityKernel q) ⟨none, j⟩).toReal| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hsome : ∑ b, |(p b).toReal - (q b).toReal| ≤
      3 * ∑ b, ∑ j : Fin (identityBlock q (some b)),
        |(p.bind (identityKernel q) ⟨some b, j⟩).toReal -
          (q.bind (identityKernel q) ⟨some b, j⟩).toReal| := by
    rw [mul_sum]
    refine sum_le_sum fun b _ => ?_
    simp only [bind_identityKernel_some, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hR := identityScale_pos q b
    have hG : 2 * (2 * Fintype.card α * (q b).toReal + 2) ≤
        3 * (identityBlock q (some b) : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * (Fintype.card α : ℝ) * (q b).toReal)
      rw [identityBlock_some]
      push_cast
      have : (0 : ℝ) ≤ identityGrain q b := Nat.cast_nonneg _
      unfold identityGrain at this ⊢
      linarith
    have he : ((p b).toReal / 2 + 1 / (2 * Fintype.card α)) /
          (2 * Fintype.card α * (q b).toReal + 2) -
        ((q b).toReal / 2 + 1 / (2 * Fintype.card α)) / (2 * Fintype.card α * (q b).toReal + 2) =
          ((p b).toReal - (q b).toReal) / (2 * (2 * Fintype.card α * (q b).toReal + 2)) := by
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (by positivity :
      (0 : ℝ) < 2 * (2 * Fintype.card α * (q b).toReal + 2))]
    rw [show 3 * ((identityBlock q (some b) : ℝ) * (|(p b).toReal - (q b).toReal| /
        (2 * (2 * Fintype.card α * (q b).toReal + 2)))) =
          |(p b).toReal - (q b).toReal| * (3 * identityBlock q (some b)) /
            (2 * (2 * Fintype.card α * (q b).toReal + 2)) by ring]
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hG (abs_nonneg _)
  linarith

/-- **The uniform distribution is complete for identity testing**
[Goldreich][Goldreich2016UniformComplete]: a `k`-sample uniformity tester on the `4 n` cells with
proximity `ε / 3`, run on samples passed through Goldreich's kernel, is a `k`-sample tester for
identity to `q` with proximity `ε`. -/
theorem isTester_identity_of_uniform {k : ℕ} {T : (Fin k → IdentityDomain q) → PMF Bool} {ε : ℝ}
    (hT : IsTester T {uniformOfFintype (IdentityDomain q)} (ε / 3)) :
    IsTester (fun x => (pi fun i => identityKernel q (x i)).bind T) {q} ε := by
  refine hT.bind_pi (identityKernel q) (fun q' hq' => ?_) fun p hp q' hq' => ?_
  · rw [Set.mem_singleton_iff] at hq' ⊢
    rw [hq', bind_identityKernel_self]
  · rw [Set.mem_singleton_iff] at hq'
    rw [hq', ← bind_identityKernel_self]
    have h1 := hp q (Set.mem_singleton q)
    have h2 := dist_le_three_mul_dist_bind_identityKernel q p
    linarith

omit [DecidableEq α] in
/-- The reduction for uniformity testers on any domain of size `4 n`: a `k`-sample uniformity
tester with proximity `ε / 3` there yields a `k`-sample tester for identity to `q` with proximity
`ε`. -/
theorem exists_isTester_identity_of_uniform {β : Type*} [Fintype β] [Nonempty β]
    (hβ : Fintype.card β = 4 * Fintype.card α) {k : ℕ} {T : (Fin k → β) → PMF Bool} {ε : ℝ}
    (hT : IsTester T {uniformOfFintype β} (ε / 3)) :
    ∃ T' : (Fin k → α) → PMF Bool, IsTester T' {q} ε := by
  classical
  exact ⟨_, isTester_identity_of_uniform q
    (hT.comp_equiv_uniform (Fintype.equivOfCardEq (hβ.trans (card_identityDomain q).symm)))⟩

/-- The identity tester for `q`: the collision tester with proximity `ε / 3`, run on `k` samples
passed through Goldreich's kernel. -/
noncomputable def identityTester (k : ℕ) (ε : ℝ) : (Fin k → α) → PMF Bool :=
  fun x => (pi fun i => identityKernel q (x i)).bind
    (collisionTester (α := IdentityDomain q) k (ε / 3))

/-- **Identity testing with `O(√n / ε²)` samples**: for every fixed distribution `q` on a domain of
size `n`, `identityTester q k ε` tests identity to `q` with proximity `ε` whenever
`720 √n ≤ (k - 1) ε²`. -/
theorem isTester_identityTester {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 720 * Real.sqrt (Fintype.card α) ≤ (k - 1) * ε ^ 2) :
    IsTester (identityTester q k ε) {q} ε := by
  refine isTester_identity_of_uniform q (isTester_collisionTester (by positivity) ?_)
  rw [card_identityDomain, Nat.cast_mul, Real.sqrt_mul (by norm_num),
    show Real.sqrt ((4 : ℕ) : ℝ) = 2 by
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  nlinarith

end Cslib.DistributionTesting
