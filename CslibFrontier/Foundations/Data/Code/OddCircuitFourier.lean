/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.OddCircuit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp

/-!
# Counting odd circuits with Fourier analysis

For a finite set `B` of vectors over `𝔽₂` write `charSum B y = ∑_{x ∈ B} (-1) ^ (y ⬝ᵥ x)`
(`Cslib.Code.charSum`) for the unnormalized Fourier transform of its indicator; Saglam's
`μ̂(y)` is `charSum B y / |B|` [Saglam2027, Section 3.1]. Character orthogonality counts the
zero-sum tuples of elements of `B`:
`2 ^ n · #{t ∈ B ^ ℓ | ∑ t = 0} = ∑_y charSum B y ^ ℓ`
(`Cslib.Code.card_filter_sum_eq_zero_mul_two_pow`), and each `ℓ`-element zero-sum subset of `B`
gives `ℓ!` such tuples (`Cslib.Code.card_filter_sum_eq_zero_mul_factorial_le`).

Summing over odd sizes `ℓ ≥ 3` against the power series of `sinh` bounds the weighted number of
odd circuits by
`∑_S q ^ (-(|S| - 1)) ≤ (q / 2 ^ n) ∑_y s(charSum B y / q)`, `s(z) = sinh z - z`,
when `0 ∉ B` and `q > 0` (`Cslib.Code.sum_odd_circuit_le_sum_sinh_sub_self`). With `q = 2 ^ m` and
`τ = |B| / q` the right side is Saglam's `(V / τ) 𝔼_y s(τ μ̂(y))`, the bound on the expected number
`𝔼 Z` of odd circuits in a random kernel [Saglam2027, Sections 2 and 3.3]; the continuous-time
random walk of the paper is only a device for this identity and is not needed here.

The elementary estimates `s(z) ≤ 0` for `z ≤ 0`, `s(z) ≤ (sinh 1 - 1) z ^ 3` for `0 ≤ z ≤ 1` and
`s(z) ≤ e ^ z / 2` (`Cslib.Code.sinh_sub_self_le`) split this bound into a third-moment term and a
tail term (`Cslib.Code.sum_odd_circuit_le_moment_add_tail`). Combined with the odd-circuit argument
of `Cslib.Code.OddCircuit`, a linear code of distance `d` with `2 ^ (n - m - 1)` words exists as
soon as
`(V / τ) ((sinh 1 - 1) τ ^ 3 𝔼_y |μ̂ y| ^ 3 + (e ^ τ / 2) Pr_y[μ̂ y > 1 / τ]) < 1`
(`Cslib.Code.exists_le_minDist_parityCheckCode_of_moment_tail`). This is the reduction of
[Saglam2027, Section 3.3] to the Fourier estimates of its Lemma 3.1, which are not proved here.

## Main definitions

* `Cslib.Code.charSum`: the unnormalized Fourier transform of the indicator of a set of vectors.

## Main results

* `Cslib.Code.card_filter_sum_eq_zero_mul_two_pow`: zero-sum tuples by Fourier inversion.
* `Cslib.Code.card_filter_sum_eq_zero_mul_factorial_le`: zero-sum sets versus zero-sum tuples.
* `Cslib.Code.sum_odd_circuit_le_sum_sinh_sub_self`: the `sinh` bound on odd circuits.
* `Cslib.Code.sinh_sub_self_le`: the three-range estimate on `sinh z - z`.
* `Cslib.Code.sum_odd_circuit_le_moment_add_tail`: the moment and tail bound.
* `Cslib.Code.exists_le_minDist_parityCheckCode_of_moment_tail`: linear codes from the moment and
  tail estimates [Saglam2027, Section 3.3].

## References

* [M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*][Saglam2027], STOC 2027
  submission 1516, Sections 2–3.
-/

public section

namespace Cslib.Code

open Finset Matrix Real

section CharSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized Fourier transform `∑_{x ∈ B} (-1) ^ (y ⬝ᵥ x)` of the indicator of a finite set
`B` of vectors over `𝔽₂`, at `y`. Saglam's `μ̂(y)` [Saglam2027, Section 3] is `charSum B y / |B|`.
-/
@[expose] noncomputable def charSum (B : Finset (ι → ZMod 2)) (y : ι → ZMod 2) : ℝ :=
  ∑ x ∈ B, (-1 : ℝ) ^ (y ⬝ᵥ x).val

omit [Fintype ι] [DecidableEq ι] in
/-- The sign of a sum in `𝔽₂` is the product of the signs. -/
theorem neg_one_pow_val_sum {α : Type*} (s : Finset α) (a : α → ZMod 2) :
    (-1 : ℝ) ^ (∑ i ∈ s, a i).val = ∏ i ∈ s, (-1 : ℝ) ^ (a i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, ZMod.neg_one_pow_val_add, ih]

omit [DecidableEq ι] in
/-- Each sign has absolute value one, so `|charSum B y| ≤ |B|`. -/
theorem abs_charSum_le (B : Finset (ι → ZMod 2)) (y : ι → ZMod 2) : |charSum B y| ≤ #B := by
  calc |charSum B y| ≤ ∑ x ∈ B, |(-1 : ℝ) ^ (y ⬝ᵥ x).val| := abs_sum_le_sum_abs _ _
    _ = #B := by simp

/-- **Zero-sum tuples by Fourier inversion** [Saglam2027, Section 3.3]. The number of `ℓ`-tuples of
elements of `B` with sum zero, times `2 ^ n`, is the `ℓ`-th power sum of the Fourier transform of
the indicator of `B`. In probabilistic terms, `p_ℓ = 𝔼_y μ̂(y) ^ ℓ`. -/
theorem card_filter_sum_eq_zero_mul_two_pow (B : Finset (ι → ZMod 2)) (ℓ : ℕ) :
    (#{t ∈ Fintype.piFinset (fun _ : Fin ℓ => B) | ∑ i, t i = 0} : ℝ) * 2 ^ Fintype.card ι =
      ∑ y, charSum B y ^ ℓ := by
  have hpow : ∀ y, charSum B y ^ ℓ =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin ℓ => B), (-1 : ℝ) ^ (y ⬝ᵥ ∑ i, t i).val := by
    intro y
    rw [charSum, ← Fin.prod_const, prod_univ_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [dotProduct_sum, neg_one_pow_val_sum]
  simp_rw [hpow]
  rw [sum_comm]
  simp_rw [sum_neg_one_pow_val_dotProduct]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]

omit [Fintype ι] in
/-- **Zero-sum sets versus zero-sum tuples** [Saglam2027, Section 2]. Each `ℓ`-element subset of
`B` with sum zero gives `ℓ!` distinct `ℓ`-tuples with sum zero, one for each ordering. -/
theorem card_filter_sum_eq_zero_mul_factorial_le {V : Type*} [AddCommMonoid V] [DecidableEq V]
    (B : Finset V) (ℓ : ℕ) :
    #{S ∈ B.powerset | #S = ℓ ∧ ∑ x ∈ S, x = 0} * ℓ.factorial ≤
      #{t ∈ Fintype.piFinset (fun _ : Fin ℓ => B) | ∑ i, t i = 0} := by
  set 𝒮 := {S ∈ B.powerset | #S = ℓ ∧ ∑ x ∈ S, x = 0}
  set T := {t ∈ Fintype.piFinset (fun _ : Fin ℓ => B) | ∑ i, t i = 0}
  let img : (Fin ℓ → V) → Finset V := fun t => univ.image t
  have hfiber : ∀ S ∈ 𝒮, ℓ.factorial ≤ #{t ∈ T | img t = S} := by
    intro S hS
    obtain ⟨hSB, hcard, hsum⟩ := by simpa [𝒮] using hS
    have e : Fin ℓ ≃ S := (S.equivFinOfCardEq hcard).symm
    calc ℓ.factorial = Fintype.card (Fin ℓ ≃ S) := by rw [Fintype.card_equiv e, Fintype.card_fin]
      _ = #(univ : Finset (Fin ℓ ≃ S)) := card_univ.symm
      _ ≤ _ := by
        refine card_le_card_of_injOn (fun e i => (e i : V)) (fun e _ => ?_) fun e₁ _ e₂ _ h => ?_
        · have himg : img (fun i => (e i : V)) = S := by
            ext x
            simp only [img, mem_image, mem_univ, true_and]
            exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).2, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
          refine mem_filter.2 ⟨mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => hSB (e i).2, ?_⟩,
            himg⟩
          rw [Equiv.sum_comp e (fun x : S => (x : V))]
          exact (sum_coe_sort S fun x : V => x).trans hsum
        · exact Equiv.ext fun i => Subtype.ext (congr_fun h i)
  calc #𝒮 * ℓ.factorial = ∑ _S ∈ 𝒮, ℓ.factorial := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ S ∈ 𝒮, #{t ∈ T | img t = S} := sum_le_sum hfiber
    _ = #{t ∈ T | img t ∈ 𝒮} := sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ #T := card_filter_le _ _

/-- An odd circuit avoiding `0` has at least three elements. -/
theorem three_le_card_of_isZeroSumCircuit {V : Type*} [AddCommGroup V] {S : Finset V}
    (hS : IsZeroSumCircuit S) (hodd : Odd #S) (h0 : (0 : V) ∉ S) : 3 ≤ #S := by
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.lt_or_ge k 1 with hk0 | hk1
  · obtain ⟨x, hx⟩ := card_eq_one.1 (by omega : #S = 1)
    subst hx
    exact (h0 (mem_singleton.2 (by simpa using hS.sum_eq_zero.symm))).elim
  · omega

/-- **The `sinh` bound on odd circuits** [Saglam2027, Sections 2 and 3.3]. For `0 ∉ B` and `q > 0`,
the odd zero-sum circuits `S` of `B` satisfy
`∑_S q ^ (-(|S| - 1)) ≤ (q / 2 ^ n) ∑_y (sinh (charSum B y / q) - charSum B y / q)`.

With `q = 2 ^ m`, `τ = |B| / q` and `μ̂ = charSum B / |B|` the right side is
`(V / τ) 𝔼_y (sinh (τ μ̂(y)) - τ μ̂(y))`, Saglam's bound on the expected number of odd circuits
in the kernel of a random `m`-row matrix. -/
theorem sum_odd_circuit_le_sum_sinh_sub_self {B : Finset (ι → ZMod 2)} (h0 : (0 : ι → ZMod 2) ∉ B)
    {q : ℝ} (hq : 0 < q) :
    ∑ S ∈ B.powerset with IsZeroSumCircuit S ∧ Odd #S, q⁻¹ ^ (#S - 1) ≤
      q / 2 ^ Fintype.card ι * ∑ y, (sinh (charSum B y / q) - charSum B y / q) := by
  set C := {S ∈ B.powerset | IsZeroSumCircuit S ∧ Odd #S}
  set n := Fintype.card ι
  -- The `k`-th term of the series collects the odd circuits of size `2 (k + 1) + 1`.
  set R : ℕ → ℝ := fun k =>
    q / 2 ^ n * ∑ y, (charSum B y / q) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1).factorial
  have hR : ∀ k, R k = (#{t ∈ Fintype.piFinset (fun _ : Fin (2 * (k + 1) + 1) => B) |
      ∑ i, t i = 0} : ℝ) / (2 * (k + 1) + 1).factorial * q⁻¹ ^ (2 * (k + 1)) := by
    intro k
    have h := card_filter_sum_eq_zero_mul_two_pow B (2 * (k + 1) + 1)
    simp only [R, div_pow]
    rw [← sum_div, ← sum_div, ← h, pow_succ, inv_pow]
    field_simp
    exact mul_comm _ _
  have hR0 : ∀ k, 0 ≤ R k := fun k => by rw [hR]; positivity
  have hsum : HasSum R (q / 2 ^ n * ∑ y, (sinh (charSum B y / q) - charSum B y / q)) := by
    refine HasSum.mul_left _ ?_
    refine hasSum_sum fun y _ => ?_
    have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_sinh (charSum B y / q))
    simpa using h
  -- Group the circuits by size.
  have hmaps : ∀ S ∈ C, #S / 2 - 1 ∈ range #B := by
    intro S hS
    obtain ⟨hSB, -, j, hj⟩ := mem_filter.1 hS
    have := card_le_card (mem_powerset.1 hSB)
    rw [mem_range]
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_le_hasSum _ (fun k _ => hR0 k) hsum)
  -- Fibre `k`: circuits of size `2 (k + 1) + 1`.
  have hcardS : ∀ S ∈ {S ∈ C | #S / 2 - 1 = k}, #S = 2 * (k + 1) + 1 := by
    intro S hS
    obtain ⟨hSC, hk⟩ := mem_filter.1 hS
    obtain ⟨hSB, hcirc, hodd⟩ := mem_filter.1 hSC
    have h3 := three_le_card_of_isZeroSumCircuit hcirc hodd fun h => h0 (mem_powerset.1 hSB h)
    obtain ⟨j, hj⟩ := hodd
    omega
  calc ∑ S ∈ {S ∈ C | #S / 2 - 1 = k}, q⁻¹ ^ (#S - 1)
      = #{S ∈ C | #S / 2 - 1 = k} * q⁻¹ ^ (2 * (k + 1)) := by
        rw [sum_congr rfl fun S hS => by rw [hcardS S hS, Nat.add_sub_cancel], sum_const,
          nsmul_eq_mul]
    _ ≤ #{S ∈ B.powerset | #S = 2 * (k + 1) + 1 ∧ ∑ x ∈ S, x = 0} * q⁻¹ ^ (2 * (k + 1)) := by
        gcongr
        intro S hS
        obtain ⟨hSC, -⟩ := mem_filter.1 hS
        obtain ⟨hSB, hcirc, -⟩ := mem_filter.1 hSC
        exact mem_filter.2 ⟨hSB, hcardS S hS, hcirc.sum_eq_zero⟩
    _ ≤ _ := by
        rw [hR]
        gcongr
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast card_filter_sum_eq_zero_mul_factorial_le B _

end CharSum

/-- **The three-range estimate** [Saglam2027, Section 3.3]. With `s(z) = sinh z - z`,
`s(z) ≤ 0` for `z ≤ 0`, `s(z) ≤ (sinh 1 - 1) z ^ 3` for `0 ≤ z ≤ 1`, and `s(z) ≤ e ^ z / 2` for
all `z`; together, `s(z) ≤ (sinh 1 - 1) |z| ^ 3 + [z > 1] e ^ z / 2`. -/
theorem sinh_sub_self_le (z : ℝ) :
    sinh z - z ≤ (sinh 1 - 1) * |z| ^ 3 + if 1 < z then exp z / 2 else 0 := by
  have hs1 : 0 ≤ sinh 1 - 1 := sub_nonneg.2 (self_le_sinh_iff.2 zero_le_one)
  have htail : sinh z - z ≤ exp z / 2 := by
    rcases le_total 0 z with hz | hz
    · rw [sinh_eq]
      nlinarith [exp_pos (-z)]
    · nlinarith [sinh_le_self_iff.2 hz, exp_pos z]
  split_ifs with h1
  · nlinarith [pow_nonneg (abs_nonneg z) 3]
  rcases le_total z 0 with hz | hz
  · nlinarith [sinh_le_self_iff.2 hz, pow_nonneg (abs_nonneg z) 3]
  -- On `[0, 1]`, compare the series term by term: `z ^ (2 k + 3) ≤ z ^ 3`.
  rw [abs_of_nonneg hz, add_zero]
  have hz1 : z ≤ 1 := not_lt.1 h1
  have hsz := (hasSum_nat_add_iff' 1).2 (Real.hasSum_sinh z)
  have hs1' := ((hasSum_nat_add_iff' 1).2 (Real.hasSum_sinh 1)).mul_left (z ^ 3)
  simp only [range_one, sum_singleton, one_pow, Nat.mul_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one] at hsz hs1'
  rw [mul_comm]
  refine hasSum_le (fun k => ?_) hsz hs1'
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hz hz1 (by omega)) (by positivity)

section CharSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The moment and tail bound** [Saglam2027, Section 3.3]. For `0 ∉ B` and `q > 0`, the odd
zero-sum circuits `S` of `B` satisfy
`∑_S q ^ (-(|S| - 1)) ≤ (q / 2 ^ n) ((sinh 1 - 1) ∑_y |charSum B y / q| ^ 3 +
  (e ^ (|B| / q) / 2) #{y | q < charSum B y})`. -/
theorem sum_odd_circuit_le_moment_add_tail {B : Finset (ι → ZMod 2)} (h0 : (0 : ι → ZMod 2) ∉ B)
    {q : ℝ} (hq : 0 < q) :
    ∑ S ∈ B.powerset with IsZeroSumCircuit S ∧ Odd #S, q⁻¹ ^ (#S - 1) ≤
      q / 2 ^ Fintype.card ι * ((sinh 1 - 1) * ∑ y, |charSum B y / q| ^ 3 +
        exp (#B / q) / 2 * #{y | q < charSum B y}) := by
  refine (sum_odd_circuit_le_sum_sinh_sub_self h0 hq).trans ?_
  gcongr
  calc ∑ y, (sinh (charSum B y / q) - charSum B y / q)
      ≤ ∑ y, ((sinh 1 - 1) * |charSum B y / q| ^ 3 +
          if q < charSum B y then exp (#B / q) / 2 else 0) := by
        refine sum_le_sum fun y _ => (sinh_sub_self_le _).trans ?_
        gcongr
        simp only [one_lt_div hq]
        split_ifs
        · gcongr
          exact (le_abs_self _).trans (abs_charSum_le B y)
        · rfl
    _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_ite, sum_const_zero, add_zero, sum_const,
          nsmul_eq_mul, mul_comm (exp _ / 2)]

/-- **Linear codes from the moment and tail estimates** [Saglam2027, Section 3.3]. Let
`B = {x ≠ 0 | |x| < d}` have `V` elements, let `m : ℕ`, `τ = V / 2 ^ m`, and
`μ̂(y) = charSum B y / V`. If
`(V / τ) ((sinh 1 - 1) τ ^ 3 𝔼_y |μ̂ y| ^ 3 + (e ^ τ / 2) Pr_y[1 / τ < μ̂ y]) < 1`,
then some `(m + 1)`-row parity-check matrix over `𝔽₂` defines a linear code of minimum distance at
least `d` with at least `2 ^ (n - (m + 1))` codewords.

This is the conditional form of Saglam's argument: Lemma 3.1 of [Saglam2027] supplies the moment
and tail estimates that make the hypothesis hold for `log n ≪ d ≤ (1/2 - ε) n`. -/
theorem exists_le_minDist_parityCheckCode_of_moment_tail (d m : ℕ)
    (h : let B : Finset (ι → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < d}
      let τ : ℝ := #B / 2 ^ m
      let μ : (ι → ZMod 2) → ℝ := fun y => charSum B y / #B
      #B / τ * ((sinh 1 - 1) * τ ^ 3 * ((∑ y, |μ y| ^ 3) / 2 ^ Fintype.card ι) +
        exp τ / 2 * (#{y | 1 / τ < μ y} / 2 ^ Fintype.card ι)) < 1) :
    ∃ H : Matrix (Fin (m + 1)) ι (ZMod 2),
      (d : ℕ∞) ≤ minDist (parityCheckCode H : Set (ι → ZMod 2)) ∧
        2 ^ (Fintype.card ι - (m + 1)) ≤ Nat.card (parityCheckCode H) := by
  set B : Finset (ι → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < d} with hB
  suffices key : ∑ S ∈ B.powerset with IsZeroSumCircuit S ∧ Odd #S, ((2 : ℝ) ^ m)⁻¹ ^ (#S - 1) < 1
    from exists_le_minDist_parityCheckCode_of_sum_lt_one d m key
  have h0 : (0 : ι → ZMod 2) ∉ B := by simp [B]
  have hq : (0 : ℝ) < 2 ^ m := by positivity
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · simp [hBe, filter_singleton]
  have hV : (0 : ℝ) < #B := by exact_mod_cast hBne.card_pos
  refine (sum_odd_circuit_le_moment_add_tail h0 hq).trans_lt (lt_of_eq_of_lt ?_ h)
  have hcount : (#{y | (2 : ℝ) ^ m < charSum B y} : ℝ) =
      #{y | 1 / (#B / (2 : ℝ) ^ m) < charSum B y / #B} := by
    congr 2
    refine filter_congr fun y _ => ?_
    rw [one_div, inv_div, div_lt_div_iff_of_pos_right hV]
  rw [hcount]
  have habs : ∀ y, |charSum B y / 2 ^ m| ^ 3 = (#B / 2 ^ m) ^ 3 * |charSum B y / #B| ^ 3 := by
    intro y
    rw [show charSum B y / 2 ^ m = #B / 2 ^ m * (charSum B y / #B) by field_simp, abs_mul,
      mul_pow, abs_of_pos (div_pos hV hq)]
  simp_rw [habs, ← mul_sum]
  field_simp

end CharSum

end Cslib.Code
