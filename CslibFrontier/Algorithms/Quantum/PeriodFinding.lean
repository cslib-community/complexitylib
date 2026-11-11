/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Foundations.Quantum.Fourier
public import CslibFrontier.Foundations.Quantum.Register
public import CslibFrontier.Foundations.Data.ZMod.Multiples
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Analysis.Fourier.ZModMultiples
import CslibFrontier.Foundations.Quantum.Bipartite
import CslibFrontier.Foundations.Data.Nat.Totient

/-!
# Exact quantum period finding

This module formalizes the quantum core of Shor's algorithm in the case where the period divides
the size of the Fourier register ([Shor][Shor1997], §5; [de Wolf][deWolf2019], §5.3, "Easy case:
r divides q").

**The problem.** A function `f : ZMod N → S` has *exact period* `r` (`Cslib.Quantum.HasExactPeriod`)
when `r ∣ N` and `f x = f x'` exactly when `x.val ≡ x'.val [MOD r]`. For instance
`a ↦ x^a mod M` on `ZMod N` has exact period the order `r` of `x` modulo `M` whenever `r ∣ N`
(`Cslib.Quantum.hasExactPeriod_pow`).

**The algorithm.** Start in `|0⟩|s₀⟩`, apply the quantum Fourier transform (`Cslib.Quantum.qft`) to
the first register, apply an oracle unitary `U` with `U|x, s₀⟩ = |x, f x⟩`, and obtain the state
`N^{-1/2} ∑_x |x⟩|f x⟩` (`Cslib.Quantum.oracleState`;
`Cslib.Quantum.unitaryEquiv_oracle_qft_ket_zero`; [Shor][Shor1997], eqs. (5.1)–(5.2)). The standard
oracle `|x, s⟩ ↦ |x, s + f x⟩` (`Cslib.Quantum.addOracle`) is one such unitary. Apply the Fourier
transform to the first register again (`Cslib.Quantum.periodState`, Shor eqs. (5.3)–(5.4)) and
measure the first register (`Cslib.Quantum.periodFindingOutcome`).

**The analysis.** The amplitude of `|y, f x₀⟩` is `N⁻¹ ∑_{x : f x = f x₀} ω^{xy}`, a character sum
over the coset `x₀ + ⟨r⟩`, whose squared modulus is the probability of Shor's eq. (5.5). By
orthogonality over the subgroup `⟨r⟩` (`ZMod.sum_dvd_val_stdAddChar_mul`) it is `ω^{x₀ y} / r` when
`N / r` divides `y`, and `0` otherwise (`Cslib.Quantum.HasExactPeriod.periodState_apply`). Since
`f` takes `r` values, each multiple of `N / r` is measured with probability exactly `1 / r`: the
outcome is uniformly distributed on the `r` multiples of `N / r`
(`Cslib.Quantum.HasExactPeriod.periodFindingOutcome_eq`; for the whole circuit
`(F_N ⊗ I) U (F_N ⊗ I)|0, s₀⟩`, `Cslib.Quantum.HasExactPeriod.measure_period_circuit`).

**Classical recovery.** An outcome `y = c · N / r` with `0 ≤ c < r` satisfies
`y / N = c / r`, so the reduced denominator `N / gcd(N, y)` of `y / N` equals `r` exactly when `c`
is coprime to `r` ([Shor][Shor1997], §5; de Wolf §5.3). Equivalently, `y` has additive order `r` in
`ZMod N`, and exactly `φ(r)` of the multiples do, so the recovery succeeds with probability exactly
`φ(r) / r` (`Cslib.Quantum.HasExactPeriod.periodFindingOutcome_recover`). An elementary bound on
`φ(r) / r` (`Nat.le_totient_mul_log_add_one`) makes this at least `1 / (log₂ r + 1)`
(`Cslib.Quantum.HasExactPeriod.inv_log_add_one_le_periodFindingOutcome_recover`).

**Scope.** This is the special case `r ∣ N` of Shor's analysis, which takes `N = q` a power of two
with `n² ≤ q < 2n²` and handles `r ∤ q` by continued fractions; that case is not formalized. The
Fourier transform and the oracle are unitary matrices, not gate-level circuits, so no gate counts,
uniformity or approximation costs are claimed, and nothing here proves that factoring is in `BQP`.
The recovery bound `1 / (log₂ r + 1)` is weaker than the `Ω(1 / log log r)` of Shor and de Wolf,
which rests on Hardy and Wright's Theorem 328 and is not formalized. The same computation solves the
hidden subgroup problem for the subgroup `⟨r⟩` of `ZMod N`: the outcomes are uniform on its
annihilator.

## Main definitions

* `Cslib.Quantum.HasExactPeriod`: `f : ZMod N → S` has exact period `r ∣ N`.
* `Cslib.Quantum.oracleState`: the state `N^{-1/2} ∑_x |x⟩|f x⟩`.
* `Cslib.Quantum.addOracle`: the oracle `|x, s⟩ ↦ |x, s + f x⟩`.
* `Cslib.Quantum.periodState`: the state after the second Fourier transform.
* `Cslib.Quantum.periodFindingOutcome`: the distribution of the first register's measurement.

## Main results

* `Cslib.Quantum.hasExactPeriod_pow`: order finding is an instance when the order divides `N`.
* `Cslib.Quantum.unitaryEquiv_oracle_qft_ket_zero`: Fourier transform and oracle prepare
  `oracleState f` from `|0, s₀⟩`.
* `Cslib.Quantum.HasExactPeriod.periodState_apply`: the final amplitudes.
* `Cslib.Quantum.HasExactPeriod.periodFindingOutcome_apply`: each outcome has probability `1 / r`
  if it is a multiple of `N / r`, and `0` otherwise.
* `Cslib.Quantum.HasExactPeriod.periodFindingOutcome_eq`: the outcome is uniform on the multiples
  of `N / r`.
* `Cslib.Quantum.HasExactPeriod.measure_period_circuit`: the same for the first register of the
  measured circuit `(F_N ⊗ I) U (F_N ⊗ I)|0, s₀⟩`, for any oracle unitary `U`.
* `Cslib.Quantum.HasExactPeriod.periodFindingOutcome_recover`: `N / gcd(N, y) = r` with probability
  exactly `φ(r) / r`.
* `Cslib.Quantum.HasExactPeriod.inv_log_add_one_le_periodFindingOutcome_recover`: that probability
  is at least `1 / (log₂ r + 1)`.

## References

* [P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a
  quantum computer*][Shor1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset ZMod

variable {N : ℕ} [NeZero N] {S : Type*}

/-- `f : ZMod N → S` has **exact period** `r`: `r` divides `N`, and `f x = f x'` exactly when
`x` and `x'` are congruent modulo `r`. This is the promise of exact period finding
([de Wolf][deWolf2019], §5.3, the case where `r` divides `q`). -/
structure HasExactPeriod (f : ZMod N → S) (r : ℕ) : Prop where
  dvd : r ∣ N
  eq_iff : ∀ x x', f x = f x' ↔ x.val ≡ x'.val [MOD r]

namespace HasExactPeriod

variable {f : ZMod N → S} {r : ℕ}

theorem pos (h : HasExactPeriod f r) : 0 < r :=
  Nat.pos_of_ne_zero fun hr => NeZero.ne N (Nat.eq_zero_of_zero_dvd (hr ▸ h.dvd))

/-- Under exact period `r`, `f x = f x'` exactly when `x' - x` lies in the subgroup generated by
`r`. -/
theorem eq_iff_sub_mem (h : HasExactPeriod f r) (x x' : ZMod N) :
    f x = f x' ↔ x' - x ∈ AddSubgroup.zmultiples (r : ZMod N) := by
  have hc : ∀ z : ZMod N, ZMod.castHom h.dvd (ZMod r) z = (z.val : ZMod r) := fun z => by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [h.eq_iff, mem_zmultiples_iff_dvd_val h.dvd, ← ZMod.natCast_eq_natCast_iff,
    ← ZMod.natCast_eq_zero_iff, ← hc, ← hc, ← hc, map_sub, sub_eq_zero, eq_comm]

/-- A function with exact period `r` takes exactly `r` values. -/
theorem card_image [DecidableEq S] (h : HasExactPeriod f r) : #(univ.image f) = r := by
  have hfib : ∀ s ∈ univ.image f, #{x ∈ univ | f x = s} = N / r := by
    intro s hs
    obtain ⟨x₀, -, rfl⟩ := mem_image.mp hs
    rw [← card_filter_dvd_val h.dvd]
    refine card_equiv (Equiv.subRight x₀) fun x => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.subRight_apply]
    rw [eq_comm, h.eq_iff_sub_mem, mem_zmultiples_iff_dvd_val h.dvd]
  have hsum := card_eq_sum_card_image f (univ : Finset (ZMod N))
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul, card_univ, ZMod.card] at hsum
  have hpos : 0 < N / r :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) h.dvd) h.pos
  rw [Nat.eq_div_of_mul_eq_left hpos.ne' hsum.symm, Nat.div_div_self h.dvd (NeZero.ne N)]

end HasExactPeriod

omit [NeZero N] in
/-- **Order finding is exact period finding** when the order divides `N`: if `orderOf x ∣ N`, then
`a ↦ x ^ a.val` has exact period `orderOf x` ([Shor][Shor1997], §5, with `x^a mod n` in the
group of units of `ZMod n`). -/
theorem hasExactPeriod_pow {G : Type*} [LeftCancelMonoid G] {x : G} (hx : orderOf x ∣ N) :
    HasExactPeriod (fun a : ZMod N => x ^ a.val) (orderOf x) :=
  ⟨hx, fun _ _ => pow_eq_pow_iff_modEq⟩

/-! ### State preparation -/

section Oracle

variable [Fintype S] [DecidableEq S]

/-- The state `N^{-1/2} ∑_x |x⟩|f x⟩` after one query to `f` on a uniform superposition
([Shor][Shor1997], eq. (5.2)). -/
noncomputable def oracleState (f : ZMod N → S) : EuclideanSpace ℂ (ZMod N × S) :=
  WithLp.toLp 2 fun (x, s) => if f x = s then (((Real.sqrt N)⁻¹ : ℝ) : ℂ) else 0

omit [NeZero N] [Fintype S] in
theorem oracleState_apply (f : ZMod N → S) (p : ZMod N × S) :
    (oracleState f).ofLp p = if f p.1 = p.2 then (((Real.sqrt N)⁻¹ : ℝ) : ℂ) else 0 := by
  rfl

theorem norm_oracleState (f : ZMod N → S) : ‖oracleState f‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp ?_
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [oracleState_apply, apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sum_ite_eq, mem_univ, ite_true]
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N),
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))]

/-- The Fourier transform of `|0⟩` is the uniform superposition: `(F_N ⊗ I)|0, s₀⟩ =
N^{-1/2} ∑_x |x, s₀⟩` ([Shor][Shor1997], eq. (5.1)). -/
theorem unitaryEquiv_onFirst_qft_ket_zero (s₀ : S) :
    unitaryEquiv (onFirst (qft N)) (ket ((0 : ZMod N), s₀)) =
      ∑ x : ZMod N, (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • ket (x, s₀) := by
  ext ⟨y, s⟩
  rw [unitaryEquiv_apply, WithLp.ofLp_sum, mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_apply]
  simp only [onFirst_apply, ket_apply, Prod.mk.injEq, qft_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_and, mem_univ, ite_true, sum_ite_eq]
  rw [Fintype.sum_eq_single 0 fun x hx => sum_eq_zero fun _ _ => ite_eq_right hx]
  simp [eq_comm]

/-- **State preparation** ([Shor][Shor1997], eqs. (5.1)–(5.2)): for any oracle unitary `U` with
`U|x, s₀⟩ = |x, f x⟩`, applying the Fourier transform to the first register of `|0, s₀⟩` and then
`U` gives `N^{-1/2} ∑_x |x⟩|f x⟩`. -/
theorem unitaryEquiv_oracle_qft_ket_zero (U : unitaryGroup (ZMod N × S) ℂ) (s₀ : S)
    {f : ZMod N → S} (hU : ∀ x, unitaryEquiv U (ket (x, s₀)) = ket (x, f x)) :
    unitaryEquiv U (unitaryEquiv (onFirst (qft N)) (ket ((0 : ZMod N), s₀))) =
      oracleState f := by
  rw [unitaryEquiv_onFirst_qft_ket_zero, map_sum]
  simp only [_root_.map_smul, hU]
  ext ⟨x, s⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, oracleState_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, ket_apply, Prod.mk.injEq, smul_eq_mul, mul_ite,
    mul_one, mul_zero, ite_and]
  rw [Fintype.sum_eq_single x fun x' hx' => ite_eq_right (Ne.symm hx')]
  simp [eq_comm]

/-- The standard oracle `|x, s⟩ ↦ |x, s + f x⟩` of a function into an additive group, the
permutation matrix of a shear of `ZMod N × S`. -/
noncomputable def addOracle [AddGroup S] (f : ZMod N → S) : unitaryGroup (ZMod N × S) ℂ :=
  let σ : Equiv.Perm (ZMod N × S) := Equiv.prodShear (Equiv.refl _) fun x => Equiv.addRight (f x)
  ⟨σ⁻¹.permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
      inv_mul_cancel, permMatrix_one]⟩

theorem unitaryEquiv_addOracle_ket [AddGroup S] (f : ZMod N → S) (x : ZMod N) (s : S) :
    unitaryEquiv (addOracle f) (ket (x, s)) = ket (x, s + f x) := by
  ext ⟨y, t⟩
  rw [unitaryEquiv_apply, addOracle, permMatrix_mulVec]
  simp only [Function.comp_apply, ket_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.prodShear_apply,
    Equiv.refl_apply, Equiv.coe_addRight, Prod.mk.injEq]

/-- With the standard oracle and `s₀ = 0`, Fourier transform and oracle prepare
`N^{-1/2} ∑_x |x⟩|f x⟩`. -/
theorem unitaryEquiv_addOracle_qft_ket_zero [AddGroup S] (f : ZMod N → S) :
    unitaryEquiv (addOracle f) (unitaryEquiv (onFirst (qft N)) (ket ((0 : ZMod N), (0 : S)))) =
      oracleState f :=
  unitaryEquiv_oracle_qft_ket_zero _ 0 fun x => by rw [unitaryEquiv_addOracle_ket, zero_add]

end Oracle

/-! ### The final state and its measurement -/

section Measurement

variable [Fintype S] [DecidableEq S]

/-- The state `(F_N ⊗ I) N^{-1/2} ∑_x |x⟩|f x⟩` before the final measurement
([Shor][Shor1997], eq. (5.4)). -/
noncomputable def periodState (f : ZMod N → S) : EuclideanSpace ℂ (ZMod N × S) :=
  unitaryEquiv (onFirst (qft N)) (oracleState f)

theorem norm_periodState (f : ZMod N → S) : ‖periodState f‖ = 1 := by
  rw [periodState, LinearIsometryEquiv.norm_map, norm_oracleState]

/-- The amplitude of `|y, s⟩` in `periodState f` is `N⁻¹ ∑_{x : f x = s} ω^{xy}`. -/
theorem periodState_apply (f : ZMod N → S) (y : ZMod N) (s : S) :
    (periodState f).ofLp (y, s) =
      (N : ℂ)⁻¹ * ∑ x : ZMod N, if f x = s then stdAddChar (x * y) else 0 := by
  rw [periodState, unitaryEquiv_apply, mulVec, dotProduct, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [onFirst_apply, oracleState_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, qft_apply]
  by_cases hx : f x = s
  · rw [ite_eq_left hx.symm, ite_eq_left hx, ← sqrt_inv_mul_sqrt_inv, mul_comm y x]; ring
  · rw [ite_eq_right (Ne.symm hx), ite_eq_right hx]

/-- Values that `f` never takes have amplitude `0`. -/
theorem periodState_apply_of_forall_ne {f : ZMod N → S} {s : S} (hs : ∀ x, f x ≠ s)
    (y : ZMod N) : (periodState f).ofLp (y, s) = 0 := by
  rw [periodState_apply, sum_eq_zero fun x _ => ite_eq_right (hs x), mul_zero]

/-- **The final amplitudes** under exact period `r`, in the case `r ∣ N`: the amplitude of
`|y, f x₀⟩` is `ω^{x₀ y} / r` when `N / r` divides `y`, and `0` otherwise. Its squared modulus is
the probability of [Shor][Shor1997], eq. (5.5) (`HasExactPeriod.norm_periodState_apply_sq`). -/
theorem HasExactPeriod.periodState_apply {f : ZMod N → S} {r : ℕ} (h : HasExactPeriod f r)
    (x₀ y : ZMod N) :
    (periodState f).ofLp (y, f x₀) =
      if N / r ∣ y.val then (r : ℂ)⁻¹ * stdAddChar (x₀ * y) else 0 := by
  -- The sum over the coset `x₀ + ⟨r⟩` is `ω^{x₀ y}` times the sum over `⟨r⟩`.
  have key : ∑ x : ZMod N, (if f x = f x₀ then stdAddChar (x * y) else 0) =
      stdAddChar (x₀ * y) * ∑ h : ZMod N, (if r ∣ h.val then stdAddChar (h * y) else 0) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight x₀) _ _ fun x => ?_
    have hiff : r ∣ (x - x₀).val ↔ f x = f x₀ := by
      rw [← mem_zmultiples_iff_dvd_val h.dvd, ← h.eq_iff_sub_mem, eq_comm]
    rw [Equiv.subRight_apply, if_congr hiff rfl rfl]
    split_ifs
    · rw [← AddChar.map_add_eq_mul]; ring_nf
    · rw [mul_zero]
  rw [Cslib.Quantum.periodState_apply, key, sum_dvd_val_stdAddChar_mul h.dvd]
  split_ifs
  · have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.pos.ne'
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [Nat.cast_div h.dvd hr]
    field_simp
  · rw [mul_zero, mul_zero]

/-- Under exact period `r`, each joint outcome `(y, f x₀)` has probability `1 / r²` when `N / r`
divides `y`, and `0` otherwise: the probability of [Shor][Shor1997], eq. (5.5), in the case
`r ∣ N`. -/
theorem HasExactPeriod.norm_periodState_apply_sq {f : ZMod N → S} {r : ℕ}
    (h : HasExactPeriod f r) (x₀ y : ZMod N) :
    ‖(periodState f).ofLp (y, f x₀)‖ ^ 2 = if N / r ∣ y.val then ((r : ℝ) ^ 2)⁻¹ else 0 := by
  rw [h.periodState_apply]
  split_ifs
  · rw [norm_mul, stdAddChar_apply, Circle.norm_coe, mul_one, norm_inv, Complex.norm_natCast,
      inv_pow]
  · rw [norm_zero, sq, mul_zero]

/-- The distribution of the outcome of measuring the first register of `periodState f`: the
marginal on `ZMod N` of the computational-basis measurement of both registers. -/
noncomputable def periodFindingOutcome (f : ZMod N → S) : PMF (ZMod N) :=
  (measure (periodState f) (norm_periodState f)).map Prod.fst

/-- The probability that the first register reads `y`, summed over the second register. -/
private theorem HasExactPeriod.sum_norm_periodState_apply_sq {f : ZMod N → S} {r : ℕ}
    (h : HasExactPeriod f r) (y : ZMod N) :
    ∑ s : S, ‖(periodState f).ofLp (y, s)‖ ^ 2 = if N / r ∣ y.val then (r : ℝ)⁻¹ else 0 := by
  rw [← sum_subset (subset_univ (univ.image f)) fun s _ hs => by
    rw [periodState_apply_of_forall_ne (fun x hx => hs (mem_image.mpr ⟨x, mem_univ _, hx⟩)),
      norm_zero, sq, mul_zero]]
  have hc : ∀ s ∈ univ.image f, ‖(periodState f).ofLp (y, s)‖ ^ 2 =
      if N / r ∣ y.val then ((r : ℝ) ^ 2)⁻¹ else 0 := by
    intro s hs
    obtain ⟨x₀, -, rfl⟩ := mem_image.mp hs
    exact h.norm_periodState_apply_sq x₀ y
  rw [sum_congr rfl hc, sum_const, h.card_image, nsmul_eq_mul]
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.pos.ne'
  split_ifs
  · field_simp
  · rw [mul_zero]

/-- **Exact period finding** ([de Wolf][deWolf2019], §5.3, the case where `r` divides `q`):
measuring the first register gives `y` with probability `1 / r` if `N / r` divides `y`, and `0`
otherwise. -/
theorem HasExactPeriod.periodFindingOutcome_apply {f : ZMod N → S} {r : ℕ}
    (h : HasExactPeriod f r) (y : ZMod N) :
    periodFindingOutcome f y = if N / r ∣ y.val then (r : ENNReal)⁻¹ else 0 := by
  rw [periodFindingOutcome, measure_map_fst_apply, EuclideanSpace.norm_sq_eq]
  simp only [condState_apply]
  rw [h.sum_norm_periodState_apply_sq]
  split_ifs
  · rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr h.pos), ENNReal.ofReal_natCast]
  · exact ENNReal.ofReal_zero

/-- **Exact period finding**, as an equality of distributions: the measured value is uniformly
distributed on the `r` multiples of `N / r`. -/
theorem HasExactPeriod.periodFindingOutcome_eq {f : ZMod N → S} {r : ℕ}
    (h : HasExactPeriod f r) :
    periodFindingOutcome f =
      Cslib.Probability.PMF.uniformOfFinset {y : ZMod N | N / r ∣ y.val}
        (filter_dvd_val_nonempty _) := by
  ext y
  rw [h.periodFindingOutcome_apply, Cslib.Probability.PMF.uniformOfFinset_apply,
    card_filter_dvd_val (Nat.div_dvd_of_dvd h.dvd), Nat.div_div_self h.dvd (NeZero.ne N)]
  simp only [mem_filter, mem_univ, true_and]

/-- **Exact period finding, end to end**: for any oracle unitary `U` with `U|x, s₀⟩ = |x, f x⟩`,
measuring the state `(F_N ⊗ I) U (F_N ⊗ I)|0, s₀⟩` and reading the first register gives a uniformly
distributed multiple of `N / r` ([Shor][Shor1997], eqs. (5.1)–(5.5), in the case `r ∣ N`;
[de Wolf][deWolf2019], §5.3). -/
theorem HasExactPeriod.measure_period_circuit {f : ZMod N → S} {r : ℕ} (h : HasExactPeriod f r)
    (U : unitaryGroup (ZMod N × S) ℂ) (s₀ : S)
    (hU : ∀ x, unitaryEquiv U (ket (x, s₀)) = ket (x, f x)) :
    (measure (unitaryEquiv (onFirst (qft N))
        (unitaryEquiv U (unitaryEquiv (onFirst (qft N)) (ket ((0 : ZMod N), s₀)))))
        (by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
          LinearIsometryEquiv.norm_map, norm_ket])).map Prod.fst =
      Cslib.Probability.PMF.uniformOfFinset {y : ZMod N | N / r ∣ y.val}
        (filter_dvd_val_nonempty _) := by
  have hψ : unitaryEquiv (onFirst (qft N))
      (unitaryEquiv U (unitaryEquiv (onFirst (qft N)) (ket ((0 : ZMod N), s₀)))) =
      periodState f := by
    rw [unitaryEquiv_oracle_qft_ket_zero U s₀ hU]
    rfl
  rw [← h.periodFindingOutcome_eq, periodFindingOutcome]
  congr 2

/-- **Classical recovery** ([Shor][Shor1997], §5; [de Wolf][deWolf2019], §5.3): the reduced
denominator `N / gcd(N, y)` of `y / N` is the period `r` with probability exactly `φ(r) / r`. -/
theorem HasExactPeriod.periodFindingOutcome_recover {f : ZMod N → S} {r : ℕ}
    (h : HasExactPeriod f r) :
    (periodFindingOutcome f).toOuterMeasure {y | N / Nat.gcd N y.val = r} =
      (Nat.totient r : ENNReal) * (r : ENNReal)⁻¹ := by
  classical
  rw [h.periodFindingOutcome_eq, Cslib.Probability.PMF.toOuterMeasure_uniformOfFinset,
    card_filter_dvd_val (Nat.div_dvd_of_dvd h.dvd), Nat.div_div_self h.dvd (NeZero.ne N)]
  congr 2
  -- A residue `y` with `N / gcd(N, y) = r` is a multiple of `N / r = gcd(N, y)`.
  have hsub : ∀ y : ZMod N, N / Nat.gcd N y.val = r → N / r ∣ y.val := by
    intro y hy
    rw [← hy, Nat.div_div_self (Nat.gcd_dvd_left N y.val) (NeZero.ne N)]
    exact Nat.gcd_dvd_right N y.val
  -- These are the `φ(r)` residues of additive order `r`.
  rw [filter_filter, ← IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod N)
    (by rw [ZMod.card]; exact h.dvd)]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq, addOrderOf_eq_div_gcd_val]
  exact ⟨fun h' => h'.2, fun h' => ⟨hsub y h', h'⟩⟩

/-- The recovery of `Cslib.Quantum.HasExactPeriod.periodFindingOutcome_recover` succeeds with
probability at least `1 / (log₂ r + 1)`, by the elementary bound `r ≤ φ(r) (log₂ r + 1)`
(`Nat.le_totient_mul_log_add_one`). -/
theorem HasExactPeriod.inv_log_add_one_le_periodFindingOutcome_recover {f : ZMod N → S}
    {r : ℕ} (h : HasExactPeriod f r) :
    ((Nat.log 2 r + 1 : ℕ) : ENNReal)⁻¹ ≤
      (periodFindingOutcome f).toOuterMeasure {y | N / Nat.gcd N y.val = r} := by
  rw [h.periodFindingOutcome_recover, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr h.pos.ne'))
      (Or.inl (ENNReal.natCast_ne_top r)),
    ENNReal.inv_mul_le_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
      (ENNReal.natCast_ne_top _), ← Nat.cast_mul, Nat.cast_le, mul_comm]
  exact Nat.le_totient_mul_log_add_one r

end Measurement

end Cslib.Quantum
