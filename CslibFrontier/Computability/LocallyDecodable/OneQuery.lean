/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.Smoothing
public import CslibFrontier.Foundations.BooleanAnalysis.FiberWeight
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith

/-!
# One-query locally decodable codes are short

A decoder making a single query learns one symbol of the received word. Katz and Trevisan
[KatzTrevisan2000] proved that one-query locally decodable codes have bounded message length: for
`q = 1` they do not exist once the message is longer than a constant depending on `δ` and `ε`
(as summarized in [Kerenidis and de Wolf, Section 1][KerenidisDeWolf2004]). This file proves a
different, explicit inequality for one-query decoders by a degree-one Fourier argument.

**Original result.** An explicit one-query bound, proved by a degree-one Fourier argument. A
`(1, c, ε)` smooth decoder with `0 ≤ ε` for a code `C : (ι → Bool) → P → Γ` satisfies
`4 |ι| ε² ≤ c² (|Γ| - 1)` (`Code.IsSmoothDecoder.four_mul_card_mul_sq_le`). So a `(1, δ, ε)`
locally decodable code, which is `(1, 1 / δ, ε)` smooth (`Code.IsLocalDecoder.isSmoothCode_of_one`),
satisfies `4 δ² |ι| ε² ≤ |Γ| - 1` (`Code.IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le`), whatever
the length of the code. The bound is polynomial in `|Γ| - 1` and in `δ²`, and the repetition code
of a single bit, read at a uniform position, attains equality with `|ι| = 1`, `c = 1`, `ε = 1 / 2`
and `|Γ| = 2`. This is not the inequality of Katz and Trevisan, and we did not find this form in
the literature we searched (Katz–Trevisan, Kerenidis–de Wolf, Yekhanin's survey, and a web
search).

The proof correlates the decoder's output with the sign of the bit `i` over a uniform message.
A decoder making one query decides from one symbol, so the correlation is at most the expected
reads weighted by the imbalance of the bit `i` on each fiber of each position
(`Code.two_mul_abs_sum_mul_decodeLaw_le`). Those imbalances are degree-one Fourier coefficients of
the fiber indicators, whose total is at most `√(|ι| (|Γ| - 1))` at each position
(`BitString.sq_sum_sum_abs_fourierCoeff_fiber_le`), and smoothness spreads the reads over the
positions.

## Main results

* `Cslib.Code.two_mul_abs_sum_mul_decodeLaw_le`: a one-query decoder's correlation with a balanced
  weight on received words is bounded by its expected reads.
* `Cslib.Code.IsSmoothDecoder.four_mul_card_mul_sq_le`: the bound `4 |ι| ε² ≤ c² (|Γ| - 1)` for
  one-query smooth decoders.
* `Cslib.Code.IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le`: the bound `4 δ² |ι| ε² ≤ |Γ| - 1` for
  one-query local decoders.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [I. Kerenidis, R. de Wolf, *Exponential lower bound for 2-query locally decodable codes via a
  quantum argument*][KerenidisDeWolf2004], numbering of arXiv:quant-ph/0208062v2
-/

public section

open Finset
open scoped ENNReal BigOperators

namespace Cslib.Code

open OracleComp ProbOracleComp BitString

variable {P Γ α M : Type} [Fintype P] [Fintype Γ] [Fintype M]

section Correlation

variable [DecidableEq P] [DecidableEq Γ]

private theorem two_mul_abs_sum_mul_decodeLaw_le_aux (Y : M → P → Γ) (φ : M → ℝ)
    (hφ : ∑ m, φ m = 0) (z : P → Γ) (a : α) :
    ∀ (program : ProbOracleComp (fun _ : P => Γ) α) (n : ℕ), n ≤ 1 → program.IsQueryBounded n →
      2 * |∑ m, φ m * (decodeLaw program (Y m) a).toReal| ≤
        ∑ j, (expectedReads program z j).toReal * ∑ σ, |∑ m, if Y m j = σ then φ m else 0| := by
  intro program
  induction program using OracleComp.induction with
  | pure b =>
    intro n _ _
    simp only [decodeLaw_pure, expectedReads_pure, ENNReal.toReal_zero, zero_mul, sum_const_zero]
    rw [← sum_mul, hφ, zero_mul, abs_zero, mul_zero]
  | query_bind q' cont ih =>
    intro n hn hqn
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hqn
    set S : P → ℝ := fun j => ∑ σ, |∑ m, if Y m j = σ then φ m else 0|
    cases q' with
    | inl k =>
      have hcont' (r : Fin (k + 1)) : ProbOracleComp.IsQueryBounded (cont r) n := by
        have h := hcont r
        simp only [Sum.elim_inl, Nat.sub_zero] at h
        exact h
      set u : Fin (k + 1) → ℝ := fun r => (ProbComp.unifOracle k r).toReal
      have hlaw (m : M) : (decodeLaw (OracleComp.query (.inl k) >>= cont) (Y m) a).toReal =
          ∑ r, u r * (decodeLaw (cont r) (Y m) a).toReal := by
        rw [decodeLaw_bind, decodeLaw_query_inl]
        exact Probability.PMF.bind_apply_toReal _ _ _
      have hreads (j : P) : (expectedReads (OracleComp.query (.inl k) >>= cont) z j).toReal =
          ∑ r, u r * (expectedReads (cont r) z j).toReal := by
        rw [expectedReads_query_bind, readCost_inl, zero_add, tsum_fintype,
          ENNReal.toReal_sum fun r _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
            (expectedReads_ne_top (hcont' r) z j)]
        simp only [ENNReal.toReal_mul]
        rfl
      simp only [hlaw, hreads]
      have hu (r : Fin (k + 1)) : 0 ≤ u r := ENNReal.toReal_nonneg
      calc 2 * |∑ m, φ m * ∑ r, u r * (decodeLaw (cont r) (Y m) a).toReal|
          = 2 * |∑ r, u r * ∑ m, φ m * (decodeLaw (cont r) (Y m) a).toReal| := by
            simp only [mul_sum]
            rw [sum_comm]
            congr 2
            refine sum_congr rfl fun r _ => sum_congr rfl fun m _ => ?_
            ring
        _ ≤ ∑ r, u r * (2 * |∑ m, φ m * (decodeLaw (cont r) (Y m) a).toReal|) := by
            refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) zero_le_two).trans ?_
            rw [mul_sum]
            refine sum_le_sum fun r _ => ?_
            rw [abs_mul, abs_of_nonneg (hu r)]
            exact le_of_eq (by ring)
        _ ≤ ∑ r, u r * ∑ j, (expectedReads (cont r) z j).toReal * S j :=
            sum_le_sum fun r _ =>
              mul_le_mul_of_nonneg_left (ih r n hn (hcont' r)) (hu r)
        _ = ∑ j, (∑ r, u r * (expectedReads (cont r) z j).toReal) * S j := by
            simp only [mul_sum, sum_mul]
            rw [sum_comm]
            refine sum_congr rfl fun j _ => sum_congr rfl fun r _ => ?_
            ring
    | inr j0 =>
      have h0 (σ : Γ) : ProbOracleComp.IsQueryBounded (cont σ) 0 := by
        have h := (hcont σ).mono (m := 0) (by simp only [Sum.elim_inr] at hle ⊢; omega)
        exact h
      set p : Γ → ℝ := fun σ => (decodeLaw (cont σ) z a).toReal
      have hlaw (m : M) : (decodeLaw (OracleComp.query (.inr j0) >>= cont) (Y m) a).toReal =
          p (Y m j0) := by
        rw [decodeLaw_bind, decodeLaw_query_inr, PMF.pure_bind,
          decodeLaw_eq_of_isQueryBounded_zero (h0 _) (Y m) z]
      have hreads (j : P) : (expectedReads (OracleComp.query (.inr j0) >>= cont) z j).toReal =
          if j0 = j then 1 else 0 := by
        rw [expectedReads_query_bind, readCost_inr]
        simp only [expectedReads_eq_zero_of_isQueryBounded_zero (h0 _), mul_zero, tsum_zero,
          add_zero]
        split_ifs <;> simp
      simp only [hlaw, hreads, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
      set T : Γ → ℝ := fun σ => ∑ m, if Y m j0 = σ then φ m else 0
      have hT : ∑ σ, T σ = 0 := by
        simp only [T]
        rw [sum_comm]
        simp only [Fintype.sum_ite_eq]
        exact hφ
      have hpT : ∑ σ, p σ * T σ = ∑ m, φ m * p (Y m j0) := by
        simp only [T, mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [Fintype.sum_ite_eq]
        ring
      have hsum : ∑ m, φ m * p (Y m j0) = ∑ σ, (p σ - 1 / 2) * T σ := by
        simp only [sub_mul]
        rw [sum_sub_distrib, ← mul_sum, hT, mul_zero, sub_zero, hpT]
      rw [hsum]
      calc 2 * |∑ σ, (p σ - 1 / 2) * T σ| ≤ 2 * ∑ σ, |(p σ - 1 / 2) * T σ| :=
            mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) zero_le_two
        _ ≤ 2 * ∑ σ, 1 / 2 * |T σ| := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum fun σ _ => ?_) zero_le_two
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            have h1 : p σ ≤ 1 := Probability.PMF.toReal_apply_le_one _ _
            have h2 : 0 ≤ p σ := ENNReal.toReal_nonneg
            rw [abs_le]
            constructor <;> linarith
        _ = ∑ σ, |T σ| := by
            rw [mul_sum]
            refine sum_congr rfl fun σ _ => ?_
            ring

/-- **A one-query decoder sees one symbol**: for a weight `φ` on received words `Y m` with total
zero, twice the correlation of `φ` with the probability that a decoder making at most one query
outputs `a` is at most the sum, over the positions `j`, of the expected reads of `j` against any
fixed word `z` times the total imbalance `∑ σ, |∑_{Y m j = σ} φ m|` of `φ` on the fibers of `j`.
-/
theorem two_mul_abs_sum_mul_decodeLaw_le {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 1) (Y : M → P → Γ) (φ : M → ℝ) (hφ : ∑ m, φ m = 0)
    (z : P → Γ) (a : α) :
    2 * |∑ m, φ m * (decodeLaw program (Y m) a).toReal| ≤
      ∑ j, (expectedReads program z j).toReal * ∑ σ, |∑ m, if Y m j = σ then φ m else 0| :=
  two_mul_abs_sum_mul_decodeLaw_le_aux Y φ hφ z a program 1 le_rfl hq

end Correlation

variable {ι : Type} [Fintype ι]

/-- **One-query smooth codes are short.** Original result: an explicit one-query bound proved by a
degree-one Fourier argument. A `(1, c, ε)` smooth decoder with `0 ≤ ε` for a code from `ι`-bit
messages to words over `Γ` satisfies `4 |ι| ε² ≤ c² (|Γ| - 1)`. Katz and Trevisan
[KatzTrevisan2000] proved that one-query locally decodable codes have bounded message length;
this is a different inequality, polynomial in `|Γ| - 1`, and we did not find this form in the
literature. -/
theorem IsSmoothDecoder.four_mul_card_mul_sq_le [DecidableEq P] [Nonempty Γ]
    {C : (ι → Bool) → P → Γ} {c ε : ℝ} {A : LocalDecoder ι P Γ} (hA : IsSmoothDecoder C 1 c ε A)
    (hε : 0 ≤ ε) : 4 * Fintype.card ι * ε ^ 2 ≤ c ^ 2 * (Fintype.card Γ - 1) := by
  classical
  set K : ℝ := (Fintype.card ι : ℝ)
  set n : ℝ := (Fintype.card P : ℝ)
  set F : P → Γ → ι → ℝ := fun j σ i => |fourierCoeff (fun x => if C x j = σ then 1 else 0) {i}|
  have hF (j : P) (σ : Γ) (i : ι) : 0 ≤ F j σ i := abs_nonneg _
  have hcard : ((Fintype.card (ι → Bool) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  -- The bound at each message index.
  have hindex (i : ι) : 2 * ε ≤ c / n * ∑ j, ∑ σ, F j σ i := by
    set φ : (ι → Bool) → ℝ := fun x => -signVal (x i)
    have hφ : ∑ x, φ x = 0 := by
      have h := sum_chi (ι := ι) {i}
      simp only [chi_singleton, singleton_ne_empty, ite_false] at h
      simp only [φ, sum_neg_distrib, h, neg_zero]
    have hcorr (x : ι → Bool) :
        ε + φ x / 2 ≤ φ x * (decodeLaw (A i) (C x) true).toReal := by
      have hc := hA.correct x i
      have hsum := toReal_decodeLaw_add_not (C x) (A i) true
      simp only [Bool.not_true] at hsum
      cases hx : x i
      · simp only [φ, hx, signVal_false] at hc ⊢
        linarith
      · simp only [φ, hx, signVal_true] at hc ⊢
        linarith
    have hlow : 2 ^ Fintype.card ι * ε ≤
        ∑ x, φ x * (decodeLaw (A i) (C x) true).toReal := by
      refine le_trans ?_ (sum_le_sum fun x _ => hcorr x)
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard, ← sum_div, hφ, zero_div,
        add_zero]
    have hkey := two_mul_abs_sum_mul_decodeLaw_le (hA.isQueryBounded i) C φ hφ
      (C fun _ => false) true
    have himb (j : P) (σ : Γ) :
        |∑ x, if C x j = σ then φ x else 0| = 2 ^ Fintype.card ι * F j σ i := by
      have h := fourierCoeff_eq_sum (fun x => if C x j = σ then (1 : ℝ) else 0) {i}
      rw [eq_div_iff hpos.ne'] at h
      have h' : ∑ x, (if C x j = σ then φ x else 0) =
          -(fourierCoeff (fun x => if C x j = σ then 1 else 0) {i} * 2 ^ Fintype.card ι) := by
        rw [h, ← sum_neg_distrib]
        refine sum_congr rfl fun x _ => ?_
        split_ifs <;> simp [φ, chi_singleton]
      rw [h', abs_neg, abs_mul, abs_of_pos hpos, mul_comm]
    have hS (j : P) : (expectedReads (A i) (C fun _ => false) j).toReal *
        ∑ σ, |∑ x, if C x j = σ then φ x else 0| ≤
          c / n * (2 ^ Fintype.card ι * ∑ σ, F j σ i) := by
      simp only [himb, ← mul_sum]
      exact mul_le_mul_of_nonneg_right (hA.smooth _ i j)
        (mul_nonneg hpos.le (sum_nonneg fun σ _ => hF j σ i))
    have h2 : 2 * (2 ^ Fintype.card ι * ε) ≤
        2 ^ Fintype.card ι * (c / n * ∑ j, ∑ σ, F j σ i) := by
      calc 2 * (2 ^ Fintype.card ι * ε)
          ≤ 2 * |∑ x, φ x * (decodeLaw (A i) (C x) true).toReal| :=
            mul_le_mul_of_nonneg_left (hlow.trans (le_abs_self _)) zero_le_two
        _ ≤ _ := hkey
        _ ≤ ∑ j, c / n * (2 ^ Fintype.card ι * ∑ σ, F j σ i) := sum_le_sum fun j _ => hS j
        _ = 2 ^ Fintype.card ι * (c / n * ∑ j, ∑ σ, F j σ i) := by
            rw [← mul_sum, ← mul_sum]
            ring
    nlinarith
  -- Sum over the message indices.
  set X : ℝ := ∑ j, ∑ σ, ∑ i, F j σ i
  have hX0 : 0 ≤ X := sum_nonneg fun j _ => sum_nonneg fun σ _ => sum_nonneg fun i _ => hF j σ i
  have hsum : 2 * K * ε ≤ c / n * X := by
    have h := sum_le_sum fun i (_ : i ∈ univ) => hindex i
    rw [sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at h
    have hX : ∑ i, ∑ j, ∑ σ, F j σ i = X := by
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_comm]
    rw [hX] at h
    linarith
  -- Each position carries little degree-one weight.
  set B : ℝ := K * (Fintype.card Γ - 1)
  have hY (j : P) : (∑ σ, ∑ i, F j σ i) ^ 2 ≤ B :=
    sq_sum_sum_abs_fourierCoeff_fiber_le fun x => C x j
  have hΓ : (1 : ℝ) ≤ Fintype.card Γ := by exact_mod_cast Fintype.card_pos
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hXsq : X ^ 2 ≤ n ^ 2 * B := by
    calc X ^ 2 ≤ n * ∑ j, (∑ σ, ∑ i, F j σ i) ^ 2 := by
          simpa only [card_univ] using sq_sum_le_card_mul_sum_sq (s := univ)
            (f := fun j => ∑ σ, ∑ i, F j σ i)
      _ ≤ n * ∑ _j : P, B := mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hY j)
          (Nat.cast_nonneg _)
      _ = n ^ 2 * B := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          ring
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hKε : 0 ≤ K * ε := mul_nonneg hK hε
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  rcases hn0.eq_or_lt with hn | hn
  · -- No positions: the decoder learns nothing, so `ε = 0` or there is no message bit.
    rw [← hn, div_zero, zero_mul] at hsum
    have : K * ε = 0 := by linarith
    have h2 : K * ε ^ 2 = 0 := by rw [sq, ← mul_assoc, this, zero_mul]
    nlinarith [sq_nonneg c]
  · rcases le_or_gt c 0 with hc | hc
    · have : c / n * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc
        hn.le) hX0
      have : K * ε = 0 := by linarith
      have h2 : K * ε ^ 2 = 0 := by rw [sq, ← mul_assoc, this, zero_mul]
      nlinarith [sq_nonneg c]
    · -- Square the bound and divide by `K`.
      have hsq : (2 * K * ε) ^ 2 ≤ c ^ 2 * B := by
        have h1 : (2 * K * ε) ^ 2 ≤ (c / n * X) ^ 2 := by gcongr
        have h2 : (c / n * X) ^ 2 = c ^ 2 / n ^ 2 * X ^ 2 := by ring
        have h3 : c ^ 2 / n ^ 2 * X ^ 2 ≤ c ^ 2 / n ^ 2 * (n ^ 2 * B) := by gcongr
        have h4 : c ^ 2 / n ^ 2 * (n ^ 2 * B) = c ^ 2 * B := by
          field_simp [hn.ne']
        linarith
      rcases hK.eq_or_lt with hK0 | hKpos
      · rw [← hK0]
        nlinarith [sq_nonneg c]
      · have : K * (4 * K * ε ^ 2) ≤ K * (c ^ 2 * (Fintype.card Γ - 1)) := by
          simp only [B] at hsq
          nlinarith
        exact le_of_mul_le_mul_left this hKpos

/-- **One-query locally decodable codes are short.** Original result: an explicit one-query bound
proved by a degree-one Fourier argument. A `(1, δ, ε)` locally decodable code with `0 < δ` and
`0 ≤ ε` from `ι`-bit messages to words over `Γ` satisfies `4 δ² |ι| ε² ≤ |Γ| - 1`, whatever its
length. Katz and Trevisan [KatzTrevisan2000] proved that one-query locally decodable codes have
bounded message length; this is a different inequality, polynomial in `|Γ| - 1` and in `δ²`, and
we did not find this form in the literature. -/
theorem IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le [DecidableEq Γ] [Nonempty Γ]
    {C : (ι → Bool) → P → Γ} {δ ε : ℝ} {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C 1 δ ε A)
    (hδ : 0 < δ) (hε : 0 ≤ ε) : 4 * δ ^ 2 * Fintype.card ι * ε ^ 2 ≤ Fintype.card Γ - 1 := by
  classical
  obtain ⟨A', hA'⟩ := isSmoothCode_iff.mp (hA.isSmoothCode_of_one hδ)
  have h := hA'.four_mul_card_mul_sq_le hε
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
  linarith

end Cslib.Code
