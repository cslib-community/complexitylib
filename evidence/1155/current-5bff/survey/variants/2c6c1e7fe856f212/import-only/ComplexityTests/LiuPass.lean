/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Kolmogorov.AverageCase
public import Complexity.Crypto.Computational.OneWay.CondEPPRG
public import Complexity.Crypto.Computational.OneWay.LiuPass
public import Complexity.Probability.Entropy.BitString


import Diag1155.Measure
/-!
# Tests for Liu–Pass (`OWF` $\Rightarrow$ $K^t$ mildly hard on average)

Concrete and nonvacuous tests for `Complexity.Probability.Entropy.BitString`,
`Complexity.Computability.Complexity.AverageCase`,
`Complexity.Computability.Kolmogorov.AverageCase`,
`Complexity.Crypto.Computational.OneWay.CondEPPRG`, and
`Complexity.Crypto.Computational.OneWay.LiuPass`.
-/

@[expose] public section

namespace Cslib.Crypto.LiuPassTests

open Cslib Cslib.Complexity Cslib.Kolmogorov Cslib.Crypto Probability Probability.PMF BitString
open Filter Turing.MultiTapeTM
open scoped Polynomial ENNReal

/-! ### 1. Concrete regularity bucket tests (Lemma 5.2) -/

/-- On the constant map `BitString 3 → Bool`, every input has fiber size $2^3 = 8$, so
`fiberLogIndex` is `3` everywhere and bucket `3` is all of `Finset.univ`. -/
example (x : BitString 3) :
    (fiberLogIndex (fun _ : BitString 3 => false) x).val = 3 := by
  have hmem : x ∈ regularityBucket (fun _ : BitString 3 => false) ⟨3, by omega⟩ := by
    rw [mem_regularityBucket]
    ext
    dsimp [fiberLogIndex]
    have hcard : Nat.card {x' : BitString 3 // false = false} = 8 := by
      simp [Nat.card_eq_fintype_card]
    rw [hcard]
    rfl
  exact congrArg Fin.val ((mem_regularityBucket _ _ _).mp hmem)

/-- On the constant map `BitString 3 → Bool`, regularity bucket `3` has cardinality `8`. -/
example :
    (regularityBucket (fun _ : BitString 3 => false) ⟨3, by omega⟩).card = 8 := by
  have huniv : regularityBucket (fun _ : BitString 3 => false) ⟨3, by omega⟩ = Finset.univ := by
    ext x
    simp only [mem_regularityBucket, Finset.mem_univ, iff_true, Fin.ext_iff, fiberLogIndex]
    have hcard : Nat.card {x' : BitString 3 // True} = 8 := by
      simp [Nat.card_eq_fintype_card]
    rw [hcard]
    rfl
  rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rfl

/-- Concrete instantiation of Lemma 5.2 (`exists_regularity_bucket`) on `BitString 4 → Bool`. -/
example (f : BitString 4 → Bool) :
    ∃ r : Fin 5,
      (regularityBucket f r).Nonempty ∧
      16 ≤ 5 * (regularityBucket f r).card ∧
      ∀ x ∈ regularityBucket f r,
        2 ^ r.val ≤ Nat.card {x' : BitString 4 // f x' = f x} ∧
          Nat.card {x' : BitString 4 // f x' = f x} < 2 ^ (r.val + 1) := by
  simpa using exists_regularity_bucket f

/-! ### 2. Concrete entropy and counting tests (Lemma 2.2 and Proof of Theorem 5.2) -/

/-- Lemma 2.2 (`entropy_ge_of_dist_uniform_le`) instantiated on the uniform distribution on
`BitString 5`: since $\mathsf{SD}(U_5, U_5) = 0 \le 1 / 25$, the bound yields $H(U_5) \ge 3$. -/
theorem three_le_entropy_uniform_five :
    3 ≤ PMF.entropy (PMF.uniformOfFintype (BitString 5)) := by
  have h := entropy_ge_of_dist_uniform_le (n := 5) (PMF.uniformOfFintype (BitString 5)) (by simp)
  have h5 : ((5 : ℕ) : ℝ) - 2 = 3 := by norm_num
  linarith

/-- Claim 2 low-point-mass subset bound (`sum_filter_mass_le_ge_of_entropy_ge`) instantiated on
`PMF.uniformOfFintype (BitString 5)` with $B = 3$. -/
example :
    (1 : ℝ) / 5 ≤
      ∑ y ∈ Finset.univ.filter (fun y : BitString 5 =>
        (PMF.uniformOfFintype (BitString 5) y).toReal ≤ (2 : ℝ) ^ (-(0 : ℝ))),
        (PMF.uniformOfFintype (BitString 5) y).toReal := by
  simpa using sum_filter_mass_le_ge_of_entropy_ge (by omega : 1 ≤ 5)
    (PMF.uniformOfFintype (BitString 5)) (B := 3) le_rfl three_le_entropy_uniform_five

/-- Proof of Theorem 5.2, Equation (2) (`card_filter_timeBoundedNat_lt` and
`sum_uniform_timeBoundedNat_lt_le`) instantiated at $n = 4, k = 2$ for $t(n) = n + 1$: at most
$3$ of the $16$ strings of length $4$ have $K^t(x) < 2$, and their uniform probability mass is
at most $1 / 4$. -/
example :
    ((Finset.univ : Finset (BitString 4)).filter fun x =>
      timeBoundedNat (fun n => n + 1) (List.ofFn x) < 2).card < 4 ∧
    (∑ x : BitString 4, (PMF.uniformOfFintype (BitString 4) x).toReal *
      if timeBoundedNat (fun n => n + 1) (List.ofFn x) < 2 then (1 : ℝ) else 0) ≤ 1 / 4 := by
  refine ⟨?_, ?_⟩
  · simpa using card_filter_timeBoundedNat_lt (t := fun n => n + 1) (n := 4) le_rfl 2
  · have h := sum_uniform_timeBoundedNat_lt_le (t := fun n => n + 1) (n := 4) le_rfl 2
    have hpow : (2 : ℝ) ^ (-(2 : ℕ) : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num
    rw [hpow] at h
    exact h

/-! ### 3. Negative-side nonvacuity tests and rounded-log bridges (`Complexity.AverageCase`) -/

/-- `fun _ => 0` is not `MildlyHardOnAverage`, `MildlyHardOnAverageDet`, `MildlyHardOnAverageIO`,
`MildlyHardOnAverageToApproxIO g`, `MildlyHardOnAverageToApproxDet g`,
`MildlyHardOnAverageToApprox g`, or `MildlyHardOnAverageToOneSidedApprox g` for any error
function `g`. -/
example (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverage (fun _ => 0) ∧
    ¬ MildlyHardOnAverageDet (fun _ => 0) ∧
    ¬ MildlyHardOnAverageIO (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApproxIO g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApproxDet g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApprox g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToOneSidedApprox g (fun _ => 0) :=
  ⟨not_mildlyHardOnAverage_zero,
   not_mildlyHardOnAverageDet_zero,
   not_mildlyHardOnAverageIO_zero,
   not_mildlyHardOnAverageToApproxIO_zero g,
   not_mildlyHardOnAverageToApproxDet_zero g,
   not_mildlyHardOnAverageToApprox_zero g,
   not_mildlyHardOnAverageToOneSidedApprox_zero g⟩

/-- Concrete instantiation of the rounded-logarithm comparison lemmas at $n = 6, d = 2$:
$\lceil \log_2 6 \rceil = 3 \le \lfloor \log_2 6 \rfloor + 1 = 3$, and any $v, w \in \mathbb{N}$
with $|(v : \mathbb{R}) - (w : \mathbb{R})| \le 2 \log_2 6$ satisfies `Nat.dist v w ≤ 6`. -/
example (v w : ℕ) (h : |(v : ℝ) - (w : ℝ)| ≤ (2 : ℝ) * Real.logb 2 (6 : ℝ)) :
    Nat.clog 2 6 ≤ Nat.log 2 6 + 1 ∧
    Real.logb 2 (6 : ℝ) ≤ (Nat.log 2 6 + 1 : ℕ) ∧
    Nat.dist v w ≤ 2 * (Nat.log 2 6 + 1) :=
  ⟨nat_clog_two_le_log_two_succ 6,
   real_logb_two_le_nat_log_two_succ (by omega : 1 ≤ 6),
   nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb (by omega : 1 ≤ 6) h⟩

/-! ### 4. End-to-end instantiations of Theorem 5.5, Theorem 5.2, and Theorem 3.1 -/

/-- Instantiating Theorem 5.5 (`OneWay.exists_condEPPRG`) at security exponent $\delta = 2$ and
stretch factor $\gamma = 11$, and chaining with Theorem 5.2 to obtain symmetric PPT approximation
hardness of `timeBoundedNat` at a concrete polynomial time bound $t(n) = p(n) + n$ under the
upper-rounded window $2 (\lfloor \log_2 n \rfloor + 1)$, ceiling window $2 \lceil \log_2 n \rceil$,
floor window $2 \lfloor \log_2 n \rfloor$, and real-valued window $2 \log_2 n$. -/
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ p : Polynomial ℕ,
      (∀ n, n + 1 ≤ p.eval n) ∧
      MildlyHardOnAverageToApprox (fun n => 2 * (Nat.log 2 n + 1))
        (timeBoundedNat fun n => p.eval n + n) ∧
      MildlyHardOnAverageToApprox (fun n => 2 * Nat.clog 2 n)
        (timeBoundedNat fun n => p.eval n + n) ∧
      MildlyHardOnAverageToApprox (fun n => 2 * Nat.log 2 n)
        (timeBoundedNat fun n => p.eval n + n) ∧
      MildlyHardOnAverageToOneSidedApprox (fun n => 2 * (Nat.log 2 n + 1))
        (timeBoundedNat fun n => p.eval n + n) ∧
      MildlyHardOnAverageIO (timeBoundedNat fun n => p.eval n + n) := by
  obtain ⟨G, α, hG⟩ := hf.exists_condEPPRG 2 11
  obtain ⟨p, hp, hhard⟩ :=
    hG.exists_mildlyHardOnAverageToApprox_timeBoundedNat_log_succ 2 (by omega)
  have h_succ := hhard (t := fun n => p.eval n + n) (fun n => Nat.le_add_right _ _)
  have h_clog : MildlyHardOnAverageToApprox (fun n => 2 * Nat.clog 2 n)
      (timeBoundedNat fun n => p.eval n + n) :=
    h_succ.mono fun n => Nat.mul_le_mul_left 2 (nat_clog_two_le_log_two_succ n)
  have h_floor : MildlyHardOnAverageToApprox (fun n => 2 * Nat.log 2 n)
      (timeBoundedNat fun n => p.eval n + n) :=
    h_succ.mono fun n => Nat.mul_le_mul_left 2 (Nat.le_succ _)
  exact ⟨p, hp, h_succ, h_clog, h_floor,
    h_succ.mildlyHardOnAverageToOneSidedApprox,
    h_succ.mildlyHardOnAverage.mildlyHardOnAverageIO⟩

/-- Instantiating `OneWay.exists_eventually_real_abs_sub_le_timeBoundedNat` at $d = 2$ and
$t(n) = p(n)$. -/
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ p q : Polynomial ℕ,
      (∀ n, n + 1 ≤ p.eval n) ∧
      (∀ n, 0 < q.eval n) ∧
      ∀ H : List Bool → ProbComp ℕ, IsPPTOn encBits encNat H →
        ∀ᶠ n in atTop,
          (((BitString.uniformList n).bind fun x =>
            (ProbComp.eval (H x)).map fun v : ℕ =>
              decide (|(v : ℝ) - (timeBoundedNat (fun m => p.eval m) x : ℝ)| ≤
                (2 : ℝ) * Real.logb 2 (n : ℝ))) true).toReal ≤
            1 - 1 / ((q.eval n : ℕ) : ℝ) := by
  obtain ⟨p, hp, h⟩ := hf.exists_eventually_real_abs_sub_le_timeBoundedNat 2
  obtain ⟨q, hq, hH⟩ := h (t := fun m => p.eval m) (fun _ => le_rfl)
  exact ⟨p, q, hp, hq, hH⟩

/-- Instantiating Theorem 3.1 (a) $\Rightarrow$ (b) (`exists_mildlyHardOnAverage_of_exists_oneWay`)
and `OneWay.exists_mildlyHardOnAverageENat_timeBounded` at the exact threshold $t(n) = p(n)$. -/
example (hOWF : ∃ f : List Bool → List Bool, OneWay f) :
    ∃ p : Polynomial ℕ,
      (∀ n, n + 1 ≤ p.eval n) ∧
      MildlyHardOnAverage (timeBoundedNat fun n => p.eval n) ∧
      MildlyHardOnAverageENat (timeBounded fun n => p.eval n) := by
  obtain ⟨f, hf⟩ := hOWF
  obtain ⟨p, hp, hENat⟩ := hf.exists_mildlyHardOnAverageENat_timeBounded
  have hENat_p := hENat (t := fun n => p.eval n) (fun _ => le_rfl)
  have hNat_p := (mildlyHardOnAverageENat_timeBounded_iff hp).mp hENat_p
  exact ⟨p, hp, hNat_p, hENat_p⟩

/-! ### 5. Converse construction (Theorem 4.1) and headline equivalences (Theorem 3.1) -/

/-- Canonical preimage existence
(`LiuPassConverse.exists_liuPassCore_eq_targetImage_timeBoundedNat`) and preimage soundness
(`LiuPassConverse.timeBoundedNat_le_of_liuPassCore_eq_targetImage`) on a concrete $3$-bit string
$y = [1, 0, 1]$ with $t(n) = n + 1$, showing that the soundness hypothesis is nonvacuously
satisfied by an `inputSchedule 3`-bit preimage. -/
example :
    ∃ x : List Bool,
      x.length = LiuPassConverse.inputSchedule 3 ∧
      LiuPassConverse.liuPassCore (fun n => n + 1) 3 x =
        LiuPassConverse.targetImage (timeBoundedNat (fun n => n + 1) [true, false, true])
          [true, false, true] ∧
      timeBoundedNat (fun n => n + 1) [true, false, true] ≤
        timeBoundedNat (fun n => n + 1) [true, false, true] := by
  obtain ⟨x, hx_len, hx_eq⟩ :=
    LiuPassConverse.exists_liuPassCore_eq_targetImage_timeBoundedNat
      (t := fun n => n + 1) (fun _ => le_rfl) (y := [true, false, true]) rfl
  exact ⟨x, hx_len, hx_eq,
    LiuPassConverse.timeBoundedNat_le_of_liuPassCore_eq_targetImage rfl le_rfl hx_eq⟩

/-- Theorem 4.1 (`weakOneWay_reindex_liuPassCore`,
`exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat`) and Theorem 3.1 (b) $\Rightarrow$ (a)
(`exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat`) instantiated on the concrete linear time
bound $t(n) = n + 1$. -/
example (hK : MildlyHardOnAverage (timeBoundedNat fun n => n + 1)) :
    WeakOneWay (OneWayReindex.reindex LiuPassConverse.inputSchedule
      (LiuPassConverse.liuPassCore fun n => n + 1)) ∧
    (∃ f : List Bool → List Bool, WeakOneWay f) ∧
    (∃ F : List Bool → List Bool, OneWay F) := by
  have ht_comp : ComputableInPolyTime (fun n => n + 1) encUnary encUnary := by fun_prop
  exact ⟨weakOneWay_reindex_liuPassCore ht_comp (fun _ => le_rfl) hK,
    exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat ht_comp (fun _ => le_rfl) hK,
    exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat ht_comp (fun _ => le_rfl) hK⟩

/-- Headline equivalences of Theorem 3.1 (a) $\Leftrightarrow$ (b) $\Leftrightarrow$ (c):
one-way functions exist iff $K^t$ is mildly hard on average (both existential-polynomial and
threshold forms, in both `ℕ` and `ℕ∞`), and iff $K^t$ is mildly hard on average to symmetrically
approximate within $d \lfloor \log_2 n \rfloor$. -/
example :
    ((∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        MildlyHardOnAverage (timeBoundedNat fun n => p.eval n))) ∧
    ((∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        MildlyHardOnAverageENat (timeBounded fun n => p.eval n))) ∧
    ((∃ f : List Bool → List Bool, OneWay f) ↔
      (∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverage (timeBoundedNat t))) ∧
    ((∃ f : List Bool → List Bool, OneWay f) ↔
      (∀ d : ℕ, ∃ p : Polynomial ℕ, (∀ n, n + 1 ≤ p.eval n) ∧
        ∀ {t : ℕ → ℕ}, (∀ n, p.eval n ≤ t n) →
          MildlyHardOnAverageToApprox (fun n => d * Nat.log 2 n) (timeBoundedNat t))) :=
  ⟨exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat,
   exists_oneWay_iff_exists_mildlyHardOnAverageENat_timeBounded,
   exists_oneWay_iff_exists_forall_mildlyHardOnAverage_timeBoundedNat,
   exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_timeBoundedNat⟩

end Cslib.Crypto.LiuPassTests
