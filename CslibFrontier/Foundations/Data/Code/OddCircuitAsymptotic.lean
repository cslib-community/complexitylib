/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.PuncturedBallFourier
import CslibFrontier.Foundations.Data.Code.BallVolume
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Linear codes beyond the Gilbert–Varshamov bound

Saglam's theorem [Saglam2027, abstract and Section 3.3]: for fixed `ε > 0` and
`log n ≪ d ≤ (1 / 2 - ε) n` there are binary linear codes of length `n`, minimum distance `d` and
size at least `c_ε n 2 ^ n / ∑_{1 ≤ i < d} C(n, i)`, which is `Ω(n)` times the Gilbert–Varshamov
bound `2 ^ n / (V + 1)`.

`Cslib.Code.exists_parityCheckCode_of_fourierBounds` derives this from Lemma 3.1 of
[Saglam2027], given as the hypothesis that `Cslib.Code.PuncturedBallFourierBounds n w C` holds for
some `C`, `K`, `N` and all `n ≥ N`, `K log₂ n ≤ w ≤ (1 / 2 - ε) n`. The asymptotic quantifiers are
explicit: there are `c > 0`, `K` and `N` such that for all `n ≥ N` and all `d` with
`K log₂ n ≤ d ≤ (1 / 2 - ε) n` some parity-check matrix `H` defines a code of minimum distance at
least `d` with `c n 2 ^ n ≤ |C| ∑_{1 ≤ i < d} C(n, i)`. A single `K` serves all `n`, which is the
uniform reading of `log n ≪ d`. The constant is `c = (log 2 - h(1 / 2 - ε)) / 8`.

The proof follows Section 3.3 with `ζ = 1 / 2`. Let `w = d - 1`, `V = |B|` for the punctured ball
`B`, and `R = log (2 ^ n / V) ≥ (log 2 - h(1 / 2 - ε)) n` by the entropy bound on the ball. Choose
`m` with `τ = V / 2 ^ m ∈ [R / 4, R / 2)`. The moment term of
`Cslib.Code.exists_le_minDist_parityCheckCode_of_moment_tail` is at most
`(sinh 1 - 1) C / n < 1 / 2`, and the tail term is at most
`exp (τ - R + 2 n u log (e / u)) / (2 τ) ≤ 1 / (2 τ)` with `u = log₂ n / w`, because
`u log (e / u) ≤ 2 √u` is small when `w ≥ K log₂ n`. The `m + 1` parity checks leave at least
`2 ^ (n - m - 1) = τ 2 ^ n / (2 V) ≥ (R / 8) 2 ^ n / V` codewords. Saglam's sharper leading
constant `(1 - ζ) / 4`, with `ζ → 0`, is not formalized.

`Cslib.Code.exists_parityCheckCode_of_ks` completes the conditional chain: it derives the same
conclusion from the Kirshner–Samorodnitsky bounds `Cslib.Code.KSThirdMomentBound` and
`Cslib.Code.KSTailBound`, which are imported results stated as hypotheses
(`Cslib.Code.exists_puncturedBallFourierBounds_of_ks`).

## Main results

* `Cslib.Code.exists_parityCheckCode_of_fourierBounds`: linear codes of size
  `c_ε n 2 ^ n / ∑_{1 ≤ i < d} C(n, i)` from Lemma 3.1.
* `Cslib.Code.exists_parityCheckCode_of_ks`: the same from the Kirshner–Samorodnitsky bounds.

## References

* [M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*][Saglam2027], STOC 2027
  submission 1516, abstract and Section 3.3.
-/

public section

namespace Cslib.Code

open Finset Real

/-- `u log (e / u) ≤ 2 √u` for `u > 0`. -/
private theorem mul_log_exp_one_div_le {u : ℝ} (hu : 0 < u) : u * log (exp 1 / u) ≤ 2 * √u := by
  have hs : 0 < √u := sqrt_pos.2 hu
  have hl := one_sub_inv_le_log_of_pos hs
  have hlog : log u = 2 * log √u := by
    have := Real.log_pow (√u) 2
    rw [sq_sqrt hu.le] at this
    rw [this]; norm_num
  have hsu : √u * √u = u := mul_self_sqrt hu.le
  rw [log_div (exp_pos 1).ne' hu.ne', log_exp, hlog]
  have : u * (√u)⁻¹ = √u := by
    calc u * (√u)⁻¹ = √u * √u * (√u)⁻¹ := by rw [hsu]
      _ = √u := by rw [mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hl hu.le]

/-- `sinh 1 - 1 < 1 / 2`. -/
private theorem sinh_one_sub_one_lt : sinh 1 - 1 < 1 / 2 := by
  have h1 : sinh 1 < exp 1 / 2 := by
    rw [sinh_eq]; have := exp_pos (-1); linarith
  have := exp_one_lt_d9
  norm_num at this
  linarith

/-- The moment term: `(V / τ) s τ ^ 3 M ≤ s C / n` when `τ ≤ n` and `M ≤ C / (V n ^ 3)`. -/
private theorem moment_term_le {V τ M C n s : ℝ} (hV : 0 < V) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hM0 : 0 ≤ M) (hM : M ≤ C / (V * n ^ 3)) (hs : 0 ≤ s) :
    V / τ * (s * τ ^ 3 * M) ≤ s * (C / n) := by
  have hn : 0 < n := hτ.trans_le hτn
  have e : V / τ * (s * τ ^ 3 * M) = s * (V * τ ^ 2 * M) := by field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hs
  calc V * τ ^ 2 * M ≤ V * n ^ 2 * M := by gcongr
    _ ≤ V * n ^ 2 * (C / (V * n ^ 3)) := by gcongr
    _ = C / n := by field_simp

/-- The tail exponent: with `R = n log 2 - log V ≥ δ n`, `τ < R / 2` and
`w ≥ K log₂ n` for `K ≥ 64 / δ ^ 2`,
`V e ^ τ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n)) ≤ 1`. -/
private theorem tail_term_le {n w V τ δ K : ℝ} (hV : 0 < V) (hn : 0 < n) (hδ : 0 < δ)
    (hR : δ * n ≤ n * log 2 - log V) (hτ : τ < (n * log 2 - log V) / 2)
    (hlg : 0 < logb 2 n) (hw : K * logb 2 n ≤ w) (hK : 64 / δ ^ 2 ≤ K) :
    V * exp τ * (2 : ℝ) ^ (-n + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) ≤ 1 := by
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  set u := logb 2 n / w with hu
  have hu0 : 0 < u := by positivity
  have huK : u ≤ δ ^ 2 / 64 := by
    have h1 : u ≤ 1 / K := by
      rw [hu, div_le_div_iff₀ hw0 hK0]; linarith
    have h2 : 1 / K ≤ 1 / (64 / δ ^ 2) := one_div_le_one_div_of_le (by positivity) hK
    rw [one_div_div] at h2
    linarith
  have hsq : √u ≤ δ / 8 := by
    rw [show δ / 8 = √((δ / 8) ^ 2) by rw [sqrt_sq (by positivity)]]
    exact sqrt_le_sqrt (by linarith)
  have hlu := mul_log_exp_one_div_le hu0
  rw [two_rpow_tail_eq, ← hu, ← exp_log hV, ← exp_add, ← exp_add]
  refine exp_le_one_iff.2 ?_
  have h' : u * log (exp 1 / u) ≤ 2 * (δ / 8) := hlu.trans (by linarith)
  have : 2 * n * (u * log (exp 1 / u)) ≤ 2 * n * (2 * (δ / 8)) := by gcongr
  have e2 : 2 * n * (2 * (δ / 8)) = δ * n / 2 := by ring
  nlinarith

/-- Some power of two puts `τ = V / 2 ^ m` in `[R / 4, R / 2)` when `0 < R ≤ V`. -/
private theorem exists_div_pow_mem {V R : ℝ} (hR : 0 < R) (hRV : R ≤ V) :
    ∃ m : ℕ, R / 4 ≤ V / 2 ^ m ∧ V / 2 ^ m < R / 2 ∧ 2 ^ (m + 1) ≤ 8 * V / R := by
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (x := 4 * V / R) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hR]; linarith) one_lt_two
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2m]; rw [le_div_iff₀ hR] at hm1; linarith
  · rw [div_lt_iff₀ h2m]; rw [div_lt_iff₀ hR, pow_succ] at hm2; linarith
  · rw [pow_succ, show 8 * V / R = 4 * V / R * 2 by ring]; gcongr

/-- The hypothesis of `exists_le_minDist_parityCheckCode_of_moment_tail` from the moment bound
`𝔼|μ̂|³ ≤ C / (V n ^ 3)` and a tail bound `Pr[|μ̂| > 1 / n] ≤ 2 ^ t` with `V e ^ τ 2 ^ t ≤ 1`,
when `2 < τ < n` and `C < n`. -/
private theorem moment_tail_lt_one {n : ℕ} (B : Finset (Fin n → ZMod 2)) {C τ t : ℝ}
    (hV : (0 : ℝ) < #B) (hτ : 2 < τ) (hτn : τ < n) (hCn : C < n)
    (hM : (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n ≤ C / (#B * n ^ 3))
    (hT : (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n ≤ 2 ^ t)
    (hX : #B * exp τ * (2 : ℝ) ^ t ≤ 1) :
    (#B : ℝ) / τ * ((sinh 1 - 1) * τ ^ 3 * ((∑ y, |charSum B y / #B| ^ 3) / 2 ^ n) +
      exp τ / 2 * ((#{y | 1 / τ < charSum B y / #B} : ℝ) / 2 ^ n)) < 1 := by
  have hτpos : 0 < τ := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hPQ : (#{y | 1 / τ < charSum B y / #B} : ℝ) / 2 ^ n ≤
      (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n := by
    refine div_le_div_of_nonneg_right ?_ h2n.le
    refine Nat.cast_le.2 (card_le_card fun y hy => ?_)
    rw [mem_filter] at hy ⊢
    have : 1 / (n : ℝ) < 1 / τ := one_div_lt_one_div_of_lt hτpos hτn
    exact ⟨hy.1, this.trans (hy.2.trans_le (le_abs_self _))⟩
  have hs0 : 0 ≤ sinh 1 - 1 := by
    have := (self_le_sinh_iff (x := 1)).2 zero_le_one; linarith
  have hs1 : sinh 1 - 1 < 1 / 2 := sinh_one_sub_one_lt
  have hA := moment_term_le hV hτpos hτn.le (by positivity) hM hs0
  have hB : (#B : ℝ) / τ * (exp τ / 2 * ((#{y | 1 / τ < charSum B y / #B} : ℝ) / 2 ^ n)) ≤
      1 / (2 * τ) := by
    calc (#B : ℝ) / τ * (exp τ / 2 * ((#{y | 1 / τ < charSum B y / #B} : ℝ) / 2 ^ n))
        ≤ #B / τ * (exp τ / 2 * (2 : ℝ) ^ t) := by gcongr; exact hPQ.trans hT
      _ = (#B * exp τ * (2 : ℝ) ^ t) / (2 * τ) := by ring
      _ ≤ 1 / (2 * τ) := by gcongr
  have hCn' : C / n < 1 := by rw [div_lt_one hnpos]; exact hCn
  have h2τ : 1 / (2 * τ) < 1 / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [mul_add]
  nlinarith [mul_le_mul_of_nonneg_left hCn'.le hs0]

/-- The size of the code: `2 ^ (n - (m + 1)) ≥ τ 2 ^ n / (2 V)` with `τ = V / 2 ^ m ≥ R / 4`. -/
private theorem le_card_mul {n m N : ℕ} {V R δ : ℝ} (hV2n : V ≤ 2 ^ n) (hR : δ * n ≤ R)
    (hδn : 8 < δ * n) (hτ1 : R / 4 ≤ V / 2 ^ m) (hm : (2 : ℝ) ^ (m + 1) ≤ 8 * V / R)
    (hN : 2 ^ (n - (m + 1)) ≤ N) :
    δ / 8 * n * 2 ^ n ≤ N * V := by
  have hRpos : 0 < R := by linarith
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hmn : (2 : ℝ) ^ (m + 1) < 2 ^ n := by
    refine hm.trans_lt ?_
    rw [div_lt_iff₀ hRpos]
    calc 8 * V ≤ 8 * 2 ^ n := by linarith
      _ < 2 ^ n * (δ * n) := by nlinarith
      _ ≤ 2 ^ n * R := by gcongr
  have hmn' : m + 1 ≤ n := ((pow_lt_pow_iff_right₀ one_lt_two).1 hmn).le
  have hcard : (2 : ℝ) ^ n / 2 ^ (m + 1) ≤ N := by
    rw [div_eq_mul_inv, ← pow_sub₀ (2 : ℝ) two_ne_zero hmn']; exact_mod_cast hN
  have hV : 0 ≤ V := by
    have := (by positivity : (0 : ℝ) ≤ 2 ^ m)
    have : 0 < V / 2 ^ m := lt_of_lt_of_le (by positivity) hτ1
    exact (div_pos_iff_of_pos_right (by positivity)).1 this |>.le
  calc δ / 8 * n * 2 ^ n ≤ 2 ^ n * (V / 2 ^ m) / 2 := by
        have : δ * n / 8 ≤ V / 2 ^ m / 2 := by linarith
        nlinarith
    _ = 2 ^ n / 2 ^ (m + 1) * V := by rw [pow_succ]; field_simp
    _ ≤ N * V := by gcongr

/-- **Saglam's theorem from Lemma 3.1** [Saglam2027, abstract and Section 3.3]: if the moment and
tail estimates `PuncturedBallFourierBounds n w C` hold for all `n ≥ N₀` and
`K₀ log₂ n ≤ w ≤ (1 / 2 - ε) n`, then there are `c > 0`, `K` and `N` such that for all `n ≥ N` and
`K log₂ n ≤ d ≤ (1 / 2 - ε) n` some parity-check matrix over `𝔽₂` defines a linear code of length
`n` and minimum distance at least `d` with `c n 2 ^ n ≤ |C| ∑_{1 ≤ i < d} C(n, i)`. -/
theorem exists_parityCheckCode_of_fourierBounds {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h31 : ∃ C K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, K * logb 2 n ≤ w →
      (w : ℝ) ≤ (1 / 2 - ε) * n → PuncturedBallFourierBounds n w C) :
    ∃ c > 0, ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, K * logb 2 n ≤ d → (d : ℝ) ≤ (1 / 2 - ε) * n →
      ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin n) (ZMod 2),
        (d : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin n → ZMod 2)) ∧
          c * n * 2 ^ n ≤ Nat.card (parityCheckCode H) * ∑ i ∈ Ico 1 d, (n.choose i : ℝ) := by
  obtain ⟨C, K₀, N₀, h31⟩ := h31
  set α : ℝ := 1 / 2 - ε with hα
  have hα0 : 0 ≤ α := by linarith
  have hα2 : α ≤ 1 / 2 := by linarith
  set δ : ℝ := log 2 - binEntropy α with hδdef
  have hδ : 0 < δ :=
    sub_pos.2 (binEntropy_lt_log_two.2 (by rw [hα]; intro h; norm_num at h; linarith))
  set K₁ : ℝ := max K₀ (max (64 / δ ^ 2) 1) with hK₁def
  have hK₀ : K₀ ≤ K₁ := le_max_left _ _
  have h64 : 64 / δ ^ 2 ≤ K₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hK₁ : 1 ≤ K₁ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ / 8, by positivity, 2 * K₁, max N₀ (max 2 (max (⌈C⌉₊ + 1) (⌈8 / δ⌉₊ + 1))), ?_⟩
  intro n hn d hKd hdn
  have hnN₀ : N₀ ≤ n := le_of_max_le_left hn
  have hn' := le_of_max_le_right hn
  have hn2 : 2 ≤ n := le_of_max_le_left hn'
  have hnC : C < n := by
    have := le_of_max_le_left (le_of_max_le_right hn')
    have h := Nat.le_ceil C
    have : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have hn8 : 8 / δ < n := by
    have := le_of_max_le_right (le_of_max_le_right hn')
    have h := Nat.le_ceil (8 / δ)
    have : ((⌈8 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have hδn : 8 < δ * n := by rwa [div_lt_iff₀ hδ, mul_comm] at hn8
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hlg : 1 ≤ logb 2 n := by
    rw [le_logb_iff_rpow_le one_lt_two hnpos, rpow_one]; exact hn2'
  have hd2 : (2 : ℝ) ≤ d := by nlinarith
  obtain ⟨w, rfl⟩ : ∃ w, d = w + 1 := ⟨d - 1, by
    have : 2 ≤ d := by exact_mod_cast hd2
    omega⟩
  push_cast at hKd hdn hd2
  have hw1 : (1 : ℝ) ≤ w := by linarith
  have hw : K₁ * logb 2 n ≤ w := by nlinarith
  have hwα : (w : ℝ) ≤ α * n := by nlinarith
  obtain ⟨hM, hT⟩ := h31 n hnN₀ w
    ((mul_le_mul_of_nonneg_right hK₀ (by linarith)).trans hw) hwα
  set B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1} with hB
  have hVsum : (#B : ℝ) = ∑ i ∈ Ico 1 (w + 1), (n.choose i : ℝ) := by
    rw [hB, card_filter_ne_zero_hammingNorm_lt]; push_cast; rfl
  have hnV : (n : ℝ) ≤ #B := by
    rw [hVsum]
    have h1 : (1 : ℕ) ∈ Ico 1 (w + 1) := mem_Ico.2 ⟨le_rfl, by
      have : (1 : ℝ) ≤ w := hw1; have : 1 ≤ w := by exact_mod_cast this
      omega⟩
    have := single_le_sum (f := fun i => (n.choose i : ℝ)) (fun i _ => by positivity) h1
    simpa using this
  have hVpos : (0 : ℝ) < #B := by linarith
  have hVexp : (#B : ℝ) ≤ exp (n * binEntropy α) := by
    rw [hVsum]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
      (sum_choose_le_exp_mul_binEntropy hα0 hα2 hwα)
    intro i hi; simp only [mem_Ico, mem_range] at hi ⊢; omega
  have hV2n : (#B : ℝ) ≤ 2 ^ n := by
    refine hVexp.trans ?_
    rw [← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_nat_mul]
    gcongr
    exact binEntropy_le_log_two
  have hR : δ * n ≤ n * log 2 - log #B := by
    have := (log_le_log hVpos hVexp).trans_eq (log_exp _)
    rw [hδdef, sub_mul]; linarith [mul_comm (n : ℝ) (binEntropy α), mul_comm (n : ℝ) (log 2)]
  have hRn : n * log 2 - log #B < n := by
    have h1 : 0 ≤ log (#B : ℝ) := log_nonneg (by linarith)
    have := log_two_lt_d9
    norm_num at this
    have : (n : ℝ) * log 2 < n * 1 := mul_lt_mul_of_pos_left (by linarith) hnpos
    linarith
  obtain ⟨m, hτ1, hτ2, hm⟩ :=
    exists_div_pow_mem (V := #B) (R := n * log 2 - log #B) (by linarith) (by linarith)
  have hlgpos : 0 < logb 2 n := by linarith
  have hX := tail_term_le (w := w) (K := K₁) hVpos hnpos hδ hR hτ2 hlgpos hw h64
  obtain ⟨H, hHd, hHcard⟩ := exists_le_minDist_parityCheckCode_of_moment_tail (ι := Fin n) (w + 1) m
    (by
      intro B' τ' μ
      simp only [Fintype.card_fin]
      exact moment_tail_lt_one B hVpos (by linarith) (by linarith) hnC hM hT hX)
  refine ⟨m + 1, H, by exact_mod_cast hHd, ?_⟩
  rw [← hVsum]
  exact le_card_mul hV2n hR hδn hτ1 hm (by simpa only [Fintype.card_fin] using hHcard)

/-- **Saglam's theorem from the Kirshner–Samorodnitsky bounds** [Saglam2027, abstract]: if the
imported bounds `KSThirdMomentBound n w` and `KSTailBound n w` hold for all `w` and all
sufficiently large `n` (Kirshner and Samorodnitsky state them for every `n`), then for
every `0 < ε < 1 / 2` there are `c > 0`, `K` and `N` such that for all `n ≥ N` and
`K log₂ n ≤ d ≤ (1 / 2 - ε) n` some binary linear code of length `n` and minimum distance at least
`d` has at least `c n 2 ^ n / ∑_{1 ≤ i < d} C(n, i)` words. -/
theorem exists_parityCheckCode_of_ks {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hKS : ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, KSThirdMomentBound n w ∧ KSTailBound n w) :
    ∃ c > 0, ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, K * logb 2 n ≤ d → (d : ℝ) ≤ (1 / 2 - ε) * n →
      ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin n) (ZMod 2),
        (d : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin n → ZMod 2)) ∧
          c * n * 2 ^ n ≤ Nat.card (parityCheckCode H) * ∑ i ∈ Ico 1 d, (n.choose i : ℝ) := by
  obtain ⟨N₀, hKS⟩ := hKS
  obtain ⟨K, N, h⟩ := exists_puncturedBallFourierBounds_of_ks hε
  exact exists_parityCheckCode_of_fourierBounds hε hε2
    ⟨2, K, max N N₀, fun n hn w h1 h2 => h n (le_of_max_le_left hn) w h1 h2
      (hKS n (le_of_max_le_right hn) w).1 (hKS n (le_of_max_le_right hn) w).2⟩

end Cslib.Code
