/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorParameters
import CslibFrontier.Foundations.Data.Nat.Choose.MultinomialMax

/-!
# Dimension and trials of the base-`r` reduction from the input

The parameter choices of [ChanItakuraMaYu2026], Theorem 3.4 (pp. 13–14), made explicit and
computed from the input, with the bounds that the error analysis needs.

* **Many balanced pairs** (`pow_mul_le_card_balancedPairs`): for `0 < r`, `r ∣ d`,
  `r ^ d (r !) ^ (d / r) ≤ (d + 1) ^ r #P`, from the exact count `card_balancedPairs_mul` and the
  maximality of the balanced multinomial coefficient (`Nat.pow_mul_pow_factorial_le`). This is the
  explicit lower bound used in the paper's estimate; the full `Θ` estimate remains open.
* **Few trials** (`three_mul_vTrials_le`):
  `3 r ^ d (r !) ^ (d / r) μ ≤ k 4 ^ (e + 2) (d + 1) ^ r + 3 r ^ d (r !) ^ (d / r)` for
  `μ = vTrials k e r d`; with `2 ^ e < 2 r ^ d` this is
  `μ ≤ 64 k (d + 1) ^ r r ^ d / (3 (r!)^{d/r}) + 1`. This is an explicit inequality for given
  `d`, `e`; the source asymptotic trial-count bound `μ = Õ(n̂² / r ^ d)` is not proved here.
* **Few bad primes** (`twenty_mul_card_badPrimesOf_le`): if
  `480 K |A × B| log₂ M ≤ (2 ^ e - 1) 2 ^ e`, at most a `1/20` fraction of the primes of the
  window `[2 ^ e, 2 ^ (e + 1))` are bad (Markov's inequality `card_badPrimesOf_le` and the prime
  density `two_pow_le_card_primeWindow`).
* **The dimension** (`vDim`): `d = r j` for the least `j ≥ 1` with
  `480 (r !) ^ j |A × B| log₂ M ≤ (r ^ (r j) - 1) r ^ (r j)` (`vDimIndex`, `vDimCond`), which exists
  for `r ≥ 2` (`exists_vDimCond`); the paper chooses `p₀² = r ^ (2 d) ≈ 4 n̂² lg² N (r!)^{d/r}`.
  `vDimIndex_min` records that smaller `j` fail the condition.
* **End to end** (`vaverage_miss_le_vDim`): with `d = vDim r n L`, `e = ⌈log₂ r ^ d⌉`,
  `μ = vTrials k e r d` and any threshold `s ≤ balancedSize r d`, all computed from `r`, `k` and
  the input, the base-`r` reduction misses a sum `c ∈ C` with probability at most
  `1/20 + exp (-k)` over a uniform prime of the window and `μ` uniform seeds.

## Differences from the paper and remaining gaps

The constants differ from the paper's (`480` instead of `4`, `log₂ M` instead of `lg² N`, the prime
window `[2 ^ e, 2 ^ (e + 1))` instead of `(r ^ d, 2 r ^ d]`), and the dimension is the least one
meeting an explicit integer condition. The full multinomial `Θ` estimate, the source asymptotic
dimension bound `2 log_ρ n̂ + O(log log N)` and the asymptotic trial-count bound remain open. The expected
running time with these parameters, its conversion to a worst-case bound, amplification to error
`O(1/N)`, and Corollaries 3.5 and 3.6 are not formalized.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.vDimCond`, `vDimIndex`, `vDim`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.pow_mul_le_card_balancedPairs`,
  `three_mul_vTrials_le`, `twenty_mul_card_badPrimesOf_le`, `exists_vDimCond`,
  `vDimIndex_spec`, `vDimIndex_min`, `vaverage_miss_le_vDim`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Nat Real

/-! ### Balanced pairs and trials -/

/-- **Many balanced pairs**: `r ^ d (r !) ^ (d / r) ≤ (d + 1) ^ r #P` for `0 < r` and `r ∣ d`. -/
theorem pow_mul_le_card_balancedPairs {r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    r ^ d * (r !) ^ (d / r) ≤ (d + 1) ^ r * #(balancedPairs r d) := by
  obtain ⟨m, rfl⟩ := hrd
  have hm : r * m / r = m := Nat.mul_div_cancel_left m hr
  have hcount := card_balancedPairs_mul hr (dvd_mul_right r m)
  have hmax := Nat.pow_mul_pow_factorial_le r m
  rw [hm] at hcount ⊢
  have hS : 0 < (m !) ^ r := pow_pos (Nat.factorial_pos _) _
  refine Nat.le_of_mul_le_mul_right ?_ hS
  calc r ^ (r * m) * (r !) ^ m * (m !) ^ r = r ^ (r * m) * (m !) ^ r * (r !) ^ m := by ring
    _ ≤ (r * m + 1) ^ r * (r * m)! * (r !) ^ m := Nat.mul_le_mul_right _ hmax
    _ = (r * m + 1) ^ r * (#(balancedPairs r (r * m)) * (m !) ^ r) := by rw [hcount]; ring
    _ = _ := by ring

/-- **Few trials**: `3 r ^ d (r !) ^ (d / r) vTrials ≤ k 4 ^ (e + 2) (d + 1) ^ r +
3 r ^ d (r !) ^ (d / r)` for `0 < r` and `r ∣ d`. -/
theorem three_mul_vTrials_le {k e r d : ℕ} (hr : 0 < r) (hrd : r ∣ d) :
    3 * r ^ d * (r !) ^ (d / r) * vTrials k e r d ≤
      k * 4 ^ (e + 2) * (d + 1) ^ r + 3 * r ^ d * (r !) ^ (d / r) := by
  set S := ((d / r)!) ^ r
  set P := #(balancedPairs r d)
  set q := k * 4 ^ (e + 2) * S / (3 * (d ! * (r !) ^ (d / r)))
  have hS : 0 < S := pow_pos (Nat.factorial_pos _) _
  have hcount : P * S = d ! * (r !) ^ (d / r) := card_balancedPairs_mul hr hrd
  have hq : 3 * (d ! * (r !) ^ (d / r)) * q ≤ k * 4 ^ (e + 2) * S := Nat.mul_div_le _ _
  have hq' : 3 * P * q ≤ k * 4 ^ (e + 2) := by
    refine Nat.le_of_mul_le_mul_right ?_ hS
    calc 3 * P * q * S = 3 * (P * S) * q := by ring
      _ = 3 * (d ! * (r !) ^ (d / r)) * q := by rw [hcount]
      _ ≤ _ := hq
  have hP := pow_mul_le_card_balancedPairs hr hrd
  have hvt : vTrials k e r d = q + 1 := rfl
  rw [hvt, mul_add, mul_one]
  refine Nat.add_le_add_right ?_ _
  calc 3 * r ^ d * (r !) ^ (d / r) * q = 3 * q * (r ^ d * (r !) ^ (d / r)) := by ring
    _ ≤ 3 * q * ((d + 1) ^ r * P) := Nat.mul_le_mul_left _ hP
    _ = (3 * P * q) * (d + 1) ^ r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hq'

/-! ### Few bad primes -/

/-- **Few bad primes**: if `480 K |A × B| log₂ M ≤ (2 ^ e - 1) 2 ^ e` for `e ≥ 1`, at most a
`1/20` fraction of the primes of `[2 ^ e, 2 ^ (e + 1))` are bad for `c`. -/
theorem twenty_mul_card_badPrimesOf_le {e K c M : ℕ} {A B : List ℕ} (he : 1 ≤ e)
    (hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ M)
    (hcond : 480 * K * (#(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M) ≤ (2 ^ e - 1) * 2 ^ e) :
    20 * #(badPrimesOf e K c A B) ≤ #(primeWindow e) := by
  set X := #(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M
  set b := #(badPrimesOf e K c A B)
  set W := #(primeWindow e)
  have hbad : e * (b * (2 ^ e - 1)) ≤ 4 * K * X := card_badPrimesOf_le hM
  have hW : 2 ^ e ≤ 3 * (e + 1) * W := two_pow_le_card_primeWindow he
  have hpos : 0 < e * ((2 ^ e - 1) * 2 ^ e) := by
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have : 1 ≤ 2 ^ e - 1 := by omega
    positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 20 * b * (e * ((2 ^ e - 1) * 2 ^ e)) = 20 * (e * (b * (2 ^ e - 1))) * 2 ^ e := by ring
    _ ≤ 20 * (4 * K * X) * 2 ^ e := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbad)
    _ ≤ 20 * (4 * K * X) * (3 * (e + 1) * W) := Nat.mul_le_mul_left _ hW
    _ ≤ 20 * (4 * K * X) * (3 * (2 * e) * W) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_))
        omega
    _ = (480 * K * X) * (e * W) := by ring
    _ ≤ ((2 ^ e - 1) * 2 ^ e) * (e * W) := Nat.mul_le_mul_right _ hcond
    _ = W * (e * ((2 ^ e - 1) * 2 ^ e)) := by ring

/-! ### The dimension -/

/-- The dimension condition for `d = r j`, `n = |A × B|` and `L = log₂ M`:
`j ≥ 1` and `480 (r !) ^ j n L ≤ (r ^ (r j) - 1) r ^ (r j)`. -/
@[expose] def vDimCond (r n L j : ℕ) : Prop :=
  1 ≤ j ∧ 480 * (r !) ^ j * (n * L) ≤ (r ^ (r * j) - 1) * r ^ (r * j)

instance (r n L j : ℕ) : Decidable (vDimCond r n L j) := inferInstanceAs (Decidable (_ ∧ _))

/-- For `r ≥ 2` the dimension condition holds for some `j`. -/
theorem exists_vDimCond {r : ℕ} (hr : 2 ≤ r) (n L : ℕ) : ∃ j, vDimCond r n L j := by
  -- `r ^ (2 r) ≥ 4 r !`, so `(r ^ (r j)) ^ 2 ≥ 4 ^ j (r !) ^ j`
  set j := 960 * (n * L) + 1
  have hfac : 4 * r ! ≤ r ^ (2 * r) := by
    have h1 : r ! ≤ r ^ r := Nat.factorial_le_pow r
    have h2 : 4 ≤ r ^ r := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
        _ ≤ r ^ r := Nat.pow_le_pow_right (by omega) hr
    calc 4 * r ! ≤ r ^ r * r ^ r := Nat.mul_le_mul h2 h1
      _ = r ^ (2 * r) := by rw [← pow_add]; ring_nf
  have hpow : 4 ^ j * (r !) ^ j ≤ r ^ (r * j) * r ^ (r * j) := by
    calc 4 ^ j * (r !) ^ j = (4 * r !) ^ j := (mul_pow _ _ _).symm
      _ ≤ (r ^ (2 * r)) ^ j := Nat.pow_le_pow_left hfac j
      _ = r ^ (r * j) * r ^ (r * j) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hj : 2 * (480 * (n * L)) < 4 ^ j := by
    have : j < 4 ^ j := Nat.lt_pow_self (by norm_num)
    omega
  have hbig : 2 ≤ r ^ (r * j) := by
    calc 2 ≤ r := hr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (r * j) := Nat.pow_le_pow_right (by omega) (by
          have : 1 ≤ j := by omega
          nlinarith)
  refine ⟨j, by omega, ?_⟩
  set R := r ^ (r * j)
  have hR : R * R ≤ 2 * ((R - 1) * R) := by
    have : R ≤ 2 * (R - 1) := by omega
    calc R * R ≤ 2 * (R - 1) * R := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have hfpos : 0 < (r !) ^ j := pow_pos (Nat.factorial_pos _) _
  refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 2)
  calc 2 * (480 * (r !) ^ j * (n * L)) = (2 * (480 * (n * L))) * (r !) ^ j := by ring
    _ ≤ 4 ^ j * (r !) ^ j := Nat.mul_le_mul_right _ hj.le
    _ ≤ R * R := hpow
    _ ≤ 2 * ((R - 1) * R) := hR

/-- The index of the dimension: the least `j` with `vDimCond r n L j` (`0` if `r < 2`). -/
@[expose] def vDimIndex (r n L : ℕ) : ℕ :=
  if h : 2 ≤ r then Nat.find (exists_vDimCond h n L) else 0

/-- **The dimension** `d = r · vDimIndex r n L` of the base-`r` reduction for `n = |A × B|` and
`L = log₂ M`. -/
@[expose] def vDim (r n L : ℕ) : ℕ := r * vDimIndex r n L

theorem vDimIndex_spec {r : ℕ} (hr : 2 ≤ r) (n L : ℕ) : vDimCond r n L (vDimIndex r n L) := by
  simp only [vDimIndex, hr, ↓reduceDIte]
  exact Nat.find_spec (exists_vDimCond hr n L)

/-- **The dimension is minimal**: every smaller index fails the condition. -/
theorem vDimIndex_min {r : ℕ} (hr : 2 ≤ r) (n L : ℕ) {j : ℕ} (hj : j < vDimIndex r n L) :
    ¬ vDimCond r n L j := by
  simp only [vDimIndex, hr, ↓reduceDIte] at hj
  exact Nat.find_min (exists_vDimCond hr n L) hj

/-! ### End to end -/

/-- **The base-`r` reduction with parameters from the input** ([ChanItakuraMaYu2026],
Theorem 3.4): for `r ≥ 2`, a target `k`, a sum `c = a + b ∈ C` with `a ∈ A`, `b ∈ B`, and
`|a' + b' - c| ≤ M` on `A × B`, let `n = |A × B|`, `L = log₂ M`, `d = vDim r n L`,
`e = ⌈log₂ r ^ d⌉` and `μ = vTrials k e r d`. For any threshold `s ≤ balancedSize r d`, over a
uniform prime of `[2 ^ e, 2 ^ (e + 1))` and `μ` uniform seeds the reduction misses `c` with
probability at most `1/20 + exp (-k)`. -/
theorem vaverage_miss_le_vDim {r k s M : ℕ} (hr : 2 ≤ r) {A B C : List ℕ} {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ M)
    (hs : s ≤ balancedSize r (vDim r #(A.toFinset ×ˢ B.toFinset) (Nat.log 2 M))) :
    let d := vDim r #(A.toFinset ×ˢ B.toFinset) (Nat.log 2 M)
    let e := Nat.clog 2 (r ^ d)
    (∑ q ∈ primeWindow e,
        missProbOf (fun q σ => vtrialM r d s (p := q) σ) (vTrials k e r d) A B C c q) /
        #(primeWindow e) ≤ 1 / 20 + exp (-k) := by
  intro d e
  set j := vDimIndex r #(A.toFinset ×ˢ B.toFinset) (Nat.log 2 M)
  obtain ⟨hj1, hcond⟩ := vDimIndex_spec hr #(A.toFinset ×ˢ B.toFinset) (Nat.log 2 M)
  have hd : d = r * j := rfl
  have hre : r ^ d ≤ 2 ^ e := Nat.le_pow_clog (by norm_num) _
  have hrd2 : 2 ≤ r ^ d := by
    calc 2 ≤ r := hr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ d := Nat.pow_le_pow_right (by omega) (by rw [hd]; nlinarith)
  have he : 1 ≤ e := Nat.clog_pos (by norm_num) (by omega)
  have hbadc : 480 * (r !) ^ (d / r) * (#(A.toFinset ×ˢ B.toFinset) * Nat.log 2 M) ≤
      (2 ^ e - 1) * 2 ^ e := by
    have hdr : d / r = j := by rw [hd]; exact Nat.mul_div_cancel_left j (by omega)
    rw [hdr]
    refine hcond.trans (Nat.mul_le_mul (Nat.sub_le_sub_right ?_ 1) ?_) <;> rw [← hd] <;> exact hre
  have h20 := twenty_mul_card_badPrimesOf_le (c := c) he hM hbadc
  have hWpos : 0 < #(primeWindow e) := by
    have := two_pow_le_card_primeWindow he
    have : 0 < 2 ^ e := pow_pos (by norm_num) _
    by_contra h
    push Not at h
    have : #(primeWindow e) = 0 := by omega
    simp_all
  have hW : (primeWindow e).Nonempty := card_pos.mp hWpos
  have hmain := vaverage_miss_le_exp (k := k) (by omega) (dvd_mul_right r j) hs hre ha hb habc hc
    hW
  refine hmain.trans (add_le_add_left ?_ _)
  have hWr : (0 : ℝ) < #(primeWindow e) := by exact_mod_cast hWpos
  rw [div_le_div_iff₀ hWr (by norm_num)]
  have : (20 * #(badPrimesOf e ((r !) ^ (r * j / r)) c A B) : ℝ) ≤ #(primeWindow e) := by
    exact_mod_cast h20
  linarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
