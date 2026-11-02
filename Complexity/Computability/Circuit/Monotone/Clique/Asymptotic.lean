/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Essential
public import Complexity.Computability.Circuit.Monotone.Clique.LowerBound
public import Complexity.Foundations.Data.Nat.Choose
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases

/-!
# A `2 ^ √k` lower bound for monotone circuits computing cliques

With width `w` and `w ^ 2` petals, `sunflowerBound (w ^ 2) w ≤ (w + 1) w ^ (3 w)`, and the two error
budgets of Razborov's dichotomy (`Cslib.Circuits.Monotone.lt_size_of_computes_clique`) are
satisfied by the size `64 ^ w = 2 ^ (6 w)` as soon as `w ≥ 16`, `4 w ^ 2 ≤ k - 1` and
`64 w ^ 6 k ≤ n` (`pow_lt_size_of_computes_clique`). Taking `w = ⌊√(k - 1)⌋ / 2` handles
`k ≥ 1025`; for `2 ≤ k ≤ 1024`, every edge is essential (`edgeCount_le_succ_size_of_separates`),
which already forces `(n / 2) ^ 2 - 1` gates.

So for `2 ≤ k` with `k ^ 4 ≤ n`, every monotone circuit computing `k`-clique on `n` vertices has
more than `2 ^ (2 ⌊√k⌋)` gates (`two_pow_two_mul_sqrt_lt_size`), hence more than `2 ^ √k`
(`two_rpow_sqrt_lt_size`). This is the `2 ^ (ε √k)` bound of Razborov and of Alon and Boppana,
in the form of [Arora and Barak, Theorem 14.7][AroraBarak09], with `ε = 1`. The hypothesis
`2 ≤ k` is needed: for `k ≤ 1` and `n ≥ 1`, `k`-clique is constantly `true`, which one gate
computes.

[LogarithmicPetals](Complexity/Computability/Circuit/Monotone/Clique/LogarithmicPetals.html)
gives stronger finite parameter bounds by choosing
`4 * w * t` petals for dyadic `w = 2 ^ t`: the lower bound becomes `w ^ w` when `k ^ 4 ≤ n`,
or remains `64 ^ w` with only `1024 * t ^ 2 * w ^ 4 * k ≤ n` vertices.

The closed approximators of Alon and Boppana give a `2 ^ l` bound under the much weaker
hypothesis `8 l (⌊log₂ n⌋ + 3) k ≤ n` (`Cslib.Circuits.Monotone.two_pow_lt_size_of_separates`), so
for cliques of size about `√n` as well.

Both the method of approximations and the essential-edge bound read a circuit only on graphs with a
`k`-clique and on `(k - 1)`-colourable graphs. So all of these bounds hold for every monotone
circuit separating the two classes (`pow_lt_size_of_separates`,
`two_pow_two_mul_sqrt_lt_size_of_separates`, `two_rpow_sqrt_lt_size_of_separates`), and the bounds
for circuits computing `k`-clique are their instances.

## Main results

* `Cslib.Circuits.Monotone.pow_lt_size_of_separates`,
  `Cslib.Circuits.Monotone.pow_lt_size_of_computes_clique`: the `64 ^ w` lower bound for
  separating circuits and for circuits computing `k`-clique.
* `Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size_of_separates`,
  `Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size`: the `2 ^ (2 ⌊√k⌋)` lower bound for
  separating circuits and for circuits computing `k`-clique.
* `Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique`: the lower bound for the
  monotone circuit complexity of `k`-clique.
* `Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size_of_separates`,
  `Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size`: the real form.

## References

* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985]
* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 14.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique

/-- The sunflower bound at `w ^ 2` petals is at most `(w + 1) w ^ (3 w)`. -/
private theorem sunflower_bound_le (w : ℕ) :
    sunflowerBound (w ^ 2) w ≤ (w + 1) * w ^ (3 * w) := by
  calc sunflowerBound (w ^ 2) w = (w ^ 2 - 1) ^ w * w.factorial := rfl
    _ ≤ (w ^ 2) ^ w * w ^ w := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le _ _) w)
        (Nat.factorial_le_pow w)
    _ = w ^ (3 * w) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ (w + 1) * w ^ (3 * w) := Nat.le_mul_of_pos_left _ (Nat.succ_pos w)

/-- A sixth power is eventually dominated by `4^w`. -/
private theorem mul_pow_six_le_four_pow
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    128 * w ^ 6 ≤ 4 ^ w := by
  induction w, sixteen_le using Nat.le_induction with
  | base => norm_num
  | succ w sixteen_le inductionHypothesis =>
      have step : 16 * (w + 1) ≤ 17 * w := by omega
      have powered := Nat.pow_le_pow_left step 6
      rw [mul_pow, mul_pow] at powered
      have successorBound : (w + 1) ^ 6 ≤ 4 * w ^ 6 := by
        norm_num at powered
        omega
      rw [pow_succ 4 w]
      omega

/-- A quadratic is eventually dominated by `2^w`. -/
private theorem six_mul_succ_sq_lt_two_pow
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    6 * (w + 1) ^ 2 < 2 ^ w := by
  induction w, sixteen_le using Nat.le_induction with
  | base => norm_num
  | succ w sixteen_le inductionHypothesis =>
      have successorBound : (w + 1 + 1) ^ 2 ≤ 2 * (w + 1) ^ 2 := by
        nlinarith
      rw [pow_succ 2 w]
      omega

/-- The positive sunflower factor `sunflowerBound (w ^ 2) w ^ 2 * 64 ^ w` is strictly below
`(64 * w ^ 6) ^ (w + 1)` for `1 ≤ w`. -/
private theorem sunflowerBound_sq_mul_sixtyFour_pow_lt (w : Nat) (one_le : 1 ≤ w) :
    sunflowerBound (w ^ 2) w ^ 2 * 64 ^ w < (64 * w ^ 6) ^ (w + 1) := by
  let familyBound := sunflowerBound (w ^ 2) w
  let ratio := 64 * w ^ 6
  have familyBound_le : familyBound ≤ (w + 1) * w ^ (3 * w) := sunflower_bound_le w
  have ratioPositive : 0 < ratio := by simp only [ratio]; positivity
  have successorSmall : (w + 1) ^ 2 < ratio := by
    have : 1 ≤ w ^ 6 := one_le_pow₀ one_le
    have : (w + 1) ^ 2 ≤ 4 * w ^ 6 := by
      calc
        (w + 1) ^ 2 ≤ (2 * w) ^ 2 := by gcongr; omega
        _ = 4 * w ^ 2 := by ring
        _ ≤ 4 * w ^ 6 := by gcongr; omega
    omega
  calc
    familyBound ^ 2 * 64 ^ w ≤ ((w + 1) * w ^ (3 * w)) ^ 2 * 64 ^ w := by gcongr
    _ = (w + 1) ^ 2 * ratio ^ w := by
      simp only [ratio]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, show 3 * w * 2 = 6 * w by ring]
      ring
    _ < ratio * ratio ^ w :=
      Nat.mul_lt_mul_of_pos_right successorSmall (pow_pos ratioPositive w)
    _ = ratio ^ (w + 1) := by ring

/-- The positive truncation budget at width `w`, `w^2` petals, and size
bound `64^w` is below the number of minimal positive clique graphs. -/
private theorem positive_budget
    (n k w : Nat)
    (one_le : 1 ≤ w)
    (width_succ_le_k : w + 1 ≤ k)
    (verticesLarge : 64 * w ^ 6 * k ≤ n) :
    Positive.errorCap n k (w ^ 2) w * 64 ^ w <
      Nat.choose n k := by
  let familyBound := sunflowerBound (w ^ 2) w
  let ratio := 64 * w ^ 6
  have ratioPositive : 0 < ratio := by simp only [ratio]; positivity
  have budgetSmall : familyBound ^ 2 * 64 ^ w < ratio ^ (w + 1) :=
    sunflowerBound_sq_mul_sixtyFour_pow_lt w one_le
  have containing := Nat.pow_mul_choose_sub_le_choose (q := ratio) (n := n) (k := k)
    (d := w + 1) ratioPositive width_succ_le_k verticesLarge
  have k_le_n : k ≤ n := by
    calc
      k ≤ 64 * w ^ 6 * k := Nat.le_mul_of_pos_left k ratioPositive
      _ ≤ n := verticesLarge
  have remainingPositive : 0 < Nat.choose (n - (w + 1)) (k - (w + 1)) :=
    Nat.choose_pos (Nat.sub_le_sub_right k_le_n _)
  calc
    Positive.errorCap n k (w ^ 2) w * 64 ^ w =
        (familyBound ^ 2 * 64 ^ w) *
          Nat.choose (n - (w + 1)) (k - (w + 1)) := by
      simp only [Positive.errorCap, familyBound]
      ring
    _ < ratio ^ (w + 1) * Nat.choose (n - (w + 1)) (k - (w + 1)) :=
      Nat.mul_lt_mul_of_pos_right budgetSmall remainingPositive
    _ ≤ Nat.choose n k := containing

/-- Six times the squared sunflower bound times `64 ^ w` is strictly below `4 ^ (w ^ 2)` for
`16 ≤ w`. -/
private theorem six_mul_sunflowerBound_sq_mul_sixtyFour_pow_lt (w : Nat) (sixteen_le : 16 ≤ w) :
    6 * sunflowerBound (w ^ 2) w ^ 2 * 64 ^ w < 4 ^ (w ^ 2) := by
  let familyBound := sunflowerBound (w ^ 2) w
  have familyBound_le : familyBound ≤ (w + 1) * w ^ (3 * w) := sunflower_bound_le w
  have exponential := mul_pow_six_le_four_pow w sixteen_le
  have quadratic := six_mul_succ_sq_lt_two_pow w sixteen_le
  calc
    6 * familyBound ^ 2 * 64 ^ w ≤ 6 * ((w + 1) * w ^ (3 * w)) ^ 2 * 64 ^ w := by gcongr
    _ = 6 * (w + 1) ^ 2 * (64 * w ^ 6) ^ w := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, show 3 * w * 2 = 6 * w by ring]
      ring
    _ < 2 ^ w * (64 * w ^ 6) ^ w :=
      Nat.mul_lt_mul_of_pos_right quadratic (pow_pos (by positivity) w)
    _ = (128 * w ^ 6) ^ w := by
      rw [← mul_pow]
      ring_nf
    _ ≤ (4 ^ w) ^ w := Nat.pow_le_pow_left exponential w
    _ = 4 ^ (w ^ 2) := by rw [← pow_mul, pow_two]

/-- The negative plucking budget at width `w`, `w^2` petals, and size bound
`64^w` is below the number of colorings with `k - 1` colors. -/
private theorem negative_budget
    (n k w : Nat)
    (sixteen_le : 16 ≤ w)
    (widthSmall : 4 * w ^ 2 ≤ k - 1)
    (petals_le_n : w ^ 2 ≤ n) :
    2 * negativeGateCap n (k - 1) (w ^ 2) w * 64 ^ w <
      (k - 1) ^ n := by
  let familyBound := sunflowerBound (w ^ 2) w
  let colors := k - 1
  let petals := w ^ 2
  have familySum : 2 * (2 * familyBound + familyBound ^ 2) ≤ 6 * familyBound ^ 2 := by
    have : familyBound ≤ familyBound ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have core : 6 * familyBound ^ 2 * 64 ^ w < 4 ^ petals :=
    six_mul_sunflowerBound_sq_mul_sixtyFour_pow_lt w sixteen_le
  have hcolors : 0 < colors := by
    have : 1 ≤ w ^ 2 := one_le_pow₀ (by omega)
    omega
  have tailPositive : 0 < (w ^ 2) ^ petals * colors ^ (n - petals) :=
    Nat.mul_pos (pow_pos (pow_pos (by omega) 2) _) (pow_pos hcolors _)
  calc
    2 * negativeGateCap n (k - 1) (w ^ 2) w * 64 ^ w =
        2 * (2 * familyBound + familyBound ^ 2) * 64 ^ w *
          ((w ^ 2) ^ petals * colors ^ (n - petals)) := by
      simp only [negativeGateCap, Negative.pluckErrorCap,
        familyBound, colors, petals]
      ring
    _ ≤ 6 * familyBound ^ 2 * 64 ^ w *
          ((w ^ 2) ^ petals * colors ^ (n - petals)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ familySum)
    _ < 4 ^ petals * ((w ^ 2) ^ petals * colors ^ (n - petals)) :=
      Nat.mul_lt_mul_of_pos_right core tailPositive
    _ = (4 * w ^ 2) ^ petals * colors ^ (n - petals) := by
      rw [mul_pow]
      ring
    _ ≤ colors ^ petals * colors ^ (n - petals) := by
      gcongr
    _ = (k - 1) ^ n := by
      rw [← pow_add]
      congr 1
      omega

/-- A monotone circuit separating the graphs with a `k`-clique from the `(k - 1)`-colourable graphs
on `n` vertices has more than `64 ^ w` gates, for every width `w ≥ 16` with `4 w ^ 2 ≤ k - 1` and
`64 w ^ 6 k ≤ n`. -/
theorem pow_lt_size_of_separates {n k w : ℕ} (hw : 16 ≤ w) (hk : 4 * w ^ 2 ≤ k - 1)
    (hn : 64 * w ^ 6 * k ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) : 64 ^ w < C.size := by
  have hsq : 256 ≤ w ^ 2 := by simpa using Nat.pow_le_pow_left hw 2
  have hww : w ≤ w ^ 2 := Nat.le_self_pow (by norm_num) w
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k (by positivity)).trans hn
  exact lt_size_of_separates (p := w ^ 2) (by omega) (by omega) (by omega) (by omega)
    (positive_budget n k w (by omega) (by omega) hn)
    (negative_budget n k w hw hk (by omega)) hC

/-- A monotone circuit computing `k`-clique on `n` vertices has more than `64 ^ w` gates, for every
width `w ≥ 16` with `4 w ^ 2 ≤ k - 1` and `64 w ^ 6 k ≤ n`. -/
theorem pow_lt_size_of_computes_clique {n k w : ℕ} (hw : 16 ≤ w) (hk : 4 * w ^ 2 ≤ k - 1)
    (hn : 64 * w ^ 6 * k ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : 64 ^ w < C.size := by
  have : 1 ≤ w ^ 2 := one_le_pow₀ (by omega)
  exact pow_lt_size_of_separates hw hk hn (separates_of_computes_clique (by omega) hC)

/-- For `1025 ≤ k` with `k ^ 4 ≤ n`, the width `⌊√(k - 1)⌋ / 2` gives the `2 ^ (2 ⌊√k⌋)` bound
through `pow_lt_size_of_separates`. -/
private theorem two_pow_two_mul_sqrt_lt_size_of_separates_of_large {n k : ℕ} (hk : 1025 ≤ k)
    (hn : k ^ 4 ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    2 ^ (2 * Nat.sqrt k) < C.size := by
  let root := Nat.sqrt (k - 1)
  let w := root / 2
  have rootLarge : 32 ≤ root := Nat.le_sqrt.2 (by omega)
  have rootSquare : root ^ 2 ≤ k - 1 := Nat.sqrt_le' (k - 1)
  have sqrtSmall : Nat.sqrt k ≤ root + 1 := by
    have : Nat.sqrt k < root + 2 := by
      rw [Nat.sqrt_lt']
      have successor : k - 1 < (root + 1) ^ 2 := Nat.lt_succ_sqrt' (k - 1)
      have : (root + 1) ^ 2 + 1 ≤ (root + 2) ^ 2 := by nlinarith
      omega
    omega
  have widthSmall : 4 * w ^ 2 ≤ k - 1 := by
    calc 4 * w ^ 2 = (2 * w) ^ 2 := by ring
      _ ≤ root ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ k - 1 := rootSquare
  have verticesLarge : 64 * w ^ 6 * k ≤ n := by
    calc 64 * w ^ 6 * k = (4 * w ^ 2) ^ 3 * k := by ring
      _ ≤ k ^ 3 * k := by gcongr; omega
      _ = k ^ 4 := by ring
      _ ≤ n := hn
  calc 2 ^ (2 * Nat.sqrt k) ≤ 2 ^ (6 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 64 ^ w := by rw [pow_mul]; norm_num
    _ < C.size := pow_lt_size_of_separates (by omega) widthSmall verticesLarge hC

/-- For `2 ≤ k ≤ 1024`, the edge count of `k^4` vertices exceeds
`4^⌊√k⌋ + 1`. -/
private theorem fourPow_sqrt_add_two_le
    (k : Nat)
    (two_le : 2 ≤ k)
    (k_le : k ≤ 1024) :
    4 ^ Nat.sqrt k + 2 ≤ (k ^ 4 / 2) ^ 2 := by
  have monotone : ∀ base, base ≤ k →
      (base ^ 4 / 2) ^ 2 ≤ (k ^ 4 / 2) ^ 2 := fun base below =>
    Nat.pow_le_pow_left (Nat.div_le_div_right (Nat.pow_le_pow_left below 4)) 2
  have sqrtSmall : Nat.sqrt k ≤ 32 := by
    have : Nat.sqrt k < 33 := Nat.sqrt_lt'.2 (by omega)
    omega
  have sqrtPositive : 1 ≤ Nat.sqrt k := Nat.le_sqrt.2 (by omega)
  have squareBelow : Nat.sqrt k ^ 2 ≤ k := Nat.sqrt_le' k
  generalize Nat.sqrt k = root at sqrtSmall sqrtPositive squareBelow ⊢
  interval_cases root
  · exact le_trans (by norm_num) (monotone 2 two_le)
  all_goals exact le_trans (by norm_num) (monotone _ squareBelow)

/-- **The monotone lower bound for separating circuits.** For `2 ≤ k` with `k ^ 4 ≤ n`, every
monotone circuit separating the graphs with a `k`-clique from the `(k - 1)`-colourable graphs on
`n` vertices has more than `2 ^ (2 ⌊√k⌋)` gates. -/
theorem two_pow_two_mul_sqrt_lt_size_of_separates {n k : ℕ} (hk : 2 ≤ k) (hn : k ^ 4 ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    2 ^ (2 * Nat.sqrt k) < C.size := by
  have hkn : k ≤ n := (Nat.le_self_pow (by norm_num) k).trans hn
  rcases Nat.lt_or_ge k 1025 with hk' | hk'
  · have edges := edgeCount_le_succ_size_of_separates hk hkn hC
    have pairs := sq_half_le_edgeCount n
    have arithmetic := fourPow_sqrt_add_two_le k hk (by omega)
    have scaled : (k ^ 4 / 2) ^ 2 ≤ (n / 2) ^ 2 :=
      Nat.pow_le_pow_left (Nat.div_le_div_right hn) 2
    rw [pow_mul]
    norm_num
    omega
  · exact two_pow_two_mul_sqrt_lt_size_of_separates_of_large hk' hn hC

/-- **The monotone lower bound for cliques.** For `2 ≤ k` with `k ^ 4 ≤ n`, every monotone circuit
computing `k`-clique on `n` vertices has more than `2 ^ (2 ⌊√k⌋)` gates. -/
theorem two_pow_two_mul_sqrt_lt_size {n k : ℕ} (hk : 2 ≤ k) (hn : k ^ 4 ≤ n)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    2 ^ (2 * Nat.sqrt k) < C.size :=
  two_pow_two_mul_sqrt_lt_size_of_separates hk hn (separates_of_computes_clique (by omega) hC)

/-- **The monotone circuit complexity of cliques.** For `2 ≤ k` with `k ^ 4 ≤ n`, the monotone
circuit complexity of `k`-clique on `n` vertices exceeds `2 ^ (2 ⌊√k⌋)`. -/
theorem two_pow_two_mul_sqrt_lt_ecomplexity_clique {n k : ℕ} (hk : 2 ≤ k) (hn : k ^ 4 ≤ n) :
    ((2 ^ (2 * Nat.sqrt k) : ℕ) : ℕ∞) < ecomplexity interpretation (single (clique n k)) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _), le_ecomplexity_iff]
  intro C hC
  exact_mod_cast two_pow_two_mul_sqrt_lt_size hk hn hC

/-- **The monotone lower bound for separating circuits, real form.** For `2 ≤ k` with `k ^ 4 ≤ n`,
every monotone circuit separating the graphs with a `k`-clique from the `(k - 1)`-colourable graphs
on `n` vertices has more than `2 ^ √k` gates. -/
theorem two_rpow_sqrt_lt_size_of_separates {n k : ℕ} (hk : 2 ≤ k) (hn : k ^ 4 ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    (2 : ℝ) ^ Real.sqrt k < C.size := by
  have natural := two_pow_two_mul_sqrt_lt_size_of_separates hk hn hC
  have sqrtPositive : 1 ≤ Nat.sqrt k := Nat.le_sqrt.2 (by omega)
  have exponentBound : Real.sqrt k ≤ ((2 * Nat.sqrt k : ℕ) : ℝ) := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := k)
    have : (1 : ℝ) ≤ Nat.sqrt k := by exact_mod_cast sqrtPositive
    push_cast
    linarith
  calc (2 : ℝ) ^ Real.sqrt k ≤ (2 : ℝ) ^ ((2 * Nat.sqrt k : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) exponentBound
    _ = ((2 ^ (2 * Nat.sqrt k) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        push_cast
        rfl
    _ < C.size := by exact_mod_cast natural

/-- **The monotone lower bound for cliques, real form.** For `2 ≤ k` with `k ^ 4 ≤ n`, every
monotone circuit computing `k`-clique on `n` vertices has more than `2 ^ √k` gates. -/
theorem two_rpow_sqrt_lt_size {n k : ℕ} (hk : 2 ≤ k) (hn : k ^ 4 ≤ n)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    (2 : ℝ) ^ Real.sqrt k < C.size :=
  two_rpow_sqrt_lt_size_of_separates hk hn (separates_of_computes_clique (by omega) hC)

end Cslib.Circuits.Monotone
