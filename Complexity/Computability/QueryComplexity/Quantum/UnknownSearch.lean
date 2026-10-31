/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.Grover
public import Complexity.Computability.QueryComplexity.Quantum.Composition
public import Complexity.Foundations.Data.BitString.Sign
public import Complexity.Foundations.Data.BitString.Threshold

/-!
# Quantum search with an unknown number of marked items

Grover's algorithm (`Cslib.Quantum.grover`) finds one of `t` marked items among `N` with
`O(√(N / t))` queries when `t` is known, but a fixed number of iterations can fail badly for an
unknown `t`. Boyer, Brassard, Høyer and Tapp choose the number of iterations at random
[Boyer, Brassard, Høyer, Tapp][BoyerBrassardHoyerTapp1998]. This file formalizes their analysis in
the query model of `Cslib.Quantum.run`, the resulting fixed-budget search algorithm, and an
algorithm computing `OR_N` with error `1/3` and `O(√N)` queries.

**Grover's algorithm with `t` marked items.** Let `θ = searchAngle N t`, so `sin² θ = t / N`.
After `k` queries every marked item has amplitude `sin((2k + 1) θ) / √t` and every other item
`cos((2k + 1) θ) / √(N - t)` (`Cslib.Quantum.run_grover_of_weight`), so a marked item is measured
with probability `sin²((2k + 1) θ)` (`Cslib.Quantum.sum_regProb_run_grover`).

**A random number of iterations.** If the number `j` of iterations is uniform below `m`, a marked
item is found with probability `P_m = 1/2 - sin(4mθ) / (4m sin 2θ)`
(`Cslib.Quantum.sum_sin_sq_div`, from the cosine sum `Cslib.Quantum.two_mul_sin_mul_sum_cos`), so
`P_m ≥ 1/4` when `m ≥ 1 / sin 2θ` (`Cslib.Quantum.le_sum_sin_sq`). If `N ≤ m²`, then
`m ≥ 1 / sin 2θ` for every `1 ≤ t < N` (`Cslib.Quantum.le_mul_sin_two_mul_searchAngle`), and
`t = N` succeeds with certainty.

**The algorithm.** `Cslib.Quantum.randomGrover` realizes the random choice inside the query model:
its workspace holds a classical register `j < m`, prepared in uniform superposition
(`Cslib.Quantum.randomGroverInit`); on the slice where the register holds `j`, Grover's algorithm
runs `j` iterations and is then parked (`Cslib.Quantum.controlled`, `Cslib.Quantum.park`). Every
outcome probability is then the average over `j` (`Cslib.Quantum.sum_regProb_run_randomGrover`).
With `m = ⌊√N⌋ + 1` it makes `⌊√N⌋ ≤ √N` queries from a unit initial state and measures a marked
item with probability at least `1/4` on every input with at least one marked item
(`Cslib.Quantum.randomGrover_search`), whatever their number.

**Deciding `OR_N`.** With the larger range `m = 4 (⌊√N⌋ + 1)` (`Cslib.Quantum.orRange`), so that
`m sin 2θ ≥ 4`, a marked item is found with probability at least `7/16`. A stage
(`Cslib.Quantum.orStage`) runs `randomGrover` and then checks the measured index with one more
query (`Cslib.Quantum.check`), so it accepts with exactly the success probability `P`, which is `0`
on the all-zero input. Running the stage twice (`Cslib.Quantum.orSearch`, `Cslib.Quantum.twice`)
and accepting when either check succeeds gives acceptance probability `1 - (1 - P)²`
(`Cslib.Quantum.measureProb_run_orSearch`): `0` if `OR_N(x) = 0`, and at least
`1 - (9/16)² > 2/3` if `OR_N(x) = 1`. So `8 (⌊√N⌋ + 1) ≤ 8√N + 8` queries compute `OR_N` with
error at most `1/3` (`Cslib.Quantum.orSearch_spec`), matching the polynomial-method lower bound
`N ≤ 16 T²` (`Cslib.Quantum.card_le_sixteen_mul_sq_of_threshold_one_right`) up to a constant.

**Source mapping** (numbering of arXiv:quant-ph/9605034v1). The closed form is equation (3) of §3,
where `k_j` and `ℓ_j` are the amplitudes of a marked and an unmarked item after `j` iterations and
`sin² θ = t / N`; here it is proved for every `0 ≤ t ≤ N`. Queries are counted as in
`Cslib.Quantum.run`, one application of the phase oracle per Grover iteration, whereas BBHT count
two table look-ups per iteration with a bit oracle (§3.1). In §4, Lemma 1 is the sum
`∑_{j < m} cos(α + 2βj)`, of which `two_mul_sin_mul_sum_cos` is the special case `α = β` stated
there, multiplied out by `2 sin α`. Lemma 2 is `sum_sin_sq_div`, and its bound `P_m ≥ 1/4` for
`m ≥ 1 / sin 2θ` follows from `le_sum_sin_sq`. BBHT then search with a range `m` growing by a
factor `λ = 6/5` after each failed round, observe and check the outcome, and prove an expected
`O(√(N / t))` time for `1 ≤ t ≤ 3N/4` (Theorem 3); they dispose of `t > 3N/4` by classical
sampling and of `t = 0` by a time-out. Here the range is fixed, which gives a single algorithm
with a fixed query budget `⌊√N⌋`, and its success probability is bounded for every `t ≥ 1` at
once, including `t > 3N/4`. This fixed-budget packaging, the bound for `1 ≤ t < N` from
`c² N ≤ m²`, the realization of the random `j` by a classical register in the workspace, and the
decision algorithm for `OR_N` (a check query and two independent stages, with its constants) are
not from the source; they are original here.

## Main definitions

* `Cslib.Quantum.searchAngle`: the angle `θ` with `sin² θ = t / N`.
* `Cslib.Quantum.randomGrover`, `Cslib.Quantum.randomGroverInit`: search with a random number of
  Grover iterations below `m`.
* `Cslib.Quantum.orSearch`, `Cslib.Quantum.orSearchInit`, `Cslib.Quantum.orAccept`: the decision
  algorithm for `OR_N`.

## Main results

* `Cslib.Quantum.run_grover_of_weight`: the state of Grover's algorithm with `t` marked items.
* `Cslib.Quantum.sum_regProb_run_grover`: its success probability `sin²((2k + 1) θ)`.
* `Cslib.Quantum.two_mul_sin_mul_sum_cos`, `Cslib.Quantum.sum_sin_sq_div`,
  `Cslib.Quantum.le_sum_sin_sq`: Lemmas 1 and 2 of [Boyer, Brassard, Høyer,
  Tapp][BoyerBrassardHoyerTapp1998].
* `Cslib.Quantum.sum_regProb_run_randomGrover`: the success probability of `randomGrover`.
* `Cslib.Quantum.le_sum_regProb_run_randomGrover`: if `c² N ≤ m²`, a marked item is found with
  probability at least `1/2 - 1/(4c)`.
* `Cslib.Quantum.randomGrover_search`: `⌊√N⌋` queries find a marked item with probability at
  least `1/4`, for every number of marked items.
* `Cslib.Quantum.orSearch_spec`: `8 (⌊√N⌋ + 1)` queries compute `OR_N` with error at most `1/3`.

## References

* [M. Boyer, G. Brassard, P. Høyer, A. Tapp, *Tight Bounds on Quantum
  Searching*][BoyerBrassardHoyerTapp1998]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Real BitString

variable {N : ℕ}

/-! ### Grover's algorithm with several marked items -/

/-- The angle `θ ∈ [0, π / 2]` with `sin² θ = t / N`. -/
noncomputable def searchAngle (N t : ℕ) : ℝ := Real.arcsin (Real.sqrt (t / N))

private theorem div_le_one_of_le' {t : ℕ} (ht : t ≤ N) : (t : ℝ) / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast ht

theorem sin_searchAngle {t : ℕ} (ht : t ≤ N) :
    Real.sin (searchAngle N t) = Real.sqrt (t / N) := by
  refine Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((t : ℝ) / N)]) ?_
  rw [Real.sqrt_le_one]
  exact div_le_one_of_le' ht

theorem cos_searchAngle (t : ℕ) :
    Real.cos (searchAngle N t) = Real.sqrt (1 - t / N) := by
  rw [searchAngle, Real.cos_arcsin, Real.sq_sqrt (by positivity)]

theorem searchAngle_nonneg (N t : ℕ) : 0 ≤ searchAngle N t :=
  Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)

theorem searchAngle_self (hN : 0 < N) : searchAngle N N = π / 2 := by
  rw [searchAngle, div_self (by exact_mod_cast hN.ne'), Real.sqrt_one, Real.arcsin_one]

theorem searchAngle_zero (N : ℕ) : searchAngle N 0 = 0 := by
  simp [searchAngle]

/-- **Grover's algorithm with any number of marked items** [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998]: on an input with `t` marked items, after `k` queries, with
control bit `1`, every marked item has amplitude `sin((2k + 1) θ) / √t` and every other item
`cos((2k + 1) θ) / √(N - t)`, where `sin² θ = t / N`; with control bit `0`, every amplitude is
`0`. -/
theorem run_grover_of_weight (hN : 0 < N) (x : Fin N → Bool) (k : ℕ) (p : Fin N × Bool × Unit) :
    (run (grover N) (uniform N) x k).ofLp p =
      if p.2.1 then ((if x p.1 then
          Real.sin ((2 * k + 1) * searchAngle N (weight x)) / Real.sqrt (weight x)
        else Real.cos ((2 * k + 1) * searchAngle N (weight x)) / Real.sqrt (N - weight x) : ℝ) :
          ℂ) else 0 := by
  set t := weight x with ht_def
  have htN : t ≤ N := weight_le_length x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have htN' : (t : ℝ) ≤ N := by exact_mod_cast htN
  set θ := searchAngle N t
  set sN := Real.sqrt N
  set st := Real.sqrt t
  set su := Real.sqrt (N - t)
  have hsN : 0 < sN := Real.sqrt_pos.mpr hN0
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt hN0.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt (Nat.cast_nonneg t)
  have hsu2 : su ^ 2 = N - t := Real.sq_sqrt (by linarith)
  have hs : Real.sin θ = st / sN := by
    rw [sin_searchAngle htN, Real.sqrt_div' _ hN0.le]
  have hc : Real.cos θ = su / sN := by
    rw [cos_searchAngle, show (1 : ℝ) - t / N = (N - t) / N by field_simp,
      Real.sqrt_div' _ hN0.le]
  -- A marked item exists only if `t ≠ 0`, and an unmarked one only if `t ≠ N`.
  have hmarked : ∀ i, x i = true → st ≠ 0 := by
    intro i hi
    refine (Real.sqrt_pos.mpr ?_).ne'
    have : 0 < t := card_pos.mpr ⟨i, by simp [hi]⟩
    exact_mod_cast this
  have hunmarked : ∀ i, x i = false → su ≠ 0 := by
    intro i hi
    refine (Real.sqrt_pos.mpr ?_).ne'
    have h1 : 0 < #{j | x j = false} := card_pos.mpr ⟨i, by simp [hi]⟩
    have h2 := card_filter_eq_false_eq_card_sub_weight x
    rw [Fintype.card_fin] at h2
    have : t < N := by omega
    have : (t : ℝ) < N := by exact_mod_cast this
    linarith
  induction k generalizing p with
  | zero =>
    obtain ⟨i, c, u⟩ := p
    simp only [run, grover, LinearIsometry.id_apply, uniform, PiLp.toLp_apply, Nat.cast_zero,
      mul_zero, zero_add, one_mul]
    cases c
    · rfl
    simp only [ite_true]
    congr 1
    cases hi : x i
    · simp only [Bool.false_eq_true, ite_false, hc]
      field_simp [hunmarked i hi]
      rfl
    · simp only [ite_true, hs]
      field_simp [hmarked i hi]
      rfl
  | succ k ih =>
    set S := Real.sin ((2 * k + 1) * θ) with hS
    set C := Real.cos ((2 * k + 1) * θ) with hC
    -- The total control-`1` amplitude after the oracle.
    have hta : (t : ℝ) * (S / st) = st * S := by
      by_cases h : st = 0
      · have : (t : ℝ) = 0 := by rw [← hst2, h]; ring
        simp [h, this]
      · field_simp
        rw [← hst2]
        ring
    have hub : ((N : ℝ) - t) * (C / su) = su * C := by
      by_cases h : su = 0
      · have : (N : ℝ) - t = 0 := by rw [← hsu2, h]; ring
        simp [h, this]
      · field_simp
        rw [← hsu2]
        ring
    have hsum : ∑ q : Fin N × Bool × Unit, (if q.2.1 then (phaseOracle x
        (run (grover N) (uniform N) x k)).ofLp q else 0) = ((-(st * S) + su * C : ℝ) : ℂ) := by
      simp only [phaseOracle_apply, ih, Fintype.sum_prod_type, Fintype.univ_unit, sum_singleton,
        Fintype.sum_bool, ite_true, Bool.true_and, Bool.false_eq_true, ite_false, add_zero]
      have hterm : ∀ i : Fin N, (if x i = true then (-1 : ℂ) else 1) *
          ((if x i = true then S / st else C / su : ℝ) : ℂ) =
            if x i = true then ((-(S / st) : ℝ) : ℂ) else ((C / su : ℝ) : ℂ) := by
        intro i
        by_cases h : x i = true <;> simp [h]
      rw [sum_congr rfl fun i _ => hterm i, sum_ite, sum_const, sum_const]
      have hcardT : #(univ.filter fun i : Fin N => x i = true) = t := rfl
      have hcardF : #(univ.filter fun i : Fin N => ¬x i = true) = N - t := by
        simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight x
      rw [hcardT, hcardF, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub htN]
      rw [← hta, ← hub]
      push_cast
      ring
    have harg : (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ = (2 * k + 1) * θ + 2 * θ := by
      push_cast
      ring
    simp only [run, grover, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [diffusion_apply hN, hsum, phaseOracle_apply, ih]
    obtain ⟨i, c, u⟩ := p
    cases c
    · simp
    simp only [Bool.true_and, ite_true]
    cases hi : x i
    · have hsu0 := hunmarked i hi
      have hreal : 2 * ((N : ℝ)⁻¹ * (-(st * S) + su * C)) - C / su =
          Real.cos ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) / su := by
        rw [harg, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, ← hS, ← hC]
        field_simp
        rw [← hsN2]
        ring
      simp only [Bool.false_eq_true, ite_false]
      rw [← hreal]
      push_cast
      ring
    · have hst0 := hmarked i hi
      have hreal : 2 * ((N : ℝ)⁻¹ * (-(st * S) + su * C)) + S / st =
          Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) / st := by
        have hrel : sN ^ 2 = st ^ 2 + su ^ 2 := by rw [hsN2, hst2, hsu2]; ring
        rw [harg, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc, ← hS, ← hC]
        field_simp
        rw [← hsN2]
        linear_combination (2 * S * sN ^ 2) * hrel
      simp only [ite_true]
      rw [← hreal]
      push_cast
      ring

/-- **The success probability of Grover's algorithm with any number of marked items** [Boyer,
Brassard, Høyer, Tapp][BoyerBrassardHoyerTapp1998]: after `k` queries, a marked item is measured
with probability `sin²((2k + 1) θ)`, where `sin² θ = t / N` for `t` marked items. -/
theorem sum_regProb_run_grover (hN : 0 < N) (x : Fin N → Bool) (k : ℕ) :
    ∑ i with x i = true, regProb (run (grover N) (uniform N) x k) i =
      Real.sin ((2 * k + 1) * searchAngle N (weight x)) ^ 2 := by
  have hterm : ∀ i ∈ (univ.filter fun i : Fin N => x i = true),
      regProb (run (grover N) (uniform N) x k) i =
        (Real.sin ((2 * k + 1) * searchAngle N (weight x)) / Real.sqrt (weight x)) ^ 2 := by
    intro i hi
    simp only [regProb_eq_sum, run_grover_of_weight hN, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.univ_unit, sum_singleton, ite_true, Bool.false_eq_true, ite_false, norm_zero,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, (mem_filter.mp hi).2]
    ring
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  change (weight x : ℝ) * _ = _
  rcases Nat.eq_zero_or_pos (weight x) with h0 | hpos
  · simp [h0, searchAngle_zero]
  · have : (0 : ℝ) < weight x := by exact_mod_cast hpos
    rw [div_pow, Real.sq_sqrt this.le]
    field_simp

/-! ### Random iteration counts -/

/-- **The cosine sum** of [Boyer, Brassard, Høyer, Tapp][BoyerBrassardHoyerTapp1998] (Lemma 1 with
`α = β`): `2 sin α ∑_{j < m} cos((2j + 1) α) = sin(2mα)`. -/
theorem two_mul_sin_mul_sum_cos (α : ℝ) (m : ℕ) :
    2 * Real.sin α * ∑ j ∈ range m, Real.cos ((2 * j + 1) * α) = Real.sin (2 * m * α) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih, Real.two_mul_sin_mul_cos]
    have h1 : α - (2 * m + 1) * α = -(2 * m * α) := by ring
    have h2 : α + (2 * m + 1) * α = 2 * ((m + 1 : ℕ) : ℝ) * α := by push_cast; ring
    rw [h1, h2, Real.sin_neg]
    ring

/-- The sum of the success probabilities `sin²((2j + 1) θ)` for `j < m` is
`m / 2 - (1/2) ∑_{j < m} cos((2j + 1) 2θ)`. -/
private theorem sum_sin_sq_eq (θ : ℝ) (m : ℕ) :
    ∑ j ∈ range m, Real.sin ((2 * j + 1) * θ) ^ 2 =
      m / 2 - (∑ j ∈ range m, Real.cos ((2 * j + 1) * (2 * θ))) / 2 := by
  have h : ∀ j : ℕ, Real.sin ((2 * j + 1) * θ) ^ 2 =
      1 / 2 - Real.cos ((2 * j + 1) * (2 * θ)) / 2 := fun j => by
    rw [Real.sin_sq_eq_half_sub]
    ring_nf
  simp only [h, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
  ring

/-- **The average success probability of a random number of iterations** [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998] (Lemma 2): for `j` uniform below `m`, a marked item is found
with probability `P_m = 1/2 - sin(4mθ) / (4m sin 2θ)`, where `sin² θ = t / N`. -/
theorem sum_sin_sq_div (θ : ℝ) {m : ℕ} (hm : 0 < m) (hθ : Real.sin (2 * θ) ≠ 0) :
    (∑ j ∈ range m, Real.sin ((2 * j + 1) * θ) ^ 2) / m =
      1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) := by
  have hcos := two_mul_sin_mul_sum_cos (2 * θ) m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [sum_sin_sq_eq, show 4 * (m : ℝ) * θ = 2 * m * (2 * θ) by ring, ← hcos]
  generalize ∑ j ∈ range m, Real.cos ((2 * j + 1) * (2 * θ)) = σ
  field_simp
  ring

/-- **A lower bound on the average success probability** [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998] (Lemma 2): if `sin 2θ > 0`, then
`∑_{j < m} sin²((2j + 1) θ) ≥ m / 2 - 1 / (4 sin 2θ)`. In particular `P_m ≥ 1/4` when
`m ≥ 1 / sin 2θ`. -/
theorem le_sum_sin_sq (θ : ℝ) (m : ℕ) (hθ : 0 < Real.sin (2 * θ)) :
    m / 2 - 1 / (4 * Real.sin (2 * θ)) ≤ ∑ j ∈ range m, Real.sin ((2 * j + 1) * θ) ^ 2 := by
  have hcos := two_mul_sin_mul_sum_cos (2 * θ) m
  have hle : 2 * Real.sin (2 * θ) * ∑ j ∈ range m, Real.cos ((2 * j + 1) * (2 * θ)) ≤ 1 :=
    hcos ▸ Real.sin_le_one _
  rw [sum_sin_sq_eq]
  have : ∑ j ∈ range m, Real.cos ((2 * j + 1) * (2 * θ)) ≤ 1 / (2 * Real.sin (2 * θ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h4 : 1 / (4 * Real.sin (2 * θ)) = 1 / (2 * Real.sin (2 * θ)) / 2 := by
    field_simp
    ring
  linarith

/-- For `1 ≤ t < N` marked items and `c² N ≤ m²`, the range `m` is at least `c / sin 2θ`. -/
theorem le_mul_sin_two_mul_searchAngle {t m : ℕ} {c : ℝ} (ht : 1 ≤ t) (htN : t < N) (hc : 0 ≤ c)
    (hm : c ^ 2 * N ≤ m ^ 2) : c ≤ m * Real.sin (2 * searchAngle N t) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htN1 : (t : ℝ) + 1 ≤ N := by exact_mod_cast htN
  rw [Real.sin_two_mul, sin_searchAngle htN.le, cos_searchAngle]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ t / N by positivity)
  have hco := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - t / N by
    rw [sub_nonneg, div_le_one hN0]; linarith)
  set a := Real.sqrt (t / N)
  set b := Real.sqrt (1 - t / N)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  -- `(m sin 2θ)² = 4 m² t (N - t) / N² ≥ c²`, since `4 t (N - t) ≥ N`.
  have hkey : (N : ℝ) ≤ 4 * t * (N - t) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * t - 1 by linarith)
      (show (0 : ℝ) ≤ 2 * (N - t) - 1 by linarith)]
  have hab : a ^ 2 * b ^ 2 = t * (N - t) / N ^ 2 := by
    rw [hs, hco]
    field_simp
  have hsq : c ^ 2 ≤ (m * (2 * a * b)) ^ 2 := by
    have : (m * (2 * a * b)) ^ 2 = 4 * m ^ 2 * (t * (N - t) / N ^ 2) := by
      rw [← hab]
      ring
    rw [this]
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    rw [show 4 * (m : ℝ) ^ 2 * (t * (N - t) / N ^ 2) = m ^ 2 * (4 * t * (N - t)) / N ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hc2]
  exact (pow_le_pow_iff_left₀ hc (by positivity) two_ne_zero).mp hsq

/-! ### Searching with an unknown number of marked items -/

/-- The isometries of **search with a random number of Grover iterations** below `m`, after
[Boyer, Brassard, Høyer, Tapp][BoyerBrassardHoyerTapp1998]: a classical register `j < m` holds the
number of iterations; on the slice where it holds `j`, Grover's algorithm runs `j` iterations and
is then parked. -/
noncomputable def randomGrover (N m : ℕ) :
    ℕ → State N (Unit × Fin m) →ₗᵢ[ℂ] State N (Unit × Fin m) :=
  fun s => controlled fun j => park (j : ℕ) (grover N) s

/-- The initial state of `randomGrover`: the uniform superposition of the query indices, with
control bit `1`, and of the iteration counts `j < m`. -/
noncomputable def randomGroverInit (N m : ℕ) : State N (Unit × Fin m) :=
  WithLp.toLp 2 fun p => if p.2.1 then (((Real.sqrt N)⁻¹ * (Real.sqrt m)⁻¹ : ℝ) : ℂ) else 0

theorem slice_randomGroverInit (m : ℕ) (j : Fin m) :
    slice j (randomGroverInit N m) = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) • uniform N := by
  ext p
  simp only [slice_apply, randomGroverInit, uniform, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem norm_randomGroverInit (hN : 0 < N) {m : ℕ} (hm : 0 < m) : ‖randomGroverInit N m‖ = 1 := by
  have h : ‖randomGroverInit N m‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum_slice]
    simp only [slice_randomGroverInit, norm_smul, norm_uniform hN, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    field_simp
  nlinarith [norm_nonneg (randomGroverInit N m)]

/-- After `T ≥ m - 1` queries, the slice of `randomGrover` where the register holds `j` is the
state of Grover's algorithm after `j` queries, parked and scaled by `1 / √m`. -/
theorem slice_run_randomGrover (hN : 0 < N) {m T : ℕ} (hT : m ≤ T + 1) (x : Fin N → Bool)
    (j : Fin m) :
    slice j (run (randomGrover N m) (randomGroverInit N m) x T) =
      (((Real.sqrt m)⁻¹ : ℝ) : ℂ) • flipCtrl (run (grover N) (uniform N) x j) := by
  have hctrl : ∀ i' w, (run (grover N) (uniform N) x j).ofLp (i', false, w) = 0 := by
    intro i' w
    simp [run_grover_of_weight hN]
  rw [show run (randomGrover N m) = run (fun s => controlled fun (j : Fin m) =>
      park (j : ℕ) (grover N) s) from rfl, slice_run, slice_randomGroverInit, run_smul,
    run_park hctrl (by omega)]

/-- After `T ≥ m - 1` queries every branch of `randomGrover` is parked: the control bit is `0`. -/
theorem run_randomGrover_ctrl (hN : 0 < N) {m T : ℕ} (hT : m ≤ T + 1) (x : Fin N → Bool)
    (i : Fin N) (w : Unit × Fin m) :
    (run (randomGrover N m) (randomGroverInit N m) x T).ofLp (i, true, w) = 0 := by
  have := congrArg (fun φ => φ.ofLp (i, true, w.1)) (slice_run_randomGrover hN hT x w.2)
  simp only [slice_apply, PiLp.smul_apply, flipCtrl_apply, smul_eq_mul, Bool.not_true,
    run_grover_of_weight hN, Bool.false_eq_true, ite_false, mul_zero] at this
  exact this

/-- **The success probability of a random number of iterations**: after `T ≥ m - 1` queries,
`randomGrover` measures a marked item with probability
`(1 / m) ∑_{j < m} sin²((2j + 1) θ)`, the average over `j < m` of the success probability of `j`
Grover iterations. -/
theorem sum_regProb_run_randomGrover (hN : 0 < N) {m T : ℕ} (hT : m ≤ T + 1) (x : Fin N → Bool) :
    ∑ i with x i = true, regProb (run (randomGrover N m) (randomGroverInit N m) x T) i =
      (∑ j ∈ range m, Real.sin ((2 * j + 1) * searchAngle N (weight x)) ^ 2) / m := by
  have hslice : ∀ (j : Fin m) i, regProb (slice j
      (run (randomGrover N m) (randomGroverInit N m) x T)) i =
        (m : ℝ)⁻¹ * regProb (run (grover N) (uniform N) x j) i := by
    intro j i
    rw [slice_run_randomGrover hN hT, regProb_smul, regProb_flipCtrl, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  simp only [regProb_eq_sum_slice, hslice]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range (fun j => Real.sin ((2 * j + 1) *
    searchAngle N (weight x)) ^ 2), sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, sum_regProb_run_grover hN, inv_mul_eq_div]

/-- **Quantum search with an unknown number of marked items** [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998]: if `c² N ≤ m²` with `c > 0`, then on every input with at least
one marked item, `randomGrover` measures a marked item with probability at least `1/2 - 1/(4c)`
after `m - 1` queries. -/
theorem le_sum_regProb_run_randomGrover (hN : 0 < N) {m : ℕ} {c : ℝ} (hc : 0 < c)
    (hm : c ^ 2 * N ≤ m ^ 2) (x : Fin N → Bool) (hx : ∃ i, x i = true) :
    1 / 2 - 1 / (4 * c) ≤ ∑ i with x i = true,
      regProb (run (randomGrover N m) (randomGroverInit N m) x (m - 1)) i := by
  have hm' : (0 : ℝ) < m := by
    have : (0 : ℝ) < c ^ 2 * N := by positivity
    nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) m]
  have hm0 : 0 < m := by exact_mod_cast hm'
  rw [sum_regProb_run_randomGrover hN (by omega), le_div_iff₀ hm']
  obtain ⟨i, hi⟩ := hx
  have ht : 1 ≤ weight x := card_pos.mpr ⟨i, by simp [hi]⟩
  rcases (weight_le_length x).lt_or_eq with htN | htN
  · -- `1 ≤ t < N`: Lemma 2 with `m sin 2θ ≥ c`.
    have hsin := le_mul_sin_two_mul_searchAngle ht htN hc.le hm
    have hpos : 0 < Real.sin (2 * searchAngle N (weight x)) := by
      by_contra h
      nlinarith [not_lt.mp h]
    have := le_sum_sin_sq (searchAngle N (weight x)) m hpos
    have h4 : 1 / (4 * Real.sin (2 * searchAngle N (weight x))) ≤ m / (4 * c) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have : (1 / 2 - 1 / (4 * c)) * m = m / 2 - m / (4 * c) := by ring
    linarith
  · -- `t = N`: every number of iterations succeeds.
    have hone : ∀ j : ℕ, Real.sin ((2 * j + 1) * searchAngle N (weight x)) ^ 2 = 1 := by
      intro j
      rw [htN, searchAngle_self hN, Real.sin_sq,
        show (2 * (j : ℝ) + 1) * (π / 2) = j * π + π / 2 by ring, Real.cos_add_pi_div_two,
        Real.sin_nat_mul_pi]
      ring
    simp only [hone, sum_const, card_range, nsmul_eq_mul, mul_one]
    have : 0 < 1 / (4 * c) := by positivity
    nlinarith

/-- **Quantum search with an unknown number of marked items in `⌊√N⌋` queries** [Boyer, Brassard,
Høyer, Tapp][BoyerBrassardHoyerTapp1998]: with iteration counts below `⌊√N⌋ + 1`, `randomGrover`
starts from a unit state, makes `⌊√N⌋ ≤ √N` queries, and on every input with at least one marked
item measures a marked item with probability at least `1/4`. -/
theorem randomGrover_search (hN : 0 < N) :
    ‖randomGroverInit N (Nat.sqrt N + 1)‖ = 1 ∧ (Nat.sqrt N : ℝ) ≤ Real.sqrt N ∧
      ∀ x : Fin N → Bool, (∃ i, x i = true) → 1 / 4 ≤ ∑ i with x i = true,
        regProb (run (randomGrover N (Nat.sqrt N + 1)) (randomGroverInit N (Nat.sqrt N + 1)) x
          (Nat.sqrt N)) i :=
  ⟨norm_randomGroverInit hN (Nat.succ_pos _), Real.nat_sqrt_le_real_sqrt, fun x hx => by
    have := le_sum_regProb_run_randomGrover hN (m := Nat.sqrt N + 1) one_pos
      (by rw [one_pow, one_mul]; exact_mod_cast (Nat.lt_succ_sqrt' N).le) x hx
    norm_num at this ⊢
    exact this⟩

/-! ### Deciding `OR_N` with error `1/3` -/

/-- The range of iteration counts for deciding `OR_N`: `m = 4 (⌊√N⌋ + 1)`, so that `16 N ≤ m²`. -/
def orRange (N : ℕ) : ℕ := 4 * (Nat.sqrt N + 1)

/-- One stage for `OR_N`: `randomGrover` with range `orRange N` for `orRange N - 1` queries, then
a check of the measured index, which writes its queried bit into the control bit. It makes
`orRange N` queries. -/
noncomputable def orStage (N : ℕ) :
    ℕ → State N (Unit × Fin (orRange N)) →ₗᵢ[ℂ] State N (Unit × Fin (orRange N)) :=
  check (orRange N - 1) (randomGrover N (orRange N))

/-- The algorithm for `OR_N`: two independent stages (`Cslib.Quantum.twice`), making
`2 orRange N` queries. -/
noncomputable def orSearch (N : ℕ) :
    ℕ → State N ((Unit × Fin (orRange N)) × (Fin N × Bool × (Unit × Fin (orRange N)))) →ₗᵢ[ℂ]
      State N ((Unit × Fin (orRange N)) × (Fin N × Bool × (Unit × Fin (orRange N)))) :=
  twice (orRange N) (orStage N)

/-- The initial state of `orSearch`: two copies of the initial state of `randomGrover`. -/
noncomputable def orSearchInit (N : ℕ) :
    State N ((Unit × Fin (orRange N)) × (Fin N × Bool × (Unit × Fin (orRange N)))) :=
  twiceInit (randomGroverInit N (orRange N))

/-- The accepting outcomes of `orSearch`: the check bit of either stage is `1`. -/
def orAccept (N : ℕ) : Finset (Fin N × Bool ×
    ((Unit × Fin (orRange N)) × (Fin N × Bool × (Unit × Fin (orRange N))))) :=
  univ.filter fun p => p.2.1 = true ∨ p.2.2.2.2.1 = true

private theorem orRange_pos (N : ℕ) : 0 < orRange N := by
  unfold orRange
  omega

/-- A stage accepts with the average success probability of `randomGrover`. -/
theorem measureProb_run_orStage (hN : 0 < N) (x : Fin N → Bool) :
    measureProb (run (orStage N) (randomGroverInit N (orRange N)) x (orRange N))
        (univ.filter fun p => p.2.1 = true) =
      ∑ i with x i = true,
        regProb (run (randomGrover N (orRange N)) (randomGroverInit N (orRange N)) x
          (orRange N - 1)) i := by
  have h := measureProb_run_check (T := orRange N - 1) (U := randomGrover N (orRange N))
    (ψ₀ := randomGroverInit N (orRange N)) (x := x)
    (fun i w => run_randomGrover_ctrl hN (by omega) x i w)
  rwa [Nat.sub_add_cancel (orRange_pos N)] at h

/-- The initial state of `orSearch` is a unit vector. -/
theorem norm_orSearchInit (hN : 0 < N) : ‖orSearchInit N‖ = 1 :=
  norm_twiceInit (norm_randomGroverInit hN (orRange_pos N))

/-- **The acceptance probability of `orSearch`**: `1 - (1 - P)²`, where `P` is the average success
probability of `randomGrover` with range `orRange N`. -/
theorem measureProb_run_orSearch (hN : 0 < N) (x : Fin N → Bool) :
    measureProb (run (orSearch N) (orSearchInit N) x (orRange N + orRange N)) (orAccept N) =
      1 - (1 - (∑ j ∈ range (orRange N),
        Real.sin ((2 * j + 1) * searchAngle N (weight x)) ^ 2) / orRange N) ^ 2 := by
  classical
  have h := measureProb_run_twice (T := orRange N) (U := orStage N)
    (norm_randomGroverInit hN (orRange_pos N)) x (univ.filter fun p => p.2.1 = true)
  rw [measureProb_run_orStage hN, sum_regProb_run_randomGrover hN (by omega)] at h
  rw [← h, orSearch, orSearchInit, orAccept]
  congr 1
  ext p
  simp

/-- **Deciding `OR_N` with `O(√N)` queries** after [Boyer, Brassard, Høyer,
Tapp][BoyerBrassardHoyerTapp1998]: `orSearch` accepts every input `x` with probability within
`1/3` of `OR_N(x)`. It accepts the all-zero input with probability `0`, and every other input with
probability at least `1 - (9/16)²`. -/
theorem abs_measureProb_run_orSearch_sub_le (hN : 0 < N) (x : Fin N → Bool) :
    |measureProb (run (orSearch N) (orSearchInit N) x (orRange N + orRange N)) (orAccept N) -
      bitVal ℝ (threshold N 1 x)| ≤ 1 / 3 := by
  set a := ∑ i with x i = true, regProb (run (randomGrover N (orRange N))
    (randomGroverInit N (orRange N)) x (orRange N - 1)) i with ha_def
  have hacc : measureProb (run (orSearch N) (orSearchInit N) x (orRange N + orRange N))
      (orAccept N) = 1 - (1 - a) ^ 2 := by
    rw [measureProb_run_orSearch hN, ha_def, sum_regProb_run_randomGrover hN (by omega)]
  -- `a` is a probability.
  have ha0 : 0 ≤ a := sum_nonneg fun i _ => by rw [regProb]; exact measureProb_nonneg _ _
  have ha1 : a ≤ 1 := by
    have := measureProb_le_measureProb_univ
      (run (orStage N) (randomGroverInit N (orRange N)) x (orRange N))
      (univ.filter fun p => p.2.1 = true)
    rw [measureProb_univ, norm_run, norm_randomGroverInit hN (orRange_pos N), one_pow,
      measureProb_run_orStage hN] at this
    exact this
  rw [hacc, threshold_one_right]
  by_cases hx : ∃ i, x i = true
  · -- `OR_N(x) = 1`: each stage succeeds with probability at least `7/16`.
    have h7 : 7 / 16 ≤ a := by
      have := le_sum_regProb_run_randomGrover hN (m := orRange N) (c := 4) (by norm_num)
        (by
          have h := (Nat.lt_succ_sqrt' N).le
          have h' : (N : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
          simp only [orRange, Nat.cast_mul, Nat.cast_ofNat]
          push_cast at h' ⊢
          nlinarith) x hx
      norm_num at this
      linarith
    simp only [hx, decide_true, bitVal_true]
    rw [abs_le]
    constructor <;> nlinarith
  · -- `OR_N(x) = 0`: there is no marked item, so `a = 0`.
    have h0 : a = 0 := by
      rw [ha_def]
      refine sum_eq_zero fun i hi => absurd ⟨i, (mem_filter.mp hi).2⟩ hx
    simp [hx, h0]

/-- **An `O(√N)`-query algorithm for `OR_N` with error `1/3`**, matching the polynomial-method
lower bound `N ≤ 16 T²` up to a constant: `orSearch` starts from a unit state, makes
`8 (⌊√N⌋ + 1) ≤ 8 √N + 8` queries, and accepts every input `x` with probability within `1/3` of
`OR_N(x)`. -/
theorem orSearch_spec (hN : 0 < N) :
    ‖orSearchInit N‖ = 1 ∧ ((orRange N + orRange N : ℕ) : ℝ) ≤ 8 * Real.sqrt N + 8 ∧
      ∀ x : Fin N → Bool, |measureProb (run (orSearch N) (orSearchInit N) x
        (orRange N + orRange N)) (orAccept N) - bitVal ℝ (threshold N 1 x)| ≤ 1 / 3 := by
  refine ⟨norm_orSearchInit hN, ?_, abs_measureProb_run_orSearch_sub_le hN⟩
  have := Real.nat_sqrt_le_real_sqrt (a := N)
  simp only [orRange]
  push_cast
  linarith

end Cslib.Quantum
