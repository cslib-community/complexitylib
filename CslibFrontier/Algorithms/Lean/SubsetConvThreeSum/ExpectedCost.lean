/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Expectation
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Parameters
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The expected cost of the reduction for the parameters of Corollary 2.4

For the parameter family `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Params`, the expected
cost of `threeSumM` over a uniform prime of `[2 ^ d, 2 ^ (d + 1))` and `μ` uniform seeds is at most
`K · 2 ^ (199 m) = K n ^ (2 - 1/100)` for `n = 2 ^ (100 m)` (`exists_avgTime_le`), for
duplicate-free inputs of at most `n` elements below `n ^ κ`; `K` depends only on `κ`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Params

/-- A polynomial times a geometric sequence below `2 ^ e`: if `X < Z 2 ^ e`, then any `T` with
`T Z ^ m ≤ c m ^ k X ^ m` is at most `C 2 ^ (e m)`, with `C` independent of `m`. -/
private theorem exists_le_two_pow_of_mul_pow_le {X Z : ℕ} (e k c : ℕ) (hZ : 0 < Z)
    (h : X < Z * 2 ^ e) : ∃ C : ℝ, ∀ m : ℕ, ∀ T : ℕ, T * Z ^ m ≤ c * m ^ k * X ^ m →
      (T : ℝ) ≤ C * 2 ^ (e * m) := by
  have hZ' : (0 : ℝ) < Z * 2 ^ e := by positivity
  set ρ : ℝ := X / (Z * 2 ^ e) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : |ρ| < 1 := by
    rw [abs_of_nonneg hρ0, hρ, div_lt_one hZ']
    exact_mod_cast h
  obtain ⟨C₀, hC₀⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k hρ1).bddAbove_range
  refine ⟨c * C₀, fun m T hT => ?_⟩
  have h1 : (m : ℝ) ^ k * ρ ^ m ≤ C₀ := hC₀ ⟨m, rfl⟩
  have hT' : (T : ℝ) * (Z : ℝ) ^ m ≤ c * (m : ℝ) ^ k * (X : ℝ) ^ m := by exact_mod_cast hT
  have hX : (X : ℝ) ^ m = ρ ^ m * ((Z : ℝ) ^ m * 2 ^ (e * m)) := by
    rw [hρ, div_pow, pow_mul, mul_pow]
    field_simp
  have hZm : (0 : ℝ) < (Z : ℝ) ^ m := by positivity
  refine le_of_mul_le_mul_right ?_ hZm
  calc (T : ℝ) * (Z : ℝ) ^ m ≤ c * (m : ℝ) ^ k * (X : ℝ) ^ m := hT'
    _ = c * ((m : ℝ) ^ k * ρ ^ m) * ((Z : ℝ) ^ m * 2 ^ (e * m)) := by rw [hX]; ring
    _ ≤ c * C₀ * ((Z : ℝ) ^ m * 2 ^ (e * m)) := by gcongr
    _ = c * C₀ * 2 ^ (e * m) * (Z : ℝ) ^ m := by ring

/-- `U (119 ^ 119 4 ^ 18) ^ m ≤ 16 (d + 1) (2 t + 1) (4 ^ 119 36 ^ 36 83 ^ 83) ^ m` for the
number `U = ⌊4 ^ (d + 2) / #P⌋` of extra trials. -/
private theorem trials_mul_le {m : ℕ} (hm : 1 ≤ m) :
    4 ^ (d m + 2) / numPairs m * (119 ^ 119 * 4 ^ 18) ^ m ≤
      16 * ((d m + 1) * (2 * t m + 1)) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m := by
  have h1 := choose_d_lower hm
  have h2 := central_lower m
  have h3 : 4 ^ (d m + 2) / numPairs m * numPairs m ≤ 4 ^ (d m + 2) := Nat.div_mul_le_self _ _
  set U := 4 ^ (d m + 2) / numPairs m
  calc U * (119 ^ 119 * 4 ^ 18) ^ m = U * (119 ^ (119 * m) * 4 ^ t m) := by
        unfold t; rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ U * ((d m + 1) * ((d m).choose (2 * t m) * 36 ^ (36 * m) * 83 ^ (83 * m)) *
        ((2 * t m + 1) * (2 * t m).choose (t m))) := by gcongr
    _ = U * numPairs m * ((d m + 1) * (2 * t m + 1) * 36 ^ (36 * m) * 83 ^ (83 * m)) := by
        unfold numPairs; ring
    _ ≤ 4 ^ (d m + 2) * ((d m + 1) * (2 * t m + 1) * 36 ^ (36 * m) * 83 ^ (83 * m)) := by
        gcongr
    _ = _ := by unfold d; rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring

private theorem d_succ_le {m : ℕ} (hm : 1 ≤ m) : d m + 1 ≤ 120 * m := by unfold d; omega

private theorem d_succ_mul_le {m : ℕ} (hm : 1 ≤ m) :
    (d m + 1) * (2 * t m + 1) ≤ 4440 * m ^ 2 := by
  have : 2 * t m + 1 ≤ 37 * m := by unfold t; omega
  calc (d m + 1) * (2 * t m + 1) ≤ (120 * m) * (37 * m) := by gcongr; exact d_succ_le hm
    _ = 4440 * m ^ 2 := by ring

/-- The input term: `U n ≤ C 2 ^ (199 m)` (base `2 ^ 103 · 36 ^ 36 83 ^ 83 < 119 ^ 119`). -/
private theorem exists_input_le : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m →
    ((4 ^ (d m + 2) / numPairs m * n m : ℕ) : ℝ) ≤ C * 2 ^ (199 * m) := by
  obtain ⟨C, hC⟩ := exists_le_two_pow_of_mul_pow_le (X := 4 ^ 119 * (36 ^ 36 * 83 ^ 83) * 2 ^ 100)
    (Z := 119 ^ 119 * 4 ^ 18) 199 2 (16 * 4440) (by norm_num) (by norm_num)
  refine ⟨C, fun m hm => hC m _ ?_⟩
  calc 4 ^ (d m + 2) / numPairs m * n m * (119 ^ 119 * 4 ^ 18) ^ m
      = 4 ^ (d m + 2) / numPairs m * (119 ^ 119 * 4 ^ 18) ^ m * 2 ^ (100 * m) := by
        unfold n; ring
    _ ≤ 16 * ((d m + 1) * (2 * t m + 1)) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m *
        2 ^ (100 * m) := Nat.mul_le_mul_right _ (trials_mul_le hm)
    _ ≤ 16 * (4440 * m ^ 2) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m * 2 ^ (100 * m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (d_succ_mul_le hm)))
    _ = _ := by rw [mul_pow _ (2 ^ 100), ← pow_mul]; ring

/-- The preprocessing term: `(d + 1) U Pre ≤ C 2 ^ (199 m)`
(base `8 · 36 ^ 36 83 ^ 83 < 33 ^ 33 86 ^ 86`). -/
private theorem exists_pre_le : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m →
    (((d m + 1) * (4 ^ (d m + 2) / numPairs m * pre m) : ℕ) : ℝ) ≤ C * 2 ^ (199 * m) := by
  obtain ⟨C, hC⟩ := exists_le_two_pow_of_mul_pow_le (X := 4 ^ 119 * (36 ^ 36 * 83 ^ 83))
    (Z := 33 ^ 33 * 86 ^ 86 * 4 ^ 18) 199 3 (16 * 120 * 4440) (by norm_num) (by norm_num)
  refine ⟨C, fun m hm => hC m _ ?_⟩
  set U := 4 ^ (d m + 2) / numPairs m
  have hU := trials_mul_le hm
  have hP := pre_upper hm
  have key : U * pre m * (33 ^ 33 * 86 ^ 86 * 4 ^ 18) ^ m ≤
      16 * ((d m + 1) * (2 * t m + 1)) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m := by
    refine Nat.le_of_mul_le_mul_right (c := 119 ^ (119 * m)) ?_ (by positivity)
    calc U * pre m * (33 ^ 33 * 86 ^ 86 * 4 ^ 18) ^ m * 119 ^ (119 * m)
        = U * (119 ^ 119 * 4 ^ 18) ^ m * (pre m * (33 ^ (33 * m) * 86 ^ (86 * m))) := by
          simp only [mul_pow, ← pow_mul]; ring
      _ ≤ 16 * ((d m + 1) * (2 * t m + 1)) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m *
          119 ^ (119 * m) := Nat.mul_le_mul hU hP
  calc (d m + 1) * (U * pre m) * (33 ^ 33 * 86 ^ 86 * 4 ^ 18) ^ m
      = (d m + 1) * (U * pre m * (33 ^ 33 * 86 ^ 86 * 4 ^ 18) ^ m) := by ring
    _ ≤ (120 * m) * (16 * (4440 * m ^ 2) * (4 ^ 119 * (36 ^ 36 * 83 ^ 83)) ^ m) :=
        Nat.mul_le_mul (d_succ_le hm) (key.trans (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (d_succ_mul_le hm))))
    _ = _ := by ring

/-- The query term: `(d + 1) U (d choose 2 t) Q n ≤ C 2 ^ (318 m)`
(base `36 ^ 36 < 2 ^ 16 · 27 · 33 ^ 33`). -/
private theorem exists_query_le : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m →
    (((d m + 1) * (4 ^ (d m + 2) / numPairs m * (d m).choose (2 * t m) * query m * n m) : ℕ) :
      ℝ) ≤ C * 2 ^ (318 * m) := by
  obtain ⟨C, hC⟩ := exists_le_two_pow_of_mul_pow_le (X := 4 ^ 119 * 36 ^ 36 * 2 ^ 100)
    (Z := 4 ^ 18 * (27 * 33 ^ 33)) 318 2 (16 * 4440) (by norm_num)
    (by rw [show 318 = 159 + 159 from rfl, pow_add]; norm_num)
  refine ⟨C, fun m hm => hC m _ ?_⟩
  set U := 4 ^ (d m + 2) / numPairs m
  have h3 : U * numPairs m ≤ 4 ^ (d m + 2) := Nat.div_mul_le_self _ _
  have hc := central_lower m
  have hQ := query_upper hm
  have hUB : U * (d m).choose (2 * t m) * 4 ^ (18 * m) ≤
      16 * (2 * t m + 1) * 4 ^ (119 * m) := by
    calc U * (d m).choose (2 * t m) * 4 ^ (18 * m)
        ≤ U * (d m).choose (2 * t m) * ((2 * t m + 1) * (2 * t m).choose (t m)) := by
          gcongr; exact hc
      _ = U * numPairs m * (2 * t m + 1) := by unfold numPairs; ring
      _ ≤ 4 ^ (d m + 2) * (2 * t m + 1) := by gcongr
      _ = _ := by unfold d; ring
  calc (d m + 1) * (U * (d m).choose (2 * t m) * query m * n m) *
        (4 ^ 18 * (27 * 33 ^ 33)) ^ m
      = (d m + 1) * (U * (d m).choose (2 * t m) * 4 ^ (18 * m)) *
          (query m * (3 ^ (3 * m) * 33 ^ (33 * m))) * 2 ^ (100 * m) := by
        unfold n
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          show (27 : ℕ) ^ m = 3 ^ (3 * m) by rw [pow_mul]; norm_num]
        ring
    _ ≤ (d m + 1) * (16 * (2 * t m + 1) * 4 ^ (119 * m)) * 36 ^ (36 * m) * 2 ^ (100 * m) := by
        gcongr
    _ = 16 * ((d m + 1) * (2 * t m + 1)) * (4 ^ (119 * m) * 36 ^ (36 * m) * 2 ^ (100 * m)) := by
        ring
    _ ≤ 16 * (4440 * m ^ 2) * (4 ^ (119 * m) * 36 ^ (36 * m) * 2 ^ (100 * m)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (d_succ_mul_le hm))
    _ = _ := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring

/-- The bad-element term: `(d + 1) 2 ^ (181 m) ≤ C 2 ^ (199 m)`. -/
private theorem exists_bad_le : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m →
    (((d m + 1) * 2 ^ (181 * m) : ℕ) : ℝ) ≤ C * 2 ^ (199 * m) := by
  obtain ⟨C, hC⟩ := exists_le_two_pow_of_mul_pow_le (X := 2 ^ 181) (Z := 1) 199 1 120
    (by norm_num) (by norm_num)
  refine ⟨C, fun m hm => hC m _ ?_⟩
  rw [one_pow, mul_one, pow_one, ← pow_mul]
  gcongr
  exact d_succ_le hm

/-- There is at least one extra trial: `#P ≤ 4 ^ (d + 2)`, so `1 ≤ U`. -/
private theorem one_le_trials (m : ℕ) : 1 ≤ 4 ^ (d m + 2) / numPairs m := by
  have h2t : 2 * t m ≤ d m := by unfold d t; omega
  have hP : 0 < numPairs m :=
    Nat.mul_pos (Nat.choose_pos h2t) (Nat.choose_pos (by omega))
  refine Nat.div_pos ?_ hP
  calc numPairs m ≤ 2 ^ d m * 2 ^ d m :=
        Nat.mul_le_mul (Nat.choose_le_two_pow _ _)
          ((Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) h2t))
    _ = 4 ^ d m := by rw [← mul_pow]; norm_num
    _ ≤ 4 ^ (d m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The query sum contains `(2 t choose 2 t) = 1`. -/
private theorem one_le_query (m : ℕ) : 1 ≤ query m := by
  have hmem : 2 * t m ∈ Icc (s m) (2 * t m) := by rw [mem_Icc]; unfold s t; omega
  calc 1 = (2 * t m).choose (2 * t m) := (Nat.choose_self _).symm
    _ ≤ query m := Finset.single_le_sum (f := fun j => (2 * t m).choose j)
        (fun _ _ => Nat.zero_le _) hmem

/-- The expected cost of `threeSumM` with the parameters for unit `m`, over a uniform prime `q` of
the window and `μ m` uniform seeds (a non-prime contributes `0`; the window has only primes). -/
@[expose] noncomputable def avgTime (m : ℕ) (A B C : List ℕ) : ℝ :=
  avgTimeOf (fun _ σ => trialM (d m) (t m) (s m) σ) (μ m) (d m) A B C

/-- **The expected cost is truly subquadratic**: there is `K` such that for every unit `m ≥ 1` and
duplicate-free `A`, `B` and any `C` with at most `n = 2 ^ (100 m)` elements, all below
`n ^ κ = 2 ^ (100 κ m)`, the expected cost is at most `K · 2 ^ (199 m) = K n ^ (2 - 1/100)`. -/
theorem exists_avgTime_le (κ : ℕ) : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ A B C : List ℕ,
    A.Nodup → B.Nodup → A.length ≤ n m → B.length ≤ n m → C.length ≤ n m →
    (∀ a ∈ A, a < 2 ^ (100 * κ * m)) → (∀ b ∈ B, b < 2 ^ (100 * κ * m)) →
    avgTime m A B C ≤ K * 2 ^ (199 * m) := by
  obtain ⟨Ci, hCi⟩ := exists_input_le
  obtain ⟨Cp, hCp⟩ := exists_pre_le
  obtain ⟨Cq, hCq⟩ := exists_query_le
  obtain ⟨Cb, hCb⟩ := exists_bad_le
  refine ⟨7 + 6 * κ * Cb + 10 * Ci + 6 * Cp + 10 * Cq, ?_⟩
  intro m hm A B C hA hB ha hb hc hAM hBM
  set N := n m with hN
  set U := 4 ^ (d m + 2) / numPairs m with hU
  have hμ : μ m ≤ 2 * U := by have := one_le_trials m; unfold μ; omega
  set W := primeWindow (d m) with hW
  have hw : 2 ^ d m ≤ 3 * (d m + 1) * #W := two_pow_le_card_primeWindow (by unfold d; omega)
  have hw0 : 0 < #W := by
    rcases Nat.eq_zero_or_pos #W with h | h
    · rw [h, mul_zero] at hw; exact absurd hw (Nat.not_le.2 (by positivity))
    · exact h
  -- the base cost, the trials and the bad elements, for the sum over the window
  set R₀ := 3 * A.length + 3 * B.length + C.length +
    μ m * (2 * A.length + 2 * B.length + C.length + 3 * (d m + 1) * pre m) with hR₀
  set Y := μ m * ((2 + 3 * (d m + 1) * query m) * (C.length * (d m).choose (2 * t m))) with hYdef
  set bad : ℕ → ℕ := fun q => (A.filter fun a => decide (¬ Isolated q A a)).length * B.length +
    A.length * (B.filter fun b => decide (¬ Isolated q B b)).length with hbad
  have hsum : avgTime m A B C ≤ R₀ + Y / 2 ^ d m + ((∑ q ∈ W, bad q : ℕ) : ℝ) / #W := by
    have hs : s m ≤ 2 * t m := by unfold s t; omega
    refine avgTimeOf_le (card_pos.mp hw0) fun q hq _ => ?_
    have h := mul_sum_time_threeSumM_le (μ := μ m) (mem_primeWindow.1 hq).2.1 hs A B C
    refine h.trans_eq ?_
    simp only [hR₀, hYdef, hbad, pre, query]
    ring
  -- the bad elements: `∑_q bad q ≤ 2 κ n ^ 3 ≤ 6 κ (d + 1) 2 ^ (181 m) #W`
  have hlog : Nat.log 2 (2 ^ (100 * κ * m)) = 100 * κ * m := Nat.log_pow (by norm_num) _
  have hbadA := mul_sum_length_bad_le (d := d m) hA hAM
  have hbadB := mul_sum_length_bad_le (d := d m) hB hBM
  rw [hlog, ← hW] at hbadA hbadB
  have hkey : ∀ S x : ℕ, x ≤ N → d m * S ≤ x * x * (100 * κ * m) → S ≤ κ * N * N := by
    intro S x hx h
    have h1 : m * (119 * S) ≤ m * (100 * (κ * N * N)) := by
      calc m * (119 * S) = d m * S := by unfold d; ring
        _ ≤ x * x * (100 * κ * m) := h
        _ ≤ N * N * (100 * κ * m) := by gcongr
        _ = m * (100 * (κ * N * N)) := by ring
    have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
    omega
  have hSA := hkey _ _ ha hbadA
  have hSB := hkey _ _ hb hbadB
  have hbadsum : ∑ q ∈ W, bad q ≤ 6 * κ * ((d m + 1) * 2 ^ (181 * m)) * #W := by
    calc ∑ q ∈ W, bad q = B.length * ∑ q ∈ W, (A.filter fun a => decide (¬ Isolated q A a)).length
          + A.length * ∑ q ∈ W, (B.filter fun b => decide (¬ Isolated q B b)).length := by
          rw [hbad, sum_add_distrib, mul_sum, mul_sum]
          congr 1
          exact sum_congr rfl fun q _ => by ring
      _ ≤ N * (κ * N * N) + N * (κ * N * N) := by gcongr
      _ = 2 * κ * 2 ^ (181 * m) * 2 ^ d m := by
          rw [hN]; unfold n d
          rw [mul_assoc (2 * κ), ← pow_add,
            show 181 * m + 119 * m = 100 * m + 100 * m + 100 * m by ring, pow_add, pow_add]
          ring
      _ ≤ 2 * κ * 2 ^ (181 * m) * (3 * (d m + 1) * #W) := by gcongr
      _ = _ := by ring
  have hbad' : ((∑ q ∈ W, bad q : ℕ) : ℝ) / #W ≤ 6 * κ * (Cb * 2 ^ (199 * m)) := by
    rw [div_le_iff₀ (by exact_mod_cast hw0)]
    calc ((∑ q ∈ W, bad q : ℕ) : ℝ) ≤ ((6 * κ * ((d m + 1) * 2 ^ (181 * m)) * #W : ℕ) : ℝ) := by
          exact_mod_cast hbadsum
      _ = 6 * κ * (((d m + 1) * 2 ^ (181 * m) : ℕ) : ℝ) * #W := by push_cast; ring
      _ ≤ _ := by gcongr; exact hCb m hm
  -- the base cost and the trials
  have hR : R₀ ≤ 7 * N + 10 * (U * N) + 6 * ((d m + 1) * (U * pre m)) := by
    rw [hR₀]
    calc _ ≤ 3 * N + 3 * N + N + 2 * U * (2 * N + 2 * N + N + 3 * (d m + 1) * pre m) := by
          gcongr
      _ = _ := by ring
  have hY : Y ≤ 10 * ((d m + 1) * (U * (d m).choose (2 * t m) * query m * N)) := by
    have hQ := one_le_query m
    rw [hYdef]
    calc _ ≤ 2 * U * ((5 * (d m + 1) * query m) * (N * (d m).choose (2 * t m))) := by
          gcongr
          nlinarith
      _ = _ := by ring
  have hY' : (Y : ℝ) / 2 ^ d m ≤ 10 * (Cq * 2 ^ (199 * m)) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := (Nat.cast_le (α := ℝ)).2 hY
    have h2 := hCq m hm
    have h3 : (2 : ℝ) ^ (318 * m) = 2 ^ (199 * m) * 2 ^ d m := by
      unfold d; rw [← pow_add]; ring_nf
    push_cast at h1 h2
    rw [h3] at h2
    nlinarith
  have hR' := (Nat.cast_le (α := ℝ)).2 hR
  have hi := hCi m hm
  have hp := hCp m hm
  have hN' : (N : ℝ) ≤ 2 ^ (199 * m) := by
    rw [hN]; unfold n; push_cast
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  push_cast at hR' hi hp
  nlinarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
