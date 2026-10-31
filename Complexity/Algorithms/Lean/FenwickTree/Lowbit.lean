/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Lowest-Set-Bit Combinatorics for Fenwick Trees

This module develops the binary arithmetic and interval combinatorics underlying Fenwick trees
(binary indexed trees, `[Fenwick1994]`, "PRINCIPLES", pp. 328–329, and "OPERATIONS AND CODE TO
HANDLE THE STRUCTURE", pp. 329–330).

For a `1`-based index `m ≥ 1`, `lowbit m` is the value `2 ^ k` of the least significant `1`-bit of
`m` (conventionally written `m & -m` in two's-complement arithmetic), and node `m` aggregates the
half-open `0`-based index interval `[m - lowbit m, m)`:

* **Downward query chains (`downChain`):** stepping `m ↦ m - lowbit m` strictly doubles the trailing
  power-of-two factor (`two_mul_lowbit_le_lowbit_sub`), terminating in at most `⌊log₂ m⌋ + 1` steps
  (`length_downChain_le_log`) and partitioning `[0, m)`.
* **Upward update chains (`upChain`):** stepping `m ↦ m + lowbit m` up to `n` likewise strictly
  doubles `lowbit` (`two_mul_lowbit_le_lowbit_add`), terminating in at most `⌊log₂ n⌋ + 1` steps
  (`length_upChain_le_log`) and visiting precisely those nodes `idx ≤ n` whose interval
  `[idx - lowbit idx, idx)` contains `m - 1` (`mem_upChain_iff`).
* **Immediate-children partition (`fenwickChildren`):** for every `idx ≥ 1`, the singleton
  `{idx - 1}` together with the intervals `[c - lowbit c, c)` of immediate children
  `c + lowbit c = idx` pairwise-disjointly partition `[idx - lowbit idx, idx)`
  (`insert_biUnion_fenwickChildren`), justifying the standard BIT folklore immediate-parent
  construction (`n` parent-propagation steps).

## Main definitions

* `Cslib.Algorithms.Lean.FenwickTree.lowbit`: value of the lowest set bit of `n` (`0` at `0`).
* `Cslib.Algorithms.Lean.FenwickTree.downChain`: downward query indices `m, m - lowbit m, …`.
* `Cslib.Algorithms.Lean.FenwickTree.upChain`: upward update indices `m, m + lowbit m, … ≤ n`.
* `Cslib.Algorithms.Lean.FenwickTree.fenwickChildren`: immediate Fenwick children `c < idx` with
  `c + lowbit c = idx`.

## Main results

* `Cslib.Algorithms.Lean.FenwickTree.exists_odd_mul_lowbit`: odd-quotient power-of-two factorization
  `n = (2 * q + 1) * lowbit n` with `lowbit n = 2 ^ k`.
* `Cslib.Algorithms.Lean.FenwickTree.two_mul_lowbit_le_lowbit_sub` and
  `two_mul_lowbit_le_lowbit_add`: `lowbit` at least doubles at every downward or upward step.
* `Cslib.Algorithms.Lean.FenwickTree.fenwick_parent_bridge`: for `0 < m < idx`,
  `idx - lowbit idx < m ↔ idx - lowbit idx < m + lowbit m ∧ m + lowbit m ≤ idx`.
* `Cslib.Algorithms.Lean.FenwickTree.length_downChain_le_log`, `length_upChain_le_log`,
  `length_downChain_le_clog`, `length_upChain_le_clog`: logarithmic chain-length bounds.
* `Cslib.Algorithms.Lean.FenwickTree.mem_upChain_iff`: exact ancestor characterization.
* `Cslib.Algorithms.Lean.FenwickTree.pairwiseDisjoint_fenwickChildren` and
  `insert_biUnion_fenwickChildren`: disjoint child-interval partition for linear-time construction.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.Algorithms.Lean.FenwickTree

/-! ## Binary lowest set bit (`lowbit`) -/

/-- Value `2 ^ k` of the least significant `1`-bit of `n` (`0` when `n = 0`), defined by binary
recursion on `ℕ` (modeling two's-complement `n & -n` on fixed-width words). -/
@[expose] def lowbit (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then 1
  else 2 * lowbit (n / 2)
termination_by n

@[simp]
theorem lowbit_zero : lowbit 0 = 0 := by
  rw [lowbit]
  simp only [↓reduceIte]

@[simp]
theorem lowbit_one : lowbit 1 = 1 := by
  rw [lowbit]
  simp only [Nat.one_ne_zero, ↓reduceIte]

theorem lowbit_pos {n : ℕ} (hn : 0 < n) : 0 < lowbit n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [lowbit]
    have hne : n ≠ 0 := Nat.ne_of_gt hn
    simp only [hne, ↓reduceIte]
    split_ifs with hodd
    · exact Nat.one_pos
    · have hdiv : 0 < n / 2 := by omega
      have hsub := ih (n / 2) (by omega) hdiv
      omega

theorem lowbit_le (n : ℕ) : lowbit n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [lowbit]
    split_ifs with h0 hodd
    · omega
    · omega
    · have hsub := ih (n / 2) (by omega)
      omega

theorem lowbit_dvd (n : ℕ) : lowbit n ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [lowbit]
    split_ifs with h0 hodd
    · subst h0
      exact Nat.dvd_refl 0
    · exact one_dvd n
    · obtain ⟨q, hq⟩ := ih (n / 2) (by omega)
      refine ⟨q, ?_⟩
      have heven : n = 2 * (n / 2) := by omega
      conv_lhs => rw [heven, hq]
      ring

/-- Odd-quotient power-of-two factorization of a positive natural via `lowbit`. -/
theorem exists_odd_mul_lowbit {n : ℕ} (hn : 0 < n) :
    ∃ q k : ℕ, lowbit n = 2 ^ k ∧ n = (2 * q + 1) * 2 ^ k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [lowbit]
    have hne : n ≠ 0 := Nat.ne_of_gt hn
    simp only [hne, ↓reduceIte]
    split_ifs with hodd
    · refine ⟨n / 2, 0, rfl, ?_⟩
      simp only [Nat.pow_zero, Nat.mul_one]
      omega
    · have hdiv_pos : 0 < n / 2 := by omega
      obtain ⟨q, k, hlb, hfact⟩ := ih (n / 2) (by omega) hdiv_pos
      refine ⟨q, k + 1, ?_, ?_⟩
      · rw [hlb]
        ring
      · have heven : n = 2 * (n / 2) := by omega
        rw [heven, hfact]
        ring

theorem lowbit_odd_mul_pow_two (q k : ℕ) : lowbit ((2 * q + 1) * 2 ^ k) = 2 ^ k := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one]
    rw [lowbit]
    have hne : 2 * q + 1 ≠ 0 := by omega
    have hodd : (2 * q + 1) % 2 = 1 := by omega
    simp only [hne, hodd, ↓reduceIte]
  | succ k ih =>
    set m := (2 * q + 1) * 2 ^ k
    have heq : (2 * q + 1) * 2 ^ (k + 1) = 2 * m := by
      dsimp only [m]
      ring
    rw [heq]
    conv_lhs => rw [lowbit]
    have hm_pos : 0 < m := Nat.mul_pos (by omega) (Nat.two_pow_pos k)
    have hne : 2 * m ≠ 0 := by omega
    have heven : ¬ ((2 * m) % 2 = 1) := by omega
    have hdiv : (2 * m) / 2 = m := by omega
    simp only [hne, heven, ↓reduceIte, hdiv, ih]
    ring

theorem lowbit_pow_two (k : ℕ) : lowbit (2 ^ k) = 2 ^ k := by
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using lowbit_odd_mul_pow_two 0 k

/-- Any power of two dividing `n > 0` is bounded by `lowbit n`. -/
theorem two_pow_le_lowbit_of_dvd {n k : ℕ} (hn : 0 < n) (hdvd : 2 ^ k ∣ n) :
    2 ^ k ≤ lowbit n := by
  obtain ⟨q, j, hlb, hfact⟩ := exists_odd_mul_lowbit hn
  rw [hlb]
  rcases le_or_gt k j with hle | hgt
  · exact Nat.pow_le_pow_right (by omega) hle
  · exfalso
    obtain ⟨c, hc⟩ := hdvd
    have hsplit : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
    rw [hfact, hsplit] at hc
    have hmul : (2 * q + 1) * 2 ^ j = (2 ^ (k - j) * c) * 2 ^ j := by
      calc (2 * q + 1) * 2 ^ j = 2 ^ (k - j) * 2 ^ j * c := hc
        _ = (2 ^ (k - j) * c) * 2 ^ j := by ring
    have heq : 2 * q + 1 = 2 ^ (k - j) * c :=
      Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos j) hmul
    have heven : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
      conv_lhs => rw [show k - j = (k - j - 1) + 1 by omega]
      ring
    rw [heven, Nat.mul_assoc] at heq
    omega

/-- Stepping downward `m ↦ m - lowbit m` at least doubles `lowbit` whenever `m - lowbit m > 0`. -/
theorem two_mul_lowbit_le_lowbit_sub {m : ℕ} (hsub : 0 < m - lowbit m) :
    2 * lowbit m ≤ lowbit (m - lowbit m) := by
  have hm : 0 < m := by omega
  obtain ⟨q, k, hlb, hfact⟩ := exists_odd_mul_lowbit hm
  have hdiff : m - lowbit m = q * 2 ^ (k + 1) := by
    rw [hlb, hfact]
    have hsum : (2 * q + 1) * 2 ^ k = q * 2 ^ (k + 1) + 2 ^ k := by ring
    rw [hsum, Nat.add_sub_cancel]
  have hdvd : 2 ^ (k + 1) ∣ m - lowbit m := ⟨q, by rw [hdiff]; ring⟩
  have hle := two_pow_le_lowbit_of_dvd hsub hdvd
  have hpow : 2 * lowbit m = 2 ^ (k + 1) := by rw [hlb]; ring
  exact hpow ▸ hle

/-- Stepping upward `m ↦ m + lowbit m` at least doubles `lowbit` for all `m > 0`. -/
theorem two_mul_lowbit_le_lowbit_add {m : ℕ} (hm : 0 < m) :
    2 * lowbit m ≤ lowbit (m + lowbit m) := by
  obtain ⟨q, k, hlb, hfact⟩ := exists_odd_mul_lowbit hm
  have hsum : m + lowbit m = (q + 1) * 2 ^ (k + 1) := by
    rw [hlb, hfact]
    ring
  have hdvd : 2 ^ (k + 1) ∣ m + lowbit m := ⟨q + 1, by rw [hsum]; ring⟩
  have hle := two_pow_le_lowbit_of_dvd (by omega) hdvd
  have hpow : 2 * lowbit m = 2 ^ (k + 1) := by rw [hlb]; ring
  exact hpow ▸ hle

/-! ## Parent-interval bridge -/

private theorem not_dvd_two_pow_succ_between {r j x : ℕ}
    (hdvd : 2 ^ (j + 1) ∣ x)
    (hlo : 2 * r * 2 ^ j < x) (hhi : x ≤ (2 * r + 1) * 2 ^ j) : False := by
  obtain ⟨c, rfl⟩ := hdvd
  have hpow : 0 < 2 ^ j := Nat.two_pow_pos j
  have hrew : 2 ^ (j + 1) * c = (2 * c) * 2 ^ j := by ring
  rw [hrew] at hlo hhi
  have hlt' : 2 * r < 2 * c := Nat.lt_of_mul_lt_mul_right hlo
  have hle' : 2 * c ≤ 2 * r + 1 := Nat.le_of_mul_le_mul_right hhi hpow
  omega

/-- Fundamental Fenwick parent-interval bridge: for `0 < m < idx`, `idx`'s interval
`[idx - lowbit idx, idx)` reaches below `m` iff it reaches below `m`'s Fenwick parent
`m + lowbit m` and `m + lowbit m ≤ idx`. -/
theorem fenwick_parent_bridge {m idx : ℕ} (hm : 0 < m) (hlt : m < idx) :
    idx - lowbit idx < m ↔ idx - lowbit idx < m + lowbit m ∧ m + lowbit m ≤ idx := by
  obtain ⟨q, k, hlb_m, hm_eq⟩ := exists_odd_mul_lowbit hm
  obtain ⟨r, j, hlb_i, hi_eq⟩ := exists_odd_mul_lowbit (Nat.lt_trans hm hlt)
  have hisub : idx - lowbit idx = 2 * r * 2 ^ j := by
    rw [hlb_i, hi_eq]
    have hsum : (2 * r + 1) * 2 ^ j = 2 * r * 2 ^ j + 2 ^ j := by ring
    rw [hsum, Nat.add_sub_cancel]
  have hmadd : m + lowbit m = (2 * q + 2) * 2 ^ k := by
    rw [hlb_m, hm_eq]
    ring
  constructor
  · intro hlo
    refine ⟨by omega, ?_⟩
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exfalso
      have hdvd : 2 ^ (j + 1) ∣ m := by
        refine ⟨(2 * q + 1) * 2 ^ (k - (j + 1)), ?_⟩
        have hp : 2 ^ k = 2 ^ (j + 1) * 2 ^ (k - (j + 1)) := by
          rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        rw [hm_eq, hp]
        ring
      exact not_dvd_two_pow_succ_between hdvd (hisub ▸ hlo) (hi_eq ▸ Nat.le_of_lt hlt)
    · exfalso
      rw [hisub, hm_eq] at hlo
      rw [hm_eq, hi_eq] at hlt
      have h1 : 2 * r < 2 * q + 1 := Nat.lt_of_mul_lt_mul_right hlo
      have h2 : 2 * q + 1 < 2 * r + 1 := Nat.lt_of_mul_lt_mul_right hlt
      omega
    · have hp : 2 ^ j = 2 * 2 ^ (j - 1 - k) * 2 ^ k := by
        have hj : j = 1 + (j - 1 - k) + k := by omega
        conv_lhs => rw [hj, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      have hi_k : idx = (2 * ((2 * r + 1) * 2 ^ (j - 1 - k))) * 2 ^ k := by
        rw [hi_eq, hp]
        ring
      have hlt_k : 2 * q + 1 < 2 * ((2 * r + 1) * 2 ^ (j - 1 - k)) := by
        rw [hm_eq, hi_k] at hlt
        exact Nat.lt_of_mul_lt_mul_right hlt
      rw [hmadd, hi_k]
      exact Nat.mul_le_mul_right (2 ^ k) (by omega)
  · rintro ⟨hlo, hhi⟩
    rcases le_or_gt j k with hjk | hkj
    · exfalso
      have hdvd : 2 ^ (j + 1) ∣ m + lowbit m := by
        refine ⟨(q + 1) * 2 ^ (k - j), ?_⟩
        have hp : 2 ^ (k + 1) = 2 ^ (j + 1) * 2 ^ (k - j) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        have h2q : (2 * q + 2) * 2 ^ k = (q + 1) * 2 ^ (k + 1) := by ring
        rw [hmadd, h2q, hp]
        ring
      exact not_dvd_two_pow_succ_between hdvd (hisub ▸ hlo) (hi_eq ▸ hhi)
    · have hp : 2 ^ j = 2 * 2 ^ (j - 1 - k) * 2 ^ k := by
        have hj : j = 1 + (j - 1 - k) + k := by omega
        conv_lhs => rw [hj, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      have hisub_k : idx - lowbit idx = (2 * (2 * r * 2 ^ (j - 1 - k))) * 2 ^ k := by
        rw [hisub, hp]
        ring
      have hlt_k : 2 * (2 * r * 2 ^ (j - 1 - k)) < 2 * q + 2 := by
        rw [hisub_k, hmadd] at hlo
        exact Nat.lt_of_mul_lt_mul_right hlo
      rw [hisub_k, hm_eq]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos k)

/-! ## Downward and upward traversal chains -/

/-- Downward Fenwick query chain `m, m - lowbit m, …` down to `0`. -/
@[expose] def downChain (m : ℕ) : List ℕ :=
  if _hm : 0 < m then m :: downChain (m - lowbit m) else []
termination_by m
decreasing_by exact Nat.sub_lt _hm (lowbit_pos _hm)

/-- Upward Fenwick update chain `m, m + lowbit m, …` within `[1, n]`. -/
@[expose] def upChain (n m : ℕ) : List ℕ :=
  if _h : 0 < m ∧ m ≤ n then m :: upChain n (m + lowbit m) else []
termination_by n + 1 - m
decreasing_by
  have := lowbit_pos _h.1
  omega

@[simp]
theorem downChain_zero : downChain 0 = [] := by
  rw [downChain]
  simp only [Nat.lt_irrefl, ↓reduceDIte]

private theorem two_pow_exponent_lt_of_two_mul_le {k k' : ℕ}
    (hle : 2 * 2 ^ k ≤ 2 ^ k') : k + 1 ≤ k' := by
  have h1 : 2 ^ (k + 1) ≤ 2 ^ k' := by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    exact hpow ▸ hle
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1

private theorem length_downChain_add_exp_le {m k : ℕ} (hm : 0 < m) (hlb : lowbit m = 2 ^ k) :
    (downChain m).length + k ≤ Nat.log 2 m + 1 := by
  induction m using Nat.strongRecOn generalizing k with
  | ind m ih =>
    rw [downChain]
    simp only [hm, ↓reduceDIte, List.length_cons]
    have hpow_le : 2 ^ k ≤ m := hlb ▸ lowbit_le m
    have hk_log : k ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by omega) hpow_le
    rcases Nat.eq_zero_or_pos (m - lowbit m) with h0 | hpos
    · rw [h0, downChain_zero, List.length_nil]
      omega
    · obtain ⟨_, k', hlb', _⟩ := exists_odd_mul_lowbit hpos
      have hk_step : k + 1 ≤ k' := by
        have h2 := two_mul_lowbit_le_lowbit_sub hpos
        rw [hlb', hlb] at h2
        exact two_pow_exponent_lt_of_two_mul_le h2
      have hlt_m : m - lowbit m < m := Nat.sub_lt hm (lowbit_pos hm)
      have hsub := ih (m - lowbit m) hlt_m hpos hlb'
      have hlog_mono : Nat.log 2 (m - lowbit m) ≤ Nat.log 2 m :=
        Nat.log_mono_right (Nat.le_of_lt hlt_m)
      omega

/-- Every downward Fenwick query chain from `m > 0` has length at most `⌊log₂ m⌋ + 1`. -/
theorem length_downChain_le_log {m : ℕ} (hm : 0 < m) :
    (downChain m).length ≤ Nat.log 2 m + 1 := by
  obtain ⟨_, k, hlb, _⟩ := exists_odd_mul_lowbit hm
  have h := length_downChain_add_exp_le hm hlb
  omega

/-- Uniform `⌈log₂ (n + 1)⌉` bound on `downChain m` for all `m ≤ n` (`0` when `n = 0`). -/
theorem length_downChain_le_clog {m n : ℕ} (hmn : m ≤ n) :
    (downChain m).length ≤ Nat.clog 2 (n + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [downChain_zero, List.length_nil, Nat.zero_le]
  · have hlog := length_downChain_le_log hm
    have hpow : 2 ^ Nat.log 2 m < n + 1 :=
      Nat.lt_succ_of_le ((Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)).trans hmn)
    have hclog : Nat.log 2 m < Nat.clog 2 (n + 1) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hpow
    omega

private theorem length_upChain_add_exp_le {n m k : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (hlb : lowbit m = 2 ^ k) :
    (upChain n m).length + k ≤ Nat.log 2 n + 1 := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m k with
  | ind rem ih =>
    rw [upChain]
    simp only [hm, hmn, and_self, ↓reduceDIte, List.length_cons]
    have hpow_le : 2 ^ k ≤ n := (hlb ▸ lowbit_le m).trans hmn
    have hk_log : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by omega) hpow_le
    by_cases hnext : m + lowbit m ≤ n
    · have hpos' : 0 < m + lowbit m := by omega
      obtain ⟨_, k', hlb', _⟩ := exists_odd_mul_lowbit hpos'
      have hk_step : k + 1 ≤ k' := by
        have h2 := two_mul_lowbit_le_lowbit_add hm
        rw [hlb', hlb] at h2
        exact two_pow_exponent_lt_of_two_mul_le h2
      have hlb_pos : 0 < lowbit m := lowbit_pos hm
      have hsub := @ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m) k' hpos' hnext hlb' rfl
      omega
    · rw [upChain]
      simp only [hnext, and_false, ↓reduceDIte, List.length_nil]
      omega

/-- Every upward Fenwick update chain from `1 ≤ m ≤ n` has length at most `⌊log₂ n⌋ + 1`. -/
theorem length_upChain_le_log {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (upChain n m).length ≤ Nat.log 2 n + 1 := by
  obtain ⟨_, k, hlb, _⟩ := exists_odd_mul_lowbit hm
  have h := length_upChain_add_exp_le hm hmn hlb
  omega

/-- Uniform `⌈log₂ (n + 1)⌉` bound on `upChain n m` (`0` when `n = 0`). -/
theorem length_upChain_le_clog (n m : ℕ) :
    (upChain n m).length ≤ Nat.clog 2 (n + 1) := by
  by_cases h : 0 < m ∧ m ≤ n
  · have hlog := length_upChain_le_log h.1 h.2
    have hn : 0 < n := Nat.lt_of_lt_of_le h.1 h.2
    have hpow : 2 ^ Nat.log 2 n < n + 1 :=
      Nat.lt_succ_of_le (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn))
    have hclog : Nat.log 2 n < Nat.clog 2 (n + 1) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hpow
    omega
  · rw [upChain]
    simp only [h, ↓reduceDIte, List.length_nil, Nat.zero_le]

private theorem ge_of_mem_upChain {n m x : ℕ} (hx : x ∈ upChain n m) : m ≤ x := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m with
  | ind rem ih =>
    rw [upChain] at hx
    split_ifs at hx with h
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | htail
      · exact Nat.le_refl _
      · have hlb_pos : 0 < lowbit m := lowbit_pos h.1
        have hge := ih (n + 1 - (m + lowbit m)) (by omega) htail rfl
        omega
    · simp only [List.not_mem_nil] at hx

theorem pairwise_lt_upChain (n m : ℕ) : (upChain n m).Pairwise (· < ·) := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m with
  | ind rem ih =>
    rw [upChain]
    split_ifs with h
    · have hlb_pos : 0 < lowbit m := lowbit_pos h.1
      refine List.Pairwise.cons (fun x hx => ?_)
        (@ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m) rfl)
      have hge := ge_of_mem_upChain hx
      omega
    · exact List.Pairwise.nil

theorem nodup_upChain (n m : ℕ) : (upChain n m).Nodup :=
  (pairwise_lt_upChain n m).imp (fun h => Nat.ne_of_lt h)

/-- Exact Fenwick ancestor characterization: starting from `m > 0`, `idx` is visited by
`upChain n m` iff `m ≤ idx ≤ n` and `idx`'s Fenwick interval `[idx - lowbit idx, idx)` contains
`m - 1` (i.e. `idx - lowbit idx < m`). -/
theorem mem_upChain_iff {n m idx : ℕ} (hm : 0 < m) :
    idx ∈ upChain n m ↔ m ≤ idx ∧ idx ≤ n ∧ idx - lowbit idx < m := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m with
  | ind rem ih =>
    rw [upChain]
    split_ifs with h
    · simp only [List.mem_cons]
      have hlb_pos : 0 < lowbit m := lowbit_pos hm
      rcases lt_trichotomy idx m with hlt | rfl | hgt
      · constructor
        · rintro (rfl | htail)
          · omega
          · have hge := ge_of_mem_upChain htail
            omega
        · omega
      · simp only [true_or, Nat.le_refl, h.2, true_and, true_iff]
        omega
      · have hneq : idx ≠ m := Nat.ne_of_gt hgt
        simp only [hneq, false_or]
        rw [@ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m) (by omega) rfl]
        have hbridge := fenwick_parent_bridge hm hgt
        constructor
        · rintro ⟨hle, hin, hsub⟩
          exact ⟨Nat.le_of_lt hgt, hin, hbridge.mpr ⟨hsub, hle⟩⟩
        · rintro ⟨_, hin, hsub⟩
          obtain ⟨hsub', hle'⟩ := hbridge.mp hsub
          exact ⟨hle', hin, hsub'⟩
    · simp only [List.not_mem_nil, false_iff]
      rintro ⟨hle, hin, _⟩
      exact h ⟨hm, Nat.le_trans hle hin⟩

/-! ## Immediate-children partition of `[idx - lowbit idx, idx)` -/

/-- Immediate Fenwick children of `idx`: positive indices `c < idx` with `c + lowbit c = idx`. -/
@[expose] def fenwickChildren (idx : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (idx - 1)).filter (fun c => c + lowbit c = idx)

/-- Every path in `upChain idx m` from `m < idx` to `idx` has an immediate child `c` of `idx`
visited along `upChain idx m`. -/
private theorem exists_child_of_mem_upChain {idx m : ℕ}
    (hm : 0 < m) (hlt : m < idx) (hmem : idx ∈ upChain idx m) :
    ∃ c ∈ fenwickChildren idx, c ∈ upChain idx m := by
  generalize hrem : idx + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m with
  | ind rem ih =>
    have hlb_pos : 0 < lowbit m := lowbit_pos hm
    have hle_idx : m ≤ idx := Nat.le_of_lt hlt
    rw [upChain] at hmem
    simp only [hm, hle_idx, and_self, ↓reduceDIte, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact False.elim (Nat.lt_irrefl _ hlt)
    · have hm'_le : m + lowbit m ≤ idx := ge_of_mem_upChain htail
      rcases Nat.eq_or_lt_of_le hm'_le with heq | hlt'
      · refine ⟨m, ?_, ?_⟩
        · simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hm, by omega⟩, heq⟩
        · rw [upChain]
          simp only [hm, hle_idx, and_self, ↓reduceDIte, List.mem_cons, true_or]
      · obtain ⟨c, hc_child, hc_mem⟩ :=
          @ih (idx + 1 - (m + lowbit m)) (by omega) (m + lowbit m) (by omega) hlt' htail rfl
        refine ⟨c, hc_child, ?_⟩
        rw [upChain]
        simp only [hm, hle_idx, and_self, ↓reduceDIte, List.mem_cons, Or.inr hc_mem]

/-- Intervals `[c - lowbit c, c)` of distinct immediate Fenwick children of `idx` are disjoint. -/
theorem pairwiseDisjoint_fenwickChildren (idx : ℕ) :
    (fenwickChildren idx : Set ℕ).PairwiseDisjoint (fun c => Finset.Ico (c - lowbit c) c) := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Finset.mem_coe, fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc₁ hc₂
  change Disjoint (Finset.Ico (c₁ - lowbit c₁) c₁) (Finset.Ico (c₂ - lowbit c₂) c₂)
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  simp only [Finset.mem_Ico] at hi₁ hi₂
  rcases lt_trichotomy c₁ c₂ with hlt | rfl | hgt
  · have hsep : c₁ ≤ c₂ - lowbit c₂ := by
      by_contra hnot
      have hbridge := (fenwick_parent_bridge hc₁.1.1 hlt).mp (by omega)
      omega
    omega
  · exact hne rfl
  · have hsep : c₂ ≤ c₁ - lowbit c₁ := by
      by_contra hnot
      have hbridge := (fenwick_parent_bridge hc₂.1.1 hgt).mp (by omega)
      omega
    omega

/-- `{idx - 1}` is disjoint from all immediate-child intervals `[c - lowbit c, c)`. -/
theorem notMem_biUnion_fenwickChildren (idx : ℕ) :
    idx - 1 ∉ (fenwickChildren idx).biUnion (fun c => Finset.Ico (c - lowbit c) c) := by
  simp only [Finset.mem_biUnion, fenwickChildren, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ico, not_exists, not_and]
  intro c hc _ _
  omega

/-- For `idx > 0`, `{idx - 1}` and the intervals `[c - lowbit c, c)` of `c ∈ fenwickChildren idx`
partition `[idx - lowbit idx, idx)`. -/
theorem insert_biUnion_fenwickChildren {idx : ℕ} (hidx : 0 < idx) :
    insert (idx - 1) ((fenwickChildren idx).biUnion (fun c => Finset.Ico (c - lowbit c) c)) =
      Finset.Ico (idx - lowbit idx) idx := by
  ext i
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Ico]
  have hlb_idx : 0 < lowbit idx := lowbit_pos hidx
  have hlb_le : lowbit idx ≤ idx := lowbit_le idx
  constructor
  · rintro (rfl | ⟨c, hc, hi⟩)
    · omega
    · simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc
      have h2 := two_mul_lowbit_le_lowbit_add hc.1.1
      rw [hc.2] at h2
      have hcle := lowbit_le c
      omega
  · rintro ⟨hlo, hhi⟩
    rcases Nat.eq_or_lt_of_le (by omega : i ≤ idx - 1) with rfl | hilt
    · exact Or.inl rfl
    · right
      have hm_pos : 0 < i + 1 := by omega
      have hm_lt : i + 1 < idx := by omega
      have hmem : idx ∈ upChain idx (i + 1) :=
        (mem_upChain_iff hm_pos).mpr ⟨Nat.le_of_lt hm_lt, Nat.le_refl idx, by omega⟩
      obtain ⟨c, hc_child, hc_mem⟩ := exists_child_of_mem_upChain hm_pos hm_lt hmem
      obtain ⟨hc_ge, _, hc_sub⟩ := (mem_upChain_iff hm_pos).mp hc_mem
      exact ⟨c, hc_child, by omega, by omega⟩

end Cslib.Algorithms.Lean.FenwickTree
