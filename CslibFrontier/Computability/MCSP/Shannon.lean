/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Basic
public import Cslib.Computability.Circuit.Boolean.Lupanov
public import Cslib.Computability.Circuit.Boolean.Shannon
import CslibFrontier.Foundations.Data.Nat.Factorial
import Mathlib.Tactic.Linarith

/-!
# The Shannon window of MCSP

Every Boolean function on `n` inputs has a circuit with about `2 ^ n / n` gates, and most of them
need about that many [Shannon1949], [Lupanov1958]. So for uniformly random truth tables the answer
to MCSP changes near threshold `2 ^ n / n`: above it every truth table is a yes-instance, and below
it almost every truth table is a no-instance. This is a statement about the distribution of
circuit complexities, not about the difficulty of deciding MCSP: at lower thresholds the rare
yes-instances must still be recognized exactly, and that regime is the one studied by hardness
magnification [OliveiraPichSanthanam2019]. This file states the window with explicit constants
and explicit arities:

* for `n ≥ 64`, every truth table is a yes-instance at threshold `12 · 2 ^ n / n`
  (`MCSP.mem_of_twelve_mul_le`), by Lupanov's construction with explicit parameters;
* for `n ≥ 16`, at most `2 ^ (2 ^ n / 4)` of the `2 ^ (2 ^ n)` truth tables are yes-instances at
  threshold `2 ^ n / (5 n)` (`MCSP.ncard_setOf_mem_le`), by counting circuits.

It also states the asymptotically sharp window, from cslib's Lupanov and Shannon bounds: for
every `ε > 0` and all large `n`, every truth table is a yes-instance at threshold
`(1 + ε) 2 ^ n / n` (`MCSP.eventually_mem`), and some truth table is a no-instance at threshold
`2 ^ n / n` (`MCSP.eventually_exists_notMem`).

Sizes count every AND, OR, NOT and constant gate.

## Main results

* `Cslib.MCSP.mem_of_twelve_mul_le`, `Cslib.MCSP.ncard_setOf_mem_le`,
  `Cslib.MCSP.exists_notMem`: the explicit window.
* `Cslib.MCSP.eventually_mem`, `Cslib.MCSP.eventually_exists_notMem`: the sharp window.

## References

* [C. E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949]
* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958]
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012],
  Theorems 1.14 and 1.15.
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean

/-! ### Elementary estimates -/

private theorem add_le_two_pow {l : ℕ} (hl : 6 ≤ l) : 6 * l + 9 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l _ ih => rw [pow_succ]; omega

private theorem mul_sq_le_two_pow {n : ℕ} (hn : 16 ≤ n) : 64 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 64 * (n + 1) ^ 2 ≤ 2 * (64 * n ^ 2) := by nlinarith
      _ ≤ 2 ^ (n + 1) := by rw [pow_succ 2 n]; omega

/-! ### Every function has a circuit with `12 · 2 ^ n / n` gates -/

/-- Lupanov's budget for a split of `n = k + d` inputs bounds the complexity of every function on
`n` inputs. -/
private theorem complexity_le_bound {n k d s : ℕ} (h : k + d = n) (hs : 0 < s)
    (f : BooleanFunction n) : complexity interpretation (single f) ≤ Lupanov.bound k d s := by
  subst h
  exact (Lupanov.synthesis f hs).complexity_le

/-- With `l = ⌊log₂ n⌋`, `2 l + 3` address bits and blocks of `n - (3 l + 4)` rows, Lupanov's
budget is at most `12 · 2 ^ n / n` once `n ≥ 64`. -/
private theorem mul_bound_le {n : ℕ} (hn : 64 ≤ n) :
    n * Lupanov.bound (2 * Nat.log2 n + 3) (n - (2 * Nat.log2 n + 3))
      (n - (3 * Nat.log2 n + 4)) ≤ 12 * 2 ^ n := by
  have hn0 : n ≠ 0 := by omega
  have hl : 6 ≤ Nat.log2 n := (Nat.le_log2 hn0).mpr (le_trans (by norm_num) hn)
  have hhigh : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hlow := (add_le_two_pow hl).trans (Nat.log2_self_le hn0)
  generalize Nat.log2 n = l at hl hhigh hlow
  set k := 2 * l + 3
  set d := n - k
  set s := n - (3 * l + 4)
  have hkd : k + d = n := by omega
  have hs : 4 ≤ s := by omega
  have hns : n ≤ 2 * s := by omega
  -- The powers of two involved, with `P = 2 ^ (2 l + 2) > n ^ 2`.
  have hA : 2 ^ k = 2 * 2 ^ (2 * l + 2) := by
    rw [show k = 1 + (2 * l + 2) by omega, pow_add, pow_one]
  have hP : n * n < 2 ^ (2 * l + 2) := by
    calc n * n < 2 ^ (l + 1) * 2 ^ (l + 1) := Nat.mul_lt_mul'' hhigh hhigh
      _ = 2 ^ (2 * l + 2) := by rw [← pow_add]; congr 1; omega
  have hAB : 2 * (2 ^ (2 * l + 2) * 2 ^ d) = 2 ^ n := by
    rw [← mul_assoc, ← hA, ← pow_add, hkd]
  have hAC : 2 * (2 ^ (l + 1) * (2 ^ (2 * l + 2) * 2 ^ s)) = 2 ^ n := by
    rw [← pow_add, ← pow_add, ← pow_succ']; congr 1; omega
  have hCP : 4 * (2 ^ s * 2 ^ (2 * l + 2)) ≤ 2 ^ n := by
    calc 4 * (2 ^ s * 2 ^ (2 * l + 2)) = 2 ^ (s + (2 * l + 4)) := by
          rw [show 2 * l + 4 = 2 * l + 2 + 2 by omega, pow_add, pow_add]; ring
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (by omega)
  have hPP : 8 * (2 ^ (2 * l + 2) * 2 ^ (2 * l + 2)) ≤ 2 ^ n := by
    calc 8 * (2 ^ (2 * l + 2) * 2 ^ (2 * l + 2)) = 2 ^ (4 * l + 7) := by
          rw [← pow_add, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
          congr 1
          omega
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (by omega)
  have hn2 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have hq : 2 ^ k / s * s ≤ 2 * 2 ^ (2 * l + 2) := hA ▸ Nat.div_mul_le_self _ _
  have hbound : n * Lupanov.bound k d s =
      4 * (n * n * 2 ^ (2 * l + 2)) + 2 * (n * 2 ^ (2 * l + 2)) + 2 * (n * n * 2 ^ d) + n * 2 ^ d +
        n * (2 ^ k / s * (2 ^ s * (2 * s + 4))) + n * (2 ^ k / s * 2 ^ d) +
        n * (2 ^ s * (2 * s + 4)) + n * 2 ^ d + n := by
    rw [Lupanov.bound, hkd, hA]; ring
  rw [hbound]
  -- Each term is at most a small multiple of `2 ^ n`.
  generalize 2 ^ k / s = q at hq
  generalize 2 ^ (2 * l + 2) = P at hq hP hAB hAC hCP hPP
  generalize 2 ^ (l + 1) = H at hhigh hAC
  generalize 2 ^ n = N at hAB hAC hCP hPP hn2 ⊢
  generalize 2 ^ d = B at hAB ⊢
  generalize 2 ^ s = C at hAC hCP ⊢
  have h1 : 1 ≤ n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have ha : n * n * P ≤ P * P := Nat.mul_le_mul_right P hP.le
  have ha' : n * P ≤ P * P := (Nat.mul_le_mul_right P hnn).trans ha
  have hb : n * n * B ≤ P * B := Nat.mul_le_mul_right B hP.le
  have hb' : n * B ≤ P * B := (Nat.mul_le_mul_right B hnn).trans hb
  have hc : n * (q * (C * (2 * s + 4))) ≤ 3 * (H * (P * C)) * 2 := by
    calc n * (q * (C * (2 * s + 4))) ≤ n * (q * (C * (3 * s))) := by gcongr; omega
      _ = 3 * (n * C * (q * s)) := by ring
      _ ≤ 3 * (H * C * (2 * P)) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul (Nat.mul_le_mul_right C hhigh.le) hq)
      _ = 3 * (H * (P * C)) * 2 := by ring
  have hd : n * (q * B) ≤ 2 * (2 * (P * B)) := by
    calc n * (q * B) ≤ 2 * s * (q * B) := Nat.mul_le_mul_right _ hns
      _ = 2 * (q * s * B) := by ring
      _ ≤ 2 * (2 * P * B) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right B hq)
      _ = 2 * (2 * (P * B)) := by ring
  have he : n * (C * (2 * s + 4)) ≤ 3 * (C * P) := by
    calc n * (C * (2 * s + 4)) ≤ n * (C * (3 * n)) := by gcongr; omega
      _ = 3 * (n * n * C) := by ring
      _ ≤ 3 * (P * C) := by gcongr
      _ = 3 * (C * P) := by ring
  omega

/-! ### Few functions have a circuit with `2 ^ n / (5 n)` gates -/

/-- For `n ≥ 16`, at most `2 ^ (2 ^ n / 4)` Boolean functions on `n` inputs have a circuit with
at most `2 ^ n / (5 n)` gates. -/
private theorem card_computableFunctions_le {n : ℕ} (hn : 16 ≤ n) :
    (computableFunctions n (2 ^ n / (5 * n))).card ≤ 2 ^ (2 ^ n / 4) := by
  set s := 2 ^ n / (5 * n)
  set c := (computableFunctions n s).card
  have h64 := mul_sq_le_two_pow hn
  have hsn : 5 * n * s ≤ 2 ^ n := Nat.mul_div_le _ _
  have hs : n + 1 ≤ s := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hs64 : 64 * s ≤ 2 ^ n := le_trans (Nat.mul_le_mul_right s (by omega : 64 ≤ 5 * n)) hsn
  -- Shannon's count, simplified with `n + 1 ≤ s` and `s ^ s ≤ 3 ^ s s!`.
  have hcount : c * s.factorial ≤ 4 * s ^ 2 * (20 * s ^ 2) ^ s := by
    refine (card_computableFunctions_mul_factorial_le n s).trans ?_
    calc (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s)
        ≤ (2 * s) * (5 * (2 * s) ^ 2) ^ s * (2 * s) := by gcongr <;> omega
      _ = 4 * s ^ 2 * (20 * s ^ 2) ^ s := by ring
  have hc : c * s ^ s ≤ 4 * s ^ 2 * (60 * s) ^ s * s ^ s := by
    calc c * s ^ s ≤ c * (3 ^ s * s.factorial) :=
          Nat.mul_le_mul_left _ (Nat.pow_self_le_three_pow_mul_factorial s)
      _ = 3 ^ s * (c * s.factorial) := by ring
      _ ≤ 3 ^ s * (4 * s ^ 2 * (20 * s ^ 2) ^ s) := Nat.mul_le_mul_left _ hcount
      _ = 4 * s ^ 2 * (60 * s) ^ s * s ^ s := by
        rw [mul_pow, mul_pow, show (60 : ℕ) ^ s = 3 ^ s * 20 ^ s by rw [← mul_pow]; norm_num]; ring
  have hc' : c ≤ 4 * s ^ 2 * (60 * s) ^ s :=
    Nat.le_of_mul_le_mul_right hc (pow_pos (by omega) s)
  have hexp : n * (s + 2) ≤ 2 ^ n / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    nlinarith
  calc c ≤ 4 * s ^ 2 * (60 * s) ^ s := hc'
    _ ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ s := by
        gcongr
        · nlinarith
        · omega
    _ = 2 ^ (n * (s + 2)) := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (2 ^ n / 4) := Nat.pow_le_pow_right two_pos hexp

/-! ### The explicit window -/

variable {n s : ℕ}

/-- **Above the window.** For `n ≥ 64`, every truth table of a function on `n` inputs is a
yes-instance of MCSP at every threshold of at least `12 · 2 ^ n / n`. -/
theorem mem_of_twelve_mul_le (hn : 64 ≤ n) (T : BitString (2 ^ n)) (hs : 12 * 2 ^ n / n ≤ s) :
    ⟨n, T, s⟩ ∈ MCSP := by
  have hn0 : n ≠ 0 := by omega
  have hlow := (add_le_two_pow ((Nat.le_log2 hn0).mpr (le_trans (by norm_num) hn))).trans
    (Nat.log2_self_le hn0)
  obtain ⟨f, rfl⟩ := (truthTable n).surjective T
  rw [mk_truthTable_mem_iff]
  refine le_trans ((complexity_le_bound (k := 2 * Nat.log2 n + 3) (d := n - (2 * Nat.log2 n + 3))
    (s := n - (3 * Nat.log2 n + 4)) (by omega) (by omega) f).trans ?_) hs
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact mul_bound_le hn)

/-- **Below the window.** For `n ≥ 16`, at most `2 ^ (2 ^ n / 4)` of the `2 ^ (2 ^ n)` truth
tables of functions on `n` inputs are yes-instances of MCSP at threshold `2 ^ n / (5 n)`. -/
theorem ncard_setOf_mem_le (hn : 16 ≤ n) :
    {T : BitString (2 ^ n) | ⟨n, T, 2 ^ n / (5 * n)⟩ ∈ MCSP}.ncard ≤ 2 ^ (2 ^ n / 4) := by
  rw [ncard_setOf_mem]
  exact card_computableFunctions_le hn

/-- For `n ≥ 16`, some truth table of a function on `n` inputs is a no-instance of MCSP at
threshold `2 ^ n / (5 n)`. -/
theorem exists_notMem (hn : 16 ≤ n) : ∃ T : BitString (2 ^ n), ⟨n, T, 2 ^ n / (5 * n)⟩ ∉ MCSP := by
  by_contra! h
  have huniv : {T : BitString (2 ^ n) | ⟨n, T, 2 ^ n / (5 * n)⟩ ∈ MCSP} = Set.univ :=
    Set.eq_univ_of_forall h
  have := ncard_setOf_mem_le hn
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at this
  exact absurd this (not_le.mpr (Nat.pow_lt_pow_right one_lt_two (Nat.div_lt_self
    (Nat.two_pow_pos n) (by norm_num))))

/-! ### The sharp window -/

/-- **Above the sharp window** [Lupanov1958]. For every `ε > 0` and all large `n`, every truth
table of a function on `n` inputs is a yes-instance of MCSP at every threshold of at least
`(1 + ε) 2 ^ n / n`. -/
theorem eventually_mem (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (T : BitString (2 ^ n)) (s : ℕ), (1 + ε) * 2 ^ n / n ≤ s →
      ⟨n, T, s⟩ ∈ MCSP := by
  obtain ⟨N, hN⟩ := Lupanov.complexity_le ε hε
  exact ⟨N, fun n hn T s hs => by exact_mod_cast (hN n hn _).trans hs⟩

/-- **Below the sharp window** [Shannon1949]. For all large `n`, some truth table of a function
on `n` inputs is a no-instance of MCSP at threshold `2 ^ n / n`. -/
theorem eventually_exists_notMem :
    ∃ N : ℕ, ∀ n ≥ N, ∃ T : BitString (2 ^ n), ⟨n, T, 2 ^ n / n⟩ ∉ MCSP := by
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n hn
  refine ⟨truthTable n f, fun h => ?_⟩
  rw [mk_truthTable_mem_iff] at h
  have : ((2 ^ n / n : ℕ) : ℝ) ≤ 2 ^ n / n := by exact_mod_cast Nat.cast_div_le
  exact absurd (hf.trans_le (by exact_mod_cast h)) (not_lt.mpr this)

end Cslib.MCSP
