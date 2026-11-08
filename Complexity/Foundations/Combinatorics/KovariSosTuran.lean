/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The Kővári–Sós–Turán bound

A set `S ⊆ α × β` of positions in a grid (equivalently, the edges of a bipartite graph between `α`
and `β`) *contains an `s × s` rectangle* when `I ×ˢ J ⊆ S` for some `s`-element sets `I ⊆ α` and
`J ⊆ β`. The **Kővári–Sós–Turán theorem** bounds the size of a set without such rectangles
(`Cslib.kovari_sos_turan`): with `m = |α|` and `n = |β|`,
`n (|S| - (s - 1) n) ^ s ≤ (s - 1) (n (m - s + 1)) ^ s`, that is,
`|S| ≤ (s - 1) ^ (1 / s) (m - s + 1) n ^ (1 - 1 / s) + (s - 1) n`. This is the form of
[Bollobás, §IV.2, Theorem 10][Bollobas1998] quoted as [Lokam2009], Lemma 2.3 (for `m = n`), stated
with natural-number powers instead of real roots. It is an upper bound for the Zarankiewicz
problem (Mathlib's `SimpleGraph.zarankiewicz` counts the analogous quantity for simple graphs).

The proof double counts pairs `(I, b)` of an `s`-element set `I ⊆ α` and a column `b` with
`I × {b} ⊆ S`: each `I` lies in fewer than `s` columns, so `∑_b C(d_b, s) ≤ (s - 1) C(m, s)`,
where `d_b` is the number of positions of `S` in column `b`. The bound
`(d + 1 - s) ^ s C(m, s) ≤ C(d, s) (m + 1 - s) ^ s` for `d ≤ m` and the power-mean inequality
`(∑_b x_b) ^ s ≤ n ^ (s - 1) ∑_b x_b ^ s` then finish the proof.

## Main results

* `Cslib.kovari_sos_turan`: the Kővári–Sós–Turán bound.

## References

* [B. Bollobás, *Modern Graph Theory*][Bollobas1998], §IV.2, Theorem 10
* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], Lemma 2.3
-/

public section

namespace Cslib

open Finset

/-- `(d + 1 - s) ^ s C(m, s) ≤ C(d, s) (m + 1 - s) ^ s` for `d ≤ m`: compare
`(d + 1 - s) (m - i) ≤ (d - i) (m + 1 - s)` factor by factor in the falling factorials. -/
private theorem pow_mul_choose_le_choose_mul_pow {d m s : ℕ} (hdm : d ≤ m) :
    (d + 1 - s) ^ s * m.choose s ≤ d.choose s * (m + 1 - s) ^ s := by
  rcases Nat.lt_or_ge d s with hds | hsd
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · rw [show d + 1 - s = 0 by omega, zero_pow hs.ne', zero_mul]
      exact Nat.zero_le _
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos s)
  calc s.factorial * ((d + 1 - s) ^ s * m.choose s)
      = (d + 1 - s) ^ s * m.descFactorial s := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
    _ = ∏ i ∈ range s, ((d + 1 - s) * (m - i)) := by
        rw [Nat.descFactorial_eq_prod_range, prod_mul_distrib, prod_const, card_range]
    _ ≤ ∏ i ∈ range s, ((d - i) * (m + 1 - s)) := by
        refine prod_le_prod fun i hi => ?_
        rw [mem_range] at hi
        obtain ⟨k, rfl⟩ : ∃ k, s = i + k + 1 := ⟨s - i - 1, by omega⟩
        obtain ⟨a, rfl⟩ : ∃ a, d = i + a := ⟨d - i, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, m = i + b := ⟨m - i, by omega⟩
        rw [show i + a + 1 - (i + k + 1) = a - k by omega, show i + b - i = b by omega,
          show i + a - i = a by omega, show i + b + 1 - (i + k + 1) = b - k by omega]
        have hab : a ≤ b := by omega
        have hka : k ≤ a := by omega
        obtain ⟨a, rfl⟩ : ∃ a', a = k + a' := ⟨a - k, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b', b = k + a + b' := ⟨b - k - a, by omega⟩
        rw [show k + a - k = a by omega, show k + a + b - k = a + b by omega]
        nlinarith
    _ = s.factorial * (d.choose s * (m + 1 - s) ^ s) := by
        rw [prod_mul_distrib, prod_const, card_range, ← Nat.descFactorial_eq_prod_range,
          Nat.descFactorial_eq_factorial_mul_choose]; ring

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **The Kővári–Sós–Turán theorem** ([Bollobás, §IV.2, Theorem 10][Bollobas1998];
[Lokam2009], Lemma 2.3). If a set `S` of positions in an `m × n` grid (`m = |α|`, `n = |β|`)
contains no `s × s` rectangle `I ×ˢ J`, then
`n (|S| - (s - 1) n) ^ s ≤ (s - 1) (n (m + 1 - s)) ^ s`. Taking `s`-th roots gives the classical
`|S| ≤ (s - 1) ^ (1 / s) (m - s + 1) n ^ (1 - 1 / s) + (s - 1) n`. -/
theorem kovari_sos_turan (S : Finset (α × β)) {s : ℕ}
    (hS : ∀ I : Finset α, ∀ J : Finset β, #I = s → #J = s → ¬ I ×ˢ J ⊆ S) :
    Fintype.card β * (#S - (s - 1) * Fintype.card β) ^ s ≤
      (s - 1) * (Fintype.card β * (Fintype.card α + 1 - s)) ^ s := by
  classical
  set m := Fintype.card α
  set n := Fintype.card β
  -- The column of `S` at `b`, and its size.
  set col : β → Finset α := fun b => univ.filter fun a => (a, b) ∈ S with hcol
  have hsum : ∑ b, #(col b) = #S := by
    rw [← card_sigma]
    refine card_bij (fun p _ => (p.2, p.1)) (fun p hp => by simpa [hcol] using hp) ?_ ?_
    · rintro ⟨b, a⟩ - ⟨b', a'⟩ - h
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · rintro ⟨a, b⟩ h
      exact ⟨⟨b, a⟩, by simpa [hcol] using h, rfl⟩
  -- Each `s`-element set of rows lies in fewer than `s` columns.
  have hfew : ∀ I ∈ powersetCard s (univ : Finset α),
      #(univ.filter fun b => I ⊆ col b) ≤ s - 1 := by
    intro I hI
    rw [mem_powersetCard] at hI
    by_contra hlt
    obtain ⟨J, hJ, hJcard⟩ := exists_subset_card_eq (s := univ.filter fun b => I ⊆ col b)
      (n := s) (by omega)
    refine hS I J hI.2 hJcard fun p hp => ?_
    rw [mem_product] at hp
    have := (mem_filter.1 (hJ hp.2)).2 hp.1
    simpa [hcol] using this
  -- Double counting: `∑_b C(d_b, s) ≤ (s - 1) C(m, s)`.
  have hdouble : ∑ b, (#(col b)).choose s ≤ (s - 1) * m.choose s := by
    have key := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := powersetCard s (univ : Finset α)) (t := (univ : Finset β)) (r := fun I b => I ⊆ col b)
    calc ∑ b, (#(col b)).choose s
        = ∑ b, #((powersetCard s (univ : Finset α)).bipartiteBelow (fun I b => I ⊆ col b) b) := by
          refine sum_congr rfl fun b _ => ?_
          rw [← card_powersetCard, bipartiteBelow]
          congr 1
          ext I
          simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
          tauto
      _ = ∑ I ∈ powersetCard s (univ : Finset α),
            #((univ : Finset β).bipartiteAbove (fun I b => I ⊆ col b) I) := key.symm
      _ ≤ ∑ _I ∈ powersetCard s (univ : Finset α), (s - 1) := sum_le_sum hfew
      _ = (s - 1) * m.choose s := by
          rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, mul_comm]
  -- If `s = 0`, the empty rectangle is in `S`, which is impossible.
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact absurd (empty_subset S) (by simpa using hS ∅ ∅)
    · exact ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show m + 1 - (t + 1) = m - t by omega]
  -- The column sizes, shifted down by `t`.
  set x : β → ℕ := fun b => #(col b) - t with hx
  have hcolm : ∀ b, #(col b) ≤ m := fun b => card_le_univ _
  rcases Nat.lt_or_ge m (t + 1) with hm | hm
  · -- Too few rows: every column has at most `t` positions.
    have hS' : #S ≤ t * n := by
      rw [← hsum]
      calc ∑ b, #(col b) ≤ ∑ _b : β, t := sum_le_sum fun b _ => by have := hcolm b; omega
        _ = t * n := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
    rw [show #S - t * n = 0 by omega, zero_pow (Nat.succ_ne_zero t), mul_zero]
    exact Nat.zero_le _
  have hchoose : 0 < m.choose (t + 1) := Nat.choose_pos hm
  -- `∑_b x_b ^ (t + 1) ≤ t (m - t) ^ (t + 1)`.
  have hpow : (∑ b, x b ^ (t + 1)) ≤ t * (m - t) ^ (t + 1) := by
    refine Nat.le_of_mul_le_mul_right ?_ hchoose
    calc (∑ b, x b ^ (t + 1)) * m.choose (t + 1)
        = ∑ b, (#(col b) + 1 - (t + 1)) ^ (t + 1) * m.choose (t + 1) := by
          rw [sum_mul]
          refine sum_congr rfl fun b _ => ?_
          rw [hx, show #(col b) + 1 - (t + 1) = #(col b) - t by omega]
      _ ≤ ∑ b, (#(col b)).choose (t + 1) * (m + 1 - (t + 1)) ^ (t + 1) :=
          sum_le_sum fun b _ => pow_mul_choose_le_choose_mul_pow (hcolm b)
      _ = (∑ b, (#(col b)).choose (t + 1)) * (m - t) ^ (t + 1) := by
          rw [sum_mul, show m + 1 - (t + 1) = m - t by omega]
      _ ≤ (t * m.choose (t + 1)) * (m - t) ^ (t + 1) := by
          gcongr
          simpa using hdouble
      _ = t * (m - t) ^ (t + 1) * m.choose (t + 1) := by ring
  -- `|S| - t n ≤ ∑_b x_b`.
  have hlin : #S - t * n ≤ ∑ b, x b := by
    rw [← hsum]
    have : ∑ b, #(col b) ≤ ∑ b, x b + t * n :=
      calc ∑ b, #(col b) ≤ ∑ b, (x b + t) :=
            sum_le_sum fun b _ => by simp only [hx]; omega
        _ = ∑ b, x b + t * n := by
            rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_comm]
    omega
  calc n * (#S - t * n) ^ (t + 1)
      ≤ n * (∑ b, x b) ^ (t + 1) := by gcongr
    _ ≤ n * (n ^ t * ∑ b, x b ^ (t + 1)) := by
        gcongr
        simpa [card_univ] using pow_sum_le_card_mul_sum_pow (s := (univ : Finset β)) (f := x)
          (fun _ _ => Nat.zero_le _) t
    _ ≤ n * (n ^ t * (t * (m - t) ^ (t + 1))) := by gcongr
    _ = t * (n * (m - t)) ^ (t + 1) := by ring

end Cslib
