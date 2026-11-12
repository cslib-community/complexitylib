/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Max

/-!
# Uniqueness of radix expansions with digits at distinct positions

A sum `∑ i ∈ s, d i * B ^ e i` with digits `d i < B` at distinct positions `e i` determines its
digits. This is the uniqueness of base-`B` expansions, stated for digits indexed by an arbitrary
finite set; for digits `0` and `1` it is `Finset.geomSum_injective`.

## Main results

* `Nat.eq_of_sum_mul_pow_eq`: two such sums are equal only if their digits are.
-/

public section

namespace Nat

open Finset

/-- A sum of digits `d i < B` weighted by powers `B ^ e i` at distinct positions `e i` determines
the digits. -/
theorem eq_of_sum_mul_pow_eq {ι : Type*} {B : ℕ} {s : Finset ι} {e : ι → ℕ}
    (he : Set.InjOn e s) {d d' : ι → ℕ} (hd : ∀ i ∈ s, d i < B) (hd' : ∀ i ∈ s, d' i < B)
    (h : ∑ i ∈ s, d i * B ^ e i = ∑ i ∈ s, d' i * B ^ e i) : ∀ i ∈ s, d i = d' i := by
  classical
  induction s using Finset.induction_on_min_value e with
  | empty => simp
  | insert a s ha hmin ih =>
    have hB : 0 < B := (Nat.zero_le _).trans_lt (hd a (mem_insert_self a s))
    have hmod : ∀ c : ι → ℕ, c a < B →
        (∑ i ∈ insert a s, c i * B ^ e i) % B ^ (e a + 1) = c a * B ^ e a := fun c hc => by
      have hdvd : B ^ (e a + 1) ∣ ∑ i ∈ s, c i * B ^ e i := Finset.dvd_sum fun x hx =>
        Dvd.dvd.mul_left (pow_dvd_pow B (lt_of_le_of_ne (hmin x hx) fun hax =>
          ha (he (mem_coe.2 (mem_insert_self a s)) (mem_coe.2 (mem_insert_of_mem hx)) hax ▸ hx))) _
      rw [sum_insert ha, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt]
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos hB)
    have hda : d a = d' a := Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hB) <| by
      rw [← hmod d (hd a (mem_insert_self a s)), ← hmod d' (hd' a (mem_insert_self a s)), h]
    rw [sum_insert ha, sum_insert ha, hda] at h
    intro i hi
    rcases mem_insert.1 hi with rfl | hi
    · exact hda
    · exact ih (he.mono (coe_subset.2 (subset_insert a s)))
        (fun i hi => hd i (mem_insert_of_mem hi)) (fun i hi => hd' i (mem_insert_of_mem hi))
        (Nat.add_left_cancel h) i hi

end Nat
