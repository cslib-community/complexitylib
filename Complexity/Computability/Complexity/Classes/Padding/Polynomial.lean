/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Tactic.Linarith

/-!
# Degree-preserving deterministic padding

A collapse from time `(n + 1) ^ b` to `(n + 1) ^ a`, where `b ≥ 2`, propagates after
multiplying the exponents by a positive integer `k`, with the target exponent at least `k + 1`.
The padded language checks whether the word framed at the start has length `m` with
`(m + 1) ^ k ≤ n`, then decides the original language on that word. On inputs that fail the
test it immediately rejects. The test costs quadratic time. Rounding the padding length up to
`2 ^ (k * Nat.size (m + 1))` permits a writer of time `O((m + 1) ^ (k + 1))`.

This specializes the standard translation argument
[Fortnow and Santhanam, §3.3, Lemma 5][FortnowSanthanam2006] to integer powers with all native
computation costs proved. No class-closure or simulation
hypothesis is hidden in the statement. If `a ≥ 2`, the writer cost is absorbed by `a * k`.
If `a = 1`, the explicit writer overhead remains available for hierarchy amplification.

## Main results

* `Cslib.Complexity.DTIME_pow_mul_subset_of_subset`: a deterministic polynomial-time collapse
  propagates after multiplying both exponents by the same positive integer.
* `Cslib.Complexity.DTIME_pow_mul_subset_of_subset_max`: the more general transfer retaining
  the writer overhead, including a collapse from quadratic to linear time.

## References

* [L. Fortnow and R. Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A polynomial-time collapse propagates under padding, retaining the degree `k + 1` needed
by the native padding writer. The quadratic guard requires `b ≥ 2`, but `a` may be linear. -/
theorem DTIME_pow_mul_subset_of_subset_max {a b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (h : DTIME encBits (fun n => (n + 1) ^ b) ⊆ DTIME encBits (fun n => (n + 1) ^ a)) :
    DTIME encBits (fun n => (n + 1) ^ (b * k)) ⊆
      DTIME encBits (fun n => (n + 1) ^ (max (a * k) (k + 1))) := by
  intro A hA
  classical
  let guard (x : List Bool) := decide (((unframe x).length + 1) ^ k ≤ x.length)
  let B : Set (List Bool) :=
    {x | (if guard x then indicator A (unframe x) else false) = true}
  have hu : ComputableInO unframe encBits encBits
      (fun x => x.length) (fun x => x.length) :=
    .of_linear (.of_unframe fun _ => rfl)
  have hdec := (computableInO_polynomialPaddingGuard k).ite
    ((computableInO_indicator_of_mem_DTIME hA).comp hu)
    (ComputableInO.const (encMid := encBool) false)
  have hB : B ∈ DTIME encBits (fun n => (n + 1) ^ b) := by
    refine setOf_mem_DTIME_of_computableInO
      (hdec.mono (T' := fun x => (x.length + 1) ^ b)
        (S' := fun x => (x.length + 1) ^ b) 4 (fun x => ?_) fun x => ?_) (fun _ => le_rfl)
    all_goals
      have hlen : x.length ≤ (x.length + 1) ^ b :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
      have hsq : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ b :=
        Nat.pow_le_pow_right (by omega) hb
      dsimp only [Function.comp_apply, encBits_apply]
      split_ifs with hg
      · have hg' := of_decide_eq_true hg
        have hpow : ((unframe x).length + 1) ^ (b * k) ≤ (x.length + 1) ^ b := by
          rw [Nat.mul_comm b k, pow_mul]
          exact Nat.pow_le_pow_left (by omega) b
        omega
      · omega
  let pad (x : List Bool) := frame x ++
    List.replicate (2 ^ (k * Nat.size (x.length + 1))) true
  have hlen (x : List Bool) :
      (pad x).length = 2 * x.length + 1 + 2 ^ (k * Nat.size (x.length + 1)) := by
    simp only [pad, List.length_append, length_frame, List.length_replicate]
  have hguard (x : List Bool) : guard (pad x) = true := by
    simp only [guard, pad, unframe_frame_append, List.length_append, length_frame,
      List.length_replicate]
    have hp := (polynomialPaddingPower_bounds k x.length).1
    exact decide_eq_true (by omega)
  have hpre : A = pad ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage, B, Set.mem_ofPred_eq, hguard, ↓reduceIte,
      pad, unframe_frame_append]
    simp [indicator]
  rw [hpre]
  refine preimage_mem_DTIME (C := (2 + 2 ^ k) ^ a + 1) (h hB)
    (computableInO_roundedPolynomialPadding hk) fun x => ?_
  simp only [encBits_apply, hlen]
  have hp : x.length + 1 ≤ (x.length + 1) ^ k := Nat.le_self_pow (by omega) _
  have htime : (x.length + 1) ^ (k + 1) ≤
      (x.length + 1) ^ (max (a * k) (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hpad : (2 * x.length + 1 + 2 ^ (k * Nat.size (x.length + 1)) + 1) ^ a ≤
      (2 + 2 ^ k) ^ a * (x.length + 1) ^ (max (a * k) (k + 1)) := by
    calc
      _ ≤ ((2 + 2 ^ k) * (x.length + 1) ^ k) ^ a := by
        apply Nat.pow_le_pow_left _ a
        have := (polynomialPaddingPower_bounds k x.length).2
        nlinarith
      _ = (2 + 2 ^ k) ^ a * (x.length + 1) ^ (a * k) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k a]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  rw [Nat.add_mul, one_mul]
  exact (Nat.add_le_add htime hpad).trans
    ((le_of_eq (Nat.add_comm _ _)).trans (Nat.le_add_right _ _))

/-- A collapse between polynomial time degrees at least two propagates under polynomial padding.
Both the native guard cost and the rounded writer cost fit within the transferred bounds. -/
theorem DTIME_pow_mul_subset_of_subset {a b k : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hk : 1 ≤ k)
    (h : DTIME encBits (fun n => (n + 1) ^ b) ⊆ DTIME encBits (fun n => (n + 1) ^ a)) :
    DTIME encBits (fun n => (n + 1) ^ (b * k)) ⊆
      DTIME encBits (fun n => (n + 1) ^ (a * k)) := by
  have hcost : k + 1 ≤ a * k := by nlinarith
  simpa only [max_eq_left hcost] using DTIME_pow_mul_subset_of_subset_max (ha.trans hab) hk h

end Cslib.Complexity
