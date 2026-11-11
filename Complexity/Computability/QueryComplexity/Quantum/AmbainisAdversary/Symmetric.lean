/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.AmbainisAdversary
public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Foundations.Data.BitString.Sign
public import Complexity.Foundations.Data.BitString.Threshold
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Bounded-error parity, threshold functions and majority by the adversary method

Ambainis's adversary bound across single bit flips
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors`) gives the `Ω(N)` lower bounds for
parity and majority that [Ambainis2002], §5.3, derives from Theorem 2, and the threshold bound
behind them.

* **Parity.** Every bit flip changes the parity, so the inputs of odd and of even parity have `N`
  neighbors across. An algorithm computing `PARITY_N` with error `ε ≤ 1/2` therefore has
  `(1 - 2√(ε(1-ε))) N ≤ 2T` (`Cslib.Quantum.one_sub_mul_card_le_two_mul_of_parity`), and
  `N ≤ 36 T` at error `1/3` (`Cslib.Quantum.card_le_thirty_six_mul_of_parity`). This is
  bounded-error. The exact bound `N ≤ 2T` is `Cslib.Quantum.card_le_two_mul_of_parity`.
* **Weight `k` against weight `k - 1`.** An input of weight `k` has `k` neighbors of weight
  `k - 1`, and an input of weight `k - 1` has `N - k + 1` neighbors of weight `k`. So an algorithm
  that tells the two layers apart with error `ε ≤ 1/2`, and need not be correct on any other input,
  has `(1 - 2√(ε(1-ε))) √(k (N + 1 - k)) ≤ 2T`
  (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_weight`). The same holds for the threshold
  function `Th^N_k` (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_threshold`).
* **Majority.** For `k = ⌈N/2⌉`, `k (N + 1 - k) ≥ N² / 4`, so computing `MAJ_N` with error
  `ε ≤ 1/2` needs `(1 - 2√(ε(1-ε))) N ≤ 4T`
  (`Cslib.Quantum.one_sub_mul_card_le_four_mul_of_majority`), and `N ≤ 72 T` at error `1/3`
  (`Cslib.Quantum.card_le_seventy_two_mul_of_majority`).

For total functions the parity and threshold bounds would also follow from the
spectral-sensitivity bound `Cslib.Quantum.one_sub_mul_spectralSensitivity_le`, since
`λ(PARITY_N) = N` and `λ(Th^N_k) = √(k (N - k + 1))`; the library does not prove these values.
The layer bound
`one_sub_mul_sqrt_le_two_mul_of_weight` constrains the algorithm only on two weight layers. The
constants are those of this proof. The source states `Ω(N)` bounds.

## Main results

* `Cslib.Quantum.one_sub_mul_card_le_two_mul_of_parity`: `(1 - 2√(ε(1-ε))) N ≤ 2T` for parity.
* `Cslib.Quantum.card_le_thirty_six_mul_of_parity`: `N ≤ 36 T` for parity at error `1/3`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_weight`: weight `k` against weight `k - 1`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_threshold`: the threshold function `Th^N_k`.
* `Cslib.Quantum.one_sub_mul_card_le_four_mul_of_majority`: `(1 - 2√(ε(1-ε))) N ≤ 4T` for
  majority.
* `Cslib.Quantum.card_le_seventy_two_mul_of_majority`: `N ≤ 72 T` for majority at error `1/3`.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
-/

public section

namespace Cslib.Quantum

open Finset Function BitString

variable {N : ℕ} {W : Type*} [Fintype W]

/-- **Bounded-error parity takes `Ω(N)` queries** [Ambainis2002], §5.3: if a `T`-query algorithm
with a unit initial state accepts every input `x`, by an outcome in `S`, with probability within
`ε ≤ 1/2` of the parity of `x`, then `(1 - 2√(ε(1-ε))) N ≤ 2T`. -/
theorem one_sub_mul_card_le_two_mul_of_parity (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (parity N x)| ≤ ε) (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * N ≤ 2 * T := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  set A : Finset (BitString N) := {x | parity N x = true}
  set B : Finset (BitString N) := {x | parity N x = false}
  have hflip (x : BitString N) (i : Fin N) : parity N (update x i (!x i)) = !parity N x :=
    parity_update_not x i
  have hA : A.Nonempty := by
    cases h0 : parity N (fun _ => false)
    · have := hflip (fun _ => false) ⟨0, hN⟩
      rw [h0] at this
      exact ⟨_, mem_filter.2 ⟨mem_univ _, this⟩⟩
    · exact ⟨fun _ => false, mem_filter.2 ⟨mem_univ _, h0⟩⟩
  have h₁ : ∀ x ∈ A, 1 - ε ≤ measureProb (run U ψ₀ x T) S := by
    intro x hx
    have hx' : parity N x = true := (mem_filter.1 hx).2
    have := (abs_le.1 (h x)).1
    rw [hx', bitVal_true] at this
    linarith
  have h₂ : ∀ y ∈ B, measureProb (run U ψ₀ y T) S ≤ ε := by
    intro y hy
    have hy' : parity N y = false := (mem_filter.1 hy).2
    have := (abs_le.1 (h y)).2
    rw [hy', bitVal_false] at this
    linarith
  have hm : ∀ x ∈ A, N ≤ #{i | update x i (!x i) ∈ B} := by
    intro x hx
    have hx' : parity N x = true := (mem_filter.1 hx).2
    refine le_of_eq ?_
    rw [filter_true_of_mem fun i _ => by simp [B, hflip, hx'], card_univ, Fintype.card_fin]
  have hm' : ∀ y ∈ B, N ≤ #{i | update y i (!y i) ∈ A} := by
    intro y hy
    have hy' : parity N y = false := (mem_filter.1 hy).2
    refine le_of_eq ?_
    rw [filter_true_of_mem fun i _ => by simp [A, hflip, hy'], card_univ, Fintype.card_fin]
  have := one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors U hψ₀ T S hA h₁ h₂ hε hm hm'
  rwa [Real.sqrt_mul_self (Nat.cast_nonneg N)] at this

/-- **Bounded-error parity takes `N / 36` queries**: if a `T`-query algorithm with a unit
initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3` of the
parity of `x`, then `N ≤ 36 T`. -/
theorem card_le_thirty_six_mul_of_parity (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (parity N x)| ≤ 1 / 3) :
    N ≤ 36 * T := by
  have := one_sub_mul_card_le_two_mul_of_parity U hψ₀ T S h (by norm_num)
  -- `2√(2/9) ≤ 17/18`, since `8/9 = 288/324 ≤ 289/324`
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : (N : ℝ) ≤ 36 * T := by nlinarith
  exact_mod_cast this

/-- **Telling weight `k` from weight `k - 1`** [Ambainis2002], §5.3: if a `T`-query algorithm with
a unit initial state accepts every input of weight `k`, by an outcome in `S`, with probability at
least `1 - ε` and every input of weight `k - 1` with probability at most `ε ≤ 1/2`, then
`(1 - 2√(ε(1-ε))) √(k (N + 1 - k)) ≤ 2T`. The algorithm is constrained on no other input. -/
theorem one_sub_mul_sqrt_le_two_mul_of_weight (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {k : ℕ} {ε : ℝ}
    (h₁ : ∀ x : BitString N, weight x = k → 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y : BitString N, weight y + 1 = k → measureProb (run U ψ₀ y T) S ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(k * (N + 1 - k)) ≤ 2 * T := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp
  rcases le_or_gt k N with hkN | hkN
  swap
  · have : (k : ℝ) * (N + 1 - k) ≤ 0 := by
      have : (N : ℝ) + 1 ≤ k := by exact_mod_cast hkN
      nlinarith
    rw [Real.sqrt_eq_zero'.2 this, mul_zero]
    positivity
  set A := weightLayer N k
  set B := weightLayer N (k - 1)
  have hA : A.Nonempty := weightLayer_nonempty hkN
  have hm : ∀ x ∈ A, k ≤ #{i | update x i (!x i) ∈ B} := by
    intro x hx
    have hx' := mem_weightLayer.1 hx
    refine le_of_eq ?_
    rw [← hx']
    refine congrArg card (filter_congr fun i _ => ?_)
    rw [mem_weightLayer]
    cases hi : x i
    · rw [Bool.not_false, weight_update_true hi]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by exfalso; omega⟩
    · rw [Bool.not_true]
      have := weight_update_false hi
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  have hm' : ∀ y ∈ B, N - (k - 1) ≤ #{i | update y i (!y i) ∈ A} := by
    intro y hy
    have hy' := mem_weightLayer.1 hy
    have hc := card_filter_eq_false_eq_card_sub_weight y
    rw [Fintype.card_fin, hy'] at hc
    rw [← hc]
    refine le_of_eq (congrArg card (filter_congr fun i _ => ?_))
    rw [mem_weightLayer]
    cases hi : y i
    · rw [Bool.not_false, weight_update_true hi]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
    · rw [Bool.not_true]
      have := weight_update_false hi
      exact ⟨fun h => absurd h.symm Bool.false_ne_true, fun h => by exfalso; omega⟩
  have h₁' : ∀ x ∈ A, 1 - ε ≤ measureProb (run U ψ₀ x T) S :=
    fun x hx => h₁ x (mem_weightLayer.1 hx)
  have h₂' : ∀ y ∈ B, measureProb (run U ψ₀ y T) S ≤ ε := fun y hy =>
    h₂ y (by have := mem_weightLayer.1 hy; omega)
  have := one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors U hψ₀ T S hA h₁' h₂' hε hm hm'
  have hcast : ((N - (k - 1) : ℕ) : ℝ) = N + 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hk0]
    ring
  rwa [hcast] at this

/-- **Threshold functions** [Ambainis2002], §5.3: if a `T`-query algorithm with a unit initial
state accepts every input `x`, by an outcome in `S`, with probability within `ε ≤ 1/2` of
`Th^N_k(x)`, then `(1 - 2√(ε(1-ε))) √(k (N + 1 - k)) ≤ 2T`. -/
theorem one_sub_mul_sqrt_le_two_mul_of_threshold (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {k : ℕ} {ε : ℝ}
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (threshold N k x)| ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(k * (N + 1 - k)) ≤ 2 * T := by
  refine one_sub_mul_sqrt_le_two_mul_of_weight U hψ₀ T S (fun x hx => ?_) (fun y hy => ?_) hε
  · have := (abs_le.1 (h x)).1
    rw [threshold_apply, decide_eq_true hx.ge, bitVal_true] at this
    linarith
  · have := (abs_le.1 (h y)).2
    rw [threshold_apply, decide_eq_false (by omega), bitVal_false] at this
    linarith

/-- **Bounded-error majority takes `Ω(N)` queries** [Ambainis2002], §5.3: if a `T`-query
algorithm with a unit initial state accepts every input `x`, by an outcome in `S`, with
probability within `ε ≤ 1/2` of the majority of `x`, then `(1 - 2√(ε(1-ε))) N ≤ 4T`. -/
theorem one_sub_mul_card_le_four_mul_of_majority (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {ε : ℝ}
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (majority N x)| ≤ ε) (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * N ≤ 4 * T := by
  have hth := one_sub_mul_sqrt_le_two_mul_of_threshold U hψ₀ T S (k := (N + 1) / 2) h hε
  have hc := one_sub_two_mul_sqrt_nonneg ε
  -- `N / 2 ≤ √(k (N + 1 - k))` for `k = ⌈N / 2⌉`
  have hsq : (N : ℝ) / 2 ≤ √(((N + 1) / 2 : ℕ) * (N + 1 - ((N + 1) / 2 : ℕ))) := by
    refine Real.le_sqrt_of_sq_le ?_
    rcases Nat.even_or_odd N with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hk : (N + 1) / 2 = a := by omega
      rw [hk, ha]
      push_cast
      nlinarith
    · have hk : (N + 1) / 2 = a + 1 := by omega
      rw [hk, ha]
      push_cast
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hc]

/-- **Bounded-error majority takes `N / 72` queries**: if a `T`-query algorithm with a unit
initial state accepts every input `x`, by an outcome in `S`, with probability within `1/3` of the
majority of `x`, then `N ≤ 72 T`. -/
theorem card_le_seventy_two_mul_of_majority (U : ℕ → State N W →ₗᵢ[ℂ] State N W)
    {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W))
    (h : ∀ x, |measureProb (run U ψ₀ x T) S - bitVal ℝ (majority N x)| ≤ 1 / 3) :
    N ≤ 72 * T := by
  have := one_sub_mul_card_le_four_mul_of_majority U hψ₀ T S h (by norm_num)
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : (N : ℝ) ≤ 72 * T := by nlinarith
  exact_mod_cast this

end Cslib.Quantum
