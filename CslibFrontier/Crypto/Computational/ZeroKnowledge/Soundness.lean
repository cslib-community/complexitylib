/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ZeroKnowledge
public import CslibFrontier.Crypto.Negligible.Basic

/-!
# Negligible soundness for zero-knowledge proof systems

`Cslib.Crypto.ZKProof enc A soundness` (`CslibFrontier.Crypto.Computational.ZeroKnowledge`) carries
a soundness bound `soundness : ℕ → ENNReal` indexed by the security parameter. The single-session
GMW systems have `soundness := fun _ => 1 / 3`, and sequential repetition
(`CslibFrontier.Crypto.Computational.ZeroKnowledge.Amplification`) amplifies this to
`fun n => (1 / 3) ^ (k n)`. This module states when such a bound is negligible.

* `ZKProof.NegligibleSoundness` asserts that `soundness n ≠ ⊤` for all `n` and
  `fun n => (soundness n).toNNReal` is `Negligible`. Requiring finiteness rules out the degenerate
  `soundness n = ⊤` case where `ENNReal.toNNReal ⊤ = 0`, and implies that against every family of
  cheating provers on false instances, the real-valued acceptance probability is negligible
  (`ZKProof.NegligibleSoundness.acceptProb_toNNReal_negligible`) and that `A ∈ IP enc`
  (`ZKProof.NegligibleSoundness.mem_IP`).
* `Cslib.Crypto.negligible_pow_of_lt_one` and `Cslib.Crypto.negligible_one_third_pow` establish
  that `(1 / 3) ^ (k n)` is negligible whenever `∀ n, n ≤ k n`.

## Main definitions

* `Cslib.Crypto.ZKProof.NegligibleSoundness`: finiteness and negligible decay of `soundness`.

## Main results

* `Cslib.Crypto.ZKProof.NegligibleSoundness.acceptProb_toNNReal_negligible`: negligible acceptance
  probability on false-instance and cheating-prover families.
* `Cslib.Crypto.ZKProof.NegligibleSoundness.mem_IP`: any `ZKProof` with negligible soundness places
  `A ∈ IP enc`.
* `Cslib.Crypto.negligible_pow_of_lt_one`, `Cslib.Crypto.negligible_one_third_pow`,
  `Cslib.Crypto.ZKProof.negligibleSoundness_one_third_pow`: geometric soundness decay under
  repetition count `n ≤ k n`.
* `Cslib.Crypto.one_third_pow_succ_le`: `(1 / 3) ^ (n + 1) ≤ 1 / 3`, for weakening an amplified
  system to the single-session bound with `ZKProof.mono`.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal
open Cslib.Probability Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

namespace ZKProof

variable {soundness soundness' : ℕ → ENNReal}

/-- **Negligible soundness** for a `ZKProof`: the soundness bound is finite at every security
parameter (`∀ n, soundness n ≠ ⊤`, ruling out the degenerate `ENNReal.toNNReal ⊤ = 0` case) and
its nonnegative real value `fun n => (soundness n).toNNReal` is `Negligible`. -/
def NegligibleSoundness (_zk : ZKProof enc A soundness) : Prop :=
  (∀ n, soundness n ≠ ⊤) ∧ Negligible (fun n => (soundness n).toNNReal)

theorem NegligibleSoundness.soundness_ne_top {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) (n : ℕ) : soundness n ≠ ⊤ :=
  h.1 n

theorem NegligibleSoundness.negligible_toNNReal {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) : Negligible (fun n => (soundness n).toNNReal) :=
  h.2

/-- Under `NegligibleSoundness`, any family of false instances `a : ℕ → α` (`∀ n, a n ∉ A`) and
any family of computationally unbounded stateful provers `P : ℕ → Prover Unit` have negligible
acceptance probability. -/
theorem NegligibleSoundness.acceptProb_toNNReal_negligible {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) {a : ℕ → α} (ha : ∀ n, a n ∉ A) (P : ℕ → Prover Unit) :
    Negligible (fun n => (acceptProb (zk.verifier n (a n)) (P n)).toNNReal) :=
  negligible_of_le h.2 fun n =>
    ENNReal.toNNReal_mono (h.1 n) (zk.sound n (a n) (ha n) (P n))

/-- A pointwise smaller soundness bound preserves `NegligibleSoundness`. -/
theorem NegligibleSoundness.of_le {zk : ZKProof enc A soundness}
    {zk' : ZKProof enc A soundness'} (h : zk.NegligibleSoundness)
    (hle : ∀ n, soundness' n ≤ soundness n) : zk'.NegligibleSoundness :=
  ⟨fun n => ne_top_of_le_ne_top (h.1 n) (hle n),
    negligible_of_le h.2 fun n => ENNReal.toNNReal_mono (h.1 n) (hle n)⟩

/-- Any `ZKProof` with negligible soundness places `A ∈ IP enc`. -/
theorem NegligibleSoundness.mem_IP {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) : A ∈ IP enc := by
  have hev := h.2.eventually_le_inv_polynomial
    (p := fun _ => 3) (PolynomiallyBounded.const 3) (fun _ => by decide)
  obtain ⟨n, hn⟩ := hev.exists
  refine zk.mem_IP ⟨n, ?_⟩
  rw [← ENNReal.coe_toNNReal (h.1 n)]
  have hle : ((soundness n).toNNReal : ℝ≥0) ≤ (1 / 3 : ℝ≥0) := by
    exact_mod_cast hn
  exact (ENNReal.coe_le_coe.mpr hle).trans (by norm_num)

end ZKProof

/-- Geometric decay `fun n => ratio ^ k n` is negligible for any ratio `ratio < 1` and repetition
count `k : ℕ → ℕ` satisfying `∀ n, n ≤ k n`. -/
theorem negligible_pow_of_lt_one {ratio : ℝ≥0} (hratio : ratio < 1) {k : ℕ → ℕ}
    (hk : ∀ n, n ≤ k n) :
    Negligible (fun n => ratio ^ k n) :=
  negligible_of_le (negligible_geometric hratio) fun n =>
    pow_le_pow_of_le_one ratio.coe_nonneg hratio.le (hk n)

/-- The amplified soundness bound `fun n => ((1 / 3 : ENNReal) ^ k n).toNNReal` is negligible
whenever `∀ n, n ≤ k n`. -/
theorem negligible_one_third_pow {k : ℕ → ℕ} (hk : ∀ n, n ≤ k n) :
    Negligible (fun n => ((1 / 3 : ENNReal) ^ k n).toNNReal) := by
  have hlt : ((1 / 3 : ENNReal).toNNReal) < 1 := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
    norm_num
  simpa only [ENNReal.toNNReal_pow] using negligible_pow_of_lt_one hlt hk

/-- Any positive number of repetitions is at least as sound as one round:
`(1 / 3) ^ (n + 1) ≤ 1 / 3`. With `ZKProof.mono`, this turns a sequentially amplified system into
one with the single-session bound `fun _ => 1 / 3`. -/
theorem one_third_pow_succ_le (n : ℕ) : (1 / 3 : ENNReal) ^ (n + 1) ≤ 1 / 3 :=
  pow_le_of_le_one zero_le (by norm_num) n.succ_ne_zero

/-- A `ZKProof` with soundness `(1 / 3) ^ (k n)` for `∀ n, n ≤ k n` has negligible soundness. -/
theorem ZKProof.negligibleSoundness_one_third_pow {k : ℕ → ℕ}
    (zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ k n)) (hk : ∀ n, n ≤ k n) :
    zk.NegligibleSoundness :=
  ⟨fun n => ENNReal.pow_ne_top (by norm_num), negligible_one_third_pow hk⟩

end Cslib.Crypto
