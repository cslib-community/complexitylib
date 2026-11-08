/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.SaksZhou.Snap
import Complexity.Foundations.LinearAlgebra.Matrix.PowPerturbation
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The Saks–Zhou iteration

Saks and Zhou [SaksZhou1999] compute a high power `M ^ (n₁ ^ n₂)` of a substochastic matrix by
iterating an approximate `n₁`-th power `n₂` times. Each round reuses the same random seed `y` but
uses a fresh random shift `zᵢ`. In the presentation of [ChattopadhyayLiao2020, Appendix A.1], let
`pow A y` be an "offline randomized" approximation of `A ^ n₁` with seed `y ∈ Ω`, and let
`M̂₀ = M` and `M̂ᵢ = Snap_d(pow M̂ᵢ₋₁ y, zᵢ)` (`snapIter`). Lemma A.4 there states that `M̂_{n₂}` is
close to `M ^ (n₁ ^ n₂)` with high probability over `(y, z₁, …, z_{n₂})`. This file proves this
probability statement in exact density form, with explicit constants and for an arbitrary finite
seed space `Ω`. Here `pow` is an arbitrary function, so the space clause of Lemma A.4
(`M̂_{n₂}` is computable in space `O(r + n₂ (s + d))`) is not formalized; it belongs to the
space-bounded realization in [#474](https://github.com/cslib-community/complexitylib/issues/474).

Suppose that for `A = M` and for every dyadic substochastic `A` at precision `d`, at most an `ε`
fraction of the seeds `y` give `|pow A y - A ^ n₁| > ε` in some entry (`entryFarSet`). Then:

* (`dens_snapIter_ne_le`) the iteration agrees with the *reference iteration*
  `Mᵢ = Snap_d(Mᵢ₋₁ ^ n₁, zᵢ)`, which does not depend on `y`, except on a set of density at most
  `n₂ (ε + w ^ 2 (2 ^ d ε + 2 ^ (-d)))`, where `w` is the number of states;
* (`sum_abs_snapIter_sub_pow_le`) deterministically, every row of the reference iterate is within
  `(∑_{k < n₂} n₁ ^ k) w 2 ^ (1 - d)` of `M ^ (n₁ ^ n₂)` in absolute sum;
* (`dens_snapIter_far_le`, `dens_snapIter_far_le_of_two_le`) hence, outside a set of the same
  density (a `rowFarSet`), every row of `M̂_{n₂} - M ^ (n₁ ^ n₂)` has absolute sum at most
  `(∑_{k < n₂} n₁ ^ k) w 2 ^ (1 - d)`, and at most `n₁ ^ n₂ w 2 ^ (1 - d)` when `n₁ ≥ 2`.

With `n = n₁ ^ n₂`, this is the bound `‖M̂_{n₂} - M ^ n‖_∞ ≤ n w 2 ^ (1 - d)` of
[ChattopadhyayLiao2020, Lemma A.4], with failure probability
`n₂ (ε + w ^ 2 (2 ^ d ε + 2 ^ (-d)))` in place of `O(w ^ 2 n₂ (2 ^ d ε + 2 ^ (-d)))`. Three points
differ from that statement. Only the probability statement is formalized, not the space clause.
The hypothesis on `pow` is needed only for `M` and for dyadic substochastic matrices, which are
the only matrices the reference iteration visits; this is the setting of [Hoza2021, proof of
Theorem A.3], where the matrices have `a`-bit entries. The geometric sum `∑_{k < n₂} n₁ ^ k` is
the exact solution of the error recursion; it is at most `n₁ ^ n₂` only for `n₁ ≥ 2`. For
`n₁ = 1` the iteration can lose `2 ^ (-d)` in every round, so the form `n w 2 ^ (1 - d)` needs
`n₁ ≥ 2`. The tests give a `1 × 1` example.

The bad-seed and far sets are named (`entryFarSet`, `rowFarSet`) so that their decidability
instances are fixed once. Restating them with set-builder notation at a concrete `ι = Fin w`
would elaborate `∃ i` with `Nat.decidableExistsFin` instead of `Fintype.decidableExistsFintype`,
and the two sets would then match only up to `congr!`.

## Proof

The reference iterates are dyadic substochastic, so the hypothesis applies to them. Fix a round
`i` and the earlier shifts. If the actual and reference iterates agree before round `i`, they
disagree after it only if `pow Mᵢ₋₁ y` is `ε`-far from `Mᵢ₋₁ ^ n₁`, which has density at most `ε`
in `y`, or if the two are `ε`-close but snap differently under the fresh shift `zᵢ`, which has
density at most `w ^ 2 (2 ^ d ε + 2 ^ (-d))` in `zᵢ` by Lemma A.3 (`dens_snapMatrix_ne_le`). A
hybrid argument over the rounds sums these bounds. For the deterministic
error, snapping a nonnegative matrix changes each row by at most `w 2 ^ (1 - d)` in absolute sum,
which is the per-step bound of [ChattopadhyayLiao2020, proof of Lemma A.4], and the `n₁`-th power
is `n₁`-Lipschitz on the unit ball of the matrix `∞`-norm (`Matrix.sum_abs_pow_sub_pow_le`). So the
error `Eᵢ` satisfies `Eᵢ ≤ w 2 ^ (1 - d) + n₁ Eᵢ₋₁`. This recursion and its exact solution are
derived here; [ChattopadhyayLiao2020] states only the per-step bound and then cites Lemma 5.4 of
[SaksZhou1999] for the conclusion.

## Main definitions

* `Cslib.Probability.SaksZhou.snapIter`: the iteration `M̂ᵢ = Snap_d(pow M̂ᵢ₋₁, zᵢ)`.
* `Cslib.Probability.SaksZhou.entryFarSet`, `Cslib.Probability.SaksZhou.rowFarSet`: the points
  where a matrix-valued function is far from a fixed matrix, entrywise or in some row sum.

## Main results

* `Cslib.Probability.SaksZhou.isDyadicSubstochastic_snapIter`: the reference iterates are dyadic
  substochastic.
* `Cslib.Probability.SaksZhou.sum_abs_snapIter_sub_pow_le`: the deterministic error bound.
* `Cslib.Probability.SaksZhou.dens_snapIter_ne_le`: the coupling with the reference iteration.
* `Cslib.Probability.SaksZhou.dens_snapIter_far_le`,
  `Cslib.Probability.SaksZhou.dens_snapIter_far_le_of_two_le`: Lemma A.4.

## References

* [M. Saks and S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999]: the iteration. The
  publisher copy was not consulted, so its internal numbering, including Lemma 5.4, is unverified.
* [E. Chattopadhyay and J.-J. Liao, *Optimal Error Pseudodistributions for Read-Once Branching
  Programs*][ChattopadhyayLiao2020], arXiv v4, Appendix A.1, Lemma A.4 and its proof sketch.
* [W. M. Hoza, *Better Pseudodistributions and Derandomization for Space-Bounded
  Computation*][Hoza2021], Appendix A, proof of Theorem A.3: the use of the iteration on matrices
  with `a`-bit entries.
-/

public section

namespace Cslib.Probability.SaksZhou

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The points `y` at which `X y` is `ε`-far from `B` in some entry. For `X = pow A` and
`B = A ^ n₁` these are the bad seeds of the hypothesis of Lemma A.4. -/
noncomputable def entryFarSet {Ω κ ν : Type*} [Fintype Ω] [Fintype κ] [Fintype ν] (ε : ℝ)
    (X : Ω → Matrix κ ν ℝ) (B : Matrix κ ν ℝ) : Finset Ω :=
  {y | ∃ i j, ε < |X y i j - B i j|}

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_entryFarSet {Ω κ ν : Type*} [Fintype Ω] [Fintype κ] [Fintype ν] {ε : ℝ}
    {X : Ω → Matrix κ ν ℝ} {B : Matrix κ ν ℝ} {y : Ω} :
    y ∈ entryFarSet ε X B ↔ ∃ i j, ε < |X y i j - B i j| := by
  simp [entryFarSet]

/-- The points `p` at which some row of `X p - B` has absolute sum greater than `c`. -/
noncomputable def rowFarSet {Ω κ ν : Type*} [Fintype Ω] [Fintype κ] [Fintype ν] (c : ℝ)
    (X : Ω → Matrix κ ν ℝ) (B : Matrix κ ν ℝ) : Finset Ω :=
  {p | ∃ i, c < ∑ j, |X p i j - B i j|}

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_rowFarSet {Ω κ ν : Type*} [Fintype Ω] [Fintype κ] [Fintype ν] {c : ℝ}
    {X : Ω → Matrix κ ν ℝ} {B : Matrix κ ν ℝ} {p : Ω} :
    p ∈ rowFarSet c X B ↔ ∃ i, c < ∑ j, |X p i j - B i j| := by
  simp [rowFarSet]

/-- The Saks–Zhou iteration: `snapIter d pow M n z` is `M̂ₙ`, where `M̂₀ = M` and
`M̂ᵢ₊₁ = Snap_d(pow M̂ᵢ, zᵢ)` for the shifts `z = (z₀, …, z_{n-1})`. With `pow = (· ^ n₁)` it is the
reference iteration of [ChattopadhyayLiao2020, proof of Lemma A.4]. -/
noncomputable def snapIter (d : ℕ) (pow : Matrix ι ι ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    (n : ℕ) → (Fin n → Fin (2 ^ d)) → Matrix ι ι ℝ
  | 0, _ => M
  | n + 1, z => snapMatrix d (pow (snapIter d pow M n (Fin.init z))) (z (Fin.last n))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem snapIter_zero (d : ℕ) (pow : Matrix ι ι ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (z : Fin 0 → Fin (2 ^ d)) : snapIter d pow M 0 z = M := by
  rw [snapIter]

omit [Fintype ι] [DecidableEq ι] in
theorem snapIter_succ (d : ℕ) (pow : Matrix ι ι ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) (n : ℕ)
    (z : Fin (n + 1) → Fin (2 ^ d)) :
    snapIter d pow M (n + 1) z =
      snapMatrix d (pow (snapIter d pow M n (Fin.init z))) (z (Fin.last n)) := by
  rw [snapIter]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem snapIter_snoc (d : ℕ) (pow : Matrix ι ι ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (n : ℕ) (z : Fin n → Fin (2 ^ d)) (t : Fin (2 ^ d)) :
    snapIter d pow M (n + 1) (Fin.snoc z t) = snapMatrix d (pow (snapIter d pow M n z)) t := by
  rw [snapIter_succ, Fin.init_snoc, Fin.snoc_last]

/-- The reference iterates `Mᵢ = Snap_d(Mᵢ₋₁ ^ n₁, zᵢ)`, `i ≥ 1`, of a substochastic matrix are
dyadic substochastic. -/
theorem isDyadicSubstochastic_snapIter (d n₁ : ℕ) {M : Matrix ι ι ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) (n : ℕ)
    (z : Fin (n + 1) → Fin (2 ^ d)) :
    IsDyadicSubstochastic d (snapIter d (· ^ n₁) M (n + 1) z) := by
  induction n with
  | zero =>
    exact isDyadicSubstochastic_snapMatrix d (Matrix.pow_apply_nonneg h0 n₁)
      (Matrix.sum_pow_apply_le_one h0 h1 n₁) _
  | succ n ih =>
    have h := ih (Fin.init z)
    exact isDyadicSubstochastic_snapMatrix d (Matrix.pow_apply_nonneg h.nonneg n₁)
      (Matrix.sum_pow_apply_le_one h.nonneg h.sum_le_one n₁) _

private theorem snapIter_nonneg_sum (d n₁ : ℕ) {M : Matrix ι ι ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) :
    ∀ (n : ℕ) (z : Fin n → Fin (2 ^ d)),
      (∀ i j, 0 ≤ snapIter d (· ^ n₁) M n z i j) ∧
        ∀ i, ∑ j, snapIter d (· ^ n₁) M n z i j ≤ 1
  | 0, _ => ⟨h0, h1⟩
  | n + 1, z => ⟨(isDyadicSubstochastic_snapIter d n₁ h0 h1 n z).nonneg,
      (isDyadicSubstochastic_snapIter d n₁ h0 h1 n z).sum_le_one⟩

/-- **The deterministic error of the reference iteration**: every row of `Mₙ - M ^ (n₁ ^ n)` has
absolute sum at most `(∑_{k < n} n₁ ^ k) w 2 ^ (1 - d)`, where `w = |ι|`. This solves the
recursion `Eᵢ ≤ w 2 ^ (1 - d) + n₁ Eᵢ₋₁`, derived here from the per-step snapping bound of
[ChattopadhyayLiao2020, proof of Lemma A.4] and the power perturbation bound
`Matrix.sum_abs_pow_sub_pow_le`; [ChattopadhyayLiao2020] cites Lemma 5.4 of [SaksZhou1999] for
this step. -/
theorem sum_abs_snapIter_sub_pow_le (d n₁ : ℕ) {M : Matrix ι ι ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) (n : ℕ)
    (z : Fin n → Fin (2 ^ d)) (i : ι) :
    ∑ j, |snapIter d (· ^ n₁) M n z i j - (M ^ n₁ ^ n) i j| ≤
      (∑ k ∈ range n, (n₁ : ℝ) ^ k) * (Fintype.card ι * (2 / 2 ^ d)) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    set R := snapIter d (· ^ n₁) M n (Fin.init z)
    obtain ⟨hR0, hR1⟩ := snapIter_nonneg_sum d n₁ h0 h1 n (Fin.init z)
    have hR : ∀ i, ∑ j, |R i j| ≤ 1 := fun i =>
      (Finset.sum_congr rfl fun j _ => abs_of_nonneg (hR0 i j)).trans_le (hR1 i)
    have hM : ∀ i, ∑ j, |(M ^ n₁ ^ n) i j| ≤ 1 := fun i =>
      (Finset.sum_congr rfl fun j _ => abs_of_nonneg (Matrix.pow_apply_nonneg h0 _ i j)).trans_le
        (Matrix.sum_pow_apply_le_one h0 h1 _ i)
    have hstep : ∀ i, ∑ j, |snapIter d (· ^ n₁) M (n + 1) z i j - (R ^ n₁) i j| ≤
        Fintype.card ι * (2 / 2 ^ d) := fun i => by
      rw [snapIter_succ]
      calc ∑ j, |snapMatrix d (R ^ n₁) (z (Fin.last n)) i j - (R ^ n₁) i j|
          ≤ ∑ _j : ι, (2 / 2 ^ d : ℝ) := Finset.sum_le_sum fun j _ => by
            rw [snapMatrix_apply]
            exact abs_snap_sub_le d (Matrix.pow_apply_nonneg hR0 n₁ i j) _
        _ = Fintype.card ι * (2 / 2 ^ d) := by simp
    have hpow := Matrix.sum_abs_pow_sub_pow_le hR hM (fun i => ih (Fin.init z) i) n₁ i
    rw [← pow_mul, ← pow_succ] at hpow
    calc ∑ j, |snapIter d (· ^ n₁) M (n + 1) z i j - (M ^ n₁ ^ (n + 1)) i j|
        ≤ ∑ j, (|snapIter d (· ^ n₁) M (n + 1) z i j - (R ^ n₁) i j| +
            |(R ^ n₁) i j - (M ^ n₁ ^ (n + 1)) i j|) :=
          Finset.sum_le_sum fun j _ => abs_sub_le _ _ _
      _ ≤ Fintype.card ι * (2 / 2 ^ d) +
            n₁ * ((∑ k ∈ range n, (n₁ : ℝ) ^ k) * (Fintype.card ι * (2 / 2 ^ d))) := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (hstep i) hpow
      _ = (∑ k ∈ range (n + 1), (n₁ : ℝ) ^ k) * (Fintype.card ι * (2 / 2 ^ d)) := by
          rw [Finset.sum_range_succ', pow_zero]
          have : ∑ k ∈ range n, (n₁ : ℝ) ^ (k + 1) = n₁ * ∑ k ∈ range n, (n₁ : ℝ) ^ k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => pow_succ' _ _
          rw [this]
          ring

private theorem card_le_of_dens_le {α : Type*} [Fintype α] {s : Finset α} {ε : ℝ}
    (h : (s.dens : ℝ) ≤ ε) : (#s : ℝ) ≤ ε * Fintype.card α := by
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | h0
  · rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a _ =>
      (Fintype.card_eq_zero_iff.1 h0).elim a)]
    simp [h0]
  · rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
      div_le_iff₀ (by exact_mod_cast h0)] at h
    exact h

private theorem dens_le_of_card_le {α : Type*} [Fintype α] {s : Finset α} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (#s : ℝ) ≤ ε * Fintype.card α) : (s.dens : ℝ) ≤ ε := by
  rw [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | h0
  · simp [h0, hε]
  · rwa [div_le_iff₀ (by exact_mod_cast h0)]

/-- The hybrid argument for two iterations `X` and `R` driven by a shared seed `y` and fresh
shifts: if one step from any reference state differs for at most `β |Ω| |T|` pairs `(y, t)`, then
after `n` steps the iterations differ for at most `n β |Ω| |T| ^ n` pairs `(y, z)`. -/
private theorem card_ne_le_of_step {Ω T S : Type*} [Fintype Ω] [Fintype T] [DecidableEq S]
    (X R : (n : ℕ) → Ω → (Fin n → T) → S) (F : Ω → S → T → S) (G : S → T → S)
    (hX : ∀ n y z t, X (n + 1) y (Fin.snoc z t) = F y (X n y z) t)
    (hR : ∀ n y z t, R (n + 1) y (Fin.snoc z t) = G (R n y z) t)
    (h0 : ∀ y z, X 0 y z = R 0 y z) {β : ℝ}
    (hstep : ∀ n z, (#{p : Ω × T | F p.1 (R n p.1 z) p.2 ≠ G (R n p.1 z) p.2} : ℝ) ≤
      β * (Fintype.card Ω * Fintype.card T)) (n : ℕ) :
    (#{p : Ω × (Fin n → T) | X n p.1 p.2 ≠ R n p.1 p.2} : ℝ) ≤
      n * β * (Fintype.card Ω * Fintype.card T ^ n) := by
  induction n with
  | zero =>
    rw [Finset.filter_false_of_mem fun p _ => not_not.2 (h0 p.1 p.2)]
    simp
  | succ n ih =>
    let e : (Ω × (Fin n → T)) × T ≃ Ω × (Fin (n + 1) → T) :=
      { toFun := fun q => (q.1.1, Fin.snoc q.1.2 q.2)
        invFun := fun p => ((p.1, Fin.init p.2), p.2 (Fin.last n))
        left_inv := fun q => by simp
        right_inv := fun p => by simp }
    have hcard : #{p : Ω × (Fin (n + 1) → T) | X (n + 1) p.1 p.2 ≠ R (n + 1) p.1 p.2} =
        #{q : (Ω × (Fin n → T)) × T |
          F q.1.1 (X n q.1.1 q.1.2) q.2 ≠ G (R n q.1.1 q.1.2) q.2} := by
      refine (Finset.card_equiv e fun q => ?_).symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.coe_fn_mk, hX, hR]
    have hpt : ∀ (q : Ω × (Fin n → T)) (t : T),
        (if F q.1 (X n q.1 q.2) t ≠ G (R n q.1 q.2) t then (1 : ℝ) else 0) ≤
          (if X n q.1 q.2 ≠ R n q.1 q.2 then 1 else 0) +
            if F q.1 (R n q.1 q.2) t ≠ G (R n q.1 q.2) t then 1 else 0 := by
      intro q t
      by_cases hq : X n q.1 q.2 = R n q.1 q.2
      · rw [hq]
        simp
      · rw [ite_eq_left hq]
        split_ifs <;> norm_num
    rw [hcard, Finset.natCast_card_filter, Fintype.sum_prod_type]
    calc ∑ q : Ω × (Fin n → T), ∑ t : T,
          (if F q.1 (X n q.1 q.2) t ≠ G (R n q.1 q.2) t then (1 : ℝ) else 0)
        ≤ ∑ q : Ω × (Fin n → T), ∑ t : T, ((if X n q.1 q.2 ≠ R n q.1 q.2 then (1 : ℝ) else 0) +
            if F q.1 (R n q.1 q.2) t ≠ G (R n q.1 q.2) t then 1 else 0) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun t _ => hpt q t
      _ = Fintype.card T * #{p : Ω × (Fin n → T) | X n p.1 p.2 ≠ R n p.1 p.2} +
            ∑ z : Fin n → T,
              (#{p : Ω × T | F p.1 (R n p.1 z) p.2 ≠ G (R n p.1 z) p.2} : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          congr 1
          · rw [Finset.natCast_card_filter, Finset.mul_sum]
          · simp only [Finset.natCast_card_filter, Fintype.sum_prod_type]
            exact Finset.sum_comm
      _ ≤ Fintype.card T * (n * β * (Fintype.card Ω * Fintype.card T ^ n)) +
            ∑ _z : Fin n → T, β * (Fintype.card Ω * Fintype.card T) :=
          add_le_add (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _))
            (Finset.sum_le_sum fun z _ => hstep n z)
      _ = (n + 1 : ℕ) * β * (Fintype.card Ω * Fintype.card T ^ (n + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring

/-- One round against a fixed reference matrix `R`: the pairs `(y, z)` for which
`Snap_d(pow R y, z) ≠ Snap_d(R ^ n₁, z)` have density at most `ε + w ^ 2 (2 ^ d ε + 2 ^ (-d))`. -/
private theorem card_snap_pow_ne_le {Ω : Type*} [Fintype Ω] (d n₁ : ℕ)
    (pow : Matrix ι ι ℝ → Ω → Matrix ι ι ℝ) (R : Matrix ι ι ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hR : (#(entryFarSet ε (pow R) (R ^ n₁)) : ℝ) ≤ ε * Fintype.card Ω) :
    (#{p : Ω × Fin (2 ^ d) |
        snapMatrix d (pow R p.1) p.2 ≠ snapMatrix d (R ^ n₁) p.2} : ℝ) ≤
      (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) *
        (Fintype.card Ω * Fintype.card (Fin (2 ^ d))) := by
  have hq : (0 : ℝ) < 2 ^ d := by positivity
  rw [entryFarSet] at hR
  set c : ℝ := Fintype.card ι * Fintype.card ι * (4 ^ d * ε + 1) with hc
  have hy : ∀ y : Ω,
      (#{t : Fin (2 ^ d) | snapMatrix d (pow R y) t ≠ snapMatrix d (R ^ n₁) t} : ℝ) ≤
        (if ∃ i j, ε < |pow R y i j - (R ^ n₁) i j| then (2 ^ d : ℝ) else 0) + c := by
    intro y
    by_cases hb : ∃ i j, ε < |pow R y i j - (R ^ n₁) i j|
    · rw [ite_eq_left hb]
      have h1 : (#{t : Fin (2 ^ d) | snapMatrix d (pow R y) t ≠ snapMatrix d (R ^ n₁) t} : ℝ) ≤
          2 ^ d := by
        have := Finset.card_le_univ
          ({t : Fin (2 ^ d) | snapMatrix d (pow R y) t ≠ snapMatrix d (R ^ n₁) t} :
            Finset (Fin (2 ^ d)))
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      have h2 : 0 ≤ c := by positivity
      linarith
    · rw [ite_eq_right hb, zero_add]
      refine card_snapMatrix_ne_le d fun i j => ?_
      by_contra h
      exact hb ⟨i, j, lt_of_not_ge h⟩
  rw [Finset.natCast_card_filter, Fintype.sum_prod_type]
  calc ∑ y : Ω, ∑ t : Fin (2 ^ d),
        (if snapMatrix d (pow R y) t ≠ snapMatrix d (R ^ n₁) t then (1 : ℝ) else 0)
      ≤ ∑ y : Ω, ((if ∃ i j, ε < |pow R y i j - (R ^ n₁) i j| then (2 ^ d : ℝ) else 0) + c) :=
        Finset.sum_le_sum fun y _ => by
          rw [← Finset.natCast_card_filter]
          exact hy y
    _ = 2 ^ d * #{y : Ω | ∃ i j, ε < |pow R y i j - (R ^ n₁) i j|} + Fintype.card Ω * c := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.natCast_card_filter, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
    _ ≤ 2 ^ d * (ε * Fintype.card Ω) + Fintype.card Ω * c := by gcongr
    _ = (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) *
          (Fintype.card Ω * Fintype.card (Fin (2 ^ d))) := by
        rw [Fintype.card_fin, hc]
        have h4 : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by
          rw [← mul_pow]
          norm_num
        push_cast
        rw [h4]
        field_simp

/-- **Coupling with the reference iteration** [ChattopadhyayLiao2020, proof of Lemma A.4]. Let
`M` be substochastic, and suppose that for `A = M` and for every dyadic substochastic `A` at
precision `d`, the seeds `y ∈ Ω` with `|pow A y - A ^ n₁| > ε` in some entry have density at
most `ε`. Then the iteration `M̂_{n₂} = snapIter d (pow · y) M n₂ z`, with one shared seed `y`
and independent uniform shifts `z`, differs from the reference iteration
`snapIter d (· ^ n₁) M n₂ z` on a set of density at most
`n₂ (ε + w ^ 2 (2 ^ d ε + 2 ^ (-d)))`, where `w = |ι|`. -/
theorem dens_snapIter_ne_le {Ω : Type*} [Fintype Ω] (d n₁ n₂ : ℕ)
    (pow : Matrix ι ι ℝ → Ω → Matrix ι ι ℝ) {M : Matrix ι ι ℝ} {ε : ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) (hε : 0 ≤ ε)
    (hpow : ∀ A, A = M ∨ IsDyadicSubstochastic d A →
      ((entryFarSet ε (pow A) (A ^ n₁)).dens : ℝ) ≤ ε) :
    (({p : Ω × (Fin n₂ → Fin (2 ^ d)) |
        snapIter d (fun A => pow A p.1) M n₂ p.2 ≠ snapIter d (· ^ n₁) M n₂ p.2} :
          Finset _).dens : ℝ) ≤
      n₂ * (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  have hβ : 0 ≤ ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹) := by positivity
  refine dens_le_of_card_le (by positivity) ?_
  have hmem : ∀ (n : ℕ) (z : Fin n → Fin (2 ^ d)),
      snapIter d (· ^ n₁) M n z = M ∨ IsDyadicSubstochastic d (snapIter d (· ^ n₁) M n z)
    | 0, _ => Or.inl rfl
    | n + 1, z => Or.inr (isDyadicSubstochastic_snapIter d n₁ h0 h1 n z)
  have h := card_ne_le_of_step (fun n y z => snapIter d (fun A => pow A y) M n z)
    (fun n _ z => snapIter d (· ^ n₁) M n z) (fun y A t => snapMatrix d (pow A y) t)
    (fun A t => snapMatrix d (A ^ n₁) t) (fun n y z t => snapIter_snoc ..)
    (fun n y z t => snapIter_snoc ..) (fun _ _ => rfl)
    (fun n z => card_snap_pow_ne_le d n₁ pow _ hε (card_le_of_dens_le (hpow _ (hmem n z))))
    n₂
  refine h.trans_eq ?_
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

/-- **The Saks–Zhou iteration** [ChattopadhyayLiao2020, Lemma A.4], with the exact error sum.
Under the hypotheses of `dens_snapIter_ne_le`, the pairs `(y, z)` for which some row of
`M̂_{n₂} - M ^ (n₁ ^ n₂)` has absolute sum greater than `(∑_{k < n₂} n₁ ^ k) w 2 ^ (1 - d)` have
density at most `n₂ (ε + w ^ 2 (2 ^ d ε + 2 ^ (-d)))`. Only the probability statement of
Lemma A.4 is formalized: `pow` is an arbitrary function, and the space clause is left to the
space-bounded realization ([#474](https://github.com/cslib-community/complexitylib/issues/474)).
-/
theorem dens_snapIter_far_le {Ω : Type*} [Fintype Ω] (d n₁ n₂ : ℕ)
    (pow : Matrix ι ι ℝ → Ω → Matrix ι ι ℝ) {M : Matrix ι ι ℝ} {ε : ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) (hε : 0 ≤ ε)
    (hpow : ∀ A, A = M ∨ IsDyadicSubstochastic d A →
      ((entryFarSet ε (pow A) (A ^ n₁)).dens : ℝ) ≤ ε) :
    ((rowFarSet ((∑ k ∈ range n₂, (n₁ : ℝ) ^ k) * (Fintype.card ι * (2 / 2 ^ d)))
        (fun p : Ω × (Fin n₂ → Fin (2 ^ d)) => snapIter d (fun A => pow A p.1) M n₂ p.2)
        (M ^ n₁ ^ n₂)).dens : ℝ) ≤
      n₂ * (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  refine le_trans ?_ (dens_snapIter_ne_le d n₁ n₂ pow h0 h1 hε hpow)
  refine NNRat.cast_le.2 (Finset.dens_le_dens fun p => ?_)
  simp only [mem_rowFarSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨i, hi⟩ heq
  rw [heq] at hi
  exact (sum_abs_snapIter_sub_pow_le d n₁ h0 h1 n₂ p.2 i).not_gt hi

/-- **The Saks–Zhou iteration** [ChattopadhyayLiao2020, Lemma A.4]: for `n₁ ≥ 2` and
`n = n₁ ^ n₂`, except on a set of density at most `n₂ (ε + w ^ 2 (2 ^ d ε + 2 ^ (-d)))`, every row
of `M̂_{n₂} - M ^ n` has absolute sum at most `n w 2 ^ (1 - d)`. As in `dens_snapIter_far_le`,
only the probability statement is formalized, not the space clause. The restriction `n₁ ≥ 2` is
needed: for `n₁ = 1` the error can reach `n₂ 2 ^ (-d)`, and the tests give an example. -/
theorem dens_snapIter_far_le_of_two_le {Ω : Type*} [Fintype Ω] (d : ℕ) {n₁ : ℕ} (n₂ : ℕ)
    (hn₁ : 2 ≤ n₁) (pow : Matrix ι ι ℝ → Ω → Matrix ι ι ℝ) {M : Matrix ι ι ℝ} {ε : ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1) (hε : 0 ≤ ε)
    (hpow : ∀ A, A = M ∨ IsDyadicSubstochastic d A →
      ((entryFarSet ε (pow A) (A ^ n₁)).dens : ℝ) ≤ ε) :
    ((rowFarSet ((n₁ : ℝ) ^ n₂ * (Fintype.card ι * (2 / 2 ^ d)))
        (fun p : Ω × (Fin n₂ → Fin (2 ^ d)) => snapIter d (fun A => pow A p.1) M n₂ p.2)
        (M ^ n₁ ^ n₂)).dens : ℝ) ≤
      n₂ * (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  refine le_trans ?_ (dens_snapIter_far_le d n₁ n₂ pow h0 h1 hε hpow)
  refine NNRat.cast_le.2 (Finset.dens_le_dens fun p => ?_)
  simp only [mem_rowFarSet]
  rintro ⟨i, hi⟩
  refine ⟨i, lt_of_le_of_lt ?_ hi⟩
  have hgeom : ∑ k ∈ range n₂, (n₁ : ℝ) ^ k ≤ (n₁ : ℝ) ^ n₂ := by
    exact_mod_cast (Nat.geomSum_lt hn₁ fun k hk => Finset.mem_range.1 hk).le
  gcongr

end Cslib.Probability.SaksZhou
