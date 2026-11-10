/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic

/-!
# Measuring tensor powers of an isometry on entangled states

A matrix `A : κ → β → ℂ` acts on amplitude vectors `φ : β → ℂ` by
`(A φ) a = ∑ b, A a b * φ b`. Its `k`-th tensor power acts on amplitude vectors
`Φ : (Fin k → β) → ℂ` by `(A^{⊗k} Φ) u = ∑ w, Φ w * ∏ j, A (u j) (w j)`
(`Cslib.Quantum.tensorPowerApply`). In a quantum circuit, `A` is the map from a witness state to
the final state of a verifier, and `A^{⊗k}` runs `k` copies of the verifier in parallel on the `k`
blocks of a witness `Φ` that need not be a product state.

Suppose `A` is an isometry and the outcomes in `T ⊆ κ` have probability at most `s` on every input
state. Then for every state `Φ` on `k` blocks, and conditioned on any event about the outcomes of
the other copies, copy `j` has outcome in `T` with probability at most `s`
(`Cslib.Quantum.sum_filter_mul_norm_tensorPowerApply_le`). This is the step of Kitaev's parallel
error reduction for `QMA` that handles entangled witnesses, in the proof of
[Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2, Lemma 14.1; see also
[Marriott, Watrous][MarriottWatrous2005], the discussion after Theorem 3.2. Iterating it gives an
exponential-moment bound (`Cslib.Quantum.sum_pow_card_filter_mul_norm_tensorPowerApply_le`), and
for `s ≤ 1 / 3` at least half of `2 r` copies have outcome in `T` with probability at most
`(8 / 9) ^ r` (`Cslib.Quantum.sum_card_filter_ge_norm_tensorPowerApply_le`).

## Main definitions

* `Cslib.Quantum.tensorPowerApply`: the amplitudes of `A^{⊗k} Φ`.

## Main results

* `Cslib.Quantum.sum_norm_tensorPowerApply`: tensor powers of an isometry are isometries.
* `Cslib.Quantum.sum_filter_mul_norm_tensorPowerApply_le`: one copy, conditioned on the others.
* `Cslib.Quantum.sum_card_filter_ge_norm_tensorPowerApply_le`: the tail bound `(8 / 9) ^ r`.

## References

* [A. Kitaev, A. Shen, M. Vyalyi, *Classical and Quantum Computation*][KitaevShenVyalyi2002]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {β κ : Type*} [Fintype β]

/-- The amplitudes `(A^{⊗k} Φ) u = ∑ w, Φ w * ∏ j, A (u j) (w j)` of the `k`-th tensor power of
the matrix `A` applied to `Φ`. -/
noncomputable def tensorPowerApply {k : ℕ} (A : κ → β → ℂ) (Φ : (Fin k → β) → ℂ)
    (u : Fin k → κ) : ℂ :=
  ∑ w, Φ w * ∏ j, A (u j) (w j)

/-- Splitting off coordinate `j`: `A^{⊗(n+1)}` is `A` on coordinate `j` after `A^{⊗n}` on the
others. -/
theorem tensorPowerApply_insertNth {n : ℕ} (A : κ → β → ℂ) (Φ : (Fin (n + 1) → β) → ℂ)
    (j : Fin (n + 1)) (a : κ) (v : Fin n → κ) :
    tensorPowerApply A Φ (j.insertNth a v) =
      ∑ b, A a b * ∑ w, Φ (j.insertNth b w) * ∏ i, A (v i) (w i) := by
  unfold tensorPowerApply
  rw [← (Fin.insertNthEquiv (fun _ => β) j).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succAbove _ j,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

variable [Fintype κ] (A : κ → β → ℂ)

/-- **Tensor powers of an isometry are isometries.** -/
theorem sum_norm_tensorPowerApply
    (hiso : ∀ φ : β → ℂ, ∑ a, ‖∑ b, A a b * φ b‖ ^ 2 = ∑ b, ‖φ b‖ ^ 2) :
    ∀ {k : ℕ} (Φ : (Fin k → β) → ℂ),
      ∑ u, ‖tensorPowerApply A Φ u‖ ^ 2 = ∑ w, ‖Φ w‖ ^ 2
  | 0, Φ => by
    simp [tensorPowerApply]
  | n + 1, Φ => by
    rw [← (Fin.insertNthEquiv (fun _ => κ) 0).sum_comp, Fintype.sum_prod_type_right,
      ← (Fin.insertNthEquiv (fun _ => β) 0).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, tensorPowerApply_insertNth]
    simp only [hiso]
    rw [sum_comm]
    exact sum_congr rfl fun b _ =>
      sum_norm_tensorPowerApply hiso fun w => Φ ((0 : Fin (n + 1)).insertNth b w)

variable [DecidableEq κ] (T : Finset κ) (s : ℝ)

/-- **One copy, conditioned on the others**, the step for entangled witnesses in the proof of
[Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Lemma 14.1: if `A` is an isometry whose outcomes in
`T` have probability at most `s` on every input, then on every input `Φ` of `A^{⊗k}`, and weighting
the outcomes by any nonnegative `g` that does not depend on coordinate `j`, the outcomes with
coordinate `j` in `T` carry at most `s` of the weight. -/
theorem sum_filter_mul_norm_tensorPowerApply_le
    (hA : ∀ φ : β → ℂ, ∑ a ∈ T, ‖∑ b, A a b * φ b‖ ^ 2 ≤ s * ∑ b, ‖φ b‖ ^ 2)
    (hiso : ∀ φ : β → ℂ, ∑ a, ‖∑ b, A a b * φ b‖ ^ 2 = ∑ b, ‖φ b‖ ^ 2)
    {k : ℕ} (Φ : (Fin k → β) → ℂ) (j : Fin k) (g : (Fin k → κ) → ℝ) (hg : ∀ u, 0 ≤ g u)
    (hgj : ∀ u a, g (Function.update u j a) = g u) :
    ∑ u with u j ∈ T, g u * ‖tensorPowerApply A Φ u‖ ^ 2 ≤
      s * ∑ u, g u * ‖tensorPowerApply A Φ u‖ ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := j.pos; omega⟩
  set e := Fin.insertNthEquiv (fun _ => κ) j
  rw [sum_filter, ← e.sum_comp, ← e.sum_comp, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right, mul_sum]
  refine sum_le_sum fun v _ => ?_
  simp only [e, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨a₀⟩⟩
  · simp
  have hc (a : κ) : g (j.insertNth a v) = g (j.insertNth a₀ v) := by
    rw [← hgj (j.insertNth a₀ v) a, Fin.update_insertNth]
  simp only [hc, ← sum_filter, ← mul_sum]
  set φ : β → ℂ := fun b => ∑ w, Φ (j.insertNth b w) * ∏ i, A (v i) (w i)
  have hΩ (a : κ) : tensorPowerApply A Φ (j.insertNth a v) = ∑ b, A a b * φ b :=
    tensorPowerApply_insertNth A Φ j a v
  simp only [hΩ, hiso φ, filter_mem_eq_inter, univ_inter]
  have := hA φ
  have := hg (j.insertNth a₀ v)
  nlinarith

/-- **The exponential moment of the number of copies in `T`**: for `t ≥ 1`, the expectation of
`t ^ #{j | u j ∈ T}` is at most `(1 + (t - 1) s) ^ k` times the squared norm, as for `k`
independent trials with success probability at most `s`. -/
theorem sum_pow_card_filter_mul_norm_tensorPowerApply_le
    (hA : ∀ φ : β → ℂ, ∑ a ∈ T, ‖∑ b, A a b * φ b‖ ^ 2 ≤ s * ∑ b, ‖φ b‖ ^ 2)
    (hiso : ∀ φ : β → ℂ, ∑ a, ‖∑ b, A a b * φ b‖ ^ 2 = ∑ b, ‖φ b‖ ^ 2) (hs : 0 ≤ s)
    {k : ℕ} (Φ : (Fin k → β) → ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ∑ u, t ^ (univ.filter fun j => u j ∈ T).card * ‖tensorPowerApply A Φ u‖ ^ 2 ≤
      (1 + (t - 1) * s) ^ k * ∑ u, ‖tensorPowerApply A Φ u‖ ^ 2 := by
  set μ : (Fin k → κ) → ℝ := fun u => ‖tensorPowerApply A Φ u‖ ^ 2
  have key (S : Finset (Fin k)) :
      ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u ≤ (1 + (t - 1) * s) ^ S.card * ∑ u, μ u := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert J S hJ ih =>
      have hsplit (u : Fin k → κ) : t ^ ((insert J S).filter fun j => u j ∈ T).card * μ u =
          t ^ (S.filter fun j => u j ∈ T).card * μ u +
            (if u J ∈ T then (t - 1) * (t ^ (S.filter fun j => u j ∈ T).card * μ u) else 0) := by
        rw [filter_insert]
        split_ifs with h
        · rw [card_insert_of_notMem (fun h' => hJ (mem_filter.mp h').1), pow_succ]
          ring
        · ring
      simp only [hsplit, sum_add_distrib, ← sum_filter, ← mul_sum]
      have hA' := sum_filter_mul_norm_tensorPowerApply_le A T s hA hiso Φ J
        (fun u => t ^ (S.filter fun j => u j ∈ T).card) (fun u => by positivity)
        (fun u a => by
          congr 2
          refine filter_congr fun j hj => ?_
          rw [Function.update_of_ne (show j ≠ J from fun h => hJ (h ▸ hj))])
      rw [card_insert_of_notMem hJ, pow_succ]
      have h1 : 0 ≤ t - 1 := by linarith
      have h2 : 0 ≤ ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u :=
        sum_nonneg fun u _ => by positivity
      have h3 : 0 ≤ 1 + (t - 1) * s := by nlinarith
      calc ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u +
            (t - 1) * ∑ u with u J ∈ T, t ^ (S.filter fun j => u j ∈ T).card * μ u
          ≤ ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u +
            (t - 1) * (s * ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u) := by
            gcongr
        _ = (1 + (t - 1) * s) * ∑ u, t ^ (S.filter fun j => u j ∈ T).card * μ u := by ring
        _ ≤ (1 + (t - 1) * s) * ((1 + (t - 1) * s) ^ S.card * ∑ u, μ u) := by gcongr
        _ = _ := by ring
  simpa using key univ

/-- **At least half of `2 r` copies in `T`** has probability at most `(8 / 9) ^ r` times the
squared norm, when each copy is in `T` with probability at most `1 / 3`. -/
theorem sum_card_filter_ge_norm_tensorPowerApply_le
    (hA : ∀ φ : β → ℂ, ∑ a ∈ T, ‖∑ b, A a b * φ b‖ ^ 2 ≤ s * ∑ b, ‖φ b‖ ^ 2)
    (hiso : ∀ φ : β → ℂ, ∑ a, ‖∑ b, A a b * φ b‖ ^ 2 = ∑ b, ‖φ b‖ ^ 2) (hs : 0 ≤ s)
    (hs₃ : s ≤ 1 / 3) {r : ℕ} (Φ : (Fin (2 * r) → β) → ℂ) :
    ∑ u with r ≤ (univ.filter fun j => u j ∈ T).card, ‖tensorPowerApply A Φ u‖ ^ 2 ≤
      (8 / 9) ^ r * ∑ u, ‖tensorPowerApply A Φ u‖ ^ 2 := by
  set μ : (Fin (2 * r) → κ) → ℝ := fun u => ‖tensorPowerApply A Φ u‖ ^ 2
  have hB := sum_pow_card_filter_mul_norm_tensorPowerApply_le A T s hA hiso hs Φ
    (t := 2) (by norm_num)
  have hμ : 0 ≤ ∑ u, μ u := sum_nonneg fun u _ => by positivity
  have hpow : (1 + (2 - 1) * s) ^ (2 * r) ≤ (16 / 9 : ℝ) ^ r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) r
  have hlow : (2 : ℝ) ^ r * ∑ u with r ≤ (univ.filter fun j => u j ∈ T).card, μ u ≤
      ∑ u, (2 : ℝ) ^ (univ.filter fun j => u j ∈ T).card * μ u := by
    rw [mul_sum]
    refine (sum_le_sum fun u hu => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ => by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (mem_filter.mp hu).2)
      (by positivity)
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  rw [← mul_le_mul_iff_of_pos_left h2r]
  calc (2 : ℝ) ^ r * ∑ u with r ≤ (univ.filter fun j => u j ∈ T).card, μ u
      ≤ (16 / 9 : ℝ) ^ r * ∑ u, μ u := hlow.trans (hB.trans (by gcongr))
    _ = 2 ^ r * ((8 / 9) ^ r * ∑ u, μ u) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num

end Cslib.Quantum
