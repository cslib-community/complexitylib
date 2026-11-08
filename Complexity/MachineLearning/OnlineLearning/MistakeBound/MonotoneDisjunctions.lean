/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MistakeBound.SOA
public import Complexity.MachineLearning.OnlineLearning.MistakeBound.VCDimension
public import Complexity.MachineLearning.OnlineLearning.MistakeBound.Winnow
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

/-!
# Optimal mistake bounds for monotone disjunctions

Littlestone's lower bound [Littlestone1988, §5, Theorem 8 and Lemma 6]: the class
`monotoneDisjunctions n k` of disjunctions of exactly `k` of `n` variables shatters a set of
`k ⌊log₂ (n / k)⌋` instances (`setShatters_monotoneDisjunctions`), so every deterministic learner
makes at least that many mistakes on some realizable sequence
(`le_optimalMistakeBound_monotoneDisjunctions`).

The construction splits `k 2^r ≤ n` of the variables into `k` groups indexed by the subsets of
`Fin r`. The instance `(j, t)` is `1` exactly on the variables of group `j` indexed by a subset
containing `t`. For a set `U` of instances, the disjunction that takes from each group `j` the
variable indexed by `{t | (j, t) ∈ U}` is `1` exactly on `U`.

Together with WINNOW1's upper bound (`mistakes_winnow_two_div_card_le`), for `1 ≤ k ≤ n` the
optimal mistake bound of `k`-literal monotone disjunctions lies between `k ⌊log₂ (n / k)⌋` and
`2 k log₂ (n / k) + 3 k` (`optimalMistakeBound_monotoneDisjunctions_le`). For `1 ≤ k` and
`2 k ≤ n` both are `Θ(k log (n / k))`, so WINNOW1 with `α = 2`, `θ = n / k` is optimal up to a
constant factor. The upper bound needs `1 ≤ k`: for `k = 0` the threshold `n / k` is `0`, and
WINNOW1 can err on the constant-false target although `2 k log₂ (n / k) + 3 k = 0`. For
`k > n` the class is empty and both bounds hold trivially. The source
also states a second lower bound in terms of `k (1 + log₂ (n / k))`; it is not formalized here.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.setShatters_monotoneDisjunctions`: a shattered
  set of size `k r` when `k 2^r ≤ n`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.le_vcDim_monotoneDisjunctions`: the VC
  dimension is at least `k ⌊log₂ (n / k)⌋`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.le_optimalMistakeBound_monotoneDisjunctions`:
  `k ⌊log₂ (n / k)⌋ ≤ opt(C_k)`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_monotoneDisjunctions_le`:
  `opt(C_k) ≤ 2 k log₂ (n / k) + 3 k` for `1 ≤ k`, attained by WINNOW1.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass SetShatters vcDim)

variable {n : ℕ}

/-- The shattered set of Littlestone's Lemma 6 for disjunctions [Littlestone1988, §5]: if
`k 2^r ≤ n`, the disjunctions of exactly `k` of `n` variables shatter a set of `k r` instances. -/
theorem setShatters_monotoneDisjunctions {k r : ℕ} (hkr : k * 2 ^ r ≤ n) :
    ∃ W : Finset (Fin n → Bool), W.card = k * r ∧
      SetShatters (monotoneDisjunctions n k) (W : Set (Fin n → Bool)) := by
  classical
  -- the variables: one per group `j : Fin k` and subset `T : Finset (Fin r)`
  have hcard : Fintype.card (Fin k × Finset (Fin r)) ≤ Fintype.card (Fin n) := by
    simpa [Fintype.card_prod, Fintype.card_finset] using hkr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- the instances: `(j, t)` is `1` on the variables `(j, T)` with `t ∈ T`
  let pt : Fin k × Fin r → Fin n → Bool := fun a i =>
    decide (∃ T : Finset (Fin r), a.2 ∈ T ∧ e (a.1, T) = i)
  have hpt : ∀ a j T, pt a (e (j, T)) = decide (a.1 = j ∧ a.2 ∈ T) := by
    intro a j T
    simp only [pt, decide_eq_decide]
    constructor
    · rintro ⟨T', hT', he⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (e.injective he)
      dsimp only at h1 h2
      subst h2
      exact ⟨h1, hT'⟩
    · rintro ⟨rfl, hT⟩
      exact ⟨T, hT, rfl⟩
  have hinj : Function.Injective pt := by
    intro a b hab
    have h := congrFun hab (e (a.1, {a.2}))
    rw [hpt, hpt] at h
    have h' : b.1 = a.1 ∧ b.2 ∈ ({a.2} : Finset (Fin r)) :=
      of_decide_eq_true (h.symm.trans (decide_eq_true ⟨rfl, Finset.mem_singleton_self _⟩))
    exact Prod.ext h'.1.symm (Finset.mem_singleton.mp h'.2).symm
  refine ⟨Finset.univ.image pt, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  · intro W' hW'
    -- the disjunction takes from group `j` the variable indexed by `{t | (j, t) ∈ W'}`
    let T : Fin k → Finset (Fin r) := fun j => Finset.univ.filter fun t => pt (j, t) ∈ W'
    let R : Finset (Fin n) := Finset.univ.image fun j => e (j, T j)
    have hRinj : Function.Injective fun j => e (j, T j) := fun j j' h =>
      (Prod.ext_iff.mp (e.injective h)).1
    refine ⟨monotoneDisjunction R, mem_monotoneDisjunctions.mpr ⟨R, ?_, rfl⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ hRinj, Finset.card_univ, Fintype.card_fin]
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image,
        Finset.coe_univ, Set.image_univ, Set.mem_range]
      constructor
      · rintro ⟨hx, a, rfl⟩
        obtain ⟨i, hi, hia⟩ := monotoneDisjunction_eq_true.mp hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
        rw [hpt] at hia
        simp only [decide_eq_true_eq] at hia
        obtain ⟨rfl, hT⟩ := hia
        simpa [T] using hT
      · intro hx
        obtain ⟨a, rfl⟩ := hW' hx |> fun h => by
          simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] using h
        refine ⟨monotoneDisjunction_eq_true.mpr ⟨e (a.1, T a.1),
          Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, a, rfl⟩
        rw [hpt]
        simpa [T] using hx

/-- `k 2^{⌊log₂ (n / k)⌋} ≤ n` for `k ≤ n`. -/
private theorem mul_two_pow_log_div_le {n k : ℕ} (hkn : k ≤ n) :
    k * 2 ^ Nat.log 2 (n / k) ≤ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (Nat.mul_le_mul_left k (Nat.pow_log_le_self 2 (Nat.div_pos hkn hk).ne')).trans
      (Nat.mul_div_le n k)

/-- **Littlestone's lower bound** [Littlestone1988, §5, Theorem 8]: the Littlestone dimension of the
disjunctions of exactly `k` of `n` variables is at least `k ⌊log₂ (n / k)⌋`. -/
theorem le_littlestoneDim_monotoneDisjunctions (n k : ℕ) :
    ((k * Nat.log 2 (n / k) : ℕ) : ℕ∞) ≤ littlestoneDim (monotoneDisjunctions n k) := by
  by_cases hkn : k ≤ n
  · obtain ⟨W, hW, hsh⟩ := setShatters_monotoneDisjunctions (mul_two_pow_log_div_le hkn)
    rw [← hW]
    exact natCast_le_littlestoneDim_of_setShatters W hsh
  · simp [Nat.div_eq_of_lt (not_le.mp hkn)]

/-- The VC dimension form of Littlestone's Lemma 6 for disjunctions [Littlestone1988, §5]: the
disjunctions of exactly `k` of `n` variables have VC dimension at least `k ⌊log₂ (n / k)⌋`. -/
theorem le_vcDim_monotoneDisjunctions (n k : ℕ) :
    k * Nat.log 2 (n / k) ≤ vcDim (monotoneDisjunctions n k) := by
  by_cases hkn : k ≤ n
  · obtain ⟨W, hW, hsh⟩ := setShatters_monotoneDisjunctions (mul_two_pow_log_div_le hkn)
    refine le_csSup ⟨Fintype.card (Fin n → Bool), ?_⟩ ⟨W, hW, hsh⟩
    rintro m ⟨V, rfl, -⟩
    exact Finset.card_le_univ V
  · simp [Nat.div_eq_of_lt (not_le.mp hkn)]

/-- **Littlestone's lower bound** [Littlestone1988, §5, Theorem 8]: every deterministic learner
makes at least `k ⌊log₂ (n / k)⌋` mistakes on some sequence labelled by a disjunction of exactly `k`
of `n` variables. -/
theorem le_optimalMistakeBound_monotoneDisjunctions (n k : ℕ) :
    ((k * Nat.log 2 (n / k) : ℕ) : ℕ∞) ≤ optimalMistakeBound (monotoneDisjunctions n k) := by
  rw [optimalMistakeBound_eq_littlestoneDim]
  exact le_littlestoneDim_monotoneDisjunctions n k

/-- The matching upper bound: WINNOW1 with `α = 2` and `θ = n / k` makes at most
`2 k log₂ (n / k) + 3 k` mistakes on the disjunctions of exactly `1 ≤ k` variables. With the lower
bound `le_optimalMistakeBound_monotoneDisjunctions`, the optimal mistake bound is
`Θ(k log (n / k))` for `1 ≤ k` and `2 k ≤ n`. For `k > n` the class is empty. -/
theorem optimalMistakeBound_monotoneDisjunctions_le {k : ℕ} (hk : 1 ≤ k) (tie : Bool) :
    optimalMistakeBound (monotoneDisjunctions n k) ≤
      mistakeBound (winnow 2 (n / k) tie) (monotoneDisjunctions n k) ∧
    mistakeBound (winnow 2 (n / k) tie) (monotoneDisjunctions n k) ≤
      (⌊2 * k * Real.logb 2 (n / k) + 3 * k⌋₊ : ℕ) := by
  refine ⟨optimalMistakeBound_le _ _, mistakeBound_le_iff.mpr fun S hS => ?_⟩
  obtain ⟨c, hc, hcS⟩ := realizable_iff.mp hS
  obtain ⟨R, rfl, rfl⟩ := mem_monotoneDisjunctions.mp hc
  exact_mod_cast Nat.le_floor (mistakes_winnow_two_div_card_le tie R hk S hcS)

end Cslib.MachineLearning.OnlineLearning.MistakeBound
