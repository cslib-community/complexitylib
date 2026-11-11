/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.ParallelRepetition.Embedding
public import Complexity.Computability.PCP.ParallelRepetition.Factorization
public import Complexity.Computability.PCP.ParallelRepetition.Recursion
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Complexity.Probability.PMF.Event

/-!
# The parallel repetition theorem

Holenstein's **parallel repetition theorem** [Holenstein, Theorem 2.5][Holenstein2009]: for every
two-prover one-round game `G` with value `v` and answer sets with `|A| |B| ≥ 2`, the `n`-fold
parallel repetition has value

`v(Gⁿ) ≤ (1 - (1 - v)³ / 6000)^{n / log₂ (|A| |B|)}`

(`Cslib.PCP.TwoProverGame.value_pow_le`). The strategies of `Gⁿ` are arbitrary maps of question
tuples to answer tuples, as in `TwoProverGame.pow` and `TwoProverGame.value`. The form for games of
value at most `1 - ε`, `v(Gⁿ) ≤ (1 - ε³ / 6000)^{n / log₂ (|A| |B|)}`, is
`value_pow_le_of_value_le`.

The proof assembles the parts in `Complexity/Computability/PCP/ParallelRepetition/`. Fix
strategies `ha` and `hb` of `Gⁿ`, and write `W_C` for the event that they win every coordinate in
`C`.

* **Lemma 6.4** (`exists_isEmbeddable_filter_questions`). The questions of `G` embed in the
  repetition conditioned on `W_C` at every free coordinate `j ∉ C`, with errors `ε_j` that sum to
  at most `27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`. The first stage of the embedding
  is `exists_isEmbeddable_condLaw_shared`
  (`Complexity/Computability/PCP/ParallelRepetition/Embedding.lean`), and the second, composed
  with the first, is `isEmbeddable_filter_questions_of_shared`
  (`Complexity/Computability/PCP/ParallelRepetition/Factorization.lean`).
* **Lemma 6.5** (`exists_winProbOn_insert_le`). Some free coordinate `j` has at most the average
  error, and strategy extraction (`TwoProverGame.winProbOn_insert_le`) bounds the probability of
  winning it given `W_C`:
  `Pr[W_C ∧ W_j] ≤ Pr[W_C] (v + 27 / √2 · √((#C ln (|A| |B|) + ln (1 / Pr[W_C])) / (n - #C)))`.
* **Theorem 2.5** (`winProb_pow_le`, `value_pow_le`). Picking coordinates by Lemma 6.5 one at a
  time gives sets `∅ = C_0 ⊂ C_1 ⊂ ⋯ ⊂ C_n = univ` whose probabilities `p_m = Pr[W_{C_m}]` satisfy
  Holenstein's recursion (7.6). The sharpened Lemma 7.1, `ParallelRepetition.le_rpow_of_step`
  (`Complexity/Computability/PCP/ParallelRepetition/Recursion.lean`), turns it into the bound
  (7.7) on `p_n`, the winning probability of the strategies.

## Constants

Holenstein's recursion (7.6) has the constant `15` and logarithms in bits. Here the constant is
`27 / √2 ≈ 19.09` and the logarithm in the error term is natural:

* the library's Corollary 5.3 (`isEmbeddable_diag_of_dist_le`) has the error `7 ε₁ + 2 ε₂` where
  Holenstein's has `3 ε₁ + 2 ε₂`, which turns `15 = 3 (3 + 2)` into `27 = 3 (7 + 2)`;
* the library's Lemma 4.1 bounds the sum of squared distances by `ln (1 / Pr[W]) / 2` in nats,
  with the factor `1 / 2` of Pinsker's inequality, where Holenstein's (4.1) has
  `log₂ (1 / Pr[W])`.

Since `ln x ≤ log₂ x` for `x ≥ 1`, the recursion holds with `L = log₂ (|A| |B|)`, and
`le_rpow_of_step` accepts every constant up to `21`. The final bound is exactly Holenstein's,
with the constant `6000`; `le_rpow_of_step` accounts for the rounding that his (7.4) ignores.

## Source mapping

* In the proof of Lemma 6.5, Holenstein relabels the coordinates in the strategies so that the
  conditioned coordinates are the last `m`; here `C` is any set of coordinates, so no relabeling
  is needed.
* Lemma 6.5 is multiplied out by `Pr[W_C]`, so that it never divides by it, and it holds with any
  probability: if `Pr[W_C] = 0`, any free coordinate works.
* Holenstein's proof of Theorem 2.5 picks the coordinate minimizing `Pr[W_j | W_C]`; any
  coordinate given by Lemma 6.5 works, and the proof picks one by choice.
* Lemma 7.1 needs `ℓ = log (|A| |B|) ≥ 1`, which is the hypothesis `2 ≤ |A| |B|` of
  `value_pow_le`.

## Main results

* `Cslib.PCP.TwoProverGame.exists_isEmbeddable_filter_questions`: Holenstein's Lemma 6.4.
* `Cslib.PCP.TwoProverGame.exists_winProbOn_insert_le`: Holenstein's Lemma 6.5.
* `Cslib.PCP.TwoProverGame.winProb_pow_le`: every strategy of the repetition wins with probability
  at most the bound of Theorem 2.5.
* `Cslib.PCP.TwoProverGame.value_pow_le`: Holenstein's Theorem 2.5, the parallel repetition
  theorem.
* `Cslib.PCP.TwoProverGame.value_pow_le_of_value_le`: Theorem 2.5 for games of value at most
  `1 - ε`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

public section

namespace Cslib.PCP.TwoProverGame

open Finset
open Cslib.PCP.ParallelRepetition
open Cslib.Probability.CorrelatedSampling (IsEmbeddable)

variable {X Y A B : Type*} [Fintype A] [Fintype B]

/-! ### Lemmas 6.4 and 6.5 -/

section Embedding

variable [Fintype X] [Fintype Y] (G : TwoProverGame X Y A B) {n : ℕ}
  (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B) {C : Finset (Fin n)}

/-- **Holenstein's Lemma 6.4** [Holenstein, Lemma 6.4][Holenstein2009]. Condition the questions
`(x, y)` of the `n`-fold repetition on the event `W_C` that the strategies `ha` and `hb` win every
coordinate in `C`. At every free coordinate `j ∉ C`, the questions of `G` embed with error `ε_j` in
the conditioned law of `((x_j, y_j), (x, y))`, and the errors satisfy
`∑_{j ∉ C} ε_j ≤ 27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`.

Holenstein conditions on the last `n - k` coordinates and bounds the sum by
`15 √k √((n - k) log (|A| |B|) + log (1 / Pr[W]))` in bits, with `k = #Cᶜ`. The constant `27 / √2`
and the natural logarithm come from the library's Corollary 5.3 and Lemma 4.1; see the module
documentation. -/
theorem exists_isEmbeddable_filter_questions
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∃ ε : {i // i ∉ C} → ℝ,
      (∀ j, IsEmbeddable G.questions
        (((G.pow n).questions.filter (G.winsOn ha hb C) hC).map
          fun (x, y) => ((x j, y j), (x, y)))
        (ε j)) ∧
      ∑ j, ε j ≤ 27 / Real.sqrt 2 *
        Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
          Real.log (1 / G.winProbOn ha hb C))) := by
  obtain ⟨ε, hemb, hsum⟩ := exists_isEmbeddable_condLaw_shared hC
  exact ⟨ε, fun j => isEmbeddable_filter_questions_of_shared j hC (hemb j), hsum⟩

end Embedding

variable [Finite X] [Finite Y] (G : TwoProverGame X Y A B)

section Step

variable [Nonempty A] [Nonempty B] {n : ℕ} (ha : (Fin n → X) → Fin n → A)
  (hb : (Fin n → Y) → Fin n → B) {C : Finset (Fin n)}

/-- **Holenstein's Lemma 6.5** [Holenstein, Lemma 6.5, (6.20)][Holenstein2009], multiplied out so
that it never divides by `Pr[W_C]`. If the strategies `ha` and `hb` of the `n`-fold repetition
leave a coordinate outside `C`, then some free coordinate `j ∉ C` satisfies

`Pr[W_C ∧ W_j] ≤ Pr[W_C] (v(G) + 27 / √2 · √((#C ln (|A| |B|) + ln (1 / Pr[W_C])) / (n - #C)))`.

If `Pr[W_C] > 0`, a coordinate with at most the average error of Lemma 6.4
(`exists_isEmbeddable_filter_questions`) works, by strategy extraction (`winProbOn_insert_le`).
If `Pr[W_C] = 0`, both sides vanish. Holenstein's constant is `15`, with logarithms in bits; see the
module documentation. -/
theorem exists_winProbOn_insert_le (hCu : C ≠ univ) :
    ∃ j ∉ C, G.winProbOn ha hb (insert j C) ≤ G.winProbOn ha hb C *
      (G.value + 27 / Real.sqrt 2 * Real.sqrt ((#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / (n - #C))) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  have hne : Cᶜ.Nonempty := (Finset.compl_ne_univ_iff_nonempty Cᶜ).mp (by rwa [compl_compl])
  rcases (G.winProbOn_nonneg ha hb C).eq_or_lt with hp | hp
  · obtain ⟨j, hj⟩ := hne
    refine ⟨j, Finset.mem_compl.mp hj, ?_⟩
    rw [← hp, zero_mul]
    exact hp ▸ G.winProbOn_anti ha hb (Finset.subset_insert j C)
  -- With positive probability, `W_C` contains a possible question tuple.
  have hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support :=
    (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mp hp
  obtain ⟨ε, hemb, hsum⟩ := G.exists_isEmbeddable_filter_questions ha hb hC
  set Z := #C * Real.log (Fintype.card A * Fintype.card B) + Real.log (1 / G.winProbOn ha hb C)
  -- The number of free coordinates is `n - #C > 0`.
  have hcompl : (#Cᶜ : ℝ) = n - #C := by
    rw [Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_univ C)]
  have hk : (0 : ℝ) < #Cᶜ := by exact_mod_cast Finset.card_pos.mpr hne
  have hcard : Fintype.card {i // i ∉ C} = #Cᶜ := by
    simp only [← Finset.mem_compl, Fintype.card_coe]
  have hfree : (univ : Finset {i // i ∉ C}).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, hcard]
    exact_mod_cast hk
  -- Averaging: some free coordinate has at most the average error.
  have hsqrt : #Cᶜ * Real.sqrt (Z / #Cᶜ) = Real.sqrt (#Cᶜ * Z) := by
    rw [← Real.sqrt_sq hk.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk.le]
    congr 1
    field_simp
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hfree (f := ε)
    (g := fun _ => 27 / Real.sqrt 2 * Real.sqrt (Z / #Cᶜ)) (by
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      calc _ ≤ _ := hsum
        _ = _ := by rw [← hsqrt]; ring)
  refine ⟨j, j.2, ?_⟩
  rw [← hcompl]
  exact G.winProbOn_insert_le ha hb C j hC ((hemb j).mono hj)

end Step

/-! ### Theorem 2.5 -/

section Theorem

/-- `2 ≤ |A| |B|` makes both answer sets nonempty. -/
private theorem nonempty_of_two_le_card_mul (hAB : 2 ≤ Fintype.card A * Fintype.card B) :
    Nonempty A ∧ Nonempty B := by
  refine ⟨Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h => ?_),
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h => ?_)⟩ <;>
    simp [h] at hAB

/-- **The parallel repetition bound for one strategy** [Holenstein, proof of Theorem 2.5, (7.6) and
(7.7)][Holenstein2009]. Every pair of strategies `ha` and `hb` of the `n`-fold repetition wins with
probability at most `(1 - (1 - v(G))³ / 6000)^{n / log₂ (|A| |B|)}`.

Starting from `C_0 = ∅`, add a coordinate given by Lemma 6.5 (`exists_winProbOn_insert_le`) at
each step, until `C_n` is every coordinate. Then `p_m = Pr[W_{C_m}]` is nonincreasing, `p_0 = 1`,
and Lemma 6.5 with `ln ≤ log₂` is the recursion of `le_rpow_of_step` with the constant `27 / √2`
and `L = log₂ (|A| |B|)`: Holenstein's (7.6). Its conclusion is (7.7) for `p_n`, the winning
probability. -/
theorem winProb_pow_le (hAB : 2 ≤ Fintype.card A * Fintype.card B) {n : ℕ}
    (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B) :
    (G.pow n).winProb ha hb ≤ (1 - (1 - G.value) ^ 3 / 6000) ^
      ((n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B)) := by
  classical
  obtain ⟨_, _⟩ := nonempty_of_two_le_card_mul hAB
  have hx : (2 : ℝ) ≤ Fintype.card A * Fintype.card B := by exact_mod_cast hAB
  -- `L = log₂ (|A| |B|) ≥ 1` is the hypothesis `ℓ ≥ 1` of Lemma 7.1; Lemma 6.5 has `ln (|A| |B|)`.
  have hL : 1 ≤ Real.logb 2 (Fintype.card A * Fintype.card B) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact hx
  have hlog : Real.log (Fintype.card A * Fintype.card B) ≤
      Real.logb 2 (Fintype.card A * Fintype.card B) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
    exact mul_le_of_le_one_right (Real.log_nonneg (by linarith))
      ((Real.log_le_sub_one_of_pos two_pos).trans (by norm_num))
  -- The constant of Lemma 6.5 is within the range of `le_rpow_of_step`.
  have hK : 27 / Real.sqrt 2 ≤ 21 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  set L := Real.logb 2 (Fintype.card A * Fintype.card B)
  -- One step of the greedy choice: add a coordinate given by Lemma 6.5.
  let next : Finset (Fin n) → Finset (Fin n) := fun C =>
    if hC : C = univ then C else insert (G.exists_winProbOn_insert_le ha hb hC).choose C
  have hnext (C : Finset (Fin n)) (hC : C ≠ univ) :
      ∃ j ∉ C, next C = insert j C ∧ G.winProbOn ha hb (insert j C) ≤ G.winProbOn ha hb C *
        (G.value + 27 / Real.sqrt 2 * Real.sqrt ((#C * Real.log (Fintype.card A *
          Fintype.card B) + Real.log (1 / G.winProbOn ha hb C)) / (n - #C))) := by
    obtain ⟨hj, hle⟩ := (G.exists_winProbOn_insert_le ha hb hC).choose_spec
    exact ⟨_, hj, dite_eq_right hC, hle⟩
  have hsub (C : Finset (Fin n)) : C ⊆ next C := by
    by_cases hC : C = univ
    · rw [show next C = C from dite_eq_left hC]
    · obtain ⟨j, -, he, -⟩ := hnext C hC
      exact he ▸ Finset.subset_insert j C
  -- The sets `C_m` and their probabilities `p_m`.
  set Cs : ℕ → Finset (Fin n) := fun m => next^[m] ∅
  have hCs (m : ℕ) : Cs (m + 1) = next (Cs m) := Function.iterate_succ_apply' next m ∅
  have hcard (m : ℕ) (hm : m ≤ n) : #(Cs m) = m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      obtain ⟨j, hj, he, -⟩ := hnext (Cs m) ((Finset.card_lt_iff_ne_univ _).mp
        (by rw [ih (by omega), Fintype.card_fin]; omega))
      rw [hCs, he, Finset.card_insert_of_notMem hj, ih (by omega)]
  set p : ℕ → ℝ := fun m => G.winProbOn ha hb (Cs m)
  have hstep : ∀ m < n, p (m + 1) ≤
      p m * (G.value + 27 / Real.sqrt 2 * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m))) := by
    intro m hm
    obtain ⟨j, -, he, hle⟩ := hnext (Cs m) ((Finset.card_lt_iff_ne_univ _).mp
      (by rwa [hcard m hm.le, Fintype.card_fin]))
    have hpm : 0 ≤ p m := G.winProbOn_nonneg ha hb _
    have hnm : (0 : ℝ) ≤ n - m := by
      rw [sub_nonneg]
      exact_mod_cast hm.le
    calc p (m + 1) = G.winProbOn ha hb (insert j (Cs m)) := by
          change G.winProbOn ha hb (Cs (m + 1)) = _
          rw [hCs, he]
      _ ≤ _ := hle
      _ ≤ _ := by
        -- `gcongr` closes the side goals with `hpm` and `hnm`, and the main goal with `hlog`.
        rw [hcard m hm.le]
        gcongr
  have hrec := le_rpow_of_step G.value_nonneg G.value_le_one (by positivity) hK hL (p := p)
    (by simp [p, Cs]) (fun m => G.winProbOn_nonneg ha hb _)
    (fun m => by
      change G.winProbOn ha hb (Cs (m + 1)) ≤ G.winProbOn ha hb (Cs m)
      rw [hCs]
      exact G.winProbOn_anti ha hb (hsub (Cs m))) hstep
  have hn : Cs n = univ := Finset.eq_univ_of_card _ (by rw [hcard n le_rfl, Fintype.card_fin])
  rwa [← G.winProbOn_univ, ← hn]

/-- **Holenstein's parallel repetition theorem** [Holenstein, Theorem 2.5][Holenstein2009]. For a
two-prover one-round game `G` with value `v` and answer sets with `|A| |B| ≥ 2`, the value of the
`n`-fold parallel repetition is at most `(1 - (1 - v)³ / 6000)^{n / log₂ (|A| |B|)}`.

The strategies of the repetition are arbitrary maps of question tuples to answer tuples. The
hypothesis `|A| |B| ≥ 2` is the condition `ℓ ≥ 1` of Holenstein's Lemma 7.1, which his proof of
Theorem 2.5 applies with `ℓ = log (|A| |B|)`; when `|A| |B| = 1`, the exponent
`n / log (|A| |B|)` is undefined. -/
theorem value_pow_le (hAB : 2 ≤ Fintype.card A * Fintype.card B) (n : ℕ) :
    (G.pow n).value ≤ (1 - (1 - G.value) ^ 3 / 6000) ^
      ((n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B)) := by
  obtain ⟨_, _⟩ := nonempty_of_two_le_card_mul hAB
  exact ciSup_le fun ha => ciSup_le fun hb => G.winProb_pow_le hAB ha hb

/-- **The parallel repetition theorem for games of value at most `1 - ε`**
[Holenstein, Theorem 2.5][Holenstein2009]: if `v(G) ≤ 1 - ε` and `|A| |B| ≥ 2`, then
`v(Gⁿ) ≤ (1 - ε³ / 6000)^{n / log₂ (|A| |B|)}`. For `ε ≤ 0` the bound is at least `1`. -/
theorem value_pow_le_of_value_le (hAB : 2 ≤ Fintype.card A * Fintype.card B) {ε : ℝ}
    (hv : G.value ≤ 1 - ε) (n : ℕ) :
    (G.pow n).value ≤ (1 - ε ^ 3 / 6000) ^
      ((n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B)) := by
  obtain ⟨_, _⟩ := nonempty_of_two_le_card_mul hAB
  have ht : 0 ≤ (n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B) :=
    div_nonneg n.cast_nonneg (Real.logb_nonneg one_lt_two (by exact_mod_cast (by omega : 1 ≤ _)))
  rcases le_or_gt ε 0 with hε | hε
  · refine (G.pow n).value_le_one.trans (Real.one_le_rpow ?_ ht)
    have : ε ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hε
    linarith
  refine (G.value_pow_le hAB n).trans (Real.rpow_le_rpow ?_ ?_ ht)
  · have h1 : (1 - G.value) ^ 3 ≤ 1 := pow_le_one₀ (by linarith [G.value_le_one])
      (by linarith [G.value_nonneg])
    linarith
  · have : ε ^ 3 ≤ (1 - G.value) ^ 3 := pow_le_pow_left₀ hε.le (by linarith) 3
    linarith

end Theorem

end Cslib.PCP.TwoProverGame
