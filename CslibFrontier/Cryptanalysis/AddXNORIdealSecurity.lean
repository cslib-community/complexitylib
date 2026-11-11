/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealCovering
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Tactic.Linarith

/-!
# Numerical security of the actual ideal-chain experiments

These bounds compose the uniform hidden-word covering law and the charged actual cut reveal.
The reveal's queries contribute to collisions while the covering term uses only the original
adversary's ledger. No security, probability or forest conclusion is a premise.

[WangLvShenZhang2027], Corollary 4 (PDF p. 28), is proved under its exact hypotheses;
the proof even obtains collision coefficient `8`. For Theorem 8 (PDF pp. 25–28), the actual
search-verification comparison followed by reveal uses `T+2*q` draws. `source_search_rate`
retains the resulting exact rational rate, and `source_search_bound` normalizes it to
`6*T/2^ceil(q/2) + 26*T^2/2^m`. This proves the same half-chain/birthday query barrier,
but not the source's sharper `3`, `10` and separate `2^(-q)` guessing argument.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Security.source_corollary_four`: literal source
  decision inequality for the actual planted/independent games.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Security.source_search_rate`: unrounded actual
  search bound with charged verification and reveal.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Security.source_search_bound`: the honest weaker
  search constants under the same source hypotheses.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Security.source_search_half_budget`: explicit
  half-chain/birthday budget alternatives for success at least one half.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Security

open Probability OracleComp RandomPermutation
open scoped ENNReal BigOperators

/-- The source's middle cut, with a prefix of `ceil(q/2)` labels including its cut edge. -/
@[expose] def middleIndex (q : ℕ) (hq : 3 ≤ q) : Fin q :=
  ⟨(q + 1) / 2 - 1, by omega⟩

/-- Actual cut-hit probability, averaged over the full hidden word in the original independent
family. The original adversary has budget `T`; the separately executed reveal contributes `q`. -/
theorem cutHit_average_rate {q : ℕ} {Output : Type} (k : Fin q)
    (hd : 0 < q - (k.val + 1)) (m T : ℕ) (seed target : Fin (2 ^ m))
    (program : ProbOracleComp (Spec q (Fin (2 ^ m))) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program T)
    (hQ : T + q < 2 ^ m) :
    (((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.cutHitGame (sourceCut bits k) perms seed target program) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q) + T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  let H := fun bits : Operators q =>
    (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
      Visible.cutHitGame (sourceCut bits k) perms seed target program
  let C := fun bits : Operators q => (ProbOracleComp.runWith Ledger.answer program []).map
    (fun (_, records) => CutBounds.coveredRecords (sourceCut bits k) seed target records)
  let p := PMF.uniformOfFintype (Operators q)
  have hH := Probability.PMF.toOuterMeasure_bind_toReal p H {true}
  have hC := Probability.PMF.toOuterMeasure_bind_toReal p C {true}
  simp only [PMF.toOuterMeasure_apply_singleton] at hH hC
  have hstep (bits : Operators q) : ((H bits) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q) + ((C bits) true).toReal := by
    have hb := CutBounds.cutHit_le_rate (sourceCut bits k) seed target program T hbudget
      (by simpa only [Covering.source_cut_length, Fintype.card_fin] using hQ)
    simpa only [Covering.source_cut_length, Fintype.card_fin, H, C] using hb
  have hlin : ((p.bind H) true).toReal ≤ Collisions.rate (2 ^ m) (T + q) +
      ((p.bind C) true).toReal := by
    rw [hH, hC]
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Operators q)))
      (fun bits _ => mul_le_mul_of_nonneg_left
        (hstep bits)
        (ENNReal.toReal_nonneg : 0 ≤ (p bits).toReal))
    simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal,
      one_mul, H, C] using hsum
  have hc := Covering.uniform_cut_covering_run k hd seed target program T hbudget
  have finite (n : ℕ) : (T : ℝ≥0∞) / 2 ^ n ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num))
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨finite (k.val + 1), finite (q - (k.val + 1))⟩) hc
  simp only [ENNReal.toReal_add (finite (k.val + 1)) (finite (q - (k.val + 1))),
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
  change ((p.bind C) true).toReal ≤ _ at hr
  change ((p.bind H) true).toReal ≤ _
  linarith

/-- Source-width specialization of the exact averaged cut-hit bound. -/
theorem source_cutHit_average {q : ℕ} {Output : Type} (k : Fin q)
    (hd : 0 < q - (k.val + 1)) (m T : ℕ) (seed target : Fin (2 ^ m))
    (program : ProbOracleComp (Spec q (Fin (2 ^ m))) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    (((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.cutHitGame (sourceCut bits k) perms seed target program) true).toReal ≤
      8 * (T : ℝ) ^ 2 / 2 ^ m + T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  have hw := Collisions.source_word_budget m T hT hlimit
  have h := cutHit_average_rate k hd m T seed target program hbudget (by omega)
  have hr := Collisions.rate_le_eight (2 ^ m) T (T + q) hT (by omega) hw
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hr
  linarith

/-- The actual fixed-input stopped coupling is bounded by the charged cut-hit experiment. -/
theorem bad_average_rate {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1))
    (m T : ℕ) (seed target : Fin (2 ^ m))
    (program : ProbOracleComp (Spec q (Fin (2 ^ m))) Bool)
    (hbudget : ProbOracleComp.IsQueryBounded program T)
    (hQ : T + q < 2 ^ m) :
    (((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.badGame perms ((sourceCut bits k).splice perms seed target) program) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q) + T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  have hm : ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.badGame perms ((sourceCut bits k).splice perms seed target) program) true ≤
      ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
        (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
          Visible.cutHitGame (sourceCut bits k) perms seed target program) true := by
    apply Probability.PMF.bind_apply_mono_on_support
    intro bits _
    apply Probability.PMF.bind_apply_mono_on_support
    intro perms _
    exact Visible.badGame_le_cutHit (sourceCut bits k) perms seed target program
  exact (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hm).trans
    (cutHit_average_rate k hd m T seed target program hbudget hQ)

/-- The whole visible stopped game, with the source's actual seed/word/family/target sampling
order, has the derived numerical bound. No conditional stopping probability is assumed. -/
theorem visibleBad_bound_rate {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1)) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) → ProbOracleComp (Spec q (Fin (2 ^ m))) Bool)
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hQ : T + q < 2 ^ m) :
    ((visibleBadGame k adversary) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q) + T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  let B := fun seed target : Fin (2 ^ m) =>
    (PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.badGame perms ((sourceCut bits k).splice perms seed target) (adversary seed target)
  have horder : visibleBadGame k adversary =
      (PMF.uniformOfFintype (Fin (2 ^ m))).bind fun seed =>
        (PMF.uniformOfFintype (Fin (2 ^ m))).bind (B seed) := by
    simp only [visibleBadGame, challenges, Challenge.changed, pmf_norm, B]
    congr 1 with seed : 1
    calc
      _ = (PMF.uniformOfFintype (Operators q)).bind fun bits =>
          (PMF.uniformOfFintype (Fin (2 ^ m))).bind fun target =>
            (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
              Visible.badGame perms ((sourceCut bits k).splice perms seed target)
                (adversary seed target) := by
        congr 1 with bits : 1
        exact PMF.bind_comm _ _ _
      _ = _ := PMF.bind_comm _ _ _
  let bound : ℝ := Collisions.rate (2 ^ m) (T + q) +
    T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1))
  have hn : 0 ≤ bound := by
    exact add_nonneg (add_nonneg (Collisions.rate_nonneg _ _ hQ.le) (by positivity))
      (by positivity)
  have hp : (visibleBadGame k adversary) true ≤ ENNReal.ofReal bound := by
    rw [horder]
    apply Probability.PMF.bind_apply_le_on_support
    intro seed _
    apply Probability.PMF.bind_apply_le_on_support
    intro target _
    exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) hn).mpr
      (bad_average_rate k hd m T seed target (adversary seed target)
        (hbudget seed target) hQ)
  simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hp

/-- The source-width stopped game bound with `T+q` charged draws and collision coefficient `8`. -/
theorem source_visibleBad_bound {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1)) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) → ProbOracleComp (Spec q (Fin (2 ^ m))) Bool)
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((visibleBadGame k adversary) true).toReal ≤
      8 * (T : ℝ) ^ 2 / 2 ^ m + T / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  have hw := Collisions.source_word_budget m T hT hlimit
  have h := visibleBad_bound_rate k hd m T adversary hbudget (by omega)
  have hr := Collisions.rate_le_eight (2 ^ m) T (T + q) hT (by omega) hw
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hr
  linarith

/-- The source middle-cut stopping probability, with collision coefficient `8` instead of `10`.
This is a bound on the actual planted/independent coupling, not a surrogate analysis event. -/
theorem source_middle_bad_bound {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) → ProbOracleComp (Spec q (Fin (2 ^ m))) Bool)
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hqT : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((visibleBadGame (middleIndex q hq) adversary) true).toReal ≤
      3 * T / 2 ^ ((q + 1) / 2) + 8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hk : (middleIndex q hq).val + 1 = (q + 1) / 2 := by simp only [middleIndex]; omega
  have hd : 0 < q - ((middleIndex q hq).val + 1) := by rw [hk]; omega
  have hb := source_visibleBad_bound (middleIndex q hq) hd m T adversary hbudget hqT hT hlimit
  rw [hk] at hb
  have hs : (q + 1) / 2 = q - (q + 1) / 2 ∨
      (q + 1) / 2 = q - (q + 1) / 2 + 1 := by omega
  have hc := Collisions.covering_fractions_le_three T ((q + 1) / 2) (q - (q + 1) / 2) hs
  linarith

/-- Corollary 4, PDF p. 28, for independent permutations on the `2^m`-word alphabet:
under the exact source hypotheses, the actual decision advantage is at most the stated
`3*T/2^ceil(q/2) + 10*T^2/2^m`. The proof obtains collision coefficient `8`. -/
theorem source_corollary_four {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) → ProbOracleComp (Spec q (Fin (2 ^ m))) Bool)
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    (Crypto.Game.advantage (decision true adversary) (decision false adversary) : ℝ) ≤
      3 * T / 2 ^ ((q + 1) / 2) + 10 * (T : ℝ) ^ 2 / 2 ^ m := by
  have h := NNReal.coe_le_coe.mpr (decision_advantage_le_visibleBad (middleIndex q hq) adversary)
  change (Crypto.Game.advantage (decision true adversary) (decision false adversary) : ℝ) ≤
    ((visibleBadGame (middleIndex q hq) adversary) true).toReal at h
  have hb := source_middle_bad_bound hq m T adversary hbudget (le_trans (le_max_left _ _) hT)
    (le_trans (le_max_right _ _) hT) hlimit
  have hn : (8 : ℝ) * T ^ 2 ≤ 10 * T ^ 2 := by nlinarith [sq_nonneg (T : ℝ)]
  have hr := div_le_div_of_nonneg_right hn (show (0 : ℝ) ≤ 2 ^ m by positivity)
  linarith

/-- The unrounded actual search bound retains the exact `T+2*q` collision rate and both
covering fractions for the `T+q` verifier. This is sharper than `source_search_bound` when the
parameters leave slack in its source-width normalization; it is not the source's sharper
planted-verification/guessing argument. -/
theorem source_search_rate {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q + q) +
        (T + q : ℕ) / (2 : ℝ) ^ ((q + 1) / 2) +
        (T + q : ℕ) / (2 : ℝ) ^ (q - (q + 1) / 2) + 8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hqT := (le_max_left q 4).trans hT
  have hT4 := (le_max_right q 4).trans hT
  have hw := Collisions.source_word_budget m T hT4 hlimit
  have hk : (middleIndex q hq).val + 1 = (q + 1) / 2 := by simp only [middleIndex]; omega
  have hd : 0 < q - ((middleIndex q hq).val + 1) := by rw [hk]; omega
  have hb := visibleBad_bound_rate (middleIndex q hq) hd m (T + q)
    (verifiedAdversary adversary)
    (fun seed target => verifiedAdversary_queryBound adversary T hbudget seed target) (by omega)
  rw [hk] at hb
  have hp := Reveal.source_search_le_visibleBad (by omega) (middleIndex q hq) m T
    adversary hbudget hqT hT4 hlimit
  linarith

/-- A repaired Theorem 8 bound under exactly its source hypotheses. This proof uses the actual
search-verification coupling and then reveals the hidden sides, so its budget is `T+2*q`.
Consequently its honest constants are `6` and `26`, instead of the source's `3` and `10`;
it does not claim the source's sharper guessing-term argument. -/
theorem source_search_bound {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      6 * T / 2 ^ ((q + 1) / 2) + 26 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hqT := (le_max_left q 4).trans hT
  have hT4 := (le_max_right q 4).trans hT
  have hw := Collisions.source_word_budget m T hT4 hlimit
  have hr := Collisions.rate_le_eighteen (2 ^ m) T (T + q + q) hT4 (by omega) hw
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hr
  have hs : (q + 1) / 2 = q - (q + 1) / 2 ∨
      (q + 1) / 2 = q - (q + 1) / 2 + 1 := by omega
  have hc := Collisions.covering_fractions_le_three (T + q) ((q + 1) / 2)
    (q - (q + 1) / 2) hs
  have hn : (3 : ℝ) * (T + q : ℕ) ≤ 6 * T := by
    exact_mod_cast (show 3 * (T + q) ≤ 6 * T by omega)
  have hf := div_le_div_of_nonneg_right hn
    (show (0 : ℝ) ≤ 2 ^ ((q + 1) / 2) by positivity)
  have hp := source_search_rate hq m T adversary hbudget hT hlimit
  calc
    _ ≤ Collisions.rate (2 ^ m) (T + q + q) +
        (T + q : ℕ) / (2 : ℝ) ^ ((q + 1) / 2) +
        (T + q : ℕ) / (2 : ℝ) ^ (q - (q + 1) / 2) + 8 * (T : ℝ) ^ 2 / 2 ^ m := hp
    _ ≤ 18 * (T : ℝ) ^ 2 / 2 ^ m + 6 * T / 2 ^ ((q + 1) / 2) +
        8 * (T : ℝ) ^ 2 / 2 ^ m := by linarith
    _ = _ := by ring

/-- The repaired search bound gives the same two-parameter generic query barrier as the source:
constant success forces either a half-chain budget or a birthday budget. The explicit constants
reflect `source_search_bound`, not the sharper constants asserted in Theorem 8. -/
theorem source_search_half_budget {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3))
    (hsuccess : (1 / 2 : ℝ) ≤ ((plantedSearch adversary) true).toReal) :
    (2 : ℝ) ^ ((q + 1) / 2) ≤ 24 * T ∨ (2 : ℝ) ^ m ≤ 104 * T ^ 2 := by
  have hb := source_search_bound hq m T adversary hbudget hT hlimit
  by_contra hn
  push Not at hn
  have hf : 6 * (T : ℝ) / 2 ^ ((q + 1) / 2) < 1 / 4 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [hn.1]
  have hc : 26 * (T : ℝ) ^ 2 / 2 ^ m < 1 / 4 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [hn.2]
  linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Security
