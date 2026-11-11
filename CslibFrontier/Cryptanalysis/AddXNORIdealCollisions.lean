/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealLedger
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
public import Mathlib.Data.Fintype.Fin
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Numerical collision and forest bounds for actual fresh ledgers

Fresh entries come from the exact indexed permutation sampler, not independent guessed
records. The proof uses the remaining available-answer set and the actual ledger's growth.
A bounded analysis handler agrees with every budgeted run of the original handler; its
extension outside that horizon is used only to apply the library's bad-event union rule.

`source_forest_bound` gives `3*T/2^h + 8*T^2/2^m` for the executed analysis event
`collisionOrCovered`. Its collision coefficient is smaller than the source's `10`, but
this is not yet the Theorem 8 or Corollary 4 bound: the implication from an actual cut
hit to this event and the independent-search verification estimate remain unproved.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Collisions.collision_le`: the summed adaptive
  fresh-collision bound.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Collisions.source_collision_le_eight`: the
  `T+q` source-width specialization, charging every external call.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Collisions.source_forest_bound`: the numerical
  collision/two-sided-covering bound for the actual sampler's analysis event.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Collisions

open Probability OracleComp RandomPermutation
open scoped ENNReal

variable {Index Word Output : Type} [DecidableEq Index]
  [Fintype Word] [DecidableEq Word] [Nonempty Word]

omit [Fintype Word] [DecidableEq Word] [Nonempty Word] in
private theorem table_length (records : List (Forest.Record Index Word)) (label : Index) :
    (Ledger.tables records label).length ≤ records.length := by
  simp only [Ledger.tables, List.length_map]
  exact List.length_filter_le _ _

private theorem answer_hit (query : Index × PermQuery Word)
    (records : List (Forest.Record Index Word))
    (value : Word) (hm : cachedAnswer (Ledger.tables records query.1) query.2 = some value) :
    Ledger.answer query records = PMF.pure (value, records) := by
  simp only [Ledger.answer, Family.answer, answer_of_cachedAnswer_eq_some hm, PMF.pure_map,
    Ledger.update, hm, reduceCtorEq, ↓reduceIte]

private theorem answer_miss (query : Index × PermQuery Word)
    (records : List (Forest.Record Index Word)) (hvalid : Family.Valid (Ledger.tables records))
    (hm : cachedAnswer (Ledger.tables records query.1) query.2 = none) :
    Ledger.answer query records =
      (PMF.uniformOfFinset _ ((hvalid _).freshAnswers_nonempty hm)).map
        (fun value => (value, ⟨query.1, query.2, value⟩ :: records)) := by
  simp only [Ledger.answer, Family.answer,
    answer_of_cachedAnswer_eq_none hm ((hvalid _).freshAnswers_nonempty hm), PMF.map_comp,
    Function.comp_def, Ledger.update, hm, ↓reduceIte]

/-- One fresh draw hits at most the old seen values and the newly supplied argument. The
excluded-answer denominator uses the actual horizon and the reconstructed cache length. -/
theorem step_le (initial : Finset Word) (hi : initial.card ≤ 2) (Q : ℕ)
    (query : Index × PermQuery Word) (records : List (Forest.Record Index Word))
    (hvalid : Family.Valid (Ledger.tables records)) (hlen : records.length < Q)
    (hc : Forest.NoCollision initial records) :
    (Ledger.answer query records).toOuterMeasure {out | ¬Forest.NoCollision initial out.2} ≤
      (records.length + 2 : ℕ) * (2 : ℝ≥0∞) * ((Fintype.card Word - Q : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  cases hm : cachedAnswer (Ledger.tables records query.1) query.2 with
  | some value =>
    rw [answer_hit query records value hm]
    simp [hc]
  | none =>
    rw [answer_miss query records hvalid hm, PMF.toOuterMeasure_map_apply]
    have hevent : (fun value => (value, Forest.Record.mk query.1 query.2 value :: records)) ⁻¹'
        {out | ¬Forest.NoCollision initial out.2} =
        {value | value ∈ insert query.2.argument (Forest.seen initial records)} := by
      ext value
      simp [Forest.NoCollision, Forest.Record.known, hc]
      tauto
    rw [hevent, PMF.toOuterMeasure_uniformOfFinset]
    have hseen : (insert query.2.argument (Forest.seen initial records)).card ≤
        2 * (records.length + 2) := by
      have hb := Forest.seen_card_le initial records
      have hi' := Finset.card_insert_le query.2.argument (Forest.seen initial records)
      omega
    have hnum : ((freshAnswers (Ledger.tables records query.1) query.2).filter
        (· ∈ insert query.2.argument (Forest.seen initial records))).card ≤
        2 * (records.length + 2) :=
      (Finset.card_le_card (fun _ hx => (Finset.mem_filter.mp hx).2)).trans hseen
    have hden : Fintype.card Word - Q ≤
        (freshAnswers (Ledger.tables records query.1) query.2).card := by
      have ht := table_length records query.1
      have hf := card_freshAnswers_lower (Ledger.tables records query.1) query.2
      omega
    have hn : (((freshAnswers (Ledger.tables records query.1) query.2).filter
        (· ∈ insert query.2.argument (Forest.seen initial records))).card : ℝ≥0∞) ≤
        (records.length + 2 : ℕ) * (2 : ℝ≥0∞) := by
      exact_mod_cast (hnum.trans_eq (Nat.mul_comm _ _))
    exact mul_le_mul' hn (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr hden))

open scoped Classical in
/-- A proof-only extension outside the requested horizon. Every budgeted run agrees with the
original oracle; beyond the horizon or outside valid caches it simply keeps the ledger. -/
@[expose] noncomputable def boundedAnswer (Q : ℕ) (fallback : Word)
    (query : Index × PermQuery Word) : StateT (List (Forest.Record Index Word)) PMF Word :=
  fun records => if records.length < Q ∧ Family.Valid (Ledger.tables records) then
    Ledger.answer query records else PMF.pure (fallback, records)

private theorem bounded_run_eq (Q : ℕ) (fallback : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) (n : ℕ)
    (hbudget : ProbOracleComp.IsQueryBounded program n)
    (records : List (Forest.Record Index Word)) (hvalid : Family.Valid (Ledger.tables records))
    (hlen : records.length + n ≤ Q) :
    ProbOracleComp.runWith (boundedAnswer Q fallback) program records =
      ProbOracleComp.runWith Ledger.answer program records := by
  classical
  induction program using ProbOracleComp.induction generalizing n records with
  | pure out => rfl
  | sample_bind m cont ih =>
    rw [ProbOracleComp.sample_unifFin] at hbudget
    have hb := (IsCostBounded.liftBind_iff.mp hbudget).2
    simp only [Sum.elim_inl, Nat.sub_zero] at hb
    simp only [ProbOracleComp.runWith_sample_bind]
    congr 1 with coin : 1
    exact ih coin n (hb coin) records hvalid hlen
  | query_bind query cont ih =>
    have hb := IsCostBounded.liftBind_iff.mp hbudget
    simp only [Sum.elim_inr] at hb
    have hlt : records.length < Q := by omega
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    rw [boundedAnswer, ite_eq_left ⟨hlt, hvalid⟩]
    apply PMF.bind_congr_on_support
    rintro ⟨value, next⟩ hout
    apply ih value (n - 1) (hb.2 value) next
    · exact Ledger.answer_valid query records hvalid value next hout
    · have hg := Ledger.answer_length query records value next hout
      omega

/-- The bounded analysis handler is the original executed sampler on every `Q`-query program. -/
theorem bounded_run_eq_original (Q : ℕ) (fallback : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (hQ : ProbOracleComp.IsQueryBounded program Q) :
    ProbOracleComp.runWith (boundedAnswer Q fallback) program [] =
      ProbOracleComp.runWith Ledger.answer program [] :=
  bounded_run_eq Q fallback program Q hQ [] Family.valid_empty (by simp)

/-- A triangular union bound for the actual ledger, including all adaptive private coins.
Only the public query budget and two public roots are supplied; the fresh-hit estimates,
validity and ledger-growth bounds are derived from the actual sampler. -/
theorem collision_le (seed target : Word) (Q : ℕ)
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (hQ : ProbOracleComp.IsQueryBounded program Q) :
    (ProbOracleComp.runWith Ledger.answer program []).toOuterMeasure
        {out | ¬Forest.NoCollision {seed, target} out.2} ≤
      ((Q * 2 + Q.choose 2 : ℕ) : ℝ≥0∞) *
        (2 * ((Fintype.card Word - Q : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  let size (records : List (Forest.Record Index Word)) := records.length + 2
  let rate : ℝ≥0∞ := 2 * ((Fintype.card Word - Q : ℕ) : ℝ≥0∞)⁻¹
  have hstep : ∀ query records, ¬(¬Forest.NoCollision {seed, target} records) →
      (boundedAnswer Q seed query records).toOuterMeasure
          {out | ¬Forest.NoCollision {seed, target} out.2} ≤ size records * rate := by
    intro query records hgood
    by_cases hg : records.length < Q ∧ Family.Valid (Ledger.tables records)
    · rw [boundedAnswer, ite_eq_left hg]
      simpa only [size, rate, mul_assoc] using
        step_le {seed, target}
          (by simpa only [Finset.card_singleton] using Finset.card_insert_le seed {target})
          Q query records hg.2 hg.1 (not_not.mp hgood)
    · rw [boundedAnswer, ite_eq_right hg]
      simp [hgood]
  have hgrow : ∀ query records, ¬(¬Forest.NoCollision {seed, target} records) →
      ∀ out ∈ (boundedAnswer Q seed query records).support,
        ¬(¬Forest.NoCollision {seed, target} out.2) → size out.2 ≤ size records + 1 := by
    intro query records _ out hout _
    by_cases hg : records.length < Q ∧ Family.Valid (Ledger.tables records)
    · rw [boundedAnswer, ite_eq_left hg] at hout
      have hl := Ledger.answer_length query records out.1 out.2 hout
      dsimp only [size]
      omega
    · rw [boundedAnswer, ite_eq_right hg, PMF.mem_support_pure_iff] at hout
      cases hout
      exact Nat.le_succ _
  have h := ProbOracleComp.toOuterMeasure_bad_choose_two_le size rate hstep hgrow hQ
    (s := []) (by simp [Forest.NoCollision])
  rw [bounded_run_eq_original Q seed program hQ] at h
  simpa only [size, List.length_nil, Nat.zero_add, rate] using h

/-- The actual `Q`-query collision probability is at most `8*T^2/|Word|` when `Q≤2*T`,
`T≥4` and `8*T≤|Word|`. This is stronger than the collision allowance in source Lemma 12;
it does not by itself bound the hidden-cut stopping or search events. -/
theorem collision_le_eight (seed target : Word) (T Q : ℕ) (hT : 4 ≤ T)
    (hQ : Q ≤ 2 * T) (hwidth : 8 * T ≤ Fintype.card Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program Q) :
    ((ProbOracleComp.runWith Ledger.answer program []).toOuterMeasure
        {out | ¬Forest.NoCollision {seed, target} out.2}).toReal ≤
      8 * (T : ℝ) ^ 2 / Fintype.card Word := by
  have hQN : Q < Fintype.card Word := by omega
  have hd : 0 < Fintype.card Word - Q := Nat.sub_pos_of_lt hQN
  have hd0 : ((Fintype.card Word - Q : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hfinite : (((Q * 2 + Q.choose 2 : ℕ) : ℝ≥0∞) *
      (2 * ((Fintype.card Word - Q : ℕ) : ℝ≥0∞)⁻¹)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr hd0))
  have hprob := ENNReal.toReal_mono hfinite (collision_le seed target Q program hbudget)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.toReal_inv, Nat.cast_sub hQN.le] at hprob
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two] at hprob
  have hprob' : ((ProbOracleComp.runWith Ledger.answer program []).toOuterMeasure
        {out | ¬Forest.NoCollision {seed, target} out.2}).toReal ≤
      ((Q : ℝ) ^ 2 + 3 * Q) / (Fintype.card Word - Q) := by
    convert hprob using 1; field_simp; ring
  have ht : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have hq : (Q : ℝ) ≤ 2 * T := by exact_mod_cast hQ
  have hn : 8 * (T : ℝ) ≤ Fintype.card Word := by exact_mod_cast hwidth
  have htn : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hqn : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < Fintype.card Word := by exact_mod_cast Fintype.card_pos
  have hdpos : (0 : ℝ) < Fintype.card Word - Q := by
    exact sub_pos.mpr (by exact_mod_cast hQN)
  have hnum : (Q : ℝ) ^ 2 + 3 * Q ≤ (11 / 2 : ℝ) * T ^ 2 := by nlinarith
  have hden : 3 * (Fintype.card Word : ℝ) ≤ 4 * (Fintype.card Word - Q) := by linarith
  have hnum' := mul_le_mul_of_nonneg_left hnum hnpos.le
  have hden' := mul_le_mul_of_nonneg_left hden (sq_nonneg (T : ℝ))
  refine hprob'.trans ((div_le_div_iff₀ hdpos hnpos).mpr ?_)
  nlinarith [mul_nonneg (sq_nonneg (T : ℝ)) hnpos.le]

/-- A source-width specialisation: an actual `T+q`-query run with `q≤T`, `T≥4` and
`T≤2^(m-3)` has fresh-collision probability at most `8*T^2/2^m`. -/
theorem source_collision_le_eight (m q T : ℕ) (seed target : Fin (2 ^ m))
    (hq : q ≤ T) (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3))
    (program : ProbOracleComp (Family.Spec Index (Fin (2 ^ m))) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program (T + q)) :
    ((ProbOracleComp.runWith Ledger.answer program []).toOuterMeasure
        {out | ¬Forest.NoCollision {seed, target} out.2}).toReal ≤
      8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hm : 3 ≤ m := by
    by_contra hnot
    have hsub : m - 3 = 0 := by omega
    rw [hsub] at hlimit
    norm_num at hlimit
    omega
  have hpow : 2 ^ m = 8 * 2 ^ (m - 3) := by
    calc
      2 ^ m = 2 ^ ((m - 3) + 3) := by rw [Nat.sub_add_cancel hm]
      _ = 8 * 2 ^ (m - 3) := by rw [pow_add]; norm_num; omega
  have hw : 8 * T ≤ Fintype.card (Fin (2 ^ m)) := by
    rw [Fintype.card_fin _, hpow]
    omega
  simpa only [Fintype.card_fin _,
    Nat.cast_pow, Nat.cast_ofNat] using
    collision_le_eight seed target T (T + q) hT (by omega) hw program hbudget

open scoped Classical in
/-- Run the actual adaptive oracle program, then draw the independent hidden prefix/suffix.
This analysis event records a fresh collision or a completely queried hidden side. It is not
identified with the stopped-coupling event here. -/
@[expose] noncomputable def collisionOrCovered {q h d : ℕ}
    (seed target : Word) (left : Fin h → Fin q) (right : Fin d → Fin q)
    (program : ProbOracleComp (Spec q Word) Output) : PMF Bool := do
  let (_, records) ← ProbOracleComp.runWith Ledger.answer program []
  let words ← PMF.uniformOfFintype (Operators h × Operators d)
  return decide (¬Forest.NoCollision {seed, target} records ∨
    (∃ endpoint, Forest.Follows records seed (Forest.binaryLabels left words.1) endpoint) ∨
    ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
      (Forest.binaryLabels right words.2) endpoint)

/-- Both covering fractions and the collision probability for an executed adaptive program.
The fresh-entry budget is derived from its supported runs, including private randomness. -/
theorem collisionOrCovered_le {q h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (seed target : Word) (left : Fin h → Fin q) (right : Fin d → Fin q)
    (Q : ℕ) (program : ProbOracleComp (Spec q Word) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program Q) :
    ((collisionOrCovered seed target left right program).toOuterMeasure {true}).toReal ≤
      ((ProbOracleComp.runWith Ledger.answer program []).toOuterMeasure
        {out | ¬Forest.NoCollision {seed, target} out.2}).toReal +
      (Q : ℝ) / 2 ^ h + Q / 2 ^ d := by
  classical
  let kernel := fun (out : Output × List (Forest.Record (Label q) Word)) =>
    (PMF.uniformOfFintype (Operators h × Operators d)).map fun words =>
      decide (¬Forest.NoCollision {seed, target} out.2 ∨
        (∃ endpoint, Forest.Follows out.2 seed (Forest.binaryLabels left words.1) endpoint) ∨
        ∃ endpoint, Forest.Follows (out.2.map Forest.Record.reverse) target
          (Forest.binaryLabels right words.2) endpoint)
  have hbound := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (ProbOracleComp.runWith Ledger.answer program []) kernel
    {out | Forest.NoCollision {seed, target} out.2} {true}
    (error := (Q : ℝ) / 2 ^ h + Q / 2 ^ d)
    (by positivity) (fun ⟨out, records⟩ hout hc => by
      change Forest.NoCollision {seed, target} records at hc
      have hn := Ledger.run_length program Q hbudget out records hout
      have hf := Forest.uniform_two_sided_covered_le hh hd left right {seed, target}
        seed target (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _)) records hc
      have finite (n : ℕ) : (records.length : ℝ≥0∞) / 2 ^ n ≠ ⊤ :=
        ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num))
      have hfinite := ENNReal.add_ne_top.mpr ⟨finite h, finite d⟩
      have hr := ENNReal.toReal_mono hfinite hf
      simp only [ENNReal.toReal_add (finite h) (finite d), ENNReal.toReal_div,
        ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
      have hevent : (kernel (out, records)).toOuterMeasure {true} =
          (PMF.uniformOfFintype (Operators h × Operators d)).toOuterMeasure
            {words | (∃ endpoint, Forest.Follows records seed
              (Forest.binaryLabels left words.1) endpoint) ∨
              ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
                (Forest.binaryLabels right words.2) endpoint} := by
        rw [PMF.toOuterMeasure_map_apply]
        congr 1
        ext words
        simp [hc]
      rw [hevent]
      exact hr.trans (add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn)
        (by positivity)) (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn) (by positivity))))
  simpa only [collisionOrCovered, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map, kernel, Function.comp_def,
    Set.compl_ofPred, add_assoc] using hbound

/-- The numerical collision/forest event has the source's `3*T/2^h` covering term, and even
`8` in place of `10` in its collision term. This is an analysis-event bound: relating the
actual stopped coupling to this event is a separate obligation. -/
theorem source_forest_bound {q h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hsplit : h = d ∨ h = d + 1) (m T : ℕ)
    (seed target : Fin (2 ^ m)) (left : Fin h → Fin q) (right : Fin d → Fin q)
    (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3))
    (program : ProbOracleComp (Spec q (Fin (2 ^ m))) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program T) :
    ((collisionOrCovered seed target left right program).toOuterMeasure {true}).toReal ≤
      3 * T / 2 ^ h + 8 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hc := source_collision_le_eight m 0 T seed target (Nat.zero_le _) hT hlimit
    program (by simpa only [Nat.add_zero] using hbudget)
  have hf := collisionOrCovered_le hh hd seed target left right T program hbudget
  have hcover : (T : ℝ) / 2 ^ h + T / 2 ^ d ≤ 3 * T / 2 ^ h := by
    rcases hsplit with heq | heq
    · rw [heq]
      have hn : (0 : ℝ) ≤ T / 2 ^ d := by positivity
      have he : (3 * T : ℝ) / 2 ^ d = 3 * (T / 2 ^ d) := by ring
      rw [he]
      linarith
    · rw [heq, pow_succ]
      have hp : (2 : ℝ) ^ d ≠ 0 := by positivity
      field_simp
      ring_nf
      exact le_rfl
  linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Collisions
