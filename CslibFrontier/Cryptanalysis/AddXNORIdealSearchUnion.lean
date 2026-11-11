/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealSecurity
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Tactic.Linarith

/-!
# Charging search verification and cut detection together

The independent verifier's successful outcomes already collide. Charge them in the same
experiment as the hidden-cut reveal instead of adding their collision probability again.
This removes the separate verification allowance, while retaining every auxiliary call.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.accept_or_bad_eq`: the complete union law
  derived from agreement at good final states.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.SearchUnion.source_search_rate`: actual search
  probability with one shared rational collision rate.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.SearchUnion.source_search_bound`: the full source
  parameter range with honest constants `6,18`.

[WangLvShenZhang2027], Theorem 8, PDF pp. 25–28, has sharper constants `3,10` and a
separate guessing term. They do not follow from this bound throughout the range. The source
uses a frontier sampler's exact-law claim (Lemma 10), which fails on collision traces; the
valid cut coupling here does not silently inherit its success-without-bad or guessing laws.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible

open Probability OracleComp RandomPermutation
open scoped ENNReal BigOperators

variable {Index Word : Type} [DecidableEq Word]

/-- Acceptance or the sticky flag has exactly the same law in both stopped worlds.
This preserves their overlap instead of summing two event probabilities. -/
theorem accept_or_bad_eq (perms changed : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Bool) :
    (ProbOracleComp.runWith (handler true perms changed) program (((), []), false)).map
        (fun (out, _, flag) => out || flag) =
      (ProbOracleComp.runWith (handler false perms changed) program (((), []), false)).map
        (fun (out, _, flag) => out || flag) := by
  classical
  let first := (ProbOracleComp.runWith (handler true perms changed) program
    (((), []), false)).map (fun (out, _, flag) => out || flag)
  let second := (ProbOracleComp.runWith (handler false perms changed) program
    (((), []), false)).map (fun (out, _, flag) => out || flag)
  have hf : first false = second false := by
    simp only [first, second, PMF.map_apply]
    apply tsum_congr
    rintro ⟨out, state, flag⟩
    cases out <;> cases flag <;> simp only [Bool.or_false, Bool.or_true,
      reduceCtorEq, ↓reduceIte]
    exact (identicalUntilBad perms changed).run_apply program (((), []), false)
      false (state, false) (by simp [FlagBad])
  have ht : (first true).toReal = (second true).toReal := by
    rw [Probability.PMF.toReal_true_eq_one_sub,
      Probability.PMF.toReal_true_eq_one_sub, hf]
  apply PMF.ext
  intro b
  cases b
  · exact hf
  · exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp ht

/-- Actual changed-world acceptance is bounded by the original joint acceptance/bad event. -/
theorem changed_accept_le_union (perms changed : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Bool) :
    interpret (Family.probEval changed) program true ≤
      ((ProbOracleComp.runWith (withTranscript (reader perms)) program ((), [])).map
        (fun (out, state) => out || traceBad perms changed state.2)) true := by
  have h := Probability.PMF.map_true_mono
    (ProbOracleComp.runWith (handler false perms changed) program (((), []), false))
    (E := Prod.fst) (F := fun (out, _, flag) => out || flag)
    (fun _ _ hout => by simp [hout])
  rw [output_law, ← accept_or_bad_eq, ← attach_flag, PMF.map_comp] at h
  exact h

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.SearchUnion

open Probability OracleComp RandomPermutation
open scoped ENNReal BigOperators

variable {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word] [Nonempty Word]

open scoped Classical in
/-- A supported independent verification/reveal execution charges acceptance and visible
answer disagreement to a single final collision event or to old-ledger covering. -/
theorem acceptance_or_bad_implies (hq : 0 < q) (cut : Cut (Label q))
    (perms : Label q → Equiv.Perm Word) (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (accepted : Bool) (before : Replay.State (Label q) Word)
    (hold : (accepted, before) ∈ (ProbOracleComp.runWith Replay.answer
      (verifiedAdversary adversary seed target) ⟨[], [], perms⟩).support)
    (result : Word × Word) (after : Replay.State (Label q) Word)
    (hnew : (result, after) ∈ (ProbOracleComp.runWith Replay.answer
      (Reveal.cutProgram cut seed target) before).support)
    (hevent : accepted || Visible.traceBad perms (cut.splice perms seed target) before.trace) :
    CutBounds.collision seed target ⟨before, after⟩ = true ∨
      CutBounds.covered cut seed target ⟨before, after⟩ = true := by
  have hevent' : accepted = true ∨
      Visible.traceBad perms (cut.splice perms seed target) before.trace = true := by
    cases accepted
    · simpa using hevent
    · simp
  rcases hevent' with ha | hb
  · have hc := Reveal.verification_collision hq perms seed target adversary before
      (by simpa only [ha] using hold)
    have hs := Replay.run_records_suffix (Reveal.cutProgram cut seed target) before
      result after hnew
    obtain ⟨more, he⟩ := hs
    left
    apply decide_eq_true
    intro hafter
    apply hc
    exact Forest.noCollision_append_right {seed, target} more before.records
      (by simpa only [he] using hafter)
  · obtain ⟨entry, hm, hd⟩ := List.any_eq_true.mp hb
    have hh : ∃ entry ∈ before.trace, cut.affected perms seed target entry.1 := by
      refine ⟨entry, hm, ?_⟩
      by_contra hn
      exact (of_decide_eq_true hd)
        (cut.eval_splice_eq_of_not_affected perms seed target entry.1 hn).symm
    have h := Reveal.cutHit_bridge cut perms seed target
      (verifiedAdversary adversary seed target) accepted before hold result after hnew hh
    simpa only [CutBounds.collision, CutBounds.covered, CutBounds.coveredRecords,
      decide_eq_true_eq] using h

/-- The actual changed-family verifier accepts no more often than the union charged in one
independent execution. Both original acceptance and answer-disagreement cases share its ledger. -/
theorem changed_accept_le (hq : 0 < q) (cut : Cut (Label q)) (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    ((PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
      interpret (Family.probEval (cut.splice perms seed target))
        (verifiedAdversary adversary seed target)) true ≤
      ((CutBounds.expose cut seed target (verifiedAdversary adversary seed target)).map
        (fun exposure => CutBounds.collision seed target exposure ||
          CutBounds.covered cut seed target exposure)) true := by
  classical
  let program := verifiedAdversary adversary seed target
  have hstep (perms : Label q → Equiv.Perm Word) :=
    Visible.changed_accept_le_union perms (cut.splice perms seed target) program
  simp only [CutBounds.expose, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_apply,
    PMF.map_comp, Function.comp_def]
  apply tsum_le_tsum
  intro perms
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply (hstep perms).trans
  rw [← Replay.erase_records program (⟨[], [], perms⟩ : Replay.State (Label q) Word),
    PMF.map_comp]
  simp only [PMF.map_apply]
  apply tsum_le_tsum
  rintro ⟨accepted, before⟩
  by_cases hs : (accepted, before) ∈
      (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).support
  · by_cases he : (accepted ||
        Visible.traceBad perms (cut.splice perms seed target) before.trace) = true
    · have hall : ∀ entry ∈ (ProbOracleComp.runWith Replay.answer
          (Reveal.cutProgram cut seed target) before).support,
          (CutBounds.collision seed target ⟨before, entry.2⟩ ||
            CutBounds.covered cut seed target ⟨before, entry.2⟩) = true := by
        rintro ⟨result, after⟩ hnew
        rcases acceptance_or_bad_implies hq cut perms seed target adversary
          accepted before hs result after hnew he with hc | hf
        · simp [hc]
        · simp [hf]
      have hone : ((ProbOracleComp.runWith Replay.answer
          (Reveal.cutProgram cut seed target) before).map
          (fun entry => CutBounds.collision seed target ⟨before, entry.2⟩ ||
            CutBounds.covered cut seed target ⟨before, entry.2⟩)) true = 1 := by
        rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
        exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr hall
      convert (by
        simpa only [PMF.map_apply, Function.comp_def, he.symm, ↓reduceIte, mul_one, program] using
        le_of_eq (congrArg (fun r =>
          (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩) (accepted, before) * r)
          hone.symm)) using 1 <;>
          simp only [Function.comp_def, he, ↓reduceIte, program]
    · simp [he, eq_comm (a := true)]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]

/-- Search acceptance is charged to the single verifier/reveal collision rate and old-ledger
covering. In particular there is no separate independent-verification collision summand. -/
theorem changed_accept_le_rate (hq : 0 < q) (cut : Cut (Label q)) (seed target : Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (B : ℕ) (hbudget : ProbOracleComp.IsQueryBounded
      (verifiedAdversary adversary seed target) B)
    (hQ : B + (cut.left.length + 1 + cut.right.length) < Fintype.card Word) :
    ((((PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
      interpret (Family.probEval (cut.splice perms seed target))
        (verifiedAdversary adversary seed target)) true)).toReal ≤
      Collisions.rate (Fintype.card Word) (B + (cut.left.length + 1 + cut.right.length)) +
      (((ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) []).map
        (fun (_, records) => CutBounds.coveredRecords cut seed target records)) true).toReal := by
  classical
  let program := verifiedAdversary adversary seed target
  have hu := Probability.PMF.map_true_le_add (CutBounds.expose cut seed target program)
    (E := fun e => CutBounds.collision seed target e || CutBounds.covered cut seed target e)
    (A := CutBounds.collision seed target) (B := CutBounds.covered cut seed target)
    (fun e _ he => by
      cases hc : CutBounds.collision seed target e <;> simp_all)
  rw [CutBounds.collision_law, CutBounds.covered_law] at hu
  have h := (changed_accept_le hq cut seed target adversary).trans hu
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩) h
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hr
  have hc := Collisions.collision_le_real seed target
    (B + (cut.left.length + 1 + cut.right.length)) hQ
    (program >>= fun _ => Reveal.cutProgram cut seed target)
    (hbudget.bind fun _ => Reveal.cutProgram_queryBound cut seed target)
  have hf : (((ProbOracleComp.runWith Ledger.answer
      (program >>= fun _ => Reveal.cutProgram cut seed target) []).map
        (fun (_, records) => decide (¬Forest.NoCollision {seed, target} records))) true).toReal ≤
      Collisions.rate (Fintype.card Word) (B + (cut.left.length + 1 + cut.right.length)) := by
    simpa only [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hc
  linarith

/-- The complete source search experiment with one shared verifier/reveal collision charge.
The source hypotheses suffice; no probability estimate is a premise. -/
theorem source_search_rate {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      Collisions.rate (2 ^ m) (T + q + q) +
        (T + q : ℕ) / (2 : ℝ) ^ ((q + 1) / 2) +
        (T + q : ℕ) / (2 : ℝ) ^ (q - (q + 1) / 2) := by
  let k := Security.middleIndex q hq
  have hk : k.val + 1 = (q + 1) / 2 := by simp only [k, Security.middleIndex]; omega
  have hd : 0 < q - (k.val + 1) := by rw [hk]; omega
  have hqT := (le_max_left q 4).trans hT
  have hw := Collisions.source_word_budget m T ((le_max_right q 4).trans hT) hlimit
  have hQ : T + q + q < 2 ^ m := by omega
  let bound : ℝ := Collisions.rate (2 ^ m) (T + q + q) +
    (T + q : ℕ) / (2 : ℝ) ^ (k.val + 1) +
    (T + q : ℕ) / (2 : ℝ) ^ (q - (k.val + 1))
  let B := fun seed target : Fin (2 ^ m) =>
    (PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        interpret (Family.probEval ((sourceCut bits k).splice perms seed target))
          (verifiedAdversary adversary seed target)
  have hfixed (seed target : Fin (2 ^ m)) : ((B seed target) true).toReal ≤ bound := by
    let C := fun bits : Operators q =>
      (ProbOracleComp.runWith Ledger.answer (verifiedAdversary adversary seed target) []).map
        (fun (_, records) => CutBounds.coveredRecords (sourceCut bits k) seed target records)
    let H := fun bits : Operators q =>
      (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        interpret (Family.probEval ((sourceCut bits k).splice perms seed target))
          (verifiedAdversary adversary seed target)
    let p := PMF.uniformOfFintype (Operators q)
    have hstep (bits : Operators q) : ((H bits) true).toReal ≤
        Collisions.rate (2 ^ m) (T + q + q) + ((C bits) true).toReal := by
      have hb := changed_accept_le_rate (by omega) (sourceCut bits k) seed target adversary
        (T + q) (verifiedAdversary_queryBound adversary T hbudget seed target)
        (by simpa only [Covering.source_cut_length, Fintype.card_fin] using hQ)
      simpa only [Covering.source_cut_length, Fintype.card_fin, H, C] using hb
    have hnrate := Collisions.rate_nonneg (2 ^ m) (T + q + q) hQ.le
    have hlin' := Probability.PMF.bind_apply_le_add_const_on_support p true
      (f := H) (g := C) (c := ENNReal.ofReal (Collisions.rate (2 ^ m) (T + q + q)))
      (fun bits _ => by
        have h := (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _)
          (add_nonneg hnrate ENNReal.toReal_nonneg)).mpr (hstep bits)
        rwa [ENNReal.ofReal_add hnrate ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), add_comm] at h)
    have hlin := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, ENNReal.ofReal_ne_top⟩) hlin'
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hnrate] at hlin
    have hc := Covering.uniform_cut_covering_run k hd seed target
      (verifiedAdversary adversary seed target) (T + q)
      (verifiedAdversary_queryBound adversary T hbudget seed target)
    have hn (n : ℕ) : ((T + q : ℕ) : ℝ≥0∞) / 2 ^ n ≠ ⊤ := by finiteness
    have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hn _, hn _⟩) hc
    rw [ENNReal.toReal_add (hn _) (hn _)] at hr
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat] at hr
    change ((B seed target) true).toReal ≤ _ at hlin
    dsimp only [bound]
    linarith
  have horder : plantedSearch adversary =
      (PMF.uniformOfFintype (Fin (2 ^ m))).bind fun seed =>
        (PMF.uniformOfFintype (Fin (2 ^ m))).bind (B seed) := by
    rw [plantedSearch_eq_verifiedDecision, ← coupledDecision_planted k]
    simp only [coupledDecision, challenges, Challenge.changed, pmf_norm,
      Bool.false_eq_true, ↓reduceIte, B]
    congr 1 with seed : 1
    calc
      _ = (PMF.uniformOfFintype (Operators q)).bind fun bits =>
          (PMF.uniformOfFintype (Fin (2 ^ m))).bind fun target =>
            (PMF.uniformOfFintype (Label q → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
              interpret (Family.probEval ((sourceCut bits k).splice perms seed target))
                (verifiedAdversary adversary seed target) := by
        congr 1 with bits : 1
        exact PMF.bind_comm _ _ _
      _ = _ := PMF.bind_comm _ _ _
  have hn : 0 ≤ bound := by
    exact add_nonneg (add_nonneg (Collisions.rate_nonneg _ _ hQ.le) (by positivity))
      (by positivity)
  have hp : (plantedSearch adversary) true ≤ ENNReal.ofReal bound := by
    rw [horder]
    apply Probability.PMF.bind_apply_le_on_support
    intro seed _
    apply Probability.PMF.bind_apply_le_on_support
    intro target _
    exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) hn).mpr (hfixed seed target)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  rw [ENNReal.toReal_ofReal hn] at hr
  simpa only [bound, hk] using hr

/-- A uniformly stronger repaired search inequality than the earlier `6,26` bound.
The collision rate is paid once, but the verifier and reveal still use up to `3*T` calls. -/
theorem source_search_bound {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      6 * T / 2 ^ ((q + 1) / 2) + 18 * (T : ℝ) ^ 2 / 2 ^ m := by
  have hqT := (le_max_left q 4).trans hT
  have hr := Collisions.rate_le_eighteen (2 ^ m) T (T + q + q)
    ((le_max_right q 4).trans hT) (by omega)
    (Collisions.source_word_budget m T ((le_max_right q 4).trans hT) hlimit)
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
  linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.SearchUnion
