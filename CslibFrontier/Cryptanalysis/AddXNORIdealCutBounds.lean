/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealReveal
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Tactic.Linarith

/-!
# Probability transfer for the actual cut reveal

The observer's cut-hit event is compared with an executed auxiliary reveal in the same hidden
family. Old and new fresh ledgers are retained separately, so the visible covering term does
not grow to include auxiliary calls. The collision term includes those calls.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.Exposure`: old and revealed replay states.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.expose`: actual adaptive run and reveal.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.hit_law`: the reveal preserves the
  original visible hit probability.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.collision_law`: every auxiliary fresh
  draw is charged through the exact sampler law.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.covered_law`: covering retains only
  the old adversary ledger.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds.cutHit_le_rate`: the actual probability
  bridge with an explicit total query horizon.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds

open Probability OracleComp RandomPermutation

/-- Preserve the visible ledger before adding the charged hidden-path observations. -/
structure Exposure (Index Word : Type) where
  /-- State after the adversary, with no auxiliary queries in its transcript. -/
  before : Replay.State Index Word
  /-- State after the concrete auxiliary cut program, including all its fresh draws. -/
  after : Replay.State Index Word

variable {Index Word : Type} [Fintype Index] [DecidableEq Index]
  [Fintype Word] [DecidableEq Word] [Nonempty Word]

/-- Execute the adversary and the actual hidden-path reveal in one independent uniform family. -/
@[expose] noncomputable def expose {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) : PMF (Exposure Index Word) := do
  let perms ← PMF.uniformOfFintype (Index → Equiv.Perm Word)
  let (_, before) ← ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩
  (ProbOracleComp.runWith Replay.answer (Reveal.cutProgram cut seed target) before).map
    (fun (_, after) => ⟨before, after⟩)

open scoped Classical in
/-- The original visible cut hit; the fixed family is retained privately in the old state. -/
@[expose] noncomputable def hit (cut : Cut Index) (seed target : Word)
    (exposure : Exposure Index Word) : Bool :=
  decide (∃ entry ∈ exposure.before.trace,
    cut.affected exposure.before.perms seed target entry.1)

open scoped Classical in
/-- A fresh collision anywhere in the adversary/reveal execution. -/
@[expose] noncomputable def collision (seed target : Word)
    (exposure : Exposure Index Word) : Bool :=
  decide (¬Forest.NoCollision {seed, target} exposure.after.records)

omit [Fintype Index] [Fintype Word] [Nonempty Word] in
open scoped Classical in
/-- The covering event is a predicate on the old visible fresh ledger only. -/
@[expose] noncomputable def coveredRecords (cut : Cut Index) (seed target : Word)
    (records : List (Forest.Record Index Word)) : Bool :=
  decide (Forest.NoCollision {seed, target} records ∧
    ((∃ endpoint, Forest.Follows records seed (cut.left ++ [cut.edge]) endpoint) ∨
      ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
        cut.right.reverse endpoint))

/-- A hidden side covered by the old visible ledger, outside its collision event. -/
@[expose] noncomputable def covered (cut : Cut Index) (seed target : Word)
    (exposure : Exposure Index Word) : Bool :=
  coveredRecords cut seed target exposure.before.records

/-- The support-wise bridge is derived from the two actual supported runs in the experiment. -/
theorem hit_implies {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) (exposure : Exposure Index Word)
    (he : exposure ∈ (expose cut seed target program).support) (hh : hit cut seed target exposure) :
    collision seed target exposure = true ∨ covered cut seed target exposure = true := by
  simp only [expose, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
    PMF.mem_support_map_iff] at he
  obtain ⟨perms, _, ⟨⟨out, before⟩, hold, ⟨⟨result, after⟩, hnew, he⟩⟩⟩ := he
  cases he
  have hπ := (Replay.run_trace_eval perms program out before hold).1
  have hh' : ∃ entry ∈ before.trace, cut.affected perms seed target entry.1 := by
    simpa only [hit, decide_eq_true_eq, hπ] using hh
  have hb := Reveal.cutHit_bridge cut perms seed target program out before hold
    result after hnew hh'
  simpa only [collision, covered, coveredRecords, decide_eq_true_eq] using hb

omit [Nonempty Word] in
/-- The original cut-hit game has its unchanged probability in the reveal experiment. -/
theorem hit_law {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (expose cut seed target program).map (hit cut seed target) =
      (PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
        Visible.cutHitGame cut perms seed target program := by
  classical
  simp only [expose, PMF.monad_bind_eq_bind, PMF.map_bind]
  congr 1 with perms : 1
  rw [Reveal.cutHitGame_replay, PMF.map]
  apply PMF.bind_congr_on_support
  rintro ⟨out, before⟩ hold
  have hπ := (Replay.run_trace_eval perms program out before hold).1
  simp only [PMF.map_comp, Function.comp_def, hit]
  calc
    _ = (ProbOracleComp.runWith Replay.answer (Reveal.cutProgram cut seed target) before).map
        (fun _ => decide (∃ entry ∈ before.trace, cut.affected perms seed target entry.1)) := by
      congr 1
      funext entry
      apply decide_eq_decide.mpr
      rw [hπ]
    _ = _ := PMF.map_const _ _

open scoped Classical in
/-- Collision probability is preserved by the joint replay law, including the reveal's draws. -/
theorem collision_law {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (expose cut seed target program).map (collision seed target) =
      (ProbOracleComp.runWith Ledger.answer
        (program >>= fun _ => Reveal.cutProgram cut seed target) []).map
          (fun (_, records) => decide (¬Forest.NoCollision {seed, target} records)) := by
  classical
  rw [← Replay.fresh_law]
  simp only [expose, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, ProbOracleComp.runWith_bind, collision]

/-- The covering probability retains only the adversary's old ledger. Auxiliary queries are
absent from this term, even though their draws remain charged in `collision_law`. -/
theorem covered_law {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (expose cut seed target program).map (covered cut seed target) =
      (ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) => coveredRecords cut seed target records) := by
  rw [← Replay.fresh_law]
  simp only [expose, PMF.monad_bind_eq_bind, PMF.map, PMF.bind_bind,
    Function.comp_def, PMF.pure_bind, covered, PMF.bind_const]

open scoped Classical in
/-- The actual independent-family cut-hit probability is bounded by collisions during the
whole adversary/reveal run plus collision-free covering by the original visible ledger. -/
theorem cutHit_le {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
        Visible.cutHitGame cut perms seed target program) true ≤
      ((ProbOracleComp.runWith Ledger.answer
        (program >>= fun _ => Reveal.cutProgram cut seed target) []).map
          (fun (_, records) => decide (¬Forest.NoCollision {seed, target} records))) true +
      ((ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) => coveredRecords cut seed target records)) true := by
  have h := PMF.map_true_le_add (expose cut seed target program)
    (hit_implies cut seed target program)
  rw [hit_law, collision_law, covered_law] at h
  exact h

/-- Exact summed collision rate for the actual cut-hit experiment, plus covering by the old
visible ledger. The query horizon includes every auxiliary reveal call. -/
theorem cutHit_le_rate {Output : Type} (cut : Cut Index) (seed target : Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) (B : ℕ)
    (hbudget : ProbOracleComp.IsQueryBounded program B)
    (hQ : B + (cut.left.length + 1 + cut.right.length) < Fintype.card Word) :
    (((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
        Visible.cutHitGame cut perms seed target program) true).toReal ≤
      Collisions.rate (Fintype.card Word) (B + (cut.left.length + 1 + cut.right.length)) +
      (((ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) => coveredRecords cut seed target records)) true).toReal := by
  classical
  have h := cutHit_le cut seed target program
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

omit [Fintype Word] [DecidableEq Word] [Nonempty Word] in
/-- The executed reveal contributes at most the source collision allowance when its syntactic
path length is at most `T`. The old covering term is still a probability of the original
adversary's ledger, not one enlarged by hidden observations. -/
theorem source_cutHit_le {Output : Type} (cut : Cut Index) (m T : ℕ)
    (seed target : Fin (2 ^ m))
    (program : ProbOracleComp (Family.Spec Index (Fin (2 ^ m))) Output)
    (hbudget : ProbOracleComp.IsQueryBounded program T)
    (hcut : cut.left.length + 1 + cut.right.length ≤ T)
    (hT : 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    (((PMF.uniformOfFintype (Index → Equiv.Perm (Fin (2 ^ m)))).bind fun perms =>
        Visible.cutHitGame cut perms seed target program) true).toReal ≤
      8 * (T : ℝ) ^ 2 / 2 ^ m +
      (((ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) => coveredRecords cut seed target records)) true).toReal := by
  have hw : 8 * T ≤ Fintype.card (Fin (2 ^ m)) := by
    simpa only [Fintype.card_fin] using Collisions.source_word_budget m T hT hlimit
  have hQ : T + (cut.left.length + 1 + cut.right.length) < Fintype.card (Fin (2 ^ m)) := by
    omega
  have h := cutHit_le_rate cut seed target program T hbudget hQ
  have hr := Collisions.rate_le_eight (Fintype.card (Fin (2 ^ m))) T
    (T + (cut.left.length + 1 + cut.right.length)) hT (by omega) hw
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h hr
  linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.CutBounds
