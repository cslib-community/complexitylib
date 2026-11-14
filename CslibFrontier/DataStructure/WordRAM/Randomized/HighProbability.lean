/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# With-High-Probability Word-RAM State-Transition Implementations

This module defines a reusable Word-RAM subroutine certificate
(`Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl`) for data structures whose
individual operations execute within a **deterministic worst-case** instruction budget
`worstCaseTime : ℕ` with probability at least `1 - failureProb` (for instance, `O(1)` worst-case
instructions with probability at least `1 - n_max ^ (-c)` in fixed-capacity hash tables; see
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024, Sections 2.1 and
5][BenderFarachColtonKuszmaulKuszmaul2024]).

## Design

1. **Exact operational coupling via `ExecRand` and clocked `evalRand`:**
   - First, `Cslib.WordRAM.ExecRand.tsum_le_eval_runRand_assemble` and
     `Cslib.WordRAM.ExecRand.toOuterMeasure_le_evalRand_program` prove that for *any* fault-free
     structured randomized execution `ExecRand w c x m` (even when rare fallback branches take more
     than `B` instructions), every execution path `(y, n)` with `n ≤ B` already halts cleanly at
     `RandCfg.halted (y.regs out) y` in the clocked flat-machine distribution
     `evalRand w (c.program out) (B + 1) ⟨0, x⟩`.
   - In `HighProbStateTransitionImpl`, each step `o : D.Op` from a coupled distribution
     `ν : PMF (CoupledState Seed D.State r_ds)` produces a transition kernel
     `μ_step : CoupledState Seed D.State r_ds → PMF (CoupledState Seed D.State r_ds × ℕ)` coupled
     with `ExecRand w P.code t.data (m_step t)` via
     `(μ_step t).map (fun p => (p.1.data, p.2)) = (m_step t).eval`, realizing `D.step`, `decode`,
     `rep`, and `Modifies (Block.mk base space).footprint` on every supported branch while bounding
     the slow-path probability `(ν.bind μ_step).toOuterMeasure {p | worstCaseTime < p.2}` by
     `failureProb` (averaged over `ν`, so both static-seed hash tables and per-operation randomized
     algorithms are covered uniformly).

2. **Both per-operation (`step_whp`) and whole-sequence (`seq_whp`) worst-case bounds:**
   - `step_whp` and `step_whp_ofFn` certify that from any reachable coupled distribution `ν` (after
     an oblivious prefix of *any* length), running `P.code.program outReg` at deterministic horizon
     `worstCaseTime + 1` is fault-free across all horizons and halts within `worstCaseTime + 1`
     instructions in a valid successor state with probability at least `1 - failureProb`.
   - `ExecWhpSteps`, `steps_whp`, `seq_whp`, and `seq_whp_ofFn` track the trajectory record
     `WhpSeqOutcome` (recording the current coupled state, the accumulated transcript
     `List (Sigma D.Result)`, and `maxSteps : ℕ`, the maximum body instruction count across all
     operations in `ops`), proving via a union bound that
     `τ_final.toOuterMeasure {tr | worstCaseTime < tr.maxSteps} ≤ ops.length * failureProb` and
     hence every operation in `ops` runs in at most `worstCaseTime` worst-case body instructions
     with probability at least `1 - ops.length * failureProb`.

3. **Basis transport and embeddings:**
   - `mapSimulates` and `toStandard` lift any `HighProbStateTransitionImpl` from `Basis.exact` to
     `Basis.standard` preserving exact instruction bounds and failure probabilities.
   - `Cslib.DataStructure.WordRAM.StateTransitionImpl.toHighProb` embeds any unamortized
     (`initPotential = 0`, `potential = 0`) deterministic `StateTransitionImpl` with uniform step
     bound `worstCaseTime` at `failureProb = 0`.

## Main definitions

* `Cslib.DataStructure.WordRAM.Randomized.WhpSeqOutcome`: trajectory outcome bundling current
  `CoupledState`, accumulated input-output `transcript`, and maximum per-operation instruction count
  `maxSteps`.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl`: reusable
  with-high-probability Word-RAM subroutine implementation certificate.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl.ofFn`: constructor for
  functional specifications `[D.HasStepFn stepFn]`.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl.ExecWhpSteps`: operational
  multi-step trajectory execution relation across `ops : List D.Op`.

## Main results

* `Cslib.WordRAM.ExecRand.tsum_le_eval_runRand_assemble`,
  `Cslib.WordRAM.ExecRand.toOuterMeasure_le_evalRand_program`,
  `Cslib.WordRAM.ExecRand.one_sub_le_evalRand_program`: partial-horizon halting probability bridges
  from `ExecRand` to clocked `evalRand` at horizon `B + 1`.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl.initFresh_exec`,
  `initClear_exec`, `initFresh_program`: worst-case randomized initialization bounds.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl.step_whp`, `step_whp_ofFn`:
  per-operation worst-case halting bounds at horizon `worstCaseTime + 1`.
* `Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl.steps_whp`, `seq_whp`,
  `steps_whp_ofFn`, `seq_whp_ofFn`, `seq_whp_poly_ofFn`: whole-sequence worst-case execution bounds
  across arbitrary and polynomial-length oblivious sequences.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 2.1 and 5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.WordRAM

open Cslib.Probability
open scoped ENNReal

section PartialHorizon

variable {B : Basis} {r : ℕ}

/-- Complementary lower bound for discrete `PMF` outer measure: if `p.toOuterMeasure s ≤ δ`, then
`1 - δ ≤ p.toOuterMeasure sᶜ`. -/
theorem _root_.Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl {α : Type*}
    (p : PMF α) (s : Set α) {δ : ℝ≥0∞} (hδ : p.toOuterMeasure s ≤ δ) :
    1 - δ ≤ p.toOuterMeasure sᶜ := by
  have hsum := Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal p s
  refine tsub_le_iff_right.mpr ?_
  calc
    1 = p.toOuterMeasure s + p.toOuterMeasure sᶜ := hsum.symm
    _ ≤ δ + p.toOuterMeasure sᶜ := by gcongr
    _ = p.toOuterMeasure sᶜ + δ := add_comm _ _

private theorem eval_runRand_step_jump {w pc t k : ℕ} {p : Program B r} {x : Data r}
    (hp : p[pc]? = some (.jump t)) :
    (runRand w p (k + 1) (.running ⟨pc, x⟩)).eval =
      (runRand w p k (.running ⟨t, x⟩)).eval := by
  rw [runRand_succ, stepRand_jump (s := ⟨pc, x⟩) hp, pure_bind]

private theorem eval_runRand_step_branch_pos {w pc t k : ℕ} {p : Program B r}
    {c : Cond r} {x : Data r} (hp : p[pc]? = some (.branch c t)) (hc : c.Holds x) :
    (runRand w p (k + 1) (.running ⟨pc, x⟩)).eval =
      (runRand w p k (.running ⟨t, x⟩)).eval := by
  rw [runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hp]
  simp only [hc, ↓reduceIte, pure_bind]

private theorem eval_runRand_step_branch_neg {w pc t k : ℕ} {p : Program B r}
    {c : Cond r} {x : Data r} (hp : p[pc]? = some (.branch c t)) (hc : ¬c.Holds x) :
    (runRand w p (k + 1) (.running ⟨pc, x⟩)).eval =
      (runRand w p k (.running ⟨pc + 1, x⟩)).eval := by
  rw [runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hp]
  simp only [hc, ↓reduceIte, pure_bind]

/-- **Partial-horizon assembly lower bound (`tsum_le_eval_runRand_assemble`).**
For any structured execution `ExecRand w c x m` assembled at `pc` inside `p` (even when `m` has
branches taking more than `T` steps), the probability mass reaching `cfg₀` at step `T` is bounded
below by the sum over all fast branches `z = (y, n)` with `n ≤ T` of continuing from
`⟨pc + c.size, y⟩` for the remaining `T - n` steps. -/
theorem ExecRand.tsum_le_eval_runRand_assemble {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} {p : Program B r} {pc : ℕ}
    (h : ExecRand w c x m) (hp : p.Contains pc (c.assemble pc)) (T : ℕ) (cfg₀ : RandCfg r) :
    (∑' z : Data r × ℕ,
      m.eval z *
        (if z.2 ≤ T then
          (runRand w p (T - z.2) (.running ⟨pc + c.size, z.1⟩)).eval cfg₀
        else 0)) ≤
      (runRand w p T (.running ⟨pc, x⟩)).eval cfg₀ := by
  classical
  induction h generalizing pc T with
  | @op o x y ho =>
    rw [ProbComp.eval_pure, tsum_eq_single (y, 1) (fun z hz => by simp [PMF.pure_apply, hz])]
    simp only [PMF.pure_apply_self, one_mul, Code.size]
    by_cases h1 : 1 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      simp only [h1, ↓reduceIte, Nat.add_sub_cancel, runRand_succ,
        stepRand_op (s := ⟨pc, x⟩) hp.head ho, pure_bind, le_rfl]
    · simp [h1]
  | @rand dst src x hfit =>
    by_cases h1 : 1 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      have hrhs :
          (runRand w p (k + 1) (.running ⟨pc, x⟩)).eval cfg₀ =
            ∑' s : Fin (x.regs src + 1),
              (ProbComp.unifFin (x.regs src)).eval s *
                (runRand w p k (.running ⟨pc + 1, x.set dst s.val⟩)).eval cfg₀ := by
        rw [runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc]
        simp only [pure_bind, ProbComp.eval_bind, PMF.bind_apply]
      rw [hrhs, ProbComp.eval_bind, Cslib.Probability.PMF.tsum_bind_mul]
      refine tsum_le_tsum fun s => ?_
      rw [ProbComp.eval_pure, tsum_eq_single (x.set dst s.val, 1)
        (fun z hz => by simp [PMF.pure_apply, hz])]
      simp [h1, Code.size]
    · refine le_trans (le_of_eq ?_) zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      let m_rand : ProbComp (Data r × ℕ) :=
        do let k ← ProbComp.unifFin (x.regs src); pure (x.set dst k.val, 1)
      by_cases hz : z ∈ m_rand.eval.support
      · rw [ProbComp.support_eval] at hz
        obtain ⟨s, -, hs⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
        cases OracleComp.eq_of_mem_supportWith_pure hs
        simp [h1]
      · rw [(PMF.apply_eq_zero_iff m_rand.eval z).mpr hz, zero_mul]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa using hp.append_right
    calc
      (∑' z : Data r × ℕ,
          (do let z₁ ← m₁; let z₂ ← m₂ z₁.1; pure (z₂.1, z₁.2 + z₂.2)).eval z *
            (if z.2 ≤ T then
              (runRand w p (T - z.2) (.running ⟨pc + (c₁.size + c₂.size), z.1⟩)).eval cfg₀
            else 0))
        = ∑' z₁ : Data r × ℕ, m₁.eval z₁ *
            ∑' z₂ : Data r × ℕ, (m₂ z₁.1).eval z₂ *
              (if z₁.2 + z₂.2 ≤ T then
                (runRand w p (T - (z₁.2 + z₂.2))
                  (.running ⟨pc + c₁.size + c₂.size, z₂.1⟩)).eval cfg₀
              else 0) := by
          rw [ProbComp.eval_bind, Cslib.Probability.PMF.tsum_bind_mul]
          refine tsum_congr fun z₁ => congrArg (m₁.eval z₁ * ·) ?_
          rw [ProbComp.eval_bind, Cslib.Probability.PMF.tsum_bind_mul]
          refine tsum_congr fun z₂ => congrArg ((m₂ z₁.1).eval z₂ * ·) ?_
          rw [ProbComp.eval_pure, tsum_eq_single (z₂.1, z₁.2 + z₂.2)
            (fun z hz => by simp [PMF.pure_apply, hz])]
          simp [Nat.add_assoc]
      _ ≤ ∑' z₁ : Data r × ℕ, m₁.eval z₁ *
            (if z₁.2 ≤ T then
              (runRand w p (T - z₁.2) (.running ⟨pc + c₁.size, z₁.1⟩)).eval cfg₀
            else 0) := by
          refine tsum_le_tsum fun z₁ => ?_
          by_cases hz₁ : z₁ ∈ m₁.eval.support
          · refine mul_le_mul_right ?_ _
            by_cases hle₁ : z₁.2 ≤ T
            · simp only [hle₁, ↓reduceIte]
              refine le_trans (le_of_eq ?_)
                (ih₂ z₁ ((ProbComp.support_eval m₁).symm ▸ hz₁) hc₂ (T - z₁.2))
              refine tsum_congr fun z₂ => congrArg ((m₂ z₁.1).eval z₂ * ·) ?_
              have hiff : (z₁.2 + z₂.2 ≤ T) ↔ (z₂.2 ≤ T - z₁.2) := by omega
              simp only [hiff]
              split_ifs with hle₂
              · rw [Nat.sub_add_eq]
              · rfl
            · simp only [hle₁, ↓reduceIte]
              refine le_of_eq (tsum_eq_zero_iff.mpr fun z₂ => ?_)
              have hnot : ¬(z₁.2 + z₂.2 ≤ T) := by omega
              simp [hnot]
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]
      _ ≤ (runRand w p T (.running ⟨pc, x⟩)).eval cfg₀ := ih₁ hp.append_left T
  | @branch_pos cond pos neg x m hc _ ih =>
    rw [ProbComp.eval_map, Cslib.Probability.PMF.tsum_map_mul]
    by_cases h1 : 1 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      rw [eval_runRand_step_branch_pos hp.head hc]
      have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
      rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
      refine le_trans (le_of_eq ?_) (ih hc' k)
      refine tsum_congr fun z => congrArg (m.eval z * ·) ?_
      have hiff : (z.2 + 1 ≤ k + 1) ↔ (z.2 ≤ k) := by omega
      simp only [Code.size, hiff, Nat.add_sub_add_right]
      rw [show pc + (neg.size + pos.size + 2) = pc + neg.size + 2 + pos.size by omega]
    · refine le_trans (le_of_eq ?_) zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      have hnot : ¬(z.2 + 1 ≤ T) := by omega
      simp [hnot]
  | @branch_neg cond pos neg x m hc _ ih =>
    rw [ProbComp.eval_map, Cslib.Probability.PMF.tsum_map_mul]
    by_cases h2 : 2 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
      rw [show k + 2 = (k + 1) + 1 by omega, eval_runRand_step_branch_neg hp.head hc]
      have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
        simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
      refine le_trans (tsum_le_tsum fun z => ?_) (ih hp.cons_tail.append_left (k + 1))
      refine mul_le_mul_right ?_ _
      have hiff : (z.2 + 2 ≤ k + 1 + 1) ↔ (z.2 ≤ k) := by omega
      by_cases hzk : z.2 ≤ k
      · have hzk1 : z.2 ≤ k + 1 := by omega
        have hrem : k + 1 - z.2 = (k + 1 + 1 - (z.2 + 2)) + 1 := by omega
        simp only [Code.size, hiff.mpr hzk, hzk1, ↓reduceIte]
        rw [hrem, eval_runRand_step_jump hj]
        rw [show pc + (neg.size + pos.size + 2) = pc + neg.size + pos.size + 2 by omega]
      · have hnot1 : ¬(z.2 + 2 ≤ k + 1 + 1) := by omega
        simp only [hnot1, ↓reduceIte]
        exact zero_le
    · refine le_trans (le_of_eq ?_) zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      have hnot : ¬(z.2 + 2 ≤ T) := by omega
      simp [hnot]
  | @loop_exit cond body x hc =>
    rw [ProbComp.eval_pure, tsum_eq_single (x, 2) (fun z hz => by simp [PMF.pure_apply, hz])]
    simp only [PMF.pure_apply_self, one_mul, Code.size]
    by_cases h2 : 2 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
      rw [show k + 2 = (k + 1) + 1 by omega, eval_runRand_step_branch_neg hp.head hc,
        eval_runRand_step_jump hp.cons_tail.head]
      simp [show 2 ≤ k + 1 + 1 by omega, show k + 1 + 1 - 2 = k by omega, Nat.add_assoc]
    · simp [h2]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    by_cases h2 : 2 ≤ T
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
      rw [show k + 2 = (k + 1) + 1 by omega, eval_runRand_step_branch_pos hp.head hc]
      have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
        simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
      have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
        simpa using hp.cons_tail.cons_tail.append_right.head
      calc
        (∑' z : Data r × ℕ,
            (do let z₁ ← mb; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2)).eval z *
              (if z.2 ≤ k + 1 + 1 then
                (runRand w p (k + 1 + 1 - z.2)
                  (.running ⟨pc + (Code.loop cond body).size, z.1⟩)).eval cfg₀
              else 0))
          = ∑' z₁ : Data r × ℕ, mb.eval z₁ *
              ∑' z₂ : Data r × ℕ, (ml z₁.1).eval z₂ *
                (if z₁.2 + z₂.2 + 2 ≤ k + 1 + 1 then
                  (runRand w p (k + 1 + 1 - (z₁.2 + z₂.2 + 2))
                    (.running ⟨pc + (Code.loop cond body).size, z₂.1⟩)).eval cfg₀
                else 0) := by
            rw [ProbComp.eval_bind, Cslib.Probability.PMF.tsum_bind_mul]
            refine tsum_congr fun z₁ => congrArg (mb.eval z₁ * ·) ?_
            rw [ProbComp.eval_bind, Cslib.Probability.PMF.tsum_bind_mul]
            refine tsum_congr fun z₂ => congrArg ((ml z₁.1).eval z₂ * ·) ?_
            rw [ProbComp.eval_pure, tsum_eq_single (z₂.1, z₁.2 + z₂.2 + 2)
              (fun z hz => by simp [PMF.pure_apply, hz])]
            simp
        _ ≤ ∑' z₁ : Data r × ℕ, mb.eval z₁ *
              (if z₁.2 ≤ k + 1 then
                (runRand w p (k + 1 - z₁.2) (.running ⟨pc + 2 + body.size, z₁.1⟩)).eval cfg₀
              else 0) := by
            refine tsum_le_tsum fun z₁ => ?_
            by_cases hz₁ : z₁ ∈ mb.eval.support
            · refine mul_le_mul_right ?_ _
              by_cases hle₁ : z₁.2 ≤ k
              · have hle₁' : z₁.2 ≤ k + 1 := by omega
                have hrem : k + 1 - z₁.2 = (k - z₁.2) + 1 := by omega
                simp only [hle₁', ↓reduceIte]
                rw [hrem, eval_runRand_step_jump hj]
                refine le_trans (tsum_le_tsum fun z₂ => ?_)
                  (ihl z₁ ((ProbComp.support_eval mb).symm ▸ hz₁) hp (k - z₁.2))
                refine mul_le_mul_right ?_ _
                have hiff : (z₁.2 + z₂.2 + 2 ≤ k + 1 + 1) ↔ (z₂.2 ≤ k - z₁.2) := by omega
                simp only [hiff]
                split_ifs with hle₂
                · have hsub : k + 1 + 1 - (z₁.2 + z₂.2 + 2) = k - z₁.2 - z₂.2 := by omega
                  rw [hsub]
                · exact le_rfl
              · refine le_trans (le_of_eq ?_) zero_le
                refine tsum_eq_zero_iff.mpr fun z₂ => ?_
                have hnot : ¬(z₁.2 + z₂.2 + 2 ≤ k + 1 + 1) := by omega
                simp [hnot]
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul]
        _ ≤ (runRand w p (k + 1) (.running ⟨pc + 2, x⟩)).eval cfg₀ :=
            ihb hbody_contains (k + 1)
    · refine le_trans (le_of_eq ?_) zero_le
      refine tsum_eq_zero_iff.mpr fun z => ?_
      by_cases hz : z ∈
          (do let z₁ ← mb; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2)).eval.support
      · rw [ProbComp.support_eval] at hz
        obtain ⟨z₁, -, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
        obtain ⟨z₂, -, hfin⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hfin
        have hnot : ¬(z₁.2 + z₂.2 + 2 ≤ T) := by omega
        simp [hnot]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul]

/-- **Partial-horizon flat-program halting lower bound (`toOuterMeasure_le_evalRand_program`).**
For any `ExecRand w c x m`, every fast branch `z = (y, n)` with `n ≤ B` halts at
`RandCfg.halted (y.regs out) y` in `evalRand w (c.program out) (B + 1) ⟨0, x⟩`. -/
theorem ExecRand.toOuterMeasure_le_evalRand_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (out : Fin r) (B_hor : ℕ) (y : Data r) :
    m.eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ B_hor} ≤
      evalRand w (c.program out) (B_hor + 1) ⟨0, x⟩ (.halted (y.regs out) y) := by
  classical
  have hasm := h.tsum_le_eval_runRand_assemble
    (Program.Contains.self (c.program out)).append_left (B_hor + 1) (.halted (y.regs out) y)
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  rw [PMF.toOuterMeasure_apply]
  refine le_trans (tsum_le_tsum fun z => ?_) hasm
  by_cases hz : z ∈ {z : Data r × ℕ | z.1 = y ∧ z.2 ≤ B_hor}
  · rcases hz with ⟨rfl, hle⟩
    have hle1 : z.2 ≤ B_hor + 1 := by omega
    have hrem : B_hor + 1 - z.2 = (B_hor - z.2) + 1 := by omega
    have hm : z ∈ {z' : Data r × ℕ | z'.1 = z.1 ∧ z'.2 ≤ B_hor} := ⟨rfl, hle⟩
    rw [Set.indicator_of_mem hm]
    simp only [hle1, ↓reduceIte]
    rw [hrem, runRand_succ, stepRand_halt (s := ⟨0 + c.size, z.1⟩) hhalt, pure_bind,
      runRand_halted, ProbComp.eval_pure, PMF.pure_apply_self, mul_one]
  · rw [Set.indicator_of_notMem hz]
    exact zero_le

/-- **Event-level partial-horizon flat-program halting bound (`one_sub_le_evalRand_program`).**
If `m` satisfies postcondition `Q z.1` on every supported branch and exceeds `B_hor` steps with
probability at most `δ`, then `evalRand w (c.program out) (B_hor + 1) ⟨0, x⟩` halts in a state
satisfying `Q` with probability at least `1 - δ`. -/
theorem ExecRand.one_sub_le_evalRand_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} {Q : Data r → Prop} {δ : ℝ≥0∞}
    (h : ExecRand w c x m) (out : Fin r) (B_hor : ℕ)
    (hQ : ∀ z ∈ m.eval.support, Q z.1)
    (hfail : m.eval.toOuterMeasure {z | B_hor < z.2} ≤ δ) :
    1 - δ ≤ (evalRand w (c.program out) (B_hor + 1) ⟨0, x⟩).toOuterMeasure
      {cfg | ∃ y, cfg = .halted (y.regs out) y ∧ Q y} := by
  classical
  have hfast : 1 - δ ≤ m.eval.toOuterMeasure {z | Q z.1 ∧ z.2 ≤ B_hor} := by
    have hcompl : 1 - δ ≤ m.eval.toOuterMeasure {z : Data r × ℕ | B_hor < z.2}ᶜ :=
      Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl m.eval _ hfail
    refine hcompl.trans ?_
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun z => ?_
    by_cases hz : z ∈ m.eval.support
    · by_cases hlt : B_hor < z.2
      · have hn1 : z ∉ ({z : Data r × ℕ | B_hor < z.2}ᶜ : Set (Data r × ℕ)) := by simp [hlt]
        rw [Set.indicator_of_notMem hn1]
        exact zero_le
      · have hm1 : z ∈ ({z : Data r × ℕ | B_hor < z.2}ᶜ : Set (Data r × ℕ)) := by simp [hlt]
        have hm2 : z ∈ {z : Data r × ℕ | Q z.1 ∧ z.2 ≤ B_hor} := ⟨hQ z hz, Nat.le_of_not_lt hlt⟩
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
    · have hz0 : m.eval z = 0 := (PMF.apply_eq_zero_iff _ _).mpr hz
      simp [Set.indicator_apply, hz0]
  refine hfast.trans ?_
  have hpart :
      m.eval.toOuterMeasure {z | Q z.1 ∧ z.2 ≤ B_hor} =
        ∑' y : Data r,
          if Q y then m.eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ B_hor} else 0 := by
    rw [PMF.toOuterMeasure_apply]
    have hinner : ∀ y : Data r,
        (if Q y then m.eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ B_hor} else 0) =
          ∑' z : Data r × ℕ,
            if z.1 = y ∧ Q y ∧ z.2 ≤ B_hor then m.eval z else 0 := by
      intro y
      by_cases hQy : Q y
      · simp only [hQy, ↓reduceIte, true_and, PMF.toOuterMeasure_apply]
        refine tsum_congr fun z => ?_
        by_cases heq : z.1 = y ∧ z.2 ≤ B_hor <;> simp [heq]
      · simp [hQy]
    simp_rw [hinner]
    rw [tsum_comm]
    refine tsum_congr fun z => ?_
    rw [tsum_eq_single z.1 (fun y hy => by simp [hy.symm])]
    by_cases hzQ : Q z.1 ∧ z.2 ≤ B_hor <;> simp [hzQ]
  rw [hpart, PMF.toOuterMeasure_apply]
  have hinj : Function.Injective (fun y : Data r => RandCfg.halted (y.regs out) y) := by
    intro y₁ y₂ heq
    exact (RandCfg.halted.inj heq).2
  calc
    (∑' y : Data r,
        if Q y then m.eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ B_hor} else 0)
      ≤ ∑' y : Data r,
          Set.indicator {cfg | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'}
            (evalRand w (c.program out) (B_hor + 1) ⟨0, x⟩) (.halted (y.regs out) y) := by
        refine tsum_le_tsum fun y => ?_
        by_cases hQy : Q y
        · simp only [hQy, ↓reduceIte]
          have hmem_cfg :
              RandCfg.halted (y.regs out) y ∈
                {cfg : RandCfg r | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'} :=
            ⟨y, rfl, hQy⟩
          rw [Set.indicator_of_mem hmem_cfg]
          exact h.toOuterMeasure_le_evalRand_program out B_hor y
        · simp [hQy]
    _ ≤ ∑' cfg : RandCfg r,
          Set.indicator {cfg | ∃ y', cfg = .halted (y'.regs out) y' ∧ Q y'}
            (evalRand w (c.program out) (B_hor + 1) ⟨0, x⟩) cfg :=
        tsum_comp_le_tsum_of_injective hinj _

end PartialHorizon

end Cslib.WordRAM

namespace Cslib.DataStructure.WordRAM.Randomized

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

universe u v z

/-- Trajectory outcome across an oblivious operation sequence `ops : List D.Op`, bundling the
current coupled `(seed, state, data)` triple, the accumulated input-output transcript, and the
maximum single-operation body instruction count `maxSteps` observed across all executed steps. -/
structure WhpSeqOutcome (Seed : Type) (D : StateTransitionSpec.{u, v, z}) (r : ℕ) :
    Type (max u v z) where
  /-- Current coupled `(seed, state, data)` configuration. -/
  current : CoupledState Seed D.State r
  /-- Accumulated input-output transcript of operations executed so far. -/
  transcript : List (Sigma D.Result)
  /-- Maximum single-operation executed instruction count across all steps so far. -/
  maxSteps : ℕ

/-- Initialize a `WhpSeqOutcome` from a `CoupledState` with empty transcript and `maxSteps = 0`. -/
@[expose] def WhpSeqOutcome.ofCoupled {Seed : Type} {D : StateTransitionSpec.{u, v, z}} {r : ℕ}
    (t : CoupledState Seed D.State r) : WhpSeqOutcome Seed D r where
  current := t
  transcript := []
  maxSteps := 0

/-- Append one operation outcome `(q, a, n)` to `tr : WhpSeqOutcome`. -/
@[expose] def WhpSeqOutcome.appendStep {Seed : Type} {D : StateTransitionSpec.{u, v, z}} {r : ℕ}
    (tr : WhpSeqOutcome Seed D r) (o : D.Op) (q : CoupledState Seed D.State r)
    (a : D.Result o) (n : ℕ) : WhpSeqOutcome Seed D r where
  current := q
  transcript := tr.transcript ++ [⟨o, a⟩]
  maxSteps := max tr.maxSteps n

/-- Reusable Word-RAM subroutine implementation certificate for a randomized data structure `P`
realizing a relational specification `D` at word width `w`, base address `base`, runtime parameters
`params`, and initial abstract state `s₀`, where every operation executes fault-free within a
**deterministic worst-case** body instruction budget `worstCaseTime : ℕ` with probability at least
`1 - failureProb`. -/
structure HighProbStateTransitionImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init) (D : StateTransitionSpec.{u, v, z})
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) : Type (max u v z 1) where
  /-- Latent random seed type (`Unit` when no persistent seed is needed). -/
  Seed : Type
  /-- Reference distribution over latent seeds. -/
  seedLaw : PMF Seed
  /-- Marginal density slack factor (`1` when the seed distribution is exact). -/
  seedSlack : ℝ≥0∞ := 1
  /-- The marginal density slack factor is finite. -/
  seedSlack_ne_top : seedSlack ≠ ⊤ := by simp
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Worst-case instruction bound for `P.allocSpan`. -/
  spanTime : ℕ
  /-- Worst-case instruction bound for `P.initSetup`. -/
  setupTime : ℕ
  /-- Worst-case `rand`-call bound for `P.initSetup`. -/
  setupRandCalls : ℕ := setupTime
  /-- Deterministic worst-case body instruction bound per operation on the high-probability event.
  -/
  worstCaseTime : ℕ
  /-- Upper bound on the probability that a single admissible operation exceeds `worstCaseTime`
  executed body instructions. -/
  failureProb : ℝ≥0∞
  /-- Deterministic oblivious ghost state type (`Unit` when unused). -/
  Ghost : Type := Unit
  /-- Initial deterministic ghost state at initialization (`s₀`). -/
  ghostInit : Ghost
  /-- Deterministic ghost-state update on operation `o`. -/
  ghostStep : Ghost → D.Op → Ghost
  /-- Ghost- and seed-indexed representation invariant linking `Ghost`, `Seed`, `D.State`, and
  `Data r_ds`. -/
  ghostRep : Ghost → Seed → D.State → Data r_ds → Prop
  /-- Standalone register encoding for argument delivery. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Partial argument-matching predicate for inline callers (refined by `encode`). -/
  argMatch : D.Op → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  /-- Represented configurations are word-bounded. -/
  bounded : ∀ {g θ s x}, ghostRep g θ s x → x.Bounded w
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Full standalone argument delivery satisfies `argMatch`. -/
  encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  /-- `ghostRep` depends only on persistent registers (`P.input i = false`) and
  `[base, base + space)`. -/
  rep_supported : ∀ {g θ s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    x'.Bounded w → ghostRep g θ s x → ghostRep g θ s x'
  /-- Distinctness of registers used by `zeroFillCode` relative to `baseReg` and `frontierReg`. -/
  clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup
  /-- Initialization parameter registers are not overwritten by `zeroFillCode`. -/
  params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg]
  /-- `P.incCur` increments `P.curReg` by `1` when `P.oneReg = 1` and the sum fits in `w` bits. -/
  incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
    P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1))
  /-- Execution of `P.allocSpan`: records `baseReg = base` and advances `frontierReg`. -/
  span_exec : ∀ {x : Data r_ds},
    x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
    ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
      x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
      (∀ j, x₁.regs (P.initParams j) = params j)
  /-- Worst-case bounded randomized execution of `P.initSetup` once `[base, base + space)` holds
  zeros, producing a coupled distribution `ν₀ : PMF (Seed × Data r_ds)` within `setupTime`
  deterministic worst-case instructions and `setupRandCalls` `rand` calls. -/
  setup_exec : ∀ {x₁ : Data r_ds},
    x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
    (∀ j, x₁.regs (P.initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
    ∃ (m₀ : ProbComp (Data r_ds × ℕ)) (ν₀ : PMF (Seed × Data r_ds)),
      ExecRand w P.initSetup x₁ m₀ ∧
      OracleComp.IsQueryBounded m₀ setupRandCalls ∧
      (∀ z ∈ m₀.support, z.2 ≤ setupTime) ∧
      ν₀.map Prod.snd = (Prod.fst <$> m₀).eval ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + space ∧
        ghostRep ghostInit p.1 s₀ p.2 ∧
        Modifies (Block.mk base space).footprint x₁.mem p.2.mem
  /-- Whether `step_exec` requires `ν` to be supported on a single abstract state `s : D.State`
  (`False` by default; `True` for oblivious functional certificates built via `ofFn`). -/
  singleState : Prop := False
  /-- Coupled one-step execution of `P.code` for any admissible operation `o` from a coupled
  distribution `ν : PMF (CoupledState Seed D.State r_ds)` with seed marginal bounded by
  `seedSlack * seedLaw`: produces a structured execution `ExecRand w P.code t.data (m_step t)` and
  coupled step-count kernel `μ_step` matching `(m_step t).eval`, realizing `D.step`, `decode`,
  `ghostRep (ghostStep g o)`, and `Modifies` on every branch, preserving the seed marginal and
  single-state invariant, and bounding `(ν.bind μ_step).toOuterMeasure {p | worstCaseTime < p.2}`
  by `failureProb`. -/
  step_exec : ∀ (g : Ghost) (o : D.Op) (ν : PMF (CoupledState Seed D.State r_ds)),
    (singleState → ∃ s, ∀ t ∈ ν.support, t.state = s) →
    (∀ θ, (ν.map CoupledState.seed) θ ≤ seedSlack * seedLaw θ) →
    (∀ t ∈ ν.support,
      D.valid t.state o ∧ ghostRep g t.seed t.state t.data ∧ argMatch o t.data.regs) →
    ∃ (m_step : CoupledState Seed D.State r_ds → ProbComp (Data r_ds × ℕ))
      (μ_step : CoupledState Seed D.State r_ds → PMF (CoupledState Seed D.State r_ds × ℕ)),
      (∀ t ∈ ν.support,
        ExecRand w P.code t.data (m_step t) ∧
        (μ_step t).map (fun p => (p.1.data, p.2)) = (m_step t).eval ∧
        ∀ p ∈ (μ_step t).support,
          ∃ a : D.Result o,
            D.step t.state o p.1.state a ∧
            decode o p.1.data.regs = some a ∧
            ghostRep (ghostStep g o) p.1.seed p.1.state p.1.data ∧
            Modifies (Block.mk base space).footprint t.data.mem p.1.data.mem) ∧
      (∀ θ', (((ν.bind μ_step).map Prod.fst).map CoupledState.seed) θ' ≤ seedSlack * seedLaw θ') ∧
      (singleState → ∃ s', ∀ p ∈ (ν.bind μ_step).support, p.1.state = s') ∧
      (ν.bind μ_step).toOuterMeasure {p | worstCaseTime < p.2} ≤ failureProb

/-- Existentially projected representation invariant `∃ g, C.ghostRep g θ s x`. -/
@[expose] def HighProbStateTransitionImpl.rep {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : HighProbStateTransitionImpl P D w base params s₀)
    (θ : C.Seed) (s : D.State) (x : Data r_ds) : Prop :=
  ∃ g : C.Ghost, C.ghostRep g θ s x

/-- Deterministic ghost state reached after oblivious operation prefix `ops`. -/
@[expose] def HighProbStateTransitionImpl.ghostRun {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : HighProbStateTransitionImpl P D w base params s₀)
    (g : C.Ghost) (ops : List D.Op) : C.Ghost :=
  ops.foldl C.ghostStep g

end Cslib.DataStructure.WordRAM.Randomized

namespace Cslib.DataStructure.WordRAM.StateTransitionImpl

open Cslib.WordRAM
open Cslib.DataStructure.WordRAM.Randomized (CoupledState HighProbStateTransitionImpl)
open scoped ENNReal

universe u v z

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Canonical embedding of an unamortized deterministic `StateTransitionImpl` (`potential = 0` and
uniform per-operation step bound `worstCaseTime`) into `HighProbStateTransitionImpl` with
`failureProb = 0`. -/
noncomputable def toHighProb (C : StateTransitionImpl P D w base params s₀)
    (worstCaseTime : ℕ)
    (hpot : ∀ x, C.potential x = 0)
    (hcharge : ∀ {s o}, D.valid s o → C.charge s o ≤ worstCaseTime) :
    HighProbStateTransitionImpl P D w base params s₀ where
  Seed := Unit
  seedLaw := PMF.pure ()
  seedSlack := 1
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  setupRandCalls := 0
  worstCaseTime := worstCaseTime
  failureProb := 0
  Ghost := Unit
  ghostInit := ()
  ghostStep _ _ := ()
  ghostRep _ _ s x := C.rep s x
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval := C.incCur_eval
  span_exec := C.span_exec
  setup_exec hx₁ hb hfr hpar hz := by
    obtain ⟨y, ⟨n₀, hn₀, he⟩, hfr', hrep, _, hmod⟩ := C.setup_exec hx₁ hb hfr hpar hz
    refine ⟨pure (y, n₀), PMF.pure ((), y), he.execRand, .pure _ 0, ?_, ?_, ?_, ?_⟩
    · intro z hz
      cases OracleComp.eq_of_mem_supportWith_pure hz
      exact hn₀
    · simp [ProbComp.eval_pure]
    · intro θ
      cases θ
      simp
    · intro p hp
      rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hfr', hrep, hmod⟩
  step_exec _ o ν _ _ hsupp := by
    classical
    let hasInv : CoupledState Unit D.State r_ds → Prop := fun t =>
      D.valid t.state o ∧ C.rep t.state t.data ∧ C.argMatch o t.data.regs
    let y : CoupledState Unit D.State r_ds → Data r_ds := fun t =>
      if ht : hasInv t then Classical.choose (C.step_exec o ht.2.1 ht.1 ht.2.2) else t.data
    let s' : CoupledState Unit D.State r_ds → D.State := fun t =>
      if ht : hasInv t then
        Classical.choose (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2))
      else t.state
    let n : CoupledState Unit D.State r_ds → ℕ := fun t =>
      if ht : hasInv t then
        Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2))))
      else 0
    refine ⟨fun t => pure (y t, n t), fun t => PMF.pure (⟨(), s' t, y t⟩, n t), ?_, ?_, nofun, ?_⟩
    · intro t ht_mem
      have ht : hasInv t := hsupp t ht_mem
      have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2))))
      let a := Classical.choose (Classical.choose_spec
        (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2)))
      rcases hspec with ⟨he, hstep, hdec, hrep', hmod, _⟩
      have hy_eq : y t = Classical.choose (C.step_exec o ht.2.1 ht.1 ht.2.2) := by simp [y, ht]
      have hs'_eq : s' t = Classical.choose
          (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2)) := by simp [s', ht]
      have hn_eq : n t = Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2)))) := by simp [n, ht]
      refine ⟨by simpa only [hy_eq, hn_eq] using he.execRand, by simp [ProbComp.eval_pure], ?_⟩
      intro p hp
      rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨a, by simpa only [hs'_eq] using hstep,
        by simpa only [hy_eq] using hdec,
        by simpa only [hs'_eq, hy_eq] using hrep',
        by simpa only [hy_eq] using hmod⟩
    · intro θ'
      cases θ'
      rw [PMF.map_comp, PMF.map_bind]
      simp
    · refine le_of_eq ?_
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro p hp hlt
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨t, ht_mem, hp_pure⟩ := hp
      rw [PMF.support_pure, Set.mem_singleton_iff] at hp_pure
      subst hp_pure
      have ht : hasInv t := hsupp t ht_mem
      have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2))))
      rcases hspec with ⟨_, _, _, _, _, hpot_ineq⟩
      have hn_eq : n t = Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (C.step_exec o ht.2.1 ht.1 ht.2.2)))) := by simp [n, ht]
      have hpot1 : C.potential (Classical.choose (C.step_exec o ht.2.1 ht.1 ht.2.2)) = 0 := hpot _
      have hpot2 : C.potential t.data = 0 := hpot _
      have hc_le : C.charge t.state o ≤ worstCaseTime := hcharge ht.1
      change worstCaseTime < n t at hlt
      omega

end Cslib.DataStructure.WordRAM.StateTransitionImpl

namespace Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

universe u v z

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Deterministic worst-case body instruction bound for `P.initFresh` (`spanTime + setupTime`). -/
@[expose] def initTime (C : HighProbStateTransitionImpl P D w base params s₀) : ℕ :=
  C.spanTime + C.setupTime

/-- Deterministic worst-case body instruction bound for `P.initClear`
(`initTime + (4 * space + 6)`). -/
@[expose] def initClearTime (C : HighProbStateTransitionImpl P D w base params s₀) : ℕ :=
  C.initTime + (4 * C.space + 6)

/-- Construct a `HighProbStateTransitionImpl` certificate with deterministic oblivious ghost state
`Ghost` for a functional specification `[D.HasStepFn stepFn]`. -/
noncomputable abbrev ofFnGhost {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn stepFn]
    (Ghost : Type) (ghostInit : Ghost) (ghostStep : Ghost → D.Op → Ghost)
    (Seed : Type) (seedLaw : PMF Seed) (seedSlack : ℝ≥0∞ := 1)
    (seedSlack_ne_top : seedSlack ≠ ⊤ := by simp)
    (space spanTime setupTime setupRandCalls worstCaseTime : ℕ)
    (failureProb : ℝ≥0∞)
    (ghostRep : Ghost → Seed → D.State → Data r_ds → Prop)
    (encode : D.Op → Fin r_ds → ℕ)
    (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {g θ s x}, ghostRep g θ s x → x.Bounded w)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (rep_supported : ∀ {g θ s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      x'.Bounded w → ghostRep g θ s x → ghostRep g θ s x')
    (clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    (span_exec : ∀ {x : Data r_ds},
      x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
      ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
        x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
        (∀ j, x₁.regs (P.initParams j) = params j))
    (setup_exec : ∀ {x₁ : Data r_ds},
      x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
      (∀ j, x₁.regs (P.initParams j) = params j) →
      (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
      ∃ (m₀ : ProbComp (Data r_ds × ℕ)) (ν₀ : PMF (Seed × Data r_ds)),
        ExecRand w P.initSetup x₁ m₀ ∧
        OracleComp.IsQueryBounded m₀ setupRandCalls ∧
        (∀ z ∈ m₀.support, z.2 ≤ setupTime) ∧
        ν₀.map Prod.snd = (Prod.fst <$> m₀).eval ∧
        (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
        ∀ p ∈ ν₀.support,
          p.2.regs P.frontierReg = base + space ∧
          ghostRep ghostInit p.1 s₀ p.2 ∧
          Modifies (Block.mk base space).footprint x₁.mem p.2.mem)
    (step_exec : ∀ {s : D.State} (g : Ghost) (o : D.Op) (ν : PMF (Seed × Data r_ds)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, ghostRep g p.1 s p.2 ∧ argMatch o p.2.regs) →
      ∃ (m_step : Seed × Data r_ds → ProbComp (Data r_ds × ℕ))
        (μ_step : Seed × Data r_ds → PMF ((Seed × Data r_ds) × ℕ)),
        (∀ p ∈ ν.support,
          ExecRand w P.code p.2 (m_step p) ∧
          (μ_step p).map (fun q => (q.1.2, q.2)) = (m_step p).eval ∧
          ∀ q ∈ (μ_step p).support,
            decode o q.1.2.regs = some (D.stepFn s o).2 ∧
            ghostRep (ghostStep g o) q.1.1 (D.stepFn s o).1 q.1.2 ∧
            Modifies (Block.mk base space).footprint p.2.mem q.1.2.mem) ∧
        (∀ θ', (((ν.bind μ_step).map Prod.fst).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (ν.bind μ_step).toOuterMeasure {q | worstCaseTime < q.2} ≤ failureProb) :
    HighProbStateTransitionImpl P D w base params s₀ where
  Seed := Seed
  seedLaw := seedLaw
  seedSlack := seedSlack
  seedSlack_ne_top := seedSlack_ne_top
  space := space
  spanTime := spanTime
  setupTime := setupTime
  setupRandCalls := setupRandCalls
  worstCaseTime := worstCaseTime
  failureProb := failureProb
  Ghost := Ghost
  ghostInit := ghostInit
  ghostStep := ghostStep
  ghostRep := ghostRep
  encode := encode
  argMatch := argMatch
  decode := decode
  singleState := True
  bounded := bounded
  arguments_fit := arguments_fit
  encode_matches := encode_matches
  rep_supported := rep_supported
  clear_nodup := clear_nodup
  params_not_clear := params_not_clear
  incCur_eval := incCur_eval
  span_exec := span_exec
  setup_exec := setup_exec
  step_exec g o ν hsingle hseed hsupp := by
    obtain ⟨s, hs⟩ := hsingle trivial
    obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
    have hv : D.valid s o := hs t₀ ht₀ ▸ (hsupp t₀ ht₀).1
    let proj : CoupledState Seed D.State r_ds → Seed × Data r_ds := fun t => (t.seed, t.data)
    let ν_det : PMF (Seed × Data r_ds) := ν.map proj
    have hseed_det : ∀ θ, (ν_det.map Prod.fst) θ ≤ seedSlack * seedLaw θ := by
      intro θ
      rw [PMF.map_comp]
      exact hseed θ
    have hsupp_det : ∀ p ∈ ν_det.support, ghostRep g p.1 s p.2 ∧ argMatch o p.2.regs := by
      intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      obtain ⟨_, hrep, harg⟩ := hsupp t ht
      exact ⟨hs t ht ▸ hrep, harg⟩
    obtain ⟨m_det, μ_det, hstep_det, hseed_det', hfail_det⟩ :=
      step_exec g o ν_det hv hseed_det hsupp_det
    let liftOut : (Seed × Data r_ds) × ℕ → CoupledState Seed D.State r_ds × ℕ :=
      fun q => (⟨q.1.1, (D.stepFn s o).1, q.1.2⟩, q.2)
    let m_step : CoupledState Seed D.State r_ds → ProbComp (Data r_ds × ℕ) :=
      fun t => m_det (proj t)
    let μ_step : CoupledState Seed D.State r_ds → PMF (CoupledState Seed D.State r_ds × ℕ) :=
      fun t => (μ_det (proj t)).map liftOut
    have hbind_eq : ν.bind μ_step = (ν_det.bind μ_det).map liftOut := by
      dsimp only [ν_det, μ_step]
      rw [PMF.bind_map, PMF.map_bind]
      rfl
    refine ⟨m_step, μ_step, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hp_det : proj t ∈ ν_det.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨hm_t, heval_t, hq_det⟩ := hstep_det (proj t) hp_det
      refine ⟨hm_t, ?_, ?_⟩
      · dsimp only [μ_step, liftOut]
        rw [PMF.map_comp]
        exact heval_t
      · intro p hp
        dsimp only [μ_step] at hp
        rw [PMF.mem_support_map_iff] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        obtain ⟨hdec, hrep', hmod⟩ := hq_det q hq
        refine ⟨(D.stepFn s o).2, ?_, hdec, hrep', hmod⟩
        rw [hs t ht]
        exact D.step_stepFn s o
    · intro θ'
      rw [hbind_eq, PMF.map_comp, PMF.map_comp]
      have hcomp :
          ((CoupledState.seed ∘ Prod.fst) ∘ liftOut) = (Prod.fst ∘ Prod.fst) := rfl
      rw [hcomp, ← PMF.map_comp]
      exact hseed_det' θ'
    · intro _
      refine ⟨(D.stepFn s o).1, fun p hp => ?_⟩
      rw [hbind_eq, PMF.mem_support_map_iff] at hp
      obtain ⟨_, _, rfl⟩ := hp
      rfl
    · rw [hbind_eq, PMF.toOuterMeasure_map_apply]
      exact hfail_det

/-- Construct a `HighProbStateTransitionImpl` certificate for a functional specification
`[D.HasStepFn stepFn]` without auxiliary ghost state (`Ghost = Unit`). -/
noncomputable abbrev ofFn {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn stepFn]
    (Seed : Type) (seedLaw : PMF Seed) (seedSlack : ℝ≥0∞ := 1)
    (seedSlack_ne_top : seedSlack ≠ ⊤ := by simp)
    (space spanTime setupTime setupRandCalls worstCaseTime : ℕ)
    (failureProb : ℝ≥0∞)
    (rep : Seed → D.State → Data r_ds → Prop)
    (encode : D.Op → Fin r_ds → ℕ)
    (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {θ s x}, rep θ s x → x.Bounded w)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (rep_supported : ∀ {θ s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      x'.Bounded w → rep θ s x → rep θ s x')
    (clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    (span_exec : ∀ {x : Data r_ds},
      x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
      ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
        x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
        (∀ j, x₁.regs (P.initParams j) = params j))
    (setup_exec : ∀ {x₁ : Data r_ds},
      x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
      (∀ j, x₁.regs (P.initParams j) = params j) →
      (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
      ∃ (m₀ : ProbComp (Data r_ds × ℕ)) (ν₀ : PMF (Seed × Data r_ds)),
        ExecRand w P.initSetup x₁ m₀ ∧
        OracleComp.IsQueryBounded m₀ setupRandCalls ∧
        (∀ z ∈ m₀.support, z.2 ≤ setupTime) ∧
        ν₀.map Prod.snd = (Prod.fst <$> m₀).eval ∧
        (∀ θ, (ν₀.map Prod.fst) θ ≤ seedSlack * seedLaw θ) ∧
        ∀ p ∈ ν₀.support,
          p.2.regs P.frontierReg = base + space ∧
          rep p.1 s₀ p.2 ∧
          Modifies (Block.mk base space).footprint x₁.mem p.2.mem)
    (step_exec : ∀ {s : D.State} (o : D.Op) (ν : PMF (Seed × Data r_ds)),
      D.valid s o →
      (∀ θ, (ν.map Prod.fst) θ ≤ seedSlack * seedLaw θ) →
      (∀ p ∈ ν.support, rep p.1 s p.2 ∧ argMatch o p.2.regs) →
      ∃ (m_step : Seed × Data r_ds → ProbComp (Data r_ds × ℕ))
        (μ_step : Seed × Data r_ds → PMF ((Seed × Data r_ds) × ℕ)),
        (∀ p ∈ ν.support,
          ExecRand w P.code p.2 (m_step p) ∧
          (μ_step p).map (fun q => (q.1.2, q.2)) = (m_step p).eval ∧
          ∀ q ∈ (μ_step p).support,
            decode o q.1.2.regs = some (D.stepFn s o).2 ∧
            rep q.1.1 (D.stepFn s o).1 q.1.2 ∧
            Modifies (Block.mk base space).footprint p.2.mem q.1.2.mem) ∧
        (∀ θ', (((ν.bind μ_step).map Prod.fst).map Prod.fst) θ' ≤ seedSlack * seedLaw θ') ∧
        (ν.bind μ_step).toOuterMeasure {q | worstCaseTime < q.2} ≤ failureProb) :
    HighProbStateTransitionImpl P D w base params s₀ :=
  ofFnGhost Unit () (fun _ _ => ()) Seed seedLaw seedSlack seedSlack_ne_top
    space spanTime setupTime setupRandCalls worstCaseTime failureProb
    (fun _ => rep) encode argMatch decode bounded arguments_fit encode_matches
    rep_supported clear_nodup params_not_clear incCur_eval span_exec setup_exec
    (fun _ => step_exec)

/-- Single-state specialization of `step_exec` when `[D.HasStepFn stepFn]`. -/
theorem step_exec_ofFn (C : HighProbStateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {s : D.State} (g : C.Ghost) (o : D.Op) (ν : PMF (C.Seed × Data r_ds))
    (hv : D.valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hsupp : ∀ p ∈ ν.support, C.ghostRep g p.1 s p.2 ∧ C.argMatch o p.2.regs) :
    ∃ (m_step : C.Seed × Data r_ds → ProbComp (Data r_ds × ℕ))
      (μ_step : C.Seed × Data r_ds → PMF ((C.Seed × Data r_ds) × ℕ)),
      (∀ p ∈ ν.support,
        ExecRand w P.code p.2 (m_step p) ∧
        (μ_step p).map (fun q => (q.1.2, q.2)) = (m_step p).eval ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.1.2.regs = some (D.stepFn s o).2 ∧
          C.ghostRep (C.ghostStep g o) q.1.1 (D.stepFn s o).1 q.1.2 ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.1.2.mem) ∧
      (∀ θ', (((ν.bind μ_step).map Prod.fst).map Prod.fst) θ' ≤ C.seedSlack * C.seedLaw θ') ∧
      (ν.bind μ_step).toOuterMeasure {q | C.worstCaseTime < q.2} ≤ C.failureProb := by
  let lift : C.Seed × Data r_ds → CoupledState C.Seed D.State r_ds := fun p => ⟨p.1, s, p.2⟩
  let ν_rel : PMF (CoupledState C.Seed D.State r_ds) := ν.map lift
  have hsingle : C.singleState → ∃ s', ∀ t ∈ ν_rel.support, t.state = s' := by
    intro _
    refine ⟨s, fun t ht => ?_⟩
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨_, _, rfl⟩ := ht
    rfl
  have hseed_rel : ∀ θ, (ν_rel.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ
    rw [PMF.map_comp]
    exact hseed θ
  have hsupp_rel : ∀ t ∈ ν_rel.support,
      D.valid t.state o ∧ C.ghostRep g t.seed t.state t.data ∧ C.argMatch o t.data.regs := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨hv, (hsupp p hp).1, (hsupp p hp).2⟩
  obtain ⟨m_rel, μ_rel, hstep_rel, hseed_rel', _, hfail_rel⟩ :=
    C.step_exec g o ν_rel hsingle hseed_rel hsupp_rel
  let projOut : CoupledState C.Seed D.State r_ds × ℕ → (C.Seed × Data r_ds) × ℕ :=
    fun p => ((p.1.seed, p.1.data), p.2)
  let m_step : C.Seed × Data r_ds → ProbComp (Data r_ds × ℕ) := fun p => m_rel (lift p)
  let μ_step : C.Seed × Data r_ds → PMF ((C.Seed × Data r_ds) × ℕ) :=
    fun p => (μ_rel (lift p)).map projOut
  have hbind_eq : ν.bind μ_step = (ν_rel.bind μ_rel).map projOut := by
    dsimp only [ν_rel, μ_step]
    rw [PMF.bind_map, PMF.map_bind]
    rfl
  refine ⟨m_step, μ_step, ?_, ?_, ?_⟩
  · intro p hp
    have ht_rel : lift p ∈ ν_rel.support := (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩
    obtain ⟨hm_rel, heval_rel, hq_rel⟩ := hstep_rel (lift p) ht_rel
    refine ⟨hm_rel, ?_, ?_⟩
    · dsimp only [μ_step, projOut]
      rw [PMF.map_comp]
      exact heval_rel
    · intro q hq
      dsimp only [μ_step] at hq
      rw [PMF.mem_support_map_iff] at hq
      obtain ⟨q_rel, hq_mem, rfl⟩ := hq
      obtain ⟨a, hstep_a, hdec, hrep', hmod⟩ := hq_rel q_rel hq_mem
      have hpair : (q_rel.1.state, a) = D.stepFn s o :=
        (D.step_iff_stepFn s o q_rel.1.state a).mp hstep_a
      exact ⟨congrArg Prod.snd hpair ▸ hdec, congrArg Prod.fst hpair ▸ hrep', hmod⟩
  · intro θ'
    rw [hbind_eq, PMF.map_comp, PMF.map_comp]
    have hcomp : ((Prod.fst ∘ Prod.fst) ∘ projOut) = (CoupledState.seed ∘ Prod.fst) := rfl
    rw [hcomp, ← PMF.map_comp]
    exact hseed_rel' θ'
  · rw [hbind_eq, PMF.toOuterMeasure_map_apply]
    exact hfail_rel

/-- Lift a `HighProbStateTransitionImpl` certificate along any defined-evaluation basis simulation
`φ : B.Simulates B'`. -/
def mapSimulates (φ : B.Simulates B') (C : HighProbStateTransitionImpl P D w base params s₀) :
    HighProbStateTransitionImpl (P.mapSimulates φ) D w base params s₀ where
  Seed := C.Seed
  seedLaw := C.seedLaw
  seedSlack := C.seedSlack
  seedSlack_ne_top := C.seedSlack_ne_top
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  setupRandCalls := C.setupRandCalls
  worstCaseTime := C.worstCaseTime
  failureProb := C.failureProb
  Ghost := C.Ghost
  ghostInit := C.ghostInit
  ghostStep := C.ghostStep
  ghostRep := C.ghostRep
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  singleState := C.singleState
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval h1 hfit := Op.eval_mapSimulates_of_some φ (C.incCur_eval h1 hfit)
  span_exec hx hf hp :=
    let ⟨x₁, he, hm, hb, hfr, hpar⟩ := C.span_exec hx hf hp
    ⟨x₁, he.mapSimulates φ, hm, hb, hfr, hpar⟩
  setup_exec hx₁ hb hfr hpar hz :=
    let ⟨m₀, ν₀, hm₀, hq₀, hT₀, heval₀, hseed₀, hsupp₀⟩ := C.setup_exec hx₁ hb hfr hpar hz
    ⟨m₀, ν₀, hm₀.mapSimulates φ, hq₀, hT₀, heval₀, hseed₀, hsupp₀⟩
  step_exec g o ν hsingle hseed hsupp :=
    let ⟨m_step, μ_step, hstep, hseed', hsingle', hfail⟩ :=
      C.step_exec g o ν hsingle hseed hsupp
    ⟨m_step, μ_step,
      fun t ht => ⟨(hstep t ht).1.mapSimulates φ, (hstep t ht).2.1, (hstep t ht).2.2⟩,
      hseed', hsingle', hfail⟩

/-- Lift an exact-basis `HighProbStateTransitionImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : HighProbStateTransitionImpl P D w base params s₀) :
    HighProbStateTransitionImpl P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

/-- Deliver externally encoded arguments, preserving maintained memory and persistent registers.
This mathematical register replacement is not a charged native instruction sequence. -/
@[expose] def prepare (C : HighProbStateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : Data r_ds) : Data r_ds :=
  P.prepare C.encode o x

theorem prepare_bounded (C : HighProbStateTransitionImpl P D w base params s₀)
    {o : D.Op} {x : Data r_ds} (hx : x.Bounded w)
    (ho : ∀ i, P.input i = true → Fits w (C.encode o i)) :
    (C.prepare o x).Bounded w :=
  P.prepare_bounded C.encode hx ho

theorem prepare_regs_of_not_input (C : HighProbStateTransitionImpl P D w base params s₀)
    {i : Fin r_ds} (hi : P.input i = false) (o : D.Op) (x : Data r_ds) :
    (C.prepare o x).regs i = x.regs i :=
  P.prepare_regs_of_not_input C.encode hi o x

@[simp] theorem prepare_mem (C : HighProbStateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : Data r_ds) : (C.prepare o x).mem = x.mem := by
  dsimp only [prepare]
  exact P.prepare_mem C.encode o x

@[simp] theorem prepare_regs (C : HighProbStateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : Data r_ds) (i : Fin r_ds) :
    (C.prepare o x).regs i = if P.input i then C.encode o i else x.regs i := rfl

theorem rep_bounded (C : HighProbStateTransitionImpl P D w base params s₀)
    {θ : C.Seed} {s : D.State} {x : Data r_ds} (hr : C.rep θ s x) : x.Bounded w := by
  obtain ⟨_, hg⟩ := hr
  exact C.bounded hg

theorem prepare_ghostRep (C : HighProbStateTransitionImpl P D w base params s₀)
    {g : C.Ghost} {θ : C.Seed} {s : D.State} {o : D.Op} {x : Data r_ds}
    (hr : C.ghostRep g θ s x) (hv : D.valid s o) :
    C.ghostRep g θ s (C.prepare o x) :=
  C.rep_supported
    (fun _ hi => C.prepare_regs_of_not_input hi o x)
    (fun _ _ => rfl)
    (C.prepare_bounded (C.bounded hr) (C.arguments_fit _ hv))
    hr

theorem prepare_rep (C : HighProbStateTransitionImpl P D w base params s₀)
    {θ : C.Seed} {s : D.State} {o : D.Op} {x : Data r_ds}
    (hr : C.rep θ s x) (hv : D.valid s o) :
    C.rep θ s (C.prepare o x) := by
  obtain ⟨g, hg⟩ := hr
  exact ⟨g, C.prepare_ghostRep hg hv⟩

theorem prepare_argMatch (C : HighProbStateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : Data r_ds) :
    C.argMatch o (C.prepare o x).regs :=
  C.encode_matches o x.regs

/-- Execute `P.initFresh` on zeroed `[base, base + C.space)` within `C.initTime` deterministic
worst-case instructions and `C.setupRandCalls` `rand` calls. -/
theorem initFresh_exec (C : HighProbStateTransitionImpl P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ (m_init : ProbComp (Data r_ds × ℕ)) (ν₀ : PMF (C.Seed × Data r_ds)),
      ExecRand w P.initFresh x m_init ∧
      OracleComp.IsQueryBounded m_init C.setupRandCalls ∧
      (∀ z ∈ m_init.support, z.2 ≤ C.initTime) ∧
      ν₀.map Prod.snd = (Prod.fst <$> m_init).eval ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.ghostRep C.ghostInit p.1 s₀ p.2 ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
  obtain ⟨x₁, hew₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := hew₁.bounded hx
  obtain ⟨n₁, hn₁, he₁⟩ := hew₁
  have hz₁ : ∀ a ∈ (Block.mk base C.space).footprint, x₁.mem a = 0 := by
    intro a ha; rw [hm₁]; exact hz a ha
  obtain ⟨m₀, ν₀, hm₀, hq₀, hT₀, heval₀, hseed₀, hsupp₀⟩ := C.setup_exec hx₁ hb₁ hfr₁ hpar₁ hz₁
  rw [hm₁] at hsupp₀
  have hseq : ExecRand w P.initFresh x
      (do let z₁ ← pure (x₁, n₁); let z₂ ← m₀; pure (z₂.1, z₁.2 + z₂.2)) :=
    he₁.execRand.seq (c₂ := P.initSetup) (m₂ := fun _ => m₀) fun z₁ hz₁ => by
      cases OracleComp.eq_of_mem_supportWith_pure hz₁
      exact hm₀
  refine ⟨_, ν₀, hseq, ?_, ?_, ?_, hseed₀, hsupp₀⟩
  · simpa [pure_bind, OracleComp.IsQueryBounded] using
      (OracleComp.isCostBounded_map_iff (f := fun z₂ : Data r_ds × ℕ => (z₂.1, n₁ + z₂.2))
        _ _).mpr hq₀
  · intro z hz
    simp only [pure_bind] at hz
    obtain ⟨z₂, hz₂, hfin⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hfin
    have h2 := hT₀ z₂ hz₂
    dsimp only [initTime]
    omega
  · rw [heval₀]
    simp [pure_bind, ProbComp.eval_map]

/-- Flat-program corollary for `P.initFresh.program out`: halts fault-free within `C.initTime + 1`
instructions on every path. -/
theorem initFresh_program (C : HighProbStateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      RandHaltsWithin w (P.initFresh.program out) ⟨0, x⟩ (C.initTime + 1) ∧
      RandCallsBounded w (P.initFresh.program out) ⟨0, x⟩ (C.initTime + 1) C.setupRandCalls ∧
      evalRand w (P.initFresh.program out) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs out) p.2) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.ghostRep C.ghostInit p.1 s₀ p.2 ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
  obtain ⟨m_init, ν₀, hm_init, hq_init, hT_init, heval_init, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec hx hfr hpar hz
  have hwithin : ExecRandWithin w P.initFresh x (fun _ => True) C.initTime C.setupRandCalls :=
    ⟨m_init, hm_init, hq_init, fun z hz => ⟨trivial, hT_init z hz⟩⟩
  obtain ⟨hhalts, hcalls, -⟩ := hwithin.program out le_rfl
  have hrun := hm_init.runRand_program out (T := C.initTime + 1) fun z hz =>
    Nat.add_le_add_right (hT_init z hz) 1
  have heval_eq :
      evalRand w (P.initFresh.program out) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs out) p.2) := by
    rw [evalRand, hrun, ProbComp.eval_map]
    have hmap_fst : (Prod.fst <$> m_init).eval = m_init.eval.map Prod.fst := ProbComp.eval_map _ _
    have hν_snd : ν₀.map Prod.snd = m_init.eval.map Prod.fst := heval_init.trans hmap_fst
    calc
      m_init.eval.map (fun z => RandCfg.halted (z.1.regs out) z.1)
        = (m_init.eval.map Prod.fst).map (fun y => RandCfg.halted (y.regs out) y) := by
          rw [PMF.map_comp]; rfl
      _ = (ν₀.map Prod.snd).map (fun y => RandCfg.halted (y.regs out) y) := by rw [← hν_snd]
      _ = ν₀.map (fun p => RandCfg.halted (p.2.regs out) p.2) := by rw [PMF.map_comp]; rfl
  exact ⟨ν₀, hhalts, hcalls, heval_eq, hseed₀, hsupp₀⟩

end Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

namespace Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

universe u v z

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Execute `P.initClear` on **arbitrary dirty memory** within `C.initClearTime` deterministic
worst-case instructions and `C.setupRandCalls` `rand` calls. -/
theorem initClear_exec (C : HighProbStateTransitionImpl P D w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ (m_clear : ProbComp (Data r_ds × ℕ)) (ν₀ : PMF (C.Seed × Data r_ds)),
      ExecRand w P.initClear x m_clear ∧
      OracleComp.IsQueryBounded m_clear C.setupRandCalls ∧
      (∀ z ∈ m_clear.support, z.2 ≤ C.initClearTime) ∧
      ν₀.map Prod.snd = (Prod.fst <$> m_clear).eval ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs P.frontierReg = base + C.space ∧
        C.ghostRep C.ghostInit p.1 s₀ p.2 ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
  obtain ⟨x₁, hew₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  obtain ⟨x₂, hew₂, hx₂, hb₂, hfr₂, hpar₂, hz₂, hmod₂⟩ :=
    P.zeroFillCode_exec C.clear_nodup C.params_not_clear C.incCur_eval
      (hew₁.bounded hx) hb₁ hfr₁ hpar₁
  obtain ⟨n₁, hn₁, he₁⟩ := hew₁
  obtain ⟨n₂, hn₂, he₂⟩ := hew₂
  obtain ⟨m₀, ν₀, hm₀, hq₀, hT₀, heval₀, hseed₀, hsupp₀⟩ :=
    C.setup_exec hx₂ hb₂ hfr₂ hpar₂ hz₂
  rw [hm₁] at hmod₂
  let m_tail : ProbComp (Data r_ds × ℕ) :=
    do let z₁ ← pure (x₂, n₂); let z₂ ← m₀; pure (z₂.1, z₁.2 + z₂.2)
  have hseq₂ : ExecRand w (.seq P.zeroFillCode P.initSetup) x₁ m_tail :=
    he₂.execRand.seq (c₂ := P.initSetup) (m₂ := fun _ => m₀) fun z₁ hz₁ => by
      cases OracleComp.eq_of_mem_supportWith_pure hz₁
      exact hm₀
  have hseq₁ : ExecRand w P.initClear x
      (do let u₁ ← pure (x₁, n₁)
          let u₂ ← m_tail
          pure (u₂.1, u₁.2 + u₂.2)) :=
    he₁.execRand.seq (c₂ := .seq P.zeroFillCode P.initSetup) (m₂ := fun _ => m_tail)
      fun u₁ hu₁ => by
        cases OracleComp.eq_of_mem_supportWith_pure hu₁
        exact hseq₂
  refine ⟨_, ν₀, hseq₁, ?_, ?_, ?_, hseed₀, fun p hp => ?_⟩
  · dsimp only [m_tail]
    simpa [pure_bind, bind_assoc, OracleComp.IsQueryBounded] using
      (OracleComp.isCostBounded_map_iff
        (f := fun z₂ : Data r_ds × ℕ => (z₂.1, n₁ + (n₂ + z₂.2)))
        _ _).mpr hq₀
  · intro z hz
    dsimp only [m_tail] at hz
    simp only [pure_bind, bind_assoc] at hz
    obtain ⟨z₂, hz₂, hfin⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hfin
    have h3 := hT₀ z₂ hz₂
    dsimp only [initClearTime, initTime]
    omega
  · rw [heval₀]
    dsimp only [m_tail]
    simp [pure_bind, ProbComp.eval_map]
  · obtain ⟨hfr₃, hrep, hmod₃⟩ := hsupp₀ p hp
    have hmod : Modifies (Block.mk base C.space).footprint x.mem p.2.mem := by
      simpa only [Finset.union_idempotent] using hmod₂.trans hmod₃
    exact ⟨hfr₃, hrep, hmod⟩

/-! ### Per-operation with-high-probability worst-case bounds (`step_whp`, `step_whp_ofFn`) -/

/-- **Per-operation with-high-probability worst-case halting bound (`step_whp`).**
From any reachable coupled state distribution `ν : PMF (CoupledState C.Seed D.State r_ds)` at
deterministic ghost state `g : C.Ghost`, preparing arguments for any admissible operation `o` and
running `P.code.program out` is fault-free across all horizons, transitions to a valid coupled
distribution `ν_next` preserving the seed marginal and `ghostRep (C.ghostStep g o)`, and halts
within deterministic horizon `C.worstCaseTime + 1` in `evalRand` with probability at least
`1 - C.failureProb`. -/
theorem step_whp (C : HighProbStateTransitionImpl P D w base params s₀)
    {g : C.Ghost} (out : Fin r_ds) (o : D.Op) (ν : PMF (CoupledState C.Seed D.State r_ds))
    (hv : ∀ t ∈ ν.support, D.valid t.state o)
    (hseed : ∀ θ, (ν.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ)
    (hrep : ∀ t ∈ ν.support, C.ghostRep g t.seed t.state t.data)
    (hsingle : C.singleState → ∃ s, ∀ t ∈ ν.support, t.state = s := by intro h; cases h) :
    ∃ (m_op : CoupledState C.Seed D.State r_ds → ProbComp (Data r_ds × ℕ))
      (μ_op : CoupledState C.Seed D.State r_ds → PMF (CoupledState C.Seed D.State r_ds × ℕ)),
      (∀ t ∈ ν.support,
        let x_in := C.prepare o t.data
        RandFaultFree w (P.code.program out) ⟨0, x_in⟩ ∧
        ExecRand w P.code x_in (m_op t) ∧
        (μ_op t).map (fun p => (p.1.data, p.2)) = (m_op t).eval ∧
        (∀ y : Data r_ds,
          (m_op t).eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ C.worstCaseTime} ≤
            evalRand w (P.code.program out) (C.worstCaseTime + 1) ⟨0, x_in⟩
              (.halted (y.regs out) y)) ∧
        ∀ p ∈ (μ_op t).support,
          ∃ a : D.Result o,
            D.step t.state o p.1.state a ∧
            C.decode o p.1.data.regs = some a ∧
            C.ghostRep (C.ghostStep g o) p.1.seed p.1.state p.1.data ∧
            p.1.data.Bounded w ∧
            Modifies (Block.mk base C.space).footprint t.data.mem p.1.data.mem) ∧
      (∀ θ', (((ν.bind μ_op).map Prod.fst).map CoupledState.seed) θ' ≤ C.seedSlack * C.seedLaw θ') ∧
      (C.singleState → ∃ s', ∀ p ∈ (ν.bind μ_op).support, p.1.state = s') ∧
      (ν.bind μ_op).toOuterMeasure {p | C.worstCaseTime < p.2} ≤ C.failureProb ∧
      1 - C.failureProb ≤
        (ν.bind fun t =>
          evalRand w (P.code.program out) (C.worstCaseTime + 1)
            ⟨0, C.prepare o t.data⟩).toOuterMeasure
          {cfg | ∃ (t : CoupledState C.Seed D.State r_ds) (q : CoupledState C.Seed D.State r_ds)
              (a : D.Result o),
            t ∈ ν.support ∧
            cfg = .halted (q.data.regs out) q.data ∧
            D.step t.state o q.state a ∧
            C.decode o q.data.regs = some a ∧
            C.ghostRep (C.ghostStep g o) q.seed q.state q.data ∧
            q.data.Bounded w ∧
            Modifies (Block.mk base C.space).footprint t.data.mem q.data.mem} := by
  let prepMap : CoupledState C.Seed D.State r_ds → CoupledState C.Seed D.State r_ds :=
    fun t => ⟨t.seed, t.state, C.prepare o t.data⟩
  let ν_prep : PMF (CoupledState C.Seed D.State r_ds) := ν.map prepMap
  have hsingle_prep : C.singleState → ∃ s, ∀ t' ∈ ν_prep.support, t'.state = s := by
    intro hd
    obtain ⟨s, hs⟩ := hsingle hd
    refine ⟨s, fun t' ht' => ?_⟩
    rw [PMF.mem_support_map_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact hs t ht
  have hseed_prep : ∀ θ, (ν_prep.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ; rw [PMF.map_comp]; exact hseed θ
  have hsupp_prep : ∀ t' ∈ ν_prep.support,
      D.valid t'.state o ∧ C.ghostRep g t'.seed t'.state t'.data ∧ C.argMatch o t'.data.regs := by
    intro t' ht'
    rw [PMF.mem_support_map_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact ⟨hv t ht, C.prepare_ghostRep (hrep t ht) (hv t ht), C.prepare_argMatch o t.data⟩
  obtain ⟨m_step, μ_step, hstep, hseed₁, hsingle₁, hfail₁⟩ :=
    C.step_exec g o ν_prep hsingle_prep hseed_prep hsupp_prep
  let m_op := fun t => m_step (prepMap t)
  let μ_op := fun t => μ_step (prepMap t)
  have hbind_eq : ν.bind μ_op = ν_prep.bind μ_step := by
    dsimp only [ν_prep, μ_op]
    rw [PMF.bind_map]
    rfl
  refine ⟨m_op, μ_op, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : prepMap t ∈ ν_prep.support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
    obtain ⟨hm_t, heval_t, hp_t⟩ := hstep (prepMap t) ht'
    obtain ⟨-, hff_t, -, -⟩ := (ExecCodeDist.of_execRand hm_t).program_halts out
    refine ⟨hff_t, hm_t, heval_t, hm_t.toOuterMeasure_le_evalRand_program out C.worstCaseTime, ?_⟩
    intro p hp
    obtain ⟨a, hst, hdec, hrep_p, hmod_p⟩ := hp_t p hp
    exact ⟨a, hst, hdec, hrep_p, C.bounded hrep_p, hmod_p⟩
  · rw [hbind_eq]; exact hseed₁
  · rw [hbind_eq]; exact hsingle₁
  · rw [hbind_eq]; exact hfail₁
  · set GoodCfg : Set (RandCfg r_ds) :=
      {cfg | ∃ (t : CoupledState C.Seed D.State r_ds) (q : CoupledState C.Seed D.State r_ds)
          (a : D.Result o),
        t ∈ ν.support ∧
        cfg = .halted (q.data.regs out) q.data ∧
        D.step t.state o q.state a ∧
        C.decode o q.data.regs = some a ∧
        C.ghostRep (C.ghostStep g o) q.seed q.state q.data ∧
        q.data.Bounded w ∧
        Modifies (Block.mk base C.space).footprint t.data.mem q.data.mem}
    have hcompl :
        1 - C.failureProb ≤
          (ν.bind μ_op).toOuterMeasure {p | p.2 ≤ C.worstCaseTime} := by
      rw [hbind_eq]
      refine (Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl _ _ hfail₁).trans ?_
      refine MeasureTheory.measure_mono fun p hp => ?_
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hp
      exact hp
    refine hcompl.trans ?_
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun t => ?_
    by_cases ht : t ∈ ν.support
    · refine mul_le_mul_right ?_ _
      have ht' : prepMap t ∈ ν_prep.support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
      obtain ⟨hm_t, heval_t, hp_t⟩ := hstep (prepMap t) ht'
      let Q_t : Data r_ds → Prop := fun y =>
        ∃ (q : CoupledState C.Seed D.State r_ds) (a : D.Result o),
          q.data = y ∧
          D.step t.state o q.state a ∧
          C.decode o q.data.regs = some a ∧
          C.ghostRep (C.ghostStep g o) q.seed q.state q.data ∧
          q.data.Bounded w ∧
          Modifies (Block.mk base C.space).footprint t.data.mem q.data.mem
      have hQ_t : ∀ z ∈ (m_op t).eval.support, Q_t z.1 := by
        intro z hz
        change z ∈ (m_step (prepMap t)).eval.support at hz
        rw [← heval_t, PMF.mem_support_map_iff] at hz
        obtain ⟨p, hp, rfl⟩ := hz
        obtain ⟨a, hst, hdec, hrep_p, hmod_p⟩ := hp_t p hp
        exact ⟨p.1, a, rfl, hst, hdec, hrep_p, C.bounded hrep_p, hmod_p⟩
      have hfail_eq :
          (μ_op t).toOuterMeasure {p | p.2 ≤ C.worstCaseTime} =
            1 - (m_op t).eval.toOuterMeasure {z | C.worstCaseTime < z.2} := by
        have hmap_meas :
            (m_op t).eval.toOuterMeasure {z | C.worstCaseTime < z.2} =
              (μ_op t).toOuterMeasure {p | C.worstCaseTime < p.2} := by
          change (m_step (prepMap t)).eval.toOuterMeasure _ = _
          rw [← heval_t, PMF.toOuterMeasure_map_apply]
          rfl
        rw [hmap_meas]
        have hsum := PMF.toOuterMeasure_add_compl_ennreal (μ_op t) {p | C.worstCaseTime < p.2}
        have hcompl_set :
            ({p : CoupledState C.Seed D.State r_ds × ℕ | C.worstCaseTime < p.2}ᶜ :
              Set (CoupledState C.Seed D.State r_ds × ℕ)) =
            {p | p.2 ≤ C.worstCaseTime} := by
          ext p; simp
        rw [hcompl_set, add_comm] at hsum
        exact ENNReal.eq_sub_of_add_eq (PMF.toOuterMeasure_ne_top _ _) hsum
      rw [hfail_eq]
      refine (hm_t.one_sub_le_evalRand_program out C.worstCaseTime hQ_t le_rfl).trans ?_
      refine (evalRand w (P.code.program out) (C.worstCaseTime + 1)
        ⟨0, C.prepare o t.data⟩).toOuterMeasure.mono fun cfg hcfg => ?_
      obtain ⟨y, rfl, q, a, rfl, hst, hdec, hrep_q, hbdd_q, hmod_q⟩ := hcfg
      exact ⟨t, q, a, ht, rfl, hst, hdec, hrep_q, hbdd_q, hmod_q⟩
    · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, zero_mul, zero_mul]

/-- **Per-operation with-high-probability worst-case bound for functional specifications
(`step_whp_ofFn`).** -/
theorem step_whp_ofFn (C : HighProbStateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {g : C.Ghost} (out : Fin r_ds) {s : D.State} (o : D.Op) (ν : PMF (C.Seed × Data r_ds))
    (hv : D.valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ)
    (hrep : ∀ p ∈ ν.support, C.ghostRep g p.1 s p.2) :
    1 - C.failureProb ≤
      (ν.bind fun p =>
        evalRand w (P.code.program out) (C.worstCaseTime + 1)
          ⟨0, C.prepare o p.2⟩).toOuterMeasure
        {cfg | ∃ (p : C.Seed × Data r_ds) (q : C.Seed × Data r_ds),
          p ∈ ν.support ∧
          cfg = .halted (q.2.regs out) q.2 ∧
          C.decode o q.2.regs = some (D.stepFn s o).2 ∧
          C.ghostRep (C.ghostStep g o) q.1 (D.stepFn s o).1 q.2 ∧
          q.2.Bounded w ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem} := by
  let lift : C.Seed × Data r_ds → CoupledState C.Seed D.State r_ds := fun p => ⟨p.1, s, p.2⟩
  let ν_rel : PMF (CoupledState C.Seed D.State r_ds) := ν.map lift
  have hs₀ : ∀ t ∈ ν_rel.support, t.state = s := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨_, _, rfl⟩ := ht; rfl
  have hv_rel : ∀ t ∈ ν_rel.support, D.valid t.state o := fun t ht => hs₀ t ht ▸ hv
  have hseed_rel : ∀ θ, (ν_rel.map CoupledState.seed) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ; rw [PMF.map_comp]; exact hseed θ
  have hrep_rel : ∀ t ∈ ν_rel.support, C.ghostRep g t.seed t.state t.data := by
    intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht; exact hrep p hp
  obtain ⟨_, _, _, _, _, _, hwhp⟩ :=
    C.step_whp out o ν_rel hv_rel hseed_rel hrep_rel (fun _ => ⟨s, hs₀⟩)
  have hbind_eq :
      (ν_rel.bind fun t =>
          evalRand w (P.code.program out) (C.worstCaseTime + 1)
            ⟨0, C.prepare o t.data⟩) =
        (ν.bind fun p =>
          evalRand w (P.code.program out) (C.worstCaseTime + 1)
            ⟨0, C.prepare o p.2⟩) := by
    dsimp only [ν_rel]; rw [PMF.bind_map]; rfl
  rw [hbind_eq] at hwhp
  refine hwhp.trans ((ν.bind fun p => evalRand w (P.code.program out) (C.worstCaseTime + 1)
    ⟨0, C.prepare o p.2⟩).toOuterMeasure.mono fun cfg hcfg => ?_)
  obtain ⟨t, q, a, ht, rfl, hst, hdec, hrep_q, hbdd_q, hmod_q⟩ := hcfg
  rw [PMF.mem_support_map_iff] at ht
  obtain ⟨p, hp, rfl⟩ := ht
  have hpair : (q.state, a) = D.stepFn s o :=
    (D.step_iff_stepFn s o q.state a).mp hst
  exact ⟨p, (q.seed, q.data), hp, rfl, congrArg Prod.snd hpair ▸ hdec,
    congrArg Prod.fst hpair ▸ hrep_q, hbdd_q, hmod_q⟩

end Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

namespace Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

universe u v z

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-! ### Multi-operation whole-sequence worst-case execution (`ExecWhpSteps`, `steps_whp`, `seq_whp`,
`steps_whp_ofFn`, `seq_whp_ofFn`, `seq_whp_poly_ofFn`) -/

/-- Operational multi-step trajectory execution relation for `C : HighProbStateTransitionImpl`.
At each operation `o :: ops`, from every supported trajectory prefix `tr ∈ τ.support`, running
`P.code` on `C.prepare o tr.current.data` executes via `ExecRand` (`m_op`),
matches `(μ_op tr.current)` in `(data, steps)` distribution (hence reaches `.halted` in `evalRand`
within `C.worstCaseTime + 1` steps on every branch with `n ≤ C.worstCaseTime`), witnesses a valid
transition `D.step tr.current.state o q.state a` with `decode o q.data.regs = some a`, `rep`,
`Bounded w`, and `Modifies`, and records `(q, a, max tr.maxSteps n)` in the trajectory. -/
inductive ExecWhpSteps (C : HighProbStateTransitionImpl P D w base params s₀) (out : Fin r_ds) :
    List D.Op → PMF (WhpSeqOutcome C.Seed D r_ds) → PMF (WhpSeqOutcome C.Seed D r_ds) → Prop where
  | nil (τ : PMF (WhpSeqOutcome C.Seed D r_ds)) :
      C.ExecWhpSteps out [] τ τ
  | cons {o : D.Op} {ops : List D.Op}
      {τ τ_final : PMF (WhpSeqOutcome C.Seed D r_ds)}
      (m_op : CoupledState C.Seed D.State r_ds → ProbComp (Data r_ds × ℕ))
      (μ_step :
        CoupledState C.Seed D.State r_ds →
          PMF ((CoupledState C.Seed D.State r_ds × D.Result o) × ℕ))
      (hstep : ∀ t ∈ (τ.map WhpSeqOutcome.current).support,
        let x_in := C.prepare o t.data
        RandFaultFree w (P.code.program out) ⟨0, x_in⟩ ∧
        ExecRand w P.code x_in (m_op t) ∧
        (μ_step t).map (fun p => (p.1.1.data, p.2)) = (m_op t).eval ∧
        (∀ y : Data r_ds,
          (m_op t).eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ C.worstCaseTime} ≤
            evalRand w (P.code.program out) (C.worstCaseTime + 1) ⟨0, x_in⟩
              (.halted (y.regs out) y)) ∧
        ∀ p ∈ (μ_step t).support,
          D.step t.state o p.1.1.state p.1.2 ∧
          C.decode o p.1.1.data.regs = some p.1.2 ∧
          C.rep p.1.1.seed p.1.1.state p.1.1.data ∧
          p.1.1.data.Bounded w ∧
          Modifies (Block.mk base C.space).footprint t.data.mem p.1.1.data.mem)
      (hrest : C.ExecWhpSteps out ops
        (τ.bind fun tr => (μ_step tr.current).map fun p => tr.appendStep o p.1.1 p.1.2 p.2)
        τ_final) :
      C.ExecWhpSteps out (o :: ops) τ τ_final

private theorem decode_unique_of_eq {α : Type v} {x y : α} {opt : Option α}
    (hx : opt = some x) (hy : opt = some y) : x = y := by
  rw [hx] at hy; injection hy

private theorem pmf_map_congr {α β : Type*} {p : PMF α} {f g : α → β}
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ha]

/-- **Whole-sequence trajectory execution and union bound (`steps_whp`).**
Across any admissible sequence `ops : List D.Op`, starting from trajectory distribution `τ` whose
current-state marginal satisfies the seed bound and `rep`, `P.code` executes all operations in `ops`
under `C.ExecWhpSteps out ops τ τ_final` such that the probability of *any* operation in `ops`
exceeding `C.worstCaseTime` executed instructions increases by at most `ops.length * C.failureProb`.
-/
theorem steps_whp (C : HighProbStateTransitionImpl P D w base params s₀)
    {g : C.Ghost} (out : Fin r_ds) (ops : List D.Op) (τ : PMF (WhpSeqOutcome C.Seed D r_ds))
    (hv : ∀ t ∈ (τ.map WhpSeqOutcome.current).support, D.ValidOpSeq t.state ops)
    (hseed : ∀ θ, ((τ.map WhpSeqOutcome.current).map CoupledState.seed) θ ≤
      C.seedSlack * C.seedLaw θ)
    (hrep : ∀ t ∈ (τ.map WhpSeqOutcome.current).support, C.ghostRep g t.seed t.state t.data)
    (hsingle : C.singleState → ∃ s, ∀ t ∈ (τ.map WhpSeqOutcome.current).support, t.state = s :=
      by intro h; cases h) :
    ∃ τ_final : PMF (WhpSeqOutcome C.Seed D r_ds),
      C.ExecWhpSteps out ops τ τ_final ∧
      (∀ θ, ((τ_final.map WhpSeqOutcome.current).map CoupledState.seed) θ ≤
        C.seedSlack * C.seedLaw θ) ∧
      (∀ t ∈ (τ_final.map WhpSeqOutcome.current).support,
        C.ghostRep (C.ghostRun g ops) t.seed t.state t.data) ∧
      τ_final.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} ≤
        τ.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} +
          (ops.length : ℝ≥0∞) * C.failureProb := by
  classical
  induction ops generalizing τ g with
  | nil =>
    exact ⟨τ, .nil τ, hseed, hrep, by simp⟩
  | cons o os ih =>
    let ν := τ.map WhpSeqOutcome.current
    have hv_o : ∀ t ∈ ν.support, D.valid t.state o := fun t ht => (hv t ht).1
    obtain ⟨m_op, μ_op, hstep_o, hseed₁, hsingle₁, hfail₁, -⟩ :=
      C.step_whp out o ν hv_o hseed hrep hsingle
    let attachRes :
        ∀ (t : CoupledState C.Seed D.State r_ds) (p : CoupledState C.Seed D.State r_ds × ℕ),
          (t ∈ ν.support ∧ p ∈ (μ_op t).support) → D.Result o :=
      fun t p hp => Classical.choose ((hstep_o t hp.1).2.2.2.2 p hp.2)
    have hDefaultRes : Nonempty (D.Result o) := by
      obtain ⟨t₀, ht₀⟩ := ν.support_nonempty
      obtain ⟨p₀, hp₀⟩ := (μ_op t₀).support_nonempty
      exact ⟨attachRes t₀ p₀ ⟨ht₀, hp₀⟩⟩
    let defRes : D.Result o := Classical.arbitrary (D.Result o)
    let μ_step :
        CoupledState C.Seed D.State r_ds →
          PMF ((CoupledState C.Seed D.State r_ds × D.Result o) × ℕ) :=
      fun t => (μ_op t).map fun p =>
        if hp : t ∈ ν.support ∧ p ∈ (μ_op t).support then
          ((p.1, attachRes t p hp), p.2)
        else
          ((p.1, defRes), p.2)
    let τ₁ : PMF (WhpSeqOutcome C.Seed D r_ds) :=
      τ.bind fun tr => (μ_step tr.current).map fun p => tr.appendStep o p.1.1 p.1.2 p.2
    have hcur₁ : τ₁.map WhpSeqOutcome.current = (ν.bind μ_op).map Prod.fst := by
      dsimp only [τ₁, ν, μ_step]
      rw [PMF.map_bind, PMF.bind_map, PMF.map_bind]
      refine congrArg (τ.bind ·) (funext fun tr => ?_)
      rw [PMF.map_comp, PMF.map_comp]
      refine congrArg ((μ_op tr.current).map ·) (funext fun p => ?_)
      dsimp only [Function.comp_apply, WhpSeqOutcome.appendStep]
      split_ifs <;> rfl
    have hstep_rel : ∀ t ∈ ν.support,
        let x_in := C.prepare o t.data
        RandFaultFree w (P.code.program out) ⟨0, x_in⟩ ∧
        ExecRand w P.code x_in (m_op t) ∧
        (μ_step t).map (fun p => (p.1.1.data, p.2)) = (m_op t).eval ∧
        (∀ y : Data r_ds,
          (m_op t).eval.toOuterMeasure {z | z.1 = y ∧ z.2 ≤ C.worstCaseTime} ≤
            evalRand w (P.code.program out) (C.worstCaseTime + 1) ⟨0, x_in⟩
              (.halted (y.regs out) y)) ∧
        ∀ p ∈ (μ_step t).support,
          D.step t.state o p.1.1.state p.1.2 ∧
          C.decode o p.1.1.data.regs = some p.1.2 ∧
          C.rep p.1.1.seed p.1.1.state p.1.1.data ∧
          p.1.1.data.Bounded w ∧
          Modifies (Block.mk base C.space).footprint t.data.mem p.1.1.data.mem := by
      intro t ht
      obtain ⟨hff, hm, hev, hreach, hq⟩ := hstep_o t ht
      refine ⟨hff, hm, ?_, hreach, ?_⟩
      · dsimp only [μ_step]
        rw [PMF.map_comp, ← hev]
        refine pmf_map_congr fun p _ => ?_
        dsimp only [Function.comp_apply]
        split_ifs <;> rfl
      · intro p' hp'
        dsimp only [μ_step] at hp'
        rw [PMF.mem_support_map_iff] at hp'
        obtain ⟨p, hp, rfl⟩ := hp'
        have hcond : t ∈ ν.support ∧ p ∈ (μ_op t).support := ⟨ht, hp⟩
        simp only [hcond]
        obtain ⟨hst_p, hdec_p, hgrep_p, hbdd_p, hmod_p⟩ := Classical.choose_spec (hq p hp)
        exact ⟨hst_p, hdec_p, ⟨C.ghostStep g o, hgrep_p⟩, hbdd_p, hmod_p⟩
    have hv₁ : ∀ q ∈ (τ₁.map WhpSeqOutcome.current).support, D.ValidOpSeq q.state os := by
      intro q hq
      rw [hcur₁, PMF.mem_support_map_iff] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨t, ht, hp_op⟩ := hp
      obtain ⟨a, hst, -, -, -, -⟩ := (hstep_o t ht).2.2.2.2 p hp_op
      exact (hv t ht).2 p.1.state a hst
    have hseed₁' : ∀ θ, ((τ₁.map WhpSeqOutcome.current).map CoupledState.seed) θ ≤
        C.seedSlack * C.seedLaw θ := by
      rw [hcur₁]; exact hseed₁
    have hrep₁ : ∀ q ∈ (τ₁.map WhpSeqOutcome.current).support,
        C.ghostRep (C.ghostStep g o) q.seed q.state q.data := by
      intro q hq
      rw [hcur₁, PMF.mem_support_map_iff] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨t, ht, hp_op⟩ := hp
      obtain ⟨_, -, -, hrep_p, -, -⟩ := (hstep_o t ht).2.2.2.2 p hp_op
      exact hrep_p
    have hsingle₁' : C.singleState → ∃ s', ∀ q ∈ (τ₁.map WhpSeqOutcome.current).support,
        q.state = s' := by
      intro hd
      obtain ⟨s', hs'⟩ := hsingle₁ hd
      refine ⟨s', fun q hq => ?_⟩
      rw [hcur₁, PMF.mem_support_map_iff] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      exact hs' p hp
    have hfail_step :
        τ₁.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} ≤
          τ.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} + C.failureProb := by
      have hle_union :
          τ₁.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} ≤
            τ.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} +
              (ν.bind μ_op).toOuterMeasure {p | C.worstCaseTime < p.2} := by
        dsimp only [τ₁, ν, μ_step]
        rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
          PMF.toOuterMeasure_bind_apply, ← tsum_add]
        refine tsum_le_tsum fun tr => ?_
        by_cases htr : tr ∈ τ.support
        · rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
          by_cases hprev : C.worstCaseTime < tr.maxSteps
          · rw [Set.indicator_of_mem hprev]
            calc
              τ tr * (μ_op tr.current).toOuterMeasure _
                ≤ τ tr * 1 := mul_le_mul_right (PMF.toOuterMeasure_le_one _ _) _
              _ = τ tr := mul_one _
              _ ≤ τ tr + τ tr * (μ_op tr.current).toOuterMeasure _ := le_self_add
          · rw [Set.indicator_of_notMem hprev, zero_add]
            refine mul_le_mul_right (MeasureTheory.measure_mono fun p hp => ?_) _
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, WhpSeqOutcome.appendStep] at hp ⊢
            split_ifs at hp <;> simp only at hp <;> omega
        · rw [(PMF.apply_eq_zero_iff _ _).mpr htr]
          simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr htr]
      exact hle_union.trans (add_le_add le_rfl hfail₁)
    obtain ⟨τ_final, hex_rest, hseed_final, hrep_final, hfail_rest⟩ :=
      ih τ₁ hv₁ hseed₁' hrep₁ hsingle₁'
    refine ⟨τ_final, .cons m_op μ_step hstep_rel hex_rest, hseed_final, hrep_final, ?_⟩
    calc
      τ_final.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps}
        ≤ τ₁.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} +
            (os.length : ℝ≥0∞) * C.failureProb := hfail_rest
      _ ≤ (τ.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} + C.failureProb) +
            (os.length : ℝ≥0∞) * C.failureProb := add_le_add hfail_step le_rfl
      _ = τ.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} +
            ((o :: os).length : ℝ≥0∞) * C.failureProb := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          ac_rfl

/-- **End-to-end whole-sequence with-high-probability theorem from fresh initialization
(`seq_whp`).**
Starting from zeroed `[base, base + C.space)`, `P.initFresh` halts within `C.initTime` deterministic
worst-case instructions, and across any admissible sequence `ops : List D.Op`, every single
operation in `ops` executes within `C.worstCaseTime` body instructions with probability at least
`1 - ops.length * C.failureProb`. -/
theorem seq_whp (C : HighProbStateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {x : Data r_ds} (ops : List D.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : D.ValidOpSeq s₀ ops) :
    ∃ (ν₀ : PMF (C.Seed × Data r_ds)) (τ_final : PMF (WhpSeqOutcome C.Seed D r_ds)),
      RandHaltsWithin w (P.initFresh.program out) ⟨0, x⟩ (C.initTime + 1) ∧
      evalRand w (P.initFresh.program out) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs out) p.2) ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs P.frontierReg = base + C.space ∧
        C.rep p.1 s₀ p.2 ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem) ∧
      C.ExecWhpSteps out ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, s₀, p.2⟩) τ_final ∧
      (∀ tr ∈ τ_final.support,
        C.ghostRep (C.ghostRun C.ghostInit ops) tr.current.seed tr.current.state tr.current.data) ∧
      (∀ θ, ((τ_final.map WhpSeqOutcome.current).map CoupledState.seed) θ ≤
        C.seedSlack * C.seedLaw θ) ∧
      τ_final.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} ≤
        (ops.length : ℝ≥0∞) * C.failureProb ∧
      1 - (ops.length : ℝ≥0∞) * C.failureProb ≤
        τ_final.toOuterMeasure {tr | tr.maxSteps ≤ C.worstCaseTime} := by
  obtain ⟨ν₀, hhalts₀, -, heval₀, hseed₀, hsupp₀⟩ := C.initFresh_program out hx hfr hpar hz
  let τ₀ : PMF (WhpSeqOutcome C.Seed D r_ds) :=
    ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, s₀, p.2⟩
  have hcur₀ : τ₀.map WhpSeqOutcome.current = ν₀.map (fun p => ⟨p.1, s₀, p.2⟩) := by
    dsimp only [τ₀]; rw [PMF.map_comp]; rfl
  have hv₀ : ∀ t ∈ (τ₀.map WhpSeqOutcome.current).support, D.ValidOpSeq t.state ops := by
    intro t ht; rw [hcur₀, PMF.mem_support_map_iff] at ht; obtain ⟨_, _, rfl⟩ := ht; exact hv
  have hseed_τ₀ : ∀ θ, ((τ₀.map WhpSeqOutcome.current).map CoupledState.seed) θ ≤
      C.seedSlack * C.seedLaw θ := by
    intro θ; rw [hcur₀, PMF.map_comp]; exact hseed₀ θ
  have hrep_τ₀ : ∀ t ∈ (τ₀.map WhpSeqOutcome.current).support,
      C.ghostRep C.ghostInit t.seed t.state t.data := by
    intro t ht; rw [hcur₀, PMF.mem_support_map_iff] at ht; obtain ⟨p, hp, rfl⟩ := ht
    exact (hsupp₀ p hp).2.1
  have hsingle₀ :
      C.singleState → ∃ s, ∀ t ∈ (τ₀.map WhpSeqOutcome.current).support, t.state = s := by
    intro _; refine ⟨s₀, fun t ht => ?_⟩
    rw [hcur₀, PMF.mem_support_map_iff] at ht; obtain ⟨_, _, rfl⟩ := ht; rfl
  have hzero_max : τ₀.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro tr htr hlt
    dsimp only [τ₀] at htr
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨_, _, rfl⟩ := htr
    change C.worstCaseTime < 0 at hlt
    omega
  obtain ⟨τ_final, hex, hseed_final, hrep_final, hfail⟩ :=
    C.steps_whp out ops τ₀ hv₀ hseed_τ₀ hrep_τ₀ hsingle₀
  rw [hzero_max, zero_add] at hfail
  refine ⟨ν₀, τ_final, hhalts₀, heval₀, ?_, hex, ?_, hseed_final, hfail, ?_⟩
  · intro p hp
    obtain ⟨hfr', hrep_p, hmod_p⟩ := hsupp₀ p hp
    exact ⟨C.bounded hrep_p, hfr', ⟨C.ghostInit, hrep_p⟩, hmod_p⟩
  · intro tr htr
    exact hrep_final tr.current ((PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩)
  · refine (Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl _ _ hfail).trans ?_
    refine MeasureTheory.measure_mono fun tr htr => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at htr
    exact htr

/-- Deterministic-specification transcript exactness for `ExecWhpSteps`: when `[D.HasStepFn stepFn]`
and the initial trajectory distribution has `tr.current.state = s` and `tr.transcript = acc` on its
support, every supported final trajectory `tr ∈ τ_final.support` reaches abstract state
`(D.run s ops).1` with exact output transcript `acc ++ (D.run s ops).2`. -/
theorem ExecWhpSteps.transcript_eq_ofFn {C : HighProbStateTransitionImpl P D w base params s₀}
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    {out : Fin r_ds} {s : D.State} {acc : List (Sigma D.Result)} {ops : List D.Op}
    {τ τ_final : PMF (WhpSeqOutcome C.Seed D r_ds)}
    (hex : C.ExecWhpSteps out ops τ τ_final)
    (hinit : ∀ tr ∈ τ.support, tr.current.state = s ∧ tr.transcript = acc) :
    ∀ tr ∈ τ_final.support,
      tr.current.state = (D.run s ops).1 ∧
      tr.transcript = acc ++ (D.run s ops).2 := by
  induction hex generalizing s acc with
  | nil _ =>
    intro tr htr
    obtain ⟨hs, htr_eq⟩ := hinit tr htr
    exact ⟨hs, by simpa using htr_eq⟩
  | @cons o os τ τ_final m_op μ_step hstep _ ih =>
    have hinit₁ : ∀ tr' ∈ (τ.bind fun tr => (μ_step tr.current).map fun p =>
        tr.appendStep o p.1.1 p.1.2 p.2).support,
        tr'.current.state = (D.stepFn s o).1 ∧
        tr'.transcript = acc ++ [⟨o, (D.stepFn s o).2⟩] := by
      intro tr' htr'
      rw [PMF.mem_support_bind_iff] at htr'
      obtain ⟨tr, htr, hmap⟩ := htr'
      rw [PMF.mem_support_map_iff] at hmap
      obtain ⟨p, hp, rfl⟩ := hmap
      have ht_cur : tr.current ∈ (τ.map WhpSeqOutcome.current).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩
      obtain ⟨hst, -, -, -, -⟩ := (hstep tr.current ht_cur).2.2.2.2 p hp
      obtain ⟨hs_tr, hacc_tr⟩ := hinit tr htr
      rw [hs_tr] at hst
      have hpair : (p.1.1.state, p.1.2) = D.stepFn s o :=
        (D.step_iff_stepFn s o p.1.1.state p.1.2).mp hst
      refine ⟨congrArg Prod.fst hpair, ?_⟩
      dsimp only [WhpSeqOutcome.appendStep]
      rw [hacc_tr, congrArg Prod.snd hpair]
    intro tr htr
    obtain ⟨hs_fin, htr_fin⟩ := ih hinit₁ tr htr
    refine ⟨by simpa only [StateTransitionSpec.run_cons] using hs_fin, ?_⟩
    simpa only [StateTransitionSpec.run_cons, List.append_assoc, List.singleton_append]
      using htr_fin

/-- **End-to-end whole-sequence with-high-probability theorem for functional specifications
(`seq_whp_ofFn`).**
Across any admissible history `ops : List D.Op`, every branch produces the exact specification
transcript `(D.run s₀ ops).2` and maintains `C.rep _ (D.run s₀ ops).1 _`, while with probability at
least `1 - ops.length * C.failureProb`, **every single operation** in `ops` executes within
`C.worstCaseTime` deterministic worst-case body instructions. -/
theorem seq_whp_ofFn (C : HighProbStateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (out : Fin r_ds) {x : Data r_ds} (ops : List D.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : D.ValidHistory s₀ ops) :
    ∃ (ν₀ : PMF (C.Seed × Data r_ds)) (τ_final : PMF (WhpSeqOutcome C.Seed D r_ds)),
      RandHaltsWithin w (P.initFresh.program out) ⟨0, x⟩ (C.initTime + 1) ∧
      evalRand w (P.initFresh.program out) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs out) p.2) ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs P.frontierReg = base + C.space ∧
        C.rep p.1 s₀ p.2 ∧
        Modifies (Block.mk base C.space).footprint x.mem p.2.mem) ∧
      C.ExecWhpSteps out ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, s₀, p.2⟩) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.current.state = (D.run s₀ ops).1 ∧
        tr.transcript = (D.run s₀ ops).2 ∧
        C.rep tr.current.seed (D.run s₀ ops).1 tr.current.data) ∧
      τ_final.toOuterMeasure {tr | C.worstCaseTime < tr.maxSteps} ≤
        (ops.length : ℝ≥0∞) * C.failureProb ∧
      1 - (ops.length : ℝ≥0∞) * C.failureProb ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ C.worstCaseTime ∧ tr.transcript = (D.run s₀ ops).2} := by
  have hv_rel : D.ValidOpSeq s₀ ops := (D.validOpSeq_iff_validHistory s₀ ops).mpr hv
  obtain ⟨ν₀, τ_final, hhalts₀, heval₀, hsupp₀, hex, hrep_fin, _, hfail, hsucc⟩ :=
    C.seq_whp out ops hx hfr hpar hz hv_rel
  have htr_eq := hex.transcript_eq_ofFn (s := s₀) (acc := []) fun tr htr => by
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨_, _, rfl⟩ := htr
    exact ⟨rfl, rfl⟩
  refine ⟨ν₀, τ_final, hhalts₀, heval₀, hsupp₀, hex, ?_, hfail, ?_⟩
  · intro tr htr
    obtain ⟨hs_tr, htrans_tr⟩ := htr_eq tr htr
    rw [List.nil_append] at htrans_tr
    exact ⟨hs_tr, htrans_tr, ⟨C.ghostRun C.ghostInit ops, hs_tr ▸ hrep_fin tr htr⟩⟩
  · refine hsucc.trans ?_
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun tr => ?_
    by_cases htr : tr ∈ τ_final.support
    · obtain ⟨_, htrans_tr⟩ := htr_eq tr htr
      rw [List.nil_append] at htrans_tr
      by_cases hle : tr.maxSteps ≤ C.worstCaseTime <;>
        simp [hle, htrans_tr]
    · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr htr]

/-- **Per-operation w.h.p. bound after an arbitrary-length oblivious prefix
(`reachable_step_whp_ofFn`).**
After executing *any* admissible oblivious prefix `ops` (regardless of `ops.length`), preparing the
next admissible operation `o` and running `P.code.program out` halts within `C.worstCaseTime + 1`
instructions in `evalRand` with probability at least `1 - C.failureProb`. -/
theorem reachable_step_whp_ofFn (C : HighProbStateTransitionImpl P D w base params s₀)
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (out : Fin r_ds) {x : Data r_ds} (ops : List D.Op) (o : D.Op)
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0)
    (hv : D.ValidHistory s₀ ops)
    (hvo : D.valid (D.run s₀ ops).1 o) :
    ∃ (ν₀ : PMF (C.Seed × Data r_ds)) (τ_pref : PMF (WhpSeqOutcome C.Seed D r_ds)),
      C.ExecWhpSteps out ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, s₀, p.2⟩) τ_pref ∧
      1 - C.failureProb ≤
        ((τ_pref.map fun tr => (tr.current.seed, tr.current.data)).bind fun p =>
          evalRand w (P.code.program out) (C.worstCaseTime + 1)
            ⟨0, C.prepare o p.2⟩).toOuterMeasure
          {cfg | ∃ (p : C.Seed × Data r_ds) (q : C.Seed × Data r_ds),
            p ∈ (τ_pref.map fun tr => (tr.current.seed, tr.current.data)).support ∧
            cfg = .halted (q.2.regs out) q.2 ∧
            C.decode o q.2.regs = some (D.stepFn (D.run s₀ ops).1 o).2 ∧
            C.rep q.1 (D.stepFn (D.run s₀ ops).1 o).1 q.2 ∧
            q.2.Bounded w ∧
            Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem} := by
  have hv_rel : D.ValidOpSeq s₀ ops := (D.validOpSeq_iff_validHistory s₀ ops).mpr hv
  obtain ⟨ν₀, τ_pref, -, -, -, hex, hrep_pref, hseed_pref, -, -⟩ :=
    C.seq_whp out ops hx hfr hpar hz hv_rel
  have htr_eq := hex.transcript_eq_ofFn (s := s₀) (acc := []) fun tr htr => by
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨_, _, rfl⟩ := htr
    exact ⟨rfl, rfl⟩
  let ν_cur : PMF (C.Seed × Data r_ds) :=
    τ_pref.map fun tr => (tr.current.seed, tr.current.data)
  have hseed_cur : ∀ θ, (ν_cur.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := by
    intro θ
    have heq : ν_cur.map Prod.fst = (τ_pref.map WhpSeqOutcome.current).map CoupledState.seed := by
      dsimp only [ν_cur]
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    rw [heq]
    exact hseed_pref θ
  have hrep_cur : ∀ p ∈ ν_cur.support,
      C.ghostRep (C.ghostRun C.ghostInit ops) p.1 (D.run s₀ ops).1 p.2 := by
    intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨tr, htr, rfl⟩ := hp
    have hs_eq := (htr_eq tr htr).1
    exact hs_eq ▸ hrep_pref tr htr
  have hstep := C.step_whp_ofFn out o ν_cur hvo hseed_cur hrep_cur
  refine ⟨ν₀, τ_pref, hex, hstep.trans (MeasureTheory.measure_mono fun cfg hcfg => ?_)⟩
  obtain ⟨p, q, hp, rfl, hdec, hgrep, hbdd, hmod⟩ := hcfg
  exact ⟨p, q, hp, rfl, hdec, ⟨_, hgrep⟩, hbdd, hmod⟩

/-- Polynomial-length sequence helper: when `ops.length ≤ max n_max 1 ^ c₀` and
`C.failureProb ≤ (max n_max 1 : ℝ≥0∞)⁻¹ ^ (c + c₀)`, the whole-sequence failure probability
`(ops.length : ℝ≥0∞) * C.failureProb` is at most `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem poly_seq_failureProb_le (C : HighProbStateTransitionImpl P D w base params s₀)
    {n_max c c₀ : ℕ} {ops : List D.Op}
    (hlen : ops.length ≤ max n_max 1 ^ c₀)
    (hfp : C.failureProb ≤ ((max n_max 1 : ℕ) : ℝ≥0∞)⁻¹ ^ (c + c₀)) :
    (ops.length : ℝ≥0∞) * C.failureProb ≤ ((max n_max 1 : ℕ) : ℝ≥0∞)⁻¹ ^ c := by
  set M : ℝ≥0∞ := ((max n_max 1 : ℕ) : ℝ≥0∞)
  have hM_ne_zero : M ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM_ne_top : M ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpow_ne_zero : M ^ c₀ ≠ 0 := pow_ne_zero c₀ hM_ne_zero
  have hpow_ne_top : M ^ c₀ ≠ ⊤ := ENNReal.pow_ne_top hM_ne_top
  have hlen_cast : (ops.length : ℝ≥0∞) ≤ M ^ c₀ := by
    dsimp only [M]
    exact_mod_cast hlen
  calc
    (ops.length : ℝ≥0∞) * C.failureProb
      ≤ (M ^ c₀) * (M⁻¹ ^ (c + c₀)) := mul_le_mul hlen_cast hfp zero_le zero_le
    _ = ((M ^ c₀) * (M⁻¹ ^ c₀)) * (M⁻¹ ^ c) := by
          rw [pow_add]
          ring
    _ = ((M ^ c₀) * (M ^ c₀)⁻¹) * (M⁻¹ ^ c) := by
          rw [ENNReal.inv_pow]
    _ = 1 * (M⁻¹ ^ c) := by
          rw [ENNReal.mul_inv_cancel hpow_ne_zero hpow_ne_top]
    _ = M⁻¹ ^ c := one_mul _

end Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl

end
