/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Classes.FPAUS.ExactSampler
public import CslibFrontier.Computability.Complexity.Classes.Oracle.ThresholdSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen

/-!
# Checked examples for threshold optimization and self-reducible exact sampling

Covers:
1. `MaxThresholdSpec` and `MinThresholdSpec` `TimeM` optimization and witness recovery on feasible,
   boundary, and infeasible instances, together with `computableInPolyTimeWithOracleQueries_bisect`
   on an exponentially large binary search range `[0, 2 ^ n)`.
2. `MaxSAT` threshold optimization and variable-by-variable optimal witness recovery on an
   unsatisfiable 4-clause 2-CNF (`maxClauseScore = 3`), the empty formula (`maxClauseScore = 0`),
   and a formula with gapped/repeated variable labels, plus `MaxSATThreshold ∈ NP`,
   `solveMaxSATProgram_query_bounds`, `computableInPolyTimeWithOracleQueries_solveMaxSAT`, and
   `computableInPolyTime_solveMaxSAT_of_mem_P`.
3. `SelfReducible.exactSample`, `SelfReducible.boundedConditionalSample`, and
   `SelfReducible.boundedConditionalOracleSample` on a non-dyadic weight-at-most-1 witness family
   (`|W ⟨2, true, true⟩| = 3`), dead instances (`W x = ∅`), and zero-length witnesses
   (`W x = {[]}`), verifying exact `1 / 3` witness probabilities, `≤ 1 + len x` counter queries,
   expected fair-flip bounds (`exactSampleExpectedBits_le` with `uniformFinTree` draws and
   `expectedCost_sampleFinBounded_le`), `IsFPAUS`, `FPAUS` membership, and `IsOraclePPTOn`
   lifting.
-/

public section

open scoped ENNReal

namespace CslibFrontierTests.ThresholdAndExactSampling

open Cslib Cslib.Algorithms.Lean Cslib.Complexity Cslib.Logic.PL
  Cslib.Probability Turing.MultiTapeTM

/-! ### 1. `TimeM` maximization, minimization, and exponential-range oracle bisection -/

/-- Bounded maximization spec: on upper cap `B`, valid witnesses are `w ≤ min B 7` when `0 < B`
(and none when `B = 0`), with score `w`. -/
def capMaxSpec : MaxThresholdSpec ℕ ℕ where
  valid B w := 0 < B ∧ w ≤ min B 7
  score _ w := w
  bound B := B
  score_le_bound B _ h := h.2.trans (min_le_left B 7)

/-- Unit-cost threshold probe for `capMaxSpec`. -/
def capMaxProbe (B q : ℕ) : TimeM ℕ Bool :=
  ⟨decide (0 < B ∧ q ≤ min B 7), 1⟩

/-- Constant-cost witness finder at threshold `q` for `capMaxSpec`. -/
def capMaxFinder (B _q : ℕ) : TimeM ℕ ℕ :=
  ⟨min B 7, 1⟩

theorem capMaxProbe_iff (B q : ℕ) :
    (capMaxProbe B q).ret = true ↔ capMaxSpec.atLeast B q := by
  simp only [capMaxProbe, decide_eq_true_eq, capMaxSpec, MaxThresholdSpec.atLeast]
  exact ⟨fun ⟨hB, hq⟩ => ⟨min B 7, ⟨hB, le_refl _⟩, hq⟩,
    fun ⟨_, ⟨hB, hw⟩, hq⟩ => ⟨hB, hq.trans hw⟩⟩

/-- On `B = 10`, `maxOptWitnessM` recovers `optValue = 7` and `witness = 7` in at most `5` ticks. -/
theorem capMax_ten_eval :
    (capMaxSpec.maxOptWitnessM capMaxProbe capMaxFinder 10).ret = some ⟨7, 7⟩ ∧
      (capMaxSpec.maxOptWitnessM capMaxProbe capMaxFinder 10).time ≤ 5 := by
  have hprobe : ∀ q, q ≤ capMaxSpec.bound 10 →
      ((capMaxProbe 10 q).ret = true ↔ capMaxSpec.atLeast 10 q) := fun q _ => capMaxProbe_iff 10 q
  have hwit : ∀ q, q ≤ capMaxSpec.bound 10 → capMaxSpec.atLeast 10 q →
      capMaxSpec.valid 10 (capMaxFinder 10 q).ret ∧
        q ≤ capMaxSpec.score 10 (capMaxFinder 10 q).ret := by
    rintro q _ ⟨w, ⟨_, hw⟩, hq⟩
    exact ⟨⟨by decide, le_refl _⟩, hq.trans hw⟩
  obtain ⟨hnone, hsome⟩ := capMaxSpec.maxOptWitnessM_spec hprobe hwit
  have htime := capMaxSpec.maxOptWitnessM_time_le capMaxProbe capMaxFinder (cp := 1) (cw := 1)
    (fun _ => le_refl 1) (fun _ _ => le_refl 1) hprobe
  have ht5 : 1 * (Nat.log 2 (capMaxSpec.bound 10 + 1) + 1) + 1 = 5 := by decide
  refine ⟨?_, htime.trans_eq ht5⟩
  cases hret : (capMaxSpec.maxOptWitnessM capMaxProbe capMaxFinder 10).ret with
  | none => exact False.elim (hnone.mp hret ⟨7, by decide, by decide⟩)
  | some sol =>
    rcases sol with ⟨v, w⟩
    obtain ⟨_, ⟨_, hw7⟩, hsc, hmax⟩ := hsome ⟨v, w⟩ hret
    have h7 : 7 ≤ v := hmax 7 ⟨by decide, by decide⟩
    simp only [capMaxSpec] at hw7 hsc h7
    congr 1
    congr <;> omega

/-- On infeasible `B = 0`, `maxOptWitnessM` returns `none`. -/
theorem capMax_infeasible_eval :
    (capMaxSpec.maxOptWitnessM capMaxProbe capMaxFinder 0).ret = none :=
  (capMaxSpec.maxOptWitnessM_spec (fun q _ => capMaxProbe_iff 0 q)
    (fun _ _ ⟨_, ⟨h0, _⟩, _⟩ => by omega)).1.mpr
    (fun ⟨_, h0, _⟩ => by omega)

/-- Bounded minimization spec: on target floor `L`, valid witnesses are `L ≤ w ≤ 12`, with cost `w`
bounded by `12`. -/
def floorMinSpec : MinThresholdSpec ℕ ℕ where
  valid L w := L ≤ w ∧ w ≤ 12
  cost _ w := w
  bound _ := 12
  cost_le_bound _ _ h := h.2

/-- Unit-cost threshold probe for `floorMinSpec`. -/
def floorMinProbe (L q : ℕ) : TimeM ℕ Bool :=
  ⟨decide (L ≤ 12 ∧ L ≤ q), 1⟩

/-- Witness finder at threshold `q` for `floorMinSpec`. -/
def floorMinFinder (L _q : ℕ) : TimeM ℕ ℕ :=
  ⟨L, 1⟩

theorem floorMinProbe_iff (L q : ℕ) :
    (floorMinProbe L q).ret = true ↔ floorMinSpec.atMost L q := by
  simp only [floorMinProbe, decide_eq_true_eq, floorMinSpec, MinThresholdSpec.atMost]
  exact ⟨fun ⟨h12, hq⟩ => ⟨L, ⟨le_refl L, h12⟩, hq⟩,
    fun ⟨_, ⟨hL, h12⟩, hq⟩ => ⟨hL.trans h12, hL.trans hq⟩⟩

/-- On `L = 5`, `minOptWitnessM` recovers minimum cost `5` and witness `5` in at most `5` ticks. -/
theorem floorMin_five_eval :
    (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 5).ret = some ⟨5, 5⟩ ∧
      (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 5).time ≤ 5 := by
  have hprobe : ∀ q, q ≤ floorMinSpec.bound 5 →
      ((floorMinProbe 5 q).ret = true ↔ floorMinSpec.atMost 5 q) := fun q _ => floorMinProbe_iff 5 q
  have hwit : ∀ q, q ≤ floorMinSpec.bound 5 → floorMinSpec.atMost 5 q →
      floorMinSpec.valid 5 (floorMinFinder 5 q).ret ∧
        floorMinSpec.cost 5 (floorMinFinder 5 q).ret ≤ q := by
    rintro q _ ⟨w, ⟨h5, _⟩, hq⟩
    dsimp only [floorMinSpec, floorMinFinder] at h5 ⊢
    exact ⟨⟨le_refl 5, by decide⟩, h5.trans hq⟩
  obtain ⟨hnone, hsome⟩ := floorMinSpec.minOptWitnessM_spec hprobe hwit
  have htime := floorMinSpec.minOptWitnessM_time_le floorMinProbe floorMinFinder
    (x := 5) (cp := 1) (cw := 1) (fun _ => le_refl 1) (fun _ _ => le_refl 1)
  have ht5 : 1 * (Nat.log 2 (floorMinSpec.bound 5 + 1) + 1) + 1 = 5 := by decide
  refine ⟨?_, htime.trans_eq ht5⟩
  cases hret : (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 5).ret with
  | none => exact False.elim (hnone.mp hret ⟨5, le_refl 5, by decide⟩)
  | some sol =>
    rcases sol with ⟨v, w⟩
    obtain ⟨_, ⟨h5w, _⟩, hcost, hmin⟩ := hsome ⟨v, w⟩ hret
    have hv5 : v ≤ 5 := hmin 5 ⟨le_refl 5, by decide⟩
    dsimp only [floorMinSpec] at h5w hcost hv5
    congr 1
    congr <;> omega

/-- On zero-cost `L = 0`, `minOptWitnessM` recovers minimum cost `0` and witness `0`. -/
theorem floorMin_zero_eval :
    (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 0).ret = some ⟨0, 0⟩ := by
  have hprobe : ∀ q, q ≤ floorMinSpec.bound 0 →
      ((floorMinProbe 0 q).ret = true ↔ floorMinSpec.atMost 0 q) := fun q _ => floorMinProbe_iff 0 q
  have hwit : ∀ q, q ≤ floorMinSpec.bound 0 → floorMinSpec.atMost 0 q →
      floorMinSpec.valid 0 (floorMinFinder 0 q).ret ∧
        floorMinSpec.cost 0 (floorMinFinder 0 q).ret ≤ q := by
    intro q _ _
    dsimp only [floorMinSpec, floorMinFinder]
    exact ⟨⟨le_refl 0, by decide⟩, Nat.zero_le q⟩
  obtain ⟨hnone, hsome⟩ := floorMinSpec.minOptWitnessM_spec hprobe hwit
  cases hret : (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 0).ret with
  | none => exact False.elim (hnone.mp hret ⟨0, le_refl 0, by decide⟩)
  | some sol =>
    rcases sol with ⟨v, w⟩
    obtain ⟨_, _, hcost, hmin⟩ := hsome ⟨v, w⟩ hret
    have hv0 : v ≤ 0 := hmin 0 ⟨le_refl 0, by decide⟩
    dsimp only [floorMinSpec] at hcost hv0
    congr 1
    congr <;> omega

/-- On infeasible `L = 15 > 12`, `minOptWitnessM` returns `none`. -/
theorem floorMin_infeasible_eval :
    (floorMinSpec.minOptWitnessM floorMinProbe floorMinFinder 15).ret = none :=
  (floorMinSpec.minOptWitnessM_spec (fun q _ => floorMinProbe_iff 15 q)
    (fun _ _ ⟨_, ⟨h1, h2⟩, _⟩ => by omega)).1.mpr
    (fun ⟨_, h1, h2⟩ => by omega)

open Classical in
/-- Oracle bisection over an exponentially large binary range `[0, 2 ^ n)` (with `n` in unary)
runs in polynomial time and makes at most `n + 1` oracle requests. -/
theorem expRange_bisect_oracleQueries (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun n => n + 1)
      (fun n : ℕ =>
        ((bisectStep (fun m => decide (encNat m ∈ A)))^[(2 ^ n - 0).size] ⟨0, 2 ^ n⟩).lo)
      encUnary encNat := by
  open ComputableInPolyTime in
  have hreq : ComputableInPolyTime (fun q : OracleThresholdQuery ℕ => encNat q.target)
      (encOracleThresholdQuery encUnary) encBits :=
    (encOracleThresholdQuery_target_polyTime id').encoding_comp
  refine computableInPolyTimeWithOracleQueries_bisect A (req := fun _ m => encNat m)
    hreq (const 0) binary_two_pow fun n => ?_
  simp only [Nat.sub_zero, encUnary_apply, List.length_replicate]
  exact Nat.size_le.mpr (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n))

/-! ### 2. `MaxSAT` threshold optimization and witness recovery -/

/-- Unsatisfiable 4-clause 2-CNF over variables `0, 1`: at most `3` clauses can be satisfied. -/
def unsatFour : CNF ℕ :=
  [[(0, true), (1, true)],
   [(0, true), (1, false)],
   [(0, false), (1, true)],
   [(0, false), (1, false)]]

theorem maxClauseScore_unsatFour : MaxSAT.maxClauseScore unsatFour = 3 := by
  obtain ⟨_, ⟨σ, hσ_eq⟩, hle⟩ := MaxSAT.maxClauseScore_spec unsatFour
  have hge3 : 3 ≤ MaxSAT.maxClauseScore unsatFour := by
    have h0 : unsatFour.countP (Clause.eval (fun _ => false)) = 3 := by decide
    simpa [h0] using hle (fun _ => false)
  have hlt4 : MaxSAT.maxClauseScore unsatFour < 4 := by
    by_contra! hge4
    have h4 : unsatFour.countP (Clause.eval σ) = 4 := by
      have := List.countP_le_length (p := Clause.eval σ) (l := unsatFour)
      change unsatFour.countP (Clause.eval σ) ≤ 4 at this
      omega
    cases hb0 : σ 0 <;> cases hb1 : σ 1 <;>
      · have hval : unsatFour.countP (Clause.eval (fun v => if v = 0 then σ 0 else σ 1)) = 3 := by
          rw [hb0, hb1]; decide
        have hcongr : unsatFour.countP (Clause.eval σ) =
            unsatFour.countP (Clause.eval (fun v => if v = 0 then σ 0 else σ 1)) :=
          Cslib.Logic.PL.CNF.countP_eval_congr fun v hv => by
            have hv01 : v = 0 ∨ v = 1 := by
              revert v hv; decide
            rcases hv01 with rfl | rfl <;> simp
        omega
  omega

/-- End-to-end `solveMaxSAT` on `unsatFour`: recovers `optValue = 3`, a witness assignment
satisfying `3` clauses, and makes at most `5 = 4.size + 2` oracle requests. -/
theorem solveMaxSAT_unsatFour_end_to_end :
    let A := encMaxSATQuery '' MaxSATThreshold
    let sol := MaxSAT.solveMaxSAT A unsatFour
    sol.optValue = 3 ∧
      unsatFour.countP (Clause.eval (SAT.assignment unsatFour sol.assignmentBits)) = 3 ∧
      (OracleComp.queriesWith (languageOracle A) (MaxSAT.solveMaxSATProgram unsatFour)).length ≤
        5 := by
  have hspec := MaxSAT.solveMaxSAT_spec unsatFour
  have hqb := (MaxSAT.solveMaxSATProgram_query_bounds
    (languageOracle (encMaxSATQuery '' MaxSATThreshold)) unsatFour).1
  have hsz : unsatFour.length.size + unsatFour.numVars = 5 := by decide
  rw [maxClauseScore_unsatFour] at hspec
  exact ⟨hspec.1, hspec.2.1, hqb.trans_eq hsz⟩

theorem solveMaxSAT_empty_end_to_end :
    (MaxSAT.solveMaxSAT (encMaxSATQuery '' MaxSATThreshold) []).optValue = 0 := by
  have hspec := (MaxSAT.solveMaxSAT_spec []).1
  have h0 : MaxSAT.maxClauseScore [] = 0 := by simpa using (MaxSAT.maxClauseScore_spec []).1
  exact hspec.trans h0

/-- Formula with repeated and gapped variable labels (`5` and `12`). -/
def gappedCNF : CNF ℕ :=
  [[(5, true), (5, true)], [(12, false)], [(5, false)]]

theorem gappedCNF_numVars_and_query_bound (answer : Unit × List Bool → List Bool) :
    gappedCNF.numVars = 2 ∧ gappedCNF.vars.length = 4 ∧
      (OracleComp.queriesWith answer (MaxSAT.solveMaxSATProgram gappedCNF)).length ≤ 4 := by
  have h1 : gappedCNF.numVars = 2 ∧ gappedCNF.vars.length = 4 := by decide
  have h2 := (MaxSAT.solveMaxSATProgram_query_bounds answer gappedCNF).1
  have h3 : gappedCNF.length.size + gappedCNF.numVars = 4 := by decide
  exact ⟨h1.1, h1.2, h2.trans_eq h3⟩

theorem check_MaxSAT_complexity_theorems (A : Set (List Bool))
    (hP : encMaxSATQuery '' MaxSATThreshold ∈ P encBits) :
    MaxSATThreshold ∈ NP encMaxSATQuery ∧
      ComputableInPolyTimeWithOracleQueries A (fun n => 2 * n + 1)
        (MaxSAT.solveMaxSAT A) encCNF encMaxSATSolution ∧
      ComputableInPolyTime
        (MaxSAT.solveMaxSAT (encMaxSATQuery '' MaxSATThreshold))
        encCNF encMaxSATSolution :=
  ⟨MaxSAT.mem_NP_threshold,
   MaxSAT.computableInPolyTimeWithOracleQueries_solveMaxSAT A,
   MaxSAT.computableInPolyTime_solveMaxSAT_of_mem_P hP⟩

/-! ### 3. Self-reducible non-dyadic witness family (`|W ⟨2, true, true⟩| = 3`) -/

/-- Instance of the weight-at-most-1 witness family: bitstrings of length `remLen` with at most one
`true` bit when `canUseOne = true` (at most zero when `canUseOne = false`), and `∅` when
`alive = false`. -/
structure HammingOneCap where
  /-- Remaining witness bit length (encoded in unary). -/
  remLen : ℕ
  /-- Whether one `true` bit is still allowed. -/
  canUseOne : Bool
  /-- Whether the branch is feasible. -/
  alive : Bool
  deriving DecidableEq, Repr

/-- Encoding of `HammingOneCap`. -/
enc_structure encHammingOneCap : HammingOneCap where
  remLen : encUnary, canUseOne : encBool, alive : encBool

/-- All bitstrings of length `n` with at most `1` (or `0`) `true` bits. -/
def hammingOneList : ℕ → Bool → List (List Bool)
  | 0, _ => [[]]
  | n + 1, false => (hammingOneList n false).map (false :: ·)
  | n + 1, true =>
    (hammingOneList n true).map (false :: ·) ++ (hammingOneList n false).map (true :: ·)

/-- Witness Finset of a `HammingOneCap` instance. -/
def hammingOneWitness (x : HammingOneCap) : Finset (List Bool) :=
  if x.alive then (hammingOneList x.remLen x.canUseOne).toFinset else ∅

theorem mem_hammingOneList_iff {n : ℕ} {canOne : Bool} {w : List Bool} :
    w ∈ hammingOneList n canOne ↔
      w.length = n ∧ w.count true ≤ (if canOne then 1 else 0) := by
  induction n generalizing canOne w with
  | zero =>
    simp only [hammingOneList, List.mem_singleton, List.length_eq_zero_iff]
    exact ⟨fun h => by subst h; simp, fun ⟨h, _⟩ => h⟩
  | succ m ih =>
    cases canOne
    · simp only [hammingOneList, List.mem_map, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨hl, hc⟩ := ih.mp hu
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        exact ⟨by simp [hl], by simpa [List.count_cons_of_ne Bool.false_ne_true] using hc⟩
      · rintro ⟨hl, hc⟩
        rcases w with _ | ⟨false | true, u⟩
        · simp at hl
        · exact ⟨u, ih.mpr ⟨by simpa using hl,
            by simpa [List.count_cons_of_ne Bool.false_ne_true] using hc⟩, rfl⟩
        · simp [List.count_cons_self] at hc
    · simp only [hammingOneList, List.mem_append, List.mem_map, ↓reduceIte]
      constructor
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
        · obtain ⟨hl, hc⟩ := ih.mp hu
          simp only [↓reduceIte] at hc
          exact ⟨by simp [hl], by simpa [List.count_cons_of_ne Bool.false_ne_true] using hc⟩
        · obtain ⟨hl, hc⟩ := ih.mp hu
          simp only [Bool.false_eq_true, ↓reduceIte] at hc
          refine ⟨by simp [hl], ?_⟩
          rw [List.count_cons_self]
          omega
      · rintro ⟨hl, hc⟩
        rcases w with _ | ⟨false | true, u⟩
        · simp at hl
        · left
          exact ⟨u, ih.mpr ⟨by simpa using hl,
            by simpa [List.count_cons_of_ne Bool.false_ne_true] using hc⟩, rfl⟩
        · right
          rw [List.count_cons_self] at hc
          exact ⟨u, ih.mpr ⟨by simpa using hl,
            by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩, rfl⟩

theorem nodup_hammingOneList : ∀ (n : ℕ) (canOne : Bool), (hammingOneList n canOne).Nodup
  | 0, _ => by simp [hammingOneList]
  | n + 1, false =>
    (nodup_hammingOneList n false).map (fun _ _ h => by injection h)
  | n + 1, true => by
    simp only [hammingOneList]
    refine List.nodup_append.mpr
      ⟨(nodup_hammingOneList n true).map (fun _ _ h => by injection h),
       (nodup_hammingOneList n false).map (fun _ _ h => by injection h), ?_⟩
    intro v₁ hv0 v₂ hv1 heq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv0
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv1
    cases heq

theorem length_hammingOneList : ∀ (n : ℕ) (canOne : Bool),
    (hammingOneList n canOne).length = if canOne then n + 1 else 1
  | 0, canOne => by cases canOne <;> rfl
  | n + 1, false => by simp [hammingOneList, length_hammingOneList n false]
  | n + 1, true => by
    simp [hammingOneList, length_hammingOneList n true, length_hammingOneList n false]

/-- Closed-form exact witness counter for `HammingOneCap`. -/
def hammingOneCount (x : HammingOneCap) : ℕ :=
  if x.alive then (if x.canUseOne then x.remLen + 1 else 1) else 0

theorem hammingOneCount_eq_card (x : HammingOneCap) :
    hammingOneCount x = (hammingOneWitness x).card := by
  simp only [hammingOneCount, hammingOneWitness]
  cases x.alive
  · simp
  · simp only [↓reduceIte, List.toFinset_card_of_nodup (nodup_hammingOneList _ _),
      length_hammingOneList]

open ComputableInPolyTime in
theorem computableInPolyTime_hammingOneCount :
    ComputableInPolyTime hammingOneCount encHammingOneCap encNat := by
  have hr := unary_to_binary.comp (encHammingOneCap_remLen_polyTime id')
  have h1 := binary_add' hr (const 1)
  have hcan : ComputableInPolyTime (fun x : HammingOneCap => decide (x.canUseOne = true))
      encHammingOneCap encBool :=
    (encHammingOneCap_canUseOne_polyTime id').of_enc_eq fun ⟨_, canOne, _⟩ => by
      cases canOne <;> rfl
  have hal : ComputableInPolyTime (fun x : HammingOneCap => decide (x.alive = true))
      encHammingOneCap encBool :=
    (encHammingOneCap_alive_polyTime id').of_enc_eq fun ⟨_, _, al⟩ => by
      cases al <;> rfl
  have hinner := ComputableInPolyTime.ite' (c := fun x : HammingOneCap => x.canUseOne = true)
    hcan h1 (const 1)
  exact (ComputableInPolyTime.ite' (c := fun x : HammingOneCap => x.alive = true)
    hal hinner (const 0)).of_enc_eq fun ⟨_, canOne, al⟩ => by
    cases al <;> cases canOne <;> rfl

/-- Child transition of `HammingOneCap`. -/
def hammingOneChild (x : HammingOneCap) (b : Bool) : HammingOneCap :=
  if b then
    if x.canUseOne then ⟨x.remLen - 1, false, x.alive⟩
    else ⟨x.remLen - 1, false, false⟩
  else ⟨x.remLen - 1, x.canUseOne, x.alive⟩

/-- `hammingOneWitness` is self-reducible under `encHammingOneCap`. -/
def hammingOneSelfReducible : SelfReducible encHammingOneCap hammingOneWitness where
  len x := x.remLen
  child := hammingOneChild
  length_eq x w hw := by
    simp only [hammingOneWitness] at hw
    split_ifs at hw
    · exact (mem_hammingOneList_iff.mp (List.mem_toFinset.mp hw)).1
    · simp at hw
  cons_mem_iff x hx b w := by
    rcases x with ⟨rem, false | true, false | true⟩
    · cases b <;> simp [hammingOneWitness, hammingOneChild]
    · cases b
      · simp only [hammingOneWitness, hammingOneChild, Bool.false_eq_true, ↓reduceIte,
          List.mem_toFinset, mem_hammingOneList_iff, List.length_cons,
          List.count_cons_of_ne Bool.false_ne_true]
        change 0 < rem at hx
        omega
      · simp [hammingOneWitness, hammingOneChild, mem_hammingOneList_iff, List.count_cons_self]
    · cases b <;> simp [hammingOneWitness, hammingOneChild]
    · cases b
      · simp only [hammingOneWitness, hammingOneChild, Bool.false_eq_true, ↓reduceIte,
          List.mem_toFinset, mem_hammingOneList_iff, List.length_cons,
          List.count_cons_of_ne Bool.false_ne_true]
        change 0 < rem at hx
        omega
      · simp only [hammingOneWitness, hammingOneChild, ↓reduceIte, List.mem_toFinset,
          mem_hammingOneList_iff, List.length_cons, List.count_cons_self, Bool.false_eq_true]
        change 0 < rem at hx
        omega
  len_child x _ b := by
    rcases x with ⟨rem, false | true, false | true⟩ <;> cases b <;> rfl
  length_child_le x _ b := by
    rcases x with ⟨rem, false | true, false | true⟩ <;> cases b <;>
      · simp only [hammingOneChild, ↓reduceIte, Bool.false_eq_true, encHammingOneCap_apply,
          encHammingOneCapFields]
        have h1 : rem - 1 ≤ rem := Nat.sub_le _ _
        enc_len
  len_polytime := by fun_prop
  child_polytime := by
    open ComputableInPolyTime in
    have hx := fst encHammingOneCap encBool
    have hb : ComputableInPolyTime (fun p : HammingOneCap × Bool => decide (p.2 = true))
        (encPair encHammingOneCap encBool) encBool :=
      (snd encHammingOneCap encBool).of_enc_eq fun ⟨_, b⟩ => by cases b <;> rfl
    have hr1 := unary_sub' (encHammingOneCap_remLen_polyTime hx) (const 1)
    have hcan_b := encHammingOneCap_canUseOne_polyTime hx
    have hcan : ComputableInPolyTime (fun p : HammingOneCap × Bool => decide (p.1.canUseOne = true))
        (encPair encHammingOneCap encBool) encBool :=
      hcan_b.of_enc_eq fun ⟨⟨_, canOne, _⟩, _⟩ => by cases canOne <;> rfl
    have hal := encHammingOneCap_alive_polyTime hx
    have hfalse := encHammingOneCap_mk_polyTime hr1 hcan_b hal
    have htrueYes := encHammingOneCap_mk_polyTime hr1 (const false) hal
    have htrueNo := encHammingOneCap_mk_polyTime hr1 (const false) (const false)
    have htrue := ComputableInPolyTime.ite'
      (c := fun p : HammingOneCap × Bool => p.1.canUseOne = true)
      hcan htrueYes htrueNo
    exact (ComputableInPolyTime.ite' (c := fun p : HammingOneCap × Bool => p.2 = true)
      hb htrue hfalse).of_enc_eq fun ⟨⟨_, canOne, _⟩, b⟩ => by
      cases b <;> cases canOne <;> rfl
  nil_mem_polytime := by
    open ComputableInPolyTime in
    have h := bool_and' (encHammingOneCap_alive_polyTime id')
      (decide_eq' (encB := encUnary) (encHammingOneCap_remLen_polyTime id') (const 0))
    refine h.of_enc_eq fun ⟨rem, canOne, al⟩ => ?_
    dsimp only [Function.comp]
    congr 1
    apply Bool.eq_iff_iff.mpr
    cases al
    · simp [hammingOneWitness]
    · simp only [hammingOneWitness, ↓reduceIte, List.mem_toFinset, mem_hammingOneList_iff,
        List.length_nil, List.count_nil, zero_le, and_true, Bool.true_and, decide_eq_true_eq]
      exact eq_comm

/-- Non-dyadic test instance `⟨2, true, true⟩` has exactly `3` witnesses. -/
def nonDyadicInst : HammingOneCap := ⟨2, true, true⟩

theorem card_hammingOneWitness_nonDyadic : (hammingOneWitness nonDyadicInst).card = 3 := by
  decide

/-- Exact conditional sampling on `nonDyadicInst` assigns probability `(3 : ℝ≥0∞)⁻¹` to each of
the three valid witnesses `[false, false]`, `[false, true]`, `[true, false]`, and `0` to
`[true, true]` and `none`. -/
theorem exactSample_nonDyadic_probs :
    let μ := hammingOneSelfReducible.exactSample hammingOneCount
      (fun n _ => PMF.uniformOfFintype (Fin n)) nonDyadicInst
    μ (some [false, false]) = (3 : ℝ≥0∞)⁻¹ ∧
      μ (some [false, true]) = (3 : ℝ≥0∞)⁻¹ ∧
      μ (some [true, false]) = (3 : ℝ≥0∞)⁻¹ ∧
      μ (some [true, true]) = 0 ∧
      μ none = 0 := by
  have heq := hammingOneSelfReducible.exactSample_eq_uniformWitness
    (count := hammingOneCount) (fun _ _ => rfl) (x := nonDyadicInst)
    (fun z _ => hammingOneCount_eq_card z)
  have hne : (hammingOneWitness nonDyadicInst).Nonempty := by
    rw [← Finset.card_pos, card_hammingOneWitness_nonDyadic]; omega
  have hmem00 : [false, false] ∈ hammingOneWitness nonDyadicInst := by decide
  have hmem01 : [false, true] ∈ hammingOneWitness nonDyadicInst := by decide
  have hmem10 : [true, false] ∈ hammingOneWitness nonDyadicInst := by decide
  have hnot11 : [true, true] ∉ hammingOneWitness nonDyadicInst := by decide
  dsimp only
  rw [heq, uniformWitness_of_nonempty hne]
  have hval : ∀ w,
      ((PMF.uniformOfFinset (hammingOneWitness nonDyadicInst) hne).map some) (some w) =
        if w ∈ hammingOneWitness nonDyadicInst then (3 : ℝ≥0∞)⁻¹ else 0 := by
    intro w
    rw [PMF.map_apply]
    by_cases hw : w ∈ hammingOneWitness nonDyadicInst
    · rw [ite_eq_left hw, tsum_eq_single w]
      · simp [PMF.uniformOfFinset_apply, hw, card_hammingOneWitness_nonDyadic]
      · intro v hv; simp [hv.symm]
    · rw [ite_eq_right hw]
      refine tsum_eq_zero_iff.mpr fun v => ?_
      by_cases hvw : w = v
      · subst hvw; simp [PMF.uniformOfFinset_apply, hw]
      · simp [hvw]
  have hnone : ((PMF.uniformOfFinset (hammingOneWitness nonDyadicInst) hne).map some) none = 0 := by
    rw [PMF.map_apply]
    exact tsum_eq_zero_iff.mpr fun _ => by simp
  refine ⟨?_, ?_, ?_, ?_, hnone⟩
  · rw [hval, ite_eq_left hmem00]
  · rw [hval, ite_eq_left hmem01]
  · rw [hval, ite_eq_left hmem10]
  · rw [hval, ite_eq_right hnot11]

/-- Dead (`⟨2, true, false⟩`) and zero-length (`⟨0, true, true⟩`) corner cases, plus query count
`3 = 1 + 2` on `nonDyadicInst`. -/
theorem exactSample_corner_cases :
    hammingOneSelfReducible.exactSample hammingOneCount
      (fun n _ => PMF.uniformOfFintype (Fin n)) ⟨2, true, false⟩ = PMF.pure none ∧
    hammingOneSelfReducible.exactSample hammingOneCount
      (fun n _ => PMF.uniformOfFintype (Fin n)) ⟨0, true, true⟩ = PMF.pure (some []) ∧
    (hammingOneSelfReducible.exactSampleQueries hammingOneCount ⟨2, true, false⟩ [0, 0]).length =
      1 ∧
    (hammingOneSelfReducible.exactSampleQueries hammingOneCount nonDyadicInst [0, 0]).length =
      3 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · have heq := hammingOneSelfReducible.exactSample_eq_uniformWitness
      (count := hammingOneCount) (fun _ _ => rfl) (x := ⟨2, true, false⟩)
      (fun z _ => hammingOneCount_eq_card z)
    have hemp : hammingOneWitness ⟨2, true, false⟩ = ∅ := rfl
    rw [heq, hemp, uniformWitness_empty]
  · have heq := hammingOneSelfReducible.exactSample_eq_uniformWitness
      (count := hammingOneCount) (fun _ _ => rfl) (x := ⟨0, true, true⟩)
      (fun z _ => hammingOneCount_eq_card z)
    have hsing : hammingOneWitness ⟨0, true, true⟩ = {[]} := rfl
    rw [heq, hsing, uniformWitness_of_nonempty (Finset.singleton_nonempty [])]
    ext o
    rw [PMF.map_apply, PMF.pure_apply]
    cases o with
    | none => simp
    | some w =>
      by_cases hw : w = []
      · subst hw
        rw [ite_eq_left rfl, tsum_eq_single []]
        · simp [PMF.uniformOfFinset_apply]
        · intro v hv; simp [hv.symm]
      · rw [ite_eq_right (by simp [hw])]
        refine tsum_eq_zero_iff.mpr fun v => ?_
        by_cases hvw : w = v
        · subst hvw; simp [PMF.uniformOfFinset_apply, hw]
        · simp [hvw]

/-- End-to-end `IsFPAUS`, `FPAUS` membership, and `IsOraclePPTOn` lifting on `HammingOneCap`. -/
theorem hammingOne_fpaus_and_oracle_lift (A : Set (List Bool)) :
    IsFPAUS encHammingOneCap hammingOneWitness
      (hammingOneSelfReducible.boundedConditionalSample hammingOneCount) ∧
    hammingOneWitness ∈ FPAUS encHammingOneCap ∧
    ∃ sampler : HammingOneCap → ℕ → WordOracleComp Unit (Option (List Bool)),
      IsOraclePPTOn (encPair encHammingOneCap encUnary) (encOption encBits)
        (Function.uncurry sampler) ∧
      ∀ x q, CloseTo
        (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun req => PMF.pure (languageOracle A req)))
          (sampler x q))
        (uniformWitness (hammingOneWitness x))
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) :=
  ⟨hammingOneSelfReducible.isFPAUS_boundedConditionalSample
      computableInPolyTime_hammingOneCount hammingOneCount_eq_card,
   hammingOneSelfReducible.mem_FPAUS_of_exact_polyTime_count
      computableInPolyTime_hammingOneCount hammingOneCount_eq_card,
   hammingOneSelfReducible.exists_oraclePPTSampler_of_oracle_count A
      (computableInPolyTime_hammingOneCount.computableInPolyTimeWithOracle A)
      hammingOneCount_eq_card⟩

/-- Expected fair-flip bounds: with `Probability.uniformFinTree` draws, the exact walk on
`nonDyadicInst` (`len = 2`) uses at most `2 * 3` expected flips and none on the dead instance
`⟨2, true, false⟩`, and one capped rejection step on `[0, 3)` costs at most `2 * Nat.size 3`
expected fair coins. -/
theorem hammingOne_expected_flips :
    hammingOneSelfReducible.exactSampleExpectedBits hammingOneCount nonDyadicInst ≤ 2 * (2 + 1) ∧
    hammingOneSelfReducible.exactSampleExpectedBits hammingOneCount ⟨2, true, false⟩ = 0 ∧
    OracleComp.expectedCost ProbComp.unifOracle (fun _ => 1) (sampleFinBounded 3 5) ≤
      2 * (Nat.size 3 : ℝ≥0∞) := by
  have h := hammingOneSelfReducible.exactSampleExpectedBits_le (count := hammingOneCount)
    (x := nonDyadicInst) (fun z _ => hammingOneCount_eq_card z)
  have h' := hammingOneSelfReducible.exactSampleExpectedBits_le (count := hammingOneCount)
    (x := ⟨2, true, false⟩) (fun z _ => hammingOneCount_eq_card z)
  refine ⟨?_, h'.1 rfl, expectedCost_sampleFinBounded_le 3 5⟩
  have hlen : hammingOneSelfReducible.len nonDyadicInst = 2 := rfl
  rw [hlen] at h
  exact_mod_cast h.2

end CslibFrontierTests.ThresholdAndExactSampling
