/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects
public import Complexity.Foundations.Optimization.FiniteMinPlus.Cached
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# Arithmetic operations for fixed-effects auditing

Executable cached group curves for [XuGaoHu2027], Theorem 4.1 and Algorithm 1
(PDF pp. 9, 21). Scores are computed from running sums rather than repeated
centering. Compression retains an actual best subset at each deletion count.
The arithmetic RAM model counts rational arithmetic/comparison, natural index
arithmetic, constant-size records, list cons and array reads/writes. Rational
bit complexity and sorting ungrouped input are separate. Input here is already
grouped; an arbitrary number of empty input groups cannot be read in O(n) time.
A score-pair addition/comparison is one RAM operation; expanding it to rational
scalar operations changes the constants by at most three. List-length traversals
and copying the recovered observations are charged. This is a count in this
explicit arithmetic model, not a claim about the Lean compiler or allocator.

The implementation scans each cached subset list once per group deletion count;
it does not claim the sharper O(2^ng) per-group Gray-code bound. Its proved
O(ng 2^ng) group work still sums to the stated O(n 2^T) total. Doubling can
exceed n by less than a factor two, rather than clipping the last cap at n.

## Main definitions

* `groupCurve`, `curves`: computed scores and actual subsets, compressed by cost.
* `run`: the executable pipeline, including cap doubling and observation recovery.

## Main results

* `run_spec`, `run_optimal_of_nondegenerate`: actual first crossings and optimality.
* `run_time_of_nondegenerate`, `run_isBigO`: derived output-sensitive operation bounds.
-/

public section

namespace Cslib.LeastSquares.FixedEffects.Resources

open Algorithms.Lean FiniteMinPlus

/-- Lexicographic cross-scatter and negative regressor-scatter score. -/
abbrev Score := ℚ ×ₗ ℚ
/-- A retained subset with a cached cost and score. -/
abbrev CachedChoice := Cached.Item Choice Score

/-- Running sufficient statistics, including the cardinality. -/
structure Sums where
  /-- Number of retained observations. -/
  count : ℕ
  /-- Sum of regressors. -/
  x : ℚ
  /-- Sum of responses. -/
  y : ℚ
  /-- Sum of regressor-response products. -/
  xy : ℚ
  /-- Sum of squared regressors. -/
  xx : ℚ

/-- Nine operations per point: two products, four sum updates, count increment,
record construction and loop dispatch. -/
@[expose] def sums : List Point → TimeM ℕ Sums
  | [] => pure ⟨0, 0, 0, 0, 0⟩
  | p :: ps => do
    let s ← sums ps
    TimeM.tick 9
    pure ⟨s.count + 1, p.1 + s.x, p.2 + s.y,
      p.1 * p.2 + s.xy, p.1 ^ 2 + s.xx⟩

/-- Exact cost of the sufficient-statistic traversal. -/
theorem sums_time (g : List Point) : (sums g).time = 9 * g.length := by
  induction g with
  | nil => rfl
  | cons p ps ih => simp [sums, ih]; omega

/-- The executable accumulator contains the mathematical sums. -/
theorem sums_correct (g : List Point) :
    (sums g).ret = ⟨g.length, (g.map Prod.fst).sum, (g.map Prod.snd).sum,
      (g.map fun p => p.1 * p.2).sum, (g.map fun p => p.1 ^ 2).sum⟩ := by
  induction g with
  | nil => rfl
  | cons p ps ih => simp [sums, ih]

/-- Compute the cached lexicographic score from the sufficient statistics.
Ten operations cover the cast, two products, two divisions, two subtractions,
negation, deletion subtraction and record construction. -/
@[expose] def cache (n : ℕ) (g : List Point) : TimeM ℕ CachedChoice := do
  let s ← sums g
  TimeM.tick 10
  pure ⟨⟨n - s.count, g⟩, n - s.count,
    toLex (s.xy - s.x * s.y / s.count, -(s.xx - s.x ^ 2 / s.count))⟩

/-- Caching computes exactly the reviewed centered objective and deletion count. -/
theorem cache_correct (n : ℕ) (g : List Point) :
    (cache n g).ret.value = ⟨n - g.length, g⟩ ∧
    (cache n g).ret.cost = n - g.length ∧
    (cache n g).ret.score = key ⟨n - g.length, g⟩ := by
  simp only [cache, TimeM.ret_bind, TimeM.ret_pure, sums_correct]
  refine ⟨trivial, trivial, ?_⟩
  simp only [key, cross_running_sums, variance_running_sums]

/-- Compute every cached subset score once. -/
@[expose] def cacheAll (n : ℕ) : List (List Point) → TimeM ℕ (List CachedChoice)
  | [] => pure []
  | g :: gs => do
    let a ← cache n g
    let rest ← cacheAll n gs
    TimeM.tick 2
    pure (a :: rest)

/-- Cache materialization preserves the number of subsets. -/
theorem cacheAll_length (n : ℕ) (gs : List (List Point)) :
    (cacheAll n gs).ret.length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [cacheAll, ih]

/-- The total cost includes all sufficient-statistic traversals. -/
theorem cacheAll_time (n : ℕ) (gs : List (List Point)) :
    (cacheAll n gs).time = 9 * (gs.map List.length).sum + 12 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [cacheAll, cache, sums_time, ih]; ring

/-- Executable subset duplication, sharing each retained tail. Three cons operations
and loop dispatch are charged for each original subset. -/
@[expose] def duplicate (p : Point) : List (List Point) → TimeM ℕ (List (List Point))
  | [] => pure []
  | s :: ss => do
    let rest ← duplicate p ss
    TimeM.tick 4
    pure (s :: (p :: s) :: rest)

/-- Exact work of subset duplication. -/
theorem duplicate_time (p : Point) (ss : List (List Point)) :
    (duplicate p ss).time = 4 * ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [duplicate, ih]; omega

/-- Duplication follows the standard sublists enumeration order. -/
theorem duplicate_correct (p : Point) (ss : List (List Point)) :
    (duplicate p ss).ret = ss.flatMap (fun s => [s, p :: s]) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [duplicate, ih]

/-- Enumerate actual retained sublists without choice or existence extraction. -/
@[expose] def subsets : List Point → TimeM ℕ (List (List Point))
  | [] => pure [[]]
  | p :: ps => do
    let ss ← subsets ps
    duplicate p ss

/-- The enumerator is the reviewed subset enumeration, with repeated values preserved. -/
theorem subsets_correct (g : List Point) : (subsets g).ret = g.sublists := by
  induction g with
  | nil => rfl
  | cons p ps ih => simp [subsets, duplicate_correct, ih, List.sublists_cons]

/-- Subset generation has linear cost in the number of generated subsets. -/
theorem subsets_time (g : List Point) : (subsets g).time + 4 = 4 * 2 ^ g.length := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    simp only [subsets, TimeM.time_bind, duplicate_time, subsets_correct,
      List.length_sublists, List.length_cons, pow_succ]
    omega

/-- Measure already grouped input, including the cost of reading empty groups. -/
@[expose] def inputSize : List (List Point) → TimeM ℕ ℕ
  | [] => pure 0
  | g :: gs => do
    let n ← Cached.lengthM g
    let rest ← inputSize gs
    TimeM.tick 1
    pure (n + rest)

/-- Input measurement counts every observation and every input group. -/
theorem inputSize_spec (groups : List (List Point)) :
    (inputSize groups).ret = sampleSize groups ∧
      (inputSize groups).time = sampleSize groups + groups.length := by
  induction groups with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    simp only [inputSize, TimeM.ret_bind, TimeM.ret_pure, TimeM.time_bind,
      TimeM.time_tick, TimeM.time_pure, (Cached.lengthM_spec g).1, (Cached.lengthM_spec g).2,
      ih.1, ih.2, sampleSize, total,
      List.map_cons, List.sum_cons, List.length_cons]
    simp [Nat.add_assoc]

/-- Cached, compressed deletion curve; at most one subset is retained per cost. -/
@[expose] def groupCurve (g : List Point) : TimeM ℕ (List CachedChoice) := do
  let n ← Cached.lengthM g
  let ss ← subsets g
  let row ← cacheAll n ss
  Cached.curve row (n + 1)

/-- There are at most size-plus-one curve entries. -/
theorem groupCurve_length (g : List Point) : (groupCurve g).ret.length ≤ g.length + 1 := by
  simp only [groupCurve, TimeM.ret_bind, (Cached.lengthM_spec g).1]
  exact Cached.curve_length _ _

/-- Preprocessing counts the enumerator, sufficient-statistic traversals and every
compression comparison. This avoids assuming a cost for computing group curves. -/
theorem groupCurve_time (g : List Point) :
    (groupCurve g).time ≤ 40 * (g.length + 1) * 2 ^ g.length := by
  have hs := subsets_time g
  have hl : (g.sublists.map List.length).sum ≤ g.length * 2 ^ g.length := by
    calc
      _ ≤ (g.sublists.map fun _ => g.length).sum := List.sum_le_sum fun s hs =>
        (List.mem_sublists.mp hs).length_le
      _ = _ := by simp [List.map_const', List.sum_replicate, Nat.mul_comm]
  simp only [groupCurve, TimeM.time_bind, Cached.curve_time, cacheAll_time,
    cacheAll_length, subsets_correct, List.length_sublists, (Cached.lengthM_spec g).1,
    (Cached.lengthM_spec g).2]
  nlinarith [(Nat.one_le_two_pow (n := g.length))]

private theorem mem_cacheAll (n : ℕ) (gs : List (List Point)) (a : CachedChoice) :
    a ∈ (cacheAll n gs).ret ↔ ∃ g ∈ gs, a = (cache n g).ret := by
  induction gs with
  | nil => simp [cacheAll]
  | cons g gs ih => simp [cacheAll, ih, eq_comm]

/-- Compressed entries are actual subsets with exactly their stored cost and score. -/
theorem groupCurve_mem (g : List Point) (a : CachedChoice)
    (ha : a ∈ (groupCurve g).ret) :
    a.value ∈ choices g ∧ a.cost = a.value.deleted ∧ a.score = key a.value := by
  simp only [groupCurve, TimeM.ret_bind, (Cached.lengthM_spec g).1] at ha
  obtain ⟨ha, _⟩ := Cached.mem_curve _ _ a ha
  obtain ⟨s, hs, rfl⟩ := (mem_cacheAll g.length g.sublists a).mp
    (by simpa only [subsets_correct] using ha)
  obtain ⟨hv, hc, hk⟩ := cache_correct g.length s
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]
    exact (mem_choices ..).mpr ⟨List.mem_sublists.mp hs, rfl⟩
  · rw [hv, hc]
  · rw [hv, hk]

/-- Group compression preserves or improves every actual subset at its exact cost. -/
theorem groupCurve_dominates (g : List Point) (a : Choice) (ha : a ∈ choices g) :
    ∃ b ∈ (groupCurve g).ret,
      b.value.deleted = a.deleted ∧ key b.value ≤ key a := by
  obtain ⟨hs, hd⟩ := (mem_choices g a).mp ha
  let c := (cache g.length a.kept).ret
  have hcv : c.value = a := by
    rw [(cache_correct g.length a.kept).1]
    cases a
    simp_all
  have hcm : c ∈ (cacheAll g.length g.sublists).ret :=
    (mem_cacheAll ..).mpr ⟨a.kept, List.mem_sublists.mpr hs, rfl⟩
  have hcc := (cache_correct g.length a.kept).2.1
  obtain ⟨b, hb, hbc, hbs⟩ := Cached.curve_dominates
    (cacheAll g.length g.sublists).ret (g.length + 1) c hcm (by dsimp [c]; rw [hcc]; omega)
  have hbg : b ∈ (groupCurve g).ret := by simpa only [groupCurve,
    TimeM.ret_bind, subsets_correct, (Cached.lengthM_spec g).1] using hb
  obtain ⟨_, hcost, hscore⟩ := groupCurve_mem g b hbg
  have hcs : c.score = key a := by
    rw [← hcv]
    exact (cache_correct g.length a.kept).2.2
  refine ⟨b, hbg, ?_, ?_⟩
  · rw [← hcost, hbc]
    simpa only [c, hcc] using hd.symm
  · rwa [hscore, hcs] at hbs

/-- Precompute every curve once; the additional operation reads the input group list. -/
@[expose] def curves : List (List Point) → TimeM ℕ (List (List CachedChoice))
  | [] => pure []
  | g :: gs => do
    let row ← groupCurve g
    let rest ← curves gs
    TimeM.tick 1
    pure (row :: rest)

/-- Precomputed curve lists have one row per input group. -/
theorem curves_length (groups : List (List Point)) :
    (curves groups).ret.length = groups.length := by
  induction groups with
  | nil => rfl
  | cons g gs ih => simp [curves, ih]

/-- Every precomputed entry obeys the cached-score contract of the generic DP. -/
theorem curves_cached (groups : List (List Point)) :
    ∀ row ∈ (curves groups).ret, ∀ a ∈ row,
      a.cost = a.value.deleted ∧ a.score = key a.value := by
  induction groups with
  | nil => simp [curves]
  | cons g gs ih =>
    intro row hr a ha
    simp only [curves, TimeM.ret_bind, TimeM.ret_pure, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact (groupCurve_mem g a ha).2
    · exact ih row hr a ha

/-- The sum of compressed row lengths is at most observations plus groups. -/
theorem curves_width (groups : List (List Point)) :
    ((curves groups).ret.map List.length).sum ≤ sampleSize groups + groups.length := by
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    have hg := groupCurve_length g
    simp only [curves, TimeM.ret_bind, TimeM.ret_pure, List.map_cons, List.sum_cons]
    change _ ≤ g.length + sampleSize gs + (gs.length + 1)
    omega

/-- Reading nonempty groups costs at most the number of observations. Arbitrarily
many empty groups need an additional input-length term and are excluded here. -/
theorem groups_length_le (groups : List (List Point))
    (hne : ∀ g ∈ groups, g ≠ []) : groups.length ≤ sampleSize groups := by
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    have hg : 0 < g.length := List.length_pos_iff.mpr (hne g (by simp))
    have ht := ih (fun a ha => hne a (by simp [ha]))
    change gs.length + 1 ≤ g.length + sampleSize gs
    omega

/-- A quantified preprocessing bound for actual enumeration and compression,
with an absolute constant independent of the data, group size and group count. -/
theorem curves_time (groups : List (List Point)) (T : ℕ)
    (hne : ∀ g ∈ groups, g ≠ []) (hT : ∀ g ∈ groups, g.length ≤ T) :
    (curves groups).time ≤ 81 * sampleSize groups * 2 ^ T := by
  induction groups with
  | nil => simp [curves, sampleSize, total]
  | cons g gs ih =>
    have hg := groupCurve_time g
    have hp : 0 < g.length := List.length_pos_iff.mpr (hne g (by simp))
    have ht := ih (fun a ha => hne a (by simp [ha])) (fun a ha => hT a (by simp [ha]))
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (hT g (by simp))
    have hlocal : (groupCurve g).time ≤ 80 * g.length * 2 ^ T := by
      calc
        _ ≤ 40 * (g.length + 1) * 2 ^ g.length := hg
        _ ≤ 80 * g.length * 2 ^ T := Nat.mul_le_mul
          (by omega) hpow
    simp only [curves, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]
    change _ ≤ 81 * (g.length + sampleSize gs) * 2 ^ T
    nlinarith [Nat.one_le_two_pow (n := T)]

/-- Compression cannot fabricate an admissible observation-removal plan. -/
theorem curves_sound (groups : List (List Point)) (p : List Choice)
    (hp : Admissible ((curves groups).ret.map (List.map Cached.Item.value)) p) :
    Valid groups p := by
  induction groups generalizing p with
  | nil => exact hp
  | cons g gs ih =>
    cases p with
    | nil => cases hp
    | cons a p =>
      obtain ⟨ha, ht⟩ := List.forall₂_cons.mp hp
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact List.Forall₂.cons (groupCurve_mem g b hb).1 (ih p ht)

/-- Every removal plan has a compressed competitor of equal cost and no larger score. -/
theorem curves_dominate (groups : List (List Point)) (q : List Choice)
    (hq : Valid groups q) :
    ∃ p, Admissible ((curves groups).ret.map (List.map Cached.Item.value)) p ∧
      deletions p = deletions q ∧ total key p ≤ total key q := by
  induction groups generalizing q with
  | nil =>
    cases q with
    | nil => exact ⟨[], .nil, rfl, le_rfl⟩
    | cons => cases hq
  | cons g gs ih =>
    cases q with
    | nil => cases hq
    | cons a q =>
      obtain ⟨ha, hq⟩ := List.forall₂_cons.mp hq
      obtain ⟨p, hp, hc, hs⟩ := ih q hq
      obtain ⟨b, hb, hbc, hbs⟩ := groupCurve_dominates g a ha
      refine ⟨b.value :: p, List.Forall₂.cons (List.mem_map.mpr ⟨b, hb, rfl⟩) hp, ?_, ?_⟩
      · change b.value.deleted + deletions p = a.deleted + deletions q
        rw [hbc, hc]
      · exact add_le_add hbs hs

/-- One capped convolution and increasing-cost scan, using precomputed curves. -/
@[expose] def attempt (rows : List (List CachedChoice)) (cap : ℕ) :
    TimeM ℕ (Option (Cached.Hit Choice Score)) := do
  let a ← Cached.table (cap + 1) rows
  Cached.scan a 0 (cap + 1)

/-- A capped attempt has linear work in n times its cap; no runtime premise is used. -/
theorem attempt_time (groups : List (List Point)) (cap : ℕ)
    (hne : ∀ g ∈ groups, g ≠ []) :
    (attempt (curves groups).ret cap).time ≤
      (26 * sampleSize groups + 7) * (cap + 1) := by
  have hg := groups_length_le groups hne
  have hl := curves_width groups
  have ht := Cached.table_time_le (cap + 1) (sampleSize groups) (curves groups).ret
    (by omega) (by rw [curves_length]; exact hg)
  have hs := Cached.scan_time (Cached.table (cap + 1) (curves groups).ret).ret 0 (cap + 1)
  change (Cached.table (cap + 1) (curves groups).ret).time +
    (Cached.scan _ 0 (cap + 1)).time ≤ _
  nlinarith

/-- Cached crossings coincide with actual subset-removal crossings, including
singular zero-scatter ones. Nonsingularity is required separately for optimality. -/
theorem table_crosses_iff (groups : List (List Point)) (cap k : ℕ) (hk : k ≤ cap) :
    Cached.Crosses (Cached.table (cap + 1) (curves groups).ret).ret k ↔
      ∃ q, Valid groups q ∧ deletions q = k ∧ numerator q ≤ 0 := by
  obtain ⟨hco, he⟩ := Cached.table_correct Choice.deleted key (curves groups).ret
    (cap + 1) (curves_cached groups) k
  simp only [show k < cap + 1 by omega, ite_true] at he
  constructor
  · rintro ⟨e, hcell, hs⟩
    rw [hcell, Option.map_some] at he
    obtain ⟨hv, hc, _⟩ := (solve_spec Choice.deleted key _ k).1 e.plan he.symm
    refine ⟨e.plan, curves_sound groups _ hv, hc, ?_⟩
    exact (key_nonpos_iff _).mp (by rwa [← hco e hcell])
  · rintro ⟨q, hq, hc, hs⟩
    obtain ⟨p, hp, hpc, hps⟩ := curves_dominate groups q hq
    obtain ⟨r, hr, hrs⟩ := (crossing_iff Choice.deleted key _ k).mpr
      ⟨p, hp, hpc.trans hc, hps.trans ((key_nonpos_iff q).mpr hs)⟩
    rw [hr] at he
    cases hx : (Cached.table (cap + 1) (curves groups).ret).ret[k]?.join with
    | none => simp [hx] at he
    | some e =>
      simp only [hx, Option.map_some, Option.some.injEq] at he
      refine ⟨e, hx, ?_⟩
      rw [hco e hx, he]
      exact hrs

/-- A successful capped run returns an actual globally least-cost crossing and
minimizes its numerator/negative-scatter pair at that exact cost. -/
theorem attempt_spec (groups : List (List Point)) (cap : ℕ)
    (h : Cached.Hit Choice Score) (hh : (attempt (curves groups).ret cap).ret = some h) :
    Valid groups h.entry.plan ∧ deletions h.entry.plan = h.index ∧ h.index ≤ cap ∧
      h.entry.score = total key h.entry.plan ∧ numerator h.entry.plan ≤ 0 ∧
      (∀ q, Valid groups q → numerator q ≤ 0 → h.index ≤ deletions q) ∧
      (∀ q, Valid groups q → deletions q = h.index →
        total key h.entry.plan ≤ total key q) := by
  obtain ⟨_, hu, hc, hs, hf⟩ := Cached.scan_some _ 0 (cap + 1) h hh
  have hcap : h.index ≤ cap := by omega
  obtain ⟨hco, he⟩ := Cached.table_correct Choice.deleted key (curves groups).ret
    (cap + 1) (curves_cached groups) h.index
  rw [hc, Option.map_some] at he
  simp only [show h.index < cap + 1 by omega, ite_true] at he
  obtain ⟨hv, hcost, hmin⟩ := (solve_spec Choice.deleted key _ h.index).1 _ he.symm
  have hscore := hco h.entry hc
  refine ⟨curves_sound groups _ hv, hcost, hcap, hscore,
    (key_nonpos_iff _).mp (by rwa [← hscore]), ?_, ?_⟩
  · intro q hq hsq
    by_contra hn
    have hl : deletions q < h.index := by omega
    exact hf (deletions q) (by omega) hl
      ((table_crosses_iff groups cap _ (by omega)).mpr ⟨q, hq, rfl, hsq⟩)
  · intro q hq hqc
    obtain ⟨p, hp, hpc, hps⟩ := curves_dominate groups q hq
    exact (hmin p hp (hpc.trans hqc)).trans hps

/-- Failure is exactly absence of an actual crossing within the cap. -/
theorem attempt_none (groups : List (List Point)) (cap : ℕ) :
    (attempt (curves groups).ret cap).ret = none ↔
      ¬ ∃ q, Valid groups q ∧ deletions q ≤ cap ∧ numerator q ≤ 0 := by
  rw [show (attempt (curves groups).ret cap).ret =
    (Cached.scan (Cached.table (cap + 1) (curves groups).ret).ret 0 (cap + 1)).ret from rfl,
    Cached.scan_none]
  constructor
  · intro h ⟨q, hq, hc, hs⟩
    exact h (deletions q) (by omega) (by omega)
      ((table_crosses_iff groups cap _ hc).mpr ⟨q, hq, rfl, hs⟩)
  · intro h k _ hk hc
    obtain ⟨q, hq, hqc, hs⟩ := (table_crosses_iff groups cap k (by omega)).mp hc
    exact h ⟨q, hq, by omega, hs⟩

/-- Output-sensitive doubling. The cap may exceed n by less than a factor two;
this avoids a final clipped stage and leaves the asymptotic bound unchanged.
Fuel is a structural termination guard; it is not a runtime hypothesis. -/
@[expose] def search (rows : List (List CachedChoice)) :
    ℕ → ℕ → TimeM ℕ (Option (Cached.Hit Choice Score))
  | 0, cap => attempt rows cap
  | fuel + 1, cap => do
    let hit ← attempt rows cap
    match hit with
    | some h => pure (some h)
    | none => do
      TimeM.tick 2
      search rows fuel (2 * cap)

/-- Any successful search result inherits capped-run correctness. -/
theorem search_spec (groups : List (List Point)) (fuel cap : ℕ)
    (h : Cached.Hit Choice Score)
    (hh : (search (curves groups).ret fuel cap).ret = some h) :
    ∃ c, (attempt (curves groups).ret c).ret = some h := by
  induction fuel generalizing cap with
  | zero => exact ⟨cap, hh⟩
  | succ fuel ih =>
    simp only [search, TimeM.ret_bind] at hh
    cases ha : (attempt (curves groups).ret cap).ret with
    | none => simp only [ha, TimeM.ret_bind] at hh; exact ih _ hh
    | some e => simp only [ha, TimeM.ret_pure, Option.some.injEq] at hh
                exact ⟨cap, ha.trans (congrArg some hh)⟩

/-- A known actual crossing forces search success once the structural guard covers
its cost. The guard decreases while the executable cap doubles. -/
theorem search_exists (groups : List (List Point)) (q : List Choice)
    (hq : Valid groups q) (hs : numerator q ≤ 0) (fuel cap : ℕ)
    (hc : 0 < cap) (hf : deletions q ≤ cap + fuel) :
    ∃ h, (search (curves groups).ret fuel cap).ret = some h := by
  induction fuel generalizing cap with
  | zero =>
    cases ha : (attempt (curves groups).ret cap).ret with
    | some h => exact ⟨h, ha⟩
    | none => exact False.elim ((attempt_none groups cap).mp ha ⟨q, hq, by omega, hs⟩)
  | succ fuel ih =>
    cases ha : (attempt (curves groups).ret cap).ret with
    | some h => exact ⟨h, by simp [search, ha]⟩
    | none =>
      obtain ⟨h, hh⟩ := ih (2 * cap) (by omega) (by omega)
      exact ⟨h, by simpa only [search, TimeM.ret_bind, ha] using hh⟩

/-- Amortized geometric-series bound for the actual early-stopping search.
The comparison is with any actual crossing, not an assumed running time.
Two operations per failed round count doubling and branch dispatch. -/
theorem search_time (groups : List (List Point)) (q : List Choice)
    (hne : ∀ g ∈ groups, g ≠ []) (hq : Valid groups q) (hs : numerator q ≤ 0)
    (fuel cap : ℕ) (hc : 0 < cap) (hcap : cap ≤ 2 * deletions q) :
    (search (curves groups).ret fuel cap).time +
        2 * (26 * sampleSize groups + 9) * cap ≤
      8 * (26 * sampleSize groups + 9) * deletions q := by
  induction fuel generalizing cap with
  | zero =>
    have ht := attempt_time groups cap hne
    change (attempt (curves groups).ret cap).time + _ ≤ _
    nlinarith
  | succ fuel ih =>
    have ht := attempt_time groups cap hne
    simp only [search, TimeM.time_bind]
    cases ha : (attempt (curves groups).ret cap).ret with
    | some h => simp only [TimeM.time_pure]; nlinarith
    | none =>
      have hl : cap < deletions q := by
        by_contra hn
        exact (attempt_none groups cap).mp ha ⟨q, hq, by omega, hs⟩
      have hi := ih (2 * cap) (by omega) (by omega)
      simp only [TimeM.time_bind, TimeM.time_tick]
      nlinarith

/-- Copy a recovered group plan into ordinary retained groups. This charges the
actual observation traversal, rather than declaring witness extraction free. -/
@[expose] def copyPoints : List Point → TimeM ℕ (List Point)
  | [] => pure []
  | p :: ps => do
    let tail ← copyPoints ps
    TimeM.tick 1
    pure (p :: tail)

/-- Materialize all retained groups from the persistent DP witness. -/
@[expose] def recover : List Choice → TimeM ℕ (List (List Point))
  | [] => pure []
  | a :: p => do
    let g ← copyPoints a.kept
    let rest ← recover p
    TimeM.tick 1
    pure (g :: rest)

/-- Recovery returns the actual retained observations. -/
theorem recover_correct (p : List Choice) :
    (recover p).ret = p.map Choice.kept := by
  have hcopy : ∀ g, (copyPoints g).ret = g := by
    intro g
    induction g with
    | nil => rfl
    | cons a g ih => simp [copyPoints, ih]
  induction p with
  | nil => rfl
  | cons a p ih => simp [recover, hcopy, ih]

/-- Recovery costs one cons per retained observation and one per retained group. -/
theorem recover_time (p : List Choice) :
    (recover p).time = total (List.length ∘ Choice.kept) p + p.length := by
  have hcopy : ∀ g, (copyPoints g).time = g.length := by
    intro g
    induction g with
    | nil => rfl
    | cons a g ih => simp [copyPoints, ih]
  induction p with
  | nil => rfl
  | cons a p ih => simp [recover, hcopy, ih, total]; omega

/-- End-to-end executable audit: compute curves once, double until a crossing,
then materialize the retained observations. The returned plan is also available
for the feasibility and optimality theorems. -/
structure Result where
  /-- Cost/index and persistent minimizing plan. -/
  hit : Cached.Hit Choice Score
  /-- Materialized retained groups. -/
  retained : List (List Point)

/-- Total executable pipeline. No algorithm is extracted from an existence proof. -/
@[expose] def run (groups : List (List Point)) : TimeM ℕ (Option Result) := do
  let n ← inputSize groups
  let rows ← curves groups
  let hit ← search rows n 1
  match hit with
  | none => pure none
  | some h => do
    let retained ← recover h.entry.plan
    pure (some ⟨h, retained⟩)

/-- The pipeline always returns actual observations; singular zero crossings remain
possible and do not assert nonsingular feasibility. -/
theorem run_exists (groups : List (List Point)) : ∃ r, (run groups).ret = some r := by
  obtain ⟨q, hq, hc, hs⟩ := all_deleted groups
  obtain ⟨h, hh⟩ := search_exists groups q hq hs.le (sampleSize groups) 1 (by omega)
    (by omega)
  exact ⟨⟨h, (recover h.entry.plan).ret⟩, by simp [run, (inputSize_spec groups).1, hh]⟩

/-- Resource-certified output has the reviewed global first-crossing and exact-score
minimality contract, plus the computed materialized retained groups. -/
theorem run_spec (groups : List (List Point)) (r : Result)
    (hr : (run groups).ret = some r) :
    Valid groups r.hit.entry.plan ∧ deletions r.hit.entry.plan = r.hit.index ∧
      numerator r.hit.entry.plan ≤ 0 ∧ r.retained = r.hit.entry.plan.map Choice.kept ∧
      (∀ q, Feasible groups q → r.hit.index ≤ deletions q) ∧
      (∀ q, Valid groups q → deletions q = r.hit.index →
        total key r.hit.entry.plan ≤ total key q) := by
  simp only [run, TimeM.ret_bind, (inputSize_spec groups).1] at hr
  cases hh : (search (curves groups).ret (sampleSize groups) 1).ret with
  | none => simp [hh] at hr
  | some h =>
    simp only [hh, TimeM.ret_bind, TimeM.ret_pure, Option.some.injEq] at hr
    subst r
    obtain ⟨cap, ha⟩ := search_spec groups _ _ h hh
    obtain ⟨hv, hc, _, _, hs, hmin, hscore⟩ := attempt_spec groups cap h ha
    refine ⟨hv, hc, hs, recover_correct _, ?_, hscore⟩
    intro q hq
    exact hmin q hq.1 ((slope_nonpos_iff q hq.2.1).mp hq.2.2)

/-- Quantified arithmetic-operation bound, with absolute constants, against every
successful removal plan of positive cost. Under the paper's nondegeneracy the
returned crossing is optimal, so choosing an optimal plan gives O(n 2^T + n s_int).
Already grouped nonempty input is explicit; this is not rational bit complexity. -/
theorem run_time (groups : List (List Point)) (T : ℕ) (q : List Choice)
    (hne : ∀ g ∈ groups, g ≠ []) (hT : ∀ g ∈ groups, g.length ≤ T)
    (hq : Feasible groups q) (hpos : 0 < deletions q) :
    (run groups).time ≤ 300 * (sampleSize groups * 2 ^ T + sampleSize groups * deletions q) := by
  have hn : 0 < sampleSize groups := by
    have := deletion_accounting groups q hq.1
    omega
  have ht := search_time groups q hne hq.1 ((slope_nonpos_iff q hq.2.1).mp hq.2.2)
    (sampleSize groups) 1 (by omega) (by omega)
  have hp := curves_time groups T hne hT
  obtain ⟨r, hr⟩ := run_exists groups
  obtain ⟨hv, _, _, _, _, _⟩ := run_spec groups r hr
  have hlen : r.hit.entry.plan.length = groups.length := by
    simpa only [List.length_map] using (List.Forall₂.length_eq hv).symm
  have hacc := deletion_accounting groups r.hit.entry.plan hv
  have hg := groups_length_le groups hne
  have hrec : (recover r.hit.entry.plan).time ≤ 2 * sampleSize groups := by
    rw [recover_time, hlen]
    omega
  simp only [run, TimeM.time_bind, (inputSize_spec groups).1, (inputSize_spec groups).2]
  cases hh : (search (curves groups).ret (sampleSize groups) 1).ret with
  | none => simp only [TimeM.time_pure]; nlinarith
  | some h =>
    have he : h = r.hit := by
      simp only [run, TimeM.ret_bind, (inputSize_spec groups).1, hh,
        TimeM.ret_pure, Option.some.injEq] at hr
      exact congrArg Result.hit hr
    subst h
    simp only [TimeM.time_bind, TimeM.time_pure, add_zero]
    nlinarith [Nat.one_le_two_pow (n := T)]

/-- The undeleted input plan. -/
@[expose] def fullPlan (groups : List (List Point)) : List Choice :=
  groups.map fun g => ⟨0, g⟩

/-- For this model, the source's positive original slope is equivalent to a
positive original numerator: scatter is nonnegative, and zero scatter forces
zero numerator. Thus the resource theorem's positivity condition has the source
meaning, rather than assuming a first crossing or its optimality. -/
theorem positive_original_iff (groups : List (List Point)) :
    0 < slope (fullPlan groups) ↔ 0 < numerator (fullPlan groups) := by
  have hv := denominator_nonneg (fullPlan groups)
  constructor
  · intro h
    rcases (div_pos_iff).mp h with h | h
    · exact h.1
    · linarith [h.2]
  · intro h
    apply div_pos h
    have hn : denominator (fullPlan groups) ≠ 0 := by
      intro hz
      have := numerator_eq_zero_of_denominator_eq_zero _ hz
      linarith
    exact lt_of_le_of_ne hv (Ne.symm hn)

/-- Zero actual deletions force the original observations, including multiplicities. -/
theorem eq_fullPlan_of_zero (groups : List (List Point)) (p : List Choice)
    (hp : Valid groups p) (hc : deletions p = 0) : p = fullPlan groups := by
  induction groups generalizing p with
  | nil => cases p with
    | nil => rfl
    | cons => cases hp
  | cons g gs ih =>
    cases p with
    | nil => cases hp
    | cons a p =>
      obtain ⟨ha, hp⟩ := List.forall₂_cons.mp hp
      obtain ⟨hs, hd⟩ := (mem_choices g a).mp ha
      have hlen := hs.length_le
      change a.deleted + deletions p = 0 at hc
      have htail := ih p hp (by omega)
      have hkeep : a.kept = g := hs.eq_of_length_le (by omega)
      have he : a = ⟨0, g⟩ := by cases a; simp_all
      simp [fullPlan, he, htail]

/-- The paper's positive original numerator excludes cost-zero successful removal. -/
theorem deletions_pos (groups : List (List Point)) (q : List Choice)
    (hfull : 0 < numerator (fullPlan groups)) (hq : Feasible groups q) :
    0 < deletions q := by
  by_contra h
  have he := eq_fullPlan_of_zero groups q hq.1 (by omega)
  have hs := (slope_nonpos_iff q hq.2.1).mp hq.2.2
  rw [he] at hs
  linarith

/-- The same source nondegeneracy as the reviewed algorithm makes the efficient
computed crossing a nonsingular optimum; it is not a runtime assumption. -/
theorem run_optimal_of_nondegenerate (groups : List (List Point)) (r : Result)
    (hr : (run groups).ret = some r)
    (hnd : ∃ q, Valid groups q ∧ deletions q = r.hit.index ∧
      numerator q = numerator r.hit.entry.plan ∧ 0 < denominator q) :
    Feasible groups r.hit.entry.plan ∧
      ∀ q, Feasible groups q → deletions r.hit.entry.plan ≤ deletions q := by
  obtain ⟨hv, hc, hs, _, hmin, hscore⟩ := run_spec groups r hr
  obtain ⟨q, hq, hqc, hn, hvar⟩ := hnd
  have hle := hscore q hq hqc
  rw [total_key, total_key, Prod.Lex.le_iff] at hle
  have hp : 0 < denominator r.hit.entry.plan := by
    rcases hle with hlt | ⟨_, hle⟩
    · change numerator r.hit.entry.plan < numerator q at hlt
      rw [hn] at hlt
      exact False.elim (lt_irrefl _ hlt)
    · change -denominator r.hit.entry.plan ≤ -denominator q at hle
      linarith
  exact ⟨⟨hv, hp, (slope_nonpos_iff _ hp).mpr hs⟩, fun q hq => hc ▸ hmin q hq⟩

/-- A strict negative first crossing supplies nondegeneracy automatically. -/
theorem run_optimal_of_negative (groups : List (List Point)) (r : Result)
    (hr : (run groups).ret = some r) (hs : numerator r.hit.entry.plan < 0) :
    Feasible groups r.hit.entry.plan ∧
      ∀ q, Feasible groups q → deletions r.hit.entry.plan ≤ deletions q := by
  obtain ⟨hv, hc, _, _, _, _⟩ := run_spec groups r hr
  have hn : denominator r.hit.entry.plan ≠ 0 := by
    intro hz
    rw [numerator_eq_zero_of_denominator_eq_zero _ hz] at hs
    exact lt_irrefl _ hs
  exact run_optimal_of_nondegenerate groups r hr
    ⟨r.hit.entry.plan, hv, hc, rfl,
      lt_of_le_of_ne (denominator_nonneg _) (Ne.symm hn)⟩

/-- The source's advertised output-sensitive guarantee for the computed optimum,
with a universal numerical constant and actual recovery included. -/
theorem run_time_of_nondegenerate (groups : List (List Point)) (T : ℕ) (r : Result)
    (hr : (run groups).ret = some r)
    (hne : ∀ g ∈ groups, g ≠ []) (hT : ∀ g ∈ groups, g.length ≤ T)
    (hfull : 0 < numerator (fullPlan groups))
    (hnd : ∃ q, Valid groups q ∧ deletions q = r.hit.index ∧
      numerator q = numerator r.hit.entry.plan ∧ 0 < denominator q) :
    Feasible groups r.hit.entry.plan ∧
      (∀ q, Feasible groups q → r.hit.index ≤ deletions q) ∧
      (run groups).time ≤
        300 * (sampleSize groups * 2 ^ T + sampleSize groups * r.hit.index) := by
  obtain ⟨hf, hm⟩ := run_optimal_of_nondegenerate groups r hr hnd
  have hc := (run_spec groups r hr).2.1
  refine ⟨hf, fun q hq => hc ▸ hm q hq, ?_⟩
  simpa only [hc] using run_time groups T r.hit.entry.plan hne hT hf
    (deletions_pos groups _ hfull hf)

/-- The quantified bound also gives Big O along any family/filter of admissible
inputs, without restricting how n, T or the optimum grow. -/
theorem run_isBigO {ι : Type*} (l : Filter ι) (groups : ι → List (List Point))
    (T : ι → ℕ) (q : ι → List Choice)
    (hne : ∀ i g, g ∈ groups i → g ≠ [])
    (hT : ∀ i g, g ∈ groups i → g.length ≤ T i)
    (hq : ∀ i, Feasible (groups i) (q i))
    (hfull : ∀ i, 0 < numerator (fullPlan (groups i))) :
    (fun i => ((run (groups i)).time : ℝ)) =O[l]
      (fun i => (sampleSize (groups i) : ℝ) * 2 ^ T i +
        (sampleSize (groups i) : ℝ) * deletions (q i)) := by
  apply Asymptotics.IsBigO.of_bound 300
  apply Filter.Eventually.of_forall
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact_mod_cast run_time (groups i) (T i) (q i) (hne i) (hT i) (hq i)
    (deletions_pos _ _ (hfull i) (hq i))

end Cslib.LeastSquares.FixedEffects.Resources
