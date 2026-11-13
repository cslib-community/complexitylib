/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
public import CslibFrontier.DataStructure.Online.Behavioral
public import CslibFrontier.DataStructure.Paging.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import CslibFrontier.Foundations.NumberTheory.Harmonic
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPowerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The randomized marking algorithm for paging (`2 H_k`-competitiveness)

This file formalizes the **randomized marking algorithm** for demand paging (`Paging.problem α k`,
`0 < k`) and proves Theorem 1 of [Fiat, Karp, Luby, McGeoch, Sleator, and Young, *Competitive
Paging Algorithms*, Section 3 ("The marking algorithm"),
Theorem 1][FiatKarpLubyMcGeochSleatorYoung1991]: randomized marking is `2 H_k`-competitive against
an oblivious adversary, with additive constant `0`.

## Algorithm

Controller memory (`MarkMem α`) stores the resident `cache : Finset α` together with the subset of
currently `marked : Finset α` pages, initialized to `⟨s₀, s₀⟩` so that all initially cached pages
start marked (as in [FiatKarpLubyMcGeochSleatorYoung1991], Section 3). On request `p`:

* **Cache hit (`p ∈ cache`):** `p` is marked and `cache` is unchanged (`stepCost = 0`).
* **Cache miss into a non-full cache (`p ∉ cache`, `cache.card < k`):** `p` is inserted and marked
  without eviction (`stepCost = 1`), extending the source's full initial cache (`|s₀| = k`) to every
  admissible initial cache `|s₀| ≤ k`.
* **Cache miss into a full cache (`p ∉ cache`, `cache.card = k`):** if every cached page is marked
  (`cache ⊆ marked`), all marks are cleared first; then a uniformly chosen unmarked cached page is
  evicted (`Cslib.Probability.PMF.uniformOfFinset`), and `p` is inserted and marked
  (`stepCost = 1`).

Because marking tosses a fresh uniform coin at unboundedly many evictions, it is packaged as an
`Online.BehavioralStrategy (problem α k)` (`markingStrategy`).

## Proof architecture

1. **Exact stale-subset distribution law (`MarkTracker`, `markLaw`,
   `expectedCost_markingStrategy_eq`):**
   At every step, the controller memory distribution equals `markLaw tr`, where `tr.marked` is the
   deterministic set of marked pages in the current phase, `tr.stale` is the deterministic set of
   unmarked pages from the previous phase not yet requested in the current phase, and the cache is
   `tr.marked ∪ U` for `U` drawn uniformly from `tr.stale.powersetCard tr.staleCached`. This yields
   an exact computable rational recursion `trackerExpectedCost` for `expectedCost`.
2. **Harmonic potential (`trackerPotential`, `trackerExpectedCost_le_harmonic_mul_cleanCount`):**
   With `c = tr.stale.card - tr.staleCached` clean misses so far in the current phase, the potential
   `c * (harmonic tr.stale.card - harmonic c)` absorbs every stale request's `c / |stale|` fault
   probability with zero residual charge and charges at most `harmonic k` per clean request, giving
   `E[MARK] ≤ H_k · #clean` across both completed and incomplete phases.
3. **Two-window offline lower bound (`cleanCount_le_two_mul_scheduleCost`):**
   Direct backward induction over arbitrary (not necessarily lazy) valid offline schedules
   `(problem α k).ValidSchedule s₀ reqs offStates` tracks the fault set `B` since the start of the
   current phase, proving `#clean ≤ 2 · OPT` without reducing to lazy schedules.

## Main definitions

* `Cslib.DataStructure.Paging.MarkMem`, `Cslib.DataStructure.Paging.ValidMarkMem`: controller memory
  and invariant of randomized marking.
* `Cslib.DataStructure.Paging.markingStep`, `Cslib.DataStructure.Paging.markingStrategy`: the
  randomized marking behavioural online strategy for `Paging.problem α k`.
* `Cslib.DataStructure.Paging.MarkTracker`, `Cslib.DataStructure.Paging.markLaw`,
  `Cslib.DataStructure.Paging.trackerExpectedCost`, `Cslib.DataStructure.Paging.cleanCount`:
  deterministic phase bookkeeping, stale-subset cache law, exact rational expected cost recursion,
  and clean-request count.

## Main results

* `markLaw_bind_markingStep`, `expectedCost_markingStrategy_eq`: exact distribution invariant and
  rational expected-cost formula.
* `trackerExpectedCost_le_harmonic_mul_cleanCount`: harmonic potential bound
  `E[MARK] ≤ H_k · #clean`.
* `cleanCount_le_two_mul_scheduleCost`: FKLMSY two-window bound `#clean ≤ 2 · OPT` against arbitrary
  valid offline schedules.
* `markingStrategy_expectedCost_le`, `markingStrategy_isCompetitive`,
  `markingStrategy_expectedCost_toReal_le`: randomized marking is `(2 * H_k, 0)`-competitive in
  `ℝ≥0∞` and `ℝ`.

## References

* [A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator, and N. E. Young, *Competitive Paging
  Algorithms*][FiatKarpLubyMcGeochSleatorYoung1991], Section 3, Theorem 1.
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

open scoped ENNReal

public section

namespace Cslib.DataStructure.Paging

open Cslib.DataStructure.Online
open Cslib.Probability.PMF

/-! ### Controller memory and deterministic tracker types -/

/-- Internal controller memory of the randomized marking algorithm: the resident `cache` together
with the subset of pages `marked` during the current phase. -/
structure MarkMem (α : Type) where
  /-- Pages currently held in fast memory. -/
  cache : Finset α
  /-- Subset of cached pages marked in the current phase. -/
  marked : Finset α
  deriving DecidableEq

/-- Representation invariant of `MarkMem`: the cache holds at most `k` pages and every marked page
is resident in the cache. -/
@[expose]
def ValidMarkMem {α : Type} (k : ℕ) (m : MarkMem α) : Prop :=
  m.cache.card ≤ k ∧ m.marked ⊆ m.cache

/-- Deterministic phase bookkeeping for the distribution invariant of `markingStrategy`:
`marked` is the set of pages marked in the current phase, `stale` is the set of unmarked pages from
the previous phase not yet requested in the current phase, and `staleCached` is the number of stale
pages currently retained in the cache. -/
structure MarkTracker (α : Type) where
  /-- Pages marked in the current phase. -/
  marked : Finset α
  /-- Stale pages from the previous phase not yet requested in the current phase. -/
  stale : Finset α
  /-- Number of stale pages currently held in the cache. -/
  staleCached : ℕ
  deriving DecidableEq

/-- Initial tracker state corresponding to `markingStrategy.init s₀`: all pages of `s₀` are marked
and no stale pages exist yet. -/
@[expose]
def initTracker {α : Type} (s₀ : Finset α) : MarkTracker α :=
  ⟨s₀, ∅, 0⟩

/-- Structural invariant of `MarkTracker` for cache capacity `k`. -/
@[expose]
def ValidTracker {α : Type} (k : ℕ) (tr : MarkTracker α) : Prop :=
  Disjoint tr.marked tr.stale ∧
    tr.staleCached ≤ tr.stale.card ∧
    tr.stale.card ≤ k ∧
    tr.marked.card + tr.staleCached ≤ k ∧
    (0 < tr.staleCached → tr.marked.card + tr.staleCached = k)

theorem validTracker_init {α : Type} {k : ℕ} {s₀ : Finset α} (hs₀ : ValidCache k s₀) :
    ValidTracker k (initTracker s₀) :=
  ⟨Finset.disjoint_empty_right s₀, le_rfl, Nat.zero_le k, hs₀,
    fun h => absurd h (Nat.lt_irrefl 0)⟩

/-- Harmonic phase potential `c * (H_{|stale|} - H_c)` where `c = |stale| - staleCached` is the
number of clean misses incurred so far in the current phase. -/
@[expose]
def trackerPotential {α : Type} (tr : MarkTracker α) : ℚ :=
  let c := tr.stale.card - tr.staleCached
  (c : ℚ) * (harmonic tr.stale.card - harmonic c)

theorem trackerPotential_init {α : Type} (s₀ : Finset α) :
    trackerPotential (initTracker s₀) = 0 := by
  simp only [trackerPotential, initTracker, Finset.card_empty, Nat.sub_zero, Nat.cast_zero,
    zero_mul]

theorem trackerPotential_nonneg {α : Type} (tr : MarkTracker α) :
    0 ≤ trackerPotential tr := by
  unfold trackerPotential
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (harmonic_mono (Nat.sub_le _ _)))

section Decidable

variable {α : Type} [DecidableEq α]

/-! ### Behavioural marking strategy -/

/-- One-step randomized transition of the marking algorithm for cache capacity `k` on page `p`. -/
@[expose]
noncomputable def markingStep (k : ℕ) (m : MarkMem α) (p : α) : PMF (MarkMem α) :=
  if p ∈ m.cache then
    PMF.pure ⟨m.cache, insert p m.marked⟩
  else if m.cache.card < k then
    PMF.pure ⟨insert p m.cache, insert p m.marked⟩
  else
    let marked₁ := if m.cache ⊆ m.marked then ∅ else m.marked
    if hunm : (m.cache \ marked₁).Nonempty then
      (uniformOfFinset (m.cache \ marked₁) hunm).map fun e =>
        ⟨insert p (m.cache.erase e), insert p marked₁⟩
    else
      PMF.pure ⟨{p}, {p}⟩

private theorem unmarked_nonempty_of_full {k : ℕ} (hk : 0 < k) {m : MarkMem α}
    (hm : ValidMarkMem k m) (hnotlt : ¬ m.cache.card < k) :
    (m.cache \ (if m.cache ⊆ m.marked then ∅ else m.marked)).Nonempty := by
  have hcard : m.cache.card = k := le_antisymm hm.1 (Nat.not_lt.mp hnotlt)
  by_cases hsub : m.cache ⊆ m.marked
  · simp only [hsub, ↓reduceIte, Finset.sdiff_empty]
    exact Finset.card_pos.mp (hcard ▸ hk)
  · simp only [hsub, ↓reduceIte]
    obtain ⟨e, he_cache, he_not_marked⟩ := Finset.not_subset.mp hsub
    exact ⟨e, Finset.mem_sdiff.mpr ⟨he_cache, he_not_marked⟩⟩

/-- **The randomized marking online strategy** ([FiatKarpLubyMcGeochSleatorYoung1991], Section 3)
for `Paging.problem α k` (`0 < k`). Marks are initialized to the initial cache `s₀`; hits mark the
requested page; misses into a non-full cache insert and mark without eviction; misses into a full
cache unmark all pages when every cached page is marked and evict uniformly among unmarked cached
pages. -/
noncomputable abbrev markingStrategy (k : ℕ) (hk : 0 < k) :
    BehavioralStrategy (problem α k) where
  Mem := MarkMem α
  ValidMem := ValidMarkMem k
  project m := m.cache
  init s₀ := ⟨s₀, s₀⟩
  step m p := markingStep k m p
  valid_init hs₀ := ⟨⟨hs₀, Finset.Subset.refl _⟩, rfl⟩
  valid_step {m} p hm m' hm' := by
    dsimp only [markingStep] at hm'
    by_cases hp : p ∈ m.cache
    · simp only [hp, ↓reduceIte, PMF.support_pure, Set.mem_singleton_iff] at hm'
      subst hm'
      exact ⟨⟨hm.1, Finset.insert_subset hp hm.2⟩, validStep_hit hm.1 hp⟩
    · simp only [hp, ↓reduceIte] at hm'
      by_cases hlt : m.cache.card < k
      · simp only [hlt, ↓reduceIte, PMF.support_pure, Set.mem_singleton_iff] at hm'
        subst hm'
        have hstep := validStep_insert hlt hp
        exact ⟨⟨hstep.2.1, Finset.insert_subset_insert p hm.2⟩, hstep⟩
      · have hunm := unmarked_nonempty_of_full hk hm hlt
        simp only [hlt, ↓reduceIte, dite_eq_left hunm, PMF.mem_support_map_iff,
          mem_support_uniformOfFinset_iff] at hm'
        obtain ⟨e, he, rfl⟩ := hm'
        obtain ⟨he_cache, he_not_m1⟩ := Finset.mem_sdiff.mp he
        have hstep := validStep_replace hm.1 hp he_cache
        refine ⟨⟨hstep.2.1, Finset.insert_subset_insert p ?_⟩, hstep⟩
        intro x hx
        refine Finset.mem_erase.mpr ⟨fun hxe => he_not_m1 (hxe ▸ hx), ?_⟩
        split_ifs at hx with hsub
        · exact absurd hx (Finset.notMem_empty x)
        · exact hm.2 hx

/-- Single-step expected cost of `markingStrategy` depends only on whether `p` is currently cached:
`0` on a hit and `1` on a miss. -/
theorem stepExpectedCost_markingStrategy {k : ℕ} (hk : 0 < k) (m : MarkMem α) (p : α) :
    (markingStrategy k hk).stepExpectedCost m p = if p ∈ m.cache then 0 else 1 := by
  simp only [BehavioralStrategy.stepExpectedCost, markingStrategy, problem, stepCost]
  by_cases hp : p ∈ m.cache
  · simp only [hp, ↓reduceIte, Nat.cast_zero, mul_zero, tsum_zero]
  · simp only [hp, ↓reduceIte, Nat.cast_one, mul_one]
    exact (markingStep k m p).tsum_coe

/-- Expected cost of `markingStrategy` on any valid initial cache and request sequence `reqs` is at
most `reqs.length`, hence finite (`≠ ⊤`). -/
theorem expectedCost_markingStrategy_le_length {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) (reqs : List α) :
    (markingStrategy k hk).expectedCost s₀ reqs ≤ reqs.length := by
  rw [BehavioralStrategy.expectedCost]
  simpa only [Nat.cast_one, one_mul] using
    (markingStrategy k hk).expectedCostFrom_le_mul_length (w := 1)
      (fun _ r m' _ => stepCost_le_one _ r m'.cache)
      (((markingStrategy k hk).valid_init hs₀).1) reqs

theorem expectedCost_markingStrategy_ne_top {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) (reqs : List α) :
    (markingStrategy k hk).expectedCost s₀ reqs ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top reqs.length)
    (expectedCost_markingStrategy_le_length hk hs₀ reqs)

/-! ### Exact stale-subset distribution law -/

/-- Deterministic transition of `MarkTracker` on page request `p`. -/
@[expose]
def stepTracker (k : ℕ) (tr : MarkTracker α) (p : α) : MarkTracker α :=
  if p ∈ tr.marked then
    tr
  else if tr.staleCached = 0 then
    if tr.marked.card < k then
      ⟨insert p tr.marked, ∅, 0⟩
    else
      ⟨{p}, tr.marked, k - 1⟩
  else if p ∈ tr.stale then
    ⟨insert p tr.marked, tr.stale.erase p, tr.staleCached - 1⟩
  else
    ⟨insert p tr.marked, tr.stale, tr.staleCached - 1⟩

/-- Run `stepTracker` across a request list. -/
@[expose]
def runTracker (k : ℕ) (tr : MarkTracker α) : List α → MarkTracker α
  | [] => tr
  | p :: rs => runTracker k (stepTracker k tr p) rs

/-- Whether request `p` is *clean* relative to tracker `tr` (unmarked, and either starting a new
phase/warmup slot when `staleCached = 0` or outside `tr.stale`). -/
@[expose]
def isCleanReq (tr : MarkTracker α) (p : α) : Bool :=
  decide (p ∉ tr.marked ∧ (tr.staleCached = 0 ∨ p ∉ tr.stale))

/-- Total number of clean requests encountered from tracker `tr` along `reqs`. -/
@[expose]
def cleanCount (k : ℕ) : MarkTracker α → List α → ℕ
  | _, [] => 0
  | tr, p :: rs => (if isCleanReq tr p then 1 else 0) + cleanCount k (stepTracker k tr p) rs

/-- Exact rational single-step expected fault cost from tracker `tr` on request `p`. -/
@[expose]
def stepTrackerCost (tr : MarkTracker α) (p : α) : ℚ :=
  if p ∈ tr.marked then
    0
  else if tr.staleCached = 0 then
    1
  else if p ∈ tr.stale then
    ((tr.stale.card - tr.staleCached : ℕ) : ℚ) / (tr.stale.card : ℚ)
  else
    1

/-- Exact rational expected fault cost from tracker `tr` across `reqs`. -/
@[expose]
def trackerExpectedCost (k : ℕ) : MarkTracker α → List α → ℚ
  | _, [] => 0
  | tr, p :: rs => stepTrackerCost tr p + trackerExpectedCost k (stepTracker k tr p) rs

theorem stepTrackerCost_nonneg (tr : MarkTracker α) (p : α) : 0 ≤ stepTrackerCost tr p := by
  unfold stepTrackerCost
  split_ifs <;> positivity

theorem trackerExpectedCost_nonneg (k : ℕ) (tr : MarkTracker α) (reqs : List α) :
    0 ≤ trackerExpectedCost k tr reqs := by
  induction reqs generalizing tr with
  | nil => exact le_rfl
  | cons p rs ih => exact add_nonneg (stepTrackerCost_nonneg tr p) (ih (stepTracker k tr p))

/-- `stepTracker` preserves `ValidTracker` when `0 < k`. -/
theorem validTracker_step {k : ℕ} (hk : 0 < k) {tr : MarkTracker α} (htr : ValidTracker k tr)
    (p : α) : ValidTracker k (stepTracker k tr p) := by
  obtain ⟨hdisj, hst, hsk, hmk, hfull⟩ := htr
  unfold stepTracker
  by_cases hpM : p ∈ tr.marked
  · simp only [hpM, ↓reduceIte]
    exact ⟨hdisj, hst, hsk, hmk, hfull⟩
  · simp only [hpM, ↓reduceIte]
    by_cases ht0 : tr.staleCached = 0
    · simp only [ht0, ↓reduceIte]
      by_cases hlt : tr.marked.card < k
      · simp only [hlt, ↓reduceIte]
        dsimp only [ValidTracker]
        refine ⟨Finset.disjoint_empty_right _, le_rfl, Nat.zero_le k, ?_,
          fun h => absurd h (Nat.lt_irrefl 0)⟩
        rw [Finset.card_insert_of_notMem hpM]
        omega
      · simp only [hlt, ↓reduceIte]
        dsimp only [ValidTracker]
        have hMcard : tr.marked.card = k := by omega
        refine ⟨Finset.disjoint_singleton_left.mpr hpM, by omega, by omega, ?_, fun _ => ?_⟩ <;>
          simp only [Finset.card_singleton] <;> omega
    · have htpos : 0 < tr.staleCached := Nat.pos_of_ne_zero ht0
      have hsum : tr.marked.card + tr.staleCached = k := hfull htpos
      simp only [ht0, ↓reduceIte]
      by_cases hpS : p ∈ tr.stale
      · simp only [hpS, ↓reduceIte]
        dsimp only [ValidTracker]
        refine ⟨Finset.disjoint_insert_left.mpr
          ⟨Finset.notMem_erase p tr.stale,
            hdisj.mono_right (Finset.erase_subset p tr.stale)⟩, ?_, ?_, ?_, fun _ => ?_⟩
        · rw [Finset.card_erase_of_mem hpS]
          omega
        · exact Finset.card_erase_le.trans hsk
        · rw [Finset.card_insert_of_notMem hpM]
          omega
        · rw [Finset.card_insert_of_notMem hpM]
          omega
      · simp only [hpS, ↓reduceIte]
        dsimp only [ValidTracker]
        refine ⟨Finset.disjoint_insert_left.mpr ⟨hpS, hdisj⟩, by omega, hsk, ?_, fun _ => ?_⟩ <;>
          rw [Finset.card_insert_of_notMem hpM] <;> omega

/-- Exact memory distribution associated with tracker `tr`: the cache is `tr.marked ∪ U` for a
uniform `tr.staleCached`-subset `U` of `tr.stale`, and the marked set is `tr.marked`. -/
@[expose]
noncomputable def markLaw (tr : MarkTracker α) : PMF (MarkMem α) :=
  if h : (tr.stale.powersetCard tr.staleCached).Nonempty then
    (uniformOfFinset (tr.stale.powersetCard tr.staleCached) h).map
      fun U => ⟨tr.marked ∪ U, tr.marked⟩
  else
    PMF.pure ⟨tr.marked, tr.marked⟩

/-- Whenever `staleCached = 0`, `markLaw` collapses to the point mass at `⟨marked, marked⟩`. -/
theorem markLaw_of_staleCached_eq_zero {M S : Finset α} :
    markLaw ⟨M, S, 0⟩ = PMF.pure ⟨M, M⟩ := by
  have hne : (S.powersetCard 0).Nonempty := Finset.powersetCard_nonempty.mpr (Nat.zero_le _)
  rw [markLaw, dite_eq_left hne]
  ext m
  rw [PMF.map_apply, tsum_eq_single (∅ : Finset α)]
  · simp only [Finset.powersetCard_zero, Finset.mem_singleton, uniformOfFinset_apply, ↓reduceIte,
      Finset.card_singleton, Nat.cast_one, inv_one, Finset.union_empty, PMF.pure_apply]
    split_ifs <;> rfl
  · intro U hU
    simp only [Finset.powersetCard_zero, uniformOfFinset_apply, Finset.mem_singleton, hU,
      ↓reduceIte, ite_self]

theorem markLaw_initTracker (s₀ : Finset α) :
    markLaw (initTracker s₀) = PMF.pure ⟨s₀, s₀⟩ :=
  markLaw_of_staleCached_eq_zero

private theorem uniformOfFinset_congr {β : Type*} {s₁ s₂ : Finset β}
    {h₁ : s₁.Nonempty} {h₂ : s₂.Nonempty} (h : s₁ = s₂) :
    uniformOfFinset s₁ h₁ = uniformOfFinset s₂ h₂ := by
  subst h
  rfl

private theorem markingStep_on_union {k : ℕ} {M U : Finset α} {p : α}
    (hdisj : Disjoint M U) (hcard : M.card + U.card = k) (hU : U.Nonempty) (hpM : p ∉ M) :
    markingStep k ⟨M ∪ U, M⟩ p =
      (if p ∈ U then PMF.pure (U.erase p) else uniformErase U).map
        fun V => ⟨insert p M ∪ V, insert p M⟩ := by
  have hMU_card : (M ∪ U).card = k := by
    rw [Finset.card_union_of_disjoint hdisj, hcard]
  have hnotlt : ¬ (M ∪ U).card < k := by omega
  have hnot_sub : ¬ M ∪ U ⊆ M := by
    obtain ⟨x, hxU⟩ := hU
    intro hsub
    exact Finset.disjoint_left.mp hdisj (hsub (Finset.mem_union_right M hxU)) hxU
  have hsdiff : (M ∪ U) \ M = U := Finset.union_sdiff_cancel_left hdisj
  by_cases hpU : p ∈ U
  · have hpMU : p ∈ M ∪ U := Finset.mem_union_right M hpU
    have hunion : insert p M ∪ U.erase p = M ∪ U := by
      rw [Finset.insert_union, ← Finset.union_comm (U.erase p) M, ← Finset.insert_union,
        Finset.insert_erase hpU, Finset.union_comm U M]
    simp only [markingStep, hpMU, hpU, ↓reduceIte, PMF.pure_map, hunion]
  · have hpMU : p ∉ M ∪ U := by
      rw [Finset.mem_union, not_or]
      exact ⟨hpM, hpU⟩
    have hunm_sdiff : ((M ∪ U) \ M).Nonempty := by
      rw [hsdiff]
      exact hU
    simp only [markingStep, hpMU, hpU, hnotlt, hnot_sub, ↓reduceIte, dite_eq_left hunm_sdiff,
      uniformErase, dite_eq_left hU, PMF.map_comp]
    rw [uniformOfFinset_congr (h₂ := hU) hsdiff]
    ext m
    simp only [PMF.map_apply, Function.comp_apply]
    refine tsum_congr fun e => ?_
    by_cases heU : e ∈ U
    · have heM : e ∉ M := Finset.disjoint_right.mp hdisj heU
      have herase : (M ∪ U).erase e = M ∪ U.erase e := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem heM]
      simp only [herase, Finset.insert_union]
    · simp only [uniformOfFinset_apply, heU, ↓reduceIte, ite_self]

/-- **Exact distribution invariant of randomized marking.** Stepping `markLaw tr` by `markingStep`
on any request `p` produces `markLaw (stepTracker k tr p)`. -/
theorem markLaw_bind_markingStep {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    (htr : ValidTracker k tr) (p : α) :
    (markLaw tr).bind (fun m => markingStep k m p) = markLaw (stepTracker k tr p) := by
  obtain ⟨hdisj, hst, hsk, hmk, hfull⟩ := htr
  have hne : (tr.stale.powersetCard tr.staleCached).Nonempty :=
    Finset.powersetCard_nonempty.mpr hst
  by_cases hpM : p ∈ tr.marked
  · have hinsert : insert p tr.marked = tr.marked := Finset.insert_eq_of_mem hpM
    simp only [stepTracker, hpM, ↓reduceIte]
    rw [markLaw, dite_eq_left hne, PMF.bind_map, ← PMF.bind_pure_comp]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun U _ => ?_
    have hpMU : p ∈ tr.marked ∪ U := Finset.mem_union_left U hpM
    simp only [Function.comp_apply, markingStep, hpMU, ↓reduceIte, hinsert]
  · by_cases ht0 : tr.staleCached = 0
    · rcases tr with ⟨M, S, t⟩
      dsimp only at hpM ht0 hdisj hst hsk hmk hfull
      subst ht0
      rw [markLaw_of_staleCached_eq_zero, PMF.pure_bind]
      simp only [stepTracker, hpM, ↓reduceIte]
      by_cases hlt : M.card < k
      · simp only [hlt, ↓reduceIte, markingStep, hpM, markLaw_of_staleCached_eq_zero]
      · have hMcard : M.card = k := by omega
        have hMne : M.Nonempty := Finset.card_pos.mp (hMcard ▸ hk)
        simp only [hlt, ↓reduceIte, markingStep, hpM, Finset.Subset.refl, Finset.sdiff_empty,
          dite_eq_left hMne]
        have hne_k1 : (M.powersetCard (k - 1)).Nonempty :=
          Finset.powersetCard_nonempty.mpr (by omega)
        rw [markLaw, dite_eq_left hne_k1]
        have hpure :
            uniformOfFinset (M.powersetCard k)
              (Finset.powersetCard_nonempty.mpr (by omega)) = PMF.pure M := by
          ext U
          have hself : M.powersetCard k = {M} := hMcard ▸ Finset.powersetCard_self M
          by_cases hUM : U = M
          · subst hUM
            simp only [hself, uniformOfFinset_apply, Finset.mem_singleton, ↓reduceIte,
              Finset.card_singleton, Nat.cast_one, inv_one, PMF.pure_apply]
          · simp only [hself, uniformOfFinset_apply, Finset.mem_singleton, hUM, ↓reduceIte,
              PMF.pure_apply]
        have herase := uniformOfFinset_powersetCard_erase (S := M) (t := k) hk (by omega)
        rw [hpure, PMF.pure_bind, uniformErase, dite_eq_left hMne] at herase
        rw [← herase, PMF.map_comp]
        ext m
        simp only [PMF.map_apply, Function.comp_apply, Finset.singleton_union, Finset.insert_empty]
    · have htpos : 0 < tr.staleCached := Nat.pos_of_ne_zero ht0
      have ht1 : 1 ≤ tr.staleCached := htpos
      have hsum : tr.marked.card + tr.staleCached = k := hfull htpos
      rw [markLaw, dite_eq_left hne, PMF.bind_map]
      simp only [stepTracker, hpM, ht0, ↓reduceIte]
      by_cases hpS : p ∈ tr.stale
      · simp only [hpS, ↓reduceIte]
        have hne' : ((tr.stale.erase p).powersetCard (tr.staleCached - 1)).Nonempty :=
          Finset.powersetCard_nonempty.mpr (by rw [Finset.card_erase_of_mem hpS]; omega)
        rw [markLaw, dite_eq_left hne',
          ← uniformOfFinset_powersetCard_hitOrErase hpS ht1 hst, PMF.map_bind]
        refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun U hU => ?_
        rw [mem_support_uniformOfFinset_iff] at hU
        obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU
        have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
        exact markingStep_on_union (hdisj.mono_right hUS) (hUcard ▸ hsum) hU_ne hpM
      · simp only [hpS, ↓reduceIte]
        have hne' : (tr.stale.powersetCard (tr.staleCached - 1)).Nonempty :=
          Finset.powersetCard_nonempty.mpr (by omega)
        rw [markLaw, dite_eq_left hne',
          ← uniformOfFinset_powersetCard_erase ht1 hst, PMF.map_bind]
        refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun U hU => ?_
        rw [mem_support_uniformOfFinset_iff] at hU
        obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU
        have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
        have hpU : p ∉ U := fun hp => hpS (hUS hp)
        rw [Function.comp_apply, markingStep_on_union (hdisj.mono_right hUS)
          (hUcard ▸ hsum) hU_ne hpM, ite_eq_right hpU]

/-- Single-step expected fault cost of `markingStrategy` under `markLaw tr` equals
`ENNReal.ofReal (stepTrackerCost tr p)`. -/
theorem stepExpectedCost_markLaw {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    (htr : ValidTracker k tr) (p : α) :
    (∑' m, markLaw tr m * (markingStrategy k hk).stepExpectedCost m p) =
      ENNReal.ofReal (stepTrackerCost tr p) := by
  obtain ⟨_, hst, _, _, _⟩ := htr
  have hne : (tr.stale.powersetCard tr.staleCached).Nonempty :=
    Finset.powersetCard_nonempty.mpr hst
  rw [markLaw, dite_eq_left hne, tsum_map_mul]
  simp only [stepExpectedCost_markingStrategy]
  by_cases hpM : p ∈ tr.marked
  · have hmem : ∀ U : Finset α, p ∈ tr.marked ∪ U := fun U => Finset.mem_union_left U hpM
    simp only [hmem, ↓reduceIte, mul_zero, tsum_zero, stepTrackerCost, hpM, Rat.cast_zero,
      ENNReal.ofReal_zero]
  · by_cases ht0 : tr.staleCached = 0
    · rcases tr with ⟨M, S, t⟩
      dsimp only at hpM ht0 hst hne
      subst ht0
      simp only [stepTrackerCost, hpM, ↓reduceIte, Rat.cast_one, ENNReal.ofReal_one]
      rw [tsum_eq_single (∅ : Finset α)]
      · simp only [Finset.powersetCard_zero, Finset.mem_singleton, uniformOfFinset_apply,
          ↓reduceIte, Finset.card_singleton, Nat.cast_one, inv_one, Finset.union_empty, hpM,
          one_mul]
      · intro U hU
        simp only [Finset.powersetCard_zero, uniformOfFinset_apply, Finset.mem_singleton, hU,
          ↓reduceIte, zero_mul]
    · simp only [stepTrackerCost, hpM, ht0, ↓reduceIte]
      by_cases hpS : p ∈ tr.stale
      · simp only [hpS, ↓reduceIte]
        have hnotMem : ∀ U : Finset α, (p ∈ tr.marked ∪ U) ↔ p ∈ U := fun U => by
          simp only [Finset.mem_union, hpM, false_or]
        have hind :
            (∑' U, uniformOfFinset (tr.stale.powersetCard tr.staleCached) hne U *
              if p ∈ tr.marked ∪ U then (0 : ℝ≥0∞) else 1) =
              (uniformOfFinset (tr.stale.powersetCard tr.staleCached) hne).toOuterMeasure
                {U | p ∉ U} := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun U => ?_
          simp only [hnotMem]
          by_cases hpU : p ∈ U <;> simp [hpU]
        rw [hind, toOuterMeasure_uniformOfFinset_powersetCard_notMem hpS hst]
        have hSpos : (0 : ℝ) < (tr.stale.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨p, hpS⟩
        rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, ENNReal.ofReal_div_of_pos hSpos,
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]
      · simp only [hpS, ↓reduceIte, Rat.cast_one, ENNReal.ofReal_one]
        calc (∑' U, uniformOfFinset (tr.stale.powersetCard tr.staleCached) hne U *
              if p ∈ tr.marked ∪ U then (0 : ℝ≥0∞) else 1)
            = ∑' U, uniformOfFinset (tr.stale.powersetCard tr.staleCached) hne U * 1 := by
              refine tsum_congr fun U => ?_
              by_cases hU : U ∈ tr.stale.powersetCard tr.staleCached
              · have hpU : p ∉ U := fun hp => hpS ((Finset.mem_powersetCard.mp hU).1 hp)
                have hpMU : p ∉ tr.marked ∪ U := by
                  rw [Finset.mem_union, not_or]
                  exact ⟨hpM, hpU⟩
                simp only [hpMU, ↓reduceIte]
              · simp only [uniformOfFinset_apply, hU, ↓reduceIte, zero_mul]
          _ = 1 := by
              simp only [mul_one]
              exact (uniformOfFinset _ hne).tsum_coe

/-- Expected continuation cost of `markingStrategy` from `markLaw tr` equals
`ENNReal.ofReal (trackerExpectedCost k tr reqs)`. -/
theorem expectedCostDist_markLaw_eq {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    (htr : ValidTracker k tr) (reqs : List α) :
    (markingStrategy k hk).expectedCostDist (markLaw tr) reqs =
      ENNReal.ofReal (trackerExpectedCost k tr reqs) := by
  induction reqs generalizing tr with
  | nil =>
    rw [(markingStrategy k hk).expectedCostDist_nil]
    simp only [trackerExpectedCost, Rat.cast_zero, ENNReal.ofReal_zero]
  | cons p rs ih =>
    rw [(markingStrategy k hk).expectedCostDist_cons, stepExpectedCost_markLaw hk htr p,
      markLaw_bind_markingStep hk htr p, ih (validTracker_step hk htr p), trackerExpectedCost,
      Rat.cast_add, ENNReal.ofReal_add
        (by exact_mod_cast stepTrackerCost_nonneg tr p)
        (by exact_mod_cast trackerExpectedCost_nonneg k (stepTracker k tr p) rs)]

/-- **Exact rational expected cost of randomized marking.** From any valid initial cache `s₀`,
`(markingStrategy k hk).expectedCost s₀ reqs` equals
`ENNReal.ofReal (trackerExpectedCost k (initTracker s₀) reqs)`. -/
theorem expectedCost_markingStrategy_eq {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) (reqs : List α) :
    (markingStrategy k hk).expectedCost s₀ reqs =
      ENNReal.ofReal (trackerExpectedCost k (initTracker s₀) reqs) := by
  have h := expectedCostDist_markLaw_eq hk (validTracker_init hs₀) reqs
  rwa [markLaw_initTracker, BehavioralStrategy.expectedCostDist_pure] at h

/-! ### Harmonic potential bound (`E[MARK] ≤ H_k · #clean`) -/

/-- Single-step harmonic potential inequality: each stale request is paid exactly out of
`trackerPotential`, and each clean request increases `cost + potential` by at most `harmonic k`. -/
theorem stepTrackerCost_add_potential_le {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    (htr : ValidTracker k tr) (p : α) :
    stepTrackerCost tr p + trackerPotential (stepTracker k tr p) ≤
      (if isCleanReq tr p then harmonic k else 0) + trackerPotential tr := by
  obtain ⟨_, hst, hsk, _, _⟩ := htr
  by_cases hpM : p ∈ tr.marked
  · have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM]
    simp only [stepTrackerCost, stepTracker, hpM, hclean, ↓reduceIte, Bool.false_eq_true, zero_add,
      le_rfl]
  · by_cases ht0 : tr.staleCached = 0
    · have hclean : isCleanReq tr p = true := by simp [isCleanReq, hpM, ht0]
      have hpot0 : trackerPotential tr = 0 := by
        simp only [trackerPotential, ht0, Nat.sub_zero, sub_self, mul_zero]
      simp only [stepTrackerCost, stepTracker, hpM, ht0, hclean, ↓reduceIte, hpot0, add_zero]
      by_cases hlt : tr.marked.card < k
      · simp only [hlt, ↓reduceIte, trackerPotential, Finset.card_empty, Nat.sub_zero,
          Nat.cast_zero, zero_mul, add_zero]
        exact one_le_harmonic hk.ne'
      · have hMcard : tr.marked.card = k := by omega
        have hsub1 : k - (k - 1) = 1 := by omega
        simp only [hlt, ↓reduceIte, trackerPotential]
        rw [hMcard, hsub1]
        simp only [Nat.cast_one, one_mul, harmonic_succ 0, harmonic_zero, zero_add, inv_one]
        linarith
    · have htpos : 0 < tr.staleCached := Nat.pos_of_ne_zero ht0
      by_cases hpS : p ∈ tr.stale
      · have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM, ht0, hpS]
        simp only [stepTrackerCost, stepTracker, hpM, ht0, hpS, hclean, ↓reduceIte,
          Bool.false_eq_true, zero_add, trackerPotential]
        have hm1 : 1 ≤ tr.stale.card := Finset.card_pos.mpr ⟨p, hpS⟩
        have herase_card : (tr.stale.erase p).card = tr.stale.card - 1 :=
          Finset.card_erase_of_mem hpS
        have hc_eq : (tr.stale.card - 1) - (tr.staleCached - 1) = tr.stale.card - tr.staleCached :=
          by omega
        have hharm_m :
            harmonic tr.stale.card = harmonic (tr.stale.card - 1) + ((tr.stale.card : ℚ))⁻¹ := by
          have hm_succ : tr.stale.card = (tr.stale.card - 1) + 1 := by omega
          conv_lhs => rw [hm_succ, harmonic_succ]
          have hcast :
              (((tr.stale.card - 1 : ℕ) + 1 : ℕ) : ℚ) = (tr.stale.card : ℚ) := by
            exact_mod_cast hm_succ.symm
          rw [hcast]
        rw [herase_card, hc_eq, hharm_m, div_eq_mul_inv]
        linarith
      · have hclean : isCleanReq tr p = true := by simp [isCleanReq, hpM, hpS]
        simp only [stepTrackerCost, stepTracker, hpM, ht0, hpS, hclean, ↓reduceIte,
          trackerPotential]
        have hc_succ : tr.stale.card - (tr.staleCached - 1) =
            (tr.stale.card - tr.staleCached) + 1 := by omega
        rw [hc_succ, harmonic_succ (tr.stale.card - tr.staleCached)]
        set c := tr.stale.card - tr.staleCached
        have hc1_ne : ((c + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hident :
            1 + ((c + 1 : ℕ) : ℚ) *
                (harmonic tr.stale.card - (harmonic c + ((c + 1 : ℕ) : ℚ)⁻¹)) =
              (harmonic tr.stale.card - harmonic c) +
                (c : ℚ) * (harmonic tr.stale.card - harmonic c) := by
          push_cast
          field_simp [hc1_ne]
          ring
        rw [hident]
        have hhm : harmonic tr.stale.card ≤ harmonic k := harmonic_mono hsk
        have hhc : 0 ≤ harmonic c := harmonic_nonneg c
        linarith

/-- Telescoped harmonic potential inequality over any request list `reqs`. -/
theorem trackerExpectedCost_add_potential_le {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    (htr : ValidTracker k tr) (reqs : List α) :
    trackerExpectedCost k tr reqs + trackerPotential (runTracker k tr reqs) ≤
      harmonic k * (cleanCount k tr reqs : ℚ) + trackerPotential tr := by
  induction reqs generalizing tr with
  | nil =>
    simp only [trackerExpectedCost, runTracker, cleanCount, Nat.cast_zero, mul_zero, zero_add,
      le_rfl]
  | cons p rs ih =>
    simp only [trackerExpectedCost, runTracker, cleanCount]
    have hstep := stepTrackerCost_add_potential_le hk htr p
    have hih := ih (validTracker_step hk htr p)
    have hcast :
        harmonic k * (((if isCleanReq tr p then 1 else 0) +
          cleanCount k (stepTracker k tr p) rs : ℕ) : ℚ) =
          (if isCleanReq tr p then harmonic k else 0) +
            harmonic k * (cleanCount k (stepTracker k tr p) rs : ℚ) := by
      push_cast
      split_ifs <;> ring
    rw [hcast]
    linarith

/-- **Harmonic phase bound (`E[MARK] ≤ H_k · #clean`).** From any valid initial cache `s₀`, the
rational expected cost of `markingStrategy` is at most `harmonic k` times the number of clean
requests. -/
theorem trackerExpectedCost_le_harmonic_mul_cleanCount {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) (reqs : List α) :
    trackerExpectedCost k (initTracker s₀) reqs ≤
      harmonic k * (cleanCount k (initTracker s₀) reqs : ℚ) := by
  have h := trackerExpectedCost_add_potential_le hk (validTracker_init hs₀) reqs
  have hpos := trackerPotential_nonneg (runTracker k (initTracker s₀) reqs)
  rw [trackerPotential_init, add_zero] at h
  linarith

/-! ### FKLMSY two-window offline lower bound (`#clean ≤ 2 · OPT`) -/

private theorem card_sdiff_le_add_card {A P S B : Finset α} (hsub : A ⊆ S ∪ B) :
    (A \ P).card ≤ (S \ P).card + B.card := by
  have hinc : A \ P ⊆ (S \ P) ∪ B := by
    intro x hx
    obtain ⟨hxA, hxP⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (hsub hxA) with hxS | hxB
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxS, hxP⟩)
    · exact Finset.mem_union_right _ hxB
  exact (Finset.card_le_card hinc).trans (Finset.card_union_le _ _)

private theorem card_sdiff_le_card_of_full {k : ℕ} {M S_off S_start B : Finset α}
    (hS_off : S_off ⊆ S_start ∪ B) (hM : M ⊆ S_start ∪ B) (hM_card : M.card = k)
    (hS_start : S_start.card ≤ k) :
    (S_off \ M).card ≤ B.card := by
  have hsub : S_off \ M ⊆ (S_start ∪ B) \ M :=
    Finset.sdiff_subset_sdiff hS_off (Finset.Subset.refl _)
  have hcard1 : ((S_start ∪ B) \ M).card = (S_start ∪ B).card - k := by
    rw [Finset.card_sdiff_of_subset hM, hM_card]
  have hcard2 : (S_start ∪ B).card ≤ k + B.card := by
    have h := Finset.card_union_le S_start B
    omega
  have hle := Finset.card_le_card hsub
  omega

/-- Active-phase backward induction for `#clean ≤ 2 · OPT`: tracks the previous phase's marked set
`P_prev` (`|P_prev| = k`), the offline cache `s_start` at the start of the current phase, and the
set `B` of pages faulted on by the offline schedule so far in the current phase. -/
private theorem cleanCount_active_bound {k : ℕ} (hk : 0 < k) {tr : MarkTracker α}
    {P_prev s_start B s_off : Finset α} {reqs : List α} {offStates : List (Finset α)}
    (htr : ValidTracker k tr)
    (hP_card : P_prev.card = k)
    (hstale : tr.stale = P_prev \ tr.marked)
    (hsum : tr.marked.card + tr.staleCached = k)
    (hs_start : s_start.card ≤ k)
    (hs_off_sub : s_off ⊆ s_start ∪ B)
    (hM_sub : tr.marked ⊆ s_start ∪ B)
    (hv : (problem α k).ValidSchedule s_off reqs offStates) :
    (tr.marked \ P_prev).card + cleanCount k tr reqs ≤
      (s_start \ P_prev).card + 2 * B.card +
        2 * (problem α k).scheduleCost s_off reqs offStates := by
  induction reqs generalizing offStates s_off tr P_prev s_start B with
  | nil =>
    cases offStates with
    | nil =>
      change (tr.marked \ P_prev).card + 0 ≤ (s_start \ P_prev).card + 2 * B.card + 2 * 0
      have hle := card_sdiff_le_add_card (P := P_prev) hM_sub
      omega
    | cons _ _ => exact absurd hv id
  | cons p rs ih =>
    cases offStates with
    | nil => exact absurd hv id
    | cons s_off' ss =>
      obtain ⟨hstep, hrest⟩ := hv
      have hs_off_card : s_off.card ≤ k := hstep.1
      set B' : Finset α := if p ∈ s_off then B else insert p B
      have hp_in_B' : p ∈ s_start ∪ B' := by
        by_cases hp_off : p ∈ s_off
        · simp only [hp_off, ↓reduceIte, B']
          exact hs_off_sub hp_off
        · simp only [hp_off, ↓reduceIte, B', Finset.union_insert, Finset.mem_insert_self]
      have hs_off'_sub : s_off' ⊆ s_start ∪ B' := by
        by_cases hp_off : p ∈ s_off
        · simp only [hp_off, ↓reduceIte, validStep_hit_eq hstep hp_off, B']
          exact hs_off_sub
        · simp only [hp_off, ↓reduceIte, B']
          refine (validStep_miss_subset hstep hp_off).trans ?_
          rw [Finset.union_insert]
          exact Finset.insert_subset_insert p hs_off_sub
      have hM_sub' : tr.marked ⊆ s_start ∪ B' := by
        refine hM_sub.trans (Finset.union_subset_union_right ?_)
        by_cases hp_off : p ∈ s_off <;> simp [hp_off, B', Finset.subset_insert]
      have hB'_card : B'.card ≤ B.card + stepCost s_off p s_off' := by
        by_cases hp_off : p ∈ s_off
        · simp only [hp_off, ↓reduceIte, stepCost_of_mem hp_off, add_zero, B', le_rfl]
        · simp only [hp_off, ↓reduceIte, stepCost_of_notMem hp_off, B']
          exact (Finset.card_insert_le p B).trans (by omega)
      simp only [cleanCount]
      change (tr.marked \ P_prev).card +
          ((if isCleanReq tr p then 1 else 0) + cleanCount k (stepTracker k tr p) rs) ≤
        (s_start \ P_prev).card + 2 * B.card +
          2 * (stepCost s_off p s_off' + (problem α k).scheduleCost s_off' rs ss)
      have htr' := validTracker_step hk htr p
      by_cases hpM : p ∈ tr.marked
      · have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM]
        have hstep_tr : stepTracker k tr p = tr := by simp [stepTracker, hpM]
        rw [hclean, hstep_tr]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        have hih := ih htr hP_card hstale hsum hs_start hs_off'_sub hM_sub' hrest
        omega
      · by_cases ht0 : tr.staleCached = 0
        · have hM_card : tr.marked.card = k := by omega
          have hnotlt : ¬ tr.marked.card < k := by omega
          have hclean : isCleanReq tr p = true := by simp [isCleanReq, hpM, ht0]
          have hstep_tr : stepTracker k tr p = ⟨{p}, tr.marked, k - 1⟩ := by
            simp [stepTracker, hpM, ht0, hnotlt]
          rw [hclean, hstep_tr]
          simp only [↓reduceIte]
          set B_new : Finset α := if p ∈ s_off then ∅ else {p}
          have hs_off'_new : s_off' ⊆ s_off ∪ B_new := by
            by_cases hp_off : p ∈ s_off
            · simp only [hp_off, ↓reduceIte, validStep_hit_eq hstep hp_off, Finset.union_empty,
                B_new, Finset.Subset.refl]
            · simp only [hp_off, ↓reduceIte, Finset.union_singleton, B_new]
              exact validStep_miss_subset hstep hp_off
          have hp_new : ({p} : Finset α) ⊆ s_off ∪ B_new := by
            by_cases hp_off : p ∈ s_off
            · simp only [hp_off, ↓reduceIte, Finset.union_empty, Finset.singleton_subset_iff,
                B_new]
            · simp only [hp_off, ↓reduceIte, Finset.union_singleton, Finset.singleton_subset_iff,
                Finset.mem_insert_self, B_new]
          have hB_new_card : B_new.card = stepCost s_off p s_off' := by
            by_cases hp_off : p ∈ s_off <;> simp [hp_off, B_new]
          have hstale_new : tr.marked = tr.marked \ {p} := by
            rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hpM]
          have hsum_new : ({p} : Finset α).card + (k - 1) = k := by
            rw [Finset.card_singleton]
            omega
          have htr_new : ValidTracker k ⟨{p}, tr.marked, k - 1⟩ := hstep_tr ▸ htr'
          have hih := ih (tr := ⟨{p}, tr.marked, k - 1⟩) (P_prev := tr.marked)
            (s_start := s_off) (B := B_new)
            htr_new hM_card hstale_new hsum_new hs_off_card hs_off'_new hp_new hrest
          have hp_sdiff : (({p} : Finset α) \ tr.marked).card = 1 := by
            rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr hpM),
              Finset.card_singleton]
          dsimp only at hih
          rw [hp_sdiff, hB_new_card] at hih
          have hc1 : (tr.marked \ P_prev).card ≤ (s_start \ P_prev).card + B.card :=
            card_sdiff_le_add_card hM_sub
          have hc2 : (s_off \ tr.marked).card ≤ B.card :=
            card_sdiff_le_card_of_full hs_off_sub hM_sub hM_card hs_start
          omega
        · by_cases hpS : p ∈ tr.stale
          · have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM, ht0, hpS]
            have hstep_tr : stepTracker k tr p =
                ⟨insert p tr.marked, tr.stale.erase p, tr.staleCached - 1⟩ := by
              simp [stepTracker, hpM, ht0, hpS]
            rw [hclean, hstep_tr]
            simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
            have hpP : p ∈ P_prev := (Finset.mem_sdiff.mp (hstale ▸ hpS)).1
            have hstale' : tr.stale.erase p = P_prev \ insert p tr.marked := by
              rw [hstale, Finset.sdiff_insert]
            have hsum' : (insert p tr.marked).card + (tr.staleCached - 1) = k := by
              rw [Finset.card_insert_of_notMem hpM]
              omega
            have hM'_sub : insert p tr.marked ⊆ s_start ∪ B' :=
              Finset.insert_subset hp_in_B' hM_sub'
            have hsdiff_eq : insert p tr.marked \ P_prev = tr.marked \ P_prev :=
              Finset.insert_sdiff_of_mem tr.marked hpP
            have hih := ih (tr := ⟨insert p tr.marked, tr.stale.erase p, tr.staleCached - 1⟩)
              (hstep_tr ▸ htr') hP_card hstale' hsum' hs_start hs_off'_sub hM'_sub hrest
            dsimp only at hih
            rw [hsdiff_eq] at hih
            omega
          · have hclean : isCleanReq tr p = true := by simp [isCleanReq, hpM, hpS]
            have hstep_tr :
                stepTracker k tr p = ⟨insert p tr.marked, tr.stale, tr.staleCached - 1⟩ := by
              simp [stepTracker, hpM, ht0, hpS]
            rw [hclean, hstep_tr]
            simp only [↓reduceIte]
            have hpP : p ∉ P_prev := by
              intro hp_in_P
              exact hpS (hstale ▸ Finset.mem_sdiff.mpr ⟨hp_in_P, hpM⟩)
            have hstale' : tr.stale = P_prev \ insert p tr.marked := by
              rw [hstale, Finset.sdiff_insert_of_notMem hpP]
            have hsum' : (insert p tr.marked).card + (tr.staleCached - 1) = k := by
              rw [Finset.card_insert_of_notMem hpM]
              omega
            have hM'_sub : insert p tr.marked ⊆ s_start ∪ B' :=
              Finset.insert_subset hp_in_B' hM_sub'
            have hsdiff_card :
                (insert p tr.marked \ P_prev).card = (tr.marked \ P_prev).card + 1 := by
              have hset : insert p tr.marked \ P_prev = insert p (tr.marked \ P_prev) :=
                Finset.insert_sdiff_of_notMem tr.marked hpP
              have hp_not : p ∉ tr.marked \ P_prev := fun h => hpM (Finset.mem_sdiff.mp h).1
              rw [hset, Finset.card_insert_of_notMem hp_not]
            have hih := ih (tr := ⟨insert p tr.marked, tr.stale, tr.staleCached - 1⟩)
              (hstep_tr ▸ htr') hP_card hstale' hsum' hs_start hs_off'_sub hM'_sub hrest
            dsimp only at hih
            rw [hsdiff_card] at hih
            omega

/-- Warmup induction before the first phase reset (`stale = ∅`, `staleCached = 0`, `s_off ⊆ M`). -/
private theorem cleanCount_warmup_bound {k : ℕ} (hk : 0 < k) {M s_off : Finset α}
    {reqs : List α} {offStates : List (Finset α)}
    (hM_card : M.card ≤ k) (hsub : s_off ⊆ M)
    (hv : (problem α k).ValidSchedule s_off reqs offStates) :
    cleanCount k ⟨M, ∅, 0⟩ reqs ≤ 2 * (problem α k).scheduleCost s_off reqs offStates := by
  induction reqs generalizing offStates s_off M with
  | nil =>
    cases offStates with
    | nil => exact Nat.zero_le _
    | cons _ _ => exact absurd hv id
  | cons p rs ih =>
    cases offStates with
    | nil => exact absurd hv id
    | cons s_off' ss =>
      obtain ⟨hstep, hrest⟩ := hv
      simp only [cleanCount]
      change (if isCleanReq ⟨M, ∅, 0⟩ p then 1 else 0) +
          cleanCount k (stepTracker k ⟨M, ∅, 0⟩ p) rs ≤
        2 * (stepCost s_off p s_off' + (problem α k).scheduleCost s_off' rs ss)
      by_cases hpM : p ∈ M
      · have hclean : isCleanReq ⟨M, ∅, 0⟩ p = false := by simp [isCleanReq, hpM]
        have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨M, ∅, 0⟩ := by simp [stepTracker, hpM]
        have hs_off'_sub : s_off' ⊆ M := by
          by_cases hp_off : p ∈ s_off
          · rw [validStep_hit_eq hstep hp_off]
            exact hsub
          · exact (validStep_miss_subset hstep hp_off).trans (Finset.insert_subset hpM hsub)
        rw [hclean, hstep_tr]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        have hih := ih hM_card hs_off'_sub hrest
        omega
      · have hp_off : p ∉ s_off := fun hp => hpM (hsub hp)
        have hcost1 : stepCost s_off p s_off' = 1 := stepCost_of_notMem hp_off
        have hclean : isCleanReq ⟨M, ∅, 0⟩ p = true := by simp [isCleanReq, hpM]
        rw [hclean, hcost1]
        simp only [↓reduceIte]
        by_cases hlt : M.card < k
        · have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨insert p M, ∅, 0⟩ := by
            simp [stepTracker, hpM, hlt]
          rw [hstep_tr]
          have hM'_card : (insert p M).card ≤ k := by
            rw [Finset.card_insert_of_notMem hpM]
            omega
          have hs_off'_sub : s_off' ⊆ insert p M :=
            (validStep_miss_subset hstep hp_off).trans (Finset.insert_subset_insert p hsub)
          have hih := ih hM'_card hs_off'_sub hrest
          omega
        · have hM_eq : M.card = k := by omega
          have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨{p}, M, k - 1⟩ := by
            simp [stepTracker, hpM, hlt]
          rw [hstep_tr]
          have htr_init : ValidTracker k ⟨M, ∅, 0⟩ :=
            ⟨Finset.disjoint_empty_right M, le_rfl, Nat.zero_le k, by omega,
              fun h => absurd h (Nat.lt_irrefl 0)⟩
          have htr_new : ValidTracker k ⟨{p}, M, k - 1⟩ :=
            hstep_tr ▸ validTracker_step hk htr_init p
          have hstale_new : M = M \ {p} := by
            rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hpM]
          have hsum_new : ({p} : Finset α).card + (k - 1) = k := by
            rw [Finset.card_singleton]
            omega
          have hs_off'_sub : s_off' ⊆ s_off ∪ {p} := by
            rw [Finset.union_singleton]
            exact validStep_miss_subset hstep hp_off
          have hp_sub : ({p} : Finset α) ⊆ s_off ∪ {p} := Finset.subset_union_right
          have hact := cleanCount_active_bound hk (tr := ⟨{p}, M, k - 1⟩) (P_prev := M)
            (s_start := s_off) (B := {p})
            htr_new hM_eq hstale_new hsum_new hstep.1 hs_off'_sub hp_sub hrest
          have hp_sdiff : (({p} : Finset α) \ M).card = 1 := by
            rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr hpM),
              Finset.card_singleton]
          have hs_sdiff : (s_off \ M).card = 0 :=
            Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hsub)
          simp only [hp_sdiff, hs_sdiff, Finset.card_singleton] at hact
          omega

/-- **FKLMSY two-window offline lower bound (`#clean ≤ 2 · OPT`).** Against any valid offline
schedule from `s₀`, the number of clean requests encountered from `initTracker s₀` is at most
twice the offline fault cost. -/
theorem cleanCount_le_two_mul_scheduleCost {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) {reqs : List α} {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    cleanCount k (initTracker s₀) reqs ≤ 2 * (problem α k).scheduleCost s₀ reqs offStates :=
  cleanCount_warmup_bound hk hs₀ (Finset.Subset.refl s₀) hv

/-! ### Main competitiveness theorems (FKLMSY Theorem 1) -/

/-- Rational expected cost of `markingStrategy` is at most `2 * harmonic k * scheduleCost`. -/
theorem trackerExpectedCost_le_two_mul_harmonic_mul_scheduleCost {k : ℕ} (hk : 0 < k)
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) {reqs : List α} {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    trackerExpectedCost k (initTracker s₀) reqs ≤
      2 * harmonic k * ((problem α k).scheduleCost s₀ reqs offStates : ℚ) := by
  have h1 := trackerExpectedCost_le_harmonic_mul_cleanCount hk hs₀ reqs
  have h2 : (cleanCount k (initTracker s₀) reqs : ℚ) ≤
      2 * ((problem α k).scheduleCost s₀ reqs offStates : ℚ) := by
    exact_mod_cast cleanCount_le_two_mul_scheduleCost hk hs₀ hv
  have h3 : harmonic k * (cleanCount k (initTracker s₀) reqs : ℚ) ≤
      harmonic k * (2 * ((problem α k).scheduleCost s₀ reqs offStates : ℚ)) :=
    mul_le_mul_of_nonneg_left h2 (harmonic_nonneg k)
  linarith

/-- **FKLMSY Theorem 1 (`ℝ≥0∞` cost bound)** [FiatKarpLubyMcGeochSleatorYoung1991]: for every
admissible initial cache `s₀` (`|s₀| ≤ k`), request sequence `reqs`, and valid offline schedule
`offStates` from `s₀`, the expected cost of `markingStrategy` is at most `2 H_k` times the offline
schedule's cost. -/
theorem markingStrategy_expectedCost_le {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) {reqs : List α} {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    (markingStrategy k hk).expectedCost s₀ reqs ≤
      2 * ENNReal.ofReal (harmonic k) * (problem α k).scheduleCost s₀ reqs offStates := by
  rw [expectedCost_markingStrategy_eq hk hs₀]
  have hrat := trackerExpectedCost_le_two_mul_harmonic_mul_scheduleCost hk hs₀ hv
  have hreal :
      (trackerExpectedCost k (initTracker s₀) reqs : ℝ) ≤
        2 * (harmonic k : ℝ) * ((problem α k).scheduleCost s₀ reqs offStates : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr hrat
  have hhk : (0 : ℝ) ≤ (harmonic k : ℝ) := by exact_mod_cast harmonic_nonneg k
  calc ENNReal.ofReal (trackerExpectedCost k (initTracker s₀) reqs)
      ≤ ENNReal.ofReal
          (2 * (harmonic k : ℝ) * ((problem α k).scheduleCost s₀ reqs offStates : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * (harmonic k : ℝ)) *
          ENNReal.ofReal ((problem α k).scheduleCost s₀ reqs offStates : ℝ) :=
        ENNReal.ofReal_mul (by positivity)
    _ = 2 * ENNReal.ofReal (harmonic k) * (problem α k).scheduleCost s₀ reqs offStates := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]

/-- **FKLMSY Theorem 1 (`BehavioralStrategy.IsCompetitive`)**
[FiatKarpLubyMcGeochSleatorYoung1991]: the randomized marking strategy is `(2 * H_k, 0)`-competitive
for demand paging against an oblivious adversary. -/
theorem markingStrategy_isCompetitive {k : ℕ} (hk : 0 < k) :
    (markingStrategy (α := α) k hk).IsCompetitive (2 * ENNReal.ofReal (harmonic k)) 0 := by
  intro s₀ hs₀ reqs offStates hv
  rw [add_zero]
  exact markingStrategy_expectedCost_le hk hs₀ hv

/-- Real-valued expectation form of FKLMSY Theorem 1. -/
theorem markingStrategy_expectedCost_toReal_le {k : ℕ} (hk : 0 < k) {s₀ : Finset α}
    (hs₀ : ValidCache k s₀) {reqs : List α} {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    ((markingStrategy k hk).expectedCost s₀ reqs).toReal ≤
      2 * (harmonic k : ℝ) * (problem α k).scheduleCost s₀ reqs offStates := by
  rw [expectedCost_markingStrategy_eq hk hs₀,
    ENNReal.toReal_ofReal (by exact_mod_cast trackerExpectedCost_nonneg k (initTracker s₀) reqs)]
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    (Rat.cast_le (K := ℝ)).mpr
      (trackerExpectedCost_le_two_mul_harmonic_mul_scheduleCost hk hs₀ hv)

end Decidable

end Cslib.DataStructure.Paging
