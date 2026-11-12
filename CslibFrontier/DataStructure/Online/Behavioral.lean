/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Online.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import CslibFrontier.Probability.PMF.Expect

/-!
# Behavioural randomized online strategies against an oblivious adversary

This file adds behavioural randomized online strategies to the online model of
`CslibFrontier.DataStructure.Online.Basic`, complementing the mixed-strategy `RandStrategy` model of
`CslibFrontier.DataStructure.Online.Randomized`.

Whereas a `RandStrategy P` draws a deterministic strategy from a single `PMF (DetStrategy P)` before
seeing any requests (and therefore covers only countably supported mixtures of deterministic
strategies), a `BehavioralStrategy P` maintains internal controller memory `Mem`, initializes it
deterministically via `init : P.State → Mem`, and updates it at each arrived request via a
`PMF`-valued transition `step : Mem → P.Req → PMF Mem` whose supported outcomes project to valid
transitions of `P`. Algorithms such as the randomized marking algorithm for paging toss fresh
uniform coins at unboundedly many steps and naturally inhabit `BehavioralStrategy P`.

Against an **oblivious adversary** — which fixes the entire request sequence `reqs` before any coin
is tossed — the expected cost from memory `m` on `reqs` is defined by backward recursion in `ℝ≥0∞`
(`BehavioralStrategy.expectedCostFrom`), and `BehavioralStrategy.expectedCost` starts from
`init s₀`. Memory-distribution helpers (`runMemDist`, `expectedCostDist`) push an arbitrary law
`μ : PMF B.Mem` forward one request at a time so that distribution-invariant analyses (such as
marking's uniform stale-subset law) reduce directly to step expectations.

Deterministic strategies embed as point-mass transitions (`BehavioralStrategy.ofDetStrategy`),
recovering deterministic `costFrom`, `cost` and competitiveness (`expectedCostFrom_ofDetStrategy`,
`expectedCost_ofDetStrategy`, `isCompetitive_ofDetStrategy_iff`).

Adaptive adversaries and Kuhn-type equivalence with `RandStrategy` are not formalized here.

## Main definitions

* `Cslib.DataStructure.Online.BehavioralStrategy`: behavioural randomized online strategies with
  `PMF`-valued per-request memory transitions.
* `BehavioralStrategy.stepExpectedCost`, `BehavioralStrategy.expectedCostFrom`,
  `BehavioralStrategy.expectedCost`: single-step and backward-recursive multi-step expected online
  costs in `ℝ≥0∞`.
* `BehavioralStrategy.runMemDist`, `BehavioralStrategy.expectedCostDist`: evolution and expected
  continuation cost from a probability distribution over controller memories.
* `BehavioralStrategy.IsCompetitiveFrom`, `BehavioralStrategy.IsCompetitive`,
  `BehavioralStrategy.IsCompetitiveAnyInit`: expected competitiveness against an oblivious
  adversary.
* `BehavioralStrategy.ofDetStrategy`: embedding of deterministic online strategies via `PMF.pure`.

## Main results

* `BehavioralStrategy.expectedCostFrom_cons_eq_add`, `BehavioralStrategy.expectedCostDist_cons`,
  `BehavioralStrategy.expectedCostDist_append`: linear decomposition of expected cost across single
  steps and concatenated request sequences.
* `BehavioralStrategy.expectedCostFrom_le_mul_length`: finiteness / linear upper bound when
  per-step costs are bounded.
* `BehavioralStrategy.expectedCostFrom_ofDetStrategy`,
  `BehavioralStrategy.expectedCost_ofDetStrategy`,
  `BehavioralStrategy.isCompetitive_ofDetStrategy_iff`,
  `BehavioralStrategy.isCompetitiveAnyInit_ofDetStrategy_iff`: deterministic agreement.

## References

* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
* [A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator, and N. E. Young, *Competitive Paging
  Algorithms*][FiatKarpLubyMcGeochSleatorYoung1991]
-/

open scoped ENNReal

public section

namespace Cslib.DataStructure.Online

/-- A behavioural randomized online strategy for `P`. Its transition `step` sees only its internal
memory `Mem` and the newly arrived request `P.Req`, returning a discrete probability distribution
`PMF Mem` whose every supported outcome preserves `ValidMem` and projects to a valid transition of
`P`. -/
structure BehavioralStrategy (P : Problem) where
  /-- Internal controller memory maintained across requests. -/
  Mem : Type
  /-- Representation invariant preserved by `init` and every supported transition of `step`. -/
  ValidMem : Mem → Prop
  /-- Observable configuration in `P.State` corresponding to internal memory. -/
  project : Mem → P.State
  /-- Deterministic online initialization from an initial configuration of `P`. -/
  init : P.State → Mem
  /-- Randomized online transition consuming the current memory and arrived request. -/
  step : Mem → P.Req → PMF Mem
  /-- `init` establishes `ValidMem` and projects back to `s₀` on admissible initial states. -/
  valid_init : ∀ {s₀}, P.ValidInit s₀ → ValidMem (init s₀) ∧ project (init s₀) = s₀
  /-- Every supported outcome of `step` preserves `ValidMem` and projects to a `ValidStep` of
  `P`. -/
  valid_step : ∀ {m} (r : P.Req), ValidMem m →
    ∀ m' ∈ (step m r).support, ValidMem m' ∧ P.ValidStep (project m) r (project m')

namespace BehavioralStrategy

variable {P : Problem} (B : BehavioralStrategy P)

/-! ### Expected cost against an oblivious adversary -/

/-- Expected single-step cost of `B` when serving request `r` from internal memory `m`. -/
@[expose]
noncomputable def stepExpectedCost (m : B.Mem) (r : P.Req) : ℝ≥0∞ :=
  ∑' m', B.step m r m' * (P.stepCost (B.project m) r (B.project m') : ℝ≥0∞)

/-- Expected total cost of `B` starting from internal memory `m` on the fixed request sequence
`reqs`, defined by backward recursion in `ℝ≥0∞`. -/
@[expose]
noncomputable def expectedCostFrom : B.Mem → List P.Req → ℝ≥0∞
  | _, [] => 0
  | m, r :: rs =>
    ∑' m', B.step m r m' *
      ((P.stepCost (B.project m) r (B.project m') : ℝ≥0∞) + expectedCostFrom m' rs)

/-- Expected total cost of `B` from initial configuration `s₀` on the fixed request sequence `reqs`
chosen by an oblivious adversary. -/
@[expose]
noncomputable def expectedCost (s₀ : P.State) (reqs : List P.Req) : ℝ≥0∞ :=
  B.expectedCostFrom (B.init s₀) reqs

@[simp]
theorem expectedCostFrom_nil (m : B.Mem) : B.expectedCostFrom m [] = 0 := rfl

@[simp]
theorem expectedCostFrom_cons (m : B.Mem) (r : P.Req) (rs : List P.Req) :
    B.expectedCostFrom m (r :: rs) =
      ∑' m', B.step m r m' *
        ((P.stepCost (B.project m) r (B.project m') : ℝ≥0∞) + B.expectedCostFrom m' rs) := rfl

@[simp]
theorem expectedCost_nil (s₀ : P.State) : B.expectedCost s₀ [] = 0 := rfl

/-- Linear split of `expectedCostFrom` into the immediate expected step cost plus the expected
continuation cost. -/
theorem expectedCostFrom_cons_eq_add (m : B.Mem) (r : P.Req) (rs : List P.Req) :
    B.expectedCostFrom m (r :: rs) =
      B.stepExpectedCost m r + ∑' m', B.step m r m' * B.expectedCostFrom m' rs := by
  simp only [expectedCostFrom_cons, stepExpectedCost, mul_add, tsum_add]

/-- If every supported transition of `B` incurs step cost at most `w`, then `stepExpectedCost` is at
most `w` on every valid memory. -/
theorem stepExpectedCost_le {w : ℕ}
    (hw : ∀ {m}, B.ValidMem m → ∀ r, ∀ m' ∈ (B.step m r).support,
      P.stepCost (B.project m) r (B.project m') ≤ w)
    {m : B.Mem} (hm : B.ValidMem m) (r : P.Req) :
    B.stepExpectedCost m r ≤ w := by
  calc B.stepExpectedCost m r
      ≤ ∑' m', B.step m r m' * (w : ℝ≥0∞) := by
        refine tsum_le_tsum fun m' => ?_
        by_cases hmem : m' ∈ (B.step m r).support
        · gcongr
          exact Nat.cast_le.mpr (hw hm r m' hmem)
        · rw [(PMF.apply_eq_zero_iff (B.step m r) m').mpr hmem, zero_mul, zero_mul]
    _ = w := by rw [ENNReal.tsum_mul_right, (B.step m r).tsum_coe, one_mul]

/-- If every supported transition of `B` incurs step cost at most `w`, then `expectedCostFrom` on
`reqs` is at most `w * reqs.length` on every valid memory. -/
theorem expectedCostFrom_le_mul_length {w : ℕ}
    (hw : ∀ {m}, B.ValidMem m → ∀ r, ∀ m' ∈ (B.step m r).support,
      P.stepCost (B.project m) r (B.project m') ≤ w)
    {m : B.Mem} (hm : B.ValidMem m) (reqs : List P.Req) :
    B.expectedCostFrom m reqs ≤ (w : ℝ≥0∞) * reqs.length := by
  induction reqs generalizing m with
  | nil => simp only [expectedCostFrom_nil, List.length_nil, Nat.cast_zero, mul_zero, le_rfl]
  | cons r rs ih =>
    rw [expectedCostFrom_cons_eq_add, List.length_cons, Nat.cast_add, Nat.cast_one, mul_add,
      mul_one, add_comm ((w : ℝ≥0∞) * rs.length) w]
    refine add_le_add (B.stepExpectedCost_le hw hm r) ?_
    calc ∑' m', B.step m r m' * B.expectedCostFrom m' rs
        ≤ ∑' m', B.step m r m' * ((w : ℝ≥0∞) * rs.length) := by
          refine tsum_le_tsum fun m' => ?_
          by_cases hmem : m' ∈ (B.step m r).support
          · have hih := ih (B.valid_step r hm m' hmem).1
            gcongr
          · rw [(PMF.apply_eq_zero_iff (B.step m r) m').mpr hmem, zero_mul, zero_mul]
      _ = (w : ℝ≥0∞) * rs.length := by
          rw [ENNReal.tsum_mul_right, (B.step m r).tsum_coe, one_mul]

/-! ### Memory-distribution evolution -/

/-- Evolve a probability distribution `μ` over controller memories across a request sequence. -/
@[expose]
noncomputable def runMemDist (μ : PMF B.Mem) : List P.Req → PMF B.Mem
  | [] => μ
  | r :: rs => runMemDist (μ.bind fun m => B.step m r) rs

/-- Expected continuation cost of `B` on `reqs` when the starting controller memory is drawn from
`μ`. -/
@[expose]
noncomputable def expectedCostDist (μ : PMF B.Mem) (reqs : List P.Req) : ℝ≥0∞ :=
  ∑' m, μ m * B.expectedCostFrom m reqs

@[simp]
theorem runMemDist_nil (μ : PMF B.Mem) : B.runMemDist μ [] = μ := rfl

@[simp]
theorem runMemDist_cons (μ : PMF B.Mem) (r : P.Req) (rs : List P.Req) :
    B.runMemDist μ (r :: rs) = B.runMemDist (μ.bind fun m => B.step m r) rs := rfl

@[simp]
theorem runMemDist_append (μ : PMF B.Mem) (reqs₁ reqs₂ : List P.Req) :
    B.runMemDist μ (reqs₁ ++ reqs₂) = B.runMemDist (B.runMemDist μ reqs₁) reqs₂ := by
  induction reqs₁ generalizing μ with
  | nil => rfl
  | cons r rs ih => exact ih (μ.bind fun m => B.step m r)

/-- `runMemDist` preserves support validity across any request sequence. -/
theorem validMem_runMemDist {μ : PMF B.Mem} (hμ : ∀ m ∈ μ.support, B.ValidMem m)
    (reqs : List P.Req) :
    ∀ m' ∈ (B.runMemDist μ reqs).support, B.ValidMem m' := by
  induction reqs generalizing μ with
  | nil => exact hμ
  | cons r rs ih =>
    apply ih
    intro m' hm'
    rw [PMF.mem_support_bind_iff] at hm'
    obtain ⟨m, hm, hm'⟩ := hm'
    exact (B.valid_step r (hμ m hm) m' hm').1

@[simp]
theorem expectedCostDist_nil (μ : PMF B.Mem) : B.expectedCostDist μ [] = 0 := by
  simp only [expectedCostDist, expectedCostFrom_nil, mul_zero, tsum_zero]

@[simp]
theorem expectedCostDist_pure (m : B.Mem) (reqs : List P.Req) :
    B.expectedCostDist (PMF.pure m) reqs = B.expectedCostFrom m reqs := by
  rw [expectedCostDist, tsum_eq_single m]
  · rw [PMF.pure_apply_self, one_mul]
  · intro m' hm'
    rw [PMF.pure_apply_of_ne _ _ hm', zero_mul]

/-- One-step Bellman decomposition of `expectedCostDist` over a memory distribution `μ`. -/
theorem expectedCostDist_cons (μ : PMF B.Mem) (r : P.Req) (rs : List P.Req) :
    B.expectedCostDist μ (r :: rs) =
      (∑' m, μ m * B.stepExpectedCost m r) +
        B.expectedCostDist (μ.bind fun m => B.step m r) rs := by
  simp only [expectedCostDist, expectedCostFrom_cons_eq_add, mul_add, tsum_add]
  rw [Cslib.Probability.PMF.tsum_bind_mul]

/-- Additivity of `expectedCostDist` across concatenated request sequences. -/
theorem expectedCostDist_append (μ : PMF B.Mem) (reqs₁ reqs₂ : List P.Req) :
    B.expectedCostDist μ (reqs₁ ++ reqs₂) =
      B.expectedCostDist μ reqs₁ + B.expectedCostDist (B.runMemDist μ reqs₁) reqs₂ := by
  induction reqs₁ generalizing μ with
  | nil => simp only [List.nil_append, expectedCostDist_nil, runMemDist_nil, zero_add]
  | cons r rs ih =>
    simp only [List.cons_append, expectedCostDist_cons, runMemDist_cons, ih, add_assoc]

/-! ### Competitive ratio predicates -/

/-- `B` is `(c, b)`-competitive from `s₀` against an oblivious adversary when its expected cost on
every request sequence is at most `c` times any valid offline schedule's cost from `s₀`, plus
`b`. -/
@[expose]
def IsCompetitiveFrom (s₀ : P.State) (c b : ℝ≥0∞) : Prop :=
  ∀ reqs offStates, P.ValidSchedule s₀ reqs offStates →
    B.expectedCost s₀ reqs ≤ c * P.scheduleCost s₀ reqs offStates + b

/-- `B` is `(c, b)`-competitive against an oblivious adversary when it is `(c, b)`-competitive from
every admissible initial state `s₀` shared with the offline schedule. -/
@[expose]
def IsCompetitive (c b : ℝ≥0∞) : Prop :=
  ∀ s₀, P.ValidInit s₀ → B.IsCompetitiveFrom s₀ c b

/-- `B` is `(c, b)`-competitive across arbitrary initial states when its expected cost from any
admissible `s₀` is at most `c` times any valid offline schedule's cost from any admissible `s_off`,
plus `b`. -/
@[expose]
def IsCompetitiveAnyInit (c b : ℝ≥0∞) : Prop :=
  ∀ s₀ s_off reqs offStates, P.ValidInit s₀ → P.ValidInit s_off →
    P.ValidSchedule s_off reqs offStates →
    B.expectedCost s₀ reqs ≤ c * P.scheduleCost s_off reqs offStates + b

/-- Competitiveness across arbitrary initial states implies same-initial-state competitiveness. -/
theorem IsCompetitiveAnyInit.toIsCompetitive {B : BehavioralStrategy P} {c b : ℝ≥0∞}
    (h : B.IsCompetitiveAnyInit c b) : B.IsCompetitive c b :=
  fun s₀ hs₀ reqs offStates hv => h s₀ s₀ reqs offStates hs₀ hs₀ hv

/-- Monotonicity of `IsCompetitive` in the competitive ratio `c` and additive constant `b`. -/
theorem IsCompetitive.mono {B : BehavioralStrategy P} {c₁ c₂ b₁ b₂ : ℝ≥0∞}
    (hc : c₁ ≤ c₂) (hb : b₁ ≤ b₂) (h : B.IsCompetitive c₁ b₁) :
    B.IsCompetitive c₂ b₂ :=
  fun s₀ hs₀ reqs offStates hv => (h s₀ hs₀ reqs offStates hv).trans (by gcongr)

/-! ### Embedding deterministic strategies -/

/-- View a deterministic online strategy `A : DetStrategy P` as a behavioural strategy whose
per-request transitions are point masses `PMF.pure (A.step m r)`. -/
noncomputable abbrev ofDetStrategy (A : DetStrategy P) : BehavioralStrategy P where
  Mem := A.Mem
  ValidMem := A.ValidMem
  project := A.project
  init := A.init
  step m r := PMF.pure (A.step m r)
  valid_init hs₀ := A.valid_init hs₀
  valid_step r hm m' hm' := by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hm'
    subst hm'
    exact A.valid_step r hm

/-- Expected cost from `m` of `ofDetStrategy A` equals `A.costFrom m reqs`. -/
@[simp]
theorem expectedCostFrom_ofDetStrategy (A : DetStrategy P) (m : A.Mem) (reqs : List P.Req) :
    (ofDetStrategy A).expectedCostFrom m reqs = A.costFrom m reqs := by
  induction reqs generalizing m with
  | nil => simp only [expectedCostFrom_nil, DetStrategy.costFrom_nil, Nat.cast_zero]
  | cons r rs ih =>
    rw [expectedCostFrom_cons, tsum_eq_single (A.step m r)]
    · simp only [ofDetStrategy, PMF.pure_apply_self, one_mul, ih, DetStrategy.costFrom_cons,
        Nat.cast_add]
    · intro m' hm'
      simp only [ofDetStrategy, PMF.pure_apply_of_ne _ _ hm', zero_mul]

/-- From any admissible initial configuration `s₀`, the expected cost of `ofDetStrategy A` equals
`A.cost s₀ reqs`. -/
theorem expectedCost_ofDetStrategy (A : DetStrategy P) {s₀ : P.State} (hs₀ : P.ValidInit s₀)
    (reqs : List P.Req) :
    (ofDetStrategy A).expectedCost s₀ reqs = A.cost s₀ reqs := by
  rw [expectedCost, expectedCostFrom_ofDetStrategy, A.cost_eq_costFrom hs₀]

/-- For natural-number coefficients, `ofDetStrategy A` is `(c, b)`-competitive iff `A` is. -/
theorem isCompetitive_ofDetStrategy_iff (A : DetStrategy P) (c b : ℕ) :
    (ofDetStrategy A).IsCompetitive c b ↔ A.IsCompetitive c b := by
  have key : ∀ x y : ℕ, ((x : ℝ≥0∞) ≤ c * y + b) ↔ x ≤ c * y + b := fun x y => by norm_cast
  constructor
  · intro h s₀ hs₀ reqs offStates hv
    have h' := h s₀ hs₀ reqs offStates hv
    rwa [expectedCost_ofDetStrategy A hs₀, key] at h'
  · intro h s₀ hs₀ reqs offStates hv
    rw [expectedCost_ofDetStrategy A hs₀, key]
    exact h s₀ hs₀ reqs offStates hv

/-- For natural-number coefficients, `ofDetStrategy A` is `(c, b)`-competitive across arbitrary
initial states iff `A` is. -/
theorem isCompetitiveAnyInit_ofDetStrategy_iff (A : DetStrategy P) (c b : ℕ) :
    (ofDetStrategy A).IsCompetitiveAnyInit c b ↔ A.IsCompetitiveAnyInit c b := by
  have key : ∀ x y : ℕ, ((x : ℝ≥0∞) ≤ c * y + b) ↔ x ≤ c * y + b := fun x y => by norm_cast
  constructor
  · intro h s₀ s_off reqs offStates hs₀ hs_off hv
    have h' := h s₀ s_off reqs offStates hs₀ hs_off hv
    rwa [expectedCost_ofDetStrategy A hs₀, key] at h'
  · intro h s₀ s_off reqs offStates hs₀ hs_off hv
    rw [expectedCost_ofDetStrategy A hs₀, key]
    exact h s₀ s_off reqs offStates hs₀ hs_off hv

end BehavioralStrategy

end Cslib.DataStructure.Online
