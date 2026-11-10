/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutput
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Deadline
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Common-oracle native token optimum

[Wang2027], Theorem 5, PDF p. 12, Appendix A.5 p. 16. Competitors share one
actual source sampler and initial hidden seed. Their code, randomness and tape
memory are unrestricted within the finite-control discrete native interface.
Admission requires provenance only for families counted as certified successes;
fabricated failed outputs are permitted, as in the source selection-only convention.
The cost includes every accrued receipt, including prefixes of divergent paths;
no integrability or bounded total bill is assumed. Source envelopes concern only
positive-probability selected epochs. External WSC encodings and general measurable
interfaces remain separate from this implemented model. Competitors use the
configured finite opportunity/cutoff interface and the original runtime input
codec; the upper implementation is the concrete fixed-block scheduler. This is
not a claim of unrestricted source Theorem 5/6 coverage.

## Main results

* `lower`: the success-level lower envelope for the infimum over every admitted competitor.
* `upper`: the constructed controller supplies feasible survival-sum, mean and budget bounds.
* `competitive`: matching envelopes give the source factor `1/η` against that infimum.
* `success_le`, `feasible_success_le`: the effective-turn binomial deadline obstruction.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchOptimum
open Turing NativeOpenExecution ConcurrentBatch NativeBatch Trace Quantitative
open AdaptiveSelection PartialCover
open BatchOutput (accept)
open scoped NNReal ENNReal
open MeasureTheory
variable {n : ℕ} {Private : Type}

/-- The original rational instance restricted to its actual finite row labels. -/
@[expose] def finiteInstance (x : Input) (hx : Valid x) : Instance ℕ (Fin x.rows.length) where
  ground := (instanceOf x hx).ground
  sets i := (instanceOf x hx).sets i.val
  sets_subset i := (instanceOf x hx).sets_subset i.val
  weight i := (instanceOf x hx).weight i.val
  weight_nonneg i := (instanceOf x hx).weight_nonneg i.val
  dual := (instanceOf x hx).dual
  dual_nonneg := (instanceOf x hx).dual_nonneg
  dual_feasible i := (instanceOf x hx).dual_feasible i.val

/-- Restriction preserves the original coverage of every decoded finite family. -/
theorem finite_covered (x : Input) (hx : Valid x) (C : Finset (Fin x.rows.length)) :
    (finiteInstance x hx).covered C = (instanceOf x hx).covered (C.image Fin.val) := by
  exact (Finset.image_biUnion (f := Fin.val) (s := C) (t := (instanceOf x hx).sets)).symm

/-- Every accepted family is a cover of the original finite-index instance. -/
theorem accept_covers (x : Input) (hx : Valid x) (C : Finset (Fin x.rows.length))
    (h : accept x hx C = true) :
    (finiteInstance x hx).covered C = (finiteInstance x hx).ground := by
  have hc := (of_decide_eq_true h).1
  rw [finite_covered]
  exact hc

/-- Actual attained expected bills of admitted native competitors meeting the
certified-output success requirement, all on one source oracle and original input. -/
@[expose] def costs (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (η : ℝ≥0∞) : Set ℝ≥0∞ :=
  {v | ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Unit),
    let world := (⟨machine.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial seed, []⟩⟩ :
        World k Control Unit (ServerState n Private) (GuardedStartup.encoding data))
    NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) data.startup.system.rows.length)
      (decodeFamily data.startup.system.rows.length) (accept data.startup.system hx) world ∧
    η ≤ ((NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (BatchOutput.certified limits data.startup.system hx)) true ∧
    v = expected limits sample machine charge (limits.turns + 1) world}

/-- Token complexity is the infimum over actual admitted native competitors;
empty feasibility has value infinity. No optimum attainment is assumed. -/
@[expose] def optimum (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (η : ℝ≥0∞) : ℝ≥0∞ := sInf (costs limits sample data seed hx η)

/-- Uniform lower source envelopes over every admitted finite native machine.
These are revealed-coverage and conditional invoice hypotheses, not cost or
success conclusions. The oracle is fixed across all competitors. -/
structure LowerEnvelopes (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (b : ℕ) (p c : ℝ≥0∞) : Prop where
  /-- Every selected positive-probability epoch satisfies all three source bounds. -/
  bounds : ∀ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Unit),
    let world := (⟨machine.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial seed, []⟩⟩ :
        World k Control Unit (ServerState n Private) (GuardedStartup.encoding data))
    NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) data.startup.system.rows.length)
      (decodeFamily data.startup.system.rows.length) (accept data.startup.system hx) world →
    ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
      (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      (∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed (finiteInstance data.startup.system hx)
          (Coverage.proposal data.startup.system.rows.length) next.records \
          revealed (finiteInstance data.startup.system hx)
            (Coverage.proposal data.startup.system.rows.length) o.history).card ≤ b) ∧
      (o.issued = true → History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if reveals (finiteInstance data.startup.system hx)
          (Coverage.proposal data.startup.system.rows.length) h x then 1 else 0) ≤ p) ∧
      (o.issued = true → c ≤ Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge)

/-- Certified tape output implies native certificate acceptance on every outcome
law. This forgets only the deadline check and preserves actual tape readback. -/
theorem certified_le_accepted {k : ℕ} {Control : Type} {input : List Bool}
    (limits : Limits n) (x : Input) (hx : Valid x)
    (μ : PMF (Option (World k Control Unit (ServerState n Private) input))) :
    (μ.map (BatchOutput.certified limits x hx)) true ≤
      (μ.map (Coverage.nativeSuccess (accept x hx))) true := by
  apply PMF.map_true_mono
  intro result _ hcert
  cases result with
  | none => simp [BatchOutput.certified] at hcert
  | some next =>
    simp only [BatchOutput.certified, Option.any_some] at hcert
    obtain ⟨C, hc, hgood⟩ := (Option.any_eq_true _ _).mp hcert
    simp only [Coverage.nativeSuccess, Option.any_some, hc, Option.any_some]
    exact (Bool.and_eq_true_iff.mp hgood).1

/-- Source success-level lower bound on the true common-oracle native optimum.
Every competitor is quantified by `LowerEnvelopes`; neither a supplied lower
optimum certificate nor a desired expected-cost conclusion is a premise. -/
theorem lower (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (η : ℝ≥0∞) (b r : ℕ) (p c : ℝ≥0∞)
    (hr : ∀ q < r, b * q < (instanceOf data.startup.system hx).ground.card)
    (hp : p ≠ 0) (hpt : p ≠ ∞)
    (H : LowerEnvelopes limits sample data seed hx b p c) :
    (η * r * c) / p ≤ optimum limits sample data seed hx η := by
  apply le_sInf
  intro v hv
  obtain ⟨k, Control, hfinite, machine, hselect, hsuccess, rfl⟩ := hv
  let world : World k Control Unit (ServerState n Private) (GuardedStartup.encoding data) :=
    ⟨machine.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  let accepts := accept data.startup.system hx
  have hs := hsuccess.trans (certified_le_accepted limits data.startup.system hx
    (NativeUnboundedExecution.terminal machine (environment limits sample) world))
  have hl := Coverage.success_cost_lower limits sample machine
    (finiteInstance data.startup.system hx) b r p c hr world
    (NativeBatch.initial_invariant limits seed) rfl accepts
    (accept_covers data.startup.system hx)
    hselect
    (fun t ht o ho => by
      obtain ⟨hcap, _, _⟩ := H.bounds k Control hfinite machine hselect t ht o ho
      exact hcap)
    (fun t ht o ho => by
      obtain ⟨_, hprob, _⟩ := H.bounds k Control hfinite machine hselect t ht o ho
      exact hprob)
    hp hpt (fun t ht o ho => by
      obtain ⟨_, _, hcost⟩ := H.bounds k Control hfinite machine hselect t ht o ho
      exact hcost)
  exact (ENNReal.div_le_div_right (mul_le_mul' (mul_le_mul' hs le_rfl) le_rfl) p).trans hl

/-- The constructed named controller is an actual feasible competitor whenever
the requested success is no larger than its proved binomial guarantee. Its three
bill bounds therefore bound the native optimum, with finite optimum concluded. -/
theorem upper (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system),
      let world : World impl.tapes impl.Controls Unit (ServerState n Private)
          (GuardedStartup.encoding data) :=
        ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
      let I := instanceOf data.startup.system hx
      let parse := BatchReceipts.proposal data.startup.system
      ∀ (a r : ℕ) (_ : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (_ : 0 < (p : ℝ))
        (c : ℝ≥0)
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → ENNReal.ofReal p ≤ History.conditionalMean limits sample program
            (law limits sample program t world) o
            (fun h x => if AdaptiveSelection.productive I data.startup.system.rho parse a h x
              then 1 else 0))
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → Quantitative.conditionalMean limits sample program
            (law limits sample program t world) o charge ≤ c),
        ∀ (η : ℝ≥0∞), η ≤ ENNReal.ofReal
          (∫ j, (if r ≤ j then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial limits.turns p) →
        optimum limits sample data seed hx η ≤
          (c : ℝ≥0∞) * ENNReal.ofReal
            (∑ t ∈ Finset.range limits.turns, binomialFailure p r t) ∧
        optimum limits sample data seed hx η ≤ (c : ℝ≥0∞) * ENNReal.ofReal (r / p) ∧
        optimum limits sample data seed hx η ≤ (c : ℝ≥0∞) * limits.turns ∧
        optimum limits sample data seed hx η ≠ ∞ := by
  dsimp only
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
    a r hr p hp c Hprod Hcost η hη
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let world : World impl.tapes impl.Controls Unit (ServerState n Private)
      (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  have hnum := BatchOutput.upper_controller (n := n) width Private limits sample data seed ell
    hn hw hc he hcut hd hbudget hallot hx a r hr p hp c Hprod Hcost
  obtain ⟨hsuccess, htail, hmean, hbudgetCost, hfinite⟩ := hnum
  have hm : expected limits sample program charge (limits.turns + 1) world ∈
      costs limits sample data seed hx η := by
    refine ⟨impl.tapes, impl.Controls, impl.finite, program, ?_, hη.trans hsuccess, rfl⟩
    have hs := BatchAdmission.selectionOnly_controller width Private limits sample data seed ell
      hn hw hc hbudget.le he hcut hd hx
    intro fuel next hn C hC _
    exact hs fuel next hn C hC rfl
  have hle : optimum limits sample data seed hx η ≤
      expected limits sample program charge (limits.turns + 1) world := sInf_le hm
  exact ⟨hle.trans htail, hle.trans hmean, hle.trans hbudgetCost,
    ne_top_of_le_ne_top hfinite hle⟩

/-- With matching progress/cost envelopes and the common rounding threshold,
the actual upper controller is within factor `1/η` of the common-oracle native
optimum. Feasibility and both bounds are derived, including the case of an
unattained infimum. The only positive-success premise is the numeric binomial
threshold; successful execution is not supplied as a contract. -/
theorem competitive (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system),
      let world : World impl.tapes impl.Controls Unit (ServerState n Private)
          (GuardedStartup.encoding data) :=
        ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
      let I := instanceOf data.startup.system hx
      let parse := BatchReceipts.proposal data.startup.system
      ∀ (a r : ℕ) (_ : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (_ : 0 < (p : ℝ))
        (c : ℝ≥0)
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → ENNReal.ofReal p ≤ History.conditionalMean limits sample program
            (law limits sample program t world) o
            (fun h x => if AdaptiveSelection.productive I data.startup.system.rho parse a h x
              then 1 else 0))
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → Quantitative.conditionalMean limits sample program
            (law limits sample program t world) o charge ≤ c),
        ∀ (η : ℝ≥0∞), η ≠ 0 → η ≤ ENNReal.ofReal
          (∫ j, (if r ≤ j then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial limits.turns p) →
        (∀ q < r, a * q < I.ground.card) →
        LowerEnvelopes limits sample data seed hx a (ENNReal.ofReal p) c →
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          optimum limits sample data seed hx η / η ∧
        optimum limits sample data seed hx η ≤
          Quantitative.expected limits sample program charge (limits.turns + 1) world := by
  dsimp only
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
    a r hr p hp c Hprod Hcost η hη0 hη hround Hlower
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let world : World impl.tapes impl.Controls Unit (ServerState n Private)
      (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  have hnum := BatchOutput.upper_controller (n := n) width Private limits sample data seed ell
    hn hw hc he hcut hd hbudget hallot hx a r hr p hp c Hprod Hcost
  obtain ⟨hsuccess, _, hmean, _, _⟩ := hnum
  have hl := lower limits sample data seed hx η a r (ENNReal.ofReal p) c hround
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top Hlower
  have hm : expected limits sample program charge (limits.turns + 1) world ∈
      costs limits sample data seed hx η := by
    refine ⟨impl.tapes, impl.Controls, impl.finite, program, ?_, hη.trans hsuccess, rfl⟩
    have hs := BatchAdmission.selectionOnly_controller width Private limits sample data seed ell
      hn hw hc hbudget.le he hcut hd hx
    intro fuel next hn C hC _
    exact hs fuel next hn C hC rfl
  refine ⟨?_, sInf_le hm⟩
  have hηtop : η ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (hη.trans (hsuccess.trans (PMF.coe_le_one _ _)))
  apply (ENNReal.le_div_iff_mul_le (Or.inl hη0) (Or.inl hηtop)).mpr
  calc
    _ ≤ ((c : ℝ≥0∞) * ENNReal.ofReal (r / p)) * η :=
      mul_le_mul' hmean le_rfl
    _ = (η * r * c) / ENNReal.ofReal p := by
      rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_natCast]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := hl

/-- Source Theorem 5(2), second sentence, for every admitted native competitor.
The effective turn count is derived from actual positive-probability batch latency,
not supplied as a physical turn cap. No independent responses, integrability or
successful-output representation premise is used. -/
theorem success_le {k : ℕ} {Control : Type} (hfinite : Finite Control)
    (limits : Limits n) (sample : Sampler n Private) (data : GuardedStartup.Input)
    (seed : Private) (hx : Valid data.startup.system)
    (machine : MultiTapePTM k Bool Control Unit) (b r : ℕ)
    (hr : ∀ q < r, b * q < (instanceOf data.startup.system hx).ground.card)
    (p : Set.Icc (0 : ℝ) 1) (c : ℝ≥0∞) (ℓ : ℝ≥0) (hℓ : 0 < ℓ)
    (H : LowerEnvelopes limits sample data seed hx b (ENNReal.ofReal p) c) :
    let world := (⟨machine.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial seed, []⟩⟩ :
        World k Control Unit (ServerState n Private) (GuardedStartup.encoding data))
    NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) data.startup.system.rows.length)
      (decodeFamily data.startup.system.rows.length) (accept data.startup.system hx) world →
    Deadline.LowerLatency limits sample machine world ℓ →
    ((NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (BatchOutput.certified limits data.startup.system hx)) true ≤ ENNReal.ofReal
      (∫ j, (if r ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (Deadline.effectiveTurns limits ℓ) p) := by
  dsimp only
  intro hselect Hlat
  let world : World k Control Unit (ServerState n Private) (GuardedStartup.encoding data) :=
    ⟨machine.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  apply (certified_le_accepted limits data.startup.system hx _).trans
  apply Deadline.success_binomial limits sample machine (finiteInstance data.startup.system hx)
    b r hr world (NativeBatch.initial_invariant limits seed) rfl
    (accept data.startup.system hx)
    (accept_covers data.startup.system hx)
    hselect
    (fun t ht o ho => by
      obtain ⟨hcap, _, _⟩ := H.bounds k Control hfinite machine hselect t ht o ho
      exact hcap)
    p ℓ hℓ ?_ Hlat
  intro t ht o ho
  have hturn : t < limits.turns + 1 :=
    (ht.trans_le (min_le_left _ _)).trans (Nat.lt_succ_self _)
  obtain ⟨_, hprob, _⟩ := H.bounds k Control hfinite machine hselect t hturn o ho
  exact hprob

/-- Theorem 5(2)'s necessary success-target bound. Feasibility means an actual
admitted finite-control competitor attains that target; the binomial conclusion
and the effective physical turn count are both derived. -/
theorem feasible_success_le (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system)
    (η : ℝ≥0∞) (b r : ℕ)
    (hr : ∀ q < r, b * q < (instanceOf data.startup.system hx).ground.card)
    (p : Set.Icc (0 : ℝ) 1) (c : ℝ≥0∞) (ℓ : ℝ≥0) (hℓ : 0 < ℓ)
    (H : LowerEnvelopes limits sample data seed hx b (ENNReal.ofReal p) c)
    (Hlat : ∀ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Unit),
      let world := (⟨machine.initialConfig (GuardedStartup.encoding data),
        ⟨ConcurrentBatch.initial seed, []⟩⟩ :
          World k Control Unit (ServerState n Private) (GuardedStartup.encoding data))
      NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
        (candidateParser (n := n) data.startup.system.rows.length)
        (decodeFamily data.startup.system.rows.length) (accept data.startup.system hx) world →
      Deadline.LowerLatency limits sample machine world ℓ)
    (hfeasible : (costs limits sample data seed hx η).Nonempty) :
    η ≤ ENNReal.ofReal (∫ j, (if r ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial (Deadline.effectiveTurns limits ℓ) p) := by
  obtain ⟨v, hv⟩ := hfeasible
  obtain ⟨k, Control, hfinite, machine, hselect, hsuccess, _⟩ := hv
  exact hsuccess.trans (success_le hfinite limits sample data seed hx machine b r hr p c ℓ hℓ H
    hselect (Hlat k Control hfinite machine hselect))

end Cslib.Probability.StochasticOracle.NativeRetention.BatchOptimum
