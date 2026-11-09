/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.ProgressComparison
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Revealed coverage and success-level native cost lower bounds

[Wang2027], Theorem 5(2), PDF p. 12, Appendix A.5 p. 16. Source proposals are
parsed from actual concurrent-batch reports. Cardinality caps and conditional
progress/cost envelopes concern only reached selected epochs. Selection-only
admission is the existing condition on the original native terminal law.

The acceptance predicate must count only covers. It may additionally require a
weight certificate; selection admission is required only for that predicate. The
success event is an actually decoded accepted output, not an assumed count
threshold. Accrued costs include receipts before silent divergence. All expectations
are nonnegative extended expectations; no integrability or bounded bill is assumed.

## Main results

* `revealed_source`: actual revealed coverage equals the source provenance ledger.
* `revealed_card_bound`: reached-response caps imply the actual pathwise count bound.
* `success_count`: actual selection-only covering output forces enough revealed progress.
* `success_cost_lower`: success-level lower bound from actual source epoch envelopes.
* `success_binomial`: native accepted-cover bound for the actual issued-turn budget.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Coverage
open NativeOpenExecution NativeInterface StochasticOracle ConcurrentBatch Turing Trace Quantitative
open AdaptiveSelection PartialCover
open scoped ENNReal
variable {n k m : ℕ} {Private Control E : Type} [DecidableEq E] {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- Actual source proposals, including all completed proposals in a concurrent receipt. -/
@[expose] def proposal (m : ℕ) (_ : List (Record n)) : Record n → List (Finset (Fin m))
  | none => []
  | some receipt => proposals m receipt.report

/-- Parsed source provenance and actual revealed coverage agree on every receipt list. -/
theorem revealed_source (I : Instance E (Fin m)) (history : List (Record n)) :
    revealed I (proposal m) history = I.covered (sourceAvailable m (history.filterMap id)) := by
  induction history with
  | nil => simp [revealed, sourceAvailable, Instance.covered]
  | cons record history ih =>
    cases record with
    | none => simpa [revealed, proposal, sourceAvailable, Instance.covered] using ih
    | some receipt =>
      simpa only [revealed, proposal, List.filterMap_cons, id_eq, sourceAvailable,
        I.covered_union] using congrArg (I.covered
          ((proposals m receipt.report).foldr (· ∪ ·) ∅) ∪ ·) ih

/-- Cardinality caps are needed only on responses to reached selected histories,
not on arbitrary histories or hidden states. -/
theorem revealed_card_bound (I : Instance E (Fin m)) (b turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    (revealed I (proposal m) state.records).card ≤
      b * count (reveals I (proposal m)) state.records := by
  classical
  induction turns generalizing state with
  | zero =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hs
    subst state
    simp [Trace.initial, revealed, count]
  | succ turns ih =>
    have hs' : state ∈ ((law limits sample machine turns world).bind
        (Trace.step limits sample machine)).support := hs
    obtain ⟨before, hb, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    obtain ⟨record, he⟩ := History.step_records limits sample machine before state hstep
    have hprior := ih (fun t ht => H t (by omega)) before hb
    rw [← selection_factor limits sample machine] at hs'
    obtain ⟨o, ho, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    obtain ⟨other, hh⟩ := History.conditional_records limits sample machine _ o ho state hn
    have hhistory : o.history = before.records := by rw [he] at hh; exact (List.cons.inj hh).2.symm
    have hcap := H turns (by omega) o ho state hn
    rw [hhistory, he] at hcap
    rw [he]
    have hm : revealed I (proposal m) before.records ⊆
        revealed I (proposal m) (record :: before.records) := Finset.subset_union_right
    have hcard := Finset.card_sdiff_add_card_eq_card hm
    by_cases hx : reveals I (proposal m) before.records record = true
    · simp only [count, hx, ite_true, Nat.mul_add, Nat.mul_one]
      omega
    · have hz : (revealed I (proposal m) (record :: before.records) \
          revealed I (proposal m) before.records).card = 0 := by
        simpa only [reveals, decide_eq_true_eq, Finset.not_nonempty_iff_eq_empty,
          Finset.card_eq_zero] using hx
      simp only [count, hx, Bool.false_eq_true, ite_false, Nat.add_zero]
      omega

open scoped Classical in
/-- Acceptance for the lower bound means a decoded covering output. A stronger
cost certificate may be imposed by the source application independently. -/
@[expose] def coverAccept (I : Instance E (Fin m)) (C : Finset (Fin m)) : Bool :=
  decide (I.covered C = I.ground)

/-- Actual decoded accepted output on the native hidden terminal phase. Divergence
and non-output phases are failures; their earlier accrued bills remain in the trace. -/
@[expose] def success (accept : Finset (Fin m) → Bool)
    (state : State n k Private Control input) : Bool :=
  match state.hidden with
  | some (.ready next) => (NativeOpenSelection.result (decodeFamily m) next).any accept
  | _ => false

/-- Acceptance read directly from the original optional native terminal world. -/
@[expose] def nativeSuccess (accept : Finset (Fin m) → Bool)
    (result : Option (World k Control Unit (ServerState n Private) input)) : Bool :=
  result.any fun next => (NativeOpenSelection.result (decodeFamily m) next).any accept

/-- Actual whole-policy acceptance agrees with the original unbounded native
terminal event, including its divergent mass. No success-law equality is assumed. -/
theorem success_law (accept : Finset (Fin m) → Bool)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    (law limits sample machine (limits.turns + 1) world).map (success accept) =
      (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeSuccess accept) := by
  rw [← law_native_terminal limits sample machine world hi, PMF.map_comp]
  apply PMF.bind_congr_on_support
  intro state hs
  rcases law_done limits sample machine world hi state hs with hn | ⟨next, he, _⟩
  · simp [success, nativeSuccess, hn, Function.comp_def]
  · simp [success, nativeSuccess, he, Function.comp_def, worldOf]

/-- Selection-only provenance, actual source parsing and reached cardinality caps
force a progress count on every actually successful terminal execution. -/
theorem success_count (I : Instance E (Fin m)) (b r : ℕ)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (H : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine (limits.turns + 1) world).support)
    (hsuccess : success accept state = true) :
    r ≤ count (reveals I (proposal m)) state.records := by
  classical
  cases he : state.hidden with
  | none => simp [success, he] at hsuccess
  | some phase =>
    cases phase with
    | pending tx => simp [success, he] at hsuccess
    | ready next =>
      cases hc : NativeOpenSelection.result (decodeFamily m) next with
      | none => simp [success, he, hc] at hsuccess
      | some C =>
        have ha : accept C = true := by simpa [success, he, hc] using hsuccess
        have hp := Trace.terminal_provenance limits sample machine m accept
          world next hi hzero hselect state hs he C hc ha
        have hcover : I.covered C = I.ground := haccept C ha
        have hm : I.covered C ⊆ I.covered (sourceAvailable m (state.records.filterMap id)) :=
          by
            intro e he
            obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
            exact Finset.mem_biUnion.mpr ⟨j, hp hj, he⟩
        rw [hcover, ← revealed_source I] at hm
        have hcard := Finset.card_le_card hm
        have hb := revealed_card_bound limits sample machine I b _ world H state hs
        by_contra hn
        have := hr _ (Nat.lt_of_not_ge hn)
        omega

/-- Selected revealed-progress envelopes bound the expected *actual* progress
count by the expected number of issued batches. -/
theorem progress_mean_le (I : Instance E (Fin m)) (p : ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      History.conditionalMean limits sample machine (law limits sample machine t world) o
        (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤
          p * (if o.issued then 1 else 0)) :
    History.expected limits sample machine
        (fun h x => if reveals I (proposal m) h x then 1 else 0) turns world ≤
      p * Quantitative.expected limits sample machine issued turns world := by
  rw [History.expected_sum, expected_accrued, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  unfold marginal
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro o
  by_cases ho : o ∈ ((select limits sample machine
      (law limits sample machine t world)).map (Quantitative.observe limits)).support
  · dsimp only
    rw [conditional_issued limits sample machine _ o ho]
    simpa only [mul_left_comm p] using mul_le_mul_right (H t (Finset.mem_range.mp ht) o ho) _
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- A zero-call decision reveals no new source proposal. This derives the
padding envelope from actual conditional receipt support, including divergence. -/
theorem conditional_revealed_zero (I : Instance E (Fin m))
    (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support)
    (hz : o.issued = false) :
    History.conditionalMean limits sample machine prior o
      (fun h x => if reveals I (proposal m) h x then 1 else 0) = 0 := by
  classical
  unfold History.conditionalMean mean
  apply tsum_eq_zero_iff.mpr
  intro next
  by_cases hn : next ∈ (conditional limits sample machine prior o).support
  · obtain ⟨record, hr⟩ := History.conditional_records limits sample machine prior o ho next hn
    have he := conditional_record_isSome limits sample machine prior o ho next hn
    rw [hz, hr, List.headD_cons] at he
    cases record with
    | some receipt => cases he
    | none => simp [History.newest, hr, reveals, revealed, proposal, Instance.covered]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]

/-- The source progress upper envelope is needed only on actual issued batches.
Halt/divergence padding contributes zero, as a theorem about actual receipts. -/
theorem revealed_envelope (I : Instance E (Fin m)) (p : ℝ≥0∞)
    (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support)
    (H : o.issued = true → History.conditionalMean limits sample machine prior o
      (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤ p) :
    History.conditionalMean limits sample machine prior o
      (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤
        p * (if o.issued then 1 else 0) := by
  cases he : o.issued with
  | true => simpa only [he, ite_true, mul_one] using H he
  | false => rw [conditional_revealed_zero limits sample machine I prior o ho he]; simp

/-- Source success-level lower accounting: actual success probability times the
required progress and per-turn cost, divided by `p`, is at most the actual accrued bill.
This is stronger than issued-count accounting: the progress requirement is derived
from decoded native output and selection-only provenance. -/
theorem success_cost_lower (I : Instance E (Fin m)) (b r : ℕ) (p c : ℝ≥0∞)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (Hcap : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (Hprob : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤ p)
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    (Hcost : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → c ≤ Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge) :
    (((NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (nativeSuccess accept) true) * r * c) / p ≤
      Quantitative.expected limits sample machine charge (limits.turns + 1) world := by
  rw [← success_law limits sample machine accept world hi]
  apply (ENNReal.div_le_iff hp0 hptop).mpr
  rw [mul_comm _ p]
  have hc : ((law limits sample machine (limits.turns + 1) world).map (success accept) true) * r ≤
      History.expected limits sample machine
        (fun h x => if reveals I (proposal m) h x then 1 else 0) (limits.turns + 1) world := by
    rw [← DiscreteComparison.indicator_mean, ← ENNReal.tsum_mul_right]
    unfold History.expected mean
    simp only [History.accumulated_count]
    apply tsum_le_tsum
    intro state
    by_cases hs : state ∈ (law limits sample machine (limits.turns + 1) world).support
    · by_cases he : success accept state = true
      · simp only [he, ite_true, mul_one]
        have hn := success_count limits sample machine I b r hr world hi hzero
          accept haccept hselect Hcap state hs he
        have hn' : (r : ℝ≥0∞) ≤ count (reveals I (proposal m)) state.records := by
          exact_mod_cast hn
        simpa only [mul_assoc] using mul_le_mul_right hn'
          (law limits sample machine (limits.turns + 1) world state)
      · simp [he]
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]
  have hp := hc.trans (progress_mean_le limits sample machine I p _ world
    (fun t ht o ho => revealed_envelope limits sample machine I p _ o ho (Hprob t ht o ho)))
  have hb := cost_lower limits sample machine c _ world Hcost
  calc
    _ ≤ (p * Quantitative.expected limits sample machine issued (limits.turns + 1) world) * c :=
      mul_le_mul_left hp c
    _ = p * (c * Quantitative.expected limits sample machine issued (limits.turns + 1) world) :=
      by ring
    _ ≤ _ := mul_le_mul_right hb p

/-- Accepted native covering outputs require the actual revealed-progress tail.
The implication follows from concrete source provenance and reached coverage caps. -/
theorem success_count_tail (I : Instance E (Fin m)) (b r : ℕ)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (H : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    : (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeSuccess accept) true ≤
      mean (law limits sample machine (limits.turns + 1) world) (fun state =>
        ENNReal.ofReal (if r ≤ count (reveals I (proposal m)) state.records then 1 else 0)) := by
  classical
  rw [← success_law limits sample machine accept world hi]
  rw [← DiscreteComparison.indicator_mean]
  apply tsum_le_tsum
  intro state
  by_cases hs : state ∈ (law limits sample machine (limits.turns + 1) world).support
  · apply mul_le_mul_right
    by_cases he : success accept state = true
    · have hn := success_count limits sample machine I b r hr world hi hzero
        accept haccept hselect H state hs he
      simp [he, hn]
    · simp [he]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]

/-- The original native machine's actual covering-output probability is bounded
by the binomial tail for the source issued-turn budget, with no fictitious trial
for silent completion. The physical-latency refinement at the source
`min(u, floor(D/ℓ))` is provided by `NativeBatch.Deadline`. -/
theorem success_binomial (I : Instance E (Fin m)) (b r : ℕ)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (H : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (p : Set.Icc (0 : ℝ) 1)
    (Hprob : ∀ t < limits.turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤ ENNReal.ofReal p) :
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeSuccess accept) true ≤ ENNReal.ofReal
      (∫ j, (if r ≤ j then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial limits.turns p) := by
  classical
  rw [← success_law limits sample machine accept world hi]
  have hm : Monotone (fun j : ℕ => if r ≤ j then (1 : ℝ) else 0) := by
    intro i j hij
    dsimp only
    split_ifs <;> norm_num; omega
  have hc := ProgressComparison.count_upper limits sample machine world
    (reveals I (proposal m)) p limits.turns
    (by
      intro t ht o ho
      have hp := revealed_envelope limits sample machine I (ENNReal.ofReal p) _ o ho
        (Hprob t ht o ho)
      apply hp.trans
      split_ifs <;> simp)
    _ hm (by intro j; split_ifs <;> norm_num)
  rw [bernoulliExpectation_eq_integral] at hc
  simp only [Nat.zero_add] at hc
  apply le_trans _ hc
  have hbound := success_count_tail limits sample machine I b r hr world hi hzero
    accept haccept hselect H
  rw [← success_law limits sample machine accept world hi] at hbound
  apply hbound.trans_eq
  rw [History.final_records_mean limits sample machine world hi
    (fun h => ENNReal.ofReal (if r ≤ count (reveals I (proposal m)) h then 1 else 0))]
  simp [count, reveals, revealed, proposal, Instance.covered]

end Cslib.Probability.NativeBatch.Coverage
