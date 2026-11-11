/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.TimeM
public import CslibFrontier.Algorithms.Lean.TimeM.Loops
public import CslibFrontier.Foundations.Combinatorics.PessimisticEstimator
public import CslibFrontier.Probability.Product.ConditionalExpectation

/-!
# Costed pessimistic estimators and conditional expectations in `TimeM`

`Cslib.PessimisticEstimator.greedy` models the method of conditional expectations purely
mathematically, treating branch construction and estimator evaluation as free. This module packages
both binary pessimistic-estimator rounds (`CostedGreedy`) and finite-product-space conditional
expectations (`CostedProductDerandomizer`) in `TimeM ℕ`, charging every branch construction,
conditional-expectation query, and comparison explicitly.

* `CostedGreedy` wraps a costed state transition `branchM : R → Bool → S → TimeM ℕ S`, a costed
  estimator `estimateM : S → TimeM ℕ M`, and a per-round `compareCost`. Its pure return value
  agrees with `PessimisticEstimator.greedy` (`ret_runM`), while `runM_spec` and
  `runM_spec_of_add_le` establish the invariant, the deterministic objective bound
  `estimate final ≤ estimate init`, and the accumulated `TimeM` step bound along reachable states.
* `CostedProductDerandomizer` executes the method of conditional expectations over a finite product
  space `∀ i : ι, α i`: for each coordinate `i` in `order`, it evaluates the costed conditional
  expectation oracle `condExpM (insert i fixed) (Function.update x i a)` across every candidate
  `a ∈ choices i` and selects a minimizing coordinate value. When `condExpM` agrees with
  `PMF.condExpect p f` through a monotone map `M → ℝ`, `derandomizeM_spec` proves both
  `f final ≤ E_{y ∼ pi p}[f y]` and the explicit total evaluation-cost bound
  `∑ i ∈ order, (choices i).length * (evalBound i + compareCost)`.

## Main definitions

* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy`: costed binary greedy / pessimistic
  estimator bundle.
* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy.stepM`, `runM`: single-round and
  multi-round `TimeM` execution.
* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedProductDerandomizer`: costed finite-product
  conditional-expectation derandomizer.
* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedProductDerandomizer.derandomizeM`: coordinate
  fixing over an explicit round order in `TimeM`.

## Main results

* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy.ret_runM`,
  `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy.time_stepM`: return-value agreement with
  `Cslib.PessimisticEstimator.greedy` and exact single-round cost.
* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy.runM_spec`,
  `Cslib.Algorithms.Lean.PessimisticEstimator.CostedGreedy.runM_spec_of_add_le`: combined
  invariant, objective, and `TimeM` cost bounds.
* `Cslib.Algorithms.Lean.PessimisticEstimator.CostedProductDerandomizer.derandomizeM_spec`:
  deterministic expectation guarantee `f final ≤ E[f]` paired with explicit `TimeM` evaluation cost
  over finite product distributions `PMF.pi p`.
-/

public section

open scoped BigOperators

namespace Cslib.Algorithms.Lean.PessimisticEstimator

open Cslib.PessimisticEstimator Cslib.Probability

/-! ### Costed binary pessimistic estimators -/

/-- Costed binary greedy / pessimistic-estimator specification in `TimeM ℕ`. -/
structure CostedGreedy (R : Type*) (S M : Type) where
  /-- Costed branch state transition for round `r` and choice `b`. -/
  branchM : R → Bool → S → TimeM ℕ S
  /-- Costed pessimistic-estimator / conditional-expectation evaluation. -/
  estimateM : S → TimeM ℕ M
  /-- Time ticks charged for comparing the two branch estimates. -/
  compareCost : ℕ := 1

namespace CostedGreedy

section Basic

variable {R : Type*} {S M : Type} (C : CostedGreedy R S M)

/-- Underlying pure branch transition `(C.branchM r b s).ret`. -/
@[expose] def branch (r : R) (b : Bool) (s : S) : S :=
  (C.branchM r b s).ret

/-- Underlying pure estimator `(C.estimateM s).ret`. -/
@[expose] def estimate (s : S) : M :=
  (C.estimateM s).ret

/-- Execute one greedy round in `TimeM ℕ`: construct both branch states, evaluate `estimateM` on
both, and charge `compareCost` for selecting the smaller branch (ties go to `true`). -/
@[expose] def stepM [LE M] [DecidableRel (α := M) (· ≤ ·)] (s : S) (r : R) : TimeM ℕ S := do
  let sT ← C.branchM r true s
  let sF ← C.branchM r false s
  let vT ← C.estimateM sT
  let vF ← C.estimateM sF
  ✓[C.compareCost] pure (if vT ≤ vF then sT else sF)

/-- Execute a list of greedy rounds sequentially in `TimeM ℕ`. -/
@[expose] def runM [LE M] [DecidableRel (α := M) (· ≤ ·)] (rounds : List R) (s : S) : TimeM ℕ S :=
  rounds.foldlM C.stepM s

@[simp]
theorem ret_stepM [LE M] [DecidableRel (α := M) (· ≤ ·)] (s : S) (r : R) :
    (C.stepM s r).ret = greedyStep C.branch C.estimate s r :=
  rfl

@[simp]
theorem ret_runM [LE M] [DecidableRel (α := M) (· ≤ ·)] (rounds : List R) (s : S) :
    (C.runM rounds s).ret = greedy C.branch C.estimate rounds s := by
  rw [runM, TimeM.ret_foldlM]
  rfl

theorem time_stepM [LE M] [DecidableRel (α := M) (· ≤ ·)] (s : S) (r : R) :
    (C.stepM s r).time =
      (C.branchM r true s).time + (C.branchM r false s).time +
        (C.estimateM (C.branch r true s)).time +
        (C.estimateM (C.branch r false s)).time + C.compareCost := by
  change (C.branchM r true s).time +
      ((C.branchM r false s).time +
        ((C.estimateM (C.branch r true s)).time +
          ((C.estimateM (C.branch r false s)).time + (C.compareCost + 0)))) = _
  omega

end Basic

section Spec

variable {R : Type*} {S M : Type} [LinearOrder M] (C : CostedGreedy R S M)

/-- **Costed pessimistic-estimator specification**: under an invariant `Inv` preserved along both
branches where the smaller branch estimate does not exceed the current estimate and per-branch
`branchM`/`estimateM` times are bounded by `branchBound r` and `estBound r`, `runM` preserves the
terminal invariant, achieves `C.estimate final ≤ C.estimate s`, and uses at most
`∑ r ∈ rounds, (2 * branchBound r + 2 * estBound r + C.compareCost)` ticks. -/
theorem runM_spec (Inv : List R → S → Prop) (branchBound estBound : R → ℕ)
    (hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (C.branch r b s))
    (hmin : ∀ r rs s, Inv (r :: rs) s →
      min (C.estimate (C.branch r true s)) (C.estimate (C.branch r false s)) ≤ C.estimate s)
    (htime_branch : ∀ r rs s b, Inv (r :: rs) s → (C.branchM r b s).time ≤ branchBound r)
    (htime_est : ∀ r rs s b, Inv (r :: rs) s →
      (C.estimateM (C.branch r b s)).time ≤ estBound r) :
    ∀ (rounds : List R) (s : S), Inv rounds s →
      Inv [] (C.runM rounds s).ret ∧
        C.estimate (C.runM rounds s).ret ≤ C.estimate s ∧
        (C.runM rounds s).time ≤
          (rounds.map fun r => 2 * branchBound r + 2 * estBound r + C.compareCost).sum
  | [], s, hs => ⟨hs, le_rfl, by simp [runM]⟩
  | r :: rs, s, hs => by
    have hstep_inv : Inv rs (C.stepM s r).ret := by
      rw [ret_stepM]
      rcases greedyStep_eq_or C.branch C.estimate s r with h | h <;>
        rw [h] <;> exact hbranch r rs s _ hs
    have hstep_le : C.estimate (C.stepM s r).ret ≤ C.estimate s := by
      rw [ret_stepM]
      exact estimate_greedyStep_le C.branch C.estimate (hmin r rs s hs)
    have hstep_time : (C.stepM s r).time ≤
        2 * branchBound r + 2 * estBound r + C.compareCost := by
      rw [time_stepM]
      have hbT := htime_branch r rs s true hs
      have hbF := htime_branch r rs s false hs
      have heT := htime_est r rs s true hs
      have heF := htime_est r rs s false hs
      omega
    obtain ⟨hinv_end, hest_end, htime_end⟩ :=
      runM_spec Inv branchBound estBound hbranch hmin htime_branch htime_est rs
        (C.stepM s r).ret hstep_inv
    refine ⟨?_, ?_, ?_⟩
    · simpa only [runM, List.foldlM_cons, TimeM.ret_bind] using hinv_end
    · have hret : (C.runM (r :: rs) s).ret = (C.runM rs (C.stepM s r).ret).ret := rfl
      rw [hret]
      exact hest_end.trans hstep_le
    · simp only [runM, List.foldlM_cons, TimeM.time_bind, List.map_cons, List.sum_cons]
        at htime_end ⊢
      omega

/-- Averaging form of `runM_spec` when the two branch estimates sum to at most twice the current
estimate. -/
theorem runM_spec_of_add_le [AddCommMonoid M] [IsOrderedCancelAddMonoid M]
    (Inv : List R → S → Prop) (branchBound estBound : R → ℕ)
    (hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (C.branch r b s))
    (havg : ∀ r rs s, Inv (r :: rs) s →
      C.estimate (C.branch r true s) + C.estimate (C.branch r false s) ≤
        C.estimate s + C.estimate s)
    (htime_branch : ∀ r rs s b, Inv (r :: rs) s → (C.branchM r b s).time ≤ branchBound r)
    (htime_est : ∀ r rs s b, Inv (r :: rs) s →
      (C.estimateM (C.branch r b s)).time ≤ estBound r)
    (rounds : List R) (s : S) (hs : Inv rounds s) :
    Inv [] (C.runM rounds s).ret ∧
      C.estimate (C.runM rounds s).ret ≤ C.estimate s ∧
      (C.runM rounds s).time ≤
        (rounds.map fun r => 2 * branchBound r + 2 * estBound r + C.compareCost).sum :=
  C.runM_spec Inv branchBound estBound hbranch
    (fun r rs s h => min_le_of_add_le_two_nsmul ((havg r rs s h).trans_eq (two_nsmul _).symm))
    htime_branch htime_est rounds s hs

end Spec

end CostedGreedy

/-! ### Costed method of conditional expectations on a finite product space -/

/-- Costed deterministic conditional-expectation derandomizer over `∀ i : ι, α i`: at each
coordinate `i`, evaluates `condExpM (insert i fixed) (Function.update x i a)` across every candidate
`a ∈ choices i` and picks a value minimizing the returned conditional expectation. -/
structure CostedProductDerandomizer (ι : Type) (α : ι → Type) (M : Type) where
  /-- Nonempty candidate list of domain values tested at coordinate `i`. -/
  choices : (i : ι) → List (α i)
  /-- Costed conditional-expectation oracle given fixed coordinates and current assignment. -/
  condExpM : Finset ι → (∀ i, α i) → TimeM ℕ M
  /-- Time ticks charged per candidate comparison. -/
  compareCost : ℕ := 1

namespace CostedProductDerandomizer

section Execution

variable {ι : Type} [DecidableEq ι] {α : ι → Type} {M : Type}
  [LE M] [DecidableRel (α := M) (· ≤ ·)]
  (D : CostedProductDerandomizer ι α M)

/-- Evaluate candidates in `cs` starting from best pair `(bestA, bestV)` in `TimeM ℕ`. -/
@[expose] def scanCandidatesM (fixedNext : Finset ι) (x : ∀ i, α i) (i : ι) :
    List (α i) → α i × M → TimeM ℕ (α i × M)
  | [], best => pure best
  | a :: cs, best => do
      let val ← D.condExpM fixedNext (Function.update x i a)
      let next ← ✓[D.compareCost] pure (if val ≤ best.2 then (a, val) else best)
      scanCandidatesM fixedNext x i cs next

/-- Choose the best value for coordinate `i` among `D.choices i` (leaving `x` unchanged if
`D.choices i` is empty). -/
@[expose] def stepCoordM (state : Finset ι × (∀ i, α i)) (i : ι) :
    TimeM ℕ (Finset ι × (∀ i, α i)) :=
  let fixedNext := insert i state.1
  match D.choices i with
  | [] => pure (fixedNext, state.2)
  | a₀ :: cs => do
      let v₀ ← D.condExpM fixedNext (Function.update state.2 i a₀)
      let best ← D.scanCandidatesM fixedNext state.2 i cs (a₀, v₀)
      pure (fixedNext, Function.update state.2 i best.1)

/-- Run coordinate fixing along `order` starting from `(fixed, x)` in `TimeM ℕ`. -/
@[expose] def runFromM (order : List ι) (fixed : Finset ι) (x : ∀ i, α i) :
    TimeM ℕ (Finset ι × (∀ i, α i)) :=
  order.foldlM D.stepCoordM (fixed, x)

/-- Deterministic assignment produced by fixing all coordinates in `order` from `∅`. -/
@[expose] def derandomizeM (order : List ι) (init : ∀ i, α i) : TimeM ℕ (∀ i, α i) :=
  Prod.snd <$> D.runFromM order ∅ init

end Execution

section CorrectnessAndCost

variable {ι : Type} [DecidableEq ι] {α : ι → Type} {M : Type} [LinearOrder M]
  (D : CostedProductDerandomizer ι α M)

private theorem scanCandidatesM_spec (fixedNext : Finset ι) (x : ∀ i, α i) (i : ι)
    {evalBound : ℕ}
    (htime : ∀ a, (D.condExpM fixedNext (Function.update x i a)).time ≤ evalBound) :
    ∀ (cs : List (α i)) (best : α i × M),
      best.2 = (D.condExpM fixedNext (Function.update x i best.1)).ret →
      (D.scanCandidatesM fixedNext x i cs best).ret.2 =
          (D.condExpM fixedNext
            (Function.update x i (D.scanCandidatesM fixedNext x i cs best).ret.1)).ret ∧
        (D.scanCandidatesM fixedNext x i cs best).ret.2 ≤ best.2 ∧
        (∀ a ∈ cs, (D.scanCandidatesM fixedNext x i cs best).ret.2 ≤
          (D.condExpM fixedNext (Function.update x i a)).ret) ∧
        (D.scanCandidatesM fixedNext x i cs best).time ≤ cs.length * (evalBound + D.compareCost)
  | [], best, hbest => ⟨hbest, le_rfl, by simp, by simp [scanCandidatesM]⟩
  | a :: cs, best, hbest => by
    let val := (D.condExpM fixedNext (Function.update x i a)).ret
    let next : α i × M := if val ≤ best.2 then (a, val) else best
    have hnext_eq : next.2 = (D.condExpM fixedNext (Function.update x i next.1)).ret := by
      dsimp only [next, val]
      split_ifs <;> simp [hbest]
    have hnext_le_best : next.2 ≤ best.2 := by
      dsimp only [next]
      split_ifs with hle
      · exact hle
      · exact le_rfl
    have hnext_le_a : next.2 ≤ val := by
      dsimp only [next]
      split_ifs with hle
      · exact le_rfl
      · exact le_of_not_ge hle
    obtain ⟨heq_out, hle_next, hforall_cs, htime_cs⟩ :=
      scanCandidatesM_spec fixedNext x i htime cs next hnext_eq
    have hret : (D.scanCandidatesM fixedNext x i (a :: cs) best).ret =
        (D.scanCandidatesM fixedNext x i cs next).ret := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hret]
      exact heq_out
    · rw [hret]
      exact hle_next.trans hnext_le_best
    · intro b hb
      rw [hret]
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hle_next.trans hnext_le_a
      · exact hforall_cs b hb'
    · have ha_time := htime a
      dsimp only [next, val] at htime_cs
      simp only [scanCandidatesM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
        TimeM.ret_pure, List.length_cons, Nat.succ_mul]
      omega

private theorem runFromM_spec [Fintype ι] [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {toReal : M → ℝ} (hmono : Monotone toReal)
    (heval : ∀ fixed x, toReal (D.condExpM fixed x).ret = PMF.condExpect p f fixed x)
    (hchoices : ∀ i a, a ∈ (p i).support → a ∈ D.choices i)
    (evalBound : ι → ℕ)
    (htime : ∀ i fixed x, (D.condExpM (insert i fixed) x).time ≤ evalBound i) :
    ∀ (order : List ι) (fixed : Finset ι) (x : ∀ i, α i),
      order.Nodup → (∀ j ∈ order, j ∉ fixed) →
      (D.runFromM order fixed x).ret.1 = fixed ∪ order.toFinset ∧
        PMF.condExpect p f (D.runFromM order fixed x).ret.1
          (D.runFromM order fixed x).ret.2 ≤ PMF.condExpect p f fixed x ∧
        (D.runFromM order fixed x).time ≤
          (order.map fun i => (D.choices i).length * (evalBound i + D.compareCost)).sum
  | [], fixed, x, _, _ => by
    simp [runFromM]
  | i :: rs, fixed, x, hnd, hdisj => by
    obtain ⟨hi_rs, hnd_rs⟩ := List.nodup_cons.mp hnd
    have hi_fix : i ∉ fixed := hdisj i List.mem_cons_self
    obtain ⟨a_star, ha_supp, ha_le⟩ := PMF.exists_condExpect_insert_le p f hi_fix x
    have ha_mem : a_star ∈ D.choices i := hchoices i a_star ha_supp
    cases hcs : D.choices i with
    | nil =>
      rw [hcs] at ha_mem
      cases ha_mem
    | cons a₀ cs =>
      let fixedNext := insert i fixed
      let v₀ := (D.condExpM fixedNext (Function.update x i a₀)).ret
      obtain ⟨heq_best, hle_v₀, hle_cs, htime_scan⟩ :=
        scanCandidatesM_spec D fixedNext x i (fun a => htime i fixed _) cs (a₀, v₀) rfl
      set best := (D.scanCandidatesM fixedNext x i cs (a₀, v₀)).ret
      have hbest_le_star : best.2 ≤ (D.condExpM fixedNext (Function.update x i a_star)).ret := by
        rw [hcs] at ha_mem
        rcases List.mem_cons.mp ha_mem with rfl | hmem_cs
        · exact hle_v₀
        · exact hle_cs a_star hmem_cs
      have hstep_exp : PMF.condExpect p f fixedNext (Function.update x i best.1) ≤
          PMF.condExpect p f fixed x := by
        have hm := hmono hbest_le_star
        rw [heq_best, heval, heval] at hm
        exact hm.trans ha_le
      have hstep_time : (D.stepCoordM (fixed, x) i).time ≤
          (a₀ :: cs).length * (evalBound i + D.compareCost) := by
        have hv₀_time := htime i fixed (Function.update x i a₀)
        dsimp only [fixedNext, v₀] at htime_scan hv₀_time
        simp only [stepCoordM, hcs, TimeM.time_bind, TimeM.time_pure, List.length_cons,
          Nat.succ_mul]
        omega
      have hdisj_next : ∀ j ∈ rs, j ∉ fixedNext := by
        intro j hj hmem
        rcases Finset.mem_insert.mp hmem with rfl | hj_fix
        · exact hi_rs hj
        · exact hdisj j (List.mem_cons_of_mem i hj) hj_fix
      have hstep_ret : (D.stepCoordM (fixed, x) i).ret =
          (fixedNext, Function.update x i best.1) := by
        simp [stepCoordM, hcs, fixedNext, best, v₀]
      obtain ⟨hset_end, hexp_end, htime_end⟩ :=
        runFromM_spec p f hmono heval hchoices evalBound htime rs fixedNext
          (Function.update x i best.1) hnd_rs hdisj_next
      have hret : (D.runFromM (i :: rs) fixed x).ret =
          (D.runFromM rs fixedNext (Function.update x i best.1)).ret := by
        simp [runFromM, hstep_ret]
      refine ⟨?_, ?_, ?_⟩
      · rw [hret, hset_end]
        ext j
        simp [fixedNext]
      · rw [hret]
        exact hexp_end.trans hstep_exp
      · simp only [runFromM, List.foldlM_cons, TimeM.time_bind, hstep_ret, List.map_cons,
          List.sum_cons, hcs] at htime_end ⊢
        omega

/-- **Costed method of conditional expectations on a finite product space**: if `order` visits
every coordinate without repetition, `D.choices i` covers `(p i).support`, and `D.condExpM`
computes `PMF.condExpect p f` (via monotone `toReal : M → ℝ`) in at most `evalBound i` ticks at
round `i`, then `D.derandomizeM order init` returns a deterministic point `x*` with
`f x* ≤ E_{y ∼ pi p}[f y]` in at most
`∑ i ∈ order, (D.choices i).length * (evalBound i + D.compareCost)` ticks. -/
theorem derandomizeM_spec [Fintype ι] [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {toReal : M → ℝ} (hmono : Monotone toReal)
    (heval : ∀ fixed x, toReal (D.condExpM fixed x).ret = PMF.condExpect p f fixed x)
    (hchoices : ∀ i a, a ∈ (p i).support → a ∈ D.choices i)
    (evalBound : ι → ℕ)
    (htime : ∀ i fixed x, (D.condExpM (insert i fixed) x).time ≤ evalBound i)
    (order : List ι) (hnd : order.Nodup) (hcov : ∀ i, i ∈ order) (init : ∀ i, α i) :
    f (D.derandomizeM order init).ret ≤ ∑ y, (PMF.pi p y).toReal * f y ∧
      (D.derandomizeM order init).time ≤
        (order.map fun i => (D.choices i).length * (evalBound i + D.compareCost)).sum := by
  obtain ⟨hset, hexp, hcost⟩ :=
    runFromM_spec D p f hmono heval hchoices evalBound htime order ∅ init hnd (by simp)
  have huniv : (D.runFromM order ∅ init).ret.1 = Finset.univ := by
    rw [hset]
    ext i
    simp [hcov i]
  rw [huniv, PMF.condExpect_univ, PMF.condExpect_empty] at hexp
  exact ⟨hexp, hcost⟩

end CorrectnessAndCost

end CostedProductDerandomizer

end Cslib.Algorithms.Lean.PessimisticEstimator
