/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Amortized

/-!
# Online request-serving problems and competitive analysis

This file defines a shared action and cost model for deterministic online algorithms and offline
reference schedules, following the amortized competitive-analysis framework of
[Sleator and Tarjan, *Amortized Efficiency of List Update and Paging Rules*][SleatorTarjan1985]
and [Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition, Chapter 17
and Problem 17-5 ("Competitive analysis of self-organizing lists with move-to-front")][CLRS2009].

An online `Problem` specifies an observable configuration type `State`, a request type `Req`, an
initial-state predicate `ValidInit`, a single-step transition relation `ValidStep`, and a
single-step cost `stepCost`. Both online strategies (`DetStrategy`) and offline schedules
(`ValidSchedule`) are evaluated with the same `ValidInit`, `ValidStep`, and `scheduleCost`
definitions:

* A `DetStrategy` maintains internal memory `Mem` and updates it from the current request alone,
  without inspecting future requests, while projecting to a valid `Problem` trajectory. Any
  prefix-dependent online decision rule can also be packaged via `DetStrategy.ofHistory`.
* `IsCompetitive` compares an online strategy against every valid offline schedule from the same
  admissible initial state with integer multiplicative factor `c : Nat` and additive constant
  `b : Nat`; `IsCompetitiveAnyInit` compares across arbitrary admissible initial states.
* `Problem.offlineSpec` and `DetStrategy.amortized_bound` reuse `Cslib.Stateful.Amortized` from
  `Complexity.Foundations.Semantics.Stateful.Amortized` directly: a step-level potential
  certificate between offline state and online internal memory telescopes via `Amortized.client`
  to yield competitive bounds.
* `DetStrategy.adaptiveRequests` generates an explicit finite request sequence step-by-step against
  a deterministic strategy's evolving observable state, making adversarial lower-bound witnesses
  concrete.

This module covers deterministic strategies (for which step-by-step adaptive request generation
produces an ordinary request list whose oblivious replay induces the identical execution).
Randomized strategies and expected-cost distinctions between oblivious and adaptive adversaries
are separate.

## Main definitions

* `Cslib.Algorithms.Lean.Online.Problem`: shared configuration, request, admissibility, and step
  cost specification.
* `Problem.ValidSchedule`, `Problem.scheduleCost`, `Problem.finalState`: offline/online trajectory
  validity, total cost, and terminal configuration.
* `Cslib.Algorithms.Lean.Online.DetStrategy`, `DetStrategy.ofHistory`: deterministic online
  strategies and prefix-history constructor.
* `DetStrategy.IsCompetitiveFrom`, `DetStrategy.IsCompetitive`, `DetStrategy.IsCompetitiveAnyInit`:
  competitive-ratio predicates with additive constants.
* `Problem.offlineSpec`, `DetStrategy.Exec`, `DetStrategy.realization`: embedding into
  `Cslib.Stateful` for potential-based competitive proofs.
* `DetStrategy.adaptiveRequestsFrom`, `DetStrategy.adaptiveRequests`: explicit adversarial request
  generation against a deterministic strategy.

## Main results

* `DetStrategy.validSchedule_states`, `DetStrategy.cost_eq_costFrom`: online strategies produce
  valid schedules evaluated in the common cost model.
* `DetStrategy.amortized_bound`, `DetStrategy.competitive_of_amortized`,
  `DetStrategy.competitiveAnyInit_of_amortized`: `Cslib.Stateful.Amortized` certificates imply
  competitive bounds.
* `DetStrategy.cost_adaptiveRequests_eq`: an adversary forcing per-step cost `w` at every reachable
  state forces total online cost `n * w` over `n` requests.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Online

open Cslib.Stateful

/-- An online request-serving problem with a common action and cost model for online strategies
and offline schedules. -/
structure Problem where
  /-- Observable configuration space shared by online and offline algorithms. -/
  State : Type
  /-- Request type arriving one item at a time. -/
  Req : Type
  /-- Admissible initial configurations. -/
  ValidInit : State → Prop
  /-- Admissible single-step transitions `s ↦ s'` serving request `r`. -/
  ValidStep : State → Req → State → Prop
  /-- Nonnegative integer cost charged for transition `s ↦ s'` on request `r`. -/
  stepCost : State → Req → State → Nat

namespace Problem

variable (P : Problem)

/-- A state trajectory `states` validly serves `reqs` starting from `s`. -/
@[expose]
def ValidSchedule (s : P.State) : List P.Req → List P.State → Prop
  | [], [] => True
  | r :: rs, s' :: ss => P.ValidStep s r s' ∧ ValidSchedule s' rs ss
  | _, _ => False

/-- Total step cost of a state trajectory `states` serving `reqs` starting from `s`. -/
@[expose]
def scheduleCost (s : P.State) : List P.Req → List P.State → Nat
  | [], [] => 0
  | r :: rs, s' :: ss => P.stepCost s r s' + scheduleCost s' rs ss
  | _, _ => 0

/-- Final configuration reached after traversing `states` from initial configuration `s`. -/
@[expose]
def finalState (s : P.State) : List P.State → P.State
  | [] => s
  | s' :: ss => finalState s' ss

@[simp]
theorem validSchedule_nil (s : P.State) : P.ValidSchedule s [] [] := trivial

@[simp]
theorem validSchedule_cons (s s' : P.State) (r : P.Req) (rs : List P.Req) (ss : List P.State) :
    P.ValidSchedule s (r :: rs) (s' :: ss) ↔ P.ValidStep s r s' ∧ P.ValidSchedule s' rs ss :=
  Iff.rfl

@[simp]
theorem scheduleCost_nil (s : P.State) : P.scheduleCost s [] [] = 0 := rfl

@[simp]
theorem scheduleCost_cons (s s' : P.State) (r : P.Req) (rs : List P.Req) (ss : List P.State) :
    P.scheduleCost s (r :: rs) (s' :: ss) = P.stepCost s r s' + P.scheduleCost s' rs ss := rfl

@[simp]
theorem finalState_nil (s : P.State) : P.finalState s [] = s := rfl

@[simp]
theorem finalState_cons (s s' : P.State) (ss : List P.State) :
    P.finalState s (s' :: ss) = P.finalState s' ss := rfl

/-- Concatenating two state trajectories composes `finalState`. -/
theorem finalState_append (s : P.State) (ss₁ ss₂ : List P.State) :
    P.finalState s (ss₁ ++ ss₂) = P.finalState (P.finalState s ss₁) ss₂ := by
  induction ss₁ generalizing s with
  | nil => rfl
  | cons s' ss₁ ih => exact ih s'

/-- Every valid schedule has one post-step configuration per request. -/
theorem ValidSchedule.length_eq {P : Problem} {s : P.State} {reqs : List P.Req}
    {states : List P.State} (h : P.ValidSchedule s reqs states) :
    states.length = reqs.length := by
  induction reqs generalizing s states with
  | nil =>
    cases states with
    | nil => rfl
    | cons _ _ => cases h
  | cons r rs ih =>
    cases states with
    | nil => cases h
    | cons s' ss =>
      simp only [List.length_cons, ih h.2]

/-- If every valid step lands in `P.ValidInit`, then `P.finalState` along any valid schedule from
an admissible initial state remains in `P.ValidInit`. -/
theorem validInit_finalState
    (hstep : ∀ {s r s'}, P.ValidInit s → P.ValidStep s r s' → P.ValidInit s')
    {s : P.State} {reqs : List P.Req} {states : List P.State}
    (hs : P.ValidInit s) (hv : P.ValidSchedule s reqs states) :
    P.ValidInit (P.finalState s states) := by
  induction reqs generalizing s states with
  | nil =>
    cases states with
    | nil => exact hs
    | cons _ _ => cases hv
  | cons _ _ ih =>
    cases states with
    | nil => cases hv
    | cons s' ss => exact @ih s' ss (hstep hs hv.1) hv.2

/-- Valid schedules compose sequentially when intermediate states match. -/
theorem validSchedule_append {s : P.State} {reqs₁ reqs₂ : List P.Req}
    {states₁ states₂ : List P.State}
    (h₁ : P.ValidSchedule s reqs₁ states₁)
    (h₂ : P.ValidSchedule (P.finalState s states₁) reqs₂ states₂) :
    P.ValidSchedule s (reqs₁ ++ reqs₂) (states₁ ++ states₂) := by
  induction reqs₁ generalizing s states₁ with
  | nil =>
    cases states₁ with
    | nil => exact h₂
    | cons _ _ => cases h₁
  | cons r rs ih =>
    cases states₁ with
    | nil => cases h₁
    | cons s' ss =>
      exact ⟨h₁.1, ih h₁.2 h₂⟩

/-- Schedule costs add across concatenated trajectories of matching lengths. -/
theorem scheduleCost_append {s : P.State} {reqs₁ reqs₂ : List P.Req}
    {states₁ states₂ : List P.State} (hlen : states₁.length = reqs₁.length) :
    P.scheduleCost s (reqs₁ ++ reqs₂) (states₁ ++ states₂) =
      P.scheduleCost s reqs₁ states₁ +
        P.scheduleCost (P.finalState s states₁) reqs₂ states₂ := by
  induction reqs₁ generalizing s states₁ with
  | nil =>
    cases states₁ with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases states₁ with
    | nil => simp at hlen
    | cons s' ss =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, scheduleCost_cons, finalState_cons, ih hlen, Nat.add_assoc]

/-- Stateful specification of valid offline transitions, used to attach `Cslib.Stateful.Amortized`
potential certificates between offline configurations and an online strategy's memory. -/
abbrev offlineSpec : Spec where
  State := P.State
  Op := P.Req × P.State
  Result _ := Unit
  step _ o := (o.2, ())
  valid s o := P.ValidStep s o.1 o.2

/-- Client program replaying a given request list and offline state trajectory in `offlineSpec`. -/
@[expose]
def scheduleClient : List P.Req → List P.State → P.offlineSpec.Client Unit
  | r :: rs, s' :: ss => .liftBind (r, s') fun _ => scheduleClient rs ss
  | _, _ => .pure ()

/-- Interpreting `scheduleClient` on a valid schedule reaches `finalState` and records the zipped
`(request, nextState)` history. -/
theorem runClient_scheduleClient {s : P.State} {reqs : List P.Req} {states : List P.State}
    (hv : P.ValidSchedule s reqs states) :
    P.offlineSpec.runClient s (P.scheduleClient reqs states) =
      ((), P.finalState s states, reqs.zip states) := by
  induction reqs generalizing s states with
  | nil =>
    cases states with
    | nil => rfl
    | cons _ _ => cases hv
  | cons r rs ih =>
    cases states with
    | nil => cases hv
    | cons s' ss =>
      change (let rest := P.offlineSpec.runClient s' (P.scheduleClient rs ss)
        (rest.1, rest.2.1, (r, s') :: rest.2.2)) = _
      rw [ih hv.2]
      rfl

/-- Every `ValidSchedule` yields an admissible `offlineSpec` operation history. -/
theorem validHistory_zip {s : P.State} {reqs : List P.Req} {states : List P.State}
    (hv : P.ValidSchedule s reqs states) :
    P.offlineSpec.ValidHistory s (reqs.zip states) := by
  induction reqs generalizing s states with
  | nil =>
    cases states with
    | nil => trivial
    | cons _ _ => cases hv
  | cons r rs ih =>
    cases states with
    | nil => cases hv
    | cons s' ss =>
      exact ⟨hv.1, ih hv.2⟩

/-- Weighted offline charges in `offlineSpec` equal `c * scheduleCost`. -/
theorem totalCost_zip (c : Nat) {s : P.State} {reqs : List P.Req} {states : List P.State}
    (hv : P.ValidSchedule s reqs states) :
    P.offlineSpec.totalCost (fun s₀ o => c * P.stepCost s₀ o.1 o.2) s (reqs.zip states) =
      c * P.scheduleCost s reqs states := by
  induction reqs generalizing s states with
  | nil =>
    cases states with
    | nil => rfl
    | cons _ _ => cases hv
  | cons r rs ih =>
    cases states with
    | nil => cases hv
    | cons s' ss =>
      change c * P.stepCost s r s' +
          P.offlineSpec.totalCost (fun s₀ o => c * P.stepCost s₀ o.1 o.2) s' (rs.zip ss) = _
      rw [ih hv.2]
      simp only [scheduleCost_cons, Nat.mul_add]

end Problem

/-- Explicit prefix-history memory for packaging a history-dependent online decision rule as a
`DetStrategy`. -/
structure HistoryMem (P : Problem) where
  /-- Initial configuration at the start of the request stream. -/
  initState : P.State
  /-- Requests observed so far in arrival order. -/
  history : List P.Req
  /-- Current observable configuration. -/
  curState : P.State

/-- A deterministic online strategy for `P`. Its transition `step` sees only its internal memory
`Mem` and the newly arrived request `P.Req`, never future requests, while projecting to valid
transitions of `P`. -/
structure DetStrategy (P : Problem) where
  /-- Internal controller memory maintained across requests. -/
  Mem : Type
  /-- Representation invariant preserved by `init` and `step`. -/
  ValidMem : Mem → Prop
  /-- Observable configuration in `P.State` corresponding to internal memory. -/
  project : Mem → P.State
  /-- Online initialization from an admissible initial state of `P`. -/
  init : P.State → Mem
  /-- Online transition consuming the current memory and arrived request. -/
  step : Mem → P.Req → Mem
  valid_init : ∀ {s₀}, P.ValidInit s₀ → ValidMem (init s₀) ∧ project (init s₀) = s₀
  valid_step : ∀ {m} (r : P.Req), ValidMem m →
    ValidMem (step m r) ∧ P.ValidStep (project m) r (project (step m r))

namespace DetStrategy

variable {P : Problem} (A : DetStrategy P)

/-- Package any prefix-dependent online decision function `next s₀ prefix curState r` that chooses
admissible transitions along reachable histories as a `DetStrategy`. -/
@[expose]
def ofHistory (next : P.State → List P.Req → P.State → P.Req → P.State)
    (hnext : ∀ {s₀ hist s} (r : P.Req), P.ValidInit s₀ →
      (∃ states, P.ValidSchedule s₀ hist states ∧ P.finalState s₀ states = s) →
      P.ValidStep s r (next s₀ hist s r)) : DetStrategy P where
  Mem := HistoryMem P
  ValidMem m :=
    P.ValidInit m.initState ∧
      ∃ states, P.ValidSchedule m.initState m.history states ∧
        P.finalState m.initState states = m.curState
  project m := m.curState
  init s₀ := ⟨s₀, [], s₀⟩
  step m r := ⟨m.initState, m.history ++ [r], next m.initState m.history m.curState r⟩
  valid_init hs₀ := ⟨⟨hs₀, [], trivial, rfl⟩, rfl⟩
  valid_step {m} r hm := by
    obtain ⟨hinit, states, hsched, hfin⟩ := hm
    have hstep : P.ValidStep m.curState r (next m.initState m.history m.curState r) :=
      hnext r hinit ⟨states, hsched, hfin⟩
    refine ⟨⟨hinit, states ++ [next m.initState m.history m.curState r], ?_, ?_⟩, hstep⟩
    · apply P.validSchedule_append hsched
      rw [hfin]
      exact ⟨hstep, trivial⟩
    · rw [P.finalState_append, hfin]
      rfl

/-- Evolve internal memory across a request list. -/
@[expose]
def runMem (m : A.Mem) : List P.Req → A.Mem
  | [] => m
  | r :: rs => runMem (A.step m r) rs

/-- Observable state trajectory produced starting from internal memory `m`. -/
@[expose]
def statesFrom (m : A.Mem) : List P.Req → List P.State
  | [] => []
  | r :: rs =>
    let m' := A.step m r
    A.project m' :: statesFrom m' rs

/-- Observable state trajectory produced from initial configuration `s₀`. -/
@[expose]
def states (s₀ : P.State) (reqs : List P.Req) : List P.State :=
  A.statesFrom (A.init s₀) reqs

/-- Total cost incurred starting from internal memory `m` on `reqs`. -/
@[expose]
def costFrom (m : A.Mem) (reqs : List P.Req) : Nat :=
  P.scheduleCost (A.project m) reqs (A.statesFrom m reqs)

/-- Total cost incurred starting from initial configuration `s₀` on `reqs`, evaluated in the same
`Problem.scheduleCost` model as offline schedules. -/
@[expose]
def cost (s₀ : P.State) (reqs : List P.Req) : Nat :=
  P.scheduleCost s₀ reqs (A.states s₀ reqs)

@[simp]
theorem runMem_nil (m : A.Mem) : A.runMem m [] = m := rfl

@[simp]
theorem runMem_cons (m : A.Mem) (r : P.Req) (rs : List P.Req) :
    A.runMem m (r :: rs) = A.runMem (A.step m r) rs := rfl

@[simp]
theorem statesFrom_nil (m : A.Mem) : A.statesFrom m [] = [] := rfl

@[simp]
theorem statesFrom_cons (m : A.Mem) (r : P.Req) (rs : List P.Req) :
    A.statesFrom m (r :: rs) = A.project (A.step m r) :: A.statesFrom (A.step m r) rs := rfl

@[simp]
theorem costFrom_nil (m : A.Mem) : A.costFrom m [] = 0 := rfl

@[simp]
theorem costFrom_cons (m : A.Mem) (r : P.Req) (rs : List P.Req) :
    A.costFrom m (r :: rs) =
      P.stepCost (A.project m) r (A.project (A.step m r)) + A.costFrom (A.step m r) rs := rfl

/-- Running `runMem` preserves `ValidMem`. -/
theorem validMem_runMem {m : A.Mem} (hm : A.ValidMem m) (reqs : List P.Req) :
    A.ValidMem (A.runMem m reqs) := by
  induction reqs generalizing m with
  | nil => exact hm
  | cons r rs ih => exact ih (A.valid_step r hm).1

/-- `statesFrom` always produces a `ValidSchedule` from `A.project m`. -/
theorem validSchedule_statesFrom {m : A.Mem} (hm : A.ValidMem m) (reqs : List P.Req) :
    P.ValidSchedule (A.project m) reqs (A.statesFrom m reqs) := by
  induction reqs generalizing m with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨hm', hstep⟩ := A.valid_step r hm
    exact ⟨hstep, ih hm'⟩

/-- From any admissible initial configuration `s₀`, `A.states s₀ reqs` is a `ValidSchedule`. -/
theorem validSchedule_states {s₀ : P.State} (hs₀ : P.ValidInit s₀) (reqs : List P.Req) :
    P.ValidSchedule s₀ reqs (A.states s₀ reqs) := by
  obtain ⟨hm₀, hproj⟩ := A.valid_init hs₀
  simpa only [states, hproj] using A.validSchedule_statesFrom hm₀ reqs

/-- From an admissible initial configuration `s₀`, `A.cost s₀ reqs` agrees with
`A.costFrom (A.init s₀) reqs`. -/
theorem cost_eq_costFrom {s₀ : P.State} (hs₀ : P.ValidInit s₀) (reqs : List P.Req) :
    A.cost s₀ reqs = A.costFrom (A.init s₀) reqs := by
  obtain ⟨_, hproj⟩ := A.valid_init hs₀
  simp only [cost, costFrom, states, hproj]

/-- `P.finalState` along `A.statesFrom m reqs` equals `A.project (A.runMem m reqs)`. -/
theorem finalState_statesFrom (m : A.Mem) (reqs : List P.Req) :
    P.finalState (A.project m) (A.statesFrom m reqs) = A.project (A.runMem m reqs) := by
  induction reqs generalizing m with
  | nil => rfl
  | cons r rs ih => exact ih (A.step m r)

/-! ### Competitive ratio predicates -/

/-- `A` is `(c, b)`-competitive from a fixed initial state `s₀` when its cost on every request
sequence is at most `c` times any valid offline schedule's cost from `s₀`, plus `b`. -/
@[expose]
def IsCompetitiveFrom (s₀ : P.State) (c b : Nat) : Prop :=
  ∀ reqs offStates, P.ValidSchedule s₀ reqs offStates →
    A.cost s₀ reqs ≤ c * P.scheduleCost s₀ reqs offStates + b

/-- `A` is `(c, b)`-competitive when it is `(c, b)`-competitive from every admissible initial
state `s₀` shared by the online and offline algorithms. -/
@[expose]
def IsCompetitive (c b : Nat) : Prop :=
  ∀ s₀, P.ValidInit s₀ → A.IsCompetitiveFrom s₀ c b

/-- `A` is `(c, b)`-competitive across arbitrary initial states when its cost from any admissible
`s₀` is at most `c` times any valid offline schedule's cost from any admissible `s_off`, plus
`b`. -/
@[expose]
def IsCompetitiveAnyInit (c b : Nat) : Prop :=
  ∀ s₀ s_off reqs offStates, P.ValidInit s₀ → P.ValidInit s_off →
    P.ValidSchedule s_off reqs offStates →
    A.cost s₀ reqs ≤ c * P.scheduleCost s_off reqs offStates + b

/-- Competitiveness across arbitrary initial states implies same-initial-state competitiveness. -/
theorem IsCompetitiveAnyInit.toIsCompetitive {A : DetStrategy P} {c b : Nat}
    (h : A.IsCompetitiveAnyInit c b) : A.IsCompetitive c b :=
  fun s₀ hs₀ reqs offStates hv => h s₀ s₀ reqs offStates hs₀ hs₀ hv

/-- Monotonicity of `IsCompetitive` in the competitive ratio `c` and additive constant `b`. -/
theorem IsCompetitive.mono {A : DetStrategy P} {c₁ c₂ b₁ b₂ : Nat}
    (hc : c₁ ≤ c₂) (hb : b₁ ≤ b₂) (h : A.IsCompetitive c₁ b₁) :
    A.IsCompetitive c₂ b₂ := by
  intro s₀ hs₀ reqs offStates hv
  calc
    A.cost s₀ reqs ≤ c₁ * P.scheduleCost s₀ reqs offStates + b₁ := h s₀ hs₀ reqs offStates hv
    _ ≤ c₂ * P.scheduleCost s₀ reqs offStates + b₂ :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hc) hb

/-! ### Potential method via `Cslib.Stateful.Amortized` -/

/-- Native step execution of `A` over `P.offlineSpec`: `A` steps using only the request `o.1`,
ignoring the offline target state `o.2`, and emits its single-step cost in `P`. -/
@[expose]
def Exec : Execution P.offlineSpec A.Mem Nat :=
  fun m o _ m' w =>
    m' = A.step m o.1 ∧ w = P.stepCost (A.project m) o.1 (A.project (A.step m o.1))

/-- Semantic realization pairing `P.offlineSpec` with online memory invariant `A.ValidMem`. -/
@[expose]
def realization : Realization P.offlineSpec A.Exec where
  rep _ m := A.ValidMem m
  total o _ _ := ⟨(), A.step _ o.1, _, rfl, rfl⟩
  correct hm _ he := by
    rcases he with ⟨rfl, -⟩
    exact ⟨rfl, (A.valid_step _ hm).1⟩

/-- Every valid offline schedule drives a concrete `Executes` trace of `A` whose summed trace
weights equal `A.costFrom m reqs`. -/
theorem exists_executes_scheduleClient (m : A.Mem) {s_off : P.State}
    {reqs : List P.Req} {offStates : List P.State} (hv : P.ValidSchedule s_off reqs offStates) :
    ∃ traces,
      Executes A.Exec (P.scheduleClient reqs offStates) m () (A.runMem m reqs) traces ∧
        total id traces = A.costFrom m reqs := by
  induction reqs generalizing m s_off offStates with
  | nil =>
    cases offStates with
    | nil => exact ⟨[], .pure () m, rfl⟩
    | cons _ _ => cases hv
  | cons r rs ih =>
    cases offStates with
    | nil => cases hv
    | cons s' ss =>
      obtain ⟨traces, hexec, htot⟩ := ih (A.step m r) hv.2
      refine ⟨P.stepCost (A.project m) r (A.project (A.step m r)) :: traces,
        .call (a := ()) ⟨rfl, rfl⟩ hexec, ?_⟩
      simp only [total_cons, id_eq, htot, costFrom_cons]

/-- Telescoping competitive potential bound derived directly from `Cslib.Stateful.Amortized.client`:
if `potential` satisfies the step inequality against `c * stepCost`, then `A.costFrom` plus final
potential is bounded by `c * P.scheduleCost` plus initial potential. -/
theorem amortized_bound {potential : P.State → A.Mem → Nat} {c : Nat}
    (Cert : Amortized A.realization id potential
      (fun s o => c * P.stepCost s o.1 o.2))
    {s_off : P.State} {m : A.Mem} {reqs : List P.Req} {offStates : List P.State}
    (hm : A.ValidMem m) (hv : P.ValidSchedule s_off reqs offStates) :
    A.costFrom m reqs + potential (P.finalState s_off offStates) (A.runMem m reqs) ≤
      c * P.scheduleCost s_off reqs offStates + potential s_off m := by
  obtain ⟨traces, hexec, htot⟩ := A.exists_executes_scheduleClient m hv
  have hrun := P.runClient_scheduleClient hv
  have hvh : P.offlineSpec.ValidHistory s_off
      (P.offlineSpec.runClient s_off (P.scheduleClient reqs offStates)).2.2 := by
    rw [hrun]
    exact P.validHistory_zip hv
  have hclient := Cert.client (s := s_off) hm hvh hexec
  rw [hrun] at hclient
  dsimp only at hclient
  rw [htot, P.totalCost_zip c hv] at hclient
  exact hclient

/-- A `Cslib.Stateful.Amortized` certificate whose initial potential on `(s₀, A.init s₀)` is at
most `b` establishes `A.IsCompetitive c b`. -/
theorem competitive_of_amortized {potential : P.State → A.Mem → Nat} {c b : Nat}
    (Cert : Amortized A.realization id potential
      (fun s o => c * P.stepCost s o.1 o.2))
    (hinit : ∀ s₀, P.ValidInit s₀ → potential s₀ (A.init s₀) ≤ b) :
    A.IsCompetitive c b := by
  intro s₀ hs₀ reqs offStates hv
  rw [A.cost_eq_costFrom hs₀]
  have hm₀ := (A.valid_init hs₀).1
  have hbound := A.amortized_bound Cert hm₀ hv
  have hb₀ := hinit s₀ hs₀
  omega

/-- A `Cslib.Stateful.Amortized` certificate whose initial potential on `(s_off, A.init s₀)` is at
most `b` across all admissible initial states establishes `A.IsCompetitiveAnyInit c b`. -/
theorem competitiveAnyInit_of_amortized {potential : P.State → A.Mem → Nat} {c b : Nat}
    (Cert : Amortized A.realization id potential
      (fun s o => c * P.stepCost s o.1 o.2))
    (hinit : ∀ s₀ s_off, P.ValidInit s₀ → P.ValidInit s_off → potential s_off (A.init s₀) ≤ b) :
    A.IsCompetitiveAnyInit c b := by
  intro s₀ s_off reqs offStates hs₀ hs_off hv
  rw [A.cost_eq_costFrom hs₀]
  have hm₀ := (A.valid_init hs₀).1
  have hbound := A.amortized_bound Cert hm₀ hv
  have hb₀ := hinit s₀ s_off hs₀ hs_off
  omega

/-! ### Explicit adversarial request generation -/

/-- Generate `n` requests step-by-step against `A` starting from internal memory `m`, choosing each
next request via `chooseReq (A.project m)` before advancing `A` on that request. -/
@[expose]
def adaptiveRequestsFrom (chooseReq : P.State → P.Req) (m : A.Mem) : Nat → List P.Req
  | 0 => []
  | n + 1 =>
    let r := chooseReq (A.project m)
    r :: adaptiveRequestsFrom chooseReq (A.step m r) n

/-- Generate `n` adversarial requests against `A` starting from initial configuration `s₀`. -/
@[expose]
def adaptiveRequests (chooseReq : P.State → P.Req) (s₀ : P.State) (n : Nat) : List P.Req :=
  A.adaptiveRequestsFrom chooseReq (A.init s₀) n

@[simp]
theorem adaptiveRequestsFrom_zero (chooseReq : P.State → P.Req) (m : A.Mem) :
    A.adaptiveRequestsFrom chooseReq m 0 = [] := rfl

@[simp]
theorem adaptiveRequestsFrom_succ (chooseReq : P.State → P.Req) (m : A.Mem) (n : Nat) :
    A.adaptiveRequestsFrom chooseReq m (n + 1) =
      chooseReq (A.project m) ::
        A.adaptiveRequestsFrom chooseReq (A.step m (chooseReq (A.project m))) n := rfl

@[simp]
theorem adaptiveRequestsFrom_length (chooseReq : P.State → P.Req) (m : A.Mem) (n : Nat) :
    (A.adaptiveRequestsFrom chooseReq m n).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => simp only [adaptiveRequestsFrom_succ, List.length_cons, ih]

@[simp]
theorem adaptiveRequests_length (chooseReq : P.State → P.Req) (s₀ : P.State) (n : Nat) :
    (A.adaptiveRequests chooseReq s₀ n).length = n :=
  A.adaptiveRequestsFrom_length chooseReq (A.init s₀) n

/-- Every request emitted by `adaptiveRequestsFrom` satisfies `Q` whenever `chooseReq` selects a
request satisfying `Q` on every reachable observable state. -/
theorem mem_adaptiveRequestsFrom {chooseReq : P.State → P.Req} {Q : P.Req → Prop}
    (hQ : ∀ {m}, A.ValidMem m → Q (chooseReq (A.project m)))
    {m : A.Mem} (hm : A.ValidMem m) {n : Nat} {r : P.Req}
    (hr : r ∈ A.adaptiveRequestsFrom chooseReq m n) : Q r := by
  induction n generalizing m with
  | zero => cases hr
  | succ n ih =>
    simp only [adaptiveRequestsFrom_succ, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hQ hm
    · exact ih (A.valid_step _ hm).1 hr

/-- Every request emitted by `adaptiveRequests` from an admissible `s₀` satisfies `Q` when
`chooseReq` preserves `Q` on reachable states. -/
theorem mem_adaptiveRequests {chooseReq : P.State → P.Req} {Q : P.Req → Prop}
    (hQ : ∀ {m}, A.ValidMem m → Q (chooseReq (A.project m)))
    {s₀ : P.State} (hs₀ : P.ValidInit s₀) {n : Nat} {r : P.Req}
    (hr : r ∈ A.adaptiveRequests chooseReq s₀ n) : Q r :=
  A.mem_adaptiveRequestsFrom hQ (A.valid_init hs₀).1 hr

/-- If `chooseReq` forces exact step cost `w` at every reachable state of `A`, then `n` generated
requests force exact online cost `n * w`. -/
theorem costFrom_adaptiveRequestsFrom_eq {chooseReq : P.State → P.Req} {w : Nat}
    (hw : ∀ {m}, A.ValidMem m →
      P.stepCost (A.project m) (chooseReq (A.project m))
        (A.project (A.step m (chooseReq (A.project m)))) = w)
    {m : A.Mem} (hm : A.ValidMem m) (n : Nat) :
    A.costFrom m (A.adaptiveRequestsFrom chooseReq m n) = n * w := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    simp only [adaptiveRequestsFrom_succ, costFrom_cons, hw hm,
      ih (A.valid_step _ hm).1, Nat.add_mul, Nat.one_mul, Nat.add_comm w]

/-- From an admissible initial state `s₀`, if `chooseReq` forces step cost `w` at every reachable
state, then `A.adaptiveRequests chooseReq s₀ n` has exact online cost `n * w`. -/
theorem cost_adaptiveRequests_eq {chooseReq : P.State → P.Req} {w : Nat}
    (hw : ∀ {m}, A.ValidMem m →
      P.stepCost (A.project m) (chooseReq (A.project m))
        (A.project (A.step m (chooseReq (A.project m)))) = w)
    {s₀ : P.State} (hs₀ : P.ValidInit s₀) (n : Nat) :
    A.cost s₀ (A.adaptiveRequests chooseReq s₀ n) = n * w := by
  rw [A.cost_eq_costFrom hs₀]
  exact A.costFrom_adaptiveRequestsFrom_eq hw (A.valid_init hs₀).1 n

end DetStrategy

end Cslib.Algorithms.Lean.Online
