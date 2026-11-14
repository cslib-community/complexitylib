/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.PIR.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Client-preprocessing single-server private information retrieval

In the client-preprocessing (subscription) model of single-server private information retrieval
[Zhou, Park, Zheng and Shi, Section 3.1][ZhouParkZhengShi2024], interaction is split into two
phases:

* **Offline setup** (`Scheme.preprocess`): the client streams the database `x : ι → Bool` once and
  stores a local hint state `h : H`.
* **Online queries** (`Scheme.query`, `Scheme.answer`, `Scheme.reconstruct`, `Scheme.refresh`): on
  each queried index `i : ι`, the client uses its current hint state `h` to generate a retained
  per-query state `r : R` and a query message `q : Q` for the server, reconstructs the bit `β` from
  `r` and the server's answer `Scheme.answer x q`, and refreshes its hint state `h` using `r` and
  `β` so that subsequent queries can be answered without skewing the hint distribution.

`Scheme.runQueries x is` executes the offline setup followed by a sequence of online queries
`is : List ι` and returns the list of reconstructed database bits. `Scheme.IsCorrect` requires
`Scheme.runQueries x is` to output `is.map x` with probability one for every database and query
sequence; `Scheme.IsCorrectFrom x h is` is the conditional form starting from a given hint state
`h`.

Privacy follows [Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024]: an adversarial
server `adv : AdaptiveServer ι Q A St` adaptively chooses each online query index `i_t ∈ ι` for the
client based on its view so far, receives the client's query message `q_t : Q`, and returns a
(possibly malicious) server response `a_t : A` that the client uses when reconstructing and
refreshing its state (`Scheme.realAdaptiveView`). In the ideal experiment (`idealAdaptiveView`), a
simulator `sim : ProbComp Q` generates each query message `q_t` without receiving the queried index
`i_t` or the database `x`. `Scheme.IsPerfectlyPrivateWith sim` requires the adversarial server's
final state distribution in the real and ideal experiments to be identical for every number of
queries `k`, database `x`, and adaptive server `adv`; `Scheme.privacyAdvantage` measures the
distinguishing advantage of an adaptive server with state `St` and a Boolean finalizer
`finalize : St → Bool`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme`: stateful client-preprocessing single-server
  PIR schemes.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.onlineCommunication`: per-query online communication
  cost in bits.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.step`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.runQueriesFrom`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.runQueries`: single-query and multi-query
  execution.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.IsCorrectFrom`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.IsCorrect`: multi-query correctness.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.AdaptiveServer`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.realAdaptiveView`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.idealAdaptiveView`: the real and ideal adaptive-server
  experiments of Definition 3.1.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.IsPerfectlyPrivateWith`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.IsPerfectlyPrivate`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.privacyAdvantage`: perfect and concrete privacy.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.queryTranscript`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.simTranscript`: non-adaptive server query transcripts.

## Main results

* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.isCorrectFrom_iff`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.isCorrect_iff`: support characterizations of
  multi-query correctness.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.IsPerfectlyPrivateWith.privacyAdvantage_eq_zero`:
  perfect privacy implies zero distinguishing advantage.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme.isPerfectlyPrivateWith_of_invariant`:
  state-invariance criterion for multi-query adaptive privacy (abstracting Lemma C.2 of
  [Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]).

## References

* [M. Zhou, A. Park, W. Zheng, E. Shi, *Piano: Extremely Simple, Single-Server PIR with Sublinear
  Server Computation*][ZhouParkZhengShi2024], Section 3.1 (Definition 3.1) and Appendix C
  (source locators follow the full ePrint version, where the author order is Zhou, Park, Shi, Zheng)
-/

public section

namespace Cslib.Crypto.Protocols.PIR.Preprocessing

open Probability
open scoped NNReal

/-- A client-preprocessing single-server private information retrieval scheme for databases
`x : ι → Bool`, with client hint state `H`, per-query retained state `R`, query message `Q`, and
server answer `A` [Zhou, Park, Zheng and Shi, Section 3.1][ZhouParkZhengShi2024]. -/
structure Scheme (ι H R Q A : Type) where
  /-- Offline setup phase: streams the database `x` and initializes the client's local hint
  state. -/
  preprocess : (ι → Bool) → ProbComp H
  /-- Online query phase: given the current hint state and target index, produces a per-query
  retained state and the query sent to the server. -/
  query : H → ι → ProbComp (R × Q)
  /-- Deterministic server answer on database `x` and query `q`. -/
  answer : (ι → Bool) → Q → A
  /-- Client reconstruction of the target database bit from the retained state and server answer. -/
  reconstruct : R → A → Bool
  /-- Client hint refresh: updates the persistent hint state using the queried index, retained
  per-query state, and reconstructed answer bit. -/
  refresh : H → ι → R → Bool → ProbComp H

/-- The per-query online communication cost of a single-server preprocessing scheme with queries `Q`
and answers `A`: `⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉`, specializing `PIR.communication Unit Q A`. -/
@[expose] def onlineCommunication (Q A : Type) [Fintype Q] [Fintype A] : ℕ :=
  PIR.communication Unit Q A

theorem onlineCommunication_eq (Q A : Type) [Fintype Q] [Fintype A] :
    onlineCommunication Q A = Nat.clog 2 (Fintype.card Q) + Nat.clog 2 (Fintype.card A) := by
  rw [onlineCommunication, PIR.communication_eq, Fintype.card_unit, one_mul]

/-- With one-bit (`Bool`) answers, each online query communicates `⌈log₂ |Q|⌉ + 1` bits. -/
theorem onlineCommunication_bool (Q : Type) [Fintype Q] :
    onlineCommunication Q Bool = Nat.clog 2 (Fintype.card Q) + 1 := by
  rw [onlineCommunication_eq, Fintype.card_bool, Nat.clog_eq_one le_rfl le_rfl]

/-- An adaptive (and potentially malicious) server in the privacy experiment of
[Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024]: at each online step, the server
may adaptively choose the next query index `i ∈ ι` from its internal state `St`, and upon receiving
the client's query `q : Q`, updates its state and returns a (possibly deviated) response `a : A`. -/
structure AdaptiveServer (ι Q A St : Type) where
  /-- Adaptively chooses the next query index `i ∈ ι` for the client. -/
  chooseQuery : St → ProbComp (St × ι)
  /-- Processes the client's query message `q : Q` and chooses a server response `a : A`. -/
  onQuery : St → Q → ProbComp (St × A)

/-- One online step of the ideal privacy experiment
[Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024]: the adversarial server chooses
the next query index (which is discarded), the simulator `sim` generates a query `q` without
receiving the index, and the server updates its state on `q`. -/
@[expose] def idealAdaptiveStep {ι Q A St : Type} (sim : ProbComp Q) (adv : AdaptiveServer ι Q A St)
    (st : St) : ProbComp St := do
  let (st₁, _) ← adv.chooseQuery st
  let q ← sim
  let (st₂, _) ← adv.onQuery st₁ q
  pure st₂

/-- The `k`-query ideal privacy experiment
[Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024] with index-independent simulator
`sim : ProbComp Q`. -/
@[expose] def idealAdaptiveView {ι Q A St : Type} (sim : ProbComp Q)
    (adv : AdaptiveServer ι Q A St) : ℕ → St → ProbComp St
  | 0, st => pure st
  | k + 1, st => do
    let st' ← idealAdaptiveStep sim adv st
    idealAdaptiveView sim adv k st'

/-- The `k`-query non-adaptive simulated transcript: `k` independent draws from `sim`. -/
@[expose] def simTranscript {Q : Type} (sim : ProbComp Q) : ℕ → ProbComp (List Q)
  | 0 => pure []
  | k + 1 => do
    let q ← sim
    let qs ← simTranscript sim k
    pure (q :: qs)

/-- Iterates a projected state transition `stepS : S → St → PMF (S × St)` for `k` steps, returning
the final server state distribution. -/
private noncomputable def runProjectedSteps {S St : Type} (stepS : S → St → PMF (S × St)) :
    ℕ → S → St → PMF St
  | 0, _, st => PMF.pure st
  | k + 1, s, st => (stepS s st).bind (fun p => runProjectedSteps stepS k p.1 p.2)

namespace Scheme

variable {ι H R Q A : Type}

/-! ### Online execution and multi-query correctness -/

/-- One honest online query-answer-reconstruct-refresh step on database `x`, hint state `h`, and
index `i`, returning the refreshed hint state and the reconstructed bit. -/
@[expose] def step (P : Scheme ι H R Q A) (x : ι → Bool) (h : H) (i : ι) : ProbComp (H × Bool) := do
  let (r, q) ← P.query h i
  let β := P.reconstruct r (P.answer x q)
  let h' ← P.refresh h i r β
  pure (h', β)

/-- Executes a sequence of online queries `is : List ι` starting from hint state `h`, threading the
refreshed hint state across queries and collecting the reconstructed bits. -/
@[expose] def runQueriesFrom (P : Scheme ι H R Q A) (x : ι → Bool) :
    H → List ι → ProbComp (H × List Bool)
  | h, [] => pure (h, [])
  | h, i :: is => do
    let (h', β) ← P.step x h i
    let (h'', βs) ← P.runQueriesFrom x h' is
    pure (h'', β :: βs)

/-- Full execution of the preprocessing PIR scheme on database `x` and online query sequence `is`:
runs `preprocess x` once followed by `runQueriesFrom x h is`. -/
@[expose] def runQueries (P : Scheme ι H R Q A) (x : ι → Bool) (is : List ι) :
    ProbComp (List Bool) := do
  let h ← P.preprocess x
  let (_, βs) ← P.runQueriesFrom x h is
  pure βs

/-- Conditional multi-query correctness from a hint state `h` on database `x` and query list `is`:
the reconstructed answer list equals `is.map x` with probability one. -/
@[expose] def IsCorrectFrom (P : Scheme ι H R Q A) (x : ι → Bool) (h : H) (is : List ι) : Prop :=
  ProbComp.eval (Prod.snd <$> P.runQueriesFrom x h is) = PMF.pure (is.map x)

/-- Unconditional multi-query correctness: for every database `x` and query sequence `is`,
`P.runQueries x is` outputs `is.map x` with probability one. -/
@[expose] def IsCorrect (P : Scheme ι H R Q A) : Prop :=
  ∀ x is, ProbComp.eval (P.runQueries x is) = PMF.pure (is.map x)

theorem isCorrectFrom_nil (P : Scheme ι H R Q A) (x : ι → Bool) (h : H) :
    P.IsCorrectFrom x h [] := by
  simp [IsCorrectFrom, runQueriesFrom]

/-- `IsCorrectFrom` holds exactly when every execution in the support of `runQueriesFrom` outputs
the exact database bits `is.map x`. -/
theorem isCorrectFrom_iff (P : Scheme ι H R Q A) (x : ι → Bool) (h : H) (is : List ι) :
    P.IsCorrectFrom x h is ↔
      ∀ h' βs, (h', βs) ∈ (ProbComp.eval (P.runQueriesFrom x h is)).support →
        βs = is.map x := by
  rw [IsCorrectFrom, ProbComp.eval_map]
  constructor
  · intro heq h' βs hmem
    have hmap : βs ∈ ((ProbComp.eval (P.runQueriesFrom x h is)).map Prod.snd).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨(h', βs), hmem, rfl⟩
    rwa [heq, PMF.support_pure, Set.mem_singleton_iff] at hmap
  · intro hsupp
    rw [Cslib.Probability.PMF.map_congr_on_support _ _ (Function.const _ (is.map x))
      fun p hp => hsupp p.1 p.2 hp, PMF.map_const]

theorem isCorrectFrom_cons {P : Scheme ι H R Q A} {x : ι → Bool} {h : H} {i : ι} {is : List ι}
    (hstep : ∀ h' β, (h', β) ∈ (ProbComp.eval (P.step x h i)).support →
      β = x i ∧ P.IsCorrectFrom x h' is) :
    P.IsCorrectFrom x h (i :: is) := by
  rw [isCorrectFrom_iff]
  intro h'' βs hmem
  simp only [runQueriesFrom, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
  obtain ⟨⟨h', β⟩, hmem₁, ⟨h₃, βs'⟩, hmem₂, -, rfl⟩ := hmem
  obtain ⟨rfl, htail⟩ := hstep h' β hmem₁
  have htail_eq := (P.isCorrectFrom_iff x h' is).mp htail h₃ βs' hmem₂
  simp [htail_eq]

/-- `IsCorrect` holds when every initial hint state in the support of `preprocess x` satisfies
`IsCorrectFrom x h is`. -/
theorem isCorrect_of_forall_preprocess {P : Scheme ι H R Q A}
    (h : ∀ x is h₀, h₀ ∈ (ProbComp.eval (P.preprocess x)).support → P.IsCorrectFrom x h₀ is) :
    P.IsCorrect := by
  intro x is
  have hrun : ProbComp.eval (P.runQueries x is) =
      (ProbComp.eval (P.preprocess x)).bind
        (fun h₀ => ProbComp.eval (Prod.snd <$> P.runQueriesFrom x h₀ is)) := by
    simp only [runQueries, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map]
    rfl
  rw [hrun, Cslib.Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (is.map x)) (h x is),
    PMF.bind_const]

theorem isCorrect_iff (P : Scheme ι H R Q A) :
    P.IsCorrect ↔ ∀ x is βs, βs ∈ (ProbComp.eval (P.runQueries x is)).support →
      βs = is.map x := by
  refine forall_congr' fun x => forall_congr' fun is => ?_
  constructor
  · intro heq βs hmem
    rwa [heq, PMF.support_pure, Set.mem_singleton_iff] at hmem
  · intro hsupp
    have hmap := Cslib.Probability.PMF.map_congr_on_support
      (ProbComp.eval (P.runQueries x is)) id (Function.const _ (is.map x)) hsupp
    simpa only [PMF.map_id, PMF.map_const] using hmap

/-! ### Non-adaptive server query transcripts -/

/-- One online step recording the refreshed hint state and the query `q : Q` sent to the server. -/
@[expose] def queryStep (P : Scheme ι H R Q A) (x : ι → Bool) (h : H) (i : ι) :
    ProbComp (H × Q) := do
  let (r, q) ← P.query h i
  let β := P.reconstruct r (P.answer x q)
  let h' ← P.refresh h i r β
  pure (h', q)

/-- The sequence of queries sent to the server over `is : List ι` starting from hint state `h`. -/
@[expose] def queryTranscriptFrom (P : Scheme ι H R Q A) (x : ι → Bool) :
    H → List ι → ProbComp (List Q)
  | _, [] => pure []
  | h, i :: is => do
    let (h', q) ← P.queryStep x h i
    let qs ← P.queryTranscriptFrom x h' is
    pure (q :: qs)

/-- The full sequence of online queries sent to the server on database `x` and query list `is`. -/
@[expose] def queryTranscript (P : Scheme ι H R Q A) (x : ι → Bool) (is : List ι) :
    ProbComp (List Q) := do
  let h ← P.preprocess x
  P.queryTranscriptFrom x h is

/-! ### Adaptive malicious-server privacy (Definition 3.1) -/

/-- One online step of the real privacy experiment
[Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024]: the adversarial server chooses
the next query index `i`, the honest client produces query `q`, the server responds with `a`, and
the client refreshes its hint state using the reconstructed bit `P.reconstruct r a`. -/
@[expose] def realAdaptiveStep {St : Type} (P : Scheme ι H R Q A) (adv : AdaptiveServer ι Q A St)
    (h : H) (st : St) : ProbComp (H × St) := do
  let (st₁, i) ← adv.chooseQuery st
  let (r, q) ← P.query h i
  let (st₂, a) ← adv.onQuery st₁ q
  let h' ← P.refresh h i r (P.reconstruct r a)
  pure (h', st₂)

/-- Runs `k` online steps of the real privacy experiment starting from client hint state `h` and
adversarial server state `st`. -/
@[expose] def realAdaptiveFrom {St : Type} (P : Scheme ι H R Q A) (adv : AdaptiveServer ι Q A St) :
    ℕ → H → St → ProbComp St
  | 0, _, st => pure st
  | k + 1, h, st => do
    let (h', st') ← P.realAdaptiveStep adv h st
    P.realAdaptiveFrom adv k h' st'

/-- The full real privacy experiment of
[Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024]: the client runs `P.preprocess x`
and then interacts with `adv` over `k` adaptive online queries. -/
@[expose] def realAdaptiveView {St : Type} (P : Scheme ι H R Q A) (adv : AdaptiveServer ι Q A St)
    (x : ι → Bool) (k : ℕ) (st₀ : St) : ProbComp St := do
  let h ← P.preprocess x
  P.realAdaptiveFrom adv k h st₀

/-- Perfect privacy with simulator `sim : ProbComp Q`
([Zhou, Park, Zheng and Shi, Definition 3.1][ZhouParkZhengShi2024] with zero distinguishing error):
for every state type `St`, adaptive server `adv`, database `x`, query count `k`, and initial server
state `st₀`, the server's final view in `realAdaptiveView` has the exact same distribution as in
`idealAdaptiveView sim`. -/
@[expose] def IsPerfectlyPrivateWith (P : Scheme ι H R Q A) (sim : ProbComp Q) : Prop :=
  ∀ (St : Type) (adv : AdaptiveServer ι Q A St) (x : ι → Bool) (k : ℕ) (st₀ : St),
    ProbComp.eval (P.realAdaptiveView adv x k st₀) =
      ProbComp.eval (idealAdaptiveView sim adv k st₀)

/-- Perfect privacy: some index-independent simulator `sim : ProbComp Q` perfectly simulates the
client in `realAdaptiveView`. -/
@[expose] def IsPerfectlyPrivate (P : Scheme ι H R Q A) : Prop :=
  ∃ sim : ProbComp Q, P.IsPerfectlyPrivateWith sim

/-- The distinguishing advantage of an adaptive server `adv : AdaptiveServer ι Q A St` with Boolean
finalizer `finalize : St → Bool` between the real privacy experiment and the ideal experiment with
simulator `sim`. -/
@[expose] noncomputable def privacyAdvantage {St : Type} (P : Scheme ι H R Q A) (sim : ProbComp Q)
    (adv : AdaptiveServer ι Q A St) (finalize : St → Bool) (x : ι → Bool) (k : ℕ)
    (st₀ : St) : ℝ≥0 :=
  Game.advantage ((ProbComp.eval (P.realAdaptiveView adv x k st₀)).map finalize)
    ((ProbComp.eval (idealAdaptiveView sim adv k st₀)).map finalize)

theorem IsPerfectlyPrivateWith.isPerfectlyPrivate {P : Scheme ι H R Q A} {sim : ProbComp Q}
    (h : P.IsPerfectlyPrivateWith sim) : P.IsPerfectlyPrivate :=
  ⟨sim, h⟩

/-- A scheme that is perfectly private with simulator `sim` has zero privacy advantage against every
adaptive server and Boolean finalizer `finalize : St → Bool`. -/
theorem IsPerfectlyPrivateWith.privacyAdvantage_eq_zero {St : Type} {P : Scheme ι H R Q A}
    {sim : ProbComp Q} (h : P.IsPerfectlyPrivateWith sim) (adv : AdaptiveServer ι Q A St)
    (finalize : St → Bool) (x : ι → Bool) (k : ℕ) (st₀ : St) :
    P.privacyAdvantage sim adv finalize x k st₀ = 0 := by
  rw [privacyAdvantage, h St adv x k st₀, Game.advantage_self]

/-! ### State-invariance criterion for multi-query adaptive privacy -/

/-- **State-invariance criterion for adaptive privacy** (abstracting Lemma C.2 of
[Zhou, Park, Zheng and Shi, Appendix C][ZhouParkZhengShi2024]): suppose a projection `proj : H → S`
of the client's hint state controls all online query distributions:

1. For every database `x`, `proj <$> P.preprocess x` has distribution `inv : PMF S`.
2. Whenever `h₁` and `h₂` have the same projection (`proj h₁ = proj h₂`), one step of
   `realAdaptiveStep` maps `(proj h, st)` identically.
3. Starting from `s ∼ inv`, for every adaptive server `adv`, running one online step produces
   `(s', st₂)` with the same distribution as running `idealAdaptiveStep sim adv st` and
   independently drawing `s' ∼ inv`.

Then `P` is perfectly private with simulator `sim` across any number of adaptive queries `k`. -/
theorem isPerfectlyPrivateWith_of_invariant {P : Scheme ι H R Q A} {S : Type} (proj : H → S)
    (inv : PMF S) (sim : ProbComp Q)
    (stepS : ∀ {St : Type}, AdaptiveServer ι Q A St → S → St → PMF (S × St))
    (hinit : ∀ x, (ProbComp.eval (P.preprocess x)).map proj = inv)
    (hcompat : ∀ {St : Type} (adv : AdaptiveServer ι Q A St) (h : H) (st : St),
      (ProbComp.eval (P.realAdaptiveStep adv h st)).map (Prod.map proj id) =
        stepS adv (proj h) st)
    (hstep : ∀ {St : Type} (adv : AdaptiveServer ι Q A St) (st : St) (kCont : S → St → PMF St),
      inv.bind (fun s => (stepS adv s st).bind (fun p => kCont p.1 p.2)) =
        (ProbComp.eval (idealAdaptiveStep sim adv st)).bind
          (fun st' => inv.bind (fun s' => kCont s' st')))
    : P.IsPerfectlyPrivateWith sim := by
  intro St adv x k st₀
  have hrunS : ∀ (m : ℕ) (h : H) (st : St),
      ProbComp.eval (P.realAdaptiveFrom adv m h st) =
        runProjectedSteps (stepS adv) m (proj h) st := by
    intro m
    induction m with
    | zero =>
      intro h st
      dsimp only [runProjectedSteps]
      simp [realAdaptiveFrom]
    | succ m ih =>
      intro h st
      dsimp only [runProjectedSteps]
      simp only [realAdaptiveFrom, ProbComp.eval_bind]
      rw [← hcompat adv h st, PMF.bind_map]
      congr 1
      funext p
      exact ih p.1 p.2
  have hideal : ∀ (m : ℕ) (st : St),
      inv.bind (fun s => runProjectedSteps (stepS adv) m s st) =
        ProbComp.eval (idealAdaptiveView sim adv m st) := by
    intro m
    induction m with
    | zero =>
      intro st
      dsimp only [runProjectedSteps]
      simp [idealAdaptiveView]
    | succ m ih =>
      intro st
      dsimp only [runProjectedSteps]
      simp only [idealAdaptiveView, ProbComp.eval_bind]
      rw [hstep adv st (runProjectedSteps (stepS adv) m)]
      congr 1
      funext st'
      exact ih st'
  simp only [realAdaptiveView, ProbComp.eval_bind, hrunS]
  have hbind : ((ProbComp.eval (P.preprocess x)).bind
      fun h => runProjectedSteps (stepS adv) k (proj h) st₀) =
      ((ProbComp.eval (P.preprocess x)).map proj).bind
        (fun s => runProjectedSteps (stepS adv) k s st₀) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, hinit x, hideal k st₀]

/-- Iterates a projected non-adaptive query step `stepQ : S → ι → PMF (S × Q)` over a query list
`is : List ι`. -/
private noncomputable def runProjectedTranscript {S : Type} (stepQ : S → ι → PMF (S × Q)) :
    S → List ι → PMF (List Q)
  | _, [] => PMF.pure []
  | s, i :: is =>
    (stepQ s i).bind (fun p => (runProjectedTranscript stepQ p.1 is).map (p.2 :: ·))

/-- **State-invariance criterion for non-adaptive query transcripts**: under the same projection
and invariance conditions, the non-adaptive server query transcript `P.queryTranscript x is` has
the exact distribution of `is.length` independent draws from `sim`, independent of the database `x`
and query sequence `is`. -/
theorem eval_queryTranscript_eq_of_invariant {P : Scheme ι H R Q A} {S : Type} (proj : H → S)
    (inv : PMF S) (sim : ProbComp Q) (stepQ : S → ι → PMF (S × Q)) (x : ι → Bool)
    (hinit : (ProbComp.eval (P.preprocess x)).map proj = inv)
    (hcompat : ∀ (h : H) (i : ι),
      (ProbComp.eval (P.queryStep x h i)).map (Prod.map proj id) = stepQ (proj h) i)
    (hstep : ∀ (i : ι) (kCont : S → Q → PMF (List Q)),
      inv.bind (fun s => (stepQ s i).bind (fun p => kCont p.1 p.2)) =
        (ProbComp.eval sim).bind (fun q => inv.bind (fun s' => kCont s' q)))
    (is : List ι) :
    ProbComp.eval (P.queryTranscript x is) = ProbComp.eval (simTranscript sim is.length) := by
  have hrunQ : ∀ (js : List ι) (h : H),
      ProbComp.eval (P.queryTranscriptFrom x h js) =
        runProjectedTranscript stepQ (proj h) js := by
    intro js
    induction js with
    | nil =>
      intro h
      dsimp only [runProjectedTranscript]
      simp [queryTranscriptFrom]
    | cons j js ih =>
      intro h
      dsimp only [runProjectedTranscript]
      simp only [queryTranscriptFrom, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map]
      rw [← hcompat h j, PMF.bind_map]
      congr 1
      funext p
      rw [ih p.1]
      rfl
  have hideal : ∀ (js : List ι),
      inv.bind (fun s => runProjectedTranscript stepQ s js) =
        ProbComp.eval (simTranscript sim js.length) := by
    intro js
    induction js with
    | nil =>
      dsimp only [runProjectedTranscript]
      simp [simTranscript]
    | cons j js ih =>
      dsimp only [runProjectedTranscript]
      simp only [List.length_cons, simTranscript, ProbComp.eval_bind, ProbComp.eval_pure]
      rw [hstep j (fun s' q => (runProjectedTranscript stepQ s' js).map (q :: ·))]
      congr 1
      funext q
      rw [← PMF.map_bind, ih]
      rfl
  simp only [queryTranscript, ProbComp.eval_bind, hrunQ]
  have hbind : ((ProbComp.eval (P.preprocess x)).bind
      fun h => runProjectedTranscript stepQ (proj h) is) =
      ((ProbComp.eval (P.preprocess x)).map proj).bind
        (fun s => runProjectedTranscript stepQ s is) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, hinit, hideal is]

end Scheme

end Cslib.Crypto.Protocols.PIR.Preprocessing
