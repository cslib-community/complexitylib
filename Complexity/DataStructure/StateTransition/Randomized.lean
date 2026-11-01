/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Refinement
public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect

/-!
# Distributional refinements of randomized specifications

A `RandomizedSpec` is a state-transition specification whose operations draw their outcome from a
distribution: `law o` is a stateful `PMF` handler. A client runs against it by
`OracleComp.interpret`, and `RandomizedSpec.run` is the joint distribution of its result and
final state. Its support is a relational `StateTransitionSpec` (`RandomizedSpec.toSpec`), and a
deterministic specification is a randomized one with point-mass outcomes
(`StateTransitionSpec.toRandomized`). An implementation that flips coins calls `E.withCoins`, the
interface `E` beside uniform sampling, whose clients are the `ProbOracleComp E.Result` programs.

A `RandomizedRefinement D F` extends a relational `Refinement` of the supports with one
distributional obligation. From a state satisfying the invariant, each admissible method's joint
distribution of answer and abstracted final state is the specified law (`law`). The relational
part then supplies the implementation invariant, the admissibility of lower calls and pathwise
amortized costs (`Refinement.Amortized` of `toRefinement`), and the law lifts to every adaptive
client (`RandomizedRefinement.run_link`). All probability is then done on the specification.
States, operations and answers live in `Type`, as for `ProbOracleComp` and
`OracleComp.IdenticalUntilBad`.

Failure events take one more step. If the real methods agree with exact ones until a bad lower
state (`OracleComp.IdenticalUntilBad`), any experiment on the real client accepts at most as often
as on the specification, plus the probability of the bad event
(`RandomizedRefinement.bind_apply_le_of_identicalUntilBad`). `OracleComp.toOuterMeasure_bad_le`
bounds that probability by per-call charges.

Expected costs go through charges as well. `RandomizedSpec.expectedCost` is the expected total
charge of a client. A `RandomizedRefinement.ExpectedAmortized` certificate bounds each method's
expected lower cost plus expected final potential by the upper charge plus the initial potential;
it telescopes along adaptive clients (`ExpectedAmortized.client`) and stacks across composition
(`ExpectedAmortized.comp`). When charges do not depend on the state, a query budget
(`OracleComp.IsCostBounded`) bounds the expected cost (`expectedCost_le_of_isCostBounded`).

## Main definitions

* `RandomizedSpec`, `RandomizedSpec.run`: randomized specifications and the law of a client run.
* `RandomizedSpec.toSpec`: the relational support.
* `StateTransitionSpec.toRandomized`: a deterministic specification as a randomized one.
* `RandomizedSpec.withCoins`: an interface together with private uniform coins.
* `RandomizedSpec.obliviousClient`: issue a fixed list of operations and record the transcript.
* `RandomizedRefinement`, `RandomizedRefinement.ofLaw`: distributional refinements, and the
  constructor that derives the relational step from the law.
* `RandomizedRefinement.comp`: composition.
* `RandomizedRefinement.handler`: the methods as a stateful handler on lower states.
* `RandomizedSpec.expectedCost`, `RandomizedRefinement.ExpectedAmortized`: expected charges and
  expected amortized cost refinements.

## Main results

* `RandomizedSpec.mem_support_run_of_clientRun`, `RandomizedSpec.exists_clientRun_of_mem_support`:
  the support of a run consists of the relational runs.
* `StateTransitionSpec.run_toRandomized`, `StateTransitionSpec.toRandomized_step_iff`: a
  deterministic run is a point mass, and the support of a deterministic specification is itself.
* `RandomizedSpec.demonicValid_liftRight`, `RandomizedSpec.demonicValid_sample_bind`: coin calls
  are admissible, and programs over `E` keep their admissibility.
* `RandomizedSpec.expectedCost_bind`, `RandomizedSpec.expectedCost_le_of_isCostBounded`,
  `RandomizedSpec.isCostBounded_obliviousClient`: expected charges of sequenced programs, and
  query budgets.
* `RandomizedRefinement.run_link`: the law of a linked client, read through the abstraction, is
  the law of the client on the specification.
* `RandomizedRefinement.inv_of_mem_support_link`: the invariant holds on every outcome.
* `RandomizedRefinement.bind_apply_le_of_identicalUntilBad`,
  `RandomizedRefinement.abs_sub_le_of_identicalUntilBad`: the identical-until-bad step.
* `RandomizedRefinement.ExpectedAmortized.client`, `RandomizedRefinement.ExpectedAmortized.comp`,
  `RandomizedRefinement.ExpectedAmortized.of_isCostBounded`: expected amortized costs.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7.
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure

open scoped ENNReal

/-- A randomized specification: from each state, an operation draws its answer and next state
from the distribution `law o`. Admissibility `valid` constrains only refinement certificates. -/
structure RandomizedSpec where
  /-- Mathematical states. -/
  State : Type
  /-- Operations available to clients. -/
  Op : Type
  /-- The answer type of each operation. -/
  Result : Op → Type
  /-- The distribution of the answer and the next state of each operation. -/
  law : (o : Op) → StateT State PMF (Result o)
  /-- Preconditions under which an implementation must realize an operation. -/
  valid : State → Op → Prop := fun _ _ => True

namespace RandomizedSpec

variable (D : RandomizedSpec) {α β : Type}

/-- The support of a randomized specification as a relational specification: a step is permitted
when the law gives it positive probability. -/
abbrev toSpec : StateTransitionSpec.{0, 0, 0} where
  State := D.State
  Op := D.Op
  Result := D.Result
  step s o s' a := (a, s') ∈ (D.law o s).support
  valid := D.valid

/-- The joint distribution of the result and the final state of a client run from `s`. -/
noncomputable abbrev run (p : OracleComp D.Result α) (s : D.State) : PMF (α × D.State) :=
  (OracleComp.interpret D.law p).run s

@[simp] theorem run_pure (a : α) (s : D.State) : D.run (pure a) s = PMF.pure (a, s) := rfl

/-- A call followed by a continuation draws the call's outcome, then runs the continuation. -/
theorem run_liftBind (o : D.Op) (k : D.Result o → OracleComp D.Result α) (s : D.State) :
    D.run (.liftBind o k) s = (D.law o s).bind fun (a, s') => D.run (k a) s' := rfl

/-- Running `p >>= k` runs `p`, then `k` at its result from the state it reached. -/
theorem run_bind (p : OracleComp D.Result α) (k : α → OracleComp D.Result β) (s : D.State) :
    D.run (p >>= k) s = (D.run p s).bind fun (a, s') => D.run (k a) s' :=
  OracleComp.run_interpret_bind _ _ _ _

/-- Mapping the result of a client maps the result of its run. -/
theorem run_map (f : α → β) (p : OracleComp D.Result α) (s : D.State) :
    D.run (f <$> p) s = (D.run p s).map fun (a, s') => (f a, s') :=
  OracleComp.run_interpret_map _ _ _ _

/-- Every relational run of a client has positive probability. -/
theorem mem_support_run_of_clientRun {p : D.toSpec.Client α} {s s' : D.toSpec.State} {a : α}
    {tr : D.toSpec.Transcript} (h : D.toSpec.ClientRun s p a s' tr) :
    (a, s') ∈ (D.run p s).support := by
  induction h with
  | pure s a => simp
  | liftBind o k r _ hstep _ ih =>
    rw [run_liftBind, PMF.mem_support_bind_iff]
    exact ⟨_, hstep, ih⟩

/-- On a demonically admissible client, every outcome of positive probability is a relational
run. -/
theorem exists_clientRun_of_mem_support {p : D.toSpec.Client α} {s s' : D.toSpec.State} {a : α}
    (hv : D.toSpec.DemonicValid s p) (h : (a, s') ∈ (D.run p s).support) :
    ∃ tr, D.toSpec.ClientRun s p a s' tr := by
  induction hv generalizing a s' with
  | pure s b =>
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ((PMF.mem_support_pure_iff _ _).mp h)
    exact ⟨[], .pure _ _⟩
  | liftBind o k hv_o _ ih =>
    rw [run_liftBind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨r, s₁⟩, hstep, hrest⟩ := h
    obtain ⟨tr, htr⟩ := ih s₁ r hstep hrest
    exact ⟨_, .liftBind o k r hv_o hstep htr⟩

/-- The expected total charge of a client run from `s`, where a call `o` from state `s` costs
`charge s o`. -/
noncomputable def expectedCost (charge : D.State → D.Op → ℕ) :
    OracleComp D.Result α → D.State → ℝ≥0∞
  | .pure _, _ => 0
  | .liftBind o k, s => charge s o + ∑' x, D.law o s x * expectedCost charge (k x.1) x.2

@[simp] theorem expectedCost_pure (charge : D.State → D.Op → ℕ) (a : α) (s : D.State) :
    D.expectedCost charge (pure a) s = 0 := rfl

theorem expectedCost_liftBind (charge : D.State → D.Op → ℕ) (o : D.Op)
    (k : D.Result o → OracleComp D.Result α) (s : D.State) :
    D.expectedCost charge (.liftBind o k) s =
      charge s o + ∑' x, D.law o s x * D.expectedCost charge (k x.1) x.2 := rfl

/-- The expected charge of `p >>= k` is that of `p` plus the expected charge of the
continuation. -/
theorem expectedCost_bind (charge : D.State → D.Op → ℕ) (p : OracleComp D.Result α)
    (k : α → OracleComp D.Result β) (s : D.State) :
    D.expectedCost charge (p >>= k) s =
      D.expectedCost charge p s + ∑' x, D.run p s x * D.expectedCost charge (k x.1) x.2 := by
  induction p generalizing s with
  | pure a =>
    change D.expectedCost charge (k a) s = 0 + ∑' x, PMF.pure (a, s) x * _
    rw [zero_add, tsum_eq_single (a, s)]
    · simp
    · intro x hx
      simp [PMF.pure_apply, hx]
  | liftBind o cont ih =>
    change D.expectedCost charge (.liftBind o fun r => cont r >>= k) s = _
    rw [expectedCost_liftBind, expectedCost_liftBind, run_liftBind,
      Probability.PMF.tsum_bind_mul, add_assoc, ← tsum_add]
    congr 1
    refine tsum_congr fun x => ?_
    rw [ih, mul_add]

/-- With charges independent of the state, a query budget bounds the expected charge. -/
theorem expectedCost_le_of_isCostBounded {cost : D.Op → ℕ} {p : OracleComp D.Result α} {n : ℕ}
    (h : OracleComp.IsCostBounded cost p n) (s : D.State) :
    D.expectedCost (fun _ o => cost o) p s ≤ n := by
  induction h generalizing s with
  | pure a n => simp
  | liftBind q cont n _ ih =>
    change D.expectedCost _ (.liftBind q cont) s ≤ _
    rw [expectedCost_liftBind, Nat.cast_add, add_comm (n : ℝ≥0∞)]
    gcongr
    calc ∑' x, D.law q s x * D.expectedCost (fun _ o => cost o) (cont x.1) x.2
        ≤ ∑' x, D.law q s x * n := tsum_le_tsum fun x => by gcongr; exact ih _ _
      _ = n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Issue a fixed list of operations and return the transcript of operations and answers. -/
def obliviousClient : List D.Op → OracleComp D.Result (List (Sigma D.Result))
  | [] => pure []
  | o :: os => .liftBind o fun a => (⟨o, a⟩ :: ·) <$> obliviousClient os

@[simp] theorem obliviousClient_nil : D.obliviousClient [] = pure [] := rfl

theorem obliviousClient_cons (o : D.Op) (os : List D.Op) :
    D.obliviousClient (o :: os) =
      .liftBind o fun a => (⟨o, a⟩ :: ·) <$> D.obliviousClient os := rfl

/-- The calls of an oblivious client cost the sum of the costs of its operations. -/
theorem isCostBounded_obliviousClient (cost : D.Op → ℕ) (ops : List D.Op) :
    OracleComp.IsCostBounded cost (D.obliviousClient ops) (ops.map cost).sum := by
  induction ops with
  | nil => exact .pure _ _
  | cons o os ih =>
    refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by simp, fun a => ?_⟩
    rw [OracleComp.isCostBounded_map_iff]
    simpa using ih

/-! ## Private coins -/

/-- The interface `E` together with private uniform coins: a call `.inl n` is answered uniformly
from `Fin (n + 1)` and leaves the state unchanged, and a call `.inr o` is a call of `E`. Its clients
are the `ProbOracleComp E.Result` programs. -/
noncomputable abbrev withCoins (E : RandomizedSpec) : RandomizedSpec where
  State := E.State
  Op := ℕ ⊕ E.Op
  Result := probOracleSpec E.Result
  law := ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) E.law
  valid s
    | .inl _ => True
    | .inr o => E.valid s o

variable {D}

/-- A program over `E` alone runs as over `E`. -/
@[simp] theorem withCoins_run_liftRight (p : OracleComp D.Result α) (s : D.State) :
    D.withCoins.run (OracleComp.liftRight p) s = D.run p s := by
  simp only [run, ProbOracleComp.handler_eq_sumHandler, OracleComp.interpret_sumHandler_liftRight]

/-- A closed sampler draws its value and leaves the state unchanged. -/
@[simp] theorem withCoins_run_sample (q : ProbComp α) (s : D.State) :
    D.withCoins.run (ProbOracleComp.sample q) s = (ProbComp.eval q).map (·, s) :=
  ProbOracleComp.run_interpret_sample D.law q s

/-- Admissibility over `E` is admissibility of the embedded program. -/
theorem demonicValid_liftRight {p : D.toSpec.Client α} {s : D.toSpec.State}
    (h : D.toSpec.DemonicValid s p) :
    D.withCoins.toSpec.DemonicValid s (OracleComp.liftRight p) := by
  induction h with
  | pure s a => exact StateTransitionSpec.DemonicValid.pure (D := D.withCoins.toSpec) s a
  | liftBind o k hv _ ih =>
    exact StateTransitionSpec.DemonicValid.liftBind (D := D.withCoins.toSpec) (Sum.inr o)
      (fun a => OracleComp.liftRight (k a)) hv fun s' a hstep => ih s' a hstep

/-- Coin calls are admissible, and leave the state unchanged. -/
theorem demonicValid_sample_bind {q : ProbComp β} {k : β → OracleComp D.withCoins.Result α}
    {s : D.State} (h : ∀ b, D.withCoins.toSpec.DemonicValid s (k b)) :
    D.withCoins.toSpec.DemonicValid s (ProbOracleComp.sample q >>= k) := by
  induction q with
  | pure b => exact h b
  | liftBind n cont ih =>
    refine StateTransitionSpec.DemonicValid.liftBind (D := D.withCoins.toSpec) (Sum.inl n)
      (fun i => ProbOracleComp.sample (cont i) >>= k) trivial fun s' i hstep => ?_
    have hs : s' = s := by
      change (i, s') ∈ ((ProbComp.unifOracle n).bind fun i => PMF.pure (i, s)).support at hstep
      obtain ⟨_, _, h⟩ := (PMF.mem_support_bind_iff _ _ _).mp hstep
      exact (Prod.ext_iff.mp ((PMF.mem_support_pure_iff _ _).mp h)).2
    subst hs
    exact ih i

end RandomizedSpec

/-! ## Deterministic specifications -/

namespace StateTransitionSpec

variable {D : StateTransitionSpec.{0, 0, 0}} {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn f] {α : Type}

variable (D) in
/-- A deterministic specification as a randomized one: each outcome is a point mass. -/
noncomputable abbrev toRandomized : RandomizedSpec where
  State := D.State
  Op := D.Op
  Result := D.Result
  law o s := let (s', a) := D.stepFn s o; PMF.pure (a, s')
  valid := D.valid

/-- A deterministic run is the point mass at the evaluated result and final state. -/
@[simp] theorem run_toRandomized (p : D.Client α) (s : D.State) :
    D.toRandomized.run p s = PMF.pure (DataStructure.eval D p s) := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih =>
    rw [RandomizedSpec.run_liftBind]
    exact (PMF.pure_bind _ _).trans (ih _ _)

/-- The support of a deterministic specification is the specification. -/
theorem toRandomized_step_iff (s s' : D.State) (o : D.Op) (a : D.Result o) :
    D.toRandomized.toSpec.step s o s' a ↔ D.step s o s' a := by
  rw [D.step_iff_stepFn]
  change (a, s') ∈ (PMF.pure ((D.stepFn s o).2, (D.stepFn s o).1)).support ↔ _
  rw [PMF.mem_support_pure_iff]
  constructor
  · intro h
    obtain ⟨ha, hs⟩ := Prod.mk.inj h
    exact Prod.ext hs ha
  · intro h
    rw [← h]

/-- Admissibility of a deterministic history is admissibility on the support. -/
theorem toRandomized_demonicValid_of_validHistory {p : D.Client α} {s : D.State}
    (h : D.ValidHistory s (D.clientHistory s p)) : D.toRandomized.toSpec.DemonicValid s p := by
  have hv := (D.demonicValid_iff_validHistory_runClient s p).mpr h
  clear h
  induction hv with
  | pure s a => exact StateTransitionSpec.DemonicValid.pure (D := D.toRandomized.toSpec) s a
  | liftBind o k hv _ ih =>
    exact StateTransitionSpec.DemonicValid.liftBind (D := D.toRandomized.toSpec) o k hv
      fun s' a hstep => ih s' a ((toRandomized_step_iff _ _ _ _).mp hstep)

end StateTransitionSpec

/-! ## Distributional refinements -/

/-- A randomized refinement of `D` by methods over `F`: a relational refinement of the supports
whose methods, from a state satisfying the invariant, realize the specified law through the
abstraction function. -/
structure RandomizedRefinement (D F : RandomizedSpec) extends Refinement D.toSpec F.toSpec where
  /-- The answer and the abstracted final state of each admissible method follow the law. -/
  law : ∀ {e} o, inv e → D.valid (abs e) o →
    (F.run (methods o) e).map (fun (a, e') => (a, abs e')) = D.law o (abs e)

namespace RandomizedRefinement

variable {D F G : RandomizedSpec} {α : Type}

/-- The constructor from admissibility, preservation of the invariant on outcomes of positive
probability, and the law. The relational step follows from the law. -/
def ofLaw (methods : Methods D.toSpec F.toSpec) (inv : F.State → Prop) (abs : F.State → D.State)
    (valid : ∀ {e} o, inv e → D.valid (abs e) o → F.toSpec.DemonicValid e (methods o))
    (inv_run : ∀ {e} o, inv e → D.valid (abs e) o →
      ∀ a e', (a, e') ∈ (F.run (methods o) e).support → inv e')
    (law : ∀ {e} o, inv e → D.valid (abs e) o →
      (F.run (methods o) e).map (fun (a, e') => (a, abs e')) = D.law o (abs e)) :
    RandomizedRefinement D F where
  methods := methods
  inv := inv
  abs := abs
  valid := valid
  correct {e} o {a e' tr} hi hv hrun := by
    have hmem := F.mem_support_run_of_clientRun hrun
    refine ⟨?_, inv_run o hi hv a e' hmem⟩
    change (a, abs e') ∈ (D.law o (abs e)).support
    rw [← law o hi hv]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, e'), hmem, rfl⟩
  law := law

variable (M : RandomizedRefinement D F)

/-- The invariant holds after every outcome of positive probability of an admissible method. -/
theorem inv_of_mem_support {e : F.State} (o : D.Op) (he : M.inv e) (hv : D.valid (M.abs e) o)
    {a : D.Result o} {e' : F.State} (h : (a, e') ∈ (F.run (M.methods o) e).support) :
    M.inv e' :=
  let ⟨_, hrun⟩ := F.exists_clientRun_of_mem_support (M.valid o he hv) h
  (M.correct o he hv hrun).2

/-- An outcome of positive probability of an admissible method abstracts to a permitted step. -/
theorem step_of_mem_support {e : F.State} (o : D.Op) (he : M.inv e) (hv : D.valid (M.abs e) o)
    {a : D.Result o} {e' : F.State} (h : (a, e') ∈ (F.run (M.methods o) e).support) :
    (a, M.abs e') ∈ (D.law o (M.abs e)).support := by
  rw [← M.law o he hv]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, e'), h, rfl⟩

/-- **The distributional hop.** The law of an admissible client linked through the methods, read
through the abstraction function, is the law of the client on the specification. This is
`OracleComp.run_interpret_map_state_of_invariant` for the methods' handler
(`run_interpret_handler`), with preconditions: the law need hold only for admissible operations,
and the client must be admissible. -/
theorem run_link (p : OracleComp D.Result α) {e : F.State} (he : M.inv e)
    (hv : D.toSpec.DemonicValid (M.abs e) p) :
    (F.run (link M.methods p) e).map (fun (a, e') => (a, M.abs e')) = D.run p (M.abs e) := by
  induction p generalizing e with
  | pure a => simp [link]
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.toSpec.demonicValid_liftBind_iff _ o k).mp hv
    change (F.run (M.methods o >>= fun r => link M.methods (k r)) e).map _ = _
    rw [F.run_bind, PMF.map_bind, Probability.PMF.bind_congr_on_support _ _
      (fun x => D.run (k x.1) (M.abs x.2)) fun x hx =>
        ih x.1 (M.inv_of_mem_support o he hv_o hx) (hv_k _ _ (M.step_of_mem_support o he hv_o hx)),
      D.run_liftBind, ← M.law o he hv_o, PMF.bind_map]
    rfl

/-- The invariant holds on every outcome of positive probability of an admissible linked
client. -/
theorem inv_of_mem_support_link (p : OracleComp D.Result α) {e : F.State} (he : M.inv e)
    (hv : D.toSpec.DemonicValid (M.abs e) p) {a : α} {e' : F.State}
    (h : (a, e') ∈ (F.run (link M.methods p) e).support) : M.inv e' := by
  obtain ⟨hvF, hrun⟩ := M.toRefinement.simulates_demonic p he hv
  obtain ⟨tr, htr⟩ := F.exists_clientRun_of_mem_support hvF h
  exact (hrun a e' tr htr).1

/-- Composition: the upper methods are linked through the lower ones, the invariants conjoin, and
the abstraction functions compose. -/
def comp (M : RandomizedRefinement D F) (N : RandomizedRefinement F G) :
    RandomizedRefinement D G where
  toRefinement := M.toRefinement.comp N.toRefinement
  law {g} o hi hv := by
    have h := N.run_link (M.methods o) hi.1 (M.valid o hi.2 hv)
    calc _ = ((G.run (link N.methods (M.methods o)) g).map fun (a, g') => (a, N.abs g')).map
            fun (a, f) => (a, M.abs f) := by rw [PMF.map_comp]; rfl
      _ = _ := by rw [h, M.law o hi.2 hv]; rfl

/-! ## Identical until bad -/

/-- The methods as a stateful handler of the upper operations on lower states. -/
noncomputable abbrev handler (methods : Methods D.toSpec F.toSpec) :
    (o : D.Op) → StateT F.State PMF (D.Result o) :=
  fun o => OracleComp.interpret F.law (methods o)

/-- Interpreting a client through the methods' handler runs the linked client. -/
theorem run_interpret_handler (methods : Methods D.toSpec F.toSpec)
    (p : OracleComp D.Result α) (e : F.State) :
    (OracleComp.interpret (handler methods) p).run e = F.run (link methods p) e :=
  congrArg (StateT.run · e) (OracleComp.interpret_interpret methods F.law p).symm

/-- **The identical-until-bad step.** Let real methods agree with the methods of an exact
randomized refinement until a bad lower state. Then an experiment continuing the real client run
accepts at most as often as on the specification, plus the probability that the real run reaches
a bad state. -/
theorem bind_apply_le_of_identicalUntilBad (real : Methods D.toSpec F.toSpec)
    {bad : F.State → Prop}
    (h : OracleComp.IdenticalUntilBad (handler real) (handler M.methods) bad)
    (p : OracleComp D.Result α) {e : F.State} (he : M.inv e)
    (hv : D.toSpec.DemonicValid (M.abs e) p) {β : Type} (next : α × D.State → PMF β) (b : β) :
    ((F.run (link real p) e).bind fun (a, e') => next (a, M.abs e')) b ≤
      (D.run p (M.abs e)).bind next b +
        (F.run (link real p) e).toOuterMeasure {x | bad x.2} := by
  have hle := h.bind_apply_le p e (fun (a, e') => next (a, M.abs e')) b
  rw [run_interpret_handler, run_interpret_handler] at hle
  rw [← M.run_link p he hv, PMF.bind_map]
  exact hle

/-- **The identical-until-bad step, two-sided.** The acceptance probabilities of the real client
and of the specification differ by at most the probability that the real run reaches a bad
state. -/
theorem abs_sub_le_of_identicalUntilBad (real : Methods D.toSpec F.toSpec)
    {bad : F.State → Prop}
    (h : OracleComp.IdenticalUntilBad (handler real) (handler M.methods) bad)
    (p : OracleComp D.Result α) {e : F.State} (he : M.inv e)
    (hv : D.toSpec.DemonicValid (M.abs e) p) {β : Type} (next : α × D.State → PMF β) (b : β) :
    |(((F.run (link real p) e).bind fun (a, e') => next (a, M.abs e')) b).toReal -
        ((D.run p (M.abs e)).bind next b).toReal| ≤
      ((F.run (link real p) e).toOuterMeasure {x | bad x.2}).toReal := by
  have hle := h.abs_sub_le p e (fun (a, e') => next (a, M.abs e')) b
  rw [run_interpret_handler, run_interpret_handler] at hle
  rw [← M.run_link p he hv, PMF.bind_map]
  exact hle

/-! ## Expected amortized costs -/

/-- Expected amortized cost refinement: the expected lower charges of every admissible method,
plus the expected potential after it, are at most the upper charge plus the potential before
it. -/
structure ExpectedAmortized (lower : F.State → F.Op → ℕ) (upper : D.State → D.Op → ℕ)
    (potential : F.State → ℝ≥0∞) : Prop where
  /-- The physicist's inequality in expectation, for one method. -/
  step : ∀ {e} o, M.inv e → D.valid (M.abs e) o →
    F.expectedCost lower (M.methods o) e + ∑' x, F.run (M.methods o) e x * potential x.2 ≤
      upper (M.abs e) o + potential e

variable {M} {lower : F.State → F.Op → ℕ} {upper : D.State → D.Op → ℕ}
  {potential : F.State → ℝ≥0∞}

/-- **Expected potentials telescope along adaptive clients.** The expected lower charges of an
admissible linked client, plus the expected final potential, are at most the expected upper
charges of the client on the specification plus the initial potential. -/
theorem ExpectedAmortized.client (A : M.ExpectedAmortized lower upper potential)
    (p : OracleComp D.Result α) {e : F.State} (he : M.inv e)
    (hv : D.toSpec.DemonicValid (M.abs e) p) :
    F.expectedCost lower (link M.methods p) e +
        ∑' x, F.run (link M.methods p) e x * potential x.2 ≤
      D.expectedCost upper p (M.abs e) + potential e := by
  induction p generalizing e with
  | pure a =>
    change 0 + ∑' x, PMF.pure (a, e) x * potential x.2 ≤ 0 + potential e
    rw [tsum_eq_single (a, e)]
    · simp
    · intro x hx
      simp [PMF.pure_apply, hx]
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.toSpec.demonicValid_liftBind_iff _ o k).mp hv
    change F.expectedCost lower (M.methods o >>= fun r => link M.methods (k r)) e +
      ∑' x, F.run (M.methods o >>= fun r => link M.methods (k r)) e x * potential x.2 ≤ _
    rw [F.expectedCost_bind, F.run_bind, Probability.PMF.tsum_bind_mul, add_assoc,
      ← tsum_add]
    simp only [← mul_add]
    calc _ ≤ F.expectedCost lower (M.methods o) e + ∑' x, F.run (M.methods o) e x *
          (D.expectedCost upper (k x.1) (M.abs x.2) + potential x.2) := by
          refine add_le_add le_rfl (tsum_le_tsum fun x => ?_)
          by_cases hx : x ∈ (F.run (M.methods o) e).support
          · exact mul_le_mul_of_nonneg_left (ih x.1 (M.inv_of_mem_support o he hv_o hx)
              (hv_k _ _ (M.step_of_mem_support o he hv_o hx))) zero_le
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul, zero_mul]
      _ = (F.expectedCost lower (M.methods o) e +
            ∑' x, F.run (M.methods o) e x * potential x.2) +
          ∑' x, D.law o (M.abs e) x * D.expectedCost upper (k x.1) x.2 := by
          rw [← M.law o he hv_o, Probability.PMF.tsum_map_mul]
          simp only [mul_add, tsum_add]
          ring
      _ ≤ (upper (M.abs e) o + potential e) +
          ∑' x, D.law o (M.abs e) x * D.expectedCost upper (k x.1) x.2 :=
          add_le_add (A.step o he hv_o) le_rfl
      _ = _ := by rw [D.expectedCost_liftBind]; ring

/-- **Expected potentials stack across composition.** The composite is amortized in
expectation with the upper potential, read through the lower abstraction, plus the lower
potential. -/
theorem ExpectedAmortized.comp {N : RandomizedRefinement F G} {lower : G.State → G.Op → ℕ}
    {middle : F.State → F.Op → ℕ} {Φ : F.State → ℝ≥0∞} {Ψ : G.State → ℝ≥0∞}
    (A : M.ExpectedAmortized middle upper Φ) (B : N.ExpectedAmortized lower middle Ψ) :
    (M.comp N).ExpectedAmortized lower upper (fun g => Φ (N.abs g) + Ψ g) where
  step {g} o hi hv := by
    have hB := B.client (M.methods o) hi.1 (M.valid o hi.2 hv)
    have hA := A.step o hi.2 hv
    have hΦ : ∑' x, G.run (link N.methods (M.methods o)) g x * Φ (N.abs x.2) =
        ∑' x, F.run (M.methods o) (N.abs g) x * Φ x.2 := by
      rw [← N.run_link (M.methods o) hi.1 (M.valid o hi.2 hv), Probability.PMF.tsum_map_mul]
    change G.expectedCost lower (link N.methods (M.methods o)) g +
        ∑' x, G.run (link N.methods (M.methods o)) g x * (Φ (N.abs x.2) + Ψ x.2) ≤
      upper (M.abs (N.abs g)) o + (Φ (N.abs g) + Ψ g)
    simp only [mul_add, tsum_add, hΦ]
    calc _ = (G.expectedCost lower (link N.methods (M.methods o)) g +
            ∑' x, G.run (link N.methods (M.methods o)) g x * Ψ x.2) +
          ∑' x, F.run (M.methods o) (N.abs g) x * Φ x.2 := by ring
      _ ≤ (F.expectedCost middle (M.methods o) (N.abs g) + Ψ g) +
          ∑' x, F.run (M.methods o) (N.abs g) x * Φ x.2 := add_le_add hB le_rfl
      _ = (F.expectedCost middle (M.methods o) (N.abs g) +
            ∑' x, F.run (M.methods o) (N.abs g) x * Φ x.2) + Ψ g := by ring
      _ ≤ (upper (M.abs (N.abs g)) o + Φ (N.abs g)) + Ψ g := add_le_add hA le_rfl
      _ = _ := by ring

/-- With charges independent of the state, query budgets of the methods give an expected
amortized certificate with zero potential. -/
theorem ExpectedAmortized.of_isCostBounded {cost : F.Op → ℕ} {budget : D.Op → ℕ}
    (h : ∀ o, OracleComp.IsCostBounded cost (M.methods o) (budget o)) :
    M.ExpectedAmortized (fun _ q => cost q) (fun _ o => budget o) fun _ => 0 where
  step {e} o _ _ := by
    simpa using F.expectedCost_le_of_isCostBounded (h o) e

end RandomizedRefinement

end Cslib.DataStructure
