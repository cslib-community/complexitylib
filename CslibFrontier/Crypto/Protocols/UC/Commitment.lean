/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF

/-!
# Ideal UC Bit Commitment and the Canetti–Fischlin Plain-Model Impossibility Theorem

This module defines the two-party ideal bit-commitment functionality `fcom` in the Universally
Composable (UC) framework with static corruptions
(`CslibFrontier/Crypto/Protocols/UC/Execution.lean`)
and proves the Canetti–Fischlin impossibility theorem ([CanettiFischlin2001], Theorem 1): no
plain-model two-party commitment protocol with nontrivial completeness can UC-realize `fcom`.

In the plain model (`PlainCommitmentScheme`), committer `0 : Fin 2` and receiver `1 : Fin 2` share
no trusted setup (such as a common reference string with a simulator trapdoor). Honest committer `0`
samples a commit message and opening message `(c, o) ← scheme.commit κ b`, and honest receiver `1`
verifies a delivered pair `(c, o)` using `scheme.verify κ c o`. When committer `0` is statically
corrupted (`C = {0}`), the adversary may inject arbitrary commit and opening messages `(c, o)` to
honest receiver `1`; when receiver `1` is statically corrupted (`C = {1}`), the adversary reads the
commit and opening messages sent by honest committer `0`.

The Canetti–Fischlin impossibility proof proceeds by combining two environments against the dummy
adversary:
1. **Corrupted-receiver experiment (`C = {1}`, `corruptReceiverEnv`):** Honest committer `0`
   commits to `b`, the environment reads the commit message `c`, honest committer `0` opens, the
   environment reads the opening message `o`, and the environment runs `scheme.verify κ c o` to
   check whether `res = some b`. In the real execution with `dummyAdversary`, this succeeds with
   probability `scheme.acceptProb κ b` (`eval_exec_real_corruptReceiverEnv`). In the ideal execution
   with any simulator `S₁`, while `fcom` is in state `.committed b` before opening, `fcom`'s
   responses on `C = {1}` are independent of `b` (`runFrom_fcom_committed`), so `S₁` must produce
   its commit message `c` and post-commit state `st₁` without knowing `b`.
2. **Corrupted-committer equivocation experiment (`C = {0}`, `corruptCommitterEnv`):** Using `S₁`,
   the environment runs `S₁`'s pre-open commit simulation (`simCommit S₁ κ`, which is independent
   of `b`) and delivers the resulting commit message `c` to honest receiver `1`, checking that `1`
   outputs `some .receipt`. It then runs `S₁`'s opening simulation `simOpen S₁ b κ st₁` for bit `b`,
   delivers the resulting opening message `o` to honest receiver `1`, and checks whether `1` outputs
   `some (.opened b)`.
   - In the **real** world (`C = {0}`), because honest receiver `1`'s state in the plain model
     depends only on the delivered messages `c` and `o`, the real execution with
     `corruptCommitterEnv` is identical to the ideal execution of `corruptReceiverEnv` with `S₁`
     (`exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv`).
   - In the **ideal** world (`C = {0}`), once honest receiver `1` observes `some .receipt` from
     `fcom`, `fcom`'s state is locked to `.committed b*` for a single bit `b* : Bool` before `b` is
     used (`runFrom_execMachine_fcom_locked`), so `fcom` can never output `some (.opened (!b*))`.
     Thus, for every simulator `S₀`, the ideal success probabilities of
     `corruptCommitterEnv S₁ false` and `corruptCommitterEnv S₁ true` sum to at most `1`
     (`succProbability_exec_fcom_corruptCommitterEnv_add_le_one`).

Combining both experiments via the triangle inequality yields the quantitative trade-off
`acceptProb_add_le_one_add_advantage` and the concrete and asymptotic impossibility theorems
`not_emulatesDummyWithin_fcom`, `not_realizesWithin_fcom`, `not_realizes_fcom`, and
`not_realizes_fcom_of_perfectlyComplete`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.CommitmentInput`,
  `Cslib.Crypto.Protocols.UC.CommitmentOutput`,
  `Cslib.Crypto.Protocols.UC.CommitmentState`: inputs, outputs, and states of the ideal
  two-party commitment functionality.
* `Cslib.Crypto.Protocols.UC.fcom`: the two-party ideal bit-commitment functionality
  $\mathcal{F}_{\mathrm{com}}$.
* `Cslib.Crypto.Protocols.UC.fcomCommittedView`,
  `Cslib.Crypto.Protocols.UC.fcomLocked`: state-abstraction machines capturing pre-open hiding
  (`C = {1}`) and post-commit binding (`C = {0}`) of `fcom`.
* `Cslib.Crypto.Protocols.UC.PlainNetQ`, `Cslib.Crypto.Protocols.UC.PlainNetR`,
  `Cslib.Crypto.Protocols.UC.CommitterState`, `Cslib.Crypto.Protocols.UC.ReceiverState`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentScheme`: plain-model two-party commitment schemes and
  their compilation `PlainCommitmentScheme.toProtocol` into a UC `Protocol`.
* `Cslib.Crypto.Protocols.UC.honestCommitEnv`,
  `Cslib.Crypto.Protocols.UC.corruptReceiverEnv`,
  `Cslib.Crypto.Protocols.UC.corruptCommitterEnv`: honest-completeness, corrupted-receiver, and
  corrupted-committer equivocation environments.

## Main results

* `Cslib.Crypto.Protocols.UC.Machine.runFrom_map_state`,
  `Cslib.Crypto.Protocols.UC.Machine.comp_handle_map_state`,
  `Cslib.Crypto.Protocols.UC.Machine.isQueryBounded_closeProgram`: state-homomorphism and
  closing budget laws for interactive machines.
* `Cslib.Crypto.Protocols.UC.fcom_polyBounded`,
  `Cslib.Crypto.Protocols.UC.runFrom_fcom_committed`,
  `Cslib.Crypto.Protocols.UC.runFrom_execMachine_fcom_locked`: budget, pre-open hiding, and
  post-commit binding of `fcom`.
* `Cslib.Crypto.Protocols.UC.eval_exec_honestCommitEnv`,
  `Cslib.Crypto.Protocols.UC.eval_exec_real_corruptReceiverEnv`,
  `Cslib.Crypto.Protocols.UC.exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv`:
  exact execution laws for honest completeness, corrupted-receiver extraction, and plain-model
  man-in-the-middle equivocation.
* `Cslib.Crypto.Protocols.UC.succProbability_exec_fcom_corruptCommitterEnv_add_le_one`:
  ideal-world binding bounds the sum of equivocation success probabilities on `false` and `true`
  by `1`.
* `Cslib.Crypto.Protocols.UC.acceptProb_add_le_one_add_advantage`: quantitative Canetti–Fischlin
  lower bound relating completeness to $C = \{1\}$ and $C = \{0\}$ distinguishing advantages.
* `Cslib.Crypto.Protocols.UC.not_emulatesDummyWithin_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizesWithin_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizes_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizes_fcom_of_perfectlyComplete`: concrete and asymptotic
  impossibility of UC bit commitment in the plain model.

## References

* [R. Canetti, M. Fischlin, *Universally Composable Commitments*][CanettiFischlin2001]: Figure 2
  ($\mathcal{F}_{\mathrm{com}}$) and Theorem 1 (impossibility in the plain model).
* [R. Canetti, *Universally Composable Security*][Canetti2020]: UC execution and emulation.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Polynomial
open OracleComp (sumHandler)
open scoped NNReal ENNReal

/-! ### Machine state homomorphisms and closing budgets -/

namespace Machine

variable {ιI ιJ ιE : Type} {I : ιI → Type} {J : ιJ → Type} {E : ιE → Type} {α : Type}

/-- If `f` intertwines every activation of `M₂` with `M₁`, running any program against `M₁` from
`f s` is running it against `M₂` from `s` and mapping the final state by `f`. -/
theorem runFrom_map_state (M₁ M₂ : Machine I E) (f : M₂.State → M₁.State)
    (h : ∀ q s, (M₁.handle q).run (f s) = Prod.map _root_.id f <$> (M₂.handle q).run s)
    (program : ProbOracleComp E α) (s : M₂.State) :
    M₁.runFrom program (f s) = Prod.map _root_.id f <$> M₂.runFrom program s := by
  have hhandler : ∀ q s,
      M₁.handler q (f s) = Prod.map _root_.id f <$> M₂.handler q s := by
    rintro (n | q) s
    · simp only [Machine.handler, sumHandler, StateT.lift, bind_pure_comp, Functor.map_map]
      rfl
    · exact h q s
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [Machine.runFrom, Machine.runFrom, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_bind, OracleComp.run_interpret_query, OracleComp.run_interpret_query,
      hhandler q s, bind_map_left, map_bind]
    exact bind_congr fun x => ih x.1 x.2

/-- Intertwining the inner machines of a composition intertwines the composed machines on the
product state. -/
theorem comp_handle_map_state (A : Machine J E) (P₁ P₂ : Machine I J) (f : P₂.State → P₁.State)
    (h : ∀ q s, (P₁.handle q).run (f s) = Prod.map _root_.id f <$> (P₂.handle q).run s)
    (q : ιE) (s : A.State × P₂.State) :
    ((A.comp P₁).handle q).run (Prod.map _root_.id f s) =
      Prod.map _root_.id (Prod.map _root_.id f) <$> ((A.comp P₂).handle q).run s := by
  rcases s with ⟨sA, sP⟩
  change Equiv.prodAssoc _ _ _ <$> P₁.runFrom ((A.handle q).run sA) (f sP) =
    Prod.map _root_.id (Prod.map _root_.id f) <$>
      (Equiv.prodAssoc _ _ _ <$> P₂.runFrom ((A.handle q).run sA) sP)
  rw [Machine.runFrom_map_state P₁ P₂ f h, Functor.map_map, Functor.map_map]
  rfl

/-- Closing a program with no external imports preserves its query budget. -/
theorem isQueryBounded_closeProgram {program : ProbOracleComp OracleSpec.empty α} {n : ℕ}
    (h : program.IsQueryBounded n) : (Machine.closeProgram program).IsQueryBounded n :=
  OracleComp.IsCostBounded.interpret
    (fun q => q.casesOn (fun k => OracleComp.IsCostBounded.query k) fun e => e.elim) h

end Machine

/-- Running the UC execution with `dummyAdversary` is running the environment directly against
`corruptRouter C (π κ C)`. -/
@[simp] theorem exec_dummyAdversary {n : ℕ} {In Out NetQ NetR : Type}
    (π : Protocol n In Out NetQ NetR) (C : Finset (Fin n))
    (Z : Environment n In Out ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR))
    (κ : ℕ) (z : List Bool) :
    exec π (dummyAdversary n _ _) C Z κ z = (corruptRouter C (π κ C)).run (Z κ z) := by
  simp only [exec, execMachine, dummyAdversary, Machine.run_comp, liftAdversary_id,
    Machine.link_id]

/-- Intertwining two protocol machines intertwines their `corruptRouter` wrappers for any static
corruption set `C`. -/
theorem handle_corruptRouter_map_state {n : ℕ} {In Out NetQ NetR : Type}
    (C : Finset (Fin n))
    (P₁ P₂ : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR))
    (f : P₂.State → P₁.State)
    (h : ∀ q s, (P₁.handle q).run (f s) = Prod.map _root_.id f <$> (P₂.handle q).run s)
    (q : (Fin n × In) ⊕ ((Fin n × In) ⊕ NetQ)) (s : P₂.State) :
    ((corruptRouter C P₁).handle q).run (f s) =
      Prod.map _root_.id f <$> ((corruptRouter C P₂).handle q).run s := by
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | q⟩
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply,
        _root_.id_eq]
    · simp only [corruptRouter, hi, ↓reduceIte, h (Sum.inl (i, x)) s]
  · by_cases hi : i ∈ C
    · simp only [corruptRouter, hi, ↓reduceIte, StateT.run_map]
      rw [h (Sum.inl (i, x)) s, Functor.map_map, Functor.map_map]
      rfl
    · simp only [corruptRouter, hi, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply,
        _root_.id_eq]
  · simp only [corruptRouter, StateT.run_map]
    rw [h (Sum.inr q) s, Functor.map_map, Functor.map_map]
    rfl

/-! ### Ideal two-party commitment functionality `fcom` -/

/-- Inputs to the two-party commitment functionality: committer `0` submits `commit b` and
`openCom`, and receiver `1` submits `query` to read its output. -/
inductive CommitmentInput : Type
  | commit (b : Bool)
  | openCom
  | query
  deriving DecidableEq, Repr

/-- Outputs of the two-party commitment functionality: `receipt` acknowledges that a commitment has
been recorded without revealing the bit, and `opened b` reveals the committed bit `b`. -/
inductive CommitmentOutput : Type
  | receipt
  | opened (b : Bool)
  deriving DecidableEq, Repr

/-- Internal state of `fcom`: initially `idle`, then `committed b` once committer `0` commits to
`b`, and finally `opened b` once committer `0` opens. -/
inductive CommitmentState : Type
  | idle
  | committed (b : Bool)
  | opened (b : Bool)
  deriving DecidableEq, Repr

/-- The ideal two-party bit-commitment functionality $\mathcal{F}_{\mathrm{com}}$
([CanettiFischlin2001], Figure 2) for committer `0 : Fin 2` and receiver `1 : Fin 2`:
- When committer `0` sends `commit b` in state `idle`, `fcom` transitions to `committed b` and
  returns `some .receipt` (subsequent `commit` inputs are ignored).
- When committer `0` sends `openCom` in state `committed b`, `fcom` transitions to `opened b` and
  returns `some (.opened b)`.
- When receiver `1` sends `query` (or the adversary queries the backdoor `()`), `fcom` returns
  `none` in `idle`, `some .receipt` in `committed b` (hiding `b`), and `some (.opened b)` in
  `opened b`. -/
@[expose] def fcom :
    IdealFunctionality 2 CommitmentInput CommitmentOutput Unit (Option CommitmentOutput) where
  State := CommitmentState
  init _ _ := pure .idle
  onInput i x s :=
    if i = 0 then
      match x, s with
      | .commit b, .idle => pure (some .receipt, .committed b)
      | .openCom, .committed b => pure (some (.opened b), .opened b)
      | _, _ => pure (none, s)
    else
      match x, s with
      | .query, .idle => pure (none, .idle)
      | .query, .committed b => pure (some .receipt, .committed b)
      | .query, .opened b => pure (some (.opened b), .opened b)
      | _, _ => pure (none, s)
  onBackdoor _ s :=
    match s with
    | .idle => pure (none, .idle)
    | .committed b => pure (some .receipt, .committed b)
    | .opened b => pure (some (.opened b), .opened b)

/-- `fcom` is purely deterministic and makes zero oracle calls per activation. -/
theorem fcom_isBounded (κ : ℕ) (C : Finset (Fin 2)) : (fcom.toProtocol κ C).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨⟩
  · fin_cases i <;> cases x <;> cases s <;> exact OracleComp.IsCostBounded.pure _ 0
  · cases s <;> exact OracleComp.IsCostBounded.pure _ 0

/-- `fcom` has polynomial call budget `0`. -/
theorem fcom_polyBounded : fcom.toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  exact fcom_isBounded κ C

/-- Routing corruptions around `fcom` still makes zero oracle calls per activation. -/
theorem corruptRouter_fcom_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (corruptRouter C (fcom.toProtocol κ C)).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | ⟨⟩⟩
  · by_cases hi : i ∈ C <;> fin_cases i <;> cases x <;> cases s <;>
      simp only [corruptRouter, hi, ↓reduceIte] <;> exact OracleComp.IsCostBounded.pure _ 0
  · by_cases hi : i ∈ C <;> fin_cases i <;> cases x <;> cases s <;>
      simp only [corruptRouter, hi, ↓reduceIte] <;> exact OracleComp.IsCostBounded.pure _ 0
  · cases s <;> exact OracleComp.IsCostBounded.pure _ 0

/-- Deterministic reply of `corruptRouter {1} (fcom.toProtocol κ {1})` on the network port while
`fcom` is in state `.committed b` (independent of `b`). -/
@[expose] def fcomCommittedReply :
    (Fin 2 × CommitmentInput) ⊕ Unit → Option CommitmentOutput ⊕ Option CommitmentOutput
  | .inl (i, x) =>
    if i = 0 then .inl none
    else match x with
      | .query => .inl (some .receipt)
      | _ => .inl none
  | .inr () => .inr (some .receipt)

/-- Stateless machine capturing the adversary's view of `corruptRouter {1} (fcom.toProtocol κ {1})`
while `fcom` is in state `.committed b`: committer `0` is honest (`0 ∉ {1}`), so `0`'s port returns
`none`, while receiver `1`'s `.query` port and the backdoor return `some .receipt`, independent of
`b`. -/
@[expose] def fcomCommittedView :
    Machine OracleSpec.empty
      (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
        (Option CommitmentOutput ⊕ Option CommitmentOutput)) where
  State := PUnit
  init := pure PUnit.unit
  handle q _ := pure (fcomCommittedReply q, PUnit.unit)

/-- The unique state `()` of `fcomCommittedView`. -/
@[expose] def fcomCommittedState : fcomCommittedView.State := PUnit.unit

/-- `s : CommitmentState` viewed as a state of `corruptRouter C (fcom.toProtocol κ C)`. -/
@[expose] def fcomRouterState (κ : ℕ) (C : Finset (Fin 2)) (s : CommitmentState) :
    (corruptRouter C (fcom.toProtocol κ C)).State := s

/-- `fcomCommittedView` makes zero oracle calls per activation. -/
theorem fcomCommittedView_isBounded : fcomCommittedView.IsBounded 0 :=
  ⟨OracleComp.IsCostBounded.pure _ 0, fun _ _ => OracleComp.IsCostBounded.pure _ 0⟩

/-- On state `.committed b`, every network-port query to `corruptRouter {1} (fcom.toProtocol κ {1})`
returns `fcomCommittedReply q` and leaves the state at `.committed b`. -/
theorem handle_corruptRouter_fcom_committed (κ : ℕ) (b : Bool)
    (q : (Fin 2 × CommitmentInput) ⊕ Unit) :
    ((corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).handle (.inr q)).run
      (.committed b) = pure (fcomCommittedReply q, .committed b) := by
  rcases q with ⟨i, x⟩ | ⟨⟩
  · fin_cases i <;> cases x <;> rfl
  · rfl

/-- **Pre-open hiding of `fcom` for `C = {1}`:** when only receiver `1` is corrupted, every network
query to `corruptRouter {1} (fcom.toProtocol κ {1})` from state `.committed b` leaves the state at
`.committed b` and agrees with the bit-independent machine `fcomCommittedView`. -/
theorem runFrom_fcom_committed (κ : ℕ) (b : Bool) {α : Type}
    (program : ProbOracleComp
      (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
        (Option CommitmentOutput ⊕ Option CommitmentOutput)) α) :
    (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet program) (fcomRouterState κ {1} (.committed b)) =
      Prod.map _root_.id (fun _ => fcomRouterState κ {1} (.committed b)) <$>
        fcomCommittedView.runFrom program fcomCommittedState := by
  induction program using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    rcases q with k | q
    · have h₁ : liftNet (n := 2) (In := CommitmentInput) (Out := CommitmentOutput)
          (OracleComp.query
            (spec := probOracleSpec (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
              (Option CommitmentOutput ⊕ Option CommitmentOutput)))
            (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftNet_sample
          (NetQ := (Fin 2 × CommitmentInput) ⊕ Unit)
          (NetR := Option CommitmentOutput ⊕ Option CommitmentOutput)]
        rfl
      have h₂ : fcomCommittedView.runFrom
          (OracleComp.query
            (spec := probOracleSpec (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
              (Option CommitmentOutput ⊕ Option CommitmentOutput)))
            (Sum.inl k)) fcomCommittedState =
          (fun a => (a, fcomCommittedState)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        fcomCommittedView.runFrom_sample (ProbComp.unifFin k) fcomCommittedState
      erw [liftNet_bind, h₁, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
        Machine.runFrom_bind, h₂, bind_map_left, map_bind]
      exact bind_congr fun a => ih a
    · rw [liftNet_bind]
      have h₁ : (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
          (liftNet (OracleComp.query
            (spec := probOracleSpec (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
              (Option CommitmentOutput ⊕ Option CommitmentOutput)))
            (Sum.inr q))) (fcomRouterState κ {1} (.committed b)) =
          pure (fcomCommittedReply q, fcomRouterState κ {1} (.committed b)) := by
        erw [liftNet_query, Machine.runFrom_query]
        exact handle_corruptRouter_fcom_committed κ b q
      have h₂ : fcomCommittedView.runFrom
          (OracleComp.query
            (spec := probOracleSpec (netSpec ((Fin 2 × CommitmentInput) ⊕ Unit)
              (Option CommitmentOutput ⊕ Option CommitmentOutput)))
            (Sum.inr q)) fcomCommittedState =
          pure (fcomCommittedReply q, fcomCommittedState) := rfl
      erw [Machine.runFrom_bind, h₁, pure_bind, Machine.runFrom_bind, h₂, pure_bind]
      exact ih (fcomCommittedReply q)

/-- Embed a Boolean `opened` flag into `CommitmentState` with locked bit `bStar`: `false`
represents `.committed bStar` and `true` represents `.opened bStar`. -/
@[expose] def CommitmentState.locked (bStar : Bool) : Bool → CommitmentState
  | false => .committed bStar
  | true => .opened bStar

/-- State-restricted version of `fcom.toProtocol` once bit `bStar` has been committed: the state is
simply `opened : Bool`, and the committed bit `bStar` can never be altered. -/
@[expose] def fcomLocked (bStar : Bool) :
    Machine OracleSpec.empty
      (protocolSpec 2 CommitmentInput CommitmentOutput Unit (Option CommitmentOutput)) where
  State := Bool
  init := pure false
  handle q opened :=
    match q with
    | .inl (i, x) =>
      if i = 0 then
        match x, opened with
        | .openCom, false => pure (some (.opened bStar), true)
        | _, _ => pure (none, opened)
      else
        match x, opened with
        | .query, false => pure (some .receipt, false)
        | .query, true => pure (some (.opened bStar), true)
        | _, _ => pure (none, opened)
    | .inr () =>
      if opened then
        pure (some (.opened bStar), true)
      else
        pure (some .receipt, false)

/-- **Post-commit binding of `fcom`:** from `CommitmentState.locked bStar opened`, every activation
of `fcom.toProtocol` factors through `fcomLocked bStar`. -/
theorem handle_fcom_locked (κ : ℕ) (C : Finset (Fin 2)) (bStar : Bool)
    (q : (Fin 2 × CommitmentInput) ⊕ Unit) (opened : Bool) :
    ((fcom.toProtocol κ C).handle q).run (CommitmentState.locked bStar opened) =
      Prod.map _root_.id (CommitmentState.locked bStar) <$>
        ((fcomLocked bStar).handle q).run opened := by
  rcases q with ⟨i, x⟩ | ⟨⟩
  · fin_cases i <;> cases x <;> cases opened <;> rfl
  · cases opened <;> rfl

/-- Running an adversary `S₀` against `fcom` from state `CommitmentState.locked bStar opened`
factors through `fcomLocked bStar`. -/
theorem runFrom_execMachine_fcom_locked {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (C : Finset (Fin 2)) (bStar : Bool) {α : Type}
    (program : ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR) α)
    (stS : (S₀ κ C).State) (opened : Bool) :
    (execMachine fcom.toProtocol S₀ κ C).runFrom
      program (stS, CommitmentState.locked bStar opened) =
      Prod.map _root_.id (Prod.map _root_.id (CommitmentState.locked bStar)) <$>
        ((liftAdversary (S₀ κ C)).comp (corruptRouter C (fcomLocked bStar))).runFrom
          program (stS, opened) :=
  Machine.runFrom_map_state
    (execMachine fcom.toProtocol S₀ κ C)
    ((liftAdversary (S₀ κ C)).comp (corruptRouter C (fcomLocked bStar)))
    (Prod.map _root_.id (CommitmentState.locked bStar))
    (Machine.comp_handle_map_state (liftAdversary (S₀ κ C))
      (corruptRouter C (fcom.toProtocol κ C)) (corruptRouter C (fcomLocked bStar))
      (CommitmentState.locked bStar)
      (handle_corruptRouter_map_state C (fcom.toProtocol κ C) (fcomLocked bStar)
        (CommitmentState.locked bStar) (handle_fcom_locked κ C bStar)))
    program (stS, opened)

/-! ### Plain-model two-party commitment schemes and UC protocol compilation -/

/-- Network queries for a two-party plain-model commitment protocol: the adversary can read the
commit and opening messages posted by honest committer `0` (`readCommit`, `readOpen`) and deliver
commit and opening messages to receiver `1` (`deliverCommit`, `deliverOpen`). -/
inductive PlainNetQ (CommitMsg OpenMsg : Type) : Type
  | readCommit
  | readOpen
  | deliverCommit (c : CommitMsg)
  | deliverOpen (o : OpenMsg)
  deriving DecidableEq, Repr

/-- Network responses for a two-party plain-model commitment protocol. -/
inductive PlainNetR (CommitMsg OpenMsg : Type) : Type
  | commitMsg (c : Option CommitMsg)
  | openMsg (o : Option OpenMsg)
  | ack
  deriving DecidableEq, Repr

/-- Local state of honest committer `0` in a plain-model commitment protocol. -/
inductive CommitterState (CommitMsg OpenMsg : Type) : Type
  | idle
  | committed (c : CommitMsg) (o : OpenMsg)
  | opened (c : CommitMsg) (o : OpenMsg)
  deriving DecidableEq, Repr

/-- Local state of honest receiver `1` in a plain-model commitment protocol. -/
inductive ReceiverState (CommitMsg : Type) : Type
  | waiting
  | committed (c : CommitMsg)
  | finished (res : Option Bool)
  deriving DecidableEq, Repr

/-- A two-party plain-model bit-commitment scheme with commit message type `CommitMsg` and opening
message type `OpenMsg`:
- `commit κ b` samples the commit message `c` and opening message `o` for bit `b` at security
  parameter `κ`.
- `verify κ c o` verifies a commit message `c` and opening message `o`, returning `some b` if the
  opening is accepted for bit `b` and `none` otherwise. -/
structure PlainCommitmentScheme (CommitMsg OpenMsg : Type) : Type where
  /-- Committer's commit and opening sampler. -/
  commit : ℕ → Bool → ProbComp (CommitMsg × OpenMsg)
  /-- Receiver's verification algorithm. -/
  verify : ℕ → CommitMsg → OpenMsg → ProbComp (Option Bool)

namespace PlainCommitmentScheme

variable {CommitMsg OpenMsg : Type} [DecidableEq CommitMsg] [DecidableEq OpenMsg]

/-- Polynomial call budgets `pC` and `pV` for `scheme.commit` and `scheme.verify`. -/
@[expose] def IsPolyBounded (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (pC pV : Polynomial ℕ) : Prop :=
  (∀ κ b, (scheme.commit κ b).IsQueryBounded (pC.eval κ)) ∧
    ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ)

/-- The standalone completeness experiment for bit `b` at security parameter `κ`: sample
`(c, o) ← scheme.commit κ b`, run `res ← scheme.verify κ co.1 co.2`, and check `res = some b`. -/
@[expose] noncomputable def acceptGame (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : Game :=
  ProbComp.eval do
    let co ← scheme.commit κ b
    let res ← scheme.verify κ co.1 co.2
    return decide (res = some b)

/-- Probability that an honest commitment to `b` followed by an honest opening is accepted by the
receiver at security parameter `κ`. -/
@[expose] noncomputable def acceptProb (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : ℝ≥0 :=
  Game.succProbability (scheme.acceptGame κ b)

/-- Perfect completeness: honest commitments to both `false` and `true` are accepted with
probability `1` at every security parameter. -/
@[expose] def PerfectlyComplete (scheme : PlainCommitmentScheme CommitMsg OpenMsg) : Prop :=
  ∀ κ b, scheme.acceptProb κ b = 1

/-- Compile a `PlainCommitmentScheme` into a two-party UC `Protocol` in the plain model:
- Committer `0` and receiver `1` maintain independent local states `CommitterState` and
  `ReceiverState` with no shared secret state.
- When `0 ∉ C` (honest committer), `deliverCommit c` and `deliverOpen o` deliver `c` and `o` to
  receiver `1` when they match the messages posted by `0`; when `0 ∈ C` (corrupted committer), the
  adversary may inject any `c` and `o` to honest receiver `1`. -/
@[expose] def toProtocol (scheme : PlainCommitmentScheme CommitMsg OpenMsg) :
    Protocol 2 CommitmentInput CommitmentOutput
      (PlainNetQ CommitMsg OpenMsg) (PlainNetR CommitMsg OpenMsg) := fun κ C => {
  State := CommitterState CommitMsg OpenMsg × ReceiverState CommitMsg
  init := pure (.idle, .waiting)
  handle q s :=
    match q with
    | .inl (i, x) =>
      if i = 0 then
        if (0 : Fin 2) ∈ C then
          pure (none, s)
        else
          match x, s.1 with
          | .commit b, .idle =>
            ProbOracleComp.sample (scheme.commit κ b) >>= fun co =>
              pure (some .receipt, (.committed co.1 co.2, s.2))
          | .openCom, .committed c o =>
            pure (some .receipt, (.opened c o, s.2))
          | _, _ => pure (none, s)
      else
        if (1 : Fin 2) ∈ C then
          pure (none, s)
        else
          match x, s.2 with
          | .query, .waiting => pure (none, s)
          | .query, .committed _ => pure (some .receipt, s)
          | .query, .finished (some b) => pure (some (.opened b), s)
          | .query, .finished none => pure (none, s)
          | _, _ => pure (none, s)
    | .inr netQ =>
      match netQ with
      | .readCommit =>
        match s.1 with
        | .idle => pure (.commitMsg none, s)
        | .committed c _ => pure (.commitMsg (some c), s)
        | .opened c _ => pure (.commitMsg (some c), s)
      | .readOpen =>
        match s.1 with
        | .opened _ o => pure (.openMsg (some o), s)
        | _ => pure (.openMsg none, s)
      | .deliverCommit c =>
        match s.2 with
        | .waiting =>
          if (0 : Fin 2) ∈ C then
            pure (.ack, (s.1, .committed c))
          else
            match s.1 with
            | .committed c' _ =>
              if c = c' then pure (.ack, (s.1, .committed c)) else pure (.ack, s)
            | .opened c' _ =>
              if c = c' then pure (.ack, (s.1, .committed c)) else pure (.ack, s)
            | .idle => pure (.ack, s)
        | _ => pure (.ack, s)
      | .deliverOpen o =>
        match s.2 with
        | .committed c =>
          if (0 : Fin 2) ∈ C then
            ProbOracleComp.sample (scheme.verify κ c o) >>= fun res =>
              pure (.ack, (s.1, .finished res))
          else
            match s.1 with
            | .opened _ o' =>
              if o = o' then
                ProbOracleComp.sample (scheme.verify κ c o) >>= fun res =>
                  pure (.ack, (s.1, .finished res))
              else
                pure (.ack, s)
            | _ => pure (.ack, s)
        | _ => pure (.ack, s) }

/-- If `scheme` has polynomial call budgets `pC` and `pV`, then `scheme.toProtocol` has polynomial
call budget `pC + pV`. -/
theorem toProtocol_polyBounded {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pC pV : Polynomial ℕ} (h : scheme.IsPolyBounded pC pV) :
    scheme.toProtocol.PolyBounded (pC + pV) := fun κ C => by
  rw [Polynomial.eval_add]
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q s => ?_⟩
  rcases s with ⟨s₁, s₂⟩
  have hcommit (b : Bool) :
      (ProbOracleComp.sample (spec := OracleSpec.empty) (scheme.commit κ b) >>= fun co =>
        pure (some CommitmentOutput.receipt,
          (CommitterState.committed co.1 co.2, s₂))).IsQueryBounded
        (pC.eval κ + pV.eval κ) := by
    have hstep (co : CommitMsg × OpenMsg) :
        (pure (some CommitmentOutput.receipt,
          (CommitterState.committed co.1 co.2, s₂)) :
          ProbOracleComp OracleSpec.empty _).IsQueryBounded 0 :=
      OracleComp.IsCostBounded.pure _ 0
    exact ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.1 κ b)).bind hstep).mono
      (by omega)
  have hverify (c : CommitMsg) (o : OpenMsg) :
      (ProbOracleComp.sample (spec := OracleSpec.empty) (scheme.verify κ c o) >>= fun res =>
        pure (PlainNetR.ack (CommitMsg := CommitMsg) (OpenMsg := OpenMsg),
          (s₁, ReceiverState.finished (CommitMsg := CommitMsg) res))).IsQueryBounded
        (pC.eval κ + pV.eval κ) := by
    have hstep (res : Option Bool) :
        (pure (PlainNetR.ack (CommitMsg := CommitMsg) (OpenMsg := OpenMsg),
          (s₁, ReceiverState.finished (CommitMsg := CommitMsg) res)) :
          ProbOracleComp OracleSpec.empty _).IsQueryBounded 0 :=
      OracleComp.IsCostBounded.pure _ 0
    exact ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.2 κ c o)).bind hstep).mono
      (by omega)
  rcases q with ⟨i, x⟩ | netQ
  · fin_cases i
    · by_cases h0 : (0 : Fin 2) ∈ C
      · simp only [toProtocol, StateT.run, ↓reduceIte, h0]
        exact OracleComp.IsCostBounded.pure _ _
      · cases x <;> cases s₁ <;>
          simp only [toProtocol, StateT.run, ↓reduceIte, h0]
        · exact hcommit _
        all_goals exact OracleComp.IsCostBounded.pure _ _
    · have h10 : (⟨1, by decide⟩ : Fin 2) ≠ 0 := by decide
      by_cases h1 : (1 : Fin 2) ∈ C
      · simp only [toProtocol, StateT.run, h10, ↓reduceIte, h1]
        exact OracleComp.IsCostBounded.pure _ _
      · rcases s₂ with _ | c | (_ | b) <;> cases x <;>
          simp only [toProtocol, StateT.run, h10, ↓reduceIte, h1] <;>
          exact OracleComp.IsCostBounded.pure _ _
  · cases netQ with
    | readCommit =>
      cases s₁ <;> exact OracleComp.IsCostBounded.pure _ _
    | readOpen =>
      cases s₁ <;> exact OracleComp.IsCostBounded.pure _ _
    | deliverCommit c =>
      cases s₂ with
      | waiting =>
        by_cases h0 : (0 : Fin 2) ∈ C
        · simp only [toProtocol, StateT.run, h0, ↓reduceIte]
          exact OracleComp.IsCostBounded.pure _ _
        · cases s₁ <;> simp only [toProtocol, StateT.run, h0, ↓reduceIte]
          · exact OracleComp.IsCostBounded.pure _ _
          · split_ifs <;> exact OracleComp.IsCostBounded.pure _ _
          · split_ifs <;> exact OracleComp.IsCostBounded.pure _ _
      | _ => exact OracleComp.IsCostBounded.pure _ _
    | deliverOpen o =>
      cases s₂ with
      | committed c =>
        by_cases h0 : (0 : Fin 2) ∈ C
        · simp only [toProtocol, StateT.run, h0, ↓reduceIte]
          exact hverify c o
        · cases s₁ <;> simp only [toProtocol, StateT.run, h0, ↓reduceIte]
          · exact OracleComp.IsCostBounded.pure _ _
          · exact OracleComp.IsCostBounded.pure _ _
          · split_ifs
            · exact hverify c o
            · exact OracleComp.IsCostBounded.pure _ _
      | _ => exact OracleComp.IsCostBounded.pure _ _

end PlainCommitmentScheme

/-! ### Honest completeness and Canetti–Fischlin attack environments -/

section Environments

variable {CommitMsg OpenMsg : Type}

/-- Honest-execution environment (`C = ∅`) that instructs committer `0` to commit to `b`, forwards
the commit message `c` to receiver `1`, instructs committer `0` to open, forwards the opening
message `o` to receiver `1`, and checks whether receiver `1` outputs `some (.opened b)`. -/
@[expose] def honestCommitEnv (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) := fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .commit b))
  let r₁ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverCommit c)))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
    let r₂ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let _ ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverOpen o)))
      let out ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
      return decide (out = some (.opened b))
    | _ => return false
  | _ => return false

/-- `(s₁, s₂)` viewed as a state of `corruptRouter C (scheme.toProtocol κ C)`. -/
@[expose] def plainRouterState [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (κ : ℕ) (C : Finset (Fin 2))
    (s₁ : CommitterState CommitMsg OpenMsg) (s₂ : ReceiverState CommitMsg) :
    (corruptRouter C (scheme.toProtocol κ C)).State := (s₁, s₂)

private theorem init_corruptRouter_toProtocol [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (C : Finset (Fin 2)) :
    (corruptRouter C (scheme.toProtocol κ C)).init =
      pure (plainRouterState scheme κ C .idle .waiting) := rfl

private theorem handle_plainRouter_commit_empty [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (b : Bool)
    (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter ∅ (scheme.toProtocol κ ∅)).handle (Sum.inl (0, .commit b))).run
      (plainRouterState scheme κ ∅ .idle s₂) =
      (fun co => (some .receipt, plainRouterState scheme κ ∅ (.committed co.1 co.2) s₂)) <$>
        ProbOracleComp.sample (scheme.commit κ b) := by
  simp [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    bind_pure_comp]

private theorem handle_plainRouter_commit_one [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (b : Bool)
    (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter {1} (scheme.toProtocol κ {1})).handle (Sum.inl (0, .commit b))).run
      (plainRouterState scheme κ {1} .idle s₂) =
      (fun co => (some .receipt, plainRouterState scheme κ {1} (.committed co.1 co.2) s₂)) <$>
        ProbOracleComp.sample (scheme.commit κ b) := by
  have h01 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  simp [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, h01, StateT.run,
    bind_pure_comp]

private theorem handle_plainRouter_openCom_empty [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (c : CommitMsg) (o : OpenMsg)
    (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter ∅ (scheme.toProtocol κ ∅)).handle (Sum.inl (0, .openCom))).run
      (plainRouterState scheme κ ∅ (.committed c o) s₂) =
      pure (some .receipt, plainRouterState scheme κ ∅ (.opened c o) s₂) := rfl

private theorem handle_plainRouter_openCom_one [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (c : CommitMsg) (o : OpenMsg)
    (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter {1} (scheme.toProtocol κ {1})).handle (Sum.inl (0, .openCom))).run
      (plainRouterState scheme κ {1} (.committed c o) s₂) =
      pure (some .receipt, plainRouterState scheme κ {1} (.opened c o) s₂) := rfl

private theorem handle_plainRouter_readCommit [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (C : Finset (Fin 2))
    (c : CommitMsg) (o : OpenMsg) (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inr (.inr .readCommit))).run
      (plainRouterState scheme κ C (.committed c o) s₂) =
      pure (.inr (.commitMsg (some c)), plainRouterState scheme κ C (.committed c o) s₂) := rfl

private theorem handle_plainRouter_readOpen [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (C : Finset (Fin 2))
    (c : CommitMsg) (o : OpenMsg) (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inr (.inr .readOpen))).run
      (plainRouterState scheme κ C (.opened c o) s₂) =
      pure (.inr (.openMsg (some o)), plainRouterState scheme κ C (.opened c o) s₂) := rfl

private theorem handle_plainRouter_deliverCommit_empty [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter ∅ (scheme.toProtocol κ ∅)).handle (Sum.inr (.inr (.deliverCommit c)))).run
      (plainRouterState scheme κ ∅ (.committed c o) .waiting) =
      pure (.inr .ack, plainRouterState scheme κ ∅ (.committed c o) (.committed c)) := by
  simp [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]

private theorem handle_plainRouter_deliverOpen_empty [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter ∅ (scheme.toProtocol κ ∅)).handle (Sum.inr (.inr (.deliverOpen o)))).run
      (plainRouterState scheme κ ∅ (.opened c o) (.committed c)) =
      (fun res => (.inr .ack, plainRouterState scheme κ ∅ (.opened c o) (.finished res))) <$>
        ProbOracleComp.sample (scheme.verify κ c o) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]
  simp [bind_pure_comp]

private theorem handle_plainRouter_query_finished_empty
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (s₁ : CommitterState CommitMsg OpenMsg) (res : Option Bool) :
    ((corruptRouter ∅ (scheme.toProtocol κ ∅)).handle (Sum.inl (1, .query))).run
      (plainRouterState scheme κ ∅ s₁ (.finished res)) =
      pure (res.map CommitmentOutput.opened, plainRouterState scheme κ ∅ s₁ (.finished res)) := by
  cases res <;> rfl

private theorem handle_plainRouter_deliverCommit_zero [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (s₁ : CommitterState CommitMsg OpenMsg) (c : CommitMsg) :
    ((corruptRouter {0} (scheme.toProtocol κ {0})).handle (Sum.inr (.inr (.deliverCommit c)))).run
      (plainRouterState scheme κ {0} s₁ .waiting) =
      pure (.inr .ack, plainRouterState scheme κ {0} s₁ (.committed c)) := rfl

private theorem handle_plainRouter_query_committed_zero
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (s₁ : CommitterState CommitMsg OpenMsg) (c : CommitMsg) :
    ((corruptRouter {0} (scheme.toProtocol κ {0})).handle (Sum.inl (1, .query))).run
      (plainRouterState scheme κ {0} s₁ (.committed c)) =
      pure (some .receipt, plainRouterState scheme κ {0} s₁ (.committed c)) := rfl

private theorem handle_plainRouter_deliverOpen_zero [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (s₁ : CommitterState CommitMsg OpenMsg) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter {0} (scheme.toProtocol κ {0})).handle (Sum.inr (.inr (.deliverOpen o)))).run
      (plainRouterState scheme κ {0} s₁ (.committed c)) =
      (fun res => (.inr .ack, plainRouterState scheme κ {0} s₁ (.finished res))) <$>
        ProbOracleComp.sample (scheme.verify κ c o) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]
  simp [bind_pure_comp]

private theorem handle_plainRouter_query_finished_zero
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (s₁ : CommitterState CommitMsg OpenMsg) (res : Option Bool) :
    ((corruptRouter {0} (scheme.toProtocol κ {0})).handle (Sum.inl (1, .query))).run
      (plainRouterState scheme κ {0} s₁ (.finished res)) =
      pure (res.map CommitmentOutput.opened, plainRouterState scheme κ {0} s₁ (.finished res)) := by
  cases res <;> rfl

/-- With no corruptions (`C = ∅`) and `dummyAdversary`, running `honestCommitEnv b` on
`scheme.toProtocol` has the exact distribution `scheme.acceptGame κ b`. -/
theorem eval_exec_honestCommitEnv [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec scheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestCommitEnv b) κ z).eval =
      scheme.acceptGame κ b := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, honestCommitEnv, PlainCommitmentScheme.acceptGame,
    init_corruptRouter_toProtocol, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, map_bind]
  rw [handle_plainRouter_commit_empty]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  congr 1
  refine bind_congr fun co => ?_
  rw [handle_plainRouter_readCommit]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, map_bind]
  rw [handle_plainRouter_deliverCommit_empty]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_plainRouter_openCom_empty]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_plainRouter_readOpen]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_plainRouter_deliverOpen_empty]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  refine bind_congr fun res => ?_
  rw [handle_plainRouter_query_finished_empty]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_pure, map_pure]
  rcases res with _ | (_ | _) <;> cases b <;> rfl

/-- **Canetti–Fischlin Corrupted-Receiver Environment (`C = {1}`):** honest committer `0` commits to
`b`, the environment reads the commit message `c` from the network, honest committer `0` opens, the
environment reads the opening message `o` from the network, and the environment runs honest receiver
verification `scheme.verify κ c o` internally to test whether `res = some b`. -/
@[expose] def corruptReceiverEnv (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) := fun κ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .commit b))
  let r₁ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
    let r₂ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let res ← ProbOracleComp.sample (scheme.verify κ c o)
      return decide (res = some b)
    | _ => return false
  | _ => return false

/-- If `scheme.verify` has polynomial call budget `pV`, then `corruptReceiverEnv scheme b` has
polynomial call budget `pV + 4`. -/
theorem corruptReceiverEnv_polyBounded {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (b : Bool) : (corruptReceiverEnv scheme b).PolyBounded (pV + 4) := fun κ _ => by
  simp only [Polynomial.eval_add, Polynomial.eval_ofNat, corruptReceiverEnv]
  have h₂ (c : CommitMsg) (r₂ : Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) :
      (match r₂ with
      | .inr (.openMsg (some o)) => do
        let res ← ProbOracleComp.sample (scheme.verify κ c o)
        return decide (res = some b)
      | _ => return false :
        ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
          ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
          (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)) Bool).IsQueryBounded
        (pV.eval κ) := by
    rcases r₂ with _ | ⟨_ | o | _⟩
    · exact OracleComp.IsCostBounded.pure _ (pV.eval κ)
    · exact OracleComp.IsCostBounded.pure _ (pV.eval κ)
    · rcases o with _ | o
      · exact OracleComp.IsCostBounded.pure _ (pV.eval κ)
      · simp only [bind_pure_comp]
        exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
          (Machine.isQueryBounded_sample (hV κ c o))
    · exact OracleComp.IsCostBounded.pure _ (pV.eval κ)
  have h₁ (r₁ : Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) :
      (match r₁ with
      | .inr (.commitMsg (some c)) => do
        let _ ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
        let r₂ ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
        match r₂ with
        | .inr (.openMsg (some o)) =>
          let res ← ProbOracleComp.sample (scheme.verify κ c o)
          return decide (res = some b)
        | _ => return false
      | _ => return false :
        ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
          ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
          (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)) Bool).IsQueryBounded
        (1 + (1 + pV.eval κ)) := by
    rcases r₁ with _ | ⟨c | _ | _⟩
    · exact OracleComp.IsCostBounded.pure _ (1 + (1 + pV.eval κ))
    · rcases c with _ | c
      · exact OracleComp.IsCostBounded.pure _ (1 + (1 + pV.eval κ))
      · exact (OracleComp.IsCostBounded.query _).bind fun _ =>
          (OracleComp.IsCostBounded.query _).bind (h₂ c)
    · exact OracleComp.IsCostBounded.pure _ (1 + (1 + pV.eval κ))
    · exact OracleComp.IsCostBounded.pure _ (1 + (1 + pV.eval κ))
  exact ((OracleComp.IsCostBounded.query _).bind fun _ =>
    (OracleComp.IsCostBounded.query _).bind h₁).mono (by omega)

/-- In the real execution with `C = {1}` and `dummyAdversary`, `corruptReceiverEnv scheme b`
evaluates to `scheme.acceptGame κ b`. -/
theorem eval_exec_real_corruptReceiverEnv [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec scheme.toProtocol (dummyAdversary 2 _ _) {1} (corruptReceiverEnv scheme b) κ z).eval =
      scheme.acceptGame κ b := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, corruptReceiverEnv, PlainCommitmentScheme.acceptGame,
    init_corruptRouter_toProtocol, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, map_bind]
  rw [handle_plainRouter_commit_one]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  congr 1
  refine bind_congr fun co => ?_
  rw [handle_plainRouter_readCommit]
  simp only [Machine.closeProgram_pure, pure_bind, bind_pure_comp, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_plainRouter_openCom_one]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_plainRouter_readOpen]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_map, Machine.runFrom_sample,
    Machine.closeProgram_map, Machine.closeProgram_sample, Functor.map_map]
  rfl

/-- Pre-open commit simulation of a simulator `S₁` for `C = {1}` against the bit-independent
functionality view `fcomCommittedView`: initializes `S₁ κ {1}` and runs its activation on
`.inr .readCommit`. -/
@[expose] def simCommit (S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)) (κ : ℕ) :
    ProbComp ((Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) × (S₁ κ {1}).State) := do
  let st₀ ← (S₁ κ {1}).init
  Prod.fst <$> Machine.closeProgram
    (fcomCommittedView.runFrom (((S₁ κ {1}).handle (.inr .readCommit)).run st₀) fcomCommittedState)

/-- Post-open opening simulation of `S₁` for `C = {1}` from post-commit state `st₁` when `fcom` has
opened bit `b`. -/
@[expose] def simOpen (S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (st₁ : (S₁ κ {1}).State) :
    ProbComp (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) :=
  (Prod.fst ∘ Prod.fst) <$> Machine.closeProgram
    ((corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet (((S₁ κ {1}).handle (.inr .readOpen)).run st₁))
      (fcomRouterState κ {1} (.opened b)))

/-- If `S₁ κ {1}` has per-activation budget `t`, then `simCommit S₁ κ` makes at most `2 * t`
queries. -/
theorem isQueryBounded_simCommit {S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)} {κ t : ℕ}
    (hS : (S₁ κ {1}).IsBounded t) : (simCommit S₁ κ).IsQueryBounded (2 * t) := by
  have hstep (st₀ : (S₁ κ {1}).State) :
      (Prod.fst <$> Machine.closeProgram
        (fcomCommittedView.runFrom (((S₁ κ {1}).handle (.inr .readCommit)).run st₀)
          fcomCommittedState)).IsQueryBounded t := by
    refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
    have hrun := Machine.isQueryBounded_runFrom fcomCommittedView_isBounded
      (hS.2 (.inr .readCommit) st₀) fcomCommittedState
    rw [Nat.mul_one] at hrun
    exact Machine.isQueryBounded_closeProgram hrun
  exact (hS.1.bind hstep).mono (by omega)

/-- If `S₁ κ {1}` has per-activation budget `t`, then `simOpen S₁ b κ st₁` makes at most `t`
queries. -/
theorem isQueryBounded_simOpen {S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)} {κ t : ℕ}
    (hS : (S₁ κ {1}).IsBounded t) (b : Bool) (st₁ : (S₁ κ {1}).State) :
    (simOpen S₁ b κ st₁).IsQueryBounded t := by
  refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
  have hrun := Machine.isQueryBounded_runFrom (corruptRouter_fcom_isBounded κ {1})
    (isQueryBounded_liftNet (hS.2 (.inr .readOpen) st₁)) (fcomRouterState κ {1} (.opened b))
  rw [Nat.mul_one] at hrun
  exact Machine.isQueryBounded_closeProgram hrun

/-- First phase of the Canetti–Fischlin corrupted-committer environment (`C = {0}`), completely
independent of the target bit `b`: run `simCommit S₁ κ` and, if it produces a commit message `c`,
deliver `c` to honest receiver `1` and return `some st₁`. -/
@[expose] def corruptCommitterPrefix (S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)) (κ : ℕ) :
    ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg))
      (Option (S₁ κ {1}).State) := do
  let r₁st₁ ← ProbOracleComp.sample (simCommit S₁ κ)
  match r₁st₁.1 with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverCommit c)))
    return some r₁st₁.2
  | _ => return none

/-- Second phase of the Canetti–Fischlin corrupted-committer environment (`C = {0}`) for target bit
`b`: verify that honest receiver `1` output `some .receipt` after the commit phase, run
`simOpen S₁ b κ st₁` to obtain an equivocated opening `o` for `b`, deliver `o` to receiver `1`, and
check whether receiver `1` outputs `some (.opened b)`. -/
@[expose] def corruptCommitterSuffix (S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) :
    Option (S₁ κ {1}).State →
    ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)) Bool
  | some st₁ => do
    let recOut ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
    if recOut = some .receipt then
      let r₂ ← ProbOracleComp.sample (simOpen S₁ b κ st₁)
      match r₂ with
      | .inr (.openMsg (some o)) =>
        let _ ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _)
          (Sum.inr (.inr (.deliverOpen o)))
        let openOut ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
        return decide (openOut = some (.opened b))
      | _ => return false
    else
      return false
  | none => return false

/-- **Canetti–Fischlin Corrupted-Committer Equivocation Environment (`C = {0}`):** runs
`corruptCommitterPrefix S₁ κ` followed by `corruptCommitterSuffix S₁ b κ`. -/
@[expose] def corruptCommitterEnv (S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) := fun κ _ => do
  let pre ← corruptCommitterPrefix S₁ κ
  corruptCommitterSuffix S₁ b κ pre

/-- If `S₁` at `C = {1}` has polynomial call budget `pS`, then `corruptCommitterEnv S₁ b` has
polynomial call budget `3 * pS + 4`. -/
theorem corruptCommitterEnv_polyBounded {S₁ : Adversary 2
    ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
    (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
    ((Fin 2 × CommitmentInput) ⊕ Unit)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)} {pS : Polynomial ℕ}
    (hS : ∀ κ, (S₁ κ {1}).IsBounded (pS.eval κ)) (b : Bool) :
    (corruptCommitterEnv S₁ b).PolyBounded (3 * pS + 4) := fun κ _ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, corruptCommitterEnv]
  have hpre : (corruptCommitterPrefix S₁ κ).IsQueryBounded (2 * pS.eval κ + 1) := by
    refine (Machine.isQueryBounded_sample (isQueryBounded_simCommit (hS κ))).bind fun r₁st₁ => ?_
    rcases r₁st₁ with ⟨r₁, st₁⟩
    rcases r₁ with _ | ⟨c | _ | _⟩
    · exact OracleComp.IsCostBounded.pure _ 1
    · rcases c with _ | c
      · exact OracleComp.IsCostBounded.pure _ 1
      · simp only [bind_pure_comp]
        exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    · exact OracleComp.IsCostBounded.pure _ 1
    · exact OracleComp.IsCostBounded.pure _ 1
  have hsuf (pre : Option (S₁ κ {1}).State) :
      (corruptCommitterSuffix S₁ b κ pre).IsQueryBounded (pS.eval κ + 3) := by
    rcases pre with _ | st₁
    · exact OracleComp.IsCostBounded.pure false (pS.eval κ + 3)
    · have hopen (r₂ : Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg) :
          (match r₂ with
          | .inr (.openMsg (some o)) => do
            let _ ← ProbOracleComp.query
              (spec := execSpec 2 CommitmentInput CommitmentOutput _ _)
              (Sum.inr (.inr (.deliverOpen o)))
            let openOut ← ProbOracleComp.query
              (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
            return decide (openOut = some (.opened b))
          | _ => return false :
            ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
              ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
              (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)) Bool).IsQueryBounded
            (1 + 1) := by
        rcases r₂ with _ | ⟨_ | o | _⟩
        · exact OracleComp.IsCostBounded.pure _ (1 + 1)
        · exact OracleComp.IsCostBounded.pure _ (1 + 1)
        · rcases o with _ | o
          · exact OracleComp.IsCostBounded.pure _ (1 + 1)
          · dsimp only
            refine (OracleComp.IsCostBounded.query _).bind fun _ => ?_
            simp only [bind_pure_comp]
            exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
        · exact OracleComp.IsCostBounded.pure _ (1 + 1)
      have hrec (recOut : Option CommitmentOutput) :
          (if recOut = some .receipt then do
            let r₂ ← ProbOracleComp.sample (simOpen S₁ b κ st₁)
            match r₂ with
            | .inr (.openMsg (some o)) =>
              let _ ← ProbOracleComp.query
                (spec := execSpec 2 CommitmentInput CommitmentOutput _ _)
                (Sum.inr (.inr (.deliverOpen o)))
              let openOut ← ProbOracleComp.query
                (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
              return decide (openOut = some (.opened b))
            | _ => return false
          else
            return false :
            ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
              ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
              (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)) Bool).IsQueryBounded
            (pS.eval κ + 2) := by
        split_ifs
        · exact (Machine.isQueryBounded_sample (isQueryBounded_simOpen (hS κ) b st₁)).bind hopen
        · exact OracleComp.IsCostBounded.pure _ (pS.eval κ + 2)
      exact ((OracleComp.IsCostBounded.query _).bind hrec).mono (by omega)
  exact (hpre.bind hsuf).mono (by omega)

/-- The common closed probabilistic program underlying both the ideal corrupted-receiver execution
(`exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b)`) and the real corrupted-committer
execution (`exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b)`). -/
@[expose] def simulatedTranscriptGame (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) : ProbComp Bool := do
  let r₁st₁ ← simCommit S₁ κ
  match r₁st₁.1 with
  | .inr (.commitMsg (some c)) =>
    let r₂ ← simOpen S₁ b κ r₁st₁.2
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let res ← scheme.verify κ c o
      return decide (res = some b)
    | _ => return false
  | _ => return false

/-- `(st, s)` viewed as a state of `execMachine fcom.toProtocol S κ C`. -/
@[expose] def fcomExecState {AdvQ AdvR : Type}
    (S : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (C : Finset (Fin 2)) (st : (S κ C).State) (s : CommitmentState) :
    (execMachine fcom.toProtocol S κ C).State := (st, s)

private theorem init_execMachine_fcom {AdvQ AdvR : Type}
    (S : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (C : Finset (Fin 2)) :
    (execMachine fcom.toProtocol S κ C).init =
      (fun sA => fcomExecState S κ C sA .idle) <$> (S κ C).init := by
  simp only [execMachine, Machine.comp, liftAdversary, corruptRouter, fcom,
    IdealFunctionality.toProtocol, fcomExecState, pure_bind, bind_pure_comp]

private theorem handle_execMachine_fcom_commit {AdvQ AdvR : Type}
    (S₁ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (st₀ : (S₁ κ {1}).State) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inl (0, .commit b))).run
      (fcomExecState S₁ κ {1} st₀ .idle) =
      pure (some .receipt, fcomExecState S₁ κ {1} st₀ (.committed b)) := rfl

private theorem handle_execMachine_fcom_openCom {AdvQ AdvR : Type}
    (S₁ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (st₁ : (S₁ κ {1}).State) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inl (0, .openCom))).run
      (fcomExecState S₁ κ {1} st₁ (.committed b)) =
      pure (some (.opened b), fcomExecState S₁ κ {1} st₁ (.opened b)) := rfl

/-- Extract the underlying `CommitmentState` from
`(corruptRouter C (fcom.toProtocol κ C)).State`. -/
@[expose] def fcomRouterStateVal (κ : ℕ) (C : Finset (Fin 2))
    (s : (corruptRouter C (fcom.toProtocol κ C)).State) : CommitmentState := s

/-- Embed a reply `r : AdvR` as a result of `execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR`
on query `Sum.inr q`. -/
@[expose] def execReplyInr {AdvQ AdvR : Type} (q : AdvQ) (r : AdvR) :
    execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR (Sum.inr q) := r

private theorem handle_execMachine_fcom_committed_inr {AdvQ AdvR : Type}
    (S₁ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (q : AdvQ) (st₀ : (S₁ κ {1}).State) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inr q)).run
      (fcomExecState S₁ κ {1} st₀ (.committed b)) =
      (fun x : (AdvR × (S₁ κ {1}).State) × fcomCommittedView.State =>
        (execReplyInr q x.1.1, fcomExecState S₁ κ {1} x.1.2 (.committed b))) <$>
        fcomCommittedView.runFrom (((S₁ κ {1}).handle q).run st₀) fcomCommittedState := by
  change Equiv.prodAssoc _ _ _ <$>
    (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet (((S₁ κ {1}).handle q).run st₀)) (fcomRouterState κ {1} (.committed b)) = _
  rw [runFrom_fcom_committed κ b, Functor.map_map]
  rfl

private theorem handle_execMachine_fcom_opened_inr {AdvQ AdvR : Type}
    (S₁ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (q : AdvQ) (st₁ : (S₁ κ {1}).State) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inr q)).run
      (fcomExecState S₁ κ {1} st₁ (.opened b)) =
      (fun x : (AdvR × (S₁ κ {1}).State) ×
          (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).State =>
        (execReplyInr q x.1.1,
          fcomExecState S₁ κ {1} x.1.2 (fcomRouterStateVal κ {1} x.2))) <$>
        (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
          (liftNet (((S₁ κ {1}).handle q).run st₁))
          (fcomRouterState κ {1} (.opened b)) := rfl

/-- In the ideal world with `C = {1}`, running `corruptReceiverEnv scheme b` with simulator `S₁`
against `fcom` produces `simulatedTranscriptGame scheme S₁ b κ`. -/
theorem exec_fcom_corruptReceiverEnv_eq (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (z : List Bool) :
    exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z =
      simulatedTranscriptGame scheme S₁ b κ := by
  simp only [exec, Machine.run, Machine.link, init_execMachine_fcom,
    Machine.closeProgram_bind, Machine.closeProgram_sample, bind_map_left,
    simulatedTranscriptGame, simCommit, simOpen, bind_assoc]
  refine bind_congr fun st₀ => ?_
  simp only [corruptReceiverEnv, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, map_bind]
  rw [handle_execMachine_fcom_commit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_execMachine_fcom_committed_inr]
  simp only [Machine.closeProgram_map, bind_map_left]
  refine bind_congr fun x => ?_
  rcases x with ⟨⟨r₁, st₁⟩, sV⟩
  rcases r₁ with _ | ⟨c | _ | _⟩
  · rfl
  · rcases c with _ | c
    · rfl
    · simp only [execReplyInr, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.closeProgram_bind, map_bind]
      rw [handle_execMachine_fcom_openCom]
      simp only [Machine.closeProgram_pure, pure_bind]
      rw [handle_execMachine_fcom_opened_inr]
      simp only [Machine.closeProgram_map, bind_map_left]
      refine bind_congr fun y => ?_
      rcases y with ⟨⟨r₂, st₂⟩, sP⟩
      rcases r₂ with _ | ⟨_ | o | _⟩
      · rfl
      · rfl
      · rcases o with _ | o
        · rfl
        · simp only [execReplyInr, bind_pure_comp, Machine.runFrom_map, Machine.runFrom_sample,
            Machine.closeProgram_map, Machine.closeProgram_sample, Functor.map_map]
          rfl
      · rfl
  · rfl
  · rfl

/-- In the real world with `C = {0}` and `dummyAdversary`, running `corruptCommitterEnv S₁ b`
against `scheme.toProtocol` also produces `simulatedTranscriptGame scheme S₁ b κ`. -/
theorem exec_real_corruptCommitterEnv_eq [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (z : List Bool) :
    exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b) κ z =
      simulatedTranscriptGame scheme S₁ b κ := by
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, corruptCommitterEnv, corruptCommitterPrefix,
    simulatedTranscriptGame, init_corruptRouter_toProtocol, bind_assoc,
    Machine.runFrom_bind, Machine.runFrom_sample,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, bind_map_left, map_bind]
  refine bind_congr fun r₁st₁ => ?_
  rcases r₁st₁ with ⟨r₁, st₁⟩
  rcases r₁ with _ | ⟨c | _ | _⟩
  · rfl
  · rcases c with _ | c
    · rfl
    · simp only [bind_pure_comp, Machine.runFrom_map, Machine.runFrom_query,
        Machine.closeProgram_map]
      rw [handle_plainRouter_deliverCommit_zero]
      simp only [corruptCommitterSuffix, map_pure, Prod.map_apply, _root_.id_eq,
        Machine.closeProgram_pure, pure_bind, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.closeProgram_bind, map_bind]
      rw [handle_plainRouter_query_committed_zero]
      simp only [Machine.closeProgram_pure, pure_bind, ↓reduceIte,
        Machine.runFrom_bind, Machine.runFrom_sample,
        Machine.closeProgram_bind, Machine.closeProgram_sample,
        bind_map_left, map_bind]
      refine bind_congr fun r₂ => ?_
      rcases r₂ with _ | ⟨_ | o | _⟩
      · rfl
      · rfl
      · rcases o with _ | o
        · rfl
        · simp only [Machine.runFrom_bind, Machine.runFrom_query,
            Machine.closeProgram_bind, map_bind]
          rw [handle_plainRouter_deliverOpen_zero]
          simp only [Machine.closeProgram_map, Machine.closeProgram_sample,
            bind_map_left]
          rw [← bind_pure_comp]
          refine bind_congr fun res => ?_
          rw [handle_plainRouter_query_finished_zero]
          simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_pure, map_pure]
          rcases res with _ | (_ | _) <;> cases b <;> rfl
      · rfl
  · rfl
  · rfl

/-- **Plain-Model Man-in-the-Middle Equivocation Identity:** the real execution of
`corruptCommitterEnv S₁ b` (`C = {0}`) with `dummyAdversary` equals the ideal execution of
`corruptReceiverEnv scheme b` (`C = {1}`) with simulator `S₁`. -/
theorem exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (z₁ z₂ : List Bool) :
    exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b) κ z₁ =
      exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₂ := by
  rw [exec_real_corruptCommitterEnv_eq, exec_fcom_corruptReceiverEnv_eq]

/-! ### Ideal-world binding bound for `corruptCommitterEnv` -/

/-- Output of `fcomLocked bStar` on a receiver query `.query` in state `opened`. -/
@[expose] def fcomLockedReply (bStar : Bool) : Bool → CommitmentOutput
  | false => .receipt
  | true => .opened bStar

/-- `(st, opened)` viewed as a state of
`(liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))`. -/
@[expose] def fcomLockedState {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ) (st : (S₀ κ {0}).State) (opened : Bool) :
    ((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).State :=
  (st, opened)

/-- `opened` viewed as a state of `corruptRouter {0} (fcomLocked bStar)`. -/
@[expose] def fcomLockedRouterState (bStar : Bool) (opened : Bool) :
    (corruptRouter ({0} : Finset (Fin 2)) (fcomLocked bStar)).State := opened

/-- Extract the underlying `Bool` state from `(corruptRouter {0} (fcomLocked bStar)).State`. -/
@[expose] def fcomLockedRouterBool (bStar : Bool)
    (s : (corruptRouter ({0} : Finset (Fin 2)) (fcomLocked bStar)).State) : Bool := s

private theorem closeProgram_fst_runFrom_execMachine_fcom_locked {AdvQ AdvR α : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ)
    (program : ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR) α)
    (stS₀ : (S₀ κ {0}).State) (opened : Bool) :
    Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        program (fcomExecState S₀ κ {0} stS₀ (CommitmentState.locked bStar opened))) =
      Prod.fst <$> Machine.closeProgram
        (((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).runFrom
          program (fcomLockedState S₀ bStar κ stS₀ opened)) := by
  change Prod.fst <$> Machine.closeProgram
    ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
      program (stS₀, CommitmentState.locked bStar opened)) = _
  rw [runFrom_execMachine_fcom_locked S₀ κ {0} bStar program stS₀ opened]
  erw [Machine.closeProgram_map, Functor.map_map]
  rfl

private theorem handle_fcomLocked_query_one {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ) (st : (S₀ κ {0}).State) (opened : Bool) :
    (((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).handle
      (Sum.inl (1, .query))).run (fcomLockedState S₀ bStar κ st opened) =
      pure (some (fcomLockedReply bStar opened), fcomLockedState S₀ bStar κ st opened) := by
  cases opened <;> rfl

private theorem handle_fcomLocked_inr {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ) (q : AdvQ) (st : (S₀ κ {0}).State) (opened : Bool) :
    (((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).handle
      (Sum.inr q)).run (fcomLockedState S₀ bStar κ st opened) =
      (fun x : (AdvR × (S₀ κ {0}).State) ×
          (corruptRouter ({0} : Finset (Fin 2)) (fcomLocked bStar)).State =>
        (execReplyInr q x.1.1,
          fcomLockedState S₀ bStar κ x.1.2 (fcomLockedRouterBool bStar x.2))) <$>
        (corruptRouter ({0} : Finset (Fin 2)) (fcomLocked bStar)).runFrom
          (liftNet (((S₀ κ {0}).handle q).run st)) (fcomLockedRouterState bStar opened) := rfl

private theorem handle_execMachine_fcom_query_one_idle {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (st : (S₀ κ {0}).State) :
    ((execMachine fcom.toProtocol S₀ κ {0}).handle (Sum.inl (1, .query))).run
      (fcomExecState S₀ κ {0} st .idle) =
      pure ((none : execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR (Sum.inl (1, .query))),
        fcomExecState S₀ κ {0} st .idle) := rfl

private theorem handle_execMachine_fcom_query_one_opened {AdvQ AdvR : Type}
    (S₀ : Adversary 2 AdvQ AdvR
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ) (st : (S₀ κ {0}).State) :
    ((execMachine fcom.toProtocol S₀ κ {0}).handle (Sum.inl (1, .query))).run
      (fcomExecState S₀ κ {0} st (.opened bStar)) =
      pure ((some (.opened bStar) :
          execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR (Sum.inl (1, .query))),
        fcomExecState S₀ κ {0} st (.opened bStar)) := rfl

private theorem pmf_bind_eq_pure {α β : Type} (p : PMF α) (f : α → PMF β) (b : β)
    (h : ∀ a, f a = PMF.pure b) : (p >>= f) = PMF.pure b := by
  change p.bind f = PMF.pure b
  simp only [funext h, PMF.bind_const]

/-- When `fcom` is locked to `bStar` (state `.committed bStar`), running
`corruptCommitterSuffix S₁ (!bStar) κ (some st₁)` against `execMachine fcom.toProtocol S₀ κ {0}`
always outputs `false`. -/
theorem eval_corruptCommitterSuffix_locked_not
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (bStar : Bool) (κ : ℕ) (st₁ : (S₁ κ {1}).State) (stS₀ : (S₀ κ {0}).State) :
    (Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        (corruptCommitterSuffix S₁ (!bStar) κ (some st₁))
        (fcomExecState S₀ κ {0} stS₀ (.committed bStar)))).eval = PMF.pure false := by
  rw [show CommitmentState.committed bStar = CommitmentState.locked bStar false from rfl,
    closeProgram_fst_runFrom_execMachine_fcom_locked]
  simp only [corruptCommitterSuffix, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, map_bind]
  rw [handle_fcomLocked_query_one]
  simp only [fcomLockedReply, Machine.closeProgram_pure, pure_bind, ↓reduceIte,
    Machine.runFrom_bind, Machine.runFrom_sample,
    Machine.closeProgram_bind, Machine.closeProgram_sample,
    bind_map_left, map_bind, ProbComp.eval_bind]
  refine pmf_bind_eq_pure _ _ false fun r₂ => ?_
  rcases r₂ with _ | ⟨_ | o | _⟩
  · rfl
  · rfl
  · rcases o with _ | o
    · rfl
    · simp only [bind_pure_comp, Machine.runFrom_bind, Machine.runFrom_query,
        Machine.runFrom_map, Machine.closeProgram_bind, Machine.closeProgram_map,
        map_bind, Functor.map_map]
      rw [handle_fcomLocked_inr]
      simp only [Machine.closeProgram_map, bind_map_left, ProbComp.eval_bind]
      refine pmf_bind_eq_pure _ _ false fun x => ?_
      rw [handle_fcomLocked_query_one]
      cases fcomLockedRouterBool bStar x.2 <;> cases bStar <;> rfl
  · rfl

private theorem succProbability_pure_false : Game.succProbability (PMF.pure false) = 0 := by
  simp [Game.succProbability, PMF.pure_apply]

/-- Pointwise bound after `corruptCommitterPrefix`: for every intermediate state `x` reached after
`corruptCommitterPrefix S₁ κ`, the sum of the success probabilities of
`corruptCommitterSuffix S₁ false κ x.1` and `corruptCommitterSuffix S₁ true κ x.1` from state `x.2`
is at most `1`. -/
theorem succProbability_corruptCommitterSuffix_add_le_one
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (x : Option (S₁ κ {1}).State × (execMachine fcom.toProtocol S₀ κ {0}).State) :
    Game.succProbability (Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        (corruptCommitterSuffix S₁ false κ x.1) x.2)).eval +
    Game.succProbability (Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        (corruptCommitterSuffix S₁ true κ x.1) x.2)).eval ≤ 1 := by
  rcases x with ⟨pre, st⟩
  let stS₀ : (S₀ κ {0}).State := st.1
  let sP : CommitmentState := st.2
  change Game.succProbability (Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        (corruptCommitterSuffix S₁ false κ pre) (fcomExecState S₀ κ {0} stS₀ sP))).eval +
    Game.succProbability (Prod.fst <$> Machine.closeProgram
      ((execMachine fcom.toProtocol S₀ κ {0}).runFrom
        (corruptCommitterSuffix S₁ true κ pre) (fcomExecState S₀ κ {0} stS₀ sP))).eval ≤ 1
  clear_value stS₀ sP
  clear st
  rcases pre with _ | st₁
  · simp [corruptCommitterSuffix, Game.succProbability]
  · rcases sP with _ | bStar | bStar
    · simp only [corruptCommitterSuffix, Machine.runFrom_bind, Machine.runFrom_query]
      rw [handle_execMachine_fcom_query_one_idle]
      simp [Game.succProbability]
    · cases bStar
      · have htrue := eval_corruptCommitterSuffix_locked_not S₁ S₀ false κ st₁ stS₀
        simp only [Bool.not_false] at htrue
        rw [htrue, succProbability_pure_false, add_zero]
        exact Game.succProbability_le_one _
      · have hfalse := eval_corruptCommitterSuffix_locked_not S₁ S₀ true κ st₁ stS₀
        simp only [Bool.not_true] at hfalse
        rw [hfalse, succProbability_pure_false, zero_add]
        exact Game.succProbability_le_one _
    · simp only [corruptCommitterSuffix, Machine.runFrom_bind, Machine.runFrom_query]
      rw [handle_execMachine_fcom_query_one_opened]
      simp [Game.succProbability]

/-- **Ideal-World Binding Inequality for `corruptCommitterEnv`:** for every simulator `S₀`
(`C = {0}`) and every simulator `S₁` (`C = {1}`), the ideal success probabilities of
`corruptCommitterEnv S₁ false` and `corruptCommitterEnv S₁ true` against `fcom` sum to at most
`1`. -/
theorem succProbability_exec_fcom_corruptCommitterEnv_add_le_one
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (z₁ z₂ : List Bool) :
    Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ false) κ z₁).eval +
      Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ true) κ z₂).eval ≤
      1 := by
  let M₀ := execMachine fcom.toProtocol S₀ κ {0}
  let preDist : PMF (Option (S₁ κ {1}).State × M₀.State) :=
    (M₀.init >>= fun s₀ => Machine.closeProgram (M₀.runFrom (corruptCommitterPrefix S₁ κ) s₀)).eval
  let sufDist (b : Bool) (x : Option (S₁ κ {1}).State × M₀.State) : PMF Bool :=
    (Prod.fst <$> Machine.closeProgram (M₀.runFrom (corruptCommitterSuffix S₁ b κ x.1) x.2)).eval
  have hexec (b : Bool) (z : List Bool) :
      (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z).eval =
        preDist.bind (sufDist b) := by
    simp only [exec, Machine.run, Machine.link, corruptCommitterEnv, preDist, sufDist, M₀,
      Machine.runFrom_bind, Machine.closeProgram_bind, Machine.closeProgram_map,
      Machine.closeProgram_sample, map_bind, ProbComp.eval_bind, PMF.bind_bind]
  rw [hexec false z₁, hexec true z₂, ← NNReal.coe_le_coe]
  simp only [NNReal.coe_add, NNReal.coe_one, Game.coe_succProbability,
    Probability.PMF.bind_apply_toReal_tsum]
  have hsum_add :
      (∑' x, (preDist x).toReal * (sufDist false x true).toReal) +
        (∑' x, (preDist x).toReal * (sufDist true x true).toReal) =
      ∑' x, (preDist x).toReal *
        ((sufDist false x true).toReal + (sufDist true x true).toReal) := by
    rw [← Summable.tsum_add]
    · refine tsum_congr fun x => ?_
      ring
    · exact Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg
          (by simpa [Game.coe_succProbability] using
            NNReal.coe_le_coe.mpr (Game.succProbability_le_one (sufDist false x))))
        (Probability.PMF.summable_toReal preDist)
    · exact Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg
          (by simpa [Game.coe_succProbability] using
            NNReal.coe_le_coe.mpr (Game.succProbability_le_one (sufDist true x))))
        (Probability.PMF.summable_toReal preDist)
  rw [hsum_add]
  calc
    (∑' x, (preDist x).toReal *
        ((sufDist false x true).toReal + (sufDist true x true).toReal)) ≤
      ∑' x, (preDist x).toReal * 1 := by
      refine Summable.tsum_le_tsum (fun x => ?_) ?_ ?_
      · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hle := NNReal.coe_le_coe.mpr
          (succProbability_corruptCommitterSuffix_add_le_one S₁ S₀ κ x)
        simpa only [NNReal.coe_add, NNReal.coe_one, Game.coe_succProbability, sufDist, M₀] using hle
      · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun x => ?_)
          (Probability.PMF.summable_toReal preDist)
        have hle := NNReal.coe_le_coe.mpr
          (succProbability_corruptCommitterSuffix_add_le_one S₁ S₀ κ x)
        have hle' : (sufDist false x true).toReal + (sufDist true x true).toReal ≤ 1 := by
          simpa only [NNReal.coe_add, NNReal.coe_one, Game.coe_succProbability, sufDist, M₀]
            using hle
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg hle'
      · simpa only [mul_one] using Probability.PMF.summable_toReal preDist
    _ = 1 := by simp [Probability.PMF.tsum_toReal]

/-! ### Canetti–Fischlin quantitative trade-off and impossibility theorems -/

/-- For each bit `b`, the honest acceptance probability `scheme.acceptProb κ b` is bounded by the
ideal equivocation success probability plus the $C = \{1\}$ and $C = \{0\}$ distinguishing
advantages. -/
theorem acceptProb_le_ideal_add_advantage [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (b : Bool) (κ : ℕ) (z₁ z₀ : List Bool) :
    scheme.acceptProb κ b ≤
      Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z₀).eval +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme b) κ z₁ +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ b) κ z₀ := by
  rw [← NNReal.coe_le_coe]
  simp only [PlainCommitmentScheme.acceptProb, ← eval_exec_real_corruptReceiverEnv scheme b κ z₁,
    advantage, NNReal.coe_add, Game.coe_advantage]
  have heq :
      Game.succProbability
        (exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b) κ z₀).eval =
      Game.succProbability
        (exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₁).eval := by
    rw [exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv scheme S₁ b κ z₀ z₁]
  rw [heq]
  have h1 := le_abs_self
    ((Game.succProbability
      (exec scheme.toProtocol (dummyAdversary 2 _ _) {1}
        (corruptReceiverEnv scheme b) κ z₁).eval : ℝ) -
     Game.succProbability (exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₁).eval)
  have h2 := le_abs_self
    ((Game.succProbability
      (exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₁).eval : ℝ) -
     Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z₀).eval)
  linarith

/-- **Canetti–Fischlin Quantitative Trade-off ([CanettiFischlin2001], Theorem 1):** for any
plain-model commitment scheme `scheme` and any simulators `S₁` (for `C = {1}`) and `S₀` (for
`C = {0}`), the sum of `scheme.acceptProb κ false` and `scheme.acceptProb κ true` is at most `1`
plus the four distinguishing advantages of `corruptReceiverEnv` and `corruptCommitterEnv` on `false`
and `true`. -/
theorem acceptProb_add_le_one_add_advantage [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ S₀ : Adversary 2
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ CommitMsg OpenMsg)
      (Option CommitmentOutput ⊕ PlainNetR CommitMsg OpenMsg)
      ((Fin 2 × CommitmentInput) ⊕ Unit)
      (Option CommitmentOutput ⊕ Option CommitmentOutput))
    (κ : ℕ) (z : List Bool) :
    scheme.acceptProb κ false + scheme.acceptProb κ true ≤
      1 +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme true) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
  have hfalse := acceptProb_le_ideal_add_advantage scheme S₁ S₀ false κ z z
  have htrue := acceptProb_le_ideal_add_advantage scheme S₁ S₀ true κ z z
  have hideal := succProbability_exec_fcom_corruptCommitterEnv_add_le_one S₁ S₀ κ z z
  calc
    scheme.acceptProb κ false + scheme.acceptProb κ true ≤
      (Game.succProbability
          (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ false) κ z).eval +
        Game.succProbability
          (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ true) κ z).eval) +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme true) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
      rw [← NNReal.coe_le_coe] at hfalse htrue ⊢
      push_cast at hfalse htrue ⊢
      linarith
    _ ≤ 1 +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme true) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
      gcongr

/-- **Concrete Impossibility against the Dummy Adversary:** if `scheme.verify` has polynomial call
budget `pV` and at security parameter `κ` the error bound `ε` satisfies
`1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ <
  scheme.acceptProb κ false + scheme.acceptProb κ true`,
then `scheme.toProtocol` does not emulate `fcom.toProtocol` against the dummy adversary within
`(pD, ε)`. -/
theorem not_emulatesDummyWithin_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ)
    (hgap : 1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ <
      scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ EmulatesDummyWithin scheme.toProtocol fcom.toProtocol pD ε := by
  rintro ⟨S, hS_poly, hadv⟩
  have hS1 : ∀ κ', (S κ' {1}).IsBounded (pD.eval κ') := fun κ' => hS_poly κ' {1}
  have h1_false := hadv {1} (corruptReceiverEnv scheme false) (pV + 4)
    (corruptReceiverEnv_polyBounded hV false) κ []
  have h1_true := hadv {1} (corruptReceiverEnv scheme true) (pV + 4)
    (corruptReceiverEnv_polyBounded hV true) κ []
  have h0_false := hadv {0} (corruptCommitterEnv S false) (3 * pD + 4)
    (corruptCommitterEnv_polyBounded hS1 false) κ []
  have h0_true := hadv {0} (corruptCommitterEnv S true) (3 * pD + 4)
    (corruptCommitterEnv_polyBounded hS1 true) κ []
  have hbound := acceptProb_add_le_one_add_advantage scheme S S κ []
  have hle : scheme.acceptProb κ false + scheme.acceptProb κ true ≤
      1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ := by
    rw [← NNReal.coe_le_coe] at h1_false h1_true h0_false h0_true hbound ⊢
    push_cast at h1_false h1_true h0_false h0_true hbound ⊢
    linarith
  exact not_lt_of_ge hle hgap

/-- **Concrete Impossibility of UC Bit Commitment (`RealizesWithin`):** if `scheme.verify` has
polynomial call budget `pV` and at security parameter `κ`, for every dummy-adversary simulator
budget `pD` with `SimPolyBound g 1 pD`, the error bound `ε` satisfies
`1 + 2 * ε 1 (pV + 4) κ + 2 * ε 1 (3 * pD + 4) κ <
  scheme.acceptProb κ false + scheme.acceptProb κ true`,
then `scheme.toProtocol` does not UC-realize `fcom` within `(g, ε)`. -/
theorem not_realizesWithin_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ)
    (hgap : ∀ pD, SimPolyBound g 1 pD →
      1 + 2 * ε 1 (pV + 4) κ + 2 * ε 1 (3 * pD + 4) κ <
        scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ RealizesWithin scheme.toProtocol fcom g ε := by
  intro hreal
  obtain ⟨pD, hg, hdummy⟩ := hreal.emulatesDummyWithin
  exact not_emulatesDummyWithin_fcom hV pD (ε 1) κ (hgap pD hg) hdummy

/-- **Canetti–Fischlin Impossibility Theorem ([CanettiFischlin2001], Theorem 1):** no plain-model
two-party commitment scheme whose verification is polynomial-call bounded and whose honest
acceptance probabilities on `false` and `true` eventually sum to at least `1 + c` (for some `c > 0`)
can UC-realize `fcom`. -/
theorem not_realizes_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    {c : ℝ≥0} (hc : 0 < c)
    (hcomplete : ∀ᶠ κ in Filter.atTop,
      1 + c ≤ scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ Realizes scheme.toProtocol fcom := by
  intro hreal
  obtain ⟨S, pD, hS_poly, hsim⟩ := (emulates_iff_emulatesDummy _ _).mp hreal
  have hS1 : ∀ κ, (S κ {1}).IsBounded (pD.eval κ) := fun κ => hS_poly κ {1}
  obtain ⟨ε₁, hε₁_neg, hε₁⟩ := hsim (pV + 4)
  obtain ⟨ε₀, hε₀_neg, hε₀⟩ := hsim (3 * pD + 4)
  have hneg : Negligible (fun κ => 2 * ε₁ κ + 2 * ε₀ κ) :=
    (hε₁_neg.const_mul 2).add (hε₀_neg.const_mul 2)
  have ht : Filter.Tendsto (fun κ => 2 * ε₁ κ + 2 * ε₀ κ) Filter.atTop (nhds 0) := by
    simpa using hneg 0
  have hlt : ∀ᶠ κ in Filter.atTop, 2 * ε₁ κ + 2 * ε₀ κ < c := ht.eventually_lt_const hc
  obtain ⟨κ, hκ_complete, hκ_lt⟩ := (hcomplete.and hlt).exists
  have h1_false := hε₁ {1} (corruptReceiverEnv scheme false)
    (corruptReceiverEnv_polyBounded hV false) κ []
  have h1_true := hε₁ {1} (corruptReceiverEnv scheme true)
    (corruptReceiverEnv_polyBounded hV true) κ []
  have h0_false := hε₀ {0} (corruptCommitterEnv S false)
    (corruptCommitterEnv_polyBounded hS1 false) κ []
  have h0_true := hε₀ {0} (corruptCommitterEnv S true)
    (corruptCommitterEnv_polyBounded hS1 true) κ []
  have hbound := acceptProb_add_le_one_add_advantage scheme S S κ []
  rw [← NNReal.coe_le_coe] at hκ_complete h1_false h1_true h0_false h0_true hbound
  rw [← NNReal.coe_lt_coe] at hκ_lt
  push_cast at hκ_complete hκ_lt h1_false h1_true h0_false h0_true hbound
  linarith

/-- **Canetti–Fischlin Impossibility for Perfectly Complete Schemes:** no perfectly complete
plain-model commitment scheme with polynomial-call bounded verification can UC-realize `fcom`. -/
theorem not_realizes_fcom_of_perfectlyComplete [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (hcomplete : scheme.PerfectlyComplete) :
    ¬ Realizes scheme.toProtocol fcom := by
  refine not_realizes_fcom hV (c := 1) zero_lt_one (Filter.Eventually.of_forall fun κ => ?_)
  rw [hcomplete κ false, hcomplete κ true]

end Environments

end Cslib.Crypto.Protocols.UC
