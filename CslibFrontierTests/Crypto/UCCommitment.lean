/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.Commitment

/-!
# Tests for ideal UC bit commitment and the Canetti–Fischlin impossibility theorem

We verify non-vacuity and concrete behavior of `fcom` and `PlainCommitmentScheme`:
1. `trivialScheme` commits by sending the bit `b` in the clear (`commit _ b := pure (b, ())`,
   `verify _ c _ := pure (some c)`): it is deterministic (`IsPolyBounded 0 0`) and perfectly
   complete (`trivialScheme_perfectlyComplete`), so its honest UC execution (`C = ∅`) succeeds with
   probability `1`, yet by Canetti–Fischlin it cannot UC-realize `fcom`
   (`not_realizes_trivialScheme`) or emulate `fcom` within error `1 / 5`
   (`not_realizesWithin_trivialScheme`).
2. `oneTimePadScheme` masks the committed bit with a uniform Boolean pad `r` in the commit phase
   (`c = b ^^ r`, `o = r`) and unmasks `c ^^ o` on opening: its commit message alone is
   information-theoretically hiding, it is polynomial-call bounded (`IsPolyBounded 1 0`) and
   perfectly complete (`oneTimePadScheme_perfectlyComplete`). In the uncorrupted case (`C = ∅`)
   the explicit simulator `oneTimePadEmptySim` perfectly simulates two fixed honest schedules:
   `honestCommitEnv` (`advantage_oneTimePadEmptySim_honestCommitEnv`) and every predicate of the
   eight fields of `HonestView` recorded by the ten-query schedule `honestViewEnv` (committer
   replies, receiver replies before and after each delivery, and the `(c, o)` transcript;
   `advantage_oneTimePadEmptySim_honestViewEnv`). This is not a simulation of every `C = ∅`
   environment. Nevertheless, by the Canetti–Fischlin argument it cannot UC-realize `fcom` against
   static corruptions (`not_realizes_oneTimePadScheme`).
-/

namespace CslibFrontierTests.Crypto.UCCommitment

open Polynomial
open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal

/-- Deterministic plain-model commitment scheme that sends `b` as the commit message and `()` as the
opening message. -/
def trivialScheme : PlainCommitmentScheme Bool Unit where
  commit _ b := pure (b, ())
  verify _ c _ := pure (some c)

theorem trivialScheme_isPolyBounded : trivialScheme.IsPolyBounded 0 0 := by
  refine ⟨fun κ b => ?_, fun κ c o => ?_⟩
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0

theorem trivialScheme_toProtocol_polyBounded : trivialScheme.toProtocol.PolyBounded (0 + 0) :=
  trivialScheme.toProtocol_polyBounded trivialScheme_isPolyBounded

@[simp] theorem acceptGame_trivialScheme (κ : ℕ) (b : Bool) :
    trivialScheme.acceptGame κ b = PMF.pure true := by
  simp [PlainCommitmentScheme.acceptGame, trivialScheme]

@[simp] theorem acceptProb_trivialScheme (κ : ℕ) (b : Bool) :
    trivialScheme.acceptProb κ b = 1 := by
  simp [PlainCommitmentScheme.acceptProb, Game.succProbability]

theorem trivialScheme_perfectlyComplete : trivialScheme.PerfectlyComplete :=
  acceptProb_trivialScheme

/-- Honest UC execution (`C = ∅`) of `trivialScheme` with `honestCommitEnv b` outputs `true` with
certainty. -/
example (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec trivialScheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestCommitEnv b) κ z).eval =
      PMF.pure true := by
  rw [eval_exec_honestCommitEnv, acceptGame_trivialScheme]

/-- Concrete Canetti–Fischlin bound for `trivialScheme`: for every pair of simulators `S₁, S₀`, the
four distinguishing advantages of `corruptReceiverEnv` and `corruptCommitterEnv` sum to at least
`1`. -/
theorem one_le_sum_advantage_trivialScheme
    (S₁ S₀ : PlainCommitmentSim Bool Unit)
    (κ : ℕ) (z : List Bool) :
    1 ≤
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv trivialScheme false) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv trivialScheme true) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage trivialScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
  have h := acceptProb_add_le_one_add_advantage trivialScheme S₁ S₀ κ z
  rw [acceptProb_trivialScheme, acceptProb_trivialScheme] at h
  rw [← NNReal.coe_le_coe] at h ⊢
  push_cast at h ⊢
  linarith

/-- Concrete impossibility: `trivialScheme` cannot UC-realize `fcom` within constant error `1 / 5`
for any simulator budget polynomial `g`. -/
theorem not_realizesWithin_trivialScheme (g : Polynomial ℕ) :
    ¬ RealizesWithin trivialScheme.toProtocol fcom g (fun _ _ _ => (1 / 5 : ℝ≥0)) := by
  refine not_realizesWithin_fcom (pV := 0) trivialScheme_isPolyBounded.2 g
    (fun _ _ _ => (1 / 5 : ℝ≥0)) 0 ?_
  rw [acceptProb_trivialScheme, acceptProb_trivialScheme]
  norm_num

/-- Asymptotic impossibility: `trivialScheme` does not UC-realize `fcom`. -/
theorem not_realizes_trivialScheme : ¬ Realizes trivialScheme.toProtocol fcom :=
  not_realizes_fcom_of_perfectlyComplete trivialScheme_isPolyBounded.2
    trivialScheme_perfectlyComplete

/-- Randomized one-time-pad commitment scheme: commits to `b` by sampling a uniform Boolean mask
`r ← unifFin 1` (`decide (r = 1)`) and sending `c = b ^^ mask` with opening `o = mask`. -/
def oneTimePadScheme : PlainCommitmentScheme Bool Bool where
  commit _ b := do
    let r ← ProbComp.unifFin 1
    let mask := decide (r.val = 1)
    return (b ^^ mask, mask)
  verify _ c o := pure (some (c ^^ o))

theorem oneTimePadScheme_isPolyBounded : oneTimePadScheme.IsPolyBounded 1 0 := by
  refine ⟨fun κ b => ?_, fun κ c o => ?_⟩
  · rw [Polynomial.eval_one]
    simp only [oneTimePadScheme, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query 1)
  · rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0

theorem oneTimePadScheme_perfectlyComplete : oneTimePadScheme.PerfectlyComplete := fun κ b => by
  have hxor (r : Fin 2) :
      decide (some ((b ^^ decide (r.val = 1)) ^^ decide (r.val = 1)) = some b) = true := by
    cases b <;> fin_cases r <;> rfl
  simp only [PlainCommitmentScheme.acceptProb, PlainCommitmentScheme.acceptGame, oneTimePadScheme,
    bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_pure, hxor, PMF.bind_const,
    Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]

/-- The ideal network port specification of `fcom`. -/
abbrev fcomIdealNet :=
  netSpec ((Fin 2 × CommitmentInput) ⊕ CommitmentBackdoor)
    (Option CommitmentOutput ⊕ Option CommitmentOutput)

/-- Explicit simulator for `oneTimePadScheme` in the uncorrupted case (`C = ∅`): when a commitment
is recorded in `fcom`, `.readCommit` samples and caches a uniform commit bit `c`; `.deliverCommit`
gates receipt delivery in `fcom` via `.deliverCommit`; once `fcom` reveals `some (.opened b)` on
`.query`, `.readOpen` computes `o := c ^^ b`; and `.deliverOpen` gates opening delivery in
`fcom` via `.deliverOpen`.

It forwards `.deliverCommit _` and `.deliverOpen _` without checking the delivered message, so it is
not a general `C = ∅` simulator: an environment that delivers `!c` instead of `c` and then polls the
receiver sees `none` in the real world but the receipt here. It is only used for the honest
schedules `honestCommitEnv` and `honestViewEnv`. -/
def oneTimePadEmptySim : PlainCommitmentSim Bool Bool := fun _ _ =>
  { State := Option Bool
    init := pure none
    handle := fun q st =>
      match q with
      | .inl _ => pure (.inl none, st)
      | .inr .readCommit => do
        let fcomSt ← ProbOracleComp.query (spec := fcomIdealNet) (Sum.inr .query)
        match fcomSt with
        | Sum.inr (some _) =>
          match st with
          | some c => return (.inr (.commitMsg (some c)), some c)
          | none =>
            let r ← ProbOracleComp.sample (ProbComp.unifFin 1)
            let c := decide (r.val = 1)
            return (.inr (.commitMsg (some c)), some c)
        | _ => return (.inr (.commitMsg none), st)
      | .inr (.deliverCommit _) => do
        let _ ← ProbOracleComp.query (spec := fcomIdealNet) (Sum.inr .deliverCommit)
        return (.inr .ack, st)
      | .inr .readOpen => do
        let fcomSt ← ProbOracleComp.query (spec := fcomIdealNet) (Sum.inr .query)
        match fcomSt, st with
        | Sum.inr (some (.opened b)), some c =>
          return (.inr (.openMsg (some (c ^^ b))), st)
        | _, _ => return (.inr (.openMsg none), st)
      | .inr (.deliverOpen _) => do
        let _ ← ProbOracleComp.query (spec := fcomIdealNet) (Sum.inr .deliverOpen)
        return (.inr .ack, st) }

private def otpIdealState (κ : ℕ) (st : Option Bool) (s : CommitmentState) :
    (execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).State := (st, s)

private def otpIdealReply (q : (Fin 2 × CommitmentInput) ⊕ PlainNetQ Bool Bool)
    (r : Option CommitmentOutput ⊕ PlainNetR Bool Bool) :
    execSpec 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ Bool Bool)
      (Option CommitmentOutput ⊕ PlainNetR Bool Bool) (.inr q) := r

private theorem init_otpIdeal (κ : ℕ) :
    (execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).init =
      pure (otpIdealState κ none .idle) := rfl

private theorem handle_otpIdeal_commit (κ : ℕ) (b : Bool) (st : Option Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (0, .commit b))).run
      (otpIdealState κ st .idle) =
      pure (none, otpIdealState κ st (.committed b false)) := rfl

private theorem handle_otpIdeal_query_idle (κ : ℕ) (st : Option Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (1, .query))).run
      (otpIdealState κ st .idle) =
      pure (none, otpIdealState κ st .idle) := rfl

private theorem handle_otpIdeal_query_active (κ : ℕ) (st : Option Bool) (b : Bool)
    (phase : CommitmentPhase) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (1, .query))).run
      (otpIdealState κ st (.active b phase)) =
      pure (fcomLockedReply b phase, otpIdealState κ st (.active b phase)) := by
  rcases phase with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

private theorem handle_otpIdeal_query_committed_false (κ : ℕ) (st : Option Bool) (b : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (1, .query))).run
      (otpIdealState κ st (.committed b false)) =
      pure (none, otpIdealState κ st (.committed b false)) := rfl

private theorem handle_otpIdeal_query_committed_true (κ : ℕ) (st : Option Bool) (b : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (1, .query))).run
      (otpIdealState κ st (.committed b true)) =
      pure (some .receipt, otpIdealState κ st (.committed b true)) := rfl

private theorem handle_otpIdeal_query_opened_true (κ : ℕ) (st : Option Bool) (b : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (1, .query))).run
      (otpIdealState κ st (.opened b true)) =
      pure (some .receipt, otpIdealState κ st (.opened b true)) := rfl

private theorem handle_otpIdeal_readCommit (κ : ℕ) (b : Bool) (recDel : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inr (.inr .readCommit))).run
      (otpIdealState κ none (.committed b recDel)) =
      (fun r : Fin 2 =>
        (otpIdealReply (.inr .readCommit) (.inr (.commitMsg (some (decide (r.val = 1))))),
          otpIdealState κ (some (decide (r.val = 1))) (.committed b recDel))) <$>
        ProbOracleComp.sample (ProbComp.unifFin 1) := by
  change Equiv.prodAssoc _ _ _ <$>
    (corruptRouter (∅ : Finset (Fin 2)) (fcom.toProtocol κ ∅)).runFrom
      (liftNet (((oneTimePadEmptySim κ ∅).handle (.inr .readCommit)).run none))
      (.committed b recDel) = _
  dsimp only [oneTimePadEmptySim, StateT.run]
  erw [liftNet_bind, liftNet_query, Machine.runFrom_bind, Machine.runFrom_query]
  change Equiv.prodAssoc _ _ _ <$>
    (pure (Sum.inr (some CommitmentOutput.receipt), CommitmentState.committed b recDel) >>= _) = _
  erw [pure_bind, liftNet_bind, liftNet_sample, Machine.runFrom_bind, Machine.runFrom_sample,
    bind_map_left]
  rfl

private theorem handle_otpIdeal_deliverCommit (κ : ℕ) (st : Option Bool) (b : Bool)
    (c : Bool) (recDel : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle
      (.inr (.inr (.deliverCommit c)))).run (otpIdealState κ st (.committed b recDel)) =
      pure (otpIdealReply (.inr (.deliverCommit c)) (.inr .ack),
        otpIdealState κ st (.committed b true)) := rfl

private theorem handle_otpIdeal_openCom (κ : ℕ) (st : Option Bool) (b : Bool) (recDel : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inl (0, .openCom))).run
      (otpIdealState κ st (.committed b recDel)) =
      pure (none, otpIdealState κ st (.opened b recDel)) := rfl

private theorem handle_otpIdeal_readOpen (κ : ℕ) (c b : Bool) (recDel : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle (.inr (.inr .readOpen))).run
      (otpIdealState κ (some c) (.opened b recDel)) =
      pure (otpIdealReply (.inr .readOpen) (.inr (.openMsg (some (c ^^ b)))),
        otpIdealState κ (some c) (.opened b recDel)) := rfl

private theorem handle_otpIdeal_deliverOpen (κ : ℕ) (st : Option Bool) (b o : Bool) :
    ((execMachine fcom.toProtocol oneTimePadEmptySim κ ∅).handle
      (.inr (.inr (.deliverOpen o)))).run (otpIdealState κ st (.opened b true)) =
      pure (otpIdealReply (.inr (.deliverOpen o)) (.inr .ack),
        otpIdealState κ st
          (.active b { opened := true, recDelivered := true, openDelivered := true })) := rfl

private theorem exec_fcom_oneTimePadEmptySim_honestCommitEnv (b : Bool) (κ : ℕ) (z : List Bool) :
    exec fcom.toProtocol oneTimePadEmptySim ∅ (honestCommitEnv b) κ z =
      (ProbComp.unifFin 1 >>= fun _ => pure true) := by
  simp only [exec, Machine.run, Machine.link, honestCommitEnv, init_otpIdeal,
    Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, map_bind]
  rw [handle_otpIdeal_commit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_readCommit]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [otpIdealReply, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, map_bind]
  rw [handle_otpIdeal_deliverCommit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_openCom]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_readOpen]
  simp only [otpIdealReply, Machine.closeProgram_pure, pure_bind,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_otpIdeal_deliverOpen]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_query_active]
  simp only [fcomLockedReply, Machine.closeProgram_pure, pure_bind, Machine.runFrom_pure, map_pure]
  cases b <;> rfl

/-- In the ideal world (`C = ∅`), running `honestCommitEnv b` with `oneTimePadEmptySim` against
`fcom` outputs `true` with probability `1`. -/
theorem eval_exec_fcom_oneTimePadEmptySim_honestCommitEnv (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec fcom.toProtocol oneTimePadEmptySim ∅ (honestCommitEnv b) κ z).eval = PMF.pure true := by
  rw [exec_fcom_oneTimePadEmptySim_honestCommitEnv]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

/-- `oneTimePadEmptySim` perfectly simulates the honest schedule `honestCommitEnv b` at `C = ∅`:
the distinguishing advantage on this environment is zero. -/
theorem advantage_oneTimePadEmptySim_honestCommitEnv (b : Bool) (κ : ℕ) (z : List Bool) :
    advantage oneTimePadScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _)
      oneTimePadEmptySim ∅ (honestCommitEnv b) κ z = 0 := by
  have hreal : (exec oneTimePadScheme.toProtocol (dummyAdversary 2 _ _) ∅
      (honestCommitEnv b) κ z).eval = PMF.pure true := by
    rw [eval_exec_honestCommitEnv]
    have hxor (r : Fin 2) :
        decide (some ((b ^^ decide (r.val = 1)) ^^ decide (r.val = 1)) = some b) = true := by
      cases b <;> fin_cases r <;> rfl
    simp only [PlainCommitmentScheme.acceptGame, oneTimePadScheme, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_pure, hxor, PMF.bind_const]
  rw [advantage, hreal, eval_exec_fcom_oneTimePadEmptySim_honestCommitEnv]
  simp

/-- The view recorded by `honestViewEnv`: the committer's replies, the receiver's replies before and
after each delivery, and the network transcript `(c, o)`. -/
structure HonestView where
  /-- Committer `0`'s reply to `.commit b`. -/
  commitReply : Option CommitmentOutput
  /-- Receiver `1`'s reply to `.query` before the commit message is delivered. -/
  receiverBeforeDelivery : Option CommitmentOutput
  /-- The commit message `c` read from the network. -/
  commitMessage : Bool
  /-- Receiver `1`'s reply to `.query` after the commit message is delivered. -/
  receiverAfterCommitDelivery : Option CommitmentOutput
  /-- Committer `0`'s reply to `.openCom`. -/
  openReply : Option CommitmentOutput
  /-- Receiver `1`'s reply to `.query` after the opening but before the opening message is
  delivered. -/
  receiverBeforeOpenDelivery : Option CommitmentOutput
  /-- The opening message `o` read from the network. -/
  openMessage : Bool
  /-- Receiver `1`'s reply to `.query` after the opening message is delivered. -/
  receiverFinal : Option CommitmentOutput

/-- Environment that exercises the full honest commit-and-open schedule at `C = ∅` while recording
the committer's outputs on `.commit b` and `.openCom`, the receiver's outputs before and after
`.deliverCommit` and `.deliverOpen`, and the network transcript `(c, o)`, then evaluates an
arbitrary distinguisher predicate `P : HonestView → Bool`. -/
def honestViewEnv (b : Bool) (P : HonestView → Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ Bool Bool)
      (Option CommitmentOutput ⊕ PlainNetR Bool Bool) := fun _ _ => do
  let outCom₀ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .commit b))
  let outRecPre ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
  let r₁ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverCommit c)))
    let outRecMid ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
    let outOpen₀ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
    let outRecPreOpen ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
    let r₂ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let _ ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverOpen o)))
      let outRecFinal ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
      return P
        { commitReply := outCom₀, receiverBeforeDelivery := outRecPre,
          commitMessage := c, receiverAfterCommitDelivery := outRecMid, openReply := outOpen₀,
          receiverBeforeOpenDelivery := outRecPreOpen, openMessage := o,
          receiverFinal := outRecFinal }
    | _ => return false
  | _ => return false

private def otpRealState (κ : ℕ) (s₁ : CommitterState Bool Bool) (s₂ : ReceiverState Bool) :
    (corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).State := (s₁, s₂)

private theorem init_otpReal (κ : ℕ) :
    (corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).init =
      pure (otpRealState κ .idle .waiting) := rfl

private theorem handle_otpReal_commit (κ : ℕ) (b : Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle (Sum.inl (0, .commit b))).run
      (otpRealState κ .idle .waiting) =
      (fun r : Fin 2 =>
        (none,
          otpRealState κ (.committed (b ^^ decide (r.val = 1)) (decide (r.val = 1))) .waiting)) <$>
        ProbOracleComp.sample (ProbComp.unifFin 1) := by
  simp [corruptRouter, PlainCommitmentScheme.toProtocol, oneTimePadScheme, otpRealState,
    StateT.run, bind_pure_comp, ProbOracleComp.sample_pure, Functor.map_map]

private theorem handle_otpReal_query_waiting (κ : ℕ) (s₁ : CommitterState Bool Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle (Sum.inl (1, .query))).run
      (otpRealState κ s₁ .waiting) =
      pure (none, otpRealState κ s₁ .waiting) := rfl

private theorem handle_otpReal_readCommit (κ : ℕ) (c o : Bool) (s₂ : ReceiverState Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle
      (Sum.inr (.inr .readCommit))).run (otpRealState κ (.committed c o) s₂) =
      pure (.inr (.commitMsg (some c)), otpRealState κ (.committed c o) s₂) := rfl

private theorem handle_otpReal_deliverCommit (κ : ℕ) (c o : Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle
      (Sum.inr (.inr (.deliverCommit c)))).run (otpRealState κ (.committed c o) .waiting) =
      pure (.inr .ack, otpRealState κ (.committed c o) (.committed c)) := by
  simp [corruptRouter, PlainCommitmentScheme.toProtocol, otpRealState, StateT.run,
    Functor.map, StateT.map]

private theorem handle_otpReal_query_committed (κ : ℕ) (s₁ : CommitterState Bool Bool) (c : Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle (Sum.inl (1, .query))).run
      (otpRealState κ s₁ (.committed c)) =
      pure (some .receipt, otpRealState κ s₁ (.committed c)) := rfl

private theorem handle_otpReal_openCom (κ : ℕ) (c o : Bool) (s₂ : ReceiverState Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle (Sum.inl (0, .openCom))).run
      (otpRealState κ (.committed c o) s₂) =
      pure (none, otpRealState κ (.opened c o) s₂) := rfl

private theorem handle_otpReal_readOpen (κ : ℕ) (c o : Bool) (s₂ : ReceiverState Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle
      (Sum.inr (.inr .readOpen))).run (otpRealState κ (.opened c o) s₂) =
      pure (.inr (.openMsg (some o)), otpRealState κ (.opened c o) s₂) := rfl

private theorem handle_otpReal_deliverOpen (κ : ℕ) (c o : Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle
      (Sum.inr (.inr (.deliverOpen o)))).run (otpRealState κ (.opened c o) (.committed c)) =
      pure (.inr .ack, otpRealState κ (.opened c o) (.finished (some (c ^^ o)))) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, oneTimePadScheme, otpRealState,
    StateT.run, Functor.map, StateT.map]
  simp [ProbOracleComp.sample_pure]

private theorem handle_otpReal_query_finished (κ : ℕ) (s₁ : CommitterState Bool Bool) (b : Bool) :
    ((corruptRouter ∅ (oneTimePadScheme.toProtocol κ ∅)).handle (Sum.inl (1, .query))).run
      (otpRealState κ s₁ (.finished (some b))) =
      pure (some (.opened b), otpRealState κ s₁ (.finished (some b))) := rfl

private theorem exec_real_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    exec oneTimePadScheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestViewEnv b P) κ z =
      (fun r : Fin 2 =>
        P
          { commitReply := none, receiverBeforeDelivery := none,
            commitMessage := b ^^ decide (r.val = 1), receiverAfterCommitDelivery := some .receipt,
            openReply := none, receiverBeforeOpenDelivery := some .receipt,
            openMessage := decide (r.val = 1),
            receiverFinal := some (.opened ((b ^^ decide (r.val = 1)) ^^ decide (r.val = 1))) }) <$>
        ProbComp.unifFin 1 := by
  rw [exec_dummyAdversary, map_eq_bind_pure_comp]
  simp only [Machine.run, Machine.link, honestViewEnv, init_otpReal,
    Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, map_bind]
  rw [handle_otpReal_commit]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  refine bind_congr fun r => ?_
  rw [handle_otpReal_query_waiting]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_readCommit]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_otpReal_deliverCommit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_query_committed]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_openCom]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_query_committed]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_readOpen]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_bind,
    Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_otpReal_deliverOpen]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpReal_query_finished]
  simp only [Machine.closeProgram_pure, pure_bind, Machine.runFrom_pure, map_pure,
    Function.comp_apply]

private theorem exec_fcom_oneTimePadEmptySim_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    exec fcom.toProtocol oneTimePadEmptySim ∅ (honestViewEnv b P) κ z =
      (fun r : Fin 2 =>
        P
          { commitReply := none, receiverBeforeDelivery := none,
            commitMessage := decide (r.val = 1), receiverAfterCommitDelivery := some .receipt,
            openReply := none, receiverBeforeOpenDelivery := some .receipt,
            openMessage := decide (r.val = 1) ^^ b, receiverFinal := some (.opened b) }) <$>
        ProbComp.unifFin 1 := by
  rw [map_eq_bind_pure_comp]
  simp only [exec, Machine.run, Machine.link, honestViewEnv, init_otpIdeal,
    Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    pure_bind, map_bind]
  rw [handle_otpIdeal_commit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_query_committed_false]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_readCommit]
  simp only [Machine.closeProgram_map, Machine.closeProgram_sample, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [otpIdealReply, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, map_bind]
  rw [handle_otpIdeal_deliverCommit]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_query_committed_true]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_openCom]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_query_opened_true]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_readOpen]
  simp only [otpIdealReply, Machine.closeProgram_pure, pure_bind,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.closeProgram_bind, map_bind]
  rw [handle_otpIdeal_deliverOpen]
  simp only [Machine.closeProgram_pure, pure_bind]
  rw [handle_otpIdeal_query_active]
  simp only [fcomLockedReply, Machine.closeProgram_pure, pure_bind, Machine.runFrom_pure,
    map_pure, Function.comp_apply, ite_true]

/-- For every bit `b` and every distinguisher predicate `P : HonestView → Bool`, the real (`C = ∅`,
`dummyAdversary`) and ideal (`C = ∅`, `oneTimePadEmptySim`) executions of `honestViewEnv b P` have
identical output distributions. -/
theorem eval_exec_oneTimePadEmptySim_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    (exec oneTimePadScheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestViewEnv b P) κ z).eval =
      (exec fcom.toProtocol oneTimePadEmptySim ∅ (honestViewEnv b P) κ z).eval := by
  rw [exec_real_honestViewEnv, exec_fcom_oneTimePadEmptySim_honestViewEnv,
    ProbComp.eval_map, ProbComp.eval_map, ProbComp.eval_unifFin]
  cases b
  · congr 1
    ext r
    fin_cases r <;> rfl
  · calc
      PMF.map _ (Probability.PMF.uniformOfFintype (Fin 2))
        = PMF.map _ (PMF.map (Equiv.swap (0 : Fin 2) 1)
            (Probability.PMF.uniformOfFintype (Fin 2))) := by
          rw [Probability.PMF.uniformOfFintype_map_equiv (Equiv.swap (0 : Fin 2) 1)]
      _ = PMF.map _ (Probability.PMF.uniformOfFintype (Fin 2)) := by
          rw [PMF.map_comp]
          congr 1
          ext r
          fin_cases r <;> rfl

/-- `oneTimePadEmptySim` perfectly simulates the honest schedule `honestViewEnv b P`: the
advantage is zero for every committed bit `b` and every predicate `P : HonestView → Bool`. -/
theorem advantage_oneTimePadEmptySim_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    advantage oneTimePadScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _)
      oneTimePadEmptySim ∅ (honestViewEnv b P) κ z = 0 := by
  rw [advantage, eval_exec_oneTimePadEmptySim_honestViewEnv]
  simp

/-- Even though `oneTimePadScheme`'s commit message `b ^^ mask` hides `b` perfectly and the honest
schedules `honestCommitEnv` and `honestViewEnv` are perfectly simulated when `C = ∅`, it still
cannot UC-realize `fcom` in the plain model against static corruptions. -/
theorem not_realizes_oneTimePadScheme : ¬ Realizes oneTimePadScheme.toProtocol fcom :=
  not_realizes_fcom_of_perfectlyComplete oneTimePadScheme_isPolyBounded.2
    oneTimePadScheme_perfectlyComplete

end CslibFrontierTests.Crypto.UCCommitment
