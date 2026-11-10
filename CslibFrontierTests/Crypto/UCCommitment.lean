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
   perfectly complete (`oneTimePadScheme_perfectlyComplete`), and in the uncorrupted case (`C = ∅`)
   the explicit simulator `oneTimePadEmptySim` achieves zero distinguishing advantage on both
   `honestCommitEnv` (`advantage_oneTimePadEmptySim_honestCommitEnv`) and any predicate of the full
   8-step honest execution view including committer replies, pre/post-delivery receiver replies,
   and the `(c, o)` transcript (`advantage_oneTimePadEmptySim_honestViewEnv`). Nevertheless, by
   Canetti–Fischlin it still cannot UC-realize `fcom` against static corruptions
   (`not_realizes_oneTimePadScheme`).
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
`fcom` via `.deliverOpen`. -/
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

/-- In the ideal world (`C = ∅`), running `honestCommitEnv b` with `oneTimePadEmptySim` against
`fcom` outputs `true` with probability `1`. -/
theorem eval_exec_fcom_oneTimePadEmptySim_honestCommitEnv (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec fcom.toProtocol oneTimePadEmptySim ∅ (honestCommitEnv b) κ z).eval = PMF.pure true := by
  simp [exec, execMachine, fcom, IdealFunctionality.toProtocol, corruptRouter,
    oneTimePadEmptySim, honestCommitEnv, Machine.run, Machine.link, Machine.comp, liftAdversary,
    liftNet, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    Machine.runFrom_sample, Machine.closeProgram_bind, Machine.closeProgram_pure,
    Machine.closeProgram_sample, StateT.run_bind, bind_assoc, ProbComp.eval_bind]

/-- `oneTimePadEmptySim` achieves zero distinguishing advantage on `honestCommitEnv b` at `C = ∅`. -/
theorem advantage_oneTimePadEmptySim_honestCommitEnv (b : Bool) (κ : ℕ) (z : List Bool) :
    advantage oneTimePadScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _)
      oneTimePadEmptySim ∅ (honestCommitEnv b) κ z = 0 := by
  have hreal : (exec oneTimePadScheme.toProtocol (dummyAdversary 2 _ _) ∅
      (honestCommitEnv b) κ z).eval = PMF.pure true := by
    have h := oneTimePadScheme_perfectlyComplete κ b
    rw [eval_exec_honestCommitEnv]
    have hxor (r : Fin 2) :
        decide (some ((b ^^ decide (r.val = 1)) ^^ decide (r.val = 1)) = some b) = true := by
      cases b <;> fin_cases r <;> rfl
    simp only [PlainCommitmentScheme.acceptGame, oneTimePadScheme, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_pure, hxor, PMF.bind_const]
  rw [advantage, hreal, eval_exec_fcom_oneTimePadEmptySim_honestCommitEnv]
  simp

/-- Full honest-execution view tuple recording all party-port and network-port replies across the
commit and open phases, including pre-delivery receiver queries and committer outputs. -/
abbrev HonestView :=
  Option CommitmentOutput ×
  Option CommitmentOutput ×
  Bool ×
  Option CommitmentOutput ×
  Option CommitmentOutput ×
  Option CommitmentOutput ×
  Bool ×
  Option CommitmentOutput

/-- Environment that exercises the full honest commit-and-open schedule at `C = ∅` while recording
the committer's outputs on `.commit b` and `.openCom`, the receiver's outputs before and after
`.deliverCommit` and `.deliverOpen`, and the network transcript `(c, o)`, then evaluates an
arbitrary distinguisher predicate `P : HonestView → Bool`. -/
def honestViewEnv (b : Bool) (P : HonestView → Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      ((Fin 2 × CommitmentInput) ⊕ PlainNetQ Bool Bool)
      (Option CommitmentOutput ⊕ PlainNetR Bool Bool) := fun _ _ => do
  let outCom₀ ← OracleComp.query (.inl (0, .commit b))
  let outRecPre ← OracleComp.query (.inl (1, .query))
  let r₁ ← OracleComp.query (.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← OracleComp.query (.inr (.inr (.deliverCommit c)))
    let outRecMid ← OracleComp.query (.inl (1, .query))
    let outOpen₀ ← OracleComp.query (.inl (0, .openCom))
    let outRecPreOpen ← OracleComp.query (.inl (1, .query))
    let r₂ ← OracleComp.query (.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let _ ← OracleComp.query (.inr (.inr (.deliverOpen o)))
      let outRecFinal ← OracleComp.query (.inl (1, .query))
      return P (outCom₀, outRecPre, c, outRecMid, outOpen₀, outRecPreOpen, o, outRecFinal)
    | _ => return false
  | _ => return false

/-- For every bit `b` and every distinguisher predicate `P : HonestView → Bool`, the real (`C = ∅`,
`dummyAdversary`) and ideal (`C = ∅`, `oneTimePadEmptySim`) executions of `honestViewEnv b P` have
identical output distributions. -/
theorem eval_exec_oneTimePadEmptySim_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    (exec oneTimePadScheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestViewEnv b P) κ z).eval =
      (exec fcom.toProtocol oneTimePadEmptySim ∅ (honestViewEnv b P) κ z).eval := by
  ext x
  simp only [exec_dummyAdversary,
    exec, execMachine, fcom, IdealFunctionality.toProtocol, PlainCommitmentScheme.toProtocol,
    oneTimePadScheme, corruptRouter, oneTimePadEmptySim, honestViewEnv, Machine.run, Machine.link,
    Machine.comp, liftAdversary, liftNet, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.runFrom_pure, Machine.runFrom_sample, Machine.closeProgram_bind,
    Machine.closeProgram_pure, Machine.closeProgram_sample, StateT.run_bind, bind_assoc,
    pure_bind, map_bind, Functor.map_map, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure]
  cases b <;>
    simp [ProbComp.unifFin, PMF.bind_apply, PMF.uniformOfFintype_apply, Fin.sum_univ_two, add_comm]

/-- `oneTimePadEmptySim` has zero distinguishing advantage against `honestViewEnv b P` for every
committed bit `b` and every distinguisher predicate `P : HonestView → Bool`. -/
theorem advantage_oneTimePadEmptySim_honestViewEnv (b : Bool) (P : HonestView → Bool)
    (κ : ℕ) (z : List Bool) :
    advantage oneTimePadScheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _)
      oneTimePadEmptySim ∅ (honestViewEnv b P) κ z = 0 := by
  rw [advantage, eval_exec_oneTimePadEmptySim_honestViewEnv]
  simp

/-- Even though `oneTimePadScheme`'s commit message `b ^^ mask` hides `b` perfectly and is
perfectly simulatable when `C = ∅`, it still cannot UC-realize `fcom` in the plain model against
static corruptions. -/
theorem not_realizes_oneTimePadScheme : ¬ Realizes oneTimePadScheme.toProtocol fcom :=
  not_realizes_fcom_of_perfectlyComplete oneTimePadScheme_isPolyBounded.2
    oneTimePadScheme_perfectlyComplete

end CslibFrontierTests.Crypto.UCCommitment
