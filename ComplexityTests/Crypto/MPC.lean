/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Crypto.Protocols.MPC.Basic
import Complexity.Crypto.Protocols.MPC.CircuitEval
import Complexity.Crypto.Protocols.MPC.Composition
import Complexity.Crypto.Protocols.MPC.PolyTime
import Complexity.Crypto.Protocols.MPC.SharedMul
import Cslib.Computability.Circuit.Boolean.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.ZMod.Basic

/-!
# Tests for additive secret sharing and multi-party protocol foundations

Concrete tests for `Complexity.Languages.Probabilistic.Sharing` and
`Complexity.Crypto.Protocols.MPC.Basic`:

1. **Additive secret sharing (`completeShares`, `sampleAdditiveShares`):** concrete evaluations over
   `ZMod 5` and `Bool` (`BooleanRing Bool`), plus 2-out-of-3 coalition marginal uniformity via
   `eval_restrict_sampleAdditiveShares`.
2. **2-party XOR protocol in `noOracleWorld`:** a concrete 2-round point-to-point protocol built
   with `Steps.append` in which party 0 sends `x 0` to party 1, party 1 sends `x 1` to party 0, and
   both output `x 0 + x 1`, proved `PerfectSemiHonestPrivate` against every static coalition
   `I : Finset (Fin 2)` by `perfectSemiHonestPrivate_of_deterministic`.
3. **2-party oracle-aided XOR protocol (`oracleXorProtocol`):** a 1-round `Round.oracle` protocol
   exercising `Round.deliverOracle` and `Steps.evalWith_oracle`, proved `PerfectSemiHonestPrivate`.
4. **Negative test 1 (`not_perfectSemiHonestPrivate_leakyProtocol`):** a leaky 1-round protocol in
   which party 0 sends `x 0` to party 1 while computing the constant functionality `constFalseFunc`,
   proved `∀ S, ¬ PerfectSemiHonestPrivate leakyProtocol noOracleWorld
   (Functionality.ofDeterministic constFalseFunc) S`.
5. **Negative test 2 (`not_perfectSemiHonestPrivate_goldreichCounterexample1`, Goldreich
   Section 7.2.2.1, print p. 621, Counterexample 1):** the randomized functionality
   `((), ()) ↦ (r, false)` (`goldreichCounterexample1Func`, modeling
   $(1^n, 1^n) \mapsto (r, \lambda)$ for uniform $r$) and the 1-round protocol
   `goldreichCounterexample1Protocol` in which party 0 samples a uniform bit `r`, sends `r` to
   party 1, and outputs `r`, while party 1 outputs `false`.
   We prove that:
   - `goldreichCounterexample1Protocol` computes `goldreichCounterexample1Func`
     (`eval_snd_goldreichCounterexample1Protocol`);
   - party 1's marginal view (`I = {1}`) is simulated by a uniform received bit, satisfying the
     marginal-view equation Eq. 7.8 (`eval_goldreichCounterexample1MarginalSim1`);
   - yet `∀ S, ¬ PerfectSemiHonestPrivate goldreichCounterexample1Protocol noOracleWorld
     goldreichCounterexample1Func S` (`not_perfectSemiHonestPrivate_goldreichCounterexample1`),
     because in every real execution party 1's view determines party 0's output, violating the
     joint view-and-output equation Eq. 7.10 / Eq. 7.40 at `I = {1}`.
6. **Negative test 3 (`not_perfectSemiHonestPrivate_independentCoinProtocol`, output-correctness
   failure at `I = ∅`):** `coinBroadcastFunc` outputting `(b, b)` versus `independentCoinProtocol`
   where each party outputs its own independent random coin, refuted at `I = ∅`.
-/

namespace ComplexityTests.Crypto.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Circuits Cslib.Crypto.Protocols.MPC

/-! ### Additive secret sharing tests -/

example : completeShares 3 (2 : ZMod 5) ![1, 3] = ![1, 3, 3] := by
  decide

example (target : Bool) (init : Fin 2 → Bool) :
    ∑ i : Fin 3, completeShares 3 target init i = target :=
  sum_completeShares 3 target init

example (target : Bool) :
    (ProbComp.eval (sampleAdditiveShares 3 target)).map ({0, 1} : Finset (Fin 3)).restrict =
      PMF.uniformOfFintype ((i : ({0, 1} : Finset (Fin 3))) → Bool) :=
  eval_restrict_sampleAdditiveShares ({0, 1} : Finset (Fin 3)) (by decide) target

/-! ### Concrete 2-party XOR protocol and perfect semi-honest privacy -/

/-- Two-round schedule in `noOracleSpec`: party 0 sends a bit to party 1, then party 1 sends a bit
to party 0. -/
abbrev xorSchedule : Schedule 2 noOracleSpec :=
  [.message 0 1 Bool, .message 1 0 Bool]

/-- First round: party 0 sends its input bit to party 1. -/
def xorStep1 :
    Steps (spec := noOracleSpec) (fun _ : Fin 2 => Bool × Unit)
      (fun i => (Bool × Unit) × (Round.message (spec := noOracleSpec) 0 1 Bool).Received i)
      [.message 0 1 Bool] :=
  .message (sender := 0) (receiver := 1) (fun st => st.1) (.done fun _ st => st)

/-- Second round: party 1 sends its input bit to party 0, and each party outputs the sum of its own
input and the bit received from the other party. -/
def xorStep2 :
    Steps (spec := noOracleSpec)
      (fun i : Fin 2 =>
        (Bool × Unit) × (Round.message (spec := noOracleSpec) 0 1 Bool).Received i)
      (fun _ => Bool)
      [.message 1 0 Bool] :=
  .message (sender := 1) (receiver := 0) (fun st => st.1.1)
    (.done fun i st =>
      if h : i = 0 then
        st.1.1.1 + st.2 h
      else
        st.1.2 (by omega) + st.1.1.1)

/-- Two-party XOR protocol built by sequentially composing `xorStep1` and `xorStep2` via
`Steps.append`. -/
def xorProtocol : Protocol 2 noOracleSpec xorSchedule
    (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps := xorStep1.append xorStep2

/-- Deterministic 2-party XOR functionality `f x i = x 0 + x 1`. -/
def xorFunc (x : Fin 2 → Bool) (_ : Fin 2) : Bool :=
  x 0 + x 1

/-- Coalition simulator for `xorProtocol`: reconstructs the other party's bit from `y i - x i`. -/
def xorSim (I : Finset (Fin 2)) :
    CoalitionSimulator xorSchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) I :=
  fun xI yI =>
    pure fun i =>
      { input := xI i
        coins := ()
        received :=
          (fun _ => yI i - xI i,
           (fun _ => yI i - xI i, ())) }

/-- `xorProtocol` is perfectly semi-honest private against every static coalition
`I : Finset (Fin 2)`. -/
theorem perfectSemiHonestPrivate_xorProtocol :
    PerfectSemiHonestPrivate xorProtocol noOracleWorld
      (Functionality.ofDeterministic xorFunc) xorSim := by
  apply perfectSemiHonestPrivate_of_deterministic
  · intro I x
    simp only [xorSim, xorProtocol, xorStep1, xorStep2, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.append, Steps.mapState, Steps.evalWith_message,
      Steps.evalWith_done, PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure (funext fun (i : I) => ?_)
    rcases i with ⟨i, hi⟩
    fin_cases i
    · refine PartyView.ext rfl rfl ?_
      refine Prod.ext (Round.received_message_eq_of_ne (by decide +revert) _ _) (Prod.ext ?_ rfl)
      refine Round.received_message_ext fun _ => ?_
      simp [xorFunc, Round.deliverMessage, add_sub_cancel_left]
    · refine PartyView.ext rfl rfl ?_
      refine Prod.ext ?_ (Prod.ext (Round.received_message_eq_of_ne (by decide +revert) _ _) rfl)
      refine Round.received_message_ext fun _ => ?_
      simp [xorFunc, Round.deliverMessage, sub_eq_add_neg]
  · intro x r hr
    simp only [xorProtocol, xorStep1, xorStep2, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.append, Steps.mapState, Steps.evalWith_message,
      Steps.evalWith_done, PMF.pure_bind, PMF.pure_map, PMF.mem_support_pure_iff] at hr
    subst hr
    ext i
    fin_cases i <;> rfl

/-- Proper-coalition privacy follows from full-coalition privacy. -/
example :
    PerfectSemiHonestPrivateProper xorProtocol noOracleWorld
      (Functionality.ofDeterministic xorFunc) xorSim :=
  perfectSemiHonestPrivate_xorProtocol.proper

/-! ### Positive test with a 2-party oracle round (`Round.oracle` / `Steps.evalWith_oracle`) -/

/-- A 2-ary oracle specification where each of the 2 slots submits a `Bool` and receives a
`Bool`. -/
abbrev xorOracleSpec : MultiOracleSpec where
  Op := Unit
  arity _ := 2
  Query _ _ := Bool
  Answer _ _ := Bool

/-- The world for `xorOracleSpec` that returns `q 0 + q 1` to both slots. -/
def xorOracleWorld : MultiOracleWorld xorOracleSpec :=
  fun () q => pure (fun _ => q 0 + q 1)

/-- Single-round oracle schedule in which parties 0 and 1 jointly query `xorOracleSpec`. -/
abbrev oracleXorSchedule : Schedule 2 xorOracleSpec :=
  [.oracle () (Function.Embedding.refl (Fin 2))]

/-- One-round oracle protocol where each party submits its input bit to `xorOracleSpec` and outputs
its received answer part. -/
def oracleXorProtocol : Protocol 2 xorOracleSpec oracleXorSchedule
    (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps :=
    .oracle (fun _ st => st.1)
      (.done fun i st => st.2 i rfl)

/-- Simulator for `oracleXorProtocol`: places party `i`'s output `yI i` into its oracle answer
record. -/
def oracleXorSim (I : Finset (Fin 2)) :
    CoalitionSimulator oracleXorSchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) I :=
  fun xI yI =>
    pure fun i =>
      { input := xI i
        coins := ()
        received := (fun _ _ => yI i, ()) }

/-- `oracleXorProtocol` is perfectly semi-honest private in `xorOracleWorld`. -/
theorem perfectSemiHonestPrivate_oracleXorProtocol :
    PerfectSemiHonestPrivate oracleXorProtocol xorOracleWorld
      (Functionality.ofDeterministic xorFunc) oracleXorSim := by
  apply perfectSemiHonestPrivate_of_deterministic
  · intro I x
    simp only [oracleXorSim, oracleXorProtocol, xorOracleWorld, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.evalWith_oracle, Steps.evalWith_done,
      PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure (funext fun (i : I) => ?_)
    refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
    refine Round.received_oracle_ext fun s hs => ?_
    rfl
  · intro x r hr
    simp only [oracleXorProtocol, xorOracleWorld, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.evalWith_oracle, Steps.evalWith_done,
      PMF.pure_bind, PMF.pure_map, PMF.mem_support_pure_iff] at hr
    subst hr
    rfl

/-! ### Negative test 1: leaky protocol fails `PerfectSemiHonestPrivate` for every simulator -/

/-- One-round schedule in which party 0 sends a `Bool` to party 1. -/
abbrev leakySchedule : Schedule 2 noOracleSpec :=
  [.message 0 1 Bool]

/-- Constant functionality `constFalseFunc x i = false`. -/
def constFalseFunc (_ : Fin 2 → Bool) (_ : Fin 2) : Bool :=
  false

/-- Leaky protocol for `constFalseFunc`: party 0 sends its private input `x 0` to party 1, and both
parties output `false`. -/
def leakyProtocol : Protocol 2 noOracleSpec leakySchedule
    (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps :=
    .message (sender := 0) (receiver := 1) (fun st => st.1)
      (.done fun _ _ => false)

/-- Extract the bit that party 1 received in round 0 from a `{1}`-coalition joint outcome. -/
def leakyExtractMsg1
    (res : ((i : ({1} : Finset (Fin 2))) →
      PartyView (fun _ => Bool) (fun _ => Unit) leakySchedule i) × (Fin 2 → Bool)) : Bool :=
  (res.1 ⟨1, by simp⟩).received.1 rfl

/-- No simulator can make `leakyProtocol` satisfy `PerfectSemiHonestPrivate` for `constFalseFunc`:
on inputs `![false, false]` and `![true, false]`, party 1's input and output are identical so the
ideal distribution for `I = {1}` is identical, whereas party 1's real view receives `false` vs
`true`. -/
theorem not_perfectSemiHonestPrivate_leakyProtocol
    (S : (I : Finset (Fin 2)) →
      CoalitionSimulator leakySchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) I) :
    ¬ PerfectSemiHonestPrivate leakyProtocol noOracleWorld
        (Functionality.ofDeterministic constFalseFunc) S := by
  intro hPriv
  let I : Finset (Fin 2) := {1}
  let x₀ : Fin 2 → Bool := ![false, false]
  let x₁ : Fin 2 → Bool := ![true, false]
  have h0 := congrArg (PMF.map leakyExtractMsg1) (hPriv I x₀)
  have h1 := congrArg (PMF.map leakyExtractMsg1) (hPriv I x₁)
  have hIdealEq :
      idealJoint (Functionality.ofDeterministic constFalseFunc) I (S I) x₀ =
        idealJoint (Functionality.ofDeterministic constFalseFunc) I (S I) x₁ := by
    have hx : I.restrict x₀ = I.restrict x₁ := by
      ext ⟨i, hi⟩
      have hi1 : i = 1 := Finset.mem_singleton.mp hi
      subst hi1
      rfl
    have hy : constFalseFunc x₀ = constFalseFunc x₁ := rfl
    simp [idealJoint, Functionality.ofDeterministic, hx, hy]
  have hReal0 :
      (leakyProtocol.realJoint noOracleWorld I x₀).map leakyExtractMsg1 = PMF.pure false := by
    simp [Protocol.realJoint, leakyProtocol, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero,
      ProbComp.eval_pure, Steps.evalWith_message, Steps.evalWith_done,
      PMF.pure_bind, PMF.pure_map, leakyExtractMsg1,
      Round.deliverMessage, x₀]
  have hReal1 :
      (leakyProtocol.realJoint noOracleWorld I x₁).map leakyExtractMsg1 = PMF.pure true := by
    simp [Protocol.realJoint, leakyProtocol, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero,
      ProbComp.eval_pure, Steps.evalWith_message, Steps.evalWith_done,
      PMF.pure_bind, PMF.pure_map, leakyExtractMsg1,
      Round.deliverMessage, x₁]
  rw [hIdealEq] at h0
  have hFalseEqTrue : (PMF.pure false : PMF Bool) = PMF.pure true := by
    rw [← hReal0, ← h0, h1, hReal1]
  have hApp := congrArg (fun p : PMF Bool => p true) hFalseEqTrue
  simp at hApp

/-! ### Negative test 2: Goldreich Counterexample 1 (Section 7.2.2.1, CUP print p. 621) -/

/-- Goldreich's Counterexample 1 functionality (Section 7.2.2.1, CUP print p. 621):
`((), ()) ↦ (r, false)` for a uniform bit `r` (with the empty output $\lambda$ modeled as
`false`). -/
noncomputable def goldreichCounterexample1Func :
    Functionality 2 (fun _ => Unit) (fun _ => Bool) :=
  fun _ => (fun b => ![b, false]) <$> ProbComp.uniform Bool

/-- Goldreich's Counterexample 1 protocol (Section 7.2.2.1, CUP print p. 621): party 0 picks a
uniform bit `r`, sends `r` to party 1, and outputs `r`, while party 1 outputs `false`. -/
noncomputable def goldreichCounterexample1Protocol :
    Protocol 2 noOracleSpec leakySchedule
      (fun _ => Unit) (fun _ => Bool) (fun _ => Bool) where
  sampleCoins i := if i = 0 then ProbComp.uniform Bool else pure false
  steps :=
    .message (sender := 0) (receiver := 1) (fun st => st.2)
      (.done fun i st => if i = 0 then st.1.2 else false)

/-- `goldreichCounterexample1Protocol` computes `goldreichCounterexample1Func` with zero error: its
joint output distribution equals `ProbComp.eval (goldreichCounterexample1Func x)`. -/
theorem eval_snd_goldreichCounterexample1Protocol (x : Fin 2 → Unit) :
    (goldreichCounterexample1Protocol.evalWith noOracleWorld x).map Prod.snd =
      ProbComp.eval (goldreichCounterexample1Func x) := by
  simp only [goldreichCounterexample1Protocol, goldreichCounterexample1Func,
    Protocol.evalWith_eq, OracleComp.pi_succ, OracleComp.pi_zero,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    Steps.evalWith_message, Steps.evalWith_done,
    Protocol.outputOfView, Steps.outputAt,
    ↓reduceIte, Fin.succ_ne_zero,
    PMF.bind_bind, PMF.pure_bind, PMF.pure_map, PMF.map_bind]
  rw [PMF.map]
  refine congrArg (ProbComp.eval (ProbComp.uniform Bool)).bind (funext fun b => ?_)
  refine congrArg PMF.pure (funext fun i => ?_)
  fin_cases i <;> rfl

/-- Marginal simulator for party 1 (`I = {1}`) in `goldreichCounterexample1Protocol` (satisfying
Goldreich Eq. 7.8 on p. 620): samples a uniform received bit `b ← ProbComp.uniform Bool`. -/
noncomputable def goldreichCounterexample1MarginalSim1 :
    CoalitionSimulator leakySchedule (fun _ => Unit)
      (fun _ => Bool) (fun _ => Bool) ({1} : Finset (Fin 2)) :=
  fun _ _ =>
    (fun (b : Bool) (_ : ({1} : Finset (Fin 2))) =>
      { input := ()
        coins := false
        received := (fun _ => b, ()) }) <$> ProbComp.uniform Bool

/-- Party 1's marginal view distribution in `goldreichCounterexample1Protocol` equals the output of
`goldreichCounterexample1MarginalSim1` (so the marginal-view equation Eq. 7.8 on p. 620 holds for
party 1). -/
theorem eval_goldreichCounterexample1MarginalSim1 (x : Fin 2 → Unit)
    (yI : ({1} : Finset (Fin 2)) → Bool) :
    ProbComp.eval (goldreichCounterexample1MarginalSim1 (({1} : Finset (Fin 2)).restrict x) yI) =
      (goldreichCounterexample1Protocol.evalWith noOracleWorld x).map
        (fun res => ({1} : Finset (Fin 2)).restrict res.1) := by
  simp only [goldreichCounterexample1MarginalSim1, goldreichCounterexample1Protocol,
    Protocol.evalWith_eq, OracleComp.pi_succ, OracleComp.pi_zero,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    Steps.evalWith_message, Steps.evalWith_done,
    ↓reduceIte, Fin.succ_ne_zero,
    PMF.bind_bind, PMF.pure_bind, PMF.pure_map, PMF.map_bind]
  rw [PMF.map]
  refine congrArg (ProbComp.eval (ProbComp.uniform Bool)).bind (funext fun b => ?_)
  refine congrArg PMF.pure (funext fun ⟨i, hi⟩ => ?_)
  have hi1 : i = 1 := Finset.mem_singleton.mp hi
  subst hi1
  refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
  refine Round.received_message_ext fun _ => rfl

/-- No simulator can make `goldreichCounterexample1Protocol` satisfy `PerfectSemiHonestPrivate` for
`goldreichCounterexample1Func` (Goldreich Eq. 7.10 on p. 620 / Eq. 7.40 on p. 696): at `I = {1}`,
party 1's received message in every real execution equals party 0's output `res.2 0`, whereas in
the ideal execution `S {1}` receives only `((), false)` independently of `res.2 0`. -/
theorem not_perfectSemiHonestPrivate_goldreichCounterexample1
    (S : (I : Finset (Fin 2)) →
      CoalitionSimulator leakySchedule (fun _ => Unit)
        (fun _ => Bool) (fun _ => Bool) I) :
    ¬ PerfectSemiHonestPrivate goldreichCounterexample1Protocol noOracleWorld
        goldreichCounterexample1Func S := by
  intro hPriv
  let I : Finset (Fin 2) := {1}
  let x : Fin 2 → Unit := fun _ => ()
  have hRealEq :
      ∀ res ∈ (goldreichCounterexample1Protocol.realJoint noOracleWorld I x).support,
        (res.1 ⟨1, by simp [I]⟩).received.1 rfl = res.2 0 := by
    intro res hres
    simp only [Protocol.realJoint, goldreichCounterexample1Protocol, Protocol.evalWith_eq,
      OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, Steps.evalWith_message, Steps.evalWith_done,
      Protocol.outputOfView, Steps.outputAt, ↓reduceIte, Fin.succ_ne_zero,
      PMF.pure_bind, PMF.pure_map, PMF.mem_support_map_iff, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hres
    obtain ⟨_, ⟨b, _, rfl⟩, rfl⟩ := hres
    rfl
  let yFalse : (i : I) → Bool := fun _ => false
  obtain ⟨v, hv⟩ := (ProbComp.eval (S I (I.restrict x) yFalse)).support_nonempty
  have hRestrict : ∀ b : Bool, I.restrict (![b, false] : Fin 2 → Bool) = yFalse := by
    intro b
    ext ⟨i, hi⟩
    have hi1 : i = 1 := Finset.mem_singleton.mp hi
    subst hi1
    rfl
  have hIdealMem : ∀ b : Bool,
      (v, (![b, false] : Fin 2 → Bool)) ∈
        (ProbComp.eval (idealJoint goldreichCounterexample1Func I (S I) x)).support := by
    intro b
    simp only [idealJoint, goldreichCounterexample1Func, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
      PMF.mem_support_pure_iff]
    refine ⟨![b, false], ⟨b, ?_, rfl⟩, v, ?_, rfl⟩
    · simp [ProbComp.eval_uniform]
    · rw [hRestrict b]
      exact hv
  have hMemFalse : (v, (![false, false] : Fin 2 → Bool)) ∈
      (goldreichCounterexample1Protocol.realJoint noOracleWorld I x).support := by
    rw [← hPriv I x]
    exact hIdealMem false
  have hMemTrue : (v, (![true, false] : Fin 2 → Bool)) ∈
      (goldreichCounterexample1Protocol.realJoint noOracleWorld I x).support := by
    rw [← hPriv I x]
    exact hIdealMem true
  have hEqFalse : (v ⟨1, by simp [I]⟩).received.1 rfl = false := hRealEq _ hMemFalse
  have hEqTrue : (v ⟨1, by simp [I]⟩).received.1 rfl = true := hRealEq _ hMemTrue
  rw [hEqFalse] at hEqTrue
  exact Bool.false_ne_true hEqTrue

/-! ### Negative test 3: output-correctness failure at `I = ∅` -/

/-- Randomized 2-party functionality `((), ()) ↦ (b, b)` for a uniform bit `b`. -/
noncomputable def coinBroadcastFunc : Functionality 2 (fun _ => Unit) (fun _ => Bool) :=
  fun _ => (fun b _ => b) <$> ProbComp.uniform Bool

/-- Zero-round protocol where each party independently samples a uniform bit `r i` and outputs `r i`
without communicating. Each singleton coalition's marginal view matches its marginal output, yet
the joint output distribution is independent rather than equal. -/
noncomputable def independentCoinProtocol :
    Protocol 2 noOracleSpec [] (fun _ => Unit) (fun _ => Bool) (fun _ => Bool) where
  sampleCoins _ := ProbComp.uniform Bool
  steps := .done fun _ st => st.2

/-- No simulator can make `independentCoinProtocol` satisfy `PerfectSemiHonestPrivate` for
`coinBroadcastFunc`, because in the ideal execution the two parties' outputs always agree
(`y 0 = y 1`), whereas in the real execution `![false, true]` occurs in the support of the joint
outputs. -/
theorem not_perfectSemiHonestPrivate_independentCoinProtocol
    (S : (I : Finset (Fin 2)) →
      CoalitionSimulator (spec := noOracleSpec) []
        (fun _ => Unit) (fun _ => Bool) (fun _ => Bool) I) :
    ¬ PerfectSemiHonestPrivate independentCoinProtocol noOracleWorld coinBroadcastFunc S := by
  intro hPriv
  have hIdealAgree :
      ∀ res ∈ (ProbComp.eval (idealJoint coinBroadcastFunc ∅ (S ∅) (fun _ => ()))).support,
        res.2 0 = res.2 1 := by
    intro res hres
    simp only [idealJoint, coinBroadcastFunc, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
      PMF.mem_support_pure_iff] at hres
    obtain ⟨y, ⟨b, _, rfl⟩, v, _, rfl⟩ := hres
    rfl
  have hRealDisagree :
      ∃ res ∈ (independentCoinProtocol.realJoint noOracleWorld ∅ (fun _ => ())).support,
        res.2 0 = false ∧ res.2 1 = true := by
    simp only [Protocol.realJoint, independentCoinProtocol, Protocol.evalWith_eq,
      Protocol.outputOfView, Steps.outputAt, Steps.evalWith_done,
      PMF.pure_map, PMF.mem_support_map_iff, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff]
    refine ⟨_, ⟨_, ⟨![false, true], ?_, rfl⟩, rfl⟩, rfl, rfl⟩
    rw [ProbComp.mem_support_pi_iff]
    intro i
    simp [ProbComp.eval_uniform]
  obtain ⟨res, hres, h0, h1⟩ := hRealDisagree
  rw [← hPriv ∅ (fun _ => ())] at hres
  have h01 := hIdealAgree res hres
  rw [h0, h1] at h01
  exact Bool.false_ne_true h01

/-! ### Ideal $\text{OT}_1^4$, 2-party shared multiplication, and $m$-party pairwise reduction -/

example : fin4ToBoolPair (boolPairToFin4 (true, false)) = (true, false) := by decide

/-- Exhaustive check of the 4-entry $\text{OT}_1^4$ residual table (Goldreich Section 7.3.3,
CUP print p. 643): for all party inputs `(a₀, b₀)` and `(a₁, b₁)` and sender coin `c₀`, the
receiver's $\text{OT}_1^4$ answer equals `c₀ + (a₀ + a₁) * (b₀ + b₁)`. -/
example (a₀ b₀ a₁ b₁ c₀ : Bool) :
    ot14Answer
      (fun s =>
        twoPartyMulQuery s
          (Fin.cases (a₀, b₀) (fun _ => (a₁, b₁)) s, twoPartyMulCoins c₀ s))
      1 = c₀ + (a₀ + a₁) * (b₀ + b₁) := by
  cases a₀ <;> cases b₀ <;> cases a₁ <;> cases b₁ <;> cases c₀ <;> rfl

/-- Locality of pairwise oracle rounds: in the 3-party setting, party `2` receives a subsingleton
record during the `(0, 1)` pairwise shared-multiplication round. -/
example :
    Subsingleton ((pairRound (m := 3) ⟨(0, 1), by decide⟩).Received 2) :=
  subsingleton_received_pairRound ⟨(0, 1), by decide⟩ (by decide) (by decide)

example : orderedPairs 1 = [] := by decide

example : (orderedPairs 3).length = 3 := by decide

example (I : Finset (Fin 1)) (x : Fin 1 → Bool × Bool) :
    ProbComp.eval (idealJoint (sharedMulFunctionality 1) I (multiPartyMulSim 1 I) x) =
      (multiPartyMulProtocol 1).realJoint (sharedMulWorld 2) I x :=
  perfectSemiHonestPrivate_multiPartyMul 1 I x

example (I : Finset (Fin 3)) (x : Fin 3 → Bool × Bool) :
    ProbComp.eval (idealJoint (sharedMulFunctionality 3) I (multiPartyMulSim 3 I) x) =
      (multiPartyMulProtocol 3).realJoint (sharedMulWorld 2) I x :=
  perfectSemiHonestPrivate_multiPartyMul 3 I x

/-! ### $m$-party Boolean circuit evaluation in `sharedMulWorld m` (Construction 7.5.10) -/

example :
    (Cslib.BitString.blocksEquiv (α := Bool) (m := 2) (k := 2)).symm
      ![![true, false], ![false, true]] =
    ![true, false, false, true] := by
  decide

/-- Concrete 2-party Boolean circuit with 2 gates:
- Gate 0 computes `x₀ && x₁` (`.and` of input wires 0 and 1);
- Gate 1 computes `!(x₀ && x₁)` (`.not` of Gate 0);
- Party 0 outputs `x₀ && x₁` (Gate 0) and party 1 outputs `!(x₀ && x₁)` (Gate 1). -/
def andNandCircuit : Cslib.Circuits.Circuit Boolean.signature (2 * 1) (2 * 1) where
  size := 2
  program :=
    ((Cslib.Circuits.Program.empty (σ := Boolean.signature) (inputCount := 2 * 1)).gate
      { op := Boolean.Op.and, wires := ![Wire.input 0, Wire.input 1] }).gate
      { op := Boolean.Op.not, wires := ![Wire.gate 0] }
  outputs := ![Wire.gate 0, Wire.gate 1]

/-- Exhaustive check of `circuitFunctionality 2 1 1 andNandCircuit` on all 4 input pairs `(b₀, b₁)`:
party 0 receives `b₀ && b₁` and party 1 receives `!(b₀ && b₁)`. -/
example (b₀ b₁ : Bool) :
    circuitFunctionality 2 1 1 andNandCircuit ![![b₀], ![b₁]] =
      ![![b₀ && b₁], ![!(b₀ && b₁)]] := by
  revert b₀ b₁
  decide

/-- Every outcome in the support of `(gmwCircuitProtocol 2 1 1 andNandCircuit).evalWith` has
outputs equal to `circuitFunctionality 2 1 1 andNandCircuit x`. -/
example (x : Fin 2 → BitString 1)
    (res : ((i : Fin 2) →
      PartyView (fun _ => BitString 1) (fun _ => Fin 1 → Fin 1 → Bool)
        (gmwCircuitSchedule 2 1 1 andNandCircuit) i) × (Fin 2 → BitString 1))
    (hres :
      res ∈ ((gmwCircuitProtocol 2 1 1 andNandCircuit).evalWith (sharedMulWorld 2) x).support) :
    res.2 = circuitFunctionality 2 1 1 andNandCircuit x :=
  snd_eq_circuitFunctionality_of_mem_support_evalWith andNandCircuit x hres

/-- `gmwCircuitProtocol 2 1 1 andNandCircuit` is perfectly semi-honest private in `sharedMulWorld 2`
against every static coalition `I : Finset (Fin 2)`. -/
example :
    PerfectSemiHonestPrivate
      (gmwCircuitProtocol 2 1 1 andNandCircuit) (sharedMulWorld 2)
      (Functionality.ofDeterministic (circuitFunctionality 2 1 1 andNandCircuit))
      (gmwCircuitSim 2 1 1 andNandCircuit) :=
  perfectSemiHonestPrivate_gmwCircuit 2 1 1 andNandCircuit

/-- Concrete 2-party circuit whose `outputs` vector exercises all three wire-reuse patterns
handled by the Step 3 `sharedMulSpec m` share refresh:
- Party 0's output bit 0 is an input wire directly (`Wire.input 0`);
- Party 0's output bit 1 and Party 1's output bit 0 both reuse the same gate wire (`Wire.gate 0`);
- Party 1's output bit 1 is a negated wire (`Wire.gate 1`) of `Wire.gate 0`. -/
def wireReuseCircuit : Cslib.Circuits.Circuit Boolean.signature (2 * 1) (2 * 2) where
  size := 2
  program :=
    ((Cslib.Circuits.Program.empty (σ := Boolean.signature) (inputCount := 2 * 1)).gate
      { op := Boolean.Op.and, wires := ![Wire.input 0, Wire.input 1] }).gate
      { op := Boolean.Op.not, wires := ![Wire.gate 0] }
  outputs := ![Wire.input 0, Wire.gate 0, Wire.gate 0, Wire.gate 1]

/-- Exhaustive check of `circuitFunctionality 2 1 2 wireReuseCircuit` on all 4 input pairs
`(b₀, b₁)`: party 0 receives `![b₀, b₀ && b₁]` and party 1 receives
`![b₀ && b₁, !(b₀ && b₁)]`. -/
example (b₀ b₁ : Bool) :
    circuitFunctionality 2 1 2 wireReuseCircuit ![![b₀], ![b₁]] =
      ![![b₀, b₀ && b₁], ![b₀ && b₁, !(b₀ && b₁)]] := by
  revert b₀ b₁
  decide

/-- `gmwCircuitProtocol 2 1 2 wireReuseCircuit` is perfectly semi-honest private in
`sharedMulWorld 2` against every static coalition `I : Finset (Fin 2)`, even though `outputs`
includes an input wire, a wire shared across both parties, and its negation. -/
example :
    PerfectSemiHonestPrivate
      (gmwCircuitProtocol 2 1 2 wireReuseCircuit) (sharedMulWorld 2)
      (Functionality.ofDeterministic (circuitFunctionality 2 1 2 wireReuseCircuit))
      (gmwCircuitSim 2 1 2 wireReuseCircuit) :=
  perfectSemiHonestPrivate_gmwCircuit 2 1 2 wireReuseCircuit

/-- 3-party circuit evaluation privacy (`m = 3`) for any circuit `C`. -/
example (C : Cslib.Circuits.Circuit Boolean.signature (3 * 2) (3 * 1))
    (I : Finset (Fin 3)) (x : Fin 3 → BitString 2) :
    ProbComp.eval
      (idealJoint (Functionality.ofDeterministic (circuitFunctionality 3 2 1 C))
        I (gmwCircuitSim 3 2 1 C I) x) =
      (gmwCircuitProtocol 3 2 1 C).realJoint (sharedMulWorld 3) I x :=
  perfectSemiHonestPrivate_gmwCircuit 3 2 1 C I x

/-- Degenerate 1-party circuit evaluation privacy (`m = 1`) for any circuit `C`. -/
example (C : Cslib.Circuits.Circuit Boolean.signature (1 * 2) (1 * 2))
    (I : Finset (Fin 1)) (x : Fin 1 → BitString 2) :
    ProbComp.eval
      (idealJoint (Functionality.ofDeterministic (circuitFunctionality 1 2 2 C))
        I (gmwCircuitSim 1 2 2 C I) x) =
      (gmwCircuitProtocol 1 2 2 C).realJoint (sharedMulWorld 1) I x :=
  perfectSemiHonestPrivate_gmwCircuit 1 2 2 C I x

/-! ### Subprotocol composition, `xorPreludeCircuit`, and $\text{OT}_1^4$-hybrid GMW (M4) -/

/-- Exhaustive check of `xorPreludeCircuit 2 1 1` on all 16 combinations of 2-party 1-bit inputs
`(b₀, b₁)` and 1-bit coin shares `(r₀, r₁)`: outputs `![b₀, b₁, r₀ + r₁]`. -/
example (b₀ b₁ r₀ r₁ : Bool) :
    (xorPreludeCircuit 2 1 1).eval Boolean.interpretation
      ![b₀, r₀, b₁, r₁] =
    ![b₀, b₁, r₀ + r₁] := by
  revert b₀ b₁ r₀ r₁
  decide

/-- Gate count of `xorPreludeCircuit 3 2 4` is `1 + 3 * (4 * 4) = 49`. -/
example : (xorPreludeCircuit 3 2 4).size = 49 := by
  simp [size_xorPreludeCircuit]

/-- Composing `multiPartyMulSchedule 3` with `twoPartyMulSchedule` expands into `3 * 2 / 2 = 3`
pairwise `ot14Spec` oracle rounds. -/
example :
    (Schedule.compose (fun _ => twoPartyMulSchedule) (multiPartyMulSchedule 3)).length = 3 :=
  rfl

/-- Composing `multiPartyMulProtocol 3` with `twoPartyMulProtocol` via
`PerfectSemiHonestPrivate.compose` (Theorem 7.5.7) yields a 3-party shared-multiplication protocol
in `ot14World` that is perfectly semi-honest private against every static coalition
`I : Finset (Fin 3)`. -/
example :
    PerfectSemiHonestPrivate
      ((multiPartyMulProtocol 3).compose (fun _ => twoPartyMulProtocol))
      ot14World (sharedMulFunctionality 3)
      (composeSim (multiPartyMulProtocol 3) (multiPartyMulSim 3) (fun _ => twoPartyMulSim)) :=
  (perfectSemiHonestPrivate_multiPartyMul 3).compose (fun _ => perfectSemiHonestPrivate_twoPartyMul)

/-- For `m = 2`, `n = 1`, `k = 1`, and `andNandCircuit` (1 `.and` gate and 1 `.not` gate),
`gmwCircuitSchedule 2 1 1 andNandCircuit` has 4 Step 1 message rounds, 1 Step 2 `sharedMulSpec 2`
oracle round, and `2 * 1 = 2` Step 3 share-refresh `sharedMulSpec 2` oracle rounds plus 4 Step 3
message rounds; composing with `multiPartyMulSchedule 2` and `twoPartyMulSchedule` expands the
`1 + 2 = 3` `sharedMulSpec 2` calls into `3 * (2 * 1 / 2) = 3` `ot14Spec` oracle rounds (11 rounds
in total). -/
example :
    (Schedule.compose (fun _ => twoPartyMulSchedule)
      (Schedule.compose (fun _ => multiPartyMulSchedule 2)
        (gmwCircuitSchedule 2 1 1 andNandCircuit))).length = 11 :=
  rfl

/-- `gmwOT14Protocol 2 1 1 andNandCircuit` is perfectly semi-honest private in `ot14World` against
every static coalition `I : Finset (Fin 2)`. -/
example :
    PerfectSemiHonestPrivate
      (gmwOT14Protocol 2 1 1 andNandCircuit) ot14World
      (Functionality.ofDeterministic (circuitFunctionality 2 1 1 andNandCircuit))
      (gmwOT14Sim 2 1 1 andNandCircuit) :=
  perfectSemiHonestPrivate_gmwOT14 2 1 1 andNandCircuit

/-- `gmwOT14Protocol 2 1 2 wireReuseCircuit` is perfectly semi-honest private in `ot14World` against
every static coalition `I : Finset (Fin 2)`. -/
example :
    PerfectSemiHonestPrivate
      (gmwOT14Protocol 2 1 2 wireReuseCircuit) ot14World
      (Functionality.ofDeterministic (circuitFunctionality 2 1 2 wireReuseCircuit))
      (gmwOT14Sim 2 1 2 wireReuseCircuit) :=
  perfectSemiHonestPrivate_gmwOT14 2 1 2 wireReuseCircuit

/-- Concrete 2-party randomized Boolean circuit (`m = 2`, `n = 1`, `coins = 1`, `k = 1`) where
input wire 0 is `x₀`, input wire 1 is `x₁`, input wire 2 is the shared coin bit `r`, party 0
outputs `x₀ && r` (Gate 0), and party 1 outputs `x₁ && r` (Gate 1). -/
def randomizedAndCoinCircuit : Cslib.Circuits.Circuit Boolean.signature (2 * 1 + 1) (2 * 1) where
  size := 2
  program :=
    ((Cslib.Circuits.Program.empty (σ := Boolean.signature) (inputCount := 2 * 1 + 1)).gate
      { op := Boolean.Op.and, wires := ![Wire.input 0, Wire.input 2] }).gate
      { op := Boolean.Op.and, wires := ![Wire.input 1, Wire.input 2] }
  outputs := ![Wire.gate 0, Wire.gate 1]

/-- Theorem 7.5.12 instantiated on `randomizedAndCoinCircuit`:
`gmwOT14RandomizedProtocol 2 1 1 1 randomizedAndCoinCircuit` is perfectly semi-honest private in
`ot14World` against every proper static coalition `I ≠ Finset.univ`. -/
example :
    PerfectSemiHonestPrivateProper
      (gmwOT14RandomizedProtocol 2 1 1 1 randomizedAndCoinCircuit) ot14World
      (randomizedFunctionality 1 (fun r x i =>
        Cslib.BitString.block
          (randomizedAndCoinCircuit.eval Boolean.interpretation
            (Fin.append
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := 2) (k := 1)).symm x) r)) i))
      (gmwOT14RandomizedSim 2 1 1 1 randomizedAndCoinCircuit) :=
  perfectSemiHonestPrivateProper_gmwOT14Randomized 2 1 1 1 randomizedAndCoinCircuit

/-- Trivial 1-party 0-round protocol outputting its 1-bit coin input `(xr 0).2 0`, used to verify
that the proper-coalition hypothesis `I ≠ Finset.univ` in
`perfectSemiHonestPrivate_randomizedWrapper` cannot be dropped when `I = Finset.univ`. -/
def coinEchoDetProtocol :
    Protocol 1 noOracleSpec [] (fun _ => Unit × BitString 1) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps := .done fun _ st => st.1.2 0

/-- Trivial simulator for `coinEchoDetProtocol`. -/
def coinEchoDetSim (I : Finset (Fin 1)) :
    CoalitionSimulator (spec := noOracleSpec) [] (fun _ => Unit × BitString 1)
      (fun _ => Unit) (fun _ => Bool) I :=
  fun xI _ => pure (fun i => ⟨xI i, (), ()⟩)

/-- `coinEchoDetProtocol` is perfectly semi-honest private against all coalitions `I` for
`detOfRandomized 1 (fun r _ _ => r 0)`. -/
theorem perfectSemiHonestPrivate_coinEchoDet :
    PerfectSemiHonestPrivate coinEchoDetProtocol noOracleWorld
      (Functionality.ofDeterministic (detOfRandomized 1 (fun r (_ : Fin 1 → Unit) _ => r 0)))
      coinEchoDetSim := by
  intro I x
  simp only [idealJoint, coinEchoDetSim, Functionality.ofDeterministic, detOfRandomized,
    Protocol.realJoint, Protocol.evalWith_eq, coinEchoDetProtocol,
    OracleComp.pi_succ, OracleComp.pi_zero, Protocol.outputOfView,
    Steps.evalWith_done, Steps.outputAt,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.pure_bind, PMF.pure_map, Finset.restrict_def, Fin.sum_univ_one]
  refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, _⟩ => ?_) (funext fun i => ?_))
  · fin_cases i
    rfl
  · fin_cases i
    rfl

/-- Negative test for `perfectSemiHonestPrivate_randomizedWrapper` at `I = Finset.univ`:
although `coinEchoDetProtocol` satisfies `PerfectSemiHonestPrivate` for all coalitions,
`coinEchoDetProtocol.randomizedWrapper 1` with `randomizedWrapperSim 1 coinEchoDetSim` FAILS
at the full coalition `I = Finset.univ`, because every real execution satisfies
`(v 0).coins.1 0 = y 0` whereas `randomizedWrapperSim` samples the coalition's coin shares
independently of the ideal output `y 0`. -/
theorem not_perfectSemiHonestPrivate_coinEchoRandomizedWrapper_univ :
    ¬ PerfectSemiHonestPrivate (coinEchoDetProtocol.randomizedWrapper 1) noOracleWorld
        (randomizedFunctionality 1 (fun r (_ : Fin 1 → Unit) _ => r 0))
        (randomizedWrapperSim 1 coinEchoDetSim) := by
  intro hAll
  have hUniv := hAll Finset.univ (fun _ => ())
  have hRealEq :
      ∀ res ∈ ((coinEchoDetProtocol.randomizedWrapper 1).realJoint
          noOracleWorld Finset.univ (fun _ => ())).support,
        (res.1 ⟨0, Finset.mem_univ 0⟩).coins.1 0 = res.2 0 := by
    intro res hres
    simp only [Protocol.realJoint, Protocol.evalWith_eq, Protocol.outputOfView,
      Protocol.randomizedWrapper, coinEchoDetProtocol,
      OracleComp.pi_succ, OracleComp.pi_zero,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_uniform,
      Steps.evalWith_mapState, Steps.evalWith_done,
      Steps.outputAt_mapState, Steps.outputAt,
      PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
      PMF.mem_support_uniformOfFintype, Finset.restrict_def] at hres
    obtain ⟨_, ⟨a, _, rfl⟩, rfl⟩ := hres
    rfl
  let badRes :
      ((i : (Finset.univ : Finset (Fin 1))) →
        PartyView (fun _ => Unit) (fun _ => BitString 1 × Unit)
          ([] : Schedule 1 noOracleSpec) i.1) × (Fin 1 → Bool) :=
    (fun _ => ⟨(), (![true], ()), ()⟩, fun _ => false)
  have hBadIdeal :
      badRes ∈ (ProbComp.eval
        (idealJoint (randomizedFunctionality 1 (fun r (_ : Fin 1 → Unit) _ => r 0))
          Finset.univ (randomizedWrapperSim 1 coinEchoDetSim Finset.univ)
          (fun _ => ()))).support := by
    simp only [idealJoint, randomizedFunctionality, randomizedWrapperSim, coinEchoDetSim,
      OracleComp.piRestrict, Finset.mem_univ, ↓reduceDIte,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_uniform,
      PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
      PMF.mem_support_uniformOfFintype]
    refine ⟨![false], trivial, ![true], trivial, ?_⟩
    refine Prod.ext (funext fun ⟨i, _⟩ => ?_) (funext fun i => ?_)
    · fin_cases i
      refine PartyView.ext rfl (Prod.ext ?_ rfl) rfl
      ext j
      fin_cases j
      rfl
    · fin_cases i
      rfl
  rw [hUniv] at hBadIdeal
  have hEq := hRealEq badRes hBadIdeal
  exact Bool.noConfusion hEq

/-! ### Milestone 5: Word-level $\text{OT}_1^4$ runner, bridge lemma, and polynomial-time
completeness (Theorem 7.5.12) -/

/-- `encodeCoinsAndInputs 2 1 2` packs two 2-bit party inputs followed by a 1-bit coin tape into a
5-bit list. -/
example :
    encodeCoinsAndInputs 2 1 2 ![true] ![![false, true], ![true, false]] =
      [false, true, true, false, true] := by
  decide

/-- Concrete check of `ot14WordHandler` on `encodeOT14Query` for table `![false, true, false, true]`
and selection index `3 : Fin 4`: returns `[true]`. -/
example :
    ot14WordHandler
      ((), encodeOT14Query (Fin.cases ![false, true, false, true] (fun _ => (3 : Fin 4)))) () =
    PMF.pure ([true], ()) :=
  rfl

/-- Concrete behavioral consequence of the bridge lemma (`Protocol.eval_runEncoded_eq_evalWith_map`)
and `perfectSemiHonestPrivate_twoPartyMul` at `I = ∅`: on input `![(true, true), (false, false)]`
(where `(a₀ + a₁) * (b₀ + b₁) = true * true = true`), every word produced by
`twoPartyMulProtocol.runEncoded` (with empty view encoding and 1-bit output encoding) under
`ot14WordHandler` encodes a pair of complementary shares `[[b], [!b]]`. -/
example {res : List Bool × Unit}
    (hres : res ∈ (Cslib.ProbOracleComp.runWith ot14WordHandler
      (twoPartyMulProtocol.runEncoded
        (fun _ _ => []) (fun _ b => [b]) ![(true, true), (false, false)]) ()).support) :
    ∃ b : Bool,
      res.1 =
        Turing.MultiTapeTM.encPair
          (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)
          (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)
          ([[], []], [[b], [!b]]) := by
  have hfst : res.1 ∈ ((Cslib.ProbOracleComp.runWith ot14WordHandler
      (twoPartyMulProtocol.runEncoded
        (fun _ _ => []) (fun _ b => [b])
        ![(true, true), (false, false)]) ()).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨res, hres, rfl⟩
  rw [Protocol.eval_runEncoded_eq_evalWith_map, PMF.mem_support_map_iff] at hfst
  obtain ⟨⟨v, y⟩, hvy, hres1⟩ := hfst
  have hpriv := congrArg (PMF.map Prod.snd)
    (perfectSemiHonestPrivate_twoPartyMul ∅ ![(true, true), (false, false)])
  have hy_mem : y ∈ ((twoPartyMulProtocol.realJoint
      ot14World ∅ ![(true, true), (false, false)]).map Prod.snd).support := by
    rw [Protocol.realJoint, PMF.map_comp, PMF.mem_support_map_iff]
    exact ⟨(v, y), hvy, rfl⟩
  rw [← hpriv] at hy_mem
  simp only [idealJoint, sharedMulFunctionality, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hy_mem
  obtain ⟨y, hy', _, _, rfl⟩ := hy_mem
  have hsum : y 0 + y 1 = (true + false) * (true + false) := by
    simpa [Fin.sum_univ_two] using ProbComp.sum_sampleAdditiveShares _ hy'
  have hb₁ : y 1 = !(y 0) := by
    revert hsum
    generalize y 0 = b₀
    generalize y 1 = b₁
    intro hsum
    revert b₀ b₁ hsum
    decide
  refine ⟨y 0, ?_⟩
  rw [← hres1]
  simp only [encodeViewsAndOutputs, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, Fin.succ_zero_eq_one, hb₁]

/-- For `F (a, w) = w.tail` at `a = 1` (`m = 2`, `coins = n = k = id`), `encodeCoinsAndInputs 2 1 1`
packs `[b₀, b₁, c]`, whose tail `[b₁, c]` assigns party 1's private input bit `b₁` to party 0's
output and the shared random coin bit `c` to party 1's output. -/
example (b₀ b₁ c : Bool) :
    (encodeCoinsAndInputs 2 1 1 ![c] ![![b₀], ![b₁]]).tail = [b₁, c] :=
  rfl

/-- Concrete end-to-end instantiation of the proper-coalition variant of Theorem 7.5.12
(`exists_perfectSemiHonestPrivate_ot14_of_polyTime`) on the polynomial-time family indexed by
`a : ℕ` (`encUnary`) with `m = 2`, `coins a = a`, `n a = a`, `k a = a`, and cross-party /
coin-dependent shift functionality `F (a, w) = w.tail` (under which party 0's output depends on
party 1's input and party 1's output depends on the shared coins for `a ≥ 1`). -/
example :
    ∃ C : (a : ℕ) → Cslib.Circuits.Circuit Boolean.signature (2 * a + a) (2 * a),
      Turing.MultiTapeTM.ComputableInPolyTime (fun a => (C a).code)
        Turing.MultiTapeTM.encUnary Boolean.encCode ∧
      (∀ a (xr : Fin (2 * a + a) → Bool) (j : Fin (2 * a)),
        (C a).eval Boolean.interpretation xr j = (List.ofFn xr).tail.getD j.val false) ∧
      (∀ a, PerfectSemiHonestPrivateProper
        (gmwOT14RandomizedProtocol 2 a a a (C a)) ot14World
        (wordRandomizedFunctionality 2 id id id (fun p : ℕ × List Bool => p.2.tail) a)
        (gmwOT14RandomizedSim 2 a a a (C a))) ∧
      Cslib.Probability.IsOraclePPTOn
        (encFamilyRunInput Turing.MultiTapeTM.encUnary 2 id)
        Turing.MultiTapeTM.encBits
        (fun inp =>
          (gmwOT14RandomizedProtocol 2 inp.1 inp.1 inp.1 (C inp.1)).runEncoded
            (encGMWPartyView 2 inp.1 inp.1 inp.1 (C inp.1))
            (fun _ y => List.ofFn y) inp.2) ∧
      (∀ (I : Finset (Fin 2)), I ≠ Finset.univ →
        Cslib.Probability.IsPPTOn
          (encFamilySimInput Turing.MultiTapeTM.encUnary 2 id id I)
          Turing.MultiTapeTM.encBits
          (fun inp =>
            encodeCoalitionView (encGMWPartyView 2 inp.1 inp.1 inp.1 (C inp.1)) I <$>
              gmwOT14RandomizedSim 2 inp.1 inp.1 inp.1 (C inp.1) I inp.2.1 inp.2.2)) :=
  exists_perfectSemiHonestPrivate_ot14_of_polyTime 2
    Turing.MultiTapeTM.ComputableInPolyTime.id'
    Turing.MultiTapeTM.ComputableInPolyTime.id'
    Turing.MultiTapeTM.ComputableInPolyTime.id'
    (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy
      (Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsTail.comp
        (Turing.MultiTapeTM.ComputableTidilyInPolyTime.snd
          Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits)))

end ComplexityTests.Crypto.MPC
