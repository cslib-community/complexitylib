/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.MPC.Basic
import Complexity.Crypto.Protocols.MPC.SharedMul
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

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto.Protocols.MPC

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

example : (orderedPairs 3).length = 3 := by decide

example (I : Finset (Fin 2)) (x : Fin 2 → Bool × Bool) :
    ProbComp.eval (idealJoint (sharedMulFunctionality 2) I (twoPartyMulSim I) x) =
      twoPartyMulProtocol.realJoint ot14World I x :=
  perfectSemiHonestPrivate_twoPartyMul I x

example (x : Fin 3 → Bool × Bool) (r : OrderedPair 3 → Bool) :
    (∑ i : Fin 3, realOut x r i) = (∑ i : Fin 3, (x i).1) * (∑ i : Fin 3, (x i).2) :=
  sum_realOut x r

example (I : Finset (Fin 3)) (x : Fin 3 → Bool × Bool) :
    ProbComp.eval (idealJoint (sharedMulFunctionality 3) I (multiPartyMulSim 3 I) x) =
      (multiPartyMulProtocol 3).realJoint (sharedMulWorld 2) I x :=
  perfectSemiHonestPrivate_multiPartyMul 3 I x

end ComplexityTests.Crypto.MPC
