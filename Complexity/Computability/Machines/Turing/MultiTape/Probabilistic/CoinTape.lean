/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import Complexity.Probability.BitString
import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Execution with saved coins

Replay is a fold of one-step calls to the shared interpreter, with each supplied coin returned
by a pure program. Exhausting the list retains the complete current configuration; a halted
machine ignores the remaining coins. Query handlers can still have effects.

Sampling all coins in advance preserves the joint final configuration and private oracle state,
provided the original coin program denotes a stateless fair bit. The query handler may be
randomized and share state across its operations. This is a semantic equality; a deterministic
machine implementing replay from an encoded input and coin tape needs a separate certificate.

## Main definitions

* `Turing.MultiTapePTM.runConfigFromCoins`: replay from an arbitrary configuration.

## Main results

* `Turing.MultiTapePTM.runConfigFromCoins_append`: pause and resume at a tape boundary.
* `Turing.MultiTapePTM.run_interpret_runConfigFrom_eq_coins`: average fixed-coin runs, retaining
  the complete configuration and private state.

## References

Adapted from the cslib `crypto` branch's
Computability/Machines/Turing/MultiTape/Probabilistic/CoinTape.lean at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common interpreter and typed program API.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Replay the shared interpreter with a supplied coin per step. Only the query handler can
have effects; the replay itself does not draw randomness. -/
def runConfigFromCoins (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input) :
    OracleComp spec (Config k Symbol State Oracle input) :=
  coins.foldlM (fun cfg bit => machine.runConfigFrom (pure bit) query 1 cfg) cfg

@[simp] theorem runConfigFromCoins_nil (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFromCoins query [] cfg = pure cfg := rfl

/-- The first coin supplies one instruction before replay resumes on the tail. -/
theorem runConfigFromCoins_cons (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (bit : Bool) (coins : List Bool) (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFromCoins query (bit :: coins) cfg =
      (machine.runConfigFrom (pure bit) query 1 cfg >>= machine.runConfigFromCoins query coins) :=
  List.foldlM_cons

/-- A halted machine ignores all remaining coins and performs no further queries. -/
@[simp] theorem runConfigFromCoins_halted (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input)
    (h : cfg.tapes.state = none) : machine.runConfigFromCoins query coins cfg = pure cfg := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    simp [runConfigFromCoins_cons, runConfigFrom, MultiTapeMachine.runConfigFrom_halted, h, ih]

/-- Concatenating tapes agrees with pausing and resuming, as an equality of typed programs. -/
theorem runConfigFromCoins_append (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins more : List Bool) (cfg : Config k Symbol State Oracle input) :
    machine.runConfigFromCoins query (coins ++ more) cfg =
      (machine.runConfigFromCoins query coins cfg >>= machine.runConfigFromCoins query more) :=
  List.foldlM_append

/-- Interpretation commutes with the replay fold, without resetting any handler state. -/
theorem interpret_runConfigFromCoins {m : Type → Type*} [Monad m] [LawfulMonad m]
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → m (spec q)) (coins : List Bool)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp.interpret oracle (machine.runConfigFromCoins query coins cfg) =
      coins.foldlM (fun cfg bit =>
        OracleComp.interpret oracle (machine.runConfigFrom (pure bit) query 1 cfg)) cfg :=
  (PFunctor.FreeM.isMonadHom_liftM (P := ⟨Query, spec⟩) oracle).map_listFoldlM _ _ _

/-- A single instruction can use a pre-sampled coin when the coin program is stateless and fair.
The entire query handler state is retained. -/
theorem run_interpret_runConfigFrom_one {OracleState : Type}
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s =
      (PMF.uniformOfFintype Bool).map (fun bit => (bit, s)))
    (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle (machine.runConfigFrom coin query 1 cfg)).run s =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        (OracleComp.interpret oracle (machine.runConfigFrom (pure bit) query 1 cfg)).run s) := by
  cases hs : cfg.tapes.state <;>
    simp [runConfigFrom, MultiTapeMachine.runConfigFrom, hs, bind_map_left,
      OracleComp.interpret_bind, StateT.run_bind, hcoin, PMF.bind_map, Function.comp_def]

/-- Sampling the entire private coin tape in advance preserves the joint configuration and
private oracle state, including randomized query handlers sharing that state. -/
theorem run_interpret_runConfigFrom_eq_coins {OracleState : Type}
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s =
      (PMF.uniformOfFintype Bool).map (fun bit => (bit, s)))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle (machine.runConfigFrom coin query fuel cfg)).run s =
      (BitString.uniformList fuel).bind (fun coins =>
        (OracleComp.interpret oracle (machine.runConfigFromCoins query coins cfg)).run s) := by
  induction fuel generalizing cfg s with
  | zero => simp [runConfigFrom]
  | succ fuel ih =>
    rw [BitString.uniformList_succ, show fuel + 1 = 1 + fuel by lia, runConfigFrom,
      MultiTapeMachine.runConfigFrom_add]
    change (OracleComp.interpret oracle
      (machine.runConfigFrom coin query 1 cfg >>= machine.runConfigFrom coin query fuel)).run s = _
    simp only [OracleComp.interpret_bind, StateT.run_bind, PMF.monad_bind_eq_bind,
      run_interpret_runConfigFrom_one machine coin query oracle hcoin, PMF.bind_bind, ih,
      PMF.bind_map, Function.comp_def, runConfigFromCoins_cons]
    congr 1
    funext bit
    exact PMF.bind_comm _ _ _

/-- Without private state, the clocked run is the average of its fixed-coin programs. -/
theorem interpret_runConfigFrom_eq_coins
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → PMF (spec q))
    (hcoin : OracleComp.interpret oracle coin = PMF.uniformOfFintype Bool)
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    OracleComp.interpret oracle (machine.runConfigFrom coin query fuel cfg) =
      (BitString.uniformList fuel).bind (fun coins =>
        OracleComp.interpret oracle (machine.runConfigFromCoins query coins cfg)) := by
  have h := run_interpret_runConfigFrom_eq_coins machine coin query
    (fun q (s : Unit) => (fun a => (a, s)) <$> oracle q)
    (fun s => by rw [OracleComp.run_interpret_stateless, hcoin]; rfl) fuel cfg ()
  simp_rw [OracleComp.run_interpret_stateless] at h
  have hout := congrArg (PMF.map Prod.fst) h
  simpa [PMF.map, PMF.bind_bind, Function.comp_def] using hout

/-- Observe the output of a replay program, retaining any effects of its query handler. -/
def runFromCoins (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input) :
    OracleComp spec (List Symbol) :=
  (fun final => final.tapes.output) <$> machine.runConfigFromCoins query coins cfg

/-- Replay from blank work and communication tapes. -/
def runCoins (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (input : List Symbol) : OracleComp spec (List Symbol) :=
  machine.runFromCoins query coins (machine.initialConfig input)

/-- Fix one Boolean branch of a closed table, retaining its original states and tapes. -/
def withCoin (machine : MultiTapePTM k Symbol State) (bit : Bool) :
    MultiTapeMachine k Symbol State Empty Id where
  initial := machine.initial
  tr state symbol work answer := machine.tr state symbol work answer bit

/-- Closed replay is a deterministic fold of the selected one-step transition tables. -/
def runClosedConfigFromCoins (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    Config k Symbol State Empty input :=
  coins.foldl (fun cfg bit => (machine.withCoin bit).step cfg) cfg

/-- A closed one-step program with a fixed coin is a pure deterministic transition. -/
theorem runConfigFrom_pure_coin (machine : MultiTapePTM k Symbol State) (bit : Bool)
    (cfg : Config k Symbol State Empty input) :
    machine.runConfigFrom (spec := spec) (pure bit) Empty.elim 1 cfg =
      pure ((machine.withCoin bit).step cfg) := by
  cases hs : cfg.tapes.state with
  | none => simp [runConfigFrom, MultiTapeMachine.runConfigFrom, MultiTapeMachine.step, hs]
  | some state =>
    simp only [runConfigFrom, MultiTapeMachine.runConfigFrom, MultiTapeMachine.step,
      withCoin, hs, map_pure, pure_bind]
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with
    | step action symbol move => rfl
    | query oracle _ => exact oracle.elim

/-- With no oracle channels, the entire fixed-coin program is pure. -/
theorem runConfigFromCoins_closed (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    machine.runConfigFromCoins (spec := spec) Empty.elim coins cfg =
      pure (machine.runClosedConfigFromCoins coins cfg) := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons bit coins ih =>
    simp [runConfigFromCoins_cons, runConfigFrom_pure_coin, ih, runClosedConfigFromCoins]

/-- The output of a closed replay from blank tapes, as a deterministic function. -/
def runClosedCoins (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (input : List Symbol) : List Symbol :=
  (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output

/-- The complete closed configuration is a deterministic function of uniform saved coins. -/
theorem eval_runClosedConfigFrom_eq_map_coins (machine : MultiTapePTM k Symbol State)
    (fuel : ℕ) (cfg : Config k Symbol State Empty input) :
    ProbComp.eval (machine.runClosedConfigFrom fuel cfg) =
      (BitString.uniformList fuel).map
        (fun coins => machine.runClosedConfigFromCoins coins cfg) := by
  rw [runClosedConfigFrom, ProbComp.eval, interpret_runConfigFrom_eq_coins machine _ _ _
    (ProbComp.eval_uniform Bool)]
  simp [runConfigFromCoins_closed, PMF.map, Function.comp_def]

/-- A closed fair-coin run is a deterministic function of a uniform tape of clock length. -/
theorem eval_runClosed_eq_map_coins (machine : MultiTapePTM k Symbol State)
    (fuel : ℕ) (input : List Symbol) :
    ProbComp.eval (machine.runClosed fuel input) =
      (BitString.uniformList fuel).map (fun coins => machine.runClosedCoins coins input) := by
  rw [runClosed_eq_map, ProbComp.eval_map, eval_runClosedConfigFrom_eq_map_coins, PMF.map_comp]
  rfl

/-- Every saved tape yields a supported configuration at the corresponding clock. -/
theorem runClosedConfigFromCoins_mem_support (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    machine.runClosedConfigFromCoins coins cfg ∈
      (ProbComp.eval (machine.runClosedConfigFrom coins.length cfg)).support := by
  rw [eval_runClosedConfigFrom_eq_map_coins]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨coins, BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩

/-- Every saved tape yields a supported output, including inputs that run to the clock cutoff. -/
theorem runClosedCoins_mem_support (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (input : List Symbol) :
    machine.runClosedCoins coins input ∈
      (ProbComp.eval (machine.runClosed coins.length input)).support := by
  rw [eval_runClosed_eq_map_coins]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨coins, BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩

end Turing.MultiTapePTM
