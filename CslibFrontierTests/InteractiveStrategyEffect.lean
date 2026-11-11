/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.StrategyEffect

/-!
# Stateful clients of strategy effect translation

The first client checks the full initialization/round/terminal effect order against a counter.
The second uses distinct role oracles and retains a private coin across the challenge and reply.
-/

namespace CslibFrontierTests.InteractiveStrategyEffect

open Cslib Cslib.Interactive Spec Probability

abbrev rounds : Spec :=
  [.prover Nat (OracleInterface.full Nat), .verifier Nat,
    .prover Nat (OracleInterface.full Nat)]

abbrev calls : OracleSpec Unit := fun _ => Nat

def sender : OracleComp calls (ProverStrategy (OracleComp calls) rounds Nat) := do
  let seed ← OracleComp.query ()
  return (show OracleComp calls (Nat × ProverStrategy (OracleComp calls)
    [.verifier Nat, .prover Nat (OracleInterface.full Nat)] Nat) from do
    let first ← OracleComp.query ()
    return (seed + first, fun challenge => pure (show OracleComp calls (Nat × Nat) from do
      let last ← OracleComp.query ()
      return (seed + challenge + last, seed))))

def receiver : OracleComp calls
    (VerifierStrategy (OracleComp calls) rounds (Nat × Nat × Nat × Nat × Nat)) := do
  let seed ← OracleComp.query ()
  return fun first => do
    let fresh ← OracleComp.query ()
    return (show OracleComp calls (Nat × VerifierStrategy (OracleComp calls)
      [.prover Nat (OracleInterface.full Nat)] (Nat × Nat × Nat × Nat × Nat)) from
      pure (seed + first + fresh, fun last => do
        let again ← OracleComp.query ()
        return (show OracleComp calls (Nat × Nat × Nat × Nat × Nat) from do
          let terminal ← OracleComp.query ()
          return (seed, first, last, again, terminal))))

def counter (_ : Unit) : StateM Nat Nat := fun state => (state, state + 1)

def translated : StateM Nat
    (Transcript rounds × Nat × (Nat × Nat × Nat × Nat × Nat)) := do
  let p ← OracleComp.interpret counter sender
  let v ← OracleComp.interpret counter receiver
  runAgainst rounds
    (ProverStrategy.hoist (OracleComp.interpret counter) rounds p)
    (VerifierStrategy.hoist (OracleComp.interpret counter) rounds v)

/-- Initialization effects and all continuations share one state, including the terminal effect. -/
example : translated.run 0 = (((2, 6, 10, ()), 0, (1, 2, 10, 5, 6)), 7) := rfl

/-- The general law also applies to this stateful interpretation before running its state. -/
example (p : ProverStrategy (OracleComp calls) rounds Nat)
    (v : VerifierStrategy (OracleComp calls) rounds Nat) :
    runAgainst rounds
      (ProverStrategy.hoist (OracleComp.interpret counter) rounds p)
      (VerifierStrategy.hoist (OracleComp.interpret counter) rounds v) =
        OracleComp.interpret counter (runAgainst rounds p v) :=
  runAgainst_hoist _ (PFunctor.FreeM.isMonadHom_liftM _) _ _ _

abbrev coinRounds : Spec :=
  [.prover Nat (OracleInterface.full Nat), .verifier Bool,
    .prover Nat (OracleInterface.full Nat)]

abbrev CoinView := Nat × Nat × Nat × Bool × Nat

def roleSender : ProbOracleComp calls (ProverStrategy (ProbOracleComp calls) coinRounds Unit) := do
  let seed ← ProbOracleComp.query ()
  return (show ProbOracleComp calls (Nat × ProverStrategy (ProbOracleComp calls)
    [.verifier Bool, .prover Nat (OracleInterface.full Nat)] Unit) from
    pure (seed, fun challenge => do
      let fresh ← ProbOracleComp.query ()
      return (show ProbOracleComp calls (Nat × Unit) from
        pure (if challenge then fresh + 1 else fresh, ()))))

noncomputable def roleReceiver :
    ProbOracleComp calls (VerifierStrategy (ProbOracleComp calls) coinRounds CoinView) := do
  let seed ← ProbOracleComp.query ()
  return fun _ => do
    let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
    let fresh ← ProbOracleComp.query ()
    return (show ProbOracleComp calls (Bool × VerifierStrategy (ProbOracleComp calls)
      [.prover Nat (OracleInterface.full Nat)] CoinView) from
      pure (coin, fun last => do
        let again ← ProbOracleComp.query ()
        return (show ProbOracleComp calls CoinView from pure (seed, fresh, again, coin, last))))

/-- Receiver replies have an offset, so confusing the two oracle embeddings changes the view. -/
noncomputable def roleWorld : World calls calls where
  State := Nat
  init := 0
  impl
    | .inl () => fun state => PMF.pure (state, state + 1)
    | .inr () => fun state => PMF.pure (100 + state, state + 1)

noncomputable def roleProgram :
    ProbOracleComp (calls ⊕ₒ calls) (Transcript coinRounds × Unit × CoinView) := do
  let v ← liftVerifier roleReceiver
  let p ← liftProver roleSender
  runAgainst coinRounds (ProverStrategy.hoist liftProver coinRounds p)
    (VerifierStrategy.hoist liftVerifier coinRounds v)

/-- The receiver retains the same private coin after a later oracle read and the sender's reply. -/
example : roleWorld.eval roleProgram = (PMF.uniformOfFintype Bool).map (fun coin =>
    ((1, coin, (if coin then 4 else 3), ()), (),
      (100, 102, 104, coin, (if coin then 4 else 3)))) := by
  change (ProbOracleComp.runWith (State := Nat) roleWorld.impl roleProgram 0).map Prod.fst = _
  have hcoin : OracleComp.interpret ProbComp.unifOracle (ProbComp.uniform Bool) =
      PMF.uniformOfFintype Bool := ProbComp.eval_uniform Bool
  have hpure {α : Type} (f : Nat → α × Nat) (i : Nat) :
      (StateT.run (fun j => PMF.pure (f j)) i) = PMF.pure (f i) := rfl
  simp [roleProgram, roleSender, roleReceiver, liftProver, liftVerifier,
    ProverStrategy.hoist, VerifierStrategy.hoist, runAgainst, roleWorld,
    ProbOracleComp.runWith, ProbOracleComp.query, ProbOracleComp.sample,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_query,
    OracleComp.interpret_interpret, OracleComp.sumHandler, OracleComp.runWith,
    StateT.run_bind, hpure,
    OracleComp.run_interpret_lift, hcoin, PMF.map, Function.comp_def]

end CslibFrontierTests.InteractiveStrategyEffect
