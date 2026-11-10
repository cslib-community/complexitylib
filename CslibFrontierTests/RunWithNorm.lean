/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Oracle
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-!
# Tests for `runWith_norm`

Verifies that `simp only [runWith_norm, pmf_norm]` confluently normalizes:
1. black-box `WordOracleComp` adversaries inside closed
   `ProbComp.eval ((OracleComp.interpret …).run s)` experiments (including nested stateful reduction
   handlers) to `ProbOracleComp.runWith`, without getting stuck inside `StateT.run`;
2. concrete multi-step `do` programs mixing `ProbOracleComp.sample`, `ProbOracleComp.query`, `pure`,
   and `<$>` into `PMF.bind` / `PMF.pure` in one pass;
3. stateless and stateful handler substitutions (`runWith_interpret_sumHandler_eta`,
   `runWith_run_interpret`, and `runWith_lift`); and
4. stateless `OracleComp.evalWith` on concrete `do` programs.
-/

namespace CslibFrontierTests.RunWithNorm

open Cslib Cslib.Probability

/-! ### 1. Black-box adversary inside a closed game and nested reduction handler -/

section BlackBoxAdversary

-- Direct closed run of a black-box `WordOracleComp Op Bool` adversary folds to `runWith`.
example {Op State : Type} (oracle : Op × List Bool → StateT State ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (s₀ : State) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) oracle)
      (adversary n)).run s₀) =
    ProbOracleComp.runWith (fun q s => ProbComp.eval (oracle q s)) (adversary n) s₀ := by
  simp only [runWith_norm, pmf_norm]

-- Closed security-game experiment wrapping a stateful reduction around a black-box adversary:
-- `runWith_norm` folds the outer run to `runWith`, steps the reduction's `sample` and `return`,
-- and collapses the inner `run` via `runWith_run_interpret` without `OracleComp.interpret_bind`
-- breaking the outer `.run`.
private def reduction {Op HState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (h₀ : HState) (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) :
    WordOracleComp Op Bool := do
  let aux ← ProbOracleComp.sample (keyGen n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (inner aux))
    (adversary n)).run h₀
  return !out.1

example {Op HState EState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (extOracle : Op × List Bool → StateT EState ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (h₀ : HState) (e₀ : EState) :
    ProbComp.eval (do
      let seed ← keyGen n
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) extOracle)
        (reduction keyGen inner h₀ adversary n)).run e₀
      return (seed.isEmpty && out.1)) =
    (ProbComp.eval (keyGen n)).bind fun seed =>
      (ProbComp.eval (keyGen n)).bind fun aux =>
        (ProbOracleComp.runWith
          (fun q st =>
            (ProbOracleComp.runWith (fun q' s' => ProbComp.eval (extOracle q' s'))
              ((inner aux q).run st.1) st.2).map fun r => (r.1.1, r.1.2, r.2))
          (adversary n) (h₀, e₀)).bind fun r =>
          PMF.pure (seed.isEmpty && !r.1) := by
  simp only [reduction, runWith_norm, pmf_norm]

-- Spelled-out `ProbComp.unifOracle` sum-handler run folds directly to `ProbOracleComp.runWith`.
example {Op State : Type} (oracle : Op × List Bool → StateT State PMF (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (s₀ : State) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) oracle)
      (adversary n)).run s₀ =
    ProbOracleComp.runWith oracle (adversary n) s₀ := by
  simp only [runWith_norm]

end BlackBoxAdversary

/-! ### 2. Concrete multi-step `do` program with `sample`, `query`, `pure`, and `<$>` -/

section ConcreteDoProgram

private def concreteProg : ProbOracleComp (fun _ : Bool => Nat) (Bool × Nat) := do
  let coin ← ProbOracleComp.sample (do
    let i ← ProbComp.unifFin 1
    return (i.val == 1))
  let first ← ProbOracleComp.query coin
  let bumped ← (· + 1) <$> ((· * 2) <$> ProbOracleComp.query (!coin))
  return (coin, first + bumped)

example (oracle : Bool → StateT Nat PMF Nat) (s₀ : Nat) :
    ProbOracleComp.runWith oracle concreteProg s₀ =
      (ProbComp.eval (ProbComp.unifFin 1)).bind fun i =>
        (oracle (i.val == 1) s₀).bind fun x =>
          (oracle (!(i.val == 1)) x.2).bind fun y =>
            PMF.pure ((i.val == 1, x.1 + (y.1 * 2 + 1)), y.2) := by
  simp only [concreteProg, runWith_norm, pmf_norm]

end ConcreteDoProgram

/-! ### 3. Handler substitution and memoryless `StateT.lift` oracles -/

section HandlerSubstitution

-- Stateless handler substitution (`runWith_interpret_sumHandler`) on a black-box program.
example {State : Type} (oracle : Bool → StateT State PMF Nat)
    (program : ProbOracleComp (fun _ : Bool => Nat) Bool) (s₀ : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun q => (· + 1) <$> ProbOracleComp.query (!q)))
        program) s₀ =
    ProbOracleComp.runWith
      (fun q s => (oracle (!q) s).map (Prod.map (· + 1) id))
      program s₀ := by
  simp only [runWith_norm, pmf_norm]

-- Stateless handler substitution on a concrete `do` program normalizes all the way to `PMF.bind`.
example {State : Type} (oracle : Bool → StateT State PMF Nat) (q₀ : Bool) (s₀ : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun q => (· + 1) <$> ProbOracleComp.query (!q)))
        (do
          let x ← ProbOracleComp.query q₀
          return x * 3)) s₀ =
    (oracle (!q₀) s₀).bind fun r => PMF.pure ((r.1 + 1) * 3, r.2) := by
  simp only [runWith_norm, pmf_norm]

-- Memoryless lifted oracle (`runWith_lift`) on a concrete `ProbOracleComp` `do` program.
example (h : Bool → PMF Nat) (s₀ : Nat) :
    ProbOracleComp.runWith (fun q => StateT.lift (h q))
      (do
        let k ← ProbOracleComp.sample (ProbComp.unifFin 2)
        let v ← ProbOracleComp.query (k.val == 0)
        return v + k.val) s₀ =
    (ProbComp.eval (ProbComp.unifFin 2)).bind fun k =>
      (h (k.val == 0)).bind fun v =>
        PMF.pure (v + k.val, s₀) := by
  simp only [runWith_norm, pmf_norm]

end HandlerSubstitution

/-! ### 4. Stateless `OracleComp.evalWith` on a concrete `do` program -/

section EvalWith

private def statelessProg : OracleComp (fun _ : Bool => Nat) Nat := do
  let x ← OracleComp.query false
  let y ← (· + 10) <$> OracleComp.query (decide (x < 5))
  return x + y

example (h : Bool → PMF Nat) :
    OracleComp.evalWith h statelessProg =
      (h false).bind fun x =>
        (h (decide (x < 5))).bind fun y =>
          PMF.pure (x + (y + 10)) := by
  simp only [statelessProg, runWith_norm, pmf_norm]

end EvalWith

end CslibFrontierTests.RunWithNorm
