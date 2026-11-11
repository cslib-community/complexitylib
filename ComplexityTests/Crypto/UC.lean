/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Protocols.UC.Emulation
import Complexity.Crypto.Negligible.Basic

/-!
# Tests for the UC execution and UC emulation

The ideal functionality `bitFunc b` answers every party input with the bit `b` and ignores its
backdoor. The environment `askParty` activates party `0` once and outputs whether the reply was
`true`. With no corrupted parties, the execution against `bitFunc b` outputs `b` with certainty
whatever the adversary, because the adversary cannot reach an honest party
(`eval_exec_askParty`); when party `0` is corrupted, the environment cannot reach it and outputs
`false` (`eval_exec_askParty_corrupt`). With no corruptions, `askParty` therefore distinguishes
`bitFunc true` from `bitFunc false` with advantage `1` against every simulator, and `bitFunc true`
does not emulate `bitFunc false` with any error below `1` (`not_emulatesWithin_bitFunc`). The
forwarding adversary and `askParty` meet the budgets `1`, so the budget hypotheses of
`UC.EmulatesWithin` and `UC.Emulates` are satisfiable.
-/

namespace ComplexityTests.Crypto.UC

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal

/-- The one-party functionality answering every input with the bit `b`. -/
def bitFunc (b : Bool) : IdealFunctionality 1 Unit Bool Unit Unit where
  State := Unit
  init _ _ := pure ()
  onInput _ _ := pure (some b)
  onBackdoor _ := pure ()

/-- Activate party `0` once and output whether it answered `true`. -/
def askParty {AdvQ AdvR : Type} : Environment 1 Unit Bool AdvQ AdvR := fun _ _ => do
  let r ← ProbOracleComp.query (spec := execSpec 1 Unit Bool AdvQ AdvR) (Sum.inl (0, ()))
  return decide (r = some true)

/-- The forwarding (dummy) adversary. -/
def forward (NetQ NetR : Type) : Adversary 1 NetQ NetR NetQ NetR :=
  fun _ _ => Machine.id (netSpec NetQ NetR)

theorem forward_polyBounded (NetQ NetR : Type) : (forward NetQ NetR).PolyBounded 1 :=
  fun _ _ => (Machine.isBounded_id (netSpec NetQ NetR)).mono (by simp)

theorem askParty_polyBounded {AdvQ AdvR : Type} :
    (askParty : Environment 1 Unit Bool AdvQ AdvR).PolyBounded 1 := fun κ z => by
  rw [Polynomial.eval_one]
  simp only [askParty, bind_pure_comp, ProbOracleComp.query]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- With no corruptions, the environment sees the functionality's bit, whatever the adversary. -/
theorem eval_exec_askParty (b : Bool) {AdvQ AdvR : Type}
    (S : Adversary 1 AdvQ AdvR ((Fin 1 × Unit) ⊕ Unit) (Option Bool ⊕ Unit)) (κ : ℕ)
    (z : List Bool) : (exec (bitFunc b).toProtocol S ∅ askParty κ z).eval = PMF.pure b := by
  simp only [exec, Machine.run, Machine.link, askParty, execMachine, Machine.comp,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure]
  simp only [liftAdversary, StateT.run, bitFunc, IdealFunctionality.toProtocol, StateT.run_pure,
    ProbOracleComp.sample_pure, corruptRouter, Finset.notMem_empty, ↓dreduceIte, bind_pure_comp,
    map_pure, Fin.isValue, StateT.lift, Machine.runFrom_map, Machine.runFrom_query, Prod.map_apply,
    id_eq, Machine.closeProgram_pure, ProbComp.eval_map]
  calc _ = PMF.map (Function.const _ b) _ := by congr 1; funext a; cases b <;> rfl
    _ = PMF.pure b := PMF.map_const _ _

/-- When party `0` is corrupted, the environment cannot reach it: the router answers `none`, so
`askParty` outputs `false`, whatever the functionality and the adversary. -/
theorem eval_exec_askParty_corrupt (b : Bool) {AdvQ AdvR : Type}
    (S : Adversary 1 AdvQ AdvR ((Fin 1 × Unit) ⊕ Unit) (Option Bool ⊕ Unit)) (κ : ℕ)
    (z : List Bool) : (exec (bitFunc b).toProtocol S {0} askParty κ z).eval = PMF.pure false := by
  simp only [exec, Machine.run, Machine.link, askParty, execMachine, Machine.comp,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure]
  simp only [Fin.isValue, liftAdversary, StateT.run, bitFunc, IdealFunctionality.toProtocol,
    StateT.run_pure, ProbOracleComp.sample_pure, corruptRouter, Finset.mem_singleton,
    bind_pure_comp, StateT.lift, Machine.runFrom_map, Machine.runFrom_query, ↓reduceIte,
    Functor.map_map, Machine.closeProgram_map, Machine.closeProgram_pure,
    ProbComp.eval_bind, ProbComp.eval_map]
  calc _ = PMF.bind _ (fun _ => PMF.pure false) := by congr 1; funext a; exact PMF.pure_map _ _
    _ = PMF.pure false := PMF.bind_const _ _

/-- Every simulator loses: `askParty` tells `bitFunc true` from `bitFunc false` with certainty. -/
theorem advantage_bitFunc {AdvQ AdvR : Type}
    (A S : Adversary 1 AdvQ AdvR ((Fin 1 × Unit) ⊕ Unit) (Option Bool ⊕ Unit)) (κ : ℕ)
    (z : List Bool) :
    advantage (bitFunc true).toProtocol (bitFunc false).toProtocol A S ∅ askParty κ z = 1 := by
  rw [advantage, eval_exec_askParty, eval_exec_askParty, Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- `bitFunc true` does not emulate `bitFunc false` with any error below `1`. -/
theorem not_emulatesWithin_bitFunc (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0)
    (hε : ε 1 1 0 < 1) :
    ¬ EmulatesWithin (bitFunc true).toProtocol (bitFunc false).toProtocol g ε := by
  intro h
  obtain ⟨S, _, _, _, hadv⟩ := h _ _ (forward _ _) 1 (forward_polyBounded _ _)
  have := hadv ∅ askParty 1 askParty_polyBounded 0 []
  rw [advantage_bitFunc] at this
  exact absurd hε (not_lt.mpr this)

/-- Emulation is satisfiable: every functionality realizes itself, with zero error. -/
example (b : Bool) : RealizesWithin (bitFunc b).toProtocol (bitFunc b) Polynomial.X
    (fun _ _ _ => 0) :=
  EmulatesWithin.refl _

/-- Transitivity composes concrete emulations; the zero error is monotone in the adversary's
budget, and the composed error is zero again. -/
theorem emulatesWithin_trans_self (b : Bool) :
    EmulatesWithin (bitFunc b).toProtocol (bitFunc b).toProtocol
      (Polynomial.X.comp (Polynomial.X + Polynomial.X)) (fun _ _ _ => 0 + 0) :=
  (EmulatesWithin.refl _).trans (EmulatesWithin.refl _) fun _ _ _ _ _ => le_rfl

/-- Zero errors are negligible, so concrete emulation gives asymptotic emulation, which composes. -/
example (b : Bool) : Realizes (bitFunc b).toProtocol (bitFunc b) :=
  ((emulatesWithin_trans_self b).emulates fun _ _ => by simp).trans
    (Emulates.refl _)

/-- The adversary reaches a corrupted party through the network port, and is refused for an honest
party. -/
example (b : Bool) (C : Finset (Fin 1)) (s : Unit) :
    ((corruptRouter C ((bitFunc b).toProtocol 0 C)).handle (.inr (.inl (0, ())))).run s =
      if (0 : Fin 1) ∈ C then pure (.inl (some b), s) else pure (.inl none, s) := by
  by_cases h : (0 : Fin 1) ∈ C
  · simp only [corruptRouter, IdealFunctionality.toProtocol, bitFunc, h, ↓reduceIte,
      StateT.run_map, StateT.run_pure, ProbOracleComp.sample_pure]
    simp [StateT.run]
  · simp only [corruptRouter, h, ↓reduceIte]
    rfl

/-- Asymptotic emulation also fails for distinguishable functionalities. -/
example : ¬ Emulates (bitFunc true).toProtocol (bitFunc false).toProtocol := by
  intro h
  obtain ⟨S, _, _, hν⟩ := h _ _ (forward _ _) 1 (forward_polyBounded _ _)
  obtain ⟨ν, hν, hadv⟩ := hν 1
  refine not_negligible_const one_ne_zero (negligible_of_eventually_le hν
    (Filter.Eventually.of_forall fun κ => ?_))
  simpa [advantage_bitFunc] using hadv ∅ askParty askParty_polyBounded κ []

end ComplexityTests.Crypto.UC
