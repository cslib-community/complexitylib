/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.DummyAdversary
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Tests for the dummy adversary

The one-party functionality `bitFunc b` answers every input with `b`; the environment `askParty`
asks party `0` once. Against the dummy adversary, every simulator loses with certainty when
`bitFunc true` is compared with `bitFunc false` (`advantage_dummy_bitFunc`), so the dummy-adversary
notion is not vacuous (`not_emulatesDummyWithin_bitFunc`). The dummy adversary simulates itself
with zero error (`emulatesDummyWithin_refl`), and completeness of the dummy adversary turns this
into concrete emulation whose simulator for an adversary `A` is `compSim (dummyAdversary 1 _ _) A`
(`emulatesWithin_of_dummy`). Absorbing an adversary into an environment is checked on an explicit
adversary that relays one environment query as two network queries (`relay`).
-/

namespace CslibFrontierTests.Crypto.UCDummyAdversary

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

/-- Every simulator of the dummy adversary loses with certainty. -/
theorem advantage_dummy_bitFunc
    (S : Adversary 1 ((Fin 1 × Unit) ⊕ Unit) (Option Bool ⊕ Unit) ((Fin 1 × Unit) ⊕ Unit)
      (Option Bool ⊕ Unit)) (κ : ℕ) (z : List Bool) :
    advantage (bitFunc true).toProtocol (bitFunc false).toProtocol (dummyAdversary 1 _ _) S ∅
      askParty κ z = 1 := by
  rw [advantage, eval_exec_askParty, eval_exec_askParty, Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- The dummy-adversary notion is not vacuous. -/
theorem not_emulatesDummyWithin_bitFunc (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0)
    (hε : ε 1 0 < 1) :
    ¬ EmulatesDummyWithin (bitFunc true).toProtocol (bitFunc false).toProtocol pD ε := by
  rintro ⟨S, -, hadv⟩
  have := hadv ∅ askParty 1 askParty_polyBounded 0 []
  rw [advantage_dummy_bitFunc] at this
  exact absurd hε (not_lt.mpr this)

/-- The dummy adversary simulates itself with zero error. -/
theorem emulatesDummyWithin_refl (b : Bool) :
    EmulatesDummyWithin (bitFunc b).toProtocol (bitFunc b).toProtocol 1 (fun _ _ => 0) :=
  ⟨dummyAdversary 1 _ _, dummyAdversary_polyBounded 1 _ _, fun _ _ _ _ _ _ => by simp⟩

/-- Completeness of the dummy adversary turns self-simulation into concrete emulation. -/
theorem emulatesWithin_of_dummy (b : Bool) :
    EmulatesWithin (bitFunc b).toProtocol (bitFunc b).toProtocol
      (Polynomial.X * (1 + 1) + 1) (fun _ _ _ => 0) :=
  (emulatesDummyWithin_refl b).emulatesWithin

/-- Completeness with negligible error: the dummy adversary simulating itself gives emulation. -/
example (b : Bool) : Realizes (bitFunc b).toProtocol (bitFunc b) :=
  (emulates_iff_emulatesDummy _ _).mpr
    ⟨dummyAdversary 1 _ _, 1, dummyAdversary_polyBounded 1 _ _,
      fun _ => ⟨fun _ => 0, negligible_zero, fun _ _ _ _ _ => by simp⟩⟩

/-- The absorbed budget is explicit: an environment with budget `1` absorbing an adversary with
budget `2` makes at most `7` calls. -/
example (κ : ℕ) : (absorbPoly 1 2).eval κ = 7 := by simp

/-- An error depending on the environment budget passes through completeness at the absorbed
budget, which is monotone in the adversary's budget, as concrete transitivity requires. -/
example {pZ p p' : Polynomial ℕ} (κ : ℕ) (h : ∀ κ', p.eval κ' ≤ p'.eval κ') :
    (absorbPoly pZ p).eval κ ≤ (absorbPoly pZ p').eval κ :=
  eval_absorbPoly_mono le_rfl (h κ)

/-- An adversary relaying each environment query to the network twice and returning the second
reply. -/
def relay : Adversary 1 ((Fin 1 × Unit) ⊕ Unit) (Option Bool ⊕ Unit) ((Fin 1 × Unit) ⊕ Unit)
    (Option Bool ⊕ Unit) := fun _ _ => {
  State := Unit
  init := pure ()
  handle q := StateT.lift do
    let _ ← ProbOracleComp.query (spec := netSpec _ (Option Bool ⊕ Unit)) q
    ProbOracleComp.query (spec := netSpec _ (Option Bool ⊕ Unit)) q }

/-- The relay's network port. -/
abbrev relayNet : (Fin 1 × Unit) ⊕ Unit → Type := netSpec _ (Option Bool ⊕ Unit)

theorem relay_polyBounded : relay.PolyBounded 2 := fun κ C => by
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q s => ?_⟩
  rw [Polynomial.eval_ofNat]
  change OracleComp.IsQueryBounded ((do
    let _ ← ProbOracleComp.query (spec := relayNet) q
    ProbOracleComp.query (spec := relayNet) q) >>= fun a => pure (a, s)) 2
  exact (((OracleComp.IsCostBounded.query _).bind fun _ => OracleComp.IsCostBounded.query _).bind
    fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)

/-- Absorbing `relay` into `askParty` gives a budgeted environment for the dummy adversary, and the
execution with `relay` is the execution of the dummy adversary with the absorbed environment. -/
example (C : Finset (Fin 1)) (κ : ℕ) (z : List Bool) :
    (absorbAdversary C relay askParty).PolyBounded (absorbPoly 1 2) ∧
      exec (bitFunc true).toProtocol relay C askParty κ z =
        exec (bitFunc true).toProtocol (dummyAdversary 1 _ _) C (absorbAdversary C relay askParty)
          κ z :=
  ⟨absorbAdversary_polyBounded C relay_polyBounded askParty_polyBounded,
    exec_eq_exec_dummy _ _ _ _ _ _⟩

end CslibFrontierTests.Crypto.UCDummyAdversary
