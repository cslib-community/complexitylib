/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.UC.Composition

/-!
# Tests for subroutine replacement and the UC composition theorem

The one-party hybrid protocol `relay` answers every input by asking its subroutine. Composed with
the functionality `bitFunc b`, which answers every input with `b`, the environment `askParty` sees
`b` whatever the adversary (`eval_exec_compose_relay`): the composed protocol really runs the
subroutine. Consequently, `relay` composed with `bitFunc true` does not emulate `relay` composed
with `bitFunc false` (`not_emulatesDummyWithin_compose_relay`), so the conclusion of the composition
theorem is not trivially true. The composition theorem itself is instantiated on self-emulation,
with the explicit simulator budget and error it produces, and the budgets of the composed protocol
and of the absorbed environment are checked on `relay`.
-/

namespace CslibFrontierTests.Crypto.UCComposition

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal

/-- The one-party functionality answering every input with the bit `b`. -/
def bitFunc (b : Bool) : IdealFunctionality 1 Unit Bool Unit Unit where
  State := Unit
  init _ _ := pure ()
  onInput _ _ := pure (some b)
  onBackdoor _ := pure ()

/-- The one-party hybrid protocol that answers each input by passing it to its subroutine. -/
def relay : HybridProtocol 1 Unit Bool Unit Unit Unit Bool := fun _ _ => {
  State := Unit
  init := pure ()
  handle
    | .inl p => StateT.lift (ProbOracleComp.query (spec := partySpec 1 Unit Bool) p)
    | .inr _ => pure () }

theorem relay_polyBounded : relay.PolyBounded 1 := fun κ C => by
  rw [Polynomial.eval_one]
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q s => ?_⟩
  rcases q with p | q
  · change ((fun a => (a, s)) <$> ProbOracleComp.query (spec := partySpec 1 Unit Bool) p
      ).IsQueryBounded 1
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  · exact OracleComp.IsCostBounded.pure _ _

/-- Ideal functionalities make no calls. -/
theorem bitFunc_polyBounded (b : Bool) : (bitFunc b).toProtocol.PolyBounded 0 := fun κ C =>
  ⟨OracleComp.IsCostBounded.pure _ _, fun q s => by
    rcases q with p | q <;> exact OracleComp.IsCostBounded.pure _ _⟩

/-- Activate party `0` once and output whether it answered `true`. -/
def askParty {AdvQ AdvR : Type} : Environment 1 Unit Bool AdvQ AdvR := fun _ _ => do
  let r ← ProbOracleComp.query (spec := execSpec 1 Unit Bool AdvQ AdvR) (Sum.inl (0, ()))
  return decide (r = some true)

theorem askParty_polyBounded {AdvQ AdvR : Type} :
    (askParty : Environment 1 Unit Bool AdvQ AdvR).PolyBounded 1 := fun κ z => by
  rw [Polynomial.eval_one]
  simp only [askParty, bind_pure_comp, ProbOracleComp.query]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- With no corruptions, the environment sees the subroutine's bit through `relay`, whatever the
adversary. -/
theorem eval_exec_compose_relay (b : Bool) {AdvQ AdvR : Type}
    (S : ExecAdversary 1 Unit Bool (Unit ⊕ RoutedNetQ 1 Unit Unit) (Unit ⊕ RoutedNetR Bool Unit)
      AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    (exec (compose relay (bitFunc b).toProtocol) S ∅ askParty κ z).eval = PMF.pure b := by
  simp only [exec, Machine.run, Machine.link, askParty, execMachine, Machine.comp,
    Machine.closeProgram_bind, Machine.closeProgram_map, Machine.closeProgram_sample,
    Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure]
  simp only [liftAdversary, StateT.run, compose, Machine.comp, corruptRouter, hybridWrap, relay,
    bitFunc, IdealFunctionality.toProtocol, StateT.run_pure, ProbOracleComp.sample_pure,
    Finset.notMem_empty, ↓reduceIte, bind_pure_comp, map_pure, Fin.isValue, StateT.lift,
    Machine.runFrom_map, Machine.runFrom_query, Prod.map_apply, id_eq, Machine.closeProgram_pure,
    ProbComp.eval_map, liftParty, OracleComp.interpret_map, ProbOracleComp.interpret_query]
  calc _ = PMF.map (Function.const _ b) _ := by congr 1 with a : 1; cases b <;> rfl
    _ = PMF.pure b := PMF.map_const _ _

/-- The environment `askParty` tells `relay` with `bitFunc true` from `relay` with `bitFunc false`
against every simulator. -/
theorem advantage_compose_relay
    (S : Adversary 1 (RoutedNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
      (RoutedNetR Bool (Unit ⊕ RoutedNetR Bool Unit))
      (RoutedNetQ 1 Unit (Unit ⊕ RoutedNetQ 1 Unit Unit))
      (RoutedNetR Bool (Unit ⊕ RoutedNetR Bool Unit))) (κ : ℕ) (z : List Bool) :
    advantage (compose relay (bitFunc true).toProtocol) (compose relay (bitFunc false).toProtocol)
      (dummyAdversary 1 _ _) S ∅ askParty κ z = 1 := by
  rw [advantage, eval_exec_compose_relay, eval_exec_compose_relay, Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- The conclusion of the composition theorem is not vacuous: `relay` composed with `bitFunc true`
does not emulate `relay` composed with `bitFunc false`, for any simulator budget and any error
below `1`. -/
theorem not_emulatesDummyWithin_compose_relay (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0)
    (hε : ε 1 0 < 1) :
    ¬ EmulatesDummyWithin (compose relay (bitFunc true).toProtocol)
      (compose relay (bitFunc false).toProtocol) pD ε := by
  rintro ⟨S, -, hadv⟩
  have := hadv ∅ askParty 1 askParty_polyBounded 0 []
  rw [advantage_compose_relay] at this
  exact absurd hε (not_lt.mpr this)

/-- The dummy adversary simulates itself with zero error. -/
theorem emulatesDummyWithin_refl (b : Bool) :
    EmulatesDummyWithin (bitFunc b).toProtocol (bitFunc b).toProtocol 1 (fun _ _ => 0) :=
  ⟨dummyAdversary 1 _ _, dummyAdversary_polyBounded 1 _ _, fun _ _ _ _ _ _ => by simp⟩

/-- The composition theorem for dummy-adversary simulators, on `relay`: the composed simulator has
budget `1 + 1`, and the error is evaluated at the absorbed environment budget. -/
example (b : Bool) :
    EmulatesDummyWithin (compose relay (bitFunc b).toProtocol)
      (compose relay (bitFunc b).toProtocol) (1 + 1) (fun _ _ => 0) :=
  (emulatesDummyWithin_refl b).compose relay_polyBounded

/-- The concrete composition theorem on `relay`, with its explicit simulator overhead. -/
example (b : Bool) :
    EmulatesWithin (compose relay (bitFunc b).toProtocol) (compose relay (bitFunc b).toProtocol)
      (Polynomial.X * ((Polynomial.X * (1 + 1) + 1).comp (Polynomial.X + 1) + 1 + 1) +
        ((Polynomial.X * (1 + 1) + 1).comp (Polynomial.X + 1) + 1)) (fun _ _ _ => 0) :=
  ((emulatesDummyWithin_refl b).emulatesWithin).compose relay_polyBounded

/-- The asymptotic composition theorem on `relay`. -/
example (b : Bool) :
    Emulates (compose relay (bitFunc b).toProtocol) (compose relay (bitFunc b).toProtocol) :=
  (Emulates.refl _).compose relay_polyBounded

/-- The composed protocol has a polynomial budget, and absorbing `relay` into `askParty` gives an
environment of the subroutine with budget `absorbPoly 1 1`, that is, `1 + 1 + 1 * (1 + 2) = 5`
calls. -/
example (C : Finset (Fin 1)) (b : Bool) :
    (compose relay (bitFunc b).toProtocol).PolyBounded ((1 + 1) * (0 + 1) + 0) ∧
      (absorbHybrid (NQ := Unit) (NR := Unit) C relay askParty).PolyBounded (absorbPoly 1 1) ∧
      ∀ κ, (absorbPoly 1 1).eval κ = 5 :=
  ⟨compose_polyBounded relay_polyBounded (bitFunc_polyBounded b),
    absorbHybrid_polyBounded C relay_polyBounded askParty_polyBounded, fun κ => by simp⟩

end CslibFrontierTests.Crypto.UCComposition
