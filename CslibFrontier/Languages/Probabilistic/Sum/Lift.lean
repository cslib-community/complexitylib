/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Sum

/-!
# Sum handlers of lifted oracles

A program with private coins often runs in a state monad whose oracle never changes the state:
both handlers of `OracleComp.sumHandler` are `StateT.lift`s, or the coins are lifted and the right
handler answers from the current state and returns it unchanged. The lemmas here pull the state
out of the combined handler, so such a run reduces to a stateless interpretation in one rewrite.

## Main results

* `Cslib.OracleComp.sumHandler_lift`: the sum of lifted handlers is the lift of their sum.
* `Cslib.OracleComp.run_interpret_sumHandler_readOnly`: a run with lifted coins and a right handler
  that only reads the state is the interpretation against the handlers at the initial state.
-/

public section

namespace Cslib.OracleComp

universe u v w

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {spec₂ : OracleSpec.{u, v} ι₂}
  {α σ : Type v} {m : Type v → Type w} [Monad m]

/-- The sum of two lifted handlers is the lift of their sum. -/
theorem sumHandler_lift (left : (q : ι₁) → m (spec₁ q)) (right : (q : ι₂) → m (spec₂ q)) :
    sumHandler (fun q => StateT.lift (σ := σ) (left q)) (fun q => StateT.lift (right q)) =
      fun q => StateT.lift (sumHandler left right q) := by
  funext q
  cases q <;> rfl

/-- A run with lifted coins whose right handler reads the state without changing it is the
interpretation against the handlers at the initial state. -/
theorem run_interpret_sumHandler_readOnly [LawfulMonad m] (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → σ → m (spec₂ q)) (program : OracleComp (spec₁ ⊕ₒ spec₂) α) (s : σ) :
    (interpret (sumHandler (m := StateT σ m) (fun q => StateT.lift (left q))
      fun q s => (fun a => (a, s)) <$> right q s) program).run s =
      (fun a => (a, s)) <$> interpret (sumHandler left fun q => right q s) program := by
  rw [← run_interpret_readOnly (fun q s => sumHandler left (fun q => right q s) q) program s]
  congr 2
  funext q s
  cases q
  · simp [StateT.lift, bind_pure_comp]
  · rfl

end Cslib.OracleComp
