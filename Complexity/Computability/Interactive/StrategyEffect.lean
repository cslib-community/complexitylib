/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Interactive.AuxZK
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Changing the effects of interactive strategies

Translate every effect of a strategy while retaining its message-dependent continuations.
Initial computations that produce strategies remain outside this operation and must be translated
separately, in their original order. Stateful interpretations should target `StateT`; run the
combined interaction once, rather than resetting the state at each translated effect.

## Main definitions

* `ProverStrategy.hoist`, `VerifierStrategy.hoist`: translate the effects of existing strategies.
* `liftVerifier`: embed receiver-side oracle computations in the joint role oracle.

## Main results

* `runAgainst_hoist`: a monad morphism commutes with the complete interaction.
-/

@[expose] public section

namespace Cslib.Interactive

open Spec

variable {m n : Type → Type} {α β : Type}

/-- Translate effects in a prover strategy, retaining each captured continuation. -/
def ProverStrategy.hoist [Functor n] (φ : ∀ {γ}, m γ → n γ) :
    (s : Spec) → ProverStrategy m s α → ProverStrategy n s α
  | [], a => a
  | .prover M _ :: s, p =>
    ((fun a => (a.1, ProverStrategy.hoist φ s a.2)) <$>
      φ (p : m (M × ProverStrategy m s α)) : n (M × ProverStrategy n s α))
  | .verifier C :: s, p => fun c : C =>
    ProverStrategy.hoist φ s <$> φ ((p : C → m (ProverStrategy m s α)) c)

/-- Translate effects in a verifier strategy, including its terminal view computation. -/
def VerifierStrategy.hoist [Functor n] (φ : ∀ {γ}, m γ → n γ) :
    (s : Spec) → VerifierStrategy m s α → VerifierStrategy n s α
  | [], v => φ (v : m α)
  | .prover M _ :: s, v => fun msg : M =>
    VerifierStrategy.hoist φ s <$> φ ((v : M → m (VerifierStrategy m s α)) msg)
  | .verifier C :: s, v =>
    ((fun a => (a.1, VerifierStrategy.hoist φ s a.2)) <$>
      φ (v : m (C × VerifierStrategy m s α)) : n (C × VerifierStrategy n s α))

/-- Translating both strategies by a monad morphism translates their entire interaction,
including the transcript and both terminal outputs. -/
theorem runAgainst_hoist [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : ∀ {γ}, m γ → n γ) (hφ : IsMonadHom m n φ) :
    ∀ (s : Spec) (p : ProverStrategy m s α) (v : VerifierStrategy m s β),
      runAgainst s (ProverStrategy.hoist φ s p) (VerifierStrategy.hoist φ s v) =
        φ (runAgainst s p v)
  | [], p, v => by
    simp [runAgainst, ProverStrategy.hoist, VerifierStrategy.hoist, hφ.map_map]
  | .prover M _ :: s, p, v => by
    simp [runAgainst, ProverStrategy.hoist, VerifierStrategy.hoist, hφ.map_bind,
      hφ.map_pure, ← bind_pure_comp, bind_assoc, runAgainst_hoist φ hφ s]
  | .verifier C :: s, p, v => by
    simp [runAgainst, ProverStrategy.hoist, VerifierStrategy.hoist, hφ.map_bind,
      hφ.map_pure, ← bind_pure_comp, bind_assoc, runAgainst_hoist φ hφ s]

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV}

/-- Lift a verifier computation into the joint oracles without granting it prover queries. -/
def liftVerifier {α : Type} : ProbOracleComp oV α → ProbOracleComp (oP ⊕ₒ oV) α :=
  OracleComp.interpret (OracleComp.sumHandler
    (fun n => OracleComp.query (spec := probOracleSpec (oP ⊕ₒ oV)) (.inl n))
    (fun q => ProbOracleComp.query (spec := oP ⊕ₒ oV) (.inr q)))

/-- The existing prover-role embedding preserves monadic effects. -/
theorem isMonadHom_liftProver :
    IsMonadHom (ProbOracleComp oP) (ProbOracleComp (oP ⊕ₒ oV)) liftProver :=
  PFunctor.FreeM.isMonadHom_liftM _

/-- The verifier-role embedding preserves monadic effects. -/
theorem isMonadHom_liftVerifier :
    IsMonadHom (ProbOracleComp oV) (ProbOracleComp (oP ⊕ₒ oV)) liftVerifier :=
  PFunctor.FreeM.isMonadHom_liftM _

end Cslib.Interactive
