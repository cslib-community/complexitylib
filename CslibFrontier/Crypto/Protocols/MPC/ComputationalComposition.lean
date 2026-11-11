/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition
public import CslibFrontier.Crypto.Protocols.MPC.Advantage

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability

-- Theorem 7.5.7 for computational privacy
theorem semiHonestAdvantage_compose_le {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₁ : Schedule m spec₁} {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {In Coins₁ Out : Fin m → Type}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    {P : Protocol m spec₁ sc₁ In Coins₁ Out}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {f : Functionality m In Out}
    {S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁) (Schedule.compose sc₂ sc₁) i.1) ×
      ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P S₁ S₂) x D ≤
      semiHonestAdvantage P W₁ f I (S₁ I) x (fun v => pure true) := by
  sorry

end Cslib.Crypto.Protocols.MPC
