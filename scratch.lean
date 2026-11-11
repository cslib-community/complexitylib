import CslibFrontier.Crypto.Protocols.MPC.Composition
open Probability Cslib.Crypto.Protocols.MPC

def Steps.hybrid {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) _ (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) _ (spec₁.Answer op) J)
    (I : Finset (Fin m)) :
    (k : ℕ) → ∀ {sc₁ : Schedule m spec₁}, Steps State Out sc₁ →
    ProbComp (((i : Fin m) → State i) × ((i : Fin m) → Out i))
| _, _, .done out => fun st => pure (st, out st)
| k, _, .message s r Msg send next => fun st =>
  Steps.hybrid Sub S₂ I k next (fun i =>
    if h : i = r then h ▸ (st i, send (st s)) else (st i, ()))
| k, _, .oracle query next => fun st => ...
