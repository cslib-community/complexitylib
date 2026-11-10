/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Commitment.World

/-! Actual phased-world clients: ordering, immutability, terminal states, and sampling. -/

@[expose] public section

namespace Cslib.Tests.CommitmentWorld

open Crypto.Protocols.Commitment.Phased

abbrev Program := ProbOracleComp (senderSpec ⊕ₒ receiverSpec)

def send (cmd : Command) : Program Unit :=
  ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (Sum.inl cmd)

def poll : Program Observation :=
  ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec) (Sum.inr ())

def honest (b : Bool) : Program (Observation × Observation) := do
  send (.commit b)
  let received ← poll
  send .open
  return (received, ← poll)

example (b : Bool) : world.eval (honest b) = PMF.pure (.receipt, .opened b) := by
  simp [honest, send, poll, Interactive.World.eval, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, handler, OracleComp.sumHandler,
    advance, observe]

-- Opening too early does not consume the session. A later commitment can still open.
example : world.eval (do
    send .open
    let early ← poll
    send (.commit true)
    send .open
    return (early, ← poll)) = PMF.pure (.idle, .opened true) := by
  simp [send, poll, Interactive.World.eval, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, handler, OracleComp.sumHandler,
    advance, observe]

-- A second commitment cannot replace the first bit; abort cannot retract the released value.
example : world.eval (do
    send (.commit false)
    send (.commit true)
    let received ← poll
    send .open
    send .abort
    send (.commit true)
    return (received, ← poll)) = PMF.pure (.receipt, .opened false) := by
  simp [send, poll, Interactive.World.eval, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, handler, OracleComp.sumHandler,
    advance, observe]

-- Abort before commitment and abort after commitment both prevent a subsequent opening.
example (b : Bool) : world.eval (do
    send (.commit b)
    send .abort
    send (.commit (!b))
    send .open
    poll) = PMF.pure .aborted := by
  simp [send, poll, Interactive.World.eval, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, handler, OracleComp.sumHandler,
    advance, observe]

example : world.eval (do
    send .abort
    send (.commit true)
    send .open
    poll) = PMF.pure .aborted := by
  simp [send, poll, Interactive.World.eval, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, handler, OracleComp.sumHandler,
    advance, observe]

-- Retain the receiver's private random bit and choose the number of polls using it.
noncomputable def privatePolls :
    ProbOracleComp receiverSpec (Fin 2 × List Observation) := do
  let coin ← ProbOracleComp.sample (ProbComp.uniform (Fin 2))
  let first ← ProbOracleComp.query ()
  if coin = 0 then return (coin, [first])
  else return (coin, [first, ← ProbOracleComp.query ()])

example :
    (ProbOracleComp.runWith (fun q => world.impl (.inr q)) privatePolls (.committed true)).map
        Prod.fst =
      (ProbOracleComp.runWith (fun q => world.impl (.inr q)) privatePolls (.committed false)).map
        Prod.fst := polling_secrecy privatePolls true false

-- Opening deliberately changes observations, so the pre-opening restriction is essential.
example : observe (.opened true) ≠ observe (.opened false) := by decide

end Cslib.Tests.CommitmentWorld
