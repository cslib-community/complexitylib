/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.MPC.OTCommitment.PolyTime

/-!
# Delayed OT commitment opening tests

Both duplicated OT slots, honest transcript/opening correlation, adaptive receiver state with
private randomness, post-opening processing, empty executions, and native list encoding.
-/

namespace ComplexityTests.Crypto.OTCommitmentEquivocation

open Cslib.Probability Cslib.Crypto.Protocols.MPC OTCommitment
open Turing.MultiTapeTM Turing.MultiTapeTM.Encodings

example : equivocate true (fun _ : Fin 1 => (3, false)) 0 false = true := by decide
example : equivocate true (fun _ : Fin 1 => (3, false)) 0 true = false := by decide
example : equivocate true (fun _ : Fin 1 => (2, false)) 0 false = false := by decide
example : equivocate true (fun _ : Fin 1 => (2, false)) 0 true = true := by decide

example : Accepts (fun _ : Fin 1 => true) (fun _ => false) true
    (equivocate true (fun _ => (3, false))) := equivocate_accepts true _

/-- Reusing the simulator's original parity-zero pair fails when opening to one. -/
example : ¬ Accepts (fun _ : Fin 1 => true) (fun _ => false) true
    (opening false (fun _ => false)) := by
  intro h
  have := (h 0).1
  simp [opening] at this

noncomputable def fixedReceiver (j : Fin 4) : Receiver Unit where
  choose _ _ := pure (j, ())
  receive _ _ := pure ()

/-- The actual OT answer and honest pair remain correlated: choosing slot three returns the
second component, not a fresh independent bit at opening. -/
example : (receiverCommit (fixedReceiver 3) true 1 ()).map
    (fun (masks, transcript, _) =>
      ((transcript 0).2, opening true masks 0 false, opening true masks 0 true)) =
    (PMF.uniformOfFintype Bool).map (fun r => (r ^^ true, r, r ^^ true)) := by
  simp only [receiverCommit_zero, receiverCommit_succ, fixedReceiver, transfer_eq,
    Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.pure_bind, PMF.map_bind, PMF.pure_map, table]
  rfl

/-- Choose slot three after a true answer XOR private coin, otherwise slot zero. The state keeps
both the previous answer and fresh private randomness for the next choice. -/
noncomputable def adaptiveReceiver : Receiver (Bool × Bool) where
  choose _ st := pure (if st.1 ^^ st.2 then 3 else 0, st)
  receive _ answer := (PMF.uniformOfFintype Bool).map (answer, ·)

/-- Full joint simulation also preserves the adaptive receiver's private state. -/
example (b : Bool) (k : ℕ) :
    (receiverCommit adaptiveReceiver b k (false, false)).map
      (fun (masks, transcript, final) => (transcript, final, opening b masks)) =
    (receiverRun adaptiveReceiver false k (false, false)).map
      (fun (transcript, final) => (transcript, final, equivocate b transcript)) :=
  equivocation adaptiveReceiver b k (false, false)

/-- A continuation consumes the selected opening component, its private state, and fresh coins.
Its observation therefore checks the opening/transcript correlation beyond the commit marginal. -/
noncomputable def finish (transcript : Fin 2 → Fin 4 × Bool) (st : Bool × Bool)
    (o : Opening 2) : PMF (Bool × Bool × Bool) :=
  (PMF.uniformOfFintype Bool).map fun coin =>
    (o 0 (fin4ToBoolPair (transcript 0).1).2, st.1 ^^ st.2, coin)

example (b : Bool) : (do
      let (masks, transcript, final) ← receiverCommit adaptiveReceiver b 2 (false, false)
      finish transcript final (opening b masks)) = (do
      let (transcript, final) ← receiverRun adaptiveReceiver false 2 (false, false)
      finish transcript final (equivocate b transcript)) :=
  equivocation_bind adaptiveReceiver b 2 (false, false) finish

example (b : Bool) : receiverCommit adaptiveReceiver b 0 (true, false) =
    pure (Fin.elim0, Fin.elim0, (true, false)) := rfl

example (b : Bool) : equivocate (k := 0) b Fin.elim0 = opening b Fin.elim0 := by
  funext i
  exact Fin.elim0 i

example (b : Bool) : equivocatePairs b [] = [] := rfl

example : equivocatePairs true [(3, false), (2, false)] =
    [(true, false), (false, true)] := by decide

example : ComputableInPolyTime
    (fun input : Bool × List (Fin 4 × Bool) => equivocatePairs input.1 input.2)
    (encPair encBool (encList (encPair (encFinEnum (Fin 4)) encBool)))
    (encList (encPair encBool encBool)) := equivocatePairs_polyTime

end ComplexityTests.Crypto.OTCommitmentEquivocation
