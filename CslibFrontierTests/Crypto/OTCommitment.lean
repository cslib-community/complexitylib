/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.MPC.OTCommitment

/-!
# OT commitment regression tests

Honest correctness, an explicit double-opening attack and its rejection for the other selection,
the zero-call boundary, and a receiver whose next query depends on its previous answer.
-/

namespace CslibFrontierTests.Crypto.OTCommitment

open Cslib.Probability Cslib.Crypto.Protocols.MPC
open OTCommitment
open scoped ENNReal

example : Accepts (fun _ : Fin 2 => true) (fun _ => true) true
    (opening true (fun _ => false)) := by
  intro i
  simp [opening]

example : ¬ Accepts (fun _ : Fin 1 => true) (fun _ => false) true
    (opening true (fun _ => false)) := by
  intro h
  have := (h 0).2
  simp [opening] at this

/-- The sender submits zero tables, without encoding a binding commitment to a unique bit. -/
noncomputable def zeroSender : Sender Unit where
  choose _ _ := pure (fun _ => false, ())
  receive _ _ := ()

/-- Claim zero via all-zero pairs and one via `(false, true)` pairs. -/
def twoOpenings (k : ℕ) : Option (Opening k × Opening k) :=
  some (opening false (fun _ => false), opening true (fun _ => false))

example : doubleOpens (fun _ : Fin 1 => false) (fun _ => false) (twoOpenings 1) = true := by
  simp [doubleOpens, twoOpenings, Accepts, opening]

example : doubleOpens (fun _ : Fin 1 => true) (fun _ => false) (twoOpenings 1) = false := by
  simp [doubleOpens, twoOpenings, Accepts, opening]

/-- With no OT calls the verifier has no evidence: the attack succeeds with probability one. -/
example : bindingGame zeroSender 0 (pure ()) (fun _ => pure (twoOpenings 0)) true = 1 := by
  simp [bindingGame, senderRun, twoOpenings, doubleOpens, Accepts,
    PMF.bind_const, PMF.pure_apply]

example : bindingGame zeroSender 1 (pure ()) (fun _ => pure (twoOpenings 1)) true ≤
    (2 : ℝ≥0∞)⁻¹ := by
  simpa using binding zeroSender 1 (pure ()) (fun _ => pure (twoOpenings 1))

/-- The one-call bound is attained by this attack. -/
example : bindingGame zeroSender 1 (pure ()) (fun _ => pure (twoOpenings 1)) true =
    (2 : ℝ≥0∞)⁻¹ := by
  have hgame : bindingGame zeroSender 1 (pure ()) (fun _ => pure (twoOpenings 1)) =
      (PMF.uniformOfFintype (Fin 1 → Bool)).map (fun c => !(c 0)) := by
    simp only [bindingGame, Cslib.Probability.PMF.monad_bind_eq_bind,
      Cslib.Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, senderRun, zeroSender,
      transfer_eq, PMF.map]
    congr 1
    funext c
    cases h : c 0 <;>
      simp [doubleOpens, twoOpenings, Accepts, opening, Fin.forall_fin_one,
        Fin.cons, h]; rfl
  rw [hgame, Cslib.Probability.PMF.uniformOfFintype_map_apply]
  have hc : Nat.card {c : Fin 1 → Bool // (!(c 0)) = true} = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc]
  simp

/-- Query slot three after a true answer and slot zero after a false answer. -/
noncomputable def adaptiveReceiver : Receiver Bool where
  choose _ previous := pure (if previous then 3 else 0, previous)
  receive _ answer := pure answer

example (k : ℕ) : receiverRun adaptiveReceiver false k false =
    receiverRun adaptiveReceiver true k false :=
  perfectHiding adaptiveReceiver false true k false

end CslibFrontierTests.Crypto.OTCommitment
