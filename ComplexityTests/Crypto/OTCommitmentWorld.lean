/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.World

/-! Actual phased-world simulations: mixed-parity attack, withheld openings and private state. -/

@[expose] public section

namespace Cslib.Tests.OTCommitmentWorld

open Probability Crypto.Protocols.MPC OTCommitment Crypto.Protocols.Commitment
open scoped ENNReal

/-- The mixed-parity attack from the extraction tests, with one row of each parity. -/
noncomputable def mixedSender : Sender Unit where
  choose remaining _ := pure (table (remaining == 0) false, ())
  receive _ _ := ()

def claimOne (k : ℕ) : Option (Bool × Opening k) :=
  some (true, opening true (fun _ => false))

noncomputable def fixedReceiver (j : Fin 4) : Receiver Unit where
  choose _ _ := pure (j, ())
  receive _ _ := pure ()

/-- Retain fresh private randomness and select duplicated slot zero or three. -/
noncomputable def adaptiveReceiver : Receiver (Bool × Bool) where
  choose _ st := pure (if st.1 ^^ st.2 then 3 else 0, st)
  receive _ answer := (PMF.uniformOfFintype Bool).map (answer, ·)

/-- The actual ideal-world store commits false on the tie and aborts the attempted true opening. -/
example : (senderIdeal mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())) .idle).map
    Prod.fst = pure (Phased.Observation.receipt, Phased.Observation.aborted, (), ()) := by
  rw [senderIdeal_run]
  let ts : Fin 2 → Fin 4 → Bool :=
    Fin.cons (table false false) (Fin.cons (table true false) Fin.elim0)
  have ht : senderTables mixedSender 2 () = pure (ts, ()) := by
    simp only [senderTables_succ, senderTables_zero, mixedSender, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind]
    rfl
  have he : extract ts = false := by decide
  have hresult (c : Fin 2 → Bool) : openResult c
      (fun i => ts i (boolPairToFin4 (false, c i))) (claimOne 2) ≠ some false := by
    simp only [openResult, claimOne]
    split <;> simp
  simp [simulatedOpening, ht, he, hresult, PMF.bind_const]

/-- The real attacker can nevertheless open to true with probability one half. -/
example : ((realOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ()))).map
    (fun (result, _, _) => result.elim Phased.Observation.aborted .opened)) (.opened true) =
      (2 : ℝ≥0∞)⁻¹ := by
  have hr : realOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())) =
      (PMF.uniformOfFintype (Fin 2 → Bool)).map
        (fun c => (if c 0 then none else some true, (), ())) := by
    simp only [realOpening, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, senderRun, mixedSender, transfer_eq, PMF.map]
    congr 1
    funext c
    cases h₀ : c 0 <;> cases h₁ : c 1 <;>
      simp [openResult, claimOne, Accepts, opening, table, Fin.forall_fin_two,
        Fin.cons, Fin.tail, h₀, h₁, fin4ToBoolPair_boolPairToFin4] <;> rfl
  rw [hr, PMF.map_comp, PMF.uniformOfFintype_map_apply]
  have hc : Nat.card {c : Fin 2 → Bool //
      (if c 0 then (none : Option Bool) else some true).elim
        Phased.Observation.aborted .opened = .opened true} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  dsimp only [Function.comp_def]
  rw [hc]
  norm_num only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat,
    Nat.reducePow]
  rw [← ENNReal.coe_ofNat 2, ← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_inv (by norm_num)]
  norm_num

/-- Preserve the private release coin as the receiver's later state. -/
noncomputable def privatePlan {State : Type} {k : ℕ}
    (_ : Fin k → Fin 4 × Bool) (_ : State) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype Bool).map fun coin => (coin, coin)

/-- A randomized continuation consumes the terminal observation and optional opening. -/
noncomputable def laterFinish (τ : Fin 2 → Fin 4 × Bool) (st : Bool × Bool)
    (later : Bool) (observed : Phased.Observation) (pairs : Option (Opening 2)) :
    PMF (Phased.Observation × Bool × Bool × Option Bool × Bool) :=
  (PMF.uniformOfFintype Bool).map fun coin =>
    (observed, st.1 ^^ st.2, later,
      pairs.map (fun o => o 0 (fin4ToBoolPair (τ 0).1).2), coin)

-- This retains both private states and the fresh continuation coin even when the plan aborts.
example (b : Bool) :
    (receiverIdeal adaptiveReceiver b 2 (false, false) privatePlan laterFinish .idle).map
        Prod.fst = receiverReal adaptiveReceiver b 2 (false, false) privatePlan laterFinish :=
  receiverIdeal_eq_real adaptiveReceiver b 2 (false, false) privatePlan laterFinish

-- All four OT slots preserve answer/opening correlation through the actual ideal world.
example (j : Fin 4) :
    ((receiverIdeal (fixedReceiver j) true 1 () (fun _ _ => pure (true, ()))
      (fun τ _ _ observed pairs => pure
        (observed, (τ 0).2, pairs.map (fun o => o 0 (fin4ToBoolPair j).2))) .idle).map
      Prod.fst).map (fun (_, _, _, _, _, out) => out) =
        (PMF.uniformOfFintype Bool).map (fun r =>
          (Phased.Observation.opened true, table true r j, some (table true r j))) := by
  rw [receiverIdeal_eq_real]
  simp only [receiverReal, receiverCommit_zero, receiverCommit_succ, fixedReceiver, transfer_eq,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    ↓reduceIte, PMF.map, PMF.bind_bind, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype Bool).bind)
  funext r
  fin_cases j <;> cases r <;> rfl

-- At zero calls the public opened bit is still available to the continuation.
example (b : Bool) :
    ((receiverIdeal (fixedReceiver 3) b 0 () (fun _ _ => pure (true, ()))
      (fun _ _ _ observed _ => pure observed) .idle).map Prod.fst).map
        (fun (_, observed, _, _, _, out) => (observed, out)) = pure (.opened b, .opened b) := by
  rw [receiverIdeal_eq_real]
  simp [receiverReal, receiverCommit_zero]

-- Withholding passes no opening and leaves an observable terminal abort.
example (b : Bool) :
    ((receiverIdeal (fixedReceiver 2) b 0 () (fun _ _ => pure (false, true))
      (fun _ _ later observed pairs => pure (later, observed, pairs.isSome)) .idle).map
      Prod.fst).map (fun (_, observed, _, _, _, out) => (observed, out)) =
        pure (.aborted, true, .aborted, false) := by
  rw [receiverIdeal_eq_real]
  simp [receiverReal, receiverCommit_zero]

end Cslib.Tests.OTCommitmentWorld
