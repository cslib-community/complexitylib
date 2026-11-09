/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.PolyTime

/-!
# Extracted OT commitment regression tests

A mixed-parity two-call sender attains extraction error one half, whereas its double-opening
success is one quarter. Empty commitments have extraction error one. The deterministic list
extractor is checked on empty, tied and strict-majority inputs and against its native certificate.
-/

namespace CslibFrontierTests.Crypto.OTCommitmentExtraction

open Cslib.Probability Cslib.Crypto.Protocols.MPC
open OTCommitment Turing.MultiTapeTM Turing.MultiTapeTM.Encodings
open scoped ENNReal

example : extractPairs [] = false := by decide
example : extractPairs [(false, false), (false, true)] = false := by decide
example : extractPairs [(false, false), (false, true), (true, false)] = true := by decide

example : ComputableInPolyTime extractPairs (encList (encPair encBool encBool)) encBool :=
  extractPairs_polyTime

/-- On two calls the sender submits one parity-zero row followed by one parity-one row. -/
noncomputable def mixedSender : Sender Unit where
  choose remaining _ := pure (table (remaining == 0) false, ())
  receive _ _ := ()

/-- Open to one using `(false, true)` in every row. -/
def claimOne (k : ℕ) : Option (Bool × Opening k) :=
  some (true, opening true (fun _ => false))

private theorem real_two : realOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())) =
    (PMF.uniformOfFintype (Fin 2 → Bool)).map
      (fun c => (if c 0 then none else some true, (), ())) := by
  simp only [realOpening, Cslib.Probability.PMF.monad_bind_eq_bind,
    Cslib.Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, senderRun, mixedSender,
    transfer_eq, PMF.map]
  congr 1 with c : 1
  cases h₀ : c 0 <;> cases h₁ : c 1 <;>
    simp [openResult, claimOne, Accepts, opening, table, Fin.forall_fin_two,
      Fin.cons, Fin.tail, h₀, h₁, fin4ToBoolPair_boolPairToFin4] <;> rfl

/-- The wrong extracted-bit opening is accepted with probability one half. -/
example : realOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ()))
    (some true, (), ()) = (2 : ℝ≥0∞)⁻¹ := by
  rw [real_two, Cslib.Probability.PMF.uniformOfFintype_map_apply]
  have hc : Nat.card {c : Fin 2 → Bool //
      (if c 0 then none else some true, (), ()) = (some true, (), ())} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc]
  norm_num only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat,
    Nat.reducePow]
  rw [← ENNReal.coe_ofNat 2, ← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_inv (by norm_num)]
  norm_num

/-- The simulator committed to false on the tie, so this true-opening attack always aborts. -/
example : simulatedOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())) =
    pure (none, (), ()) := by
  let ts : Fin 2 → Fin 4 → Bool :=
    Fin.cons (table false false) (Fin.cons (table true false) Fin.elim0)
  have ht : senderTables mixedSender 2 () = pure (ts, ()) := by
    simp only [senderTables_succ, senderTables_zero, mixedSender,
      Cslib.Probability.PMF.monad_bind_eq_bind,
      Cslib.Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rfl
  have he : extract ts = false := by decide
  have hresult (c : Fin 2 → Bool) : openResult c
      (fun i => ts i (boolPairToFin4 (false, c i))) (claimOne 2) ≠ some false := by
    simp only [openResult, claimOne]
    split <;> simp
  simp [simulatedOpening, ht, he, hresult, PMF.bind_const]

/-- The coupling bound is one half for two calls, not the double-opening bound one quarter. -/
example : Cslib.Probability.PMF.CoupledWithin
    (realOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())))
    (simulatedOpening mixedSender 2 (pure ()) (fun _ => pure (claimOne 2, ())))
    ((2 : ℝ≥0∞)⁻¹) := by
  simpa using simulatedOpening_coupled mixedSender 2 (pure ())
    (fun _ => pure (claimOne 2, ()))

/-- The same sender's double-opening success is one quarter. -/
example : bindingGame mixedSender 2 (pure ())
    (fun _ => pure (some (opening false (fun _ => false), opening true (fun _ => false)))) true =
    (2 : ℝ≥0∞)⁻¹ ^ 2 := by
  have he : bindingGame mixedSender 2 (pure ())
      (fun _ => pure (some (opening false (fun _ => false), opening true (fun _ => false)))) =
      (PMF.uniformOfFintype (Fin 2 → Bool)).map (fun c => (!(c 0)) && (!(c 1))) := by
    simp only [bindingGame, Cslib.Probability.PMF.monad_bind_eq_bind,
      Cslib.Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, senderRun, mixedSender,
      transfer_eq, PMF.map]
    congr 1 with c : 1
    cases h₀ : c 0 <;> cases h₁ : c 1 <;>
      simp [doubleOpens, Accepts, opening, table, Fin.forall_fin_two,
        Fin.cons, Fin.tail, h₀, h₁, fin4ToBoolPair_boolPairToFin4] <;> rfl
  rw [he, Cslib.Probability.PMF.uniformOfFintype_map_apply]
  have hc : Nat.card {c : Fin 2 → Bool // ((!(c 0)) && (!(c 1))) = true} = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc]
  norm_num [← ENNReal.inv_pow]

/-- With no calls, an opening to one is accepted even though the extractor's empty vote is false. -/
example : realOpening mixedSender 0 (pure ()) (fun _ => pure (claimOne 0, ())) =
    pure (some true, (), ()) := by
  simp [realOpening, senderRun, openResult, claimOne, Accepts, PMF.bind_const]

example : simulatedOpening mixedSender 0 (pure ()) (fun _ => pure (claimOne 0, ())) =
    pure (none, (), ()) := by
  have he : extract (k := 0) Fin.elim0 = false := by decide
  simp [simulatedOpening, senderTables_zero, he, openResult, claimOne, Accepts, PMF.bind_const]

end CslibFrontierTests.Crypto.OTCommitmentExtraction
