/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.SenderProgram.PolyTime
import CslibFrontier.Tactic.PPT

/-! Actual supplied sender programs, uniform growing schedules and excluded doubling. -/

@[expose] public section

namespace CslibFrontierTests.Crypto.OTCommitmentSenderProgram

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.MPC.OTCommitment Cslib.Crypto.Protocols.Commitment
open Turing.MultiTapeTM
open scoped ENNReal

noncomputable def choose (_ : ℕ) (history : List Bool) :
    ProbComp ((Fin 4 → Bool) × List Bool) := do
  let mask ← ProbComp.uniform Bool
  return (table true mask, mask :: history)

def receive (history : List Bool) (_ : Unit) : List Bool := history

noncomputable def finish (_ : ℕ) (history : List Bool) :
    ProbComp (Option (Bool × List (Bool × Bool)) × Bool) := do
  let release ← ProbComp.uniform Bool
  let privateCoin ← ProbComp.uniform Bool
  return (if release then some (true, history.reverse.map fun r => (r, r ^^ true)) else none,
    privateCoin)

theorem choose_isPPT : IsPPTOn (encPair encUnary encBits)
    (encPair (encFinEnum (Fin 4 → Bool)) encBits) (fun p => choose p.1 p.2) := by
  have htable : ComputableInPolyTime (table true) encBool (encFinEnum (Fin 4 → Bool)) :=
    .of_finite _
  unfold choose
  ppt

theorem finish_isPPT : IsPPTOn (encPair encUnary encBits)
    (encPair (encOption (encPair encBool (encList (encPair encBool encBool)))) encBool)
    (fun p => finish p.1 p.2) := by
  have hpairs : ComputableInPolyTime
      (fun history : List Bool => history.reverse.map fun r => (r, r ^^ true))
      encBits (encList (encPair encBool encBool)) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.bitsToList.comp ComputableInPolyTime.bitsReverse)
      ((ComputableInPolyTime.of_finite (fun r : Bool => (r, r ^^ true))).comp (.snd _ _))
  unfold finish
  ppt

theorem round_growth (k : ℕ) (st : List Bool) (t : Fin 4 → Bool) (middle : List Bool)
    (h : (t, middle) ∈ (ProbComp.eval (choose k st)).support) :
    (encBits (receive middle ())).length ≤ (encBits st).length + 1 := by
  simp only [choose, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨coin, _, h⟩ := h
  cases h
  simp [receive]

-- Uniform over growing unary round counts and arbitrary charged initial histories.
theorem simulator_isPPT : IsPPTOn (encPair encUnary encBits)
    (encPair (encFinite Phased.Observation)
      (encPair (encFinite Phased.Observation) (encPair encBits encBool)))
    (fun p => senderClosedProgram choose receive p.1 p.2 finish) :=
  senderClosedProgram_isPPT encBits encBool choose receive finish choose_isPPT
    ComputableInPolyTime.id' finish_isPPT 1 round_growth

-- One uniform machine for the concrete security schedule k=2n, initialized with empty history.
example : IsPPTOn encUnary
    (encPair (encFinite Phased.Observation)
      (encPair (encFinite Phased.Observation) (encPair encBits encBool)))
    (fun n => senderClosedProgram choose receive (2 * n) [] finish) :=
  simulator_isPPT.preprocess (prepare := fun n : ℕ => (2 * n, ([] : List Bool)))
    (((ComputableInPolyTime.const 2).unary_mul' ComputableInPolyTime.id').prod
      (ComputableInPolyTime.const []))

-- Real supported private randomness is retained in commit-final history.
example : ([table true true, table true false], [false, true]) ∈
    (ProbComp.eval (senderViewProgram choose receive 2 [])).support := by
  simp [senderViewProgram_succ, senderViewProgram_zero, choose, receive, ProbComp.eval_bind]

-- Randomized finish really supports opening and abort, with its independent output coin retained.
example : (Phased.Observation.receipt, Phased.Observation.opened true, [false], true) ∈
    (ProbComp.eval (senderClosedProgram choose receive 1 [] finish)).support := by
  simp [senderClosedProgram_eq, senderViewProgram_succ, senderViewProgram_zero,
    choose, receive, finish, BitString.sampleList, ProbComp.eval_bind,
    extractPairs, BitString.listStrictMajority, selectedBits, openPairs,
    table, fin4ToBoolPair_boolPairToFin4]

example : (Phased.Observation.receipt, Phased.Observation.aborted, [false], false) ∈
    (ProbComp.eval (senderClosedProgram choose receive 1 [] finish)).support := by
  simp [senderClosedProgram_eq, senderViewProgram_succ, senderViewProgram_zero,
    choose, receive, finish, BitString.sampleList, ProbComp.eval_bind,
    extractPairs, BitString.listStrictMajority, selectedBits, openPairs,
    table, fin4ToBoolPair_boolPairToFin4]

-- Zero rounds have the documented error bound 1; no binding claim follows from empty lists.
example : ((2 : ℝ≥0∞)⁻¹ ^ (0 - 0 / 2)) = 1 := by simp
example : decodeOpening 0 (some (true, [])) = some (true, Fin.elim0) := by
  simp only [decodeOpening, Option.bind_some, List.length_nil, ↓reduceIte, Option.some.injEq,
    Prod.mk.injEq, true_and]
  funext i
  exact Fin.elim0 i

-- Reject both malformed opening directions before creating a semantic finite opening.
example : decodeOpening 2 (some (true, [(false, true)])) = none := rfl
example : decodeOpening 1 (some (true, [(false, true), (false, true)])) = none := rfl

-- Actual zero-round world executions distinguish accepted false from rejected true.
example : ProbComp.eval (senderClosedProgram choose receive 0 []
    (fun _ _ => pure (some (false, []), ()))) =
      pure (Phased.Observation.receipt, Phased.Observation.opened false, [], ()) := by
  simp [senderClosedProgram_eq, senderViewProgram_zero, BitString.sampleList,
    extractPairs, BitString.listStrictMajority, selectedBits, openPairs]

example : ProbComp.eval (senderClosedProgram choose receive 0 []
    (fun _ _ => pure (some (true, []), ()))) =
      pure (Phased.Observation.receipt, Phased.Observation.aborted, [], ()) := by
  simp [senderClosedProgram_eq, senderViewProgram_zero, BitString.sampleList,
    extractPairs, BitString.listStrictMajority, selectedBits, openPairs]

noncomputable def mixedChoose (remaining : ℕ) (_ : Unit) :
    ProbComp ((Fin 4 → Bool) × Unit) := pure (table (remaining == 0) false, ())

def mixedFinish (_ : ℕ) (_ : Unit) :
    ProbComp (Option (Bool × List (Bool × Bool)) × Unit) :=
  pure (some (true, [(false, true), (false, true)]), ())

-- The actual simulator commits false on the parity tie and rejects this claimed true opening.
theorem mixed_ideal_aborts : ProbComp.eval (senderClosedProgram mixedChoose (fun _ _ => ())
    2 () mixedFinish) = pure (Phased.Observation.receipt, Phased.Observation.aborted, (), ()) := by
  have he : extractPairs [(false, false), (false, true)] = false := by decide
  have hresult (choices : List Bool) :
      openPairs choices (selectedBits [table false false, table true false] choices)
        (some (true, [(false, true), (false, true)])) ≠ some false := by
    change (if _ then some true else none) ≠ some false
    split <;> simp
  calc
    _ = (BitString.uniformList 2).map (fun _ =>
        (Phased.Observation.receipt, Phased.Observation.aborted, (), ())) := by
      simp [senderClosedProgram_eq, senderViewProgram_succ, senderViewProgram_zero,
        mixedChoose, mixedFinish, table, fin4ToBoolPair_boolPairToFin4, he, hresult]
    _ = _ := PMF.map_const _ _

-- The actual native driver rejects a short list, rather than accepting an empty zip.
example : ProbComp.eval (senderClosedProgram mixedChoose (fun _ _ => ()) 1 ()
    (fun _ _ => pure (some (true, []), ()))) =
      pure (Phased.Observation.receipt, Phased.Observation.aborted, (), ()) := by
  calc
    _ = (PMF.uniformOfFintype Bool).map (fun _ =>
        (Phased.Observation.receipt, Phased.Observation.aborted, (), ())) := by
      simp [senderClosedProgram_eq, senderViewProgram_succ, senderViewProgram_zero,
        mixedChoose, BitString.sampleList, extractPairs, BitString.listStrictMajority,
        selectedBits, openPairs]
    _ = _ := PMF.map_const _ _

-- The same actual OT attack opens true in the real world with probability 1/2.
theorem mixed_real_accepts_half :
    ((realOpening (senderOfPrograms mixedChoose (fun _ _ => ())) 2 (pure ())
      (fun final => (ProbComp.eval (mixedFinish 2 final)).map
        (fun (submission, out) => (decodeOpening 2 submission, out)))).map
      (fun (result, _, _) => result.elim Phased.Observation.aborted .opened)) (.opened true) =
      (2 : ℝ≥0∞)⁻¹ := by
  have hr : realOpening (senderOfPrograms mixedChoose (fun _ _ => ())) 2 (pure ())
      (fun final => (ProbComp.eval (mixedFinish 2 final)).map
        (fun (submission, out) => (decodeOpening 2 submission, out))) =
      (PMF.uniformOfFintype (Fin 2 → Bool)).map
        (fun c => (if c 0 then none else some true, (), ())) := by
    simp only [realOpening, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, senderRun, senderOfPrograms, mixedChoose, mixedFinish,
      ProbComp.eval_pure, transfer_eq, PMF.map]
    congr 1 with c : 1
    cases h₀ : c 0 <;> cases h₁ : c 1 <;>
      simp [openResult, decodeOpening, Accepts, table, Fin.forall_fin_two,
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

-- Efficient individual callbacks can still yield exponential state growth under iteration.
def doubling (st : List Bool) (_ : Unit) : List Bool := st ++ st

example : ComputableInPolyTime (fun st => doubling st ()) encBits encBits := by
  unfold doubling
  fun_prop

noncomputable def keepState (_ : ℕ) (st : List Bool) :
    ProbComp ((Fin 4 → Bool) × List Bool) := pure (table false false, st)

example : IsPPTOn (encPair encUnary encBits)
    (encPair (encFinEnum (Fin 4 → Bool)) encBits) (fun p => keepState p.1 p.2) := by
  unfold keepState
  ppt

theorem doubling_excluded : ¬ ∃ growth : ℕ,
    ∀ k st t middle, (t, middle) ∈ (ProbComp.eval (keepState k st)).support →
      (encBits (doubling middle ())).length ≤ (encBits st).length + growth := by
  rintro ⟨growth, h⟩
  have hg := h 0 (List.replicate (growth + 1) false) (table false false)
    (List.replicate (growth + 1) false) (by simp [keepState])
  simp only [doubling, encBits_apply, List.length_append, List.length_replicate] at hg
  omega

end CslibFrontierTests.Crypto.OTCommitmentSenderProgram
