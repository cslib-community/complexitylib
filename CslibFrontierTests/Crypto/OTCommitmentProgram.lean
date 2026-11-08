/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Program.PolyTime
import CslibFrontier.Tactic.PPT

/-! A concrete uniformly efficient adaptive receiver, plus a separately efficient callback
excluded by the necessary iteration-growth contract. -/

@[expose] public section

namespace ComplexityTests.Crypto.OTCommitmentProgram

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.MPC.OTCommitment Cslib.Crypto.Protocols.Commitment
open Turing.MultiTapeTM

abbrev State := Bool × List Bool
abbrev Later := Bool × List Bool
abbrev Output := Bool × Phased.Observation × Option (List (Bool × Bool))

def stateEncoding : State ↪ List Bool := encPair encBool encBits
noncomputable def outputEncoding : Output ↪ List Bool :=
  encPair encBool (encPair (encFinite Phased.Observation)
    (encOption (encList (encPair encBool encBool))))

-- The fresh private coin picks the duplicated slot; the previous selected answer picks parity.
noncomputable def choose (_ : ℕ) (st : State) : ProbComp (Fin 4 × State) := do
  let privateCoin ← ProbComp.uniform Bool
  return (boolPairToFin4 (privateCoin, st.1), (privateCoin, st.2))

def receive (st : State) (answer : Bool) : ProbComp State :=
  pure (answer, answer :: st.2)

noncomputable def plan (_ : List (Fin 4 × Bool)) (st : State) : ProbComp (Bool × Later) := do
  let release ← ProbComp.uniform Bool
  return (release, (release, st.2))

noncomputable def finish (_ : List (Fin 4 × Bool)) (_ : State) (later : Later)
    (observed : Phased.Observation) (pairs : Option (List (Bool × Bool))) : ProbComp Output := do
  let privateCoin ← ProbComp.uniform Bool
  return (privateCoin ^^ later.1, observed, pairs)

theorem choose_isPPT : IsPPTOn (encPair encUnary stateEncoding)
    (encPair (encFinEnum (Fin 4)) stateEncoding) (fun p => choose p.1 p.2) := by
  have hindex : ComputableInPolyTime boolPairToFin4
      (encPair encBool encBool) (encFinEnum (Fin 4)) := .of_finite _
  unfold choose stateEncoding
  ppt

theorem receive_isPPT : IsPPTOn (encPair stateEncoding encBool) stateEncoding
    (fun p => receive p.1 p.2) := by
  unfold receive stateEncoding
  ppt

theorem choose_growth (k : ℕ) (st : State) (j : Fin 4) (next : State)
    (h : (j, next) ∈ (ProbComp.eval (choose k st)).support) :
    (stateEncoding next).length ≤ (stateEncoding st).length + 0 := by
  simp only [choose, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨coin, _, h⟩ := h
  cases h
  simp [stateEncoding]

theorem receive_growth (st : State) (answer : Bool) (next : State)
    (h : next ∈ (ProbComp.eval (receive st answer)).support) :
    (stateEncoding next).length ≤ (stateEncoding st).length + 1 := by
  simp only [receive, ProbComp.eval_pure, PMF.mem_support_pure_iff] at h
  cases h
  simp [stateEncoding]

-- One machine works for every unary round count and every honestly encoded auxiliary state.
theorem simulator_isPPT :
    IsPPTOn (encPair encBool (encPair encUnary stateEncoding))
      (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation)
        (encPair (encList (encPair (encFinEnum (Fin 4)) encBool))
          (encPair stateEncoding (encPair stateEncoding outputEncoding)))))
      (fun p => receiverClosedProgram choose receive p.1 p.2.1 p.2.2 plan finish) := by
  apply receiverClosedProgram_isPPT stateEncoding stateEncoding outputEncoding choose receive
    plan finish choose_isPPT receive_isPPT
  · unfold plan stateEncoding
    ppt
  · unfold finish outputEncoding stateEncoding
    ppt
  · exact choose_growth
  · exact receive_growth

-- A real supported adaptive run visits duplicated slots 2 and 3 and retains selected answers.
theorem adaptive_slots_support :
    ([(2, true), (3, false)], (false, [false, true])) ∈
      (ProbComp.eval (receiverViewProgram choose receive 2 (false, []))).support := by
  simp [receiverViewProgram_succ, receiverViewProgram_zero, choose, receive,
    ProbComp.eval_bind, boolPairToFin4]

-- Zero OT rounds still perform the phased opening and pass its bit separately to the callback.
theorem zero_opened (b : Bool) :
    ProbComp.eval (receiverClosedProgram choose receive b 0 (false, [])
      (fun _ _ => pure (true, ()))
      (fun _ _ _ observed pairs => pure (observed, pairs))) =
      PMF.pure (.receipt, .opened b, [], (false, []), (), (.opened b, some [])) := by
  simp [receiverClosedProgram_eq, receiverViewProgram_zero, equivocatePairs]

theorem zero_withheld (b : Bool) :
    ProbComp.eval (receiverClosedProgram choose receive b 0 (false, [])
      (fun _ _ => pure (false, ()))
      (fun _ _ _ observed pairs => pure (observed, pairs))) =
      PMF.pure (.receipt, .aborted, [], (false, []), (), (.aborted, none)) := by
  simp [receiverClosedProgram_eq, receiverViewProgram_zero]

-- The complete certified private-coin instance has the same law as honest OT with its actual
-- opening masks, including randomized withholding, retained later state and the final coin.
theorem adaptive_simulation (b : Bool) (k : ℕ) (st : State) :
    ProbComp.eval (receiverClosedProgram choose receive b k st plan finish) =
      (receiverReal (receiverOfPrograms choose receive) b k st
        (fun transcript final => ProbComp.eval (plan (List.ofFn transcript) final))
        (fun transcript final later observed pairs => ProbComp.eval
          (finish (List.ofFn transcript) final later observed
            (pairs.map (fun o => List.ofFn (fun i => (o i false, o i true))))))).map
        (fun (received, observed, transcript, final, later, out) =>
          (received, observed, List.ofFn transcript, final, later, out)) :=
  eval_receiverClosedProgram_eq_real choose receive b k st plan finish

-- Every duplicated OT slot preserves the selected answer in a one-round actual program run.
theorem selected_answer (j : Fin 4) (b : Bool) :
    (ProbComp.eval (receiverClosedProgram (fun (_ : ℕ) (_ : Unit) => pure (j, ()))
      (fun _ _ => pure ()) b 1 () (fun _ _ => pure (true, ()))
      (fun transcript _ _ _ pairs => pure
        (let pair := (pairs.getD []).headD (false, false)
         (if (fin4ToBoolPair j).2 then pair.2 else pair.1) ==
           (transcript.headD (0, false)).2)))).map
      (fun result => result.2.2.2.2.2) = PMF.pure true := by
  calc
    _ = (PMF.uniformOfFintype Bool).map (fun _ => true) := by
      cases h : (fin4ToBoolPair j).2 <;>
        simp [receiverClosedProgram_eq, receiverViewProgram_succ, receiverViewProgram_zero,
          equivocatePairs, equivocate, opening, h, PMF.map_comp, Function.comp_def]
    _ = _ := PMF.map_const _ _

-- Each doubling call is strict PPT, but repeated calls may make exponentially large states.
def doubling (bits : List Bool) (_ : Bool) : ProbComp (List Bool) := pure (bits ++ bits)

theorem doubling_isPPT : IsPPTOn (encPair encBits encBool) encBits
    (fun p => doubling p.1 p.2) := by
  unfold doubling
  ppt

theorem doubling_has_no_additive_bound :
    ¬ ∃ growth : ℕ, ∀ bits answer next,
      next ∈ (ProbComp.eval (doubling bits answer)).support →
      (encBits next).length ≤ (encBits bits).length + growth := by
  rintro ⟨growth, h⟩
  have h := h (List.replicate (growth + 1) false) false
    (List.replicate (growth + 1) false ++ List.replicate (growth + 1) false)
    (by simp [doubling])
  simp only [encBits_apply, List.length_append, List.length_replicate] at h
  omega

end ComplexityTests.Crypto.OTCommitmentProgram
