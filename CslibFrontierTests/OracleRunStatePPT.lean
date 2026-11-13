/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Tactic.PPT

/-! Clients of `IsOraclePPTOn.isPPTOn_runState`: a program run against a stateful oracle that
accumulates sampled bits, and a parameterized program run against a one-time oracle. -/

namespace CslibFrontierTests.OracleRunStatePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- Request the empty word once and return at most the first reply bit. -/
noncomputable def requestHead (_ : List Bool) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), [])

theorem requestHead_isOraclePPTOn : IsOraclePPTOn encBits encBits requestHead := by
  unfold requestHead
  fun_prop

/-- Reply with a fresh bit followed by the caller's word, and push the bit onto the state. -/
noncomputable def respond (caller : List Bool) (_ : Unit × List Bool) :
    StateT (List Bool) ProbComp (List Bool) := fun state => do
  let bit ← ProbComp.uniform Bool
  return (bit :: caller, bit :: state)

-- The run against the accumulating oracle is PPT, with the final state returned. Replies grow
-- with the caller, and the invariant that the state is at least as long survives every call.
example : IsPPTOn encBits (encPair encBits encBits)
    (fun word => ((requestHead word).runState (respond word)).run word) := by
  apply requestHead_isOraclePPTOn.isPPTOn_runState (operationEncoding := encFinEnum Unit)
    (resources := fun caller _ => caller.length + 1)
    (by fun_prop) (by unfold respond; fun_prop)
    (by fun_prop) (fun caller state => caller.length ≤ state.length)
    (fun _ => le_rfl) (by fun_prop)
  intro caller request state hstate result hresult
  simp only [respond, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨bit, _, hresult⟩ := hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp only [encBits_apply, List.length_cons]
  exact ⟨by lia, le_rfl, by lia⟩

/-- Answer the first request with the caller's word and every later one with the empty word. -/
noncomputable def oneTime (caller : ℕ × List Bool) (_ : Unit × List Bool) :
    StateT Bool ProbComp (List Bool) := fun used =>
  pure (if used then [] else caller.2, true)

-- The parameterized form: the security parameter and word are the caller, and the one-time
-- oracle's state records whether it has answered.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits encBool)
    (fun caller => ((requestHead caller.2).runState (oneTime caller)).run false) := by
  apply IsOraclePPT.isPPTOn_runState (program := fun _ word => requestHead word)
    (operationEncoding := encFinEnum Unit) (prepare := fun caller => caller)
    (resources := fun caller _ => caller.2.length)
    (by unfold requestHead; fun_prop) (by fun_prop) (by unfold oneTime; fun_prop)
    (by fun_prop) (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request used _ result hresult
  simp only [oneTime, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  cases used <;> simp [encBool_apply]

end CslibFrontierTests.OracleRunStatePPT
