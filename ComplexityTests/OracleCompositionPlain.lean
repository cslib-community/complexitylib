/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Tactic.PolyTime

/-! Plain-hypothesis strict oracle PPT combinators: branches, finite dispatch and loops whose side
conditions are ordinary `ComputableInPolyTime` certificates. -/

namespace ComplexityTests.OracleCompositionPlain

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-- On a nonzero unary input `n`, ask the empty request and keep `n` reply bits. -/
private noncomputable def askUnlessZero (n : ℕ) : WordOracleComp Unit (List Bool) :=
  if n = 0 then pure [] else List.take n <$> ProbOracleComp.query ((), [])

private theorem isOraclePPTOn_ask :
    IsOraclePPTOn encUnary encBits (fun n : ℕ => List.take n <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), [])) :=
  IsOraclePPTOn.query_take' () (.const []) ComputableInPolyTime.id'

-- `ite'`: the decision `n = 0` is a plain certificate.
private theorem askUnlessZero_isOraclePPTOn : IsOraclePPTOn encUnary encBits askUnlessZero :=
  IsOraclePPTOn.ite' (by polytime) (ComputableInPolyTime.const []).isOraclePPTOn isOraclePPTOn_ask

/-- An oracle answering every request with `k` copies of `true`, counting its calls. -/
private noncomputable def constant (k : ℕ) (_ : Unit × List Bool) : StateT ℕ PMF (List Bool) :=
  fun calls => PMF.pure (List.replicate k true, calls + 1)

private theorem run_constant (k : ℕ) (request : Unit × List Bool) (calls : ℕ) :
    (constant k request).run calls = PMF.pure (List.replicate k true, calls + 1) := rfl

-- The zero branch makes no call; a nonzero input truncates a longer reply and makes one call.
example : (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) (constant 5))
      (askUnlessZero 0)).run 0 = PMF.pure ([], 0) := by
  simp [askUnlessZero]

example : (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) (constant 5))
      (askUnlessZero 2)).run 0 = PMF.pure ([true, true], 1) := by
  simp [askUnlessZero, run_constant]

/-- The branch selected by a Boolean tag: answer `[]` directly, or ask the oracle. -/
private noncomputable def branch (tag : Bool) (n : ℕ) : WordOracleComp Unit (List Bool) :=
  if tag then pure [] else List.take n <$> ProbOracleComp.query ((), [])

-- `finite_cases'`: a plain Boolean tag selects one of two certified branches.
example : IsOraclePPTOn encUnary encBits (fun n : ℕ => branch (decide (n = 0)) n) := by
  refine IsOraclePPTOn.finite_cases' (tagEncoding := encBool) (tag := fun n => decide (n = 0))
    (branch := branch) (by polytime) fun tag => ?_
  unfold branch
  cases tag
  · exact isOraclePPTOn_ask
  · exact (ComputableInPolyTime.const []).isOraclePPTOn

/-- Each round appends one reply bit to the bits collected so far. -/
private noncomputable def collectStep (bits : List Bool) : WordOracleComp Unit (List Bool) :=
  (bits ++ ·) <$> (List.take 1 <$> ProbOracleComp.query ((), bits))

private theorem collectStep_isOraclePPTOn : IsOraclePPTOn encBits encBits collectStep :=
  (IsOraclePPTOn.query_take' () ComputableInPolyTime.id' (.const 1)).map_with' (by polytime)

private theorem length_le_of_mem_collectStep {bits next : List Bool}
    (h : next ∈ OracleComp.support (collectStep bits)) : next.length ≤ bits.length + 1 := by
  obtain ⟨prefix_, hprefix, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp h
  obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hprefix
  simpa only [List.length_append] using Nat.add_le_add_left (List.length_take_le _ _) _

private theorem polyBounded_unary : PolyBounded (fun n : ℕ => (encUnary n).length) id :=
  .of_forall_le 1 1 fun n => by simp [encUnary_apply]

-- `iterate_spec'`: `n` rounds from the empty word, with the invariant "length ≤ rounds".
example : IsOraclePPTOn encUnary encBits (fun n => OracleComp.iterate n collectStep []) :=
  (IsOraclePPTOn.iterate_spec' (count := id) (initial := fun _ => [])
    ComputableInPolyTime.id' (.const []) collectStep_isOraclePPTOn
    (fun _ i bits => bits.length ≤ i) (fun _ => le_rfl)
    (fun _ _ _ _ hbits _ hnext => (length_le_of_mem_collectStep hnext).trans (by lia))
    polyBounded_unary (fun _ _ _ hi hbits => by simp only [encBits_apply]; exact hbits.trans hi)).1

-- `iterateWith_spec'`: the step reads only the state, captured through the paired input.
example : IsOraclePPTOn encUnary encBits (fun n => OracleComp.iterate n
    ((fun (_ : ℕ) bits => collectStep bits) n) []) :=
  (IsOraclePPTOn.iterateWith_spec' (count := id) (initial := fun _ => [])
    (step := fun _ bits => collectStep bits)
    ComputableInPolyTime.id' (.const [])
    (collectStep_isOraclePPTOn.preprocess' (ComputableInPolyTime.snd encUnary encBits))
    (fun _ i bits => bits.length ≤ i) (fun _ => le_rfl)
    (fun _ _ _ _ hbits _ hnext => (length_le_of_mem_collectStep hnext).trans (by lia))
    polyBounded_unary (fun _ _ _ hi hbits => by simp only [encBits_apply]; exact hbits.trans hi)).1

end ComplexityTests.OracleCompositionPlain
