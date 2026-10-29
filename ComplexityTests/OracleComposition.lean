/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.QueryBounds
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-! Compositional strict oracle PPT: adaptive branches, stateful oracles, loops and boundaries. -/

namespace ComplexityTests.OracleComposition

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-! ### An adaptive branch with a stateful oracle -/

/-- Query channel `false` with the input. Only if the first reply bit is `true`, query channel
`true` with that bit and return an input-length prefix of the second reply. -/
private noncomputable def adaptive (word : List Bool) : WordOracleComp Bool (List Bool) := do
  let first ← List.take 1 <$> ProbOracleComp.query (false, word)
  if first = [true] then List.take word.length <$> ProbOracleComp.query (true, first)
  else pure []

-- The certificate is found compositionally from the bounded-prefix query and the conditional.
private theorem adaptive_isOraclePPTOn : IsOraclePPTOn encBits encBits adaptive := by
  unfold adaptive
  fun_prop

-- On the empty input, the certificate bounds both the query count and request lengths.
example : ∃ c d : ℕ, (adaptive []).IsQueryBounded (c * 1 ^ d) ∧
    (adaptive []).QueriesSatisfy fun request => request.2.length ≤ c * 1 ^ d := by
  obtain ⟨c, d, h⟩ := adaptive_isOraclePPTOn.query_bounds
  exact ⟨c, d, by simpa using h []⟩

/-- A stateful handler whose reply depends on the number of calls answered so far. -/
private noncomputable def counting (reply : ℕ → List Bool) (_ : Bool × List Bool) :
    StateT ℕ PMF (List Bool) :=
  fun calls => PMF.pure (reply calls, calls + 1)

private theorem run_counting (reply : ℕ → List Bool) (request : Bool × List Bool) (calls : ℕ) :
    (counting reply request).run calls = PMF.pure (reply calls, calls + 1) := rfl

-- The unselected branch makes no call: the counter records exactly one external request.
example (word : List Bool) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (counting fun _ => [false, true])) (adaptive word)).run 0 = PMF.pure ([], 1) := by
  simp [adaptive, run_counting]

-- The selected branch sees the first reply prefix and the advanced oracle state; the long second
-- reply is truncated to the input length.
example :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (counting fun calls => List.replicate (calls + 5) true))
          (adaptive [false, false, false])).run 0 = PMF.pure ([true, true, true], 2) := by
  simp [adaptive, run_counting]

/-! ### Closed sampling and adaptive loops -/

-- A closed PPT sampler is oracle PPT, and its sample may form an external request.
example : IsOraclePPTOn (Operation := Unit) encUnary encBits (fun n => do
    let request ← ProbOracleComp.sample (BitString.sampleList n)
    List.take n <$> ProbOracleComp.query ((), request)) := by
  have hsample := isPPTOn_sampleList.isOraclePPTOn (Operation := Unit)
  fun_prop

/-- Each round queries the oracle with the bits collected so far and keeps one reply bit. -/
private noncomputable def collectStep (bits : List Bool) : WordOracleComp Unit (List Bool) :=
  (bits ++ ·) <$> (List.take 1 <$> ProbOracleComp.query ((), bits))

-- An adaptive loop with growing requests is strict oracle PPT by its one-bit growth bound.
example : IsOraclePPTOn encUnary encBits
    (fun n => OracleComp.iterate n collectStep []) := by
  refine IsOraclePPTOn.iterate_of_bounded_growth (count := fun n => n) (initial := fun _ => [])
    (by fun_prop) (.const []) (by unfold collectStep; fun_prop) (growth := 1) ?_
  intro bits next hnext
  obtain ⟨prefix_, hprefix, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hprefix
  simp only [encBits, Function.Embedding.coe_refl, id_eq, List.length_append]
  exact Nat.add_le_add_left (List.length_take_le _ _) _

/-! ### Failure boundaries -/

/-- An exponential output cannot have a polynomial-length encoding. -/
private theorem not_two_pow_le (c d : ℕ) : ∃ n, c * (n + 1) ^ d < 2 ^ n :=
  (Cslib.PolynomiallyBounded.eventually_lt_two_pow
    (Cslib.PolynomiallyBounded.of_forall_le c d fun _ => le_rfl)).exists

-- A reply prefix whose length is exponential in the input is not strict oracle PPT.
example : ¬ IsOraclePPTOn encUnary encBits (fun n => List.take (2 ^ n) <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), [])) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  obtain ⟨n, hn⟩ := not_two_pow_le c d
  have hlength := hbound n Unit (fun _ s => PMF.pure (List.replicate (2 ^ n) true, s)) () ()
    (List.replicate (2 ^ n) true) (by
      rw [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query]
      simp [StateT.run])
  simp only [encBits, Function.Embedding.coe_refl, id_eq, List.length_replicate, encUnary_apply]
    at hlength
  lia

-- A one-bit output does not hide an exponentially long request: writing the request is charged.
example : ¬ IsOraclePPTOn encUnary encBits (fun n => List.take 1 <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), List.replicate (2 ^ n) true)) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.query_bounds
  obtain ⟨n, hn⟩ := not_two_pow_le c d
  have hcall := (hbound n).2.forall_mem_transcript (fun _ (s : Unit) => PMF.pure ([], s))
    (s := ()) (s' := ()) (result := [])
    (transcript := [⟨((), List.replicate (2 ^ n) true), []⟩]) (by
      rw [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query]
      simp [OracleComp.withTranscript, StateT.run]) _ List.mem_cons_self
  simp only [List.length_replicate, encUnary_apply] at hcall
  lia

-- A polynomial reply prefix is strict oracle PPT.
example : IsOraclePPTOn encUnary encBits (fun n => List.take n <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), [])) := by
  fun_prop

-- Repeated doubling of retained state is not strict oracle PPT, even without any oracle call.
example : ¬ IsOraclePPTOn (Operation := Unit) encUnary encBits
    (fun n => OracleComp.iterate n (fun word => pure (word ++ word)) [true]) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  obtain ⟨n, hn⟩ := not_two_pow_le c d
  have hiterate (m : ℕ) : (OracleComp.iterate m (fun word : List Bool => pure (word ++ word))
      [true] : WordOracleComp Unit (List Bool)) = pure (List.replicate (2 ^ m) true) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [OracleComp.iterate_succ, ih, pure_bind, pow_succ, Nat.mul_two, List.replicate_add]
  have hlength := hbound n Unit (fun _ s => PMF.pure ([], s)) () () (List.replicate (2 ^ n) true)
    (by rw [hiterate, OracleComp.interpret_pure, StateT.run_pure]; simp)
  simp only [encBits, Function.Embedding.coe_refl, id_eq, List.length_replicate, encUnary_apply]
    at hlength
  lia

end ComplexityTests.OracleComposition
