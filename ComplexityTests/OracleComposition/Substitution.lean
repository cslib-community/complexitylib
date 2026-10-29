/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Oracle.Parameter
import Complexity.Computability.Probabilistic.Oracle.Memoize
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-! Open stateful oracle substitution: a two-level adaptive cache client and failure boundaries. -/

namespace ComplexityTests.OracleSubstitution

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-! ### A two-level adaptive cache client -/

/-- Ask for the empty word, then for the first reply's prefix, then for the empty word again,
keeping input-length prefixes of the replies. The third request repeats the first one. -/
private noncomputable def client (n : ℕ) : WordOracleComp Unit (List Bool) := do
  let first ← List.take n <$> ProbOracleComp.query ((), [])
  let second ← List.take n <$> ProbOracleComp.query ((), first)
  let third ← List.take n <$> ProbOracleComp.query ((), [])
  pure (second ++ third)

private theorem client_isOraclePPTOn : IsOraclePPTOn encUnary encBits client := by
  unfold client
  fun_prop

/-- Answer a request from the cache, or forward it to the external oracle and store an
input-length prefix of the reply. -/
private noncomputable def cached (n : ℕ) (request : Unit × List Bool)
    (cache : List (List Bool × List Bool)) :
    WordOracleComp Unit (List Bool × List (List Bool × List Bool)) :=
  memoize (fun key => List.take n <$> ProbOracleComp.query ((), key)) request.2 cache

private theorem run_cached (n : ℕ) (request : Unit × List Bool)
    (cache : List (List Bool × List Bool)) :
    StateT.run (cached n request) cache =
      memoize (fun key => List.take n <$> ProbOracleComp.query (spec := fun _ => List Bool)
        ((), key)) request.2 cache := rfl

-- The cache is certified from the memoization contract and the bounded-prefix query.
private theorem cached_isOraclePPTOn : IsOraclePPTOn
    (encPair encUnary
      (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encBits encBits))))
    (encPair encBits (encList (encPair encBits encBits)))
    (fun pair => cached pair.1 pair.2.1 pair.2.2) := by
  unfold cached
  fun_prop

/-- The client run against the cache, which forwards its misses to the external oracle. -/
private noncomputable def twoLevel (n : ℕ) :
    WordOracleComp Unit (List Bool × List (List Bool × List Bool)) :=
  (OracleComp.interpret
    (ProbOracleComp.handler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (cached n)) (client n)).run []

-- The two-level client is strict oracle PPT, returning its result and the final cache. The local
-- cache invariant and the one-entry growth bound hide the interpreter's storage arithmetic.
private theorem twoLevel_isOraclePPTOn :
    IsOraclePPTOn encUnary (encPair encBits (encList (encPair encBits encBits))) twoLevel := by
  unfold twoLevel
  apply client_isOraclePPTOn.run_interpret_preprocess_open
    (resources := fun n request => 4 * request.length + 2 * n + 3)
    (by fun_prop) cached_isOraclePPTOn (.const [])
    (fun n cache => ∀ entry ∈ cache, entry.2.length ≤ n) (by simp) (by fun_prop)
  intro n request cache hcache result hresult
  obtain ⟨hreply, hcache', hgrowth⟩ := ProbOracleComp.memoize_call_size_le encBits encBits
    _ request.2 cache n hcache (fun value hvalue => by
      obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hvalue
      exact List.length_take_le _ _) hresult
  exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by lia), by
    simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩

/-- An external oracle that answers the first call with ones and every later call with zeros,
counting its calls. -/
private noncomputable def firstOnes (_ : Unit × List Bool) : StateT ℕ PMF (List Bool) :=
  fun calls => PMF.pure (List.replicate 5 (decide (calls = 0)), calls + 1)

private theorem run_firstOnes (request : Unit × List Bool) (calls : ℕ) :
    (firstOnes request).run calls = PMF.pure (List.replicate 5 (decide (calls = 0)), calls + 1) :=
  rfl

-- The repeated request is a cache hit: the external oracle answers exactly two calls, and the
-- third result is the cached first reply rather than a fresh one.
example :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) firstOnes)
        (twoLevel 3)).run 0 =
      PMF.pure (([false, false, false, true, true, true],
        [([true, true, true], [false, false, false]), ([], [true, true, true])]), 2) := by
  simp only [twoLevel, client, OracleComp.interpret_bind, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map]
  simp [run_cached, memoize, run_firstOnes, List.lookup]

/-! ### Failure boundaries -/

/-- An exponential output cannot have a polynomial-length encoding. -/
private theorem not_two_pow_le (c d : ℕ) : ∃ n, c * (n + 1) ^ d < 2 ^ n :=
  (Cslib.PolynomiallyBounded.eventually_lt_two_pow
    (Cslib.PolynomiallyBounded.of_forall_le c d fun _ => le_rfl)).exists

/-- Request the empty word once and keep at most one reply bit. -/
private noncomputable def requestHead (_ : ℕ) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), [])

/-- A handler that copies the complete external reply into its own state for free. -/
private noncomputable def copyReply (_ : ℕ) (request : Unit × List Bool) (_ : List Bool) :
    WordOracleComp Unit (List Bool × List Bool) :=
  (fun reply => ([], reply)) <$> ProbOracleComp.query ((), request.2)

private theorem run_copyReply (n : ℕ) (request : Unit × List Bool) (state : List Bool) :
    StateT.run (copyReply n request) state =
      (fun reply => ([], reply)) <$> ProbOracleComp.query (spec := fun _ => List Bool)
        ((), request.2) := rfl

-- Copying an unbounded external reply into the handler's state is not strict oracle PPT, even
-- though the client keeps one bit; such a handler has no strict oracle PPT certificate.
example : ¬ IsOraclePPTOn encUnary (encPair encBits encBits) (fun n =>
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (copyReply n)) (requestHead n)).run []) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  let reply := List.replicate (c + 1) false
  have hlength := hbound 0 Unit (fun _ s => PMF.pure (reply, s)) () () ([], reply) (by
    simp only [requestHead, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      StateT.run_map, run_copyReply]
    simp [StateT.run])
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, reply,
    List.length_nil] at hlength
  lia

/-- A handler that doubles its state on every call. Each call is efficient. -/
private noncomputable def double (_ : ℕ) (_ : Unit × List Bool) (state : List Bool) :
    WordOracleComp Unit (List Bool × List Bool) :=
  pure ([], state ++ state)

private theorem run_double (n : ℕ) (request : Unit × List Bool) (state : List Bool) :
    StateT.run (double n request) state = pure ([], state ++ state) := rfl

-- Each doubling call is strict oracle PPT in its caller, request and state.
example : IsOraclePPTOn
    (encPair encUnary (encPair (encPair (encFinEnum Unit) encBits) encBits))
    (encPair encBits encBits) (fun pair => double pair.1 pair.2.1 pair.2.2) := by
  unfold double
  fun_prop

/-- Repeat `requestHead` once per input unit. -/
private noncomputable def repeatHead (n : ℕ) : WordOracleComp Unit (List Bool) :=
  OracleComp.iterate n (fun _ => List.take 1 <$> ProbOracleComp.query ((), [])) []

-- The repeated client is strict oracle PPT.
example : IsOraclePPTOn encUnary encBits repeatHead := by
  refine IsOraclePPTOn.iterate_of_bounded_growth (count := fun n => n) (initial := fun _ => [])
    (by fun_prop) (.const []) (by fun_prop) (growth := 1) ?_
  intro _ next hnext
  obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simp only [encBits, Function.Embedding.coe_refl, id_eq]
  exact (List.length_take_le _ _).trans (Nat.le_add_left _ _)

-- Substituting the doubling handler into the repeated client is not strict oracle PPT: no
-- additive allowance bounds its state growth.
example : ¬ IsOraclePPTOn encUnary (encPair encBits encBits) (fun n =>
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (double n)) (repeatHead n)).run [true]) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  obtain ⟨n, hn⟩ := not_two_pow_le c d
  have hiterate (m : ℕ) (word : List Bool) : (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (double n)) (OracleComp.iterate m
          (fun _ => List.take 1 <$> ProbOracleComp.query ((), [])) word)).run [true] =
      pure (if m = 0 then word else [], List.replicate (2 ^ m) true) := by
    induction m generalizing word with
    | zero => simp
    | succ m ih =>
      rw [OracleComp.iterate_succ, OracleComp.interpret_bind, StateT.run_bind, ih, pure_bind]
      simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query, StateT.run_map,
        run_double, map_pure, pow_succ, Nat.mul_two, List.replicate_add]
      simp
  have hlength := hbound n Unit (fun _ s => PMF.pure ([], s)) () ()
    (if n = 0 then [] else [], List.replicate (2 ^ n) true) (by
      rw [repeatHead, hiterate]
      simp)
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hlength
  lia

end ComplexityTests.OracleSubstitution
