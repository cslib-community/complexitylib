/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.QueryBounds
import Complexity.Computability.Probabilistic.OracleSimulation
import Complexity.Computability.Probabilistic.Oracle.Parameter
import Complexity.Computability.Probabilistic.Presample
import Complexity.Computability.Probabilistic.Memoize
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic
import Complexity.Tactic.PPT

/-! Private coins, adaptive queries, and non-vacuous strict oracle-PPT certificates. -/

namespace ComplexityTests.OraclePPT

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

private noncomputable def randomized :
    ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool × Bool) := do
  let first ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let answer ← ProbOracleComp.query first
  let second ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let repeated ← ProbOracleComp.query first
  return (answer, second, repeated)

-- Private samples do not count as external calls; the adaptive client makes two requests.
private theorem randomized_queryBounds : randomized.IsQueryBounded 2 :=
  ((ProbOracleComp.IsQueryBounded.sample _).bind fun first =>
    (ProbOracleComp.IsQueryBounded.query first).bind fun answer =>
      (ProbOracleComp.IsQueryBounded.sample _).bind fun second =>
        (ProbOracleComp.IsQueryBounded.query first).bind fun repeated =>
          OracleComp.IsCostBounded.pure (answer, second, repeated) 0).mono (by norm_num)

-- The structural budget bounds every logged execution of `randomized` by 2 external calls.
example (State : Type) (oracle : Bool → StateT State PMF Bool)
    (s s' : State) (result : Bool × Bool × Bool)
    (transcript : OracleComp.Transcript (fun _ : Bool => Bool))
    (h : (result, s', transcript) ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript oracle)) randomized).run (s, [])).support) :
    (transcript.map fun _ => 1).sum ≤ 2 :=
  ProbOracleComp.isCostBounded_iff_transcript_cost_le.mp randomized_queryBounds
    State oracle s s' result transcript h

-- With an empty reply type there is no oracle at all, so a bound on logged executions holds
-- vacuously. The structural budget still counts the call.
example : ¬(OracleComp.query (spec := fun _ : Unit => Empty) ()).IsQueryBounded 0 := by
  intro h
  have := (OracleComp.IsCostBounded.liftBind_iff.mp h).1
  norm_num at this

example (State : Type) (oracle : Unit → StateT State PMF Empty) (s : State) : False :=
  (oracle () s).support_nonempty.elim fun x _ => x.1.elim

-- Possible results are read off the program's tree: every reply and every coin can occur.
example (answer second repeated : Bool) :
    (answer, second, repeated) ∈ OracleComp.support randomized := by
  simp [randomized]

-- With an empty reply type a returned value is still possible, although no oracle exists.
example : (1 : ℕ) ∈ OracleComp.support (pure 1 : ProbOracleComp (fun _ : Unit => Empty) ℕ) := by
  simp

-- Forgetting outputs cannot hide external calls; weakening the budget keeps it valid.
example : ((fun _ => ()) <$> randomized).IsQueryBounded 3 :=
  ((OracleComp.isCostBounded_map_iff _ _ _).mpr randomized_queryBounds).mono (by decide)

private noncomputable def duplicatedRequests :
    ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool) := do
  let _ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let first ← ProbOracleComp.query false
  let _ ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let second ← ProbOracleComp.query false
  return (first, second)

private noncomputable def flipOracle (_ : Bool) : StateT Bool PMF Bool :=
  fun state => PMF.pure (state, !state)

-- Private samples do not enter the log; repeated requests retain their two different replies
-- in reverse chronological order, and both state transitions are retained jointly.
private theorem run_duplicatedRequests :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript flipOracle)) duplicatedRequests).run (false, []) =
      PMF.pure ((false, true), false,
        ([⟨false, true⟩, ⟨false, false⟩] : OracleComp.Transcript (fun _ : Bool => Bool))) := by
  simp only [duplicatedRequests, OracleComp.interpret_bind, ProbOracleComp.interpret_sample,
    ProbOracleComp.interpret_query, OracleComp.interpret_pure, StateT.run_bind,
    StateT.run_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  simp [ProbComp.unifFin, OracleComp.interpret_query, StateT.lift,
    OracleComp.withTranscript, flipOracle, StateT.run]

example : ¬duplicatedRequests.IsQueryBounded 1 := by
  intro h
  have hbound := h.length_transcript_le flipOracle (s := false) (s' := false)
    (result := (false, true)) (transcript := [⟨false, true⟩, ⟨false, false⟩])
    (by rw [run_duplicatedRequests]; simp)
  norm_num at hbound

-- Executable list memoization implements both the eager and lazy randomized adaptive table
-- experiments on `randomized`.
example :
    ProbComp.eval (Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (memoize (fun _ : Bool => ProbComp.uniform Bool))) randomized).run []) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
          (Cslib.RandomOracle.answer (fun _ => PMF.uniformOfFintype Bool))) randomized).run
            (fun _ => none)).map Prod.fst := by
  have heager :
      ProbComp.eval (Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (memoize (fun _ : Bool => ProbComp.uniform Bool))) randomized).run []) =
        (do
          let table ← PMF.pi (fun _ : Bool => PMF.uniformOfFintype Bool)
          OracleComp.interpret
            (ProbOracleComp.handler ProbComp.unifOracle (fun q => PMF.pure (table q)))
              randomized) := by
    simpa only [ProbComp.eval_uniform] using
      Cslib.RandomOracle.eval_run_interpret_memoize_prob_eq_eager
        (fun _ : Bool => ProbComp.uniform Bool) randomized
  rw [heager, PMF.pi_uniformOfFintype, Cslib.RandomOracle.uniform_interpret_prob_eq_lazy]

-- Two external calls give at most 18 encoded bits, including pair/list framing; draws are free
-- only with respect to this storage bound, not the separate machine time certificate.
example (result : Bool × Bool × Bool) (cache : List (Bool × Bool))
    (h : (result, cache) ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))) randomized).run []).support) :
    (encList (encPair encBool encBool) cache).length ≤ 18 := by
  exact memoize_cache_size_le encBool encBool _ randomized 2 1 1 randomized_queryBounds
    (ProbOracleComp.QueriesSatisfy.of_forall (by simp) _)
    (by simp only [encBool_apply, List.length_singleton, le_refl, implies_true]) [] cache
    (by simp) result h

-- A duplicate preassigned answer may lie outside the sampler's support and still be returned.
example : (true, [(false, true), (false, false)]) ∈
    (memoize (fun _ : Bool => PMF.pure false) false [(false, true), (false, false)]).support := by
  rw [Cslib.RandomOracle.mem_support_memoize_iff]
  exact Or.inl ⟨by decide, rfl⟩

-- Two equal sampling requests draw independently, even in the presence of an external oracle.
example (State : Type) (oracle : Bool → StateT State PMF Bool) (s : State) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((do
          let first ← ProbOracleComp.sample (ProbComp.uniform Bool)
          let second ← ProbOracleComp.sample (ProbComp.uniform Bool)
          return (first, second)) : ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool))).run s =
      (PMF.uniformOfFintype (Bool × Bool)).map (·, s) := by
  simp only [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
    OracleComp.interpret_pure, StateT.run_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, ProbComp.eval_uniform, PMF.bind_map, Function.comp_def,
    PMF.map_comp, ← PMF.uniformOfFintype_prod, PMF.map_bind]
  rfl

-- Functional deterministic code reuses the existing tactic certificates with external channels.
example : IsOraclePPTOn (Operation := Bool) encBits encBits
    (fun word => pure (word ++ word)) := by fun_prop

/-- Request the empty word once and return at most the first reply bit. -/
private noncomputable def requestHead (_ : List Bool) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), [])

-- The bounded-prefix query primitive certifies the client; no machine is written by hand.
private theorem requestHead_isOraclePPTOn : IsOraclePPTOn encBits encBits requestHead := by
  unfold requestHead
  fun_prop

-- Parameterization retains the concrete client's external call and its entire private-state law.
private theorem requestHead_isOraclePPT : IsOraclePPT encBits (fun _ word => requestHead word) :=
  IsOraclePPTOn.isOraclePPT (IsOraclePPTOn.query_take () (.const []) (.const 1))

-- The resource contracts derive uniform query budgets for `requestHead` on the empty input.
example :
    (∃ c d : ℕ, (requestHead []).IsQueryBounded (c * 2 ^ d) ∧
      (requestHead []).QueriesSatisfy fun request => request.2.length ≤ c * 2 ^ d) ∧
    (∃ c d : ℕ, (requestHead []).IsQueryBounded (c * 1 ^ d) ∧
      (requestHead []).QueriesSatisfy fun request => request.2.length ≤ c * 1 ^ d) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨c, d, h⟩ := requestHead_isOraclePPT.query_bounds
    exact ⟨c, d, by simpa using h 0 []⟩
  · obtain ⟨c, d, h⟩ := requestHead_isOraclePPTOn.query_bounds
    exact ⟨c, d, by simpa using h []⟩

private noncomputable def respond (caller : List Bool) (_ : Unit × List Bool)
    (state : List Bool) : ProbComp (List Bool × List Bool) := do
  let bit ← ProbComp.uniform Bool
  return (bit :: caller, bit :: state)

-- A functional oracle client becomes closed PPT with correlated output and accumulated state.
-- Reply size is unbounded in the caller, and the local invariant survives every sampled bit.
example : IsPPTOn encBits (encPair encBits encBits) (fun word =>
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n)) (respond word))
        (requestHead word)).run word) := by
  apply requestHead_isOraclePPTOn.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
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

-- The same bit appears in the output and the returned state; no marginalization is hidden.
example (word : List Bool) :
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n)) (respond word))
        (requestHead word)).run word) =
      (PMF.uniformOfFintype Bool).map (fun bit => ([bit], bit :: word)) := by
  rw [ProbOracleComp.eval_run_interpret]
  simp only [requestHead, OracleComp.interpret_map, StateT.run_map,
    ProbOracleComp.interpret_query, PMF.monad_map_eq_map]
  change PMF.map _ (ProbComp.eval (respond word ((), []) word)) = _
  simp [respond, PMF.map_comp, Function.comp_def]

-- The API accepts a different caller encoding and preprocessing without any machine annotation.
example : IsPPTOn (encList encBool) (encPair encBits encBits) (fun word =>
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n)) (respond word))
        (requestHead word.reverse)).run word) := by
  apply requestHead_isOraclePPTOn.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (resources := fun caller _ => caller.length + 1)
    (ComputableTidilyInPolyTime.bitsReverse.comp ComputableTidilyInPolyTime.listToBits)
    (by
      have h : IsPPTOn
          (encPair encBits (encPair (encPair (encFinEnum Unit) encBits) encBits))
          (encPair encBits encBits) (fun pair => respond pair.1 pair.2.1 pair.2.2) := by
        unfold respond
        fun_prop
      exact h.preprocess
        ((ComputableInPolyTime.listToBits.comp (by fun_prop)).prod (by fun_prop)))
    (by fun_prop)
    (fun caller state => caller.length ≤ state.length) (fun _ => le_rfl) (by fun_prop)
  intro caller request state hstate result hresult
  simp only [respond, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨bit, _, hresult⟩ := hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp only [encBits_apply, List.length_cons]
  exact ⟨by lia, le_rfl, by lia⟩

-- A fixed caller/request allowance cannot conceal unbounded doubling of retained raw state.
example (allowance : ℕ) : ¬ ∀ state : List Bool,
    (encBits (state ++ state)).length ≤ (encBits state).length + allowance := by
  intro h
  have hlarge := h (List.replicate (allowance + 1) false)
  simp only [encBits_apply, List.length_append, List.length_replicate] at hlarge
  lia

-- An arbitrary certified adaptive client can use a lazy random function with unbounded words.
-- The local cache invariant and one-entry growth bound hide the interpreter's storage arithmetic.
example {β : Type} {output : β ↪ List Bool} {program : List Bool → WordOracleComp Unit β}
    (hprogram : IsOraclePPTOn encBits output program) :
    IsPPTOn encBits (encPair output (encList (encPair encBits encBits))) (fun word =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (fun request => memoize (fun _ => BitString.sampleList word.length) request.2))
            (program word)).run []) := by
  apply hprogram.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (resources := fun caller query => 4 * query.length + 2 * caller.length + 3)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun caller cache => ∀ entry ∈ cache, entry.2.length ≤ caller.length)
    (by simp) (by fun_prop)
  intro caller request cache hcache result hresult
  rw [ProbComp.eval_memoize] at hresult
  obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
    (fun _ => ProbComp.eval (BitString.sampleList caller.length)) request.2 cache caller.length
    hcache (fun value hvalue => by
      rw [BitString.eval_sampleList] at hvalue
      exact (BitString.length_of_mem_support_uniformList hvalue).le) result hresult
  exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by lia), by
    simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩

-- The trace contains one external request despite private draws and an unbounded reply.
example (n : ℕ) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript (fun _ : Unit × List Bool =>
          fun state : ℕ => PMF.pure (List.replicate n true, state + 1))))
            (requestHead [])).run (7, []) =
      PMF.pure ((List.replicate n true).take 1, 8, [⟨((), []), List.replicate n true⟩]) := by
  rw [requestHead, OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query]
  simp [OracleComp.withTranscript, StateT.run]

-- Returning an unrestricted oracle reply cannot satisfy a uniform strict polynomial clock.
example : ¬ IsOraclePPTOn encBits encBits
    (fun _ : List Bool => ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), [])) := by
  intro h
  obtain ⟨c, d, hbound⟩ := h.length_le
  let reply := List.replicate (c + 1) false
  have hlength := hbound [] Unit (fun _ s => PMF.pure (reply, s)) () () reply (by
    simp [StateT.run])
  simp only [encBits, Function.Embedding.coe_refl, id_eq, List.length_nil, Nat.zero_add, one_pow,
    Nat.mul_one, reply, List.length_replicate] at hlength
  lia

-- The saved-list certificate has an actual querying machine witness and arbitrary challenges.
-- Truncation bounds each reply and added ordinary state; the unused list is retained in full.
example : IsPPTOn (encPair encBits (encList encBits))
    (encPair encBits (encPair encBits (encList encBits))) (fun pair =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (OracleComp.withSampleList [] (fun value _ state =>
            pure (value.take pair.1.length, value.take pair.1.length ++ state))))
              (requestHead pair.1)).run (pair.1, pair.2)) := by
  apply requestHead_isOraclePPTOn.run_interpret_withSampleList
    (operationEncoding := encFinEnum Unit) []
    (prepare := fun pair => pair.1) (resources := fun pair _ => pair.1.length)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun _ _ => True) (by simp) (by fun_prop)
  intro caller value request state _ result hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  refine ⟨trivial, List.length_take_le _ _, ?_⟩
  simp only [encBits_apply, List.length_append, List.length_take]
  lia

end ComplexityTests.OraclePPT
