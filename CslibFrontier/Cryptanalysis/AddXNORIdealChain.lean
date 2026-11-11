/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutationFamily
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Crypto.Game
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# The independent-permutation ideal-chain experiment

[WangLvShenZhang2027], Section 6.1 (PDF pp. 24–25), replaces the arithmetic steps
by independent permutations indexed by the layer and operator bit. `plantedSearch` and
`decision` are the actual eager experiments, not the manuscript's problematic lazy `Real`.
`plantedSearch_eq_lazy` realizes planting, adaptive queries and final verification using
valid lazy permutation tables; it proves their exact output law without a simulation premise.
Planting is performed before the adversary starts, and verification afterwards. Their oracle
calls are experiment-internal, not charged as adversary calls.

This module does not prove the security inequalities of Theorem 8 or Corollary 4. In particular,
preinstalling the planted path does not make its hidden tables independent of the public target.
The hidden-cut route in `AddXNORIdealCoupling` supplies a valid stopped coupling; its
fresh-ledger collision/covering estimates are in `AddXNORIdealCollisions`, but the
bridge from its analysis event to the stopped game remains open. The source's
Lemma 10 literal frontier-only simulator can violate table injectivity after a collision;
the search client records a checked example. No equivalence to that simulator is asserted.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Label`, `Spec`, `Operators`: oracle labels and words.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.walk`, `chain`: queried and deterministic evaluation.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.plantedSearch`, `decision`: the source experiments.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.plantedProgram`: actual lazy planting/search/checking.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.walk_correct`: exact evaluation and query count.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.plantedProgram_queryBound`: planting and verification
  contribute at most two chain walks, separately from the adversary budget.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.plantedSearch_eq_lazy`: eager/lazy planted search law.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.decision_eq_lazy`: eager/lazy planted decision law.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain

open Probability OracleComp Crypto
open RandomPermutation (PermQuery)

/-- Zero-based layer and operator bit: one independent permutation for every pair. -/
abbrev Label (q : ℕ) := Fin q × Bool
/-- The source's complete operator string. -/
abbrev Operators (q : ℕ) := Fin q → Bool
/-- Every layer/bit permutation supports both forward and inverse queries. -/
abbrev Spec (q : ℕ) (Word : Type) := RandomPermutation.Family.Spec (Label q) Word

/-- Query a path in its listed layer order. -/
@[expose] def walk {Index Word : Type} :
    List Index → Word → OracleComp (RandomPermutation.Family.Spec Index Word) Word
  | [], seed => pure seed
  | i :: rest, seed => do
    let next ← OracleComp.query (i, PermQuery.forward seed)
    walk rest next

/-- Evaluate the same path using actual permutations. -/
@[expose] def evaluate {Index Word : Type} (perms : Index → Equiv.Perm Word) :
    List Index → Word → Word
  | [], seed => seed
  | i :: rest, seed => evaluate perms rest (perms i seed)

/-- A walk makes one query per edge and has exactly the deterministic path value. -/
theorem walk_correct {Index Word : Type} (perms : Index → Equiv.Perm Word)
    (path : List Index) (seed : Word) :
    IsQueryBounded (walk path seed) path.length ∧
      interpret (fun query => PMF.pure (RandomPermutation.Family.eval perms query))
        (walk path seed) = PMF.pure (evaluate perms path seed) := by
  induction path generalizing seed with
  | nil => exact ⟨.pure seed 0, rfl⟩
  | cons i rest ih =>
    constructor
    · exact .liftBind _ _ _ fun next => (ih next).1
    · simp only [walk, interpret_bind, interpret_query, PMF.monad_bind_eq_bind,
        PMF.pure_bind, RandomPermutation.Family.eval, RandomPermutation.evalPerm_forward]
      exact (ih _).2

/-- The source's $\Pi_x(s)$ with all layers in increasing order. -/
@[expose] def chain {q : ℕ} {Word : Type} (perms : Label q → Equiv.Perm Word)
    (bits : Operators q) (seed : Word) : Word :=
  evaluate perms (List.ofFn fun i => (i, bits i)) seed

variable {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word] [Nonempty Word]

/-- Plant using real oracle calls, run the adversary, and verify using the same tables.
The adversary's budget excludes the two internal walks. -/
@[expose] def plantedProgram (seed : Word) (bits : Operators q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    ProbOracleComp (Spec q Word) Bool := do
  let target ← liftRight (walk (List.ofFn fun i => (i, bits i)) seed)
  let candidate ← adversary seed target
  let endpoint ← liftRight (walk (List.ofFn fun i => (i, candidate i)) seed)
  return decide (endpoint = target)

omit [Fintype Word] [DecidableEq Word] [Nonempty Word] in
/-- A forward path lifted into a private-coin program makes one external call per label. -/
theorem walk_queryBound (path : List (Label q)) (seed : Word) :
    ProbOracleComp.IsQueryBounded
      (liftRight (spec₁ := unifSpec) (walk path seed)) path.length := by
  induction path generalizing seed with
  | nil => exact .pure seed 0
  | cons i rest ih =>
    change IsCostBounded _
      (.liftBind (.inr (i, PermQuery.forward seed)) fun next => liftRight (walk rest next))
      (rest.length + 1)
    exact .liftBind _ _ _ ih

omit [Fintype Word] [Nonempty Word] in
/-- The two experiment-internal walks contribute at most `2*q` calls in addition to the
adversary budget, whatever its private samples or the oracle answers. -/
theorem plantedProgram_queryBound (seed : Word) (bits : Operators q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) (T : ℕ)
    (hT : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T) :
    ProbOracleComp.IsQueryBounded (plantedProgram seed bits adversary) (T + 2 * q) := by
  have hwalk (bits : Operators q) := walk_queryBound (List.ofFn fun i => (i, bits i)) seed
  simp only [List.length_ofFn] at hwalk
  simpa only [plantedProgram, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul,
    Nat.add_zero] using
    (hwalk bits).bind fun target => (hT seed target).bind fun candidate =>
      (hwalk candidate).bind fun endpoint => IsCostBounded.pure (decide (endpoint = target)) 0

/-- Search in the actual independent-permutation planted experiment (source Section 6.1).
The finite family is sampled uniformly, so its coordinates are independent uniforms. -/
@[expose] noncomputable def plantedSearch
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) : Game := do
  let seed ← PMF.uniformOfFintype Word
  let bits ← PMF.uniformOfFintype (Operators q)
  let perms ← PMF.uniformOfFintype (Label q → Equiv.Perm Word)
  let target := chain perms bits seed
  let candidate ← interpret (RandomPermutation.Family.probEval perms)
    (adversary seed target)
  return decide (chain perms candidate seed = target)

omit [Fintype Word] [Nonempty Word] in
/-- Planting/search/verification against eager permutations is the same oracle program. -/
theorem interpret_plantedProgram (seed : Word) (bits : Operators q)
    (perms : Label q → Equiv.Perm Word)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    interpret (RandomPermutation.Family.probEval perms)
      (plantedProgram seed bits adversary) = do
        let candidate ← interpret
          (RandomPermutation.Family.probEval perms)
          (adversary seed (chain perms bits seed))
        return decide (chain perms candidate seed = chain perms bits seed) := by
  simp only [plantedProgram, interpret_bind, interpret_pure, RandomPermutation.Family.probEval,
    interpret_sumHandler_liftRight,
    (walk_correct perms _ _).2, pmf_norm, chain]
  rfl

/-- The lazy experiment is an exact realization of the planted game. All stored entries
remain valid partial bijections, including on collision traces. No forced invalid entry is used. -/
theorem plantedSearch_eq_lazy
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    plantedSearch adversary = (do
      let seed ← PMF.uniformOfFintype Word
      let bits ← PMF.uniformOfFintype (Operators q)
      ((interpret RandomPermutation.Family.probAnswer (plantedProgram seed bits adversary)).run
        (fun _ => [])).map Prod.fst) := by
  simp only [plantedSearch, PMF.monad_bind_eq_bind]
  congr 1 with seed : 1
  congr 1 with bits : 1
  rw [← RandomPermutation.Family.uniform_prob_interpret_eq_lazy]
  congr 1 with perms : 1
  exact (interpret_plantedProgram seed bits perms adversary).symm

/-- A decision experiment's actual oracle program. In the planted branch it first computes
the target; in the independent branch the externally sampled target is used directly. -/
@[expose] def decisionProgram (planted : Bool) (seed independent : Word) (bits : Operators q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) :
    ProbOracleComp (Spec q Word) Bool := do
  let target ← if planted then
    liftRight (walk (List.ofFn fun i => (i, bits i)) seed) else pure independent
  adversary seed target

omit [Fintype Word] [DecidableEq Word] [Nonempty Word] in
/-- Only the planted decision branch adds the internal `q`-edge setup walk; neither branch
performs search verification. The external adversary still has its original `T`-query budget. -/
theorem decisionProgram_queryBound (planted : Bool) (seed independent : Word)
    (bits : Operators q) (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool)
    (T : ℕ) (hT : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T) :
    ProbOracleComp.IsQueryBounded (decisionProgram planted seed independent bits adversary)
      (T + if planted then q else 0) := by
  cases planted with
  | false => simpa [decisionProgram] using hT seed independent
  | true =>
    have hw := walk_queryBound (List.ofFn fun i => (i, bits i)) seed
    simp only [List.length_ofFn] at hw
    simpa only [decisionProgram, Bool.true_eq, ↓reduceIte, Nat.add_comm] using
      hw.bind fun target => hT seed target

/-- The two conditional decision laws from source Section 6.1. `true` plants a chain;
`false` samples an independent target. The returned bit is the adversary's guess. -/
@[expose] noncomputable def decision (planted : Bool)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) : Game := do
  let seed ← PMF.uniformOfFintype Word
  let independent ← PMF.uniformOfFintype Word
  let bits ← PMF.uniformOfFintype (Operators q)
  let perms ← PMF.uniformOfFintype (Label q → Equiv.Perm Word)
  interpret (RandomPermutation.Family.probEval perms)
    (adversary seed (if planted then chain perms bits seed else independent))

/-- Both branches of the real decision experiment admit exact valid-table lazy execution. -/
theorem decision_eq_lazy (planted : Bool)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) :
    decision planted adversary = (do
      let seed ← PMF.uniformOfFintype Word
      let independent ← PMF.uniformOfFintype Word
      let bits ← PMF.uniformOfFintype (Operators q)
      ((interpret RandomPermutation.Family.probAnswer
        (decisionProgram planted seed independent bits adversary)).run (fun _ => [])).map
          Prod.fst) := by
  simp only [decision, PMF.monad_bind_eq_bind]
  congr 1 with seed : 1
  congr 1 with independent : 1
  congr 1 with bits : 1
  rw [← RandomPermutation.Family.uniform_prob_interpret_eq_lazy]
  congr 1 with perms : 1
  cases planted <;>
    simp [decisionProgram, RandomPermutation.Family.probEval,
      interpret_sumHandler_liftRight, (walk_correct perms _ _).2, chain]

end Cslib.Cryptanalysis.AddXNOR.IdealChain
