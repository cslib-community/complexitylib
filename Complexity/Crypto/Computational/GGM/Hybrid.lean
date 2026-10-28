/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GGM.Evaluation
public import Complexity.Crypto.Computational.PseudorandomFunction.RandomOracle
import Complexity.Computability.Probabilistic.Memoize
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# The GGM prefix hybrids

At level `depth`, sample an independent label for each newly queried prefix of that length.
Remember it for later queries with the same prefix, and evaluate the remaining suffix using the
generator. Malformed queries receive the empty word, as in the PRF games.

The cache is an ordinary list. One call preserves a label-width invariant and adds at most one
entry. The shared stateful interpreter certifies the entire adaptive game, including copying,
sampling, replies and growing storage. This module identifies the endpoint games; adjacent-hybrid
security requires a further reduction.

## Main definitions

* `Cslib.Crypto.GGM.frontierOracle`: memoized prefix labels followed by tree evaluation.
* `Cslib.Crypto.GGM.hybridGame`: the complete adaptive prefix experiment.

## Main results

* `Cslib.Crypto.GGM.frontierOracle_bounds`: bounds label widths and the cache-encoding growth
  per query.
* `Cslib.Crypto.GGM.hybridGame_zero`, `.hybridGame_self`: exact real and ideal endpoints.
* `Cslib.Crypto.GGM.isPPTOn_hybridGame`: uniform strict PPT for the complete experiment.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3, the algorithms `A_i` in the proof of Theorem 3.

Adapts Crypto/Computational/GGM/Hybrid.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability Turing.MultiTapeTM

/-- A finite collection of queried prefixes and their sampled labels. -/
abbrev Cache := List (List Bool × List Bool)

/-- Charge every stored prefix and label, including list and pair delimiters. -/
def cacheEncoding : Cache ↪ List Bool := encList (encPair encBits encBits)

/-- Answer from a cached random label at the chosen level, followed by ordinary tree evaluation. -/
noncomputable def frontierOracle (generator : List Bool → List Bool) (n depth : ℕ)
    (query : List Bool) : StateT Cache ProbComp (List Bool) := fun cache =>
  if query.length = n then do
    let (seed, cache') ← memoize (fun _ : List Bool => BitString.sampleList n)
      (query.take depth) cache
    return (eval generator seed (query.drop depth), cache')
  else pure ([], cache)

/-- The adaptive hybrid game starts with an empty prefix cache. -/
noncomputable def hybridGame (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth : ℕ) : ProbComp Bool :=
  Prod.fst <$> (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request => frontierOracle generator n depth request.2)) (adversary n [])).run []

/-- At level zero, all valid queries share one root label. Sampling that label on demand agrees
with choosing the key at the start of the real PRF game, even if there are no valid queries. -/
theorem hybridGame_zero (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n 0) =
      ProbComp.eval (prfRealGame (eval generator) adversary n) := by
  let root := fun cache : Cache => (cache.lookup []).elim (BitString.uniformList n) PMF.pure
  have hstep : ∀ query cache,
      (ProbComp.eval (frontierOracle generator n 0 query cache)).bind
        (fun (answer, cache') => (root cache').map (answer, ·)) =
      (root cache).bind (fun seed =>
        (PMF.pure (prfOracle (eval generator) n seed query)).map (·, seed)) := by
    intro query cache
    by_cases hquery : query.length = n <;> cases hcache : cache.lookup [] <;>
      simp [frontierOracle, memoize, root, hquery, hcache, BitString.eval_sampleList,
        prfOracle, PMF.map, Function.comp_def]
  have h := ProbOracleComp.run_interpret_simulation
    (fun request cache => ProbComp.eval (frontierOracle generator n 0 request.2 cache))
    (fun request seed => (PMF.pure (prfOracle (eval generator) n seed request.2)).map (·, seed))
    root (fun request => hstep request.2) (adversary n []) []
  simp only [ProbOracleComp.run_interpret_readOnly] at h
  have houtput := congrArg (PMF.map Prod.fst) h
  simpa [hybridGame, prfRealGame, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.eval_interpret, BitString.eval_sampleList, root, PMF.map,
    Function.comp_def] using houtput

/-- The final level caches full query answers directly. There is no suffix left to evaluate. -/
theorem frontierOracle_self (generator : List Bool → List Bool) (n : ℕ) :
    frontierOracle generator n n = cachedRandomFunctionOracle n := by
  funext query cache
  by_cases h : query.length = n
  · simp [frontierOracle, cachedRandomFunctionOracle, ← h]
  · simp [frontierOracle, cachedRandomFunctionOracle, h]

/-- At the final level, the prefix hybrid is exactly the ideal PRF game. -/
theorem hybridGame_self (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n n) =
      ProbComp.eval (prfIdealGame adversary n) := by
  simp only [hybridGame, frontierOracle_self, prfIdealGame_eq_cached]

/-- Each call preserves label widths and adds at most one encoded entry. Key lengths and duplicate
cache keys are unrestricted; only cached label widths are constrained. -/
theorem frontierOracle_bounds (generator : List Bool → List Bool) (n depth : ℕ)
    (query : List Bool) (cache : Cache) (hcache : ∀ entry ∈ cache, entry.2.length ≤ n)
    (result : List Bool × Cache)
    (hresult : result ∈ (ProbComp.eval (frontierOracle generator n depth query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (cacheEncoding result.2).length ≤
        (cacheEncoding cache).length + 4 * query.length + 2 * n + 3 := by
  by_cases hquery : query.length = n
  · simp only [frontierOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨seed, cache'⟩, hseed, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    have hsample : (seed, cache') ∈
        (memoize (fun _ : List Bool => BitString.uniformList n)
          (query.take depth) cache).support := by
      simpa only [ProbComp.eval_memoize, BitString.eval_sampleList] using hseed
    obtain ⟨hwidth, hcache', hsize⟩ := memoize_call_size_le encBits encBits
      (fun _ : List Bool => BitString.uniformList n) (query.take depth) cache n hcache
      (fun _ hvalue => (BitString.length_of_mem_support_uniformList hvalue).le)
      (seed, cache') hsample
    refine ⟨hcache', (length_eval_le _ _ _).trans hwidth, ?_⟩
    change (cacheEncoding cache').length ≤ (cacheEncoding cache).length +
      4 * (query.take depth).length + 2 * n + 3 at hsize
    simp only [List.length_take] at hsize
    dsimp
    lia
  · simp only [frontierOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨hcache, by simp, by dsimp; lia⟩

/-- Certify a prefix call written with computed parameters, query and full cache. -/
@[fun_prop]
theorem isPPTOn_frontierOracle {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {parameter depth : α → ℕ}
    {query : α → List Bool} {cache : α → Cache}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hparameter : ComputableInPolyTime parameter input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input cacheEncoding) :
    IsPPTOn input (encPair encBits cacheEncoding)
      (fun a => frontierOracle generator (parameter a) (depth a) (query a) (cache a)) := by
  have hgenerator := hgenerator.tidy
  have hparameter := hparameter.tidy
  have hdepth := hdepth.tidy
  have hquery := hquery.tidy
  have hcache := hcache.tidy
  have heval := (computableInPolyTime_eval (.of_tidy hgenerator)).tidy
  unfold frontierOracle cacheEncoding
  fun_prop

/-- A uniform adversary's complete adaptive prefix game is strict PPT, uniformly over the chosen
level. The local invariant accounts for every reply and all added encoded storage. -/
theorem isPPTOn_hybridGame {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary encUnary) encBool
      (fun pair => hybridGame generator adversary pair.1 pair.2) := by
  have hgenerator := hgenerator.tidy
  have hrun : IsPPTOn (encPair encUnary encUnary) (encPair encBool cacheEncoding)
      (fun pair : ℕ × ℕ => (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => frontierOracle generator pair.1 pair.2 request.2))
            (adversary pair.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
      (prepare := fun pair : ℕ × ℕ => (pair.1, []))
      (resources := fun pair query => 4 * query.length + 2 * pair.1 + 3)
      (by fun_prop) (by fun_prop) (by fun_prop)
      (fun pair cache => ∀ entry ∈ cache, entry.2.length ≤ pair.1) (by simp) (by fun_prop)
    intro pair request cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ :=
      frontierOracle_bounds generator pair.1 pair.2 request.2 cache hcache result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (ComputableInPolyTime.fst _ _)

end Cslib.Crypto.GGM
