/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Computability.Probabilistic.Parameter
import Complexity.Computability.Probabilistic.Memoize
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# An executable finite-list oracle for the PRF ideal game

Valid queries are memoized as ordinary words. Malformed queries receive the empty word and retain
the cache. Injective key representations and the shared eager/lazy theorem identify this program
with the ideal PRF game for every randomized adaptive adversary.

## Main definitions

* `Cslib.Crypto.cachedRandomFunctionOracle`: a list cache with fair-bit sampling on misses.

## Main results

* `Cslib.Crypto.prfIdealGame_eq_cached`: exact equality of the eager and cached experiments.
* `Cslib.Crypto.isPPT_prfIdealGame`: a strict PPT realization for every oracle-PPT adversary.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapts Crypto/Computational/PseudorandomFunction/RandomOracle.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Memoize sampled words on valid queries, rejecting malformed words without altering the cache. -/
noncomputable def cachedRandomFunctionOracle (n : ℕ) (query : List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) := fun cache =>
  if query.length = n then memoize (fun _ => BitString.sampleList n) query cache
  else pure ([], cache)

open Turing.MultiTapeTM in
/-- Each cached call charges the parameter, query and complete input and output cache. -/
@[fun_prop]
theorem isPPTOn_cachedRandomFunctionOracle {α : Type} {input : α ↪ List Bool}
    {parameter : α → ℕ} {query : α → List Bool}
    {cache : α → List (List Bool × List Bool)}
    (hparameter : Turing.MultiTapeTM.ComputableInPolyTime parameter input encUnary)
    (hquery : Turing.MultiTapeTM.ComputableInPolyTime query input encBits)
    (hcache : Turing.MultiTapeTM.ComputableInPolyTime cache input (encList (encPair encBits
      encBits))) :
    IsPPTOn input (encPair encBits (encList (encPair encBits encBits)))
      (fun a => cachedRandomFunctionOracle (parameter a) (query a) (cache a)) := by
  have hparameter := hparameter.tidy
  have hquery := hquery.tidy
  have hcache := hcache.tidy
  unfold cachedRandomFunctionOracle
  fun_prop

/-- An executable list cache realizes the ideal experiment, preserving repeated-query
consistency and independent private randomness under arbitrary adaptive interaction. -/
theorem prfIdealGame_eq_cached (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame adversary n) =
      ProbComp.eval (Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => cachedRandomFunctionOracle n request.2)) (adversary n [])).run []) := by
  let adapter := fun query : List Bool => if query.length = n then
    (ProbOracleComp.query (BitString.ofList n query) :
      ProbOracleComp (fun _ : BitString n => List Bool) (List Bool))
    else pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map
    (⟨List.ofFn, List.ofFn_injective⟩ : BitString n ↪ List Bool) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => BitString.uniformList n)
    (fun _ => rfl) (OracleComp.interpret
      (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => adapter request.2)) (adversary n []))
  have hstep (query : List Bool) : OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key => memoize (fun _ => BitString.uniformList n) (List.ofFn key)))
          (adapter query) =
        fun cache => ProbComp.eval (cachedRandomFunctionOracle n query cache) := by
    funext cache
    by_cases hquery : query.length = n
    · simp [adapter, cachedRandomFunctionOracle, hquery, BitString.ofFn_ofList hquery,
        ProbComp.eval_memoize, BitString.eval_sampleList]
    · simp only [adapter, cachedRandomFunctionOracle, hquery, ↓reduceIte,
        OracleComp.interpret_pure, ProbComp.eval_pure]
      rfl
  have heager (table : BitString n → BitString n) (query : List Bool) : OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
        (adapter query) = PMF.pure (randomFunctionOracle n table query) := by
    by_cases hquery : query.length = n <;> simp [adapter, randomFunctionOracle, hquery]
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  simpa only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, PMF.pi_uniformOfFintype,
    OracleComp.interpret_interpret, ProbOracleComp.interpret_handler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query,
    Function.Embedding.coeFn_mk, hstep, heager, PMF.monad_bind_eq_bind] using h

open Turing.MultiTapeTM in
/-- The ideal experiment has a strict PPT realization through its lazy cache. This does not
construct the exponentially large eager table; the entire adaptive interaction is certified. -/
theorem isPPT_prfIdealGame {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPT encBool (fun n _ => prfIdealGame adversary n) := by
  have hrun : IsPPTOn (encPair encUnary encBits)
      (encPair encBool (encList (encPair encBits encBits))) (fun pair : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (fun request => cachedRandomFunctionOracle pair.1 request.2))
              (adversary pair.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
      (prepare := fun pair : ℕ × List Bool => (pair.1, []))
      (resources := fun pair query => 4 * query.length + 2 * pair.1 + 3)
      (by fun_prop) (by fun_prop) (by fun_prop)
      (fun pair cache => ∀ entry ∈ cache, entry.2.length ≤ pair.1) (by simp) (by fun_prop)
    intro pair request cache hcache result hresult
    by_cases hquery : request.2.length = pair.1
    · simp only [cachedRandomFunctionOracle, hquery, ↓reduceIte] at hresult
      rw [ProbComp.eval_memoize] at hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (BitString.sampleList pair.1)) request.2 cache pair.1
        hcache (fun value hvalue => by
          rw [BitString.eval_sampleList] at hvalue
          exact (BitString.length_of_mem_support_uniformList hvalue).le) result hresult
      exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by lia), by
        simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩
    · simp only [cachedRandomFunctionOracle, hquery, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨hcache, by simp, by lia⟩
  exact ((hrun.map (ComputableInPolyTime.fst _ _)).isPPT).congr
    (fun n _ => (prfIdealGame_eq_cached adversary n).symm)

end Cslib.Crypto
