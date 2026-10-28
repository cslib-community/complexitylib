/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GGM.Hybrid
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Probabilistic.Memoize
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Cached expansions between adjacent GGM levels

Cache one expansion per queried parent prefix. Generator outputs reproduce the earlier prefix
hybrid; independent random child labels give the next hybrid. Only the first two labels of an
expansion are retained. These identities hold for arbitrary adaptive randomized adversaries.

The complete expansion game has a uniform strict PPT certificate when its sampler does. A further
security reduction must replace these repeated sampler calls with a single PRG challenge.

## Main definitions

* `Cslib.Crypto.GGM.expansionOracle`: memoized sampled expansions and child selection.
* `Cslib.Crypto.GGM.expansionGame`: the complete adaptive expansion experiment.

## Main results

* `Cslib.Crypto.GGM.expansionGame_generated`, `.expansionGame_uniform`: adjacent hybrid laws.
* `Cslib.Crypto.GGM.isPPTOn_expansionGame`: strict PPT for the entire captured-input game.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3, the simulation used in the proof of Theorem 3.

Adapts Crypto/Computational/GGM/Expansion.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability Turing.MultiTapeTM

/-- Cache a sampled expansion at each parent prefix and follow its selected child. -/
def expansionOracle (generator : List Bool → List Bool)
    (sample : ProbComp (List Bool)) (n depth : ℕ) (query : List Bool) :
    StateT Cache ProbComp (List Bool) := fun cache =>
  if query.length = n then do
    let (expansion, cache') ← memoize (fun _ : List Bool => List.take (2 * n) <$> sample)
      (query.take depth) cache
    return (eval generator (selectChild n expansion (query[depth]?.getD false))
      (query.drop (depth + 1)), cache')
  else pure ([], cache)

/-- Run the adversary using sampled, cached expansions at the selected level. -/
def expansionGame (generator : List Bool → List Bool)
    (sample : ProbComp (List Bool)) (adversary : OracleDistinguisher) (n depth : ℕ) :
    ProbComp Bool :=
  Prod.fst <$> (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request => expansionOracle generator sample n depth request.2))
        (adversary n [])).run []

/-- A cached expansion uses at most two labels of storage. The sampled word may have any length;
truncation bounds the stored value and selected child even on malformed challenges. -/
theorem expansionOracle_bounds (generator : List Bool → List Bool) (sample : ProbComp (List Bool))
    (n depth : ℕ) (query : List Bool) (cache : Cache)
    (hcache : ∀ entry ∈ cache, entry.2.length ≤ 2 * n) (result : List Bool × Cache)
    (hresult : result ∈ (ProbComp.eval
      (expansionOracle generator sample n depth query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ 2 * n) ∧ result.1.length ≤ n ∧
      (cacheEncoding result.2).length ≤
        (cacheEncoding cache).length + 4 * query.length + 4 * n + 3 := by
  by_cases hquery : query.length = n
  · simp only [expansionOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨expansion, next⟩, hsample, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    have hvalues : ∀ value ∈ ((ProbComp.eval sample).map (List.take (2 * n))).support,
        value.length ≤ 2 * n := by
      intro value hvalue
      obtain ⟨word, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalue
      simp
    have hsample' : (expansion, next) ∈ (memoize
        (fun _ : List Bool => (ProbComp.eval sample).map (List.take (2 * n)))
        (query.take depth) cache).support := by
      simpa only [ProbComp.eval_memoize, ProbComp.eval_map] using hsample
    obtain ⟨_, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
      (fun _ : List Bool => (ProbComp.eval sample).map (List.take (2 * n)))
      (query.take depth) cache (2 * n) hcache hvalues (expansion, next) hsample'
    refine ⟨hcache', (length_eval_le ..).trans (length_selectChild_le ..), ?_⟩
    change (cacheEncoding next).length ≤ (cacheEncoding cache).length +
      4 * (query.take depth).length + 2 * (2 * n) + 3 at hgrowth
    simp only [List.length_take] at hgrowth
    dsimp
    lia
  · simp only [expansionOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨hcache, by simp, by dsimp; lia⟩

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Expansion handlers compose a certified sampler with ordinary cache and tree code. Every
argument may depend on the caller's captured input, including the entire initial cache. -/
@[fun_prop]
theorem isPPTOn_expansionOracle {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {sample : α → ProbComp (List Bool)}
    {width depth : α → ℕ} {query : α → List Bool} {cache : α → Cache}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hsample : IsPPTOn input encBits sample)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input cacheEncoding) :
    IsPPTOn input (encPair encBits cacheEncoding) (fun a =>
      expansionOracle generator (sample a) (width a) (depth a) (query a) (cache a)) := by
  have hgenerator := hgenerator.tidy
  have hwidth := hwidth.tidy
  have hdepth := hdepth.tidy
  have hquery := hquery.tidy
  have hcache := hcache.tidy
  have heval := (computableInPolyTime_eval (.of_tidy hgenerator)).tidy
  unfold expansionOracle cacheEncoding
  fun_prop

/-- A complete adaptive expansion game is strict PPT, uniformly in the captured parameters and
sampler. The public local contracts account for the clock, replies and full cache growth. -/
theorem isPPTOn_expansionGame {Caller : Type} {input : Caller ↪ List Bool}
    {generator : List Bool → List Bool} {sample : Caller → ProbComp (List Bool)}
    {width depth : Caller → ℕ}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hsample : IsPPTOn input encBits sample)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn input encBool
      (fun a => expansionGame generator (sample a) adversary (width a) (depth a)) := by
  have hgenerator := hgenerator.tidy
  have hwidth := hwidth.tidy
  have hdepth := hdepth.tidy
  have hrun : IsPPTOn input (encPair encBool cacheEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => expansionOracle generator (sample a) (width a) (depth a) request.2))
            (adversary (width a) [])).run []) := by
    apply hadversary.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
      (prepare := fun a => (width a, []))
      (resources := fun a query => 4 * query.length + 4 * width a + 3)
      (by fun_prop) (by fun_prop) (by fun_prop)
      (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ 2 * width a) (by simp) (by fun_prop)
    intro a request cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ :=
      expansionOracle_bounds generator (sample a) (width a) (depth a) request.2 cache hcache
        result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (ComputableInPolyTime.fst _ _)

private def expandCache (generator : List Bool → List Bool) (n : ℕ) (cache : Cache) : Cache :=
  cache.map (fun entry => (entry.1, (generator entry.2).take (2 * n)))

private theorem frontierOracle_preserves_labels (generator : List Bool → List Bool) (n depth : ℕ)
    (query : List Bool) (cache : Cache) (hcache : ∀ entry ∈ cache, entry.2.length = n)
    (answer : List Bool) (cache' : Cache)
    (hresult : (answer, cache') ∈
      (ProbComp.eval (frontierOracle generator n depth query cache)).support) :
    ∀ entry ∈ cache', entry.2.length = n := by
  by_cases hquery : query.length = n
  · simp only [frontierOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨seed, next⟩, hseed, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hresult
    rw [hresult.2]
    have hsample : (seed, next) ∈
        (memoize (fun _ : List Bool => BitString.uniformList n)
          (query.take depth) cache).support := by
      simpa only [ProbComp.eval_memoize, BitString.eval_sampleList] using hseed
    exact (RandomOracle.memoize_invariant (fun _ : List Bool => BitString.uniformList n)
      (fun _ seed => seed.length = n) (query.take depth) cache hcache
      (fun _ h => BitString.length_of_mem_support_uniformList h) (seed, next) hsample).2
  · simp only [frontierOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hresult
    simpa only [hresult.2] using hcache

private theorem expansionOracle_generated_step (generator : List Bool → List Bool) (n depth : ℕ)
    (hdepth : depth < n) (query : List Bool) (cache : Cache)
    (hcache : ∀ entry ∈ cache, entry.2.length = n) :
    (ProbComp.eval (frontierOracle generator n depth query cache)).map
      (fun result => (result.1, expandCache generator n result.2)) =
      ProbComp.eval (expansionOracle generator (generator <$> BitString.sampleList n) n depth
        query (expandCache generator n cache)) := by
  by_cases hquery : query.length = n
  · have hmap := memoize_map (m := PMF) (Function.Embedding.refl (List Bool))
      (fun seed => (generator seed).take (2 * n)) (fun _ : List Bool => BitString.uniformList n)
      (fun _ : List Bool =>
        (BitString.uniformList n).map (fun seed => (generator seed).take (2 * n)))
      (fun _ => rfl) (query.take depth) cache
    simp only [PMF.monad_map_eq_map, Function.Embedding.refl_apply] at hmap
    simp only [frontierOracle, expansionOracle, hquery, ite_true, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_memoize, ProbComp.eval_map,
      BitString.eval_sampleList, PMF.map_comp, Function.comp_def]
    rw [show expandCache generator n cache =
      cache.map (fun entry => (entry.1, (generator entry.2).take (2 * n))) from rfl, ← hmap]
    simp only [PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]
    apply PMF.bind_congr_on_support
    rintro ⟨seed, next⟩ hseed
    have hlength := (RandomOracle.memoize_invariant (fun _ : List Bool => BitString.uniformList n)
      (fun _ seed => seed.length = n) (query.take depth) cache hcache
      (fun _ h => BitString.length_of_mem_support_uniformList h) (seed, next) hseed).1
    simp only [selectChild_take, ← hlength,
      eval_drop_succ generator seed query depth (by lia), child, expandCache]
  · simp [frontierOracle, expansionOracle, hquery, PMF.pure_map]

/-- Sampling generator expansions reproduces the earlier prefix hybrid for every adaptive
randomized adversary. No security or output-width assumption on the generator is needed. -/
theorem expansionGame_generated (generator : List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ) (hdepth : depth < n) :
    ProbComp.eval (expansionGame generator (generator <$> BitString.sampleList n)
      adversary n depth) = ProbComp.eval (hybridGame generator adversary n depth) := by
  have h := ProbOracleComp.run_interpret_map_state_of_invariant
    (fun request cache => ProbComp.eval (frontierOracle generator n depth request.2 cache))
    (fun request cache => ProbComp.eval
      (expansionOracle generator (generator <$> BitString.sampleList n) n depth request.2 cache))
    (expandCache generator n) (fun cache => ∀ entry ∈ cache, entry.2.length = n)
    (fun request => frontierOracle_preserves_labels generator n depth request.2)
    (fun request => expansionOracle_generated_step generator n depth hdepth request.2)
    (adversary n []) [] (by simp)
  have houtput := congrArg (PMF.map Prod.fst) h
  simpa [expansionGame, hybridGame, ProbOracleComp.eval_run_interpret,
    expandCache, PMF.map_comp, Function.comp_def] using houtput.symm

private theorem prefix_eager (n depth width : ℕ) (hdepth : depth ≤ n)
    (respond : List Bool → List Bool → List Bool) (program : WordOracleComp Unit Bool) :
    (PMF.uniformOfFintype (BitString depth → BitString width)).bind (fun table =>
      OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle (fun request =>
        PMF.pure (if request.2.length = n then respond request.2
          (List.ofFn (table (BitString.ofList depth (request.2.take depth)))) else []))) program) =
      ((OracleComp.interpret (ProbOracleComp.handler
        (fun k => StateT.lift (ProbComp.unifOracle k)) (fun request cache =>
          if request.2.length = n then
            (memoize (fun _ : List Bool => BitString.uniformList width)
              (request.2.take depth) cache).map
                (fun (value, next) => (respond request.2 value, next))
          else PMF.pure ([], cache))) program).run []).map Prod.fst := by
  let adapter := fun query : List Bool => if query.length = n then
    (respond query) <$> (ProbOracleComp.query (BitString.ofList depth (query.take depth)) :
      ProbOracleComp (fun _ : BitString depth => List Bool) (List Bool))
    else pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map
    (⟨List.ofFn, List.ofFn_injective⟩ : BitString depth ↪ List Bool) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString width)) (fun _ => BitString.uniformList width)
    (fun _ => rfl) (OracleComp.interpret
      (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
        (fun request : Unit × List Bool => adapter request.2)) program)
  have hstep (query : List Bool) : OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key => memoize (fun _ : List Bool => BitString.uniformList width) (List.ofFn key)))
          (adapter query) = fun cache => if query.length = n then
        (memoize (fun _ : List Bool => BitString.uniformList width) (query.take depth) cache).map
          (fun (value, next) => (respond query value, next)) else PMF.pure ([], cache) := by
    funext cache
    by_cases hquery : query.length = n
    · have hprefix : List.ofFn (BitString.ofList depth (query.take depth)) = query.take depth :=
        BitString.ofFn_ofList (by simp [List.length_take, hquery, Nat.min_eq_left hdepth])
      simp only [adapter, hquery, ↓reduceIte, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, hprefix]
      rfl
    · simp only [adapter, hquery, ↓reduceIte, OracleComp.interpret_pure]
      rfl
  have heval (table : BitString depth → BitString width) (query : List Bool) :
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
          (adapter query) = PMF.pure (if query.length = n then
        respond query (List.ofFn (table (BitString.ofList depth (query.take depth)))) else []) := by
    by_cases hquery : query.length = n <;> simp [adapter, hquery, PMF.pure_map]
  simpa only [PMF.pi_uniformOfFintype, OracleComp.interpret_interpret,
    ProbOracleComp.interpret_handler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
    OracleComp.interpret_query, Function.Embedding.coeFn_mk, hstep, heval,
    PMF.monad_bind_eq_bind] using h

private def childrenEquiv (n : ℕ) : BitString (2 * n) ≃ (Bool → BitString n) :=
  (BitString.blocksEquiv (m := 2) (k := n)).trans
    (Equiv.arrowCongr finTwoEquiv (Equiv.refl (BitString n)))

private theorem selectChild_ofFn (n : ℕ) (expansion : BitString (2 * n)) (bit : Bool) :
    selectChild n (List.ofFn expansion) bit = List.ofFn (childrenEquiv n expansion bit) := by
  have h : List.ofFn expansion =
      List.ofFn (BitString.block expansion 0) ++ List.ofFn (BitString.block expansion 1) := by
    rw [List.ofFn_mul]
    simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    congr 1 <;> apply congrArg List.ofFn <;> funext j <;>
      simp [BitString.block, finProdFinEquiv, Nat.add_comm]
  rw [h]
  cases bit <;> simp [childrenEquiv, selectChild, finTwoEquiv]

private def childIndexEquiv (depth : ℕ) : BitString (depth + 1) ≃ (BitString depth × Bool) :=
  (Fin.snocEquiv (fun _ : Fin (depth + 1) => Bool)).symm.trans (Equiv.prodComm _ _)

private def childTableEquiv (n depth : ℕ) :
    (BitString depth → BitString (2 * n)) ≃ (BitString (depth + 1) → BitString n) :=
  ((Equiv.piCongrRight (fun _ : BitString depth => childrenEquiv n)).trans
    (Equiv.curry (BitString depth) Bool (BitString n)).symm).trans
      (Equiv.arrowCongr (childIndexEquiv depth).symm (Equiv.refl (BitString n)))

private theorem childTableEquiv_apply (n depth : ℕ) (table : BitString depth → BitString (2 * n))
    (query : BitString (depth + 1)) :
    childTableEquiv n depth table query =
      childrenEquiv n (table (Fin.init query)) (query (Fin.last depth)) := rfl

private theorem ofFn_childTable (n depth : ℕ) (table : BitString depth → BitString (2 * n))
    (query : List Bool) :
    List.ofFn (childTableEquiv n depth table
      (BitString.ofList (depth + 1) (query.take (depth + 1)))) =
        selectChild n (List.ofFn (table (BitString.ofList depth (query.take depth))))
          (query[depth]?.getD false) := by
  rw [childTableEquiv_apply, selectChild_ofFn]
  have hprefix : Fin.init (BitString.ofList (depth + 1) (query.take (depth + 1))) =
      BitString.ofList depth (query.take depth) := by
    funext i
    simp [Fin.init, BitString.ofList, i.isLt, show i.val < depth + 1 by lia]
  simp [hprefix, BitString.ofList]

/-- Uniform expansions give the next prefix hybrid: the two independent children of each parent
are exactly the independent labels at the next level, under randomized adaptive queries. -/
theorem expansionGame_uniform (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth : ℕ) (hdepth : depth < n) :
    ProbComp.eval (expansionGame generator (BitString.sampleList (2 * n)) adversary n depth) =
      ProbComp.eval (hybridGame generator adversary n (depth + 1)) := by
  let earlier := fun table : BitString depth → BitString (2 * n) =>
    OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle (fun request =>
      PMF.pure (if request.2.length = n then eval generator
        (selectChild n (List.ofFn (table (BitString.ofList depth (request.2.take depth))))
          (request.2[depth]?.getD false)) (request.2.drop (depth + 1)) else []))) (adversary n [])
  let later := fun table : BitString (depth + 1) → BitString n =>
    OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle (fun request =>
      PMF.pure (if request.2.length = n then eval generator
        (List.ofFn (table (BitString.ofList (depth + 1) (request.2.take (depth + 1)))))
          (request.2.drop (depth + 1)) else []))) (adversary n [])
  have hearlier := prefix_eager n depth (2 * n) hdepth.le
    (fun query expansion => eval generator (selectChild n expansion (query[depth]?.getD false))
      (query.drop (depth + 1))) (adversary n [])
  have hlater := prefix_eager n (depth + 1) n (by lia)
    (fun query seed => eval generator seed (query.drop (depth + 1))) (adversary n [])
  calc
    _ = (PMF.uniformOfFintype (BitString depth → BitString (2 * n))).bind earlier := by
      dsimp only [earlier]
      rw [hearlier]
      simp only [expansionGame, ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
      congr 4
      funext request cache
      by_cases hquery : request.2.length = n
      · simp only [expansionOracle, hquery, ite_true, ProbComp.eval_bind,
          ProbComp.eval_memoize, ProbComp.eval_map, BitString.eval_sampleList,
          BitString.uniformList_take (Nat.le_refl (2 * n)), ProbComp.eval_pure]
        rfl
      · simp [expansionOracle, hquery]
    _ = (PMF.uniformOfFintype (BitString (depth + 1) → BitString n)).bind later := by
      rw [← PMF.uniformOfFintype_map_equiv (childTableEquiv n depth), PMF.bind_map]
      simp only [earlier, later, Function.comp_def, ofFn_childTable]
    _ = _ := by
      dsimp only [later]
      rw [hlater]
      simp only [hybridGame, ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
      congr 4
      funext request cache
      by_cases hquery : request.2.length = n <;>
        simp [frontierOracle, hquery, ProbComp.eval_memoize, PMF.map, Function.comp_def]

end Cslib.Crypto.GGM
