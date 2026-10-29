/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Control.Monad.Memoize
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Languages.Probabilistic.Oracle.QueryCount

import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Efficient memoized sampling

An association-list cache preserves the efficiency of a closed probabilistic sampler. The
certificate charges for comparing complete key encodings, looking up an answer and writing the
returned cache. Queries, samplers and initial caches may capture the input.

The proof uses a sample as a fallback for optional lookup, so neither keys nor values need an
inhabitant chosen in advance. Its realizing machine may run and discard the sampler on a hit;
the source program still has exactly the joint result/cache law of `memoize`.

## Main results

* `Cslib.Probability.IsPPTOn.memoize`: certify a memoized sampler through `fun_prop`.
* `Cslib.Probability.memoize_cache_growth_le`: bound new storage independently of existing entries.
* `Cslib.Probability.memoize_call_size_le`: preserve reply sizes and bound local storage growth.
* `Cslib.Probability.memoize_cache_size_le`: bound the encoded cache using external query budgets.

## References

Adapted from Computability/Probabilistic/Memoize.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using plain computability and captured-input rules.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

private theorem lookup_eq_map_find {K V : Type} [BEq K] (key : K) (cache : List (K × V)) :
    cache.lookup key = (cache.find? (fun entry => key == entry.1)).map Prod.snd := by
  simp only [List.lookup_eq_findSome?, List.find?_eq_findSome?_guard, List.map_findSome?]
  congr 1
  funext entry
  cases h : key == entry.1 <;> simp [Option.guard, h]

/-- Cache a certified sampler's results using an ordinary list. Runtime query data, captured
inputs and the complete returned cache are included in the certificate. No default key or value
is required, and repeated keys use their first cached occurrence. -/
@[fun_prop]
theorem IsPPTOn.memoize {α Key Value : Type} [BEq Key] [LawfulBEq Key] {input : α ↪ List Bool}
    {keyEncoding : Key ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {compute : α → Key → ProbComp Value} {query : α → Key} {cache : α → List (Key × Value)}
    (hcompute : IsPPTOn input valueEncoding (fun a => compute a (query a)))
    (hquery : ComputableInPolyTime query input keyEncoding)
    (hcache : ComputableInPolyTime cache input
      (encList (encPair keyEncoding valueEncoding))) :
    IsPPTOn input (encPair valueEncoding (encList (encPair keyEncoding valueEncoding)))
      (fun a => memoize (compute a) (query a) (cache a)) := by
  let found (a : α) := (cache a).find? (fun entry => query a == entry.1)
  have hfound : ComputableInPolyTime found input
      (encOption (encPair keyEncoding valueEncoding)) := by fun_prop
  let finish (a : α) (value : Value) :=
    if (found a).isSome then ((found a).getD (query a, value) |>.2, cache a)
    else (value, (query a, value) :: cache a)
  have hpost : ComputableInPolyTime (fun p : α × Value => finish p.1 p.2)
      (encPair input valueEncoding)
      (encPair valueEncoding (encList (encPair keyEncoding valueEncoding))) := by
    unfold finish
    fun_prop
  refine (hcompute.map_with (f := finish) hpost).congr ?_
  intro a
  rw [Cslib.memoize, lookup_eq_map_find]
  cases h : (cache a).find? (fun entry => query a == entry.1) <;>
    simp [finish, found, h, ProbComp.eval_map, PMF.map, Function.comp_def]

/-- A cached call adds at most one encoded entry, charging the complete key and value and both
layers of framing. Existing entries need no size invariant: a cache hit preserves the cache. -/
theorem memoize_cache_growth_le {Key Value : Type} [BEq Key]
    (keyEncoding : Key ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (distribution : Key → PMF Value) (key : Key) (cache : List (Key × Value)) (maxValue : ℕ)
    (hvalues : ∀ value ∈ (distribution key).support, (valueEncoding value).length ≤ maxValue)
    (result : Value × List (Key × Value))
    (hresult : result ∈ (memoize distribution key cache).support) :
    (encList (encPair keyEncoding valueEncoding) result.2).length ≤
      (encList (encPair keyEncoding valueEncoding) cache).length +
        4 * (keyEncoding key).length + 2 * maxValue + 3 := by
  rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hresult with
    ⟨_, hnext⟩ | ⟨_, hvalue, hnext⟩
  · simp only [hnext]
    lia
  · have := hvalues _ hvalue
    simp only [hnext, encList_cons, List.length_append, length_frame, length_encPair]
    lia

/-- A cached call preserves a reply-size invariant and adds at most one encoded entry. The bound
charges the complete key and value, including both layers of framing. -/
theorem memoize_call_size_le {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (keyEncoding : Key ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (distribution : Key → PMF Value) (key : Key) (cache : List (Key × Value)) (maxValue : ℕ)
    (hcache : ∀ entry ∈ cache, (valueEncoding entry.2).length ≤ maxValue)
    (hvalues : ∀ value ∈ (distribution key).support, (valueEncoding value).length ≤ maxValue)
    (result : Value × List (Key × Value))
    (hresult : result ∈ (memoize distribution key cache).support) :
    (valueEncoding result.1).length ≤ maxValue ∧
      (∀ entry ∈ result.2, (valueEncoding entry.2).length ≤ maxValue) ∧
      (encList (encPair keyEncoding valueEncoding) result.2).length ≤
        (encList (encPair keyEncoding valueEncoding) cache).length +
          4 * (keyEncoding key).length + 2 * maxValue + 3 := by
  obtain ⟨hreply, hcache'⟩ := RandomOracle.memoize_invariant distribution
    (fun _ value => (valueEncoding value).length ≤ maxValue) key cache hcache hvalues result hresult
  exact ⟨hreply, hcache', memoize_cache_growth_le keyEncoding valueEncoding distribution key cache
    maxValue hvalues result hresult⟩

/-- Bounds on external calls, encoded keys and replies bound the complete cache of a randomized
client. Preassigned entries are included, as are both pair and list framing costs. -/
theorem memoize_cache_size_le {α Key Value : Type} [BEq Key]
    (keyEncoding : Key ↪ List Bool) (valueEncoding : Value ↪ List Bool)
    (distribution : Key → PMF Value) (program : ProbOracleComp (fun _ : Key => Value) α)
    (calls maxKey maxValue : ℕ)
    (hcalls : program.IsQueryBounded calls)
    (hkeys : program.QueriesSatisfy fun key => (keyEncoding key).length ≤ maxKey)
    (hvalues : ∀ key, (keyEncoding key).length ≤ maxKey →
      ∀ value ∈ (distribution key).support, (valueEncoding value).length ≤ maxValue)
    (cache cache' : List (Key × Value))
    (hcache : ∀ entry ∈ cache,
      (keyEncoding entry.1).length ≤ maxKey ∧ (valueEncoding entry.2).length ≤ maxValue)
    (result : α)
    (h : (result, cache') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
        (memoize distribution)) program).run cache).support) :
    (encList (encPair keyEncoding valueEncoding) cache').length ≤
      (cache.length + calls) * (4 * maxKey + 2 * maxValue + 3) := by
  obtain ⟨hcount, hentries⟩ := RandomOracle.memoize_cache_bounds_prob distribution program
    (fun key => (keyEncoding key).length) calls maxKey hcalls hkeys cache cache' result h
  have hentry : ∀ entry ∈ cache', (encPair keyEncoding valueEncoding entry).length ≤
      2 * maxKey + maxValue + 1 := by
    intro entry hentry
    have hbounds : (keyEncoding entry.1).length ≤ maxKey ∧
        (valueEncoding entry.2).length ≤ maxValue := by
      rcases hentries entry hentry with h | ⟨hkey, hvalue⟩
      · exact hcache entry h
      · exact ⟨hkey, hvalues entry.1 hkey entry.2 hvalue⟩
    simp only [length_encPair]
    lia
  have hlength := (length_encList_le _ _ hentry).trans
    (Nat.mul_le_mul_right (2 * (2 * maxKey + maxValue + 1) + 1) hcount)
  convert hlength using 1
  ring

end Cslib.Probability
