/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Control.Monad.Memoize
public import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Memoized oracle computations

An association-list cache in front of a strict oracle PPT computation is strict oracle PPT. On a
cache hit the stored value is returned and the computation does not run, so it makes no external
call; on a miss it runs once and its result is stored. The certificate charges comparing complete
key encodings, the lookup and writing the returned cache.

The closed rule `Cslib.Probability.IsPPTOn.memoize` may run and discard its sampler on a hit. An
oracle computation cannot be run speculatively: a stateful external oracle observes every call.

## Main results

* `Cslib.ProbOracleComp.mem_support_memoize`: a possible result of a cached call is a hit or a
  possible result of the computation, stored at the front of the cache.
* `Cslib.ProbOracleComp.memoize_call_size_le`: a cached call preserves a value-size invariant
  and adds at most one encoded entry, for every external oracle.
* `Cslib.Probability.IsOraclePPTOn.memoize`: certify a memoized oracle computation by `fun_prop`.

## References

Adapts Computability/Probabilistic/Memoize.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to oracle computations.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query Key Value : Type} {spec : Query → Type} [BEq Key]

/-- A possible result of a cached call is either a hit, leaving the cache unchanged, or a possible
result of the computation, stored at the front of the cache. -/
theorem mem_support_memoize (compute : Key → ProbOracleComp spec Value) (key : Key)
    (cache : List (Key × Value)) {result : Value × List (Key × Value)}
    (hresult : result ∈ support (memoize compute key cache)) :
    (cache.lookup key = some result.1 ∧ result.2 = cache) ∨
      (cache.lookup key = none ∧ result.1 ∈ support (compute key) ∧
        result.2 = (key, result.1) :: cache) := by
  rw [memoize] at hresult
  cases hlookup : cache.lookup key with
  | some value =>
    simp only [hlookup] at hresult
    exact .inl ⟨by rw [eq_of_mem_supportWith_pure hresult],
      by rw [eq_of_mem_supportWith_pure hresult]⟩
  | none =>
    simp only [hlookup, bind_pure_comp] at hresult
    obtain ⟨value, hvalue, rfl⟩ := mem_supportWith_map_iff.mp hresult
    exact .inr ⟨rfl, hvalue, rfl⟩

open Turing.MultiTapeTM in
/-- A cached call preserves a bound on the encoded values of all entries, returns a value within
that bound and adds at most one encoded entry, for every possible result under every external
oracle. The growth charges the complete key and value and both layers of framing. -/
theorem memoize_call_size_le [LawfulBEq Key] (keyEncoding : Key ↪ List Bool)
    (valueEncoding : Value ↪ List Bool) (compute : Key → ProbOracleComp spec Value) (key : Key)
    (cache : List (Key × Value)) (maxValue : ℕ)
    (hcache : ∀ entry ∈ cache, (valueEncoding entry.2).length ≤ maxValue)
    (hvalues : ∀ value ∈ support (compute key), (valueEncoding value).length ≤ maxValue)
    {result : Value × List (Key × Value)}
    (hresult : result ∈ support (memoize compute key cache)) :
    (valueEncoding result.1).length ≤ maxValue ∧
      (∀ entry ∈ result.2, (valueEncoding entry.2).length ≤ maxValue) ∧
      (encList (encPair keyEncoding valueEncoding) result.2).length ≤
        (encList (encPair keyEncoding valueEncoding) cache).length +
          4 * (keyEncoding key).length + 2 * maxValue + 3 := by
  rcases mem_support_memoize compute key cache hresult with
    ⟨hlookup, hnext⟩ | ⟨_, hvalue, hnext⟩
  · obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hlookup
    rw [hnext]
    exact ⟨hcache (key, result.1) (by simp [hlist]), hcache, by lia⟩
  · have hbound := hvalues result.1 hvalue
    rw [hnext]
    refine ⟨hbound, ?_, ?_⟩
    · simpa using And.intro hbound hcache
    · simp only [encList_cons, List.length_append, length_frame, length_encPair]
      lia

end Cslib.ProbOracleComp

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Cache a strict oracle PPT computation's results in an ordinary list. On a hit the computation
does not run and makes no external call; on a miss it runs once. Comparing complete key
encodings, the lookup and the complete returned cache are charged. Repeated keys use their first
cached occurrence. The inhabitant of `Value` is never returned. -/
@[fun_prop]
theorem IsOraclePPTOn.memoize {Operation α Key Value : Type} [DecidableEq Operation]
    [Finite Operation] [BEq Key] [LawfulBEq Key] [Nonempty Value] {input : α ↪ List Bool}
    {keyEncoding : Key ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {compute : α → Key → WordOracleComp Operation Value} {query : α → Key}
    {cache : α → List (Key × Value)}
    (hcompute : IsOraclePPTOn input valueEncoding (fun a => compute a (query a)))
    (hquery : ComputableTidilyInPolyTime query input keyEncoding)
    (hcache : ComputableTidilyInPolyTime cache input
      (encList (encPair keyEncoding valueEncoding))) :
    IsOraclePPTOn input (encPair valueEncoding (encList (encPair keyEncoding valueEncoding)))
      (fun a => memoize (compute a) (query a) (cache a)) := by
  let found (a : α) := (cache a).find? (fun entry => query a == entry.1)
  have hfound : ComputableTidilyInPolyTime found input
      (encOption (encPair keyEncoding valueEncoding)) := by fun_prop
  have hhit : ComputableTidilyInPolyTime
      (fun a => (((found a).getD (query a, Classical.arbitrary Value)).2, cache a)) input
      (encPair valueEncoding (encList (encPair keyEncoding valueEncoding))) := by fun_prop
  have hmiss : ComputableTidilyInPolyTime
      (fun pair : α × Value => (pair.2, (query pair.1, pair.2) :: cache pair.1))
      (encPair input valueEncoding)
      (encPair valueEncoding (encList (encPair keyEncoding valueEncoding))) := by fun_prop
  refine (IsOraclePPTOn.cond (condition := fun a => (found a).isSome) (by fun_prop)
    hhit.isOraclePPTOn (hcompute.map_with (f := fun a value => (value, (query a, value) :: cache a))
      hmiss)).congr fun a _ _ _ => ?_
  have hlookup : (cache a).lookup (query a) = (found a).map Prod.snd := by
    simp only [found, List.lookup_eq_findSome?, List.find?_eq_findSome?_guard,
      List.map_findSome?]
    congr 1
    funext entry
    cases h : query a == entry.1 <;> simp [Option.guard, h]
  rw [Cslib.memoize, hlookup]
  cases found a <;> simp only [Option.isSome_none, Option.isSome_some, Option.map_none,
    Option.map_some, Option.getD_some, bind_pure_comp, Bool.false_eq_true, ite_false, ite_true]

end Cslib.Probability
