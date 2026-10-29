/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT

/-! Memoization composes through functional programs, with no default inhabitants. -/

namespace ComplexityTests.MemoizePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

-- Neither key nor value types have an Inhabited instance in this generic client, and it consumes
-- plain query/cache certificates directly.
example {α Key Value : Type} [BEq Key] [LawfulBEq Key] {input : α ↪ List Bool}
    {keyEncoding : Key ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {compute : α → Key → ProbComp Value} {query : α → Key} {cache : α → List (Key × Value)}
    (hcompute : IsPPTOn input valueEncoding (fun a => compute a (query a)))
    (hquery : ComputableInPolyTime query input keyEncoding)
    (hcache : ComputableInPolyTime cache input
      (encList (encPair keyEncoding valueEncoding))) :
    IsPPTOn input (encPair valueEncoding (encList (encPair keyEncoding valueEncoding)))
      (fun a => memoize (compute a) (query a) (cache a)) := by ppt

-- Runtime word lengths and the whole initial cache are charged, including all framing.
example : IsPPTOn (encPair encBits (encList (encPair encBits encBits)))
    (encPair encBits (encList (encPair encBits encBits)))
    (fun p => memoize (fun key => BitString.sampleList key.length) p.1 p.2) := by fun_prop

private noncomputable def repeated (word : List Bool) :
    ProbComp ((List Bool × List Bool) × List (List Bool × List Bool)) := do
  let (first, cache) ← memoize (fun key => BitString.sampleList key.length) word []
  let (second, cache) ← memoize (fun key => BitString.sampleList key.length) word cache
  return ((first, second), cache)

-- Ordinary do notation threads the cache and retains the query across both calls.
example : IsPPTOn encBits
    (encPair (encPair encBits encBits) (encList (encPair encBits encBits))) repeated := by
  unfold repeated
  ppt

-- The two replies agree in their full joint law; the second call does not resample.
example (word : List Bool) : ProbComp.eval (repeated word) =
    (BitString.uniformList word.length).map (fun value => ((value, value), [(word, value)])) := by
  rw [repeated, memoize_repeat]
  simp [memoize, ProbComp.eval_map, PMF.map, Function.comp_def]

private abbrev Cache := List (List Bool × List Bool)
private abbrev cacheEncoding := encList (encPair encBits encBits)

private noncomputable def fillCache (word : List Bool) (cache : Cache) : ProbComp Cache := do
  let (_, next) ← memoize (fun key => BitString.sampleList key.length)
    (word.take cache.length) cache
  return next

private theorem fillCache_ppt :
    IsPPTOn (encPair encBits cacheEncoding) cacheEncoding
      (fun pair => fillCache pair.1 pair.2) := by
  unfold fillCache
  ppt

-- The next query depends on the cache. Growth includes key/value framing and holds for arbitrary
-- initial entries, since the program retains the cache rather than the returned reply.
private theorem fillCache_growth (word : List Bool) (cache next : Cache)
    (h : next ∈ (ProbComp.eval (fillCache word cache)).support) :
    (cacheEncoding next).length ≤ (cacheEncoding cache).length + 6 * word.length + 3 := by
  simp only [fillCache, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_memoize,
    BitString.eval_sampleList] at h
  obtain ⟨⟨value, next⟩, hnext, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have hsize := memoize_cache_growth_le encBits encBits
    (fun key => BitString.uniformList key.length) (word.take cache.length) cache word.length
    (fun _ hvalue => (BitString.length_of_mem_support_uniformList hvalue).le.trans
      (by simp)) (value, next) hnext
  simp only [encBits_apply, List.length_take] at hsize
  dsimp only [cacheEncoding]
  lia

-- A quadratic number of adaptive calls charges the complete supplied initial cache. The client
-- supplies only the one-call growth contract; the loop rule handles accumulation and copying.
example : IsPPTOn (encPair (encPair encBits encUnary) cacheEncoding) cacheEncoding
    (fun p : (List Bool × ℕ) × Cache =>
      OracleComp.iterate (p.1.2 * p.1.2) (fillCache p.1.1) p.2) := by
  have hstep : IsPPTOn
      (encPair (encPair (encPair encBits encUnary) cacheEncoding) cacheEncoding) cacheEncoding
      (fun pair => fillCache pair.1.1.1 pair.2) := by
    have h := fillCache_ppt
    ppt
  have hsize : PolyBounded
      (fun p => (encPair (encPair encBits encUnary) cacheEncoding p).length)
      (fun p => 6 * p.1.1.length + 3) := ComputableInPolyTime.polyBounded (by fun_prop)
  have hgrowth := fun (p : (List Bool × ℕ) × Cache) => fillCache_growth p.1.1
  ppt

-- Zero calls preserve all initial entries.
example (word : List Bool) (cache : Cache) :
    ProbComp.eval (OracleComp.iterate 0 (fillCache word) cache) = PMF.pure cache := by simp

-- A miss extends the cache with the sampled value and preserves the old entry.
example : ProbComp.eval (fillCache [true] [([], [])]) =
    (BitString.uniformList 1).map (fun value => ([true], value) :: [([], [])]) := by
  simp [fillCache, memoize, BitString.eval_sampleList, ProbComp.eval_map, PMF.map]

-- A hit may return an oversized existing value. Cache growth alone promises no reply-size bound.
example : ProbComp.eval (memoize (fun key : List Bool => BitString.sampleList key.length)
    [] [([], [true, true, true])]) = PMF.pure ([true, true, true], [([], [true, true, true])]) := by
  simp [memoize]

end ComplexityTests.MemoizePPT
