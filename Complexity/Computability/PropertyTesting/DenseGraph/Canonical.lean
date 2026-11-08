/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PropertyTesting.DenseGraph.Basic
public import Cslib.Probability.PMF
public import Mathlib.Combinatorics.SimpleGraph.Maps
import Complexity.Foundations.Combinatorics.SimpleGraph.SymmDiff
import Complexity.Languages.Probabilistic.RandomPermutation
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform

/-!
# Canonical testers in the dense graph model

A tester in the dense graph model is *canonical* if it samples a uniformly random set of `s`
vertices, queries all pairs among them and accepts if and only if the induced subgraph has some
fixed graph property `D` [Goldreich and Trevisan, §2.3][GoldreichTrevisan2003]. Goldreich and
Trevisan show that every one-sided tester, adaptive or not, can be converted into a canonical
one-sided tester with `2 q` sample vertices and hence `(2 q).choose 2` queries [Goldreich and
Trevisan, Theorem 2 and Theorem 4.5][GoldreichTrevisan2003]. This file formalizes this one-sided
half of their theorem.

A *graph property* in their sense is closed under relabelling the vertices (`IsInvariant`); the
model's distance is then relabelling-invariant too (`editDist_comap_equiv`, `IsFar.comap`).
`canonicalTester n s hs D` samples a uniform permutation `σ` of `Fin n`, queries all pairs among
`σ 0, …, σ (s - 1)` (`queryInduced`) and accepts if and only if the induced labelled graph on
`Fin s` has property `D`. It makes `s.choose 2` queries (`isQueryBounded_canonicalTester`). The
sample is the ordered prefix of a uniform permutation; when `D` is closed under relabelling, as in
the theorem below, this is the same as sampling a uniform `s`-set of vertices.

The main theorem, `isOneSidedTester_canonicalTester`, takes a one-sided tester `T` for an
invariant property `P` with proximity `ε` and query bound `q`. It returns the canonical tester with
`min (2 q) n` sample vertices and the decision property `InducedOf P`: the graph on the sample is
an induced subgraph of some graph with property `P`. That tester is one-sided for `P` with the same
proximity and `(2 q).choose 2` queries. `InducedOf P` is the least decision property possible: a
canonical tester accepts every graph with property `P` with probability one exactly when its
decision property holds on all labelled induced subgraphs of graphs with property `P`
(`acceptProb_canonicalTester_eq_one_iff`). The proximity `ε` enters only through `IsFar.comap`, so
the theorem holds equally with Goldreich and Trevisan's normalization of the distance.

## Source mapping

The following locators refer to the journal version [GoldreichTrevisan2003].

* §2.1, the definition of a graph property and Claim 2.1 (relabelling preserves distance):
  `IsInvariant` and `IsFar.comap`.
* §2.3, the definition of a canonical tester and Theorem 2, one-sided part: `canonicalTester` and
  `isOneSidedTester_canonicalTester`.
* §4.1, Lemma 4.1, proof: the uniform relabelling `π`, chosen on the fly, and the count of at most
  `2 q` uncovered vertices. Goldreich and Trevisan first convert `T` into a vertex-uncovering
  tester. We instead run `T` itself against the lazily sampled permutation of
  `Cslib.RandomPermutation` and argue by induction on the query bound.
* §4.2.1–§4.2.2, Claims 4.2 and 4.3, one-sided parts: for a one-sided tester, the decision is a
  deterministic property of the induced subgraph, closed under isomorphism. Here it is
  `InducedOf P`.
* §4.3, Theorem 4.5, one-sided case: a sample of `2 q` vertices suffices.

## Proof outline

Let `G` be `ε`-far from `P` and relabel it by a uniform permutation `π`. Every relabelled copy
is `ε`-far (`IsFar.comap`), so `T` accepts it with probability at most `1 / 3`, and so does the
average over `π`. Sample `π` lazily, one image at a time, and record the `k`-th vertex of `G`
that is uncovered at position `k`; these positions again follow a uniform permutation. If a run of
`T` rejects, the vertices of `G` uncovered by that run do not induce a subgraph of any graph with
property `P`. Otherwise one-sidedness, applied to a relabelled graph with property `P` that
agrees with `G` on the run, would force acceptance. A run uncovers at most `2 q` vertices (two per
query). Hence the probability that the first `2 q` positions induce a subgraph of a graph with
property `P` is at most the acceptance probability of `T`. This comparison is proved by
induction on the query bound. The canonical tester accepts exactly in this event, because a
graph with property `P` that agrees with `G` on the sample can be relabelled so that the sample
sits at its first positions.

## Main definitions

* `Cslib.DenseGraphTesting.IsInvariant`: a property of graphs on `Fin n` closed under relabelling.
* `Cslib.DenseGraphTesting.InducedOf`: a graph that is an induced subgraph of some graph with a
  given property.
* `Cslib.DenseGraphTesting.canonicalTester`: sample a uniform set of vertices, query the induced
  subgraph and decide by a fixed property.

## Main results

* `Cslib.DenseGraphTesting.IsFar.comap`: relabelling preserves the distance to an invariant
  property.
* `Cslib.DenseGraphTesting.acceptProb_canonicalTester`: the acceptance probability of a canonical
  tester.
* `Cslib.DenseGraphTesting.acceptProb_canonicalTester_eq_one_iff`: a canonical tester is perfectly
  complete exactly when its decision property contains the induced subgraphs of the property.
* `Cslib.DenseGraphTesting.isOneSidedTester_canonicalTester`: every one-sided tester with `q`
  queries for an invariant property yields a canonical one-sided tester with `(2 q).choose 2`
  queries.
* `Cslib.DenseGraphTesting.OneSidedTestable.canonical`: the same for a family of properties.

## Limitations

Only the one-sided half of Goldreich and Trevisan's theorem is formalized. The two-sided half
(canonical testers with `O(q)` sample vertices and `O(q²)` queries, by error reduction and their
Lemma 4.4) is not. The decision property `InducedOf P` depends on the number `n` of vertices
through `P`, as Goldreich and Trevisan allow (their footnote 6). Whether it can be replaced by `P`
itself (their §4.2.4), as for properties closed under induced subgraphs (their Proposition D.2, due
to Alon) and graph partition properties (Corollary 5.9), is not addressed. The theorems bound
queries, not running time.

## References

* [O. Goldreich, L. Trevisan, *Three theorems regarding testing graph
  properties*][GoldreichTrevisan2003]
-/

public section

namespace Cslib.DenseGraphTesting

open SimpleGraph Finset Probability

/-! ### Graph properties and relabelling -/

/-- A property of graphs on `Fin n` is *invariant* (a graph property in the sense of Goldreich and
Trevisan) when it is closed under relabelling the vertices. -/
def IsInvariant {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)), P G → P (G.comap π)

theorem isInvariant_iff {n : ℕ} {P : SimpleGraph (Fin n) → Prop} :
    IsInvariant P ↔ ∀ (π : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)), P G → P (G.comap π) :=
  Iff.rfl

/-- The labelled graph `K` on `Fin s` is an induced subgraph of some graph on `Fin n` with property
`P`. This is the decision property of the canonical tester. -/
def InducedOf {n s : ℕ} (P : SimpleGraph (Fin n) → Prop) (K : SimpleGraph (Fin s)) : Prop :=
  ∃ H, P H ∧ Nonempty (K ↪g H)

theorem inducedOf_iff {n s : ℕ} {P : SimpleGraph (Fin n) → Prop} {K : SimpleGraph (Fin s)} :
    InducedOf P K ↔ ∃ H, P H ∧ Nonempty (K ↪g H) :=
  Iff.rfl

theorem IsInvariant.comap_iff {n : ℕ} {P : SimpleGraph (Fin n) → Prop} (hP : IsInvariant P)
    (π : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) : P (G.comap π) ↔ P G := by
  refine ⟨fun h => ?_, hP π G⟩
  have := hP π.symm _ h
  rwa [comap_comap, show ((π : Fin n → Fin n) ∘ (π.symm : Fin n → Fin n)) = id from
    funext fun x => π.apply_symm_apply x, comap_id] at this

/-- Relabelling a graph preserves its distance to an invariant property [Goldreich and Trevisan,
Claim 2.1][GoldreichTrevisan2003]. -/
theorem IsFar.comap {n : ℕ} {P : SimpleGraph (Fin n) → Prop} (hP : IsInvariant P)
    {G : SimpleGraph (Fin n)} {ε : ℝ} (h : IsFar G P ε) (π : Equiv.Perm (Fin n)) :
    IsFar (G.comap π) P ε := by
  rw [isFar_iff] at h ⊢
  intro H hH
  have h₁ := h (H.comap π.symm) (hP π.symm H hH)
  have h₂ : H = (H.comap π.symm).comap π := by
    rw [comap_comap, show ((π.symm : Fin n → Fin n) ∘ (π : Fin n → Fin n)) = id from
      funext fun x => π.symm_apply_apply x, comap_id]
  rw [h₂, editDist_comap_equiv]
  exact h₁

/-! ### Sampling a uniform permutation -/

/-- A uniformly random permutation of `Fin n`, drawn with one call to the uniform sampler. -/
noncomputable def unifPerm (n : ℕ) : ProbComp (Equiv.Perm (Fin n)) :=
  have h : Fintype.card (Equiv.Perm (Fin n)) = (n.factorial - 1) + 1 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    have := Nat.factorial_pos n
    omega
  (Fintype.equivFinOfCardEq h).symm <$> ProbComp.unifFin (n.factorial - 1)

theorem eval_unifPerm (n : ℕ) :
    ProbComp.eval (unifPerm n) = PMF.uniformOfFintype (Equiv.Perm (Fin n)) := by
  rw [unifPerm, ProbComp.eval_map, ProbComp.eval_unifFin]
  exact Probability.PMF.uniformOfFintype_map_equiv _

/-! ### Querying an induced subgraph -/

/-- Query the pairs `(w i, v)` for `i : Fin m` and return the answers. -/
def queryRow {n : ℕ} (v : Fin n) :
    (m : ℕ) → (Fin m → Fin n) → ProbOracleComp (pairSpec (Fin n)) (Fin m → Bool)
  | 0, _ => pure Fin.elim0
  | m + 1, w => do
    let b ← queryAdj (w 0) v
    let r ← queryRow v m (fun i => w i.succ)
    pure (Fin.cons b r)

/-- Extend a graph on `Fin m` by a last vertex adjacent to the vertices `i` with `r i`. -/
def snocGraph {m : ℕ} (K : SimpleGraph (Fin m)) (r : Fin m → Bool) :
    SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel fun i j =>
    Fin.lastCases (Fin.lastCases False (fun j' => r j' = true) j)
      (fun i' => Fin.lastCases (r i' = true) (fun j' => K.Adj i' j') j) i

/-- Query all `m.choose 2` pairs among `w 0, …, w (m - 1)` and return the induced labelled graph on
`Fin m`. -/
def queryInduced {n : ℕ} :
    (m : ℕ) → (Fin m → Fin n) → ProbOracleComp (pairSpec (Fin n)) (SimpleGraph (Fin m))
  | 0, _ => pure ⊥
  | m + 1, w => do
    let K ← queryInduced m (fun i => w i.castSucc)
    let r ← queryRow (w (Fin.last m)) m (fun i => w i.castSucc)
    pure (snocGraph K r)

theorem isQueryBounded_queryRow {n : ℕ} (v : Fin n) (m : ℕ) (w : Fin m → Fin n) :
    ProbOracleComp.IsQueryBounded (queryRow v m w) m := by
  induction m with
  | zero => exact .pure _ _
  | succ m ih =>
    rw [queryRow]
    refine ((isQueryBounded_queryAdj (w 0) v).bind fun b =>
      (ih (fun i => w i.succ)).bind (m := 0) fun r => .pure _ 0).mono (by omega)

theorem isQueryBounded_queryInduced {n : ℕ} (m : ℕ) (w : Fin m → Fin n) :
    ProbOracleComp.IsQueryBounded (queryInduced m w) (m.choose 2) := by
  induction m with
  | zero => exact .pure _ _
  | succ m ih =>
    rw [queryInduced]
    refine ((ih (fun i => w i.castSucc)).bind fun K =>
      (isQueryBounded_queryRow (w (Fin.last m)) m (fun i => w i.castSucc)).bind (m := 0)
        fun r => .pure _ 0).mono ?_
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    omega

theorem evalWith_queryRow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (m : ℕ) (w : Fin m → Fin n) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (queryRow v m w) = PMF.pure fun i => decide (G.Adj (w i) v) := by
  induction m with
  | zero =>
    rw [queryRow, OracleComp.evalWith_pure]
    exact congrArg PMF.pure (funext fun i => i.elim0)
  | succ m ih =>
    rw [queryRow, OracleComp.evalWith_bind, evalWith_queryAdj, PMF.pure_bind,
      OracleComp.evalWith_bind, ih, PMF.pure_bind, OracleComp.evalWith_pure]
    exact congrArg PMF.pure (funext fun i => Fin.cases rfl (fun _ => rfl) i)

theorem snocGraph_comap {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin (m + 1) → Fin n) :
    snocGraph (G.comap fun i => w i.castSucc) (fun i => decide (G.Adj (w i.castSucc)
      (w (Fin.last m)))) = G.comap w := by
  ext i j
  simp only [snocGraph, fromRel_adj, comap_adj]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, decide_eq_true_eq, or_self]
      exact ⟨fun h => h.2.symm, fun h => ⟨fun e => h.ne (congrArg w e), h.symm⟩⟩
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, decide_eq_true_eq, or_self]
      exact ⟨fun h => h.2, fun h => ⟨fun e => h.ne (congrArg w e), h⟩⟩
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact ⟨fun h => h.2.elim id (·.symm), fun h => ⟨fun e => h.ne (congrArg w e), Or.inl h⟩⟩

/-- `queryInduced` returns the induced labelled subgraph `G.comap w`. -/
theorem evalWith_queryInduced {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) (w : Fin m → Fin n) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle G))
      (queryInduced m w) = PMF.pure (G.comap w) := by
  classical
  induction m with
  | zero =>
    rw [queryInduced, OracleComp.evalWith_pure]
    exact congrArg PMF.pure (SimpleGraph.ext (funext fun i => i.elim0))
  | succ m ih =>
    rw [queryInduced, OracleComp.evalWith_bind, ih, PMF.pure_bind, OracleComp.evalWith_bind,
      evalWith_queryRow, PMF.pure_bind, OracleComp.evalWith_pure, snocGraph_comap]

/-! ### Canonical testers -/

/-- The canonical tester with `s` sample vertices and decision property `D`: sample a uniform
permutation `σ` of `Fin n`, query all pairs among `σ 0, …, σ (s - 1)` and accept if and only if the
induced labelled graph on `Fin s` has property `D` [Goldreich and Trevisan,
§2.3][GoldreichTrevisan2003]. When `D` is closed under relabelling this is the same as sampling a
uniform `s`-set of vertices. -/
noncomputable def canonicalTester (n s : ℕ) (hs : s ≤ n) (D : SimpleGraph (Fin s) → Prop)
    [DecidablePred D] : Tester n := do
  let σ ← ProbOracleComp.sample (unifPerm n)
  let K ← queryInduced s fun i => σ (Fin.castLE hs i)
  pure (decide (D K))

/-- A canonical tester with `s` sample vertices makes `s.choose 2` queries. -/
theorem isQueryBounded_canonicalTester (n s : ℕ) (hs : s ≤ n) (D : SimpleGraph (Fin s) → Prop)
    [DecidablePred D] :
    ProbOracleComp.IsQueryBounded (canonicalTester n s hs D) (s.choose 2) := by
  rw [canonicalTester]
  exact ((ProbOracleComp.IsQueryBounded.sample (spec := pairSpec (Fin n)) (unifPerm n)).bind
    fun σ => (isQueryBounded_queryInduced s fun i => σ (Fin.castLE hs i)).bind (m := 0)
      fun K => .pure _ 0).mono (by omega)

/-- The acceptance probability of a canonical tester is the probability that the induced subgraph
on the first `s` positions of a uniform permutation has the decision property. -/
theorem acceptProb_canonicalTester (n s : ℕ) (hs : s ≤ n) (D : SimpleGraph (Fin s) → Prop)
    [DecidablePred D] (G : SimpleGraph (Fin n)) :
    acceptProb (canonicalTester n s hs D) G =
      ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).toOuterMeasure
        {σ | D (G.comap fun i => σ (Fin.castLE hs i))}).toReal := by
  rw [acceptProb_eq, canonicalTester, OracleComp.evalWith_bind, evalWith_sample, eval_unifPerm]
  simp only [OracleComp.evalWith_bind, evalWith_queryInduced, PMF.pure_bind,
    OracleComp.evalWith_pure]
  have h : ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun σ =>
      PMF.pure (decide (D (G.comap fun i => σ (Fin.castLE hs i))))) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
        fun σ => decide (D (G.comap fun i => σ (Fin.castLE hs i))) := rfl
  rw [h, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 2
  ext σ
  simp

/-- Every injection `Fin s ↪ Fin n` extends a permutation of `Fin n` along `Fin.castLE`. -/
private theorem exists_perm_extend {n s : ℕ} (hs : s ≤ n) (φ : Fin s ↪ Fin n) :
    ∃ ρ : Equiv.Perm (Fin n), ∀ i : Fin s, ρ (Fin.castLE hs i) = φ i := by
  classical
  let e₀ : {x : Fin n // x.val < s} ≃ Fin s :=
    ⟨fun x => ⟨x.1.val, x.2⟩, fun i => ⟨Fin.castLE hs i, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  let e : {x : Fin n // x.val < s} ≃ {y : Fin n // y ∈ Set.range φ} :=
    e₀.trans (Equiv.ofInjective φ φ.injective)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ i.2]
  rfl

/-- A canonical tester accepts every graph with property `P` with probability one if and only if
its decision property holds on every labelled induced subgraph of a graph with property `P`. In
particular `InducedOf P` is the least decision property of a perfectly complete canonical tester
with `s` sample vertices. -/
theorem acceptProb_canonicalTester_eq_one_iff {n s : ℕ} (hs : s ≤ n)
    (P : SimpleGraph (Fin n) → Prop) (D : SimpleGraph (Fin s) → Prop) [DecidablePred D] :
    (∀ G, P G → acceptProb (canonicalTester n s hs D) G = 1) ↔ ∀ K, InducedOf P K → D K := by
  simp only [acceptProb_canonicalTester, ENNReal.toReal_eq_one_iff,
    PMF.toOuterMeasure_apply_eq_one_iff]
  constructor
  · rintro h K ⟨H, hH, ⟨f⟩⟩
    obtain ⟨ρ, hρ⟩ := exists_perm_extend hs f.toEmbedding
    have hK : (H.comap fun i => ρ (Fin.castLE hs i)) = K := by
      ext i j
      simp only [comap_adj, hρ]
      exact f.map_adj_iff
    rw [← hK]
    exact h H hH (Probability.PMF.mem_support_uniformOfFintype ρ)
  · intro h G hG σ _
    exact h _ ⟨G, hG, ⟨Embedding.comap ((Fin.castLEEmb hs).trans σ.toEmbedding) G⟩⟩

/-- A one-sided tester never rejects a graph with the property. -/
theorem IsOneSidedTester.evalWith_false_eq_zero {n : ℕ} {P : SimpleGraph (Fin n) → Prop}
    {T : Tester n} {ε : ℝ} {q : ℕ} (hT : IsOneSidedTester T P ε q) {H : SimpleGraph (Fin n)}
    (hH : P H) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle H)) T false = 0 := by
  have h1 := hT.accept H hH
  rw [acceptProb_eq] at h1
  have h2 := Probability.PMF.toReal_true_add_toReal_false
    (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle H)) T)
  rw [h1] at h2
  have h3 : (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (adjOracle H)) T
      false).toReal = 0 := by linarith
  rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (PMF.apply_ne_top _ _)] at h3

/-! ### Lazy relabelling caches

The relabelling `π` is sampled lazily by `Cslib.RandomPermutation.answer`; a cache lists the
pairs `(u, π u)` uncovered so far, newest first. -/

section Lazy

open RandomPermutation

variable {n : ℕ}

/-- A cache of the lazily sampled relabelling: a partial bijection with distinct inputs. -/
private def CacheValid (c : Cache (Fin n)) : Prop :=
  IsPartialBijection c ∧ (c.map Prod.fst).Nodup

/-- Relabel the `k`-th entry from the end of the cache by the position `k`. -/
private def posCache [NeZero n] : Cache (Fin n) → Cache (Fin n)
  | [] => []
  | e :: c => (⟨c.length % n, Nat.mod_lt _ (NeZero.pos n)⟩, e.2) :: posCache c

private theorem map_snd_posCache [NeZero n] (c : Cache (Fin n)) :
    (posCache c).map Prod.snd = c.map Prod.snd := by
  induction c with
  | nil => rfl
  | cons e c ih => simp only [posCache, List.map_cons, ih]

private theorem invLookup_posCache_eq_none_iff [NeZero n] (c : Cache (Fin n)) (y : Fin n) :
    invLookup (posCache c) y = none ↔ invLookup c y = none := by
  have h := map_snd_posCache c
  simp only [invLookup_eq_none_iff]
  constructor
  · intro hp e he hy
    have : y ∈ (posCache c).map Prod.snd := h ▸ List.mem_map.mpr ⟨e, he, hy⟩
    obtain ⟨e', he', hy'⟩ := List.mem_map.mp this
    exact hp e' he' hy'
  · intro hc e he hy
    have : y ∈ c.map Prod.snd := h ▸ List.mem_map.mpr ⟨e, he, hy⟩
    obtain ⟨e', he', hy'⟩ := List.mem_map.mp this
    exact hc e' he' hy'

private theorem unusedRange_posCache [NeZero n] (c : Cache (Fin n)) :
    unusedRange (posCache c) = unusedRange c := by
  ext y
  simp only [mem_unusedRange_iff, invLookup_posCache_eq_none_iff]

private theorem CacheValid.length_le {c : Cache (Fin n)} (h : CacheValid c) : c.length ≤ n := by
  simpa using h.2.length_le_card

private theorem not_mem_map_fst_of_lookup_eq_none {c : Cache (Fin n)} {u : Fin n}
    (hu : c.lookup u = none) : u ∉ c.map Prod.fst := by
  intro hmem
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  exact lookup_eq_none_iff.mp hu e he rfl

private theorem val_fst_lt_of_mem_posCache [NeZero n] {c : Cache (Fin n)} (hc : c.length ≤ n)
    {e : Fin n × Fin n} (he : e ∈ posCache c) : e.1.val < c.length := by
  induction c with
  | nil => simp [posCache] at he
  | cons a c ih =>
    simp only [posCache, List.mem_cons] at he
    simp only [List.length_cons] at hc ⊢
    rcases he with rfl | he
    · simp only
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have := ih (by omega) he
      omega

private theorem exists_mem_posCache [NeZero n] {c : Cache (Fin n)} (hc : c.length ≤ n)
    {e : Fin n × Fin n} (he : e ∈ c) : ∃ i : Fin n, i.val < c.length ∧ (i, e.2) ∈ posCache c := by
  induction c with
  | nil => simp at he
  | cons a c ih =>
    simp only [List.length_cons] at hc ⊢
    rcases List.mem_cons.mp he with rfl | he
    · refine ⟨⟨c.length % n, Nat.mod_lt _ (NeZero.pos n)⟩, ?_, List.mem_cons_self⟩
      simp only
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · obtain ⟨i, hi, hmem⟩ := ih (by omega) he
      exact ⟨i, by omega, List.mem_cons_of_mem _ hmem⟩

private theorem lookup_posCache_eq_none [NeZero n] {c : Cache (Fin n)} (hc : c.length < n) :
    (posCache c).lookup ⟨c.length % n, Nat.mod_lt _ (NeZero.pos n)⟩ = none := by
  rw [lookup_eq_none_iff]
  intro e he heq
  have := val_fst_lt_of_mem_posCache hc.le he
  rw [heq] at this
  simp only [Nat.mod_eq_of_lt hc] at this
  omega

private theorem CacheValid.cons {c : Cache (Fin n)} (hc : CacheValid c) {u x : Fin n}
    (hu : c.lookup u = none) (hx : invLookup c x = none) : CacheValid ((u, x) :: c) :=
  ⟨hc.1.cons_of_lookup_eq_none hu hx,
    List.nodup_cons.mpr ⟨not_mem_map_fst_of_lookup_eq_none hu, hc.2⟩⟩

private theorem isPartialBijection_posCache [NeZero n] {c : Cache (Fin n)} (hc : CacheValid c) :
    IsPartialBijection (posCache c) := by
  induction c with
  | nil => exact isPartialBijection_nil
  | cons a c ih =>
    obtain ⟨⟨π, hπ⟩, hnd⟩ := hc
    rw [agreesWith_cons] at hπ
    have hnd' := List.nodup_cons.mp hnd
    have hc' : CacheValid c := ⟨⟨π, hπ.2⟩, hnd'.2⟩
    have hlen : c.length < n := by
      have := (show CacheValid (a :: c) from ⟨⟨π, (agreesWith_cons _ _ _).mpr hπ⟩, hnd⟩).length_le
      simp only [List.length_cons] at this
      omega
    refine (ih hc').cons_of_lookup_eq_none (lookup_posCache_eq_none hlen) ?_
    rw [invLookup_posCache_eq_none_iff, invLookup_eq_none_iff]
    intro e he heq
    apply hnd'.1
    rw [← hπ.1, ← hπ.2 e he] at heq
    exact List.mem_map.mpr ⟨e, he, π.injective heq⟩

private theorem mem_support_answer_forward [Nonempty (Fin n)] {c : Cache (Fin n)}
    (hc : CacheValid c) {u x : Fin n} {c' : Cache (Fin n)}
    (h : (x, c') ∈ (answer (.forward u) c).support) :
    CacheValid c' ∧ (u, x) ∈ c' ∧ (∀ e ∈ c, e ∈ c') ∧ c'.length ≤ c.length + 1 := by
  dsimp [answer] at h
  cases hu : c.lookup u with
  | some y =>
    rw [hu, PMF.mem_support_pure_iff] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hc, mem_of_lookup_eq_some hu, fun e he => he, by omega⟩
  | none =>
    have hne := hc.1.unusedRange_nonempty hu
    rw [hu, dite_eq_left hne, PMF.mem_support_map_iff] at h
    obtain ⟨y, hy, heq⟩ := h
    rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedRange_iff] at hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨hc.cons hu hy, List.mem_cons_self, fun e he => List.mem_cons_of_mem _ he,
      by simp⟩

private theorem answer_bind_complete [Nonempty (Fin n)] (q : PermQuery (Fin n)) (c : Cache (Fin n))
    (hc : IsPartialBijection c) :
    (answer q c).bind (fun p => complete p.2) = complete c := by
  have h := congrArg (PMF.map Prod.snd) (answer_complete q c hc)
  rw [PMF.map_comp, PMF.map_bind] at h
  have hid : ∀ p : PMF (Equiv.Perm (Fin n)), p.map (fun x => x) = p := PMF.map_id
  simpa [Function.comp_def, PMF.map_comp, hid] using h

private theorem mem_support_complete {c : Cache (Fin n)} (hc : IsPartialBijection c)
    [Nonempty (Fin n)] {π : Equiv.Perm (Fin n)} (h : π ∈ (complete c).support) :
    AgreesWith c π := by
  have hne : (extPerms c).Nonempty := extPerms_nonempty_iff.mpr hc
  rw [complete, dite_eq_left hne, PMF.mem_support_uniformOfFinset_iff, mem_extPerms_iff] at h
  exact h

/-- The positional marginal: lazily answering a forward query and relabelling the new cache by
positions has the same law as relabelling the old cache. -/
private theorem answer_bind_complete_posCache [NeZero n] {c : Cache (Fin n)} (hc : CacheValid c)
    (u : Fin n) :
    (answer (.forward u) c).bind (fun p => complete (posCache p.2)) = complete (posCache c) := by
  cases hu : c.lookup u with
  | some y =>
    simp only [answer, hu, PMF.pure_bind]
  | none =>
    have hne := hc.1.unusedRange_nonempty hu
    have hlen : c.length < n := by
      have := (List.nodup_cons.mpr ⟨not_mem_map_fst_of_lookup_eq_none hu, hc.2⟩).length_le_card
      simp only [List.length_cons, List.length_map, Fintype.card_fin] at this
      omega
    have hk := lookup_posCache_eq_none hlen
    have h := answer_bind_complete (.forward ⟨c.length % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      (posCache c) (isPartialBijection_posCache hc)
    rw [← h]
    simp only [answer, hu, hk, unusedRange_posCache, dite_eq_left hne, PMF.bind_map]
    rfl

end Lazy

/-! ### Soundness -/

section Soundness

open RandomPermutation

variable {n : ℕ}

local notation "⟪" G "⟫" => OracleComp.sumHandler ProbComp.unifOracle (adjOracle G)

/-- `H` agrees with `G` on the cache `c`: an entry `(u, x)` says that vertex `u` of `H` stands for
vertex `x` of `G`. -/
private def Agree (G H : SimpleGraph (Fin n)) (c : Cache (Fin n)) : Prop :=
  ∀ e₁ ∈ c, ∀ e₂ ∈ c, (H.Adj e₁.1 e₂.1 ↔ G.Adj e₁.2 e₂.2)

/-- Some graph with property `P` agrees with `G.comap σ` on the vertices below `k`. -/
private def Good (P : SimpleGraph (Fin n) → Prop) (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (k : ℕ) : Prop :=
  ∃ H, P H ∧ ∀ i j : Fin n, i.val < k → j.val < k → (H.Adj i j ↔ G.Adj (σ i) (σ j))

private theorem Good.mono {P : SimpleGraph (Fin n) → Prop} {G : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} {k k' : ℕ} (h : Good P G σ k) (hk : k' ≤ k) : Good P G σ k' := by
  obtain ⟨H, hH, hadj⟩ := h
  exact ⟨H, hH, fun i j hi hj => hadj i j (by omega) (by omega)⟩

private theorem Good.of_min {P : SimpleGraph (Fin n) → Prop} {G : SimpleGraph (Fin n)}
    {σ : Equiv.Perm (Fin n)} {k : ℕ} (h : Good P G σ (min k n)) : Good P G σ k := by
  obtain ⟨H, hH, hadj⟩ := h
  exact ⟨H, hH, fun i j hi hj => hadj i j (lt_min hi i.2) (lt_min hj j.2)⟩

private theorem toOuterMeasure_bind_le_bind_apply {α β γ : Type*} (p : PMF α) (f : α → PMF β)
    (g : α → PMF γ) (s : Set β) (b : γ)
    (h : ∀ a ∈ p.support, (f a).toOuterMeasure s ≤ g a b) :
    (p.bind f).toOuterMeasure s ≤ (p.bind g) b := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

private theorem bind_apply_eq_zero_of_mem_support {α β : Type*} {p : PMF α} {f : α → PMF β} {b : β}
    (h : p.bind f b = 0) {a : α} (ha : a ∈ p.support) : f a b = 0 := by
  rw [PMF.apply_eq_zero_iff] at h ⊢
  exact fun hb => h ((PMF.mem_support_bind_iff _ _ _).2 ⟨a, ha, hb⟩)

private theorem complete_bind_eq_answer_bind [Nonempty (Fin n)] {c : Cache (Fin n)}
    (hc : IsPartialBijection c) (u : Fin n) {β : Type}
    (F : Fin n → Equiv.Perm (Fin n) → PMF β) :
    ((complete c).bind fun π => F (π u) π) =
      (answer (.forward u) c).bind fun p => (complete p.2).bind (F p.1) := by
  rw [show ((complete c).bind fun π => F (π u) π) =
      ((complete c).map fun π => (evalPerm π (.forward u), π)).bind fun p => F p.1 p.2 by
    rw [PMF.bind_map]; rfl, ← answer_complete (.forward u) c hc, PMF.bind_bind]
  congr 1
  funext p
  obtain ⟨a, c'⟩ := p
  simp only [PMF.bind_map]
  rfl

/-- The main induction. Along the lazy run of `T` from the cache `c`, if no graph with property
`P` that agrees with `G` on `c` is ever rejected, then the positions seen so far, extended by
`2 q` fresh positions, can be good for `G` only as often as `T` accepts. -/
private theorem toOuterMeasure_good_le [NeZero n] {P : SimpleGraph (Fin n) → Prop}
    (hP : IsInvariant P) (G : SimpleGraph (Fin n)) {T : Tester n} {q : ℕ}
    (hT : ProbOracleComp.IsQueryBounded T q)
    {c : Cache (Fin n)} (hc : CacheValid c)
    (hfalse : ∀ H, P H → Agree G H c → OracleComp.evalWith ⟪H⟫ T false = 0) :
    (complete (posCache c)).toOuterMeasure {σ | Good P G σ (c.length + 2 * q)} ≤
      ((complete c).bind fun π => OracleComp.evalWith ⟪G.comap π⟫ T) true := by
  classical
  induction hT generalizing c with
  | pure b m =>
    simp only [OracleComp.evalWith_pure, PMF.bind_const, PMF.pure_apply]
    cases b with
    | true => exact (Probability.PMF.toOuterMeasure_le_one _ _).trans (by simp)
    | false =>
      simp only [Bool.true_eq_false, ite_false]
      refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
      rw [Set.disjoint_left]
      rintro σ hσ ⟨H, hH, hadj⟩
      have hlen := hc.length_le
      have hσc := mem_support_complete (isPartialBijection_posCache hc) hσ
      obtain ⟨π, hπ⟩ := hc.1
      refine absurd (hfalse (H.comap (π.trans σ.symm)) (hP _ H hH) ?_) (by simp)
      intro e₁ he₁ e₂ he₂
      obtain ⟨i, hi, hi'⟩ := exists_mem_posCache hlen he₁
      obtain ⟨j, hj, hj'⟩ := exists_mem_posCache hlen he₂
      have hσi : σ i = e₁.2 := hσc _ hi'
      have hσj : σ j = e₂.2 := hσc _ hj'
      have h₁ : (π.trans σ.symm) e₁.1 = i := by
        rw [Equiv.trans_apply, hπ e₁ he₁, Equiv.symm_apply_eq]
        exact hσi.symm
      have h₂ : (π.trans σ.symm) e₂.1 = j := by
        rw [Equiv.trans_apply, hπ e₂ he₂, Equiv.symm_apply_eq]
        exact hσj.symm
      rw [comap_adj, h₁, h₂, hadj i j (by omega) (by omega), hσi, hσj]
  | liftBind q cont m hcont ih =>
    rcases q with k | ⟨u, v⟩
    · simp only [Sum.elim_inl, add_zero, OracleComp.evalWith_bind,
        OracleComp.evalWith_query] at hfalse ⊢
      rw [PMF.bind_comm]
      refine Probability.PMF.le_bind_apply_on_support _ fun a ha => ih a hc fun H hH hA => ?_
      exact bind_apply_eq_zero_of_mem_support (hfalse H hH hA) ha
    · simp only [Sum.elim_inr]
      have hR : ((complete c).bind fun π =>
            OracleComp.evalWith ⟪G.comap π⟫ (OracleComp.query (Sum.inr (u, v)) >>= cont)) =
          (answer (.forward u) c).bind fun p₁ => (answer (.forward v) p₁.2).bind fun p₂ =>
            (complete p₂.2).bind fun π =>
              OracleComp.evalWith ⟪G.comap π⟫ (cont (decide (G.Adj p₁.1 p₂.1))) := by
        calc _ = (complete c).bind fun π =>
                OracleComp.evalWith ⟪G.comap π⟫ (cont (decide (G.Adj (π u) (π v)))) := by
              congr 1
              funext π
              rw [OracleComp.evalWith_bind, OracleComp.evalWith_query,
                OracleComp.sumHandler_inr, adjOracle_apply, PMF.pure_bind]
              rfl
          _ = (answer (.forward u) c).bind fun p₁ => (complete p₁.2).bind fun π =>
                OracleComp.evalWith ⟪G.comap π⟫ (cont (decide (G.Adj p₁.1 (π v)))) :=
              complete_bind_eq_answer_bind hc.1 u fun x π =>
                OracleComp.evalWith ⟪G.comap π⟫ (cont (decide (G.Adj x (π v))))
          _ = _ := by
              refine Probability.PMF.bind_congr_on_support _ _ _ fun p₁ hp₁ => ?_
              exact complete_bind_eq_answer_bind (mem_support_answer_forward hc hp₁).1.1 v
                fun y π => OracleComp.evalWith ⟪G.comap π⟫ (cont (decide (G.Adj p₁.1 y)))
      rw [hR, ← answer_bind_complete_posCache hc u]
      refine toOuterMeasure_bind_le_bind_apply _ _ _ _ _ fun p₁ hp₁ => ?_
      obtain ⟨hv₁, hu₁, hsub₁, hlen₁⟩ := mem_support_answer_forward hc hp₁
      rw [← answer_bind_complete_posCache hv₁ v]
      refine toOuterMeasure_bind_le_bind_apply _ _ _ _ _ fun p₂ hp₂ => ?_
      obtain ⟨hv₂, hv₂', hsub₂, hlen₂⟩ := mem_support_answer_forward hv₁ hp₂
      refine le_trans (PMF.toOuterMeasure_mono _ ?_) (ih _ hv₂ ?_)
      · rintro σ ⟨hσ, -⟩
        exact hσ.mono (by omega)
      · intro H hH hA
        have hA' : Agree G H c := fun e₁ he₁ e₂ he₂ =>
          hA e₁ (hsub₂ _ (hsub₁ _ he₁)) e₂ (hsub₂ _ (hsub₁ _ he₂))
        have hadj : H.Adj u v ↔ G.Adj p₁.1 p₂.1 := hA _ (hsub₂ _ hu₁) _ hv₂'
        have h0 := hfalse H hH hA'
        rw [OracleComp.evalWith_bind, OracleComp.evalWith_query] at h0
        have hq : OracleComp.sumHandler ProbComp.unifOracle (adjOracle H) (Sum.inr (u, v)) =
            PMF.pure (decide (G.Adj p₁.1 p₂.1)) :=
          by rw [OracleComp.sumHandler_inr, adjOracle_apply]
             exact congrArg PMF.pure (decide_eq_decide.mpr hadj)
        rw [hq, PMF.pure_bind] at h0
        exact h0

private theorem toOuterMeasure_good_le_one_third [NeZero n] {P : SimpleGraph (Fin n) → Prop}
    (hP : IsInvariant P) {T : Tester n} {ε : ℝ} {q : ℕ} (hT : IsOneSidedTester T P ε q)
    {G : SimpleGraph (Fin n)} (hG : IsFar G P ε) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toOuterMeasure {σ | Good P G σ (2 * q)} ≤
      ENNReal.ofReal (1 / 3) := by
  have h := toOuterMeasure_good_le hP G hT.queryBounded (c := [])
    ⟨isPartialBijection_nil, List.nodup_nil⟩ fun H hH _ => hT.evalWith_false_eq_zero hH
  simp only [posCache, complete_nil, List.length_nil, zero_add] at h
  refine h.trans (Probability.PMF.bind_apply_le_on_support _ fun π _ => ?_)
  have := hT.reject _ (hG.comap hP π)
  rw [acceptProb_eq] at this
  exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) (by norm_num)).2 this

end Soundness

/-! ### The canonical tester theorem -/

private theorem inducedOf_comap_iff_good {n s : ℕ} (hs : s ≤ n) {P : SimpleGraph (Fin n) → Prop}
    (hP : IsInvariant P) (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    InducedOf P (G.comap fun i => σ (Fin.castLE hs i)) ↔ Good P G σ s := by
  constructor
  · rintro ⟨H, hH, ⟨f⟩⟩
    obtain ⟨ρ, hρ⟩ := exists_perm_extend hs f.toEmbedding
    refine ⟨H.comap ρ, hP ρ H hH, fun i j hi hj => ?_⟩
    have hi' : ρ i = f ⟨i.val, hi⟩ := hρ ⟨i.val, hi⟩
    have hj' : ρ j = f ⟨j.val, hj⟩ := hρ ⟨j.val, hj⟩
    rw [comap_adj, hi', hj']
    exact f.map_adj_iff
  · rintro ⟨H, hH, hadj⟩
    exact ⟨H, hH, ⟨⟨Fin.castLEEmb hs, fun {a b} => hadj _ _ a.2 b.2⟩⟩⟩

open Classical in
/-- **Canonical testers**, the one-sided half of [Goldreich and Trevisan, Theorem 2 and
Theorem 4.5][GoldreichTrevisan2003]. A one-sided tester for an invariant property `P` with
proximity `ε` and `q` queries yields the canonical tester with `min (2 q) n` sample vertices and
decision property `InducedOf P`, which is one-sided for `P` with the same proximity and
`(2 q).choose 2` queries. -/
theorem isOneSidedTester_canonicalTester {n : ℕ} {P : SimpleGraph (Fin n) → Prop}
    (hP : IsInvariant P) {T : Tester n} {ε : ℝ} {q : ℕ} (hT : IsOneSidedTester T P ε q) :
    IsOneSidedTester (canonicalTester n (min (2 * q) n) (min_le_right _ _) (InducedOf P)) P ε
      ((2 * q).choose 2) where
  queryBounded := (isQueryBounded_canonicalTester _ _ _ _).mono
    (Nat.choose_le_choose 2 (min_le_left _ _))
  accept := (acceptProb_canonicalTester_eq_one_iff _ P _).2 fun _ h => h
  reject G hG := by
    rw [acceptProb_canonicalTester]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hnone : ∀ H, ¬ P H := fun H hH => by
        have := isFar_iff.mp hG H hH
        have hGH : G = H := SimpleGraph.ext (funext fun i => i.elim0)
        rw [hGH, editDist_self] at this
        simp at this
      have hempty : {σ : Equiv.Perm (Fin 0) |
          InducedOf P (G.comap fun i => σ (Fin.castLE (min_le_right (2 * q) 0) i))} = ∅ := by
        ext σ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨H, hH, -⟩
        exact hnone H hH
      rw [hempty]
      simp
    · have : NeZero n := ⟨hn.ne'⟩
      refine ENNReal.toReal_le_of_le_ofReal (by norm_num)
        ((PMF.toOuterMeasure_mono _ ?_).trans (toOuterMeasure_good_le_one_third hP hT hG))
      rintro σ ⟨hσ, -⟩
      exact Good.of_min ((inducedOf_comap_iff_good _ hP G σ).1 hσ)

open Classical in
/-- **Canonical testers for a family of properties.** If every `P n` is invariant and the family
is one-sided testable with `q ε` queries, then for every `ε > 0` and every `n` the canonical tester
with `min (2 q ε) n` sample vertices and decision property `InducedOf (P n)` is a one-sided tester
for `P n` with `(2 q ε).choose 2` queries [Goldreich and Trevisan,
Theorem 2][GoldreichTrevisan2003]. -/
theorem OneSidedTestable.canonical {P : ∀ n, SimpleGraph (Fin n) → Prop} {q : ℝ → ℕ}
    (hP : ∀ n, IsInvariant (P n)) (hT : OneSidedTestable P q) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    IsOneSidedTester
      (canonicalTester n (min (2 * q ε) n) (min_le_right _ _) (InducedOf (P n))) (P n) ε
      ((2 * q ε).choose 2) := by
  obtain ⟨T, hT⟩ := oneSidedTestable_iff.mp hT ε hε n
  exact isOneSidedTester_canonicalTester (hP n) hT

end Cslib.DenseGraphTesting
