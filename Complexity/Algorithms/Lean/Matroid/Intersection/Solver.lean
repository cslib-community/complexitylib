/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Matroid.Intersection
public import Complexity.Algorithms.Reachability.ShortestWalk
public import Cslib.Foundations.Control.Monad.IsMonadHom
import Complexity.Foundations.Control.Monad.FilterM
import Complexity.Foundations.Data.List.EraseDups

/-!
# An executable matroid intersection algorithm

This module implements the cardinality matroid intersection algorithm of [Schrijver2017],
Section 10.5, for two matroids given by independence tests, and proves it correct. Each phase
builds the exchange digraph `H(M₁, M₂, I)` of the current common independent set `I` by
independence tests: the sources `X₁(I)`, the sinks `X₂(I)`, and the arcs between `I` and the
other candidates (`Cslib.Algorithms.Lean.Matroid.exchTables`). Breadth-first search
(`Cslib.Reachability.findWalk`) then either finds a shortest source-to-sink walk, along which `I`
is augmented, or returns the vertices reachable from the sources, whose complement certifies that
`I` is maximum. The algorithm starts from `∅` and stops after at most `n + 1` phases, where `n` is
the number of distinct candidates.

The independence tests are effectful (`Finset α → m Bool` for a monad `m`), so the same program
runs purely (`Cslib.Algorithms.Lean.Matroid.maxCommonIndep`), and in the query model of
`Complexity.Algorithms.Lean.Query.Matroid.Intersection`, which counts the oracle calls.
Breadth-first search and the bookkeeping on lists are pure host computation and make no test.

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.ExchTables`, `exchTablesM`, `exchTables`: the exchange digraph of
  `I` computed by independence tests.
* `Cslib.Algorithms.Lean.Matroid.exchSearch`: breadth-first search in the exchange digraph.
* `Cslib.Algorithms.Lean.Matroid.maxCommonIndepLoopM`, `maxCommonIndepM`, `maxCommonIndepLoop`,
  `maxCommonIndep`: the augmenting-path algorithm, monadic and pure. The output is a pair `(I, U)`
  of a common independent set and a separator.

## Main results

* `Cslib.Algorithms.Lean.Matroid.augment_of_exchSearch_eq_inl`,
  `Cslib.Algorithms.Lean.Matroid.card_eq_of_exchSearch_eq_inr`: one phase is correct
  ([Schrijver2017], Theorems 10.6 and 10.7).
* `Cslib.Algorithms.Lean.Matroid.maxCommonIndep_spec`: **correctness**: for independence tests
  deciding `M₁` and `M₂`, `maxCommonIndep` returns a maximum common independent subset `I` of the
  candidates and a separator `U` with `I.card = M₁.eRk U + M₂.eRk (E \ U)`
  ([Schrijver2017], Theorem 10.8).
* `Cslib.Algorithms.Lean.Matroid.maxCommonIndepM_pure`, `Cslib.IsMonadHom.map_maxCommonIndepM`:
  the monadic algorithm with pure tests is the pure algorithm, and monad morphisms commute with it.
  The tests are issued through core `List.filterM`; the bridges use `List.filterM_pure` and
  `Cslib.IsMonadHom.map_filterM` from `Complexity.Foundations.Control.Monad.FilterM`.

## References

* [J. Edmonds, *Submodular Functions, Matroids, and Certain Polyhedra*][Edmonds1970]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 10.5
-/

public section

open Cslib (IsMonadHom)
open Cslib.Reachability
open scoped symmDiff

namespace Cslib.Algorithms.Lean.Matroid

/-! ### The exchange digraph -/

/-- The exchange digraph `H(M₁, M₂, I)` of a common independent set `I`, computed by independence
tests ([Schrijver2017], (23) and (24)). Its vertices are the candidates. `sources` and `sinks` list
the candidates `y ∉ I` with `insert y I` independent in `M₁`, resp. `M₂`. `arcs₁` lists the pairs
`(x, y)` with `x ∈ I`, `y ∉ I` and `insert y (I.erase x)` independent in `M₁`, each an arc
`x → y`; `arcs₂` lists those with `insert y (I.erase x)` independent in `M₂`, each an arc
`y → x`. -/
structure ExchTables (α : Type*) where
  /-- The source set `X₁(I)`. -/
  sources : List α
  /-- The sink set `X₂(I)`. -/
  sinks : List α
  /-- The pairs `(x, y)` giving `M₁`-arcs `x → y`. -/
  arcs₁ : List (α × α)
  /-- The pairs `(x, y)` giving `M₂`-arcs `y → x`. -/
  arcs₂ : List (α × α)

namespace ExchTables

variable {α : Type*} [DecidableEq α]

/-- The arc test of the exchange digraph. -/
@[expose] def arc (T : ExchTables α) (u v : α) : Bool :=
  decide ((u, v) ∈ T.arcs₁) || decide ((v, u) ∈ T.arcs₂)

/-- The source test of the exchange digraph. -/
@[expose] def src (T : ExchTables α) (v : α) : Bool := decide (v ∈ T.sources)

/-- The sink test of the exchange digraph. -/
@[expose] def tgt (T : ExchTables α) (v : α) : Bool := decide (v ∈ T.sinks)

theorem arc_eq_true_iff {T : ExchTables α} {u v : α} :
    T.arc u v = true ↔ (u, v) ∈ T.arcs₁ ∨ (v, u) ∈ T.arcs₂ := by
  simp [arc]

theorem src_eq_true_iff {T : ExchTables α} {v : α} : T.src v = true ↔ v ∈ T.sources := by
  simp [src]

theorem tgt_eq_true_iff {T : ExchTables α} {v : α} : T.tgt v = true ↔ v ∈ T.sinks := by
  simp [tgt]

end ExchTables

/-- The pairs `(x, y)` with `x ∈ I` and `y ∉ I` among the candidates `V`, each tested once per
matroid for an exchange arc. -/
@[expose] def exchPairs {α : Type*} [DecidableEq α] (V : List α) (I : Finset α) : List (α × α) :=
  (V.filter (· ∈ I)).flatMap fun x => (V.filter (· ∉ I)).map fun y => (x, y)

/-- The exchange digraph of `I` on the candidates `V`, computed by the effectful independence
tests `indep₁` and `indep₂`: `2 * |V \ I| * (1 + |I|)` tests on duplicate-free `V` with
`I ⊆ V`. -/
@[expose] def exchTablesM {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep₁ indep₂ : Finset α → m Bool) (V : List α) (I : Finset α) : m (ExchTables α) := do
  let sources ← (V.filter (· ∉ I)).filterM fun y => indep₁ (insert y I)
  let sinks ← (V.filter (· ∉ I)).filterM fun y => indep₂ (insert y I)
  let arcs₁ ← (exchPairs V I).filterM fun e => indep₁ (insert e.2 (I.erase e.1))
  let arcs₂ ← (exchPairs V I).filterM fun e => indep₂ (insert e.2 (I.erase e.1))
  pure ⟨sources, sinks, arcs₁, arcs₂⟩

/-- The exchange digraph of `I` on the candidates `V`, computed by Boolean independence tests. -/
@[expose] def exchTables {α : Type*} [DecidableEq α] (indep₁ indep₂ : Finset α → Bool)
    (V : List α) (I : Finset α) : ExchTables α :=
  ⟨(V.filter (· ∉ I)).filter (fun y => indep₁ (insert y I)),
    (V.filter (· ∉ I)).filter (fun y => indep₂ (insert y I)),
    (exchPairs V I).filter (fun e => indep₁ (insert e.2 (I.erase e.1))),
    (exchPairs V I).filter (fun e => indep₂ (insert e.2 (I.erase e.1)))⟩

/-- Breadth-first search in the exchange digraph `T` on the candidates `V`: a shortest
source-to-sink walk, or the vertices reachable from the sources. -/
@[expose] def exchSearch {α : Type*} [DecidableEq α] (V : List α) (T : ExchTables α) :
    List α ⊕ List α :=
  findWalk V T.arc T.src T.tgt

/-! ### The augmenting-path algorithm -/

/-- At most `fuel` phases of the augmenting-path algorithm on the candidates `V` from `I`, with
effectful independence tests. A phase augments `I` along a shortest walk, or stops with `I` and
the separator `U`: the candidates not reachable from the sources. -/
@[expose] def maxCommonIndepLoopM {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep₁ indep₂ : Finset α → m Bool) (V : List α) :
    ℕ → Finset α → m (Finset α × Finset α)
  | 0, I => pure (I, ∅)
  | fuel + 1, I => do
    let T ← exchTablesM indep₁ indep₂ V I
    match exchSearch V T with
    | .inl p => maxCommonIndepLoopM indep₁ indep₂ V fuel (I ∆ p.toFinset)
    | .inr R => pure (I, V.toFinset \ R.toFinset)

/-- **Matroid intersection** with effectful independence tests: from `∅`, at most `n + 1` phases
on the `n` distinct candidates of `es`. Returns `(I, U)`. -/
@[expose] def maxCommonIndepM {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep₁ indep₂ : Finset α → m Bool) (es : List α) : m (Finset α × Finset α) :=
  maxCommonIndepLoopM indep₁ indep₂ es.eraseDups (es.eraseDups.length + 1) ∅

/-- At most `fuel` phases of the augmenting-path algorithm with Boolean independence tests. -/
@[expose] def maxCommonIndepLoop {α : Type*} [DecidableEq α] (indep₁ indep₂ : Finset α → Bool)
    (V : List α) : ℕ → Finset α → Finset α × Finset α
  | 0, I => (I, ∅)
  | fuel + 1, I =>
    match exchSearch V (exchTables indep₁ indep₂ V I) with
    | .inl p => maxCommonIndepLoop indep₁ indep₂ V fuel (I ∆ p.toFinset)
    | .inr R => (I, V.toFinset \ R.toFinset)

/-- **Matroid intersection** with Boolean independence tests: a maximum common independent subset
`I` of the candidates `es` and a separator `U` (`maxCommonIndep_spec`). -/
@[expose] def maxCommonIndep {α : Type*} [DecidableEq α] (indep₁ indep₂ : Finset α → Bool)
    (es : List α) : Finset α × Finset α :=
  maxCommonIndepLoop indep₁ indep₂ es.eraseDups (es.eraseDups.length + 1) ∅

/-! ### Pure runs and monad morphisms -/

section Bridges

variable {α : Type} [DecidableEq α] {m n : Type → Type*} [Monad m] [Monad n]

@[simp] theorem exchTablesM_pure [LawfulMonad m] (indep₁ indep₂ : Finset α → Bool) (V : List α)
    (I : Finset α) :
    exchTablesM (fun S => (pure (indep₁ S) : m Bool)) (fun S => pure (indep₂ S)) V I =
      pure (exchTables indep₁ indep₂ V I) := by
  simp only [exchTablesM, exchTables]
  rw [List.filterM_pure (p := fun y => indep₁ (insert y I)),
    List.filterM_pure (p := fun y => indep₂ (insert y I)),
    List.filterM_pure (p := fun e : α × α => indep₁ (insert e.2 (I.erase e.1))),
    List.filterM_pure (p := fun e : α × α => indep₂ (insert e.2 (I.erase e.1)))]
  simp only [pure_bind]

@[simp] theorem maxCommonIndepLoopM_pure [LawfulMonad m] (indep₁ indep₂ : Finset α → Bool)
    (V : List α) (fuel : ℕ) (I : Finset α) :
    maxCommonIndepLoopM (fun S => (pure (indep₁ S) : m Bool)) (fun S => pure (indep₂ S)) V
        fuel I =
      pure (maxCommonIndepLoop indep₁ indep₂ V fuel I) := by
  induction fuel generalizing I with
  | zero => rfl
  | succ fuel ih =>
    simp only [maxCommonIndepLoopM, maxCommonIndepLoop, exchTablesM_pure, pure_bind]
    rcases exchSearch V (exchTables indep₁ indep₂ V I) with p | R
    · exact ih _
    · rfl

@[simp] theorem maxCommonIndepM_pure [LawfulMonad m] (indep₁ indep₂ : Finset α → Bool)
    (es : List α) :
    maxCommonIndepM (fun S => (pure (indep₁ S) : m Bool)) (fun S => pure (indep₂ S)) es =
      pure (maxCommonIndep indep₁ indep₂ es) :=
  maxCommonIndepLoopM_pure indep₁ indep₂ _ _ _

theorem _root_.Cslib.IsMonadHom.map_exchTablesM {f : {γ : Type} → m γ → n γ}
    (hf : IsMonadHom m n f) (indep₁ indep₂ : Finset α → m Bool) (V : List α) (I : Finset α) :
    f (exchTablesM indep₁ indep₂ V I) =
      exchTablesM (fun S => f (indep₁ S)) (fun S => f (indep₂ S)) V I := by
  simp only [exchTablesM, hf.map_bind, hf.map_filterM, hf.map_pure]

theorem _root_.Cslib.IsMonadHom.map_maxCommonIndepLoopM {f : {γ : Type} → m γ → n γ}
    (hf : IsMonadHom m n f) (indep₁ indep₂ : Finset α → m Bool) (V : List α) (fuel : ℕ)
    (I : Finset α) :
    f (maxCommonIndepLoopM indep₁ indep₂ V fuel I) =
      maxCommonIndepLoopM (fun S => f (indep₁ S)) (fun S => f (indep₂ S)) V fuel I := by
  induction fuel generalizing I with
  | zero => exact hf.map_pure _
  | succ fuel ih =>
    simp only [maxCommonIndepLoopM, hf.map_bind, hf.map_exchTablesM]
    congr 1
    funext T
    split
    · exact ih _
    · exact hf.map_pure _

theorem _root_.Cslib.IsMonadHom.map_maxCommonIndepM {f : {γ : Type} → m γ → n γ}
    (hf : IsMonadHom m n f) (indep₁ indep₂ : Finset α → m Bool) (es : List α) :
    f (maxCommonIndepM indep₁ indep₂ es) =
      maxCommonIndepM (fun S => f (indep₁ S)) (fun S => f (indep₂ S)) es :=
  hf.map_maxCommonIndepLoopM indep₁ indep₂ _ _ _

end Bridges

/-! ### Correctness -/

section Correctness

variable {α : Type*} [DecidableEq α] {M₁ M₂ : Matroid α} {indep₁ indep₂ : Finset α → Bool}

theorem mem_exchPairs {V : List α} {I : Finset α} {x y : α} :
    (x, y) ∈ exchPairs V I ↔ x ∈ V ∧ x ∈ I ∧ y ∈ V ∧ y ∉ I := by
  simp [exchPairs, and_assoc]

theorem length_exchPairs (V : List α) (I : Finset α) :
    (exchPairs V I).length = (V.filter (· ∈ I)).length * (V.filter (· ∉ I)).length := by
  simp [exchPairs, List.length_flatMap]

private theorem src_exchTables_iff (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    {V : List α} {I : Finset α} {v : α} :
    (exchTables indep₁ indep₂ V I).src v = true ↔ IsExchSource M₁ V.toFinset I v := by
  rw [ExchTables.src_eq_true_iff]
  simp only [exchTables, List.mem_filter, decide_eq_true_eq, h₁, IsExchSource, Finset.mem_sdiff,
    List.mem_toFinset]

private theorem tgt_exchTables_iff (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α))
    {V : List α} {I : Finset α} {v : α} :
    (exchTables indep₁ indep₂ V I).tgt v = true ↔ IsExchSink M₂ V.toFinset I v := by
  rw [ExchTables.tgt_eq_true_iff]
  simp only [exchTables, List.mem_filter, decide_eq_true_eq, h₂, IsExchSink, Finset.mem_sdiff,
    List.mem_toFinset]

private theorem arc_exchTables_iff (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) {V : List α} {I : Finset α}
    (hIV : I ⊆ V.toFinset) {u v : α} :
    (exchTables indep₁ indep₂ V I).arc u v = true ↔ IsExchArc M₁ M₂ V.toFinset I u v := by
  have hI : ∀ x ∈ I, x ∈ V := fun x hx => List.mem_toFinset.mp (hIV hx)
  rw [ExchTables.arc_eq_true_iff]
  simp only [exchTables, List.mem_filter, mem_exchPairs, h₁, h₂, IsExchArc, Finset.mem_sdiff,
    List.mem_toFinset]
  constructor
  · rintro (⟨⟨-, hu, hv, hvI⟩, hind⟩ | ⟨⟨-, hv, hu, huI⟩, hind⟩)
    · exact .inl ⟨hu, ⟨hv, hvI⟩, hind⟩
    · exact .inr ⟨⟨hu, huI⟩, hv, hind⟩
  · rintro (⟨hu, ⟨hv, hvI⟩, hind⟩ | ⟨⟨hu, huI⟩, hv, hind⟩)
    · exact .inl ⟨⟨hI u hu, hu, hv, hvI⟩, hind⟩
    · exact .inr ⟨⟨hI v hv, hv, hu, huI⟩, hind⟩

private theorem isSrcTgtWalk_exchTables_iff (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) {V : List α} {I : Finset α}
    (hIV : I ⊆ V.toFinset) {p : List α} :
    IsSrcTgtWalk V (exchTables indep₁ indep₂ V I).arc (exchTables indep₁ indep₂ V I).src
        (exchTables indep₁ indep₂ V I).tgt p ↔
      IsExchAugWalk M₁ M₂ V.toFinset I p := by
  have harc : (fun u v => (exchTables indep₁ indep₂ V I).arc u v = true) =
      IsExchArc M₁ M₂ V.toFinset I := by
    funext u v
    exact propext (arc_exchTables_iff h₁ h₂ hIV)
  simp only [IsSrcTgtWalk, IsExchAugWalk, IsWalk, IsExchWalk, harc, src_exchTables_iff h₁,
    tgt_exchTables_iff h₂, List.mem_toFinset]

/-- **One phase, augmenting case** ([Schrijver2017], Theorem 10.6): if the search finds a walk `p`
in the exchange digraph of `I ⊆ V`, then `I ∆ p` is a common independent subset of `V` with one more
element. -/
theorem augment_of_exchSearch_eq_inl (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) {V : List α} {I : Finset α}
    (hIV : I ⊆ V.toFinset) {p : List α}
    (hp : exchSearch V (exchTables indep₁ indep₂ V I) = .inl p) :
    I ∆ p.toFinset ⊆ V.toFinset ∧ IsCommonIndep M₁ M₂ (I ∆ p.toFinset) ∧
      (I ∆ p.toFinset).card = I.card + 1 := by
  obtain ⟨hwalk, hmin⟩ := isShortestSrcTgtWalk_of_findWalk_eq_inl hp
  refine IsShortestExchAugWalk.augment ⟨(isSrcTgtWalk_exchTables_iff h₁ h₂ hIV).mp hwalk,
    fun q hq => hmin q ((isSrcTgtWalk_exchTables_iff h₁ h₂ hIV).mpr hq)⟩ hIV

/-- **One phase, stopping case** ([Schrijver2017], Theorem 10.7): if the search in the exchange
digraph of a common independent set `I ⊆ V` returns the reachable vertices `R`, then the
unreachable candidates `U = V \ R` satisfy `I.card = M₁.eRk U + M₂.eRk (V \ U)`. -/
theorem card_eq_of_exchSearch_eq_inr (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) {V : List α} {I : Finset α}
    (hIV : I ⊆ V.toFinset) (hI : IsCommonIndep M₁ M₂ I) {R : List α}
    (hR : exchSearch V (exchTables indep₁ indep₂ V I) = .inr R) :
    (I.card : ℕ∞) = M₁.eRk ((V.toFinset \ R.toFinset : Finset α) : Set α) +
      M₂.eRk ((V.toFinset \ (V.toFinset \ R.toFinset) : Finset α) : Set α) := by
  obtain ⟨hRV, hsrc, hcl, htgt⟩ := isSrcTgtSeparator_of_findWalk_eq_inr hR
  have hRV' : R.toFinset ⊆ V.toFinset := fun v hv =>
    List.mem_toFinset.mpr (hRV v (List.mem_toFinset.mp hv))
  rw [Finset.sdiff_sdiff_eq_self hRV']
  refine card_eq_eRk_add_eRk_of_closed hIV hI ?_ ?_ ?_ ?_
  · intro y hy hind
    obtain ⟨hyV, hyI⟩ := Finset.mem_sdiff.mp hy
    exact List.mem_toFinset.mpr (hsrc y (List.mem_toFinset.mp hyV)
      ((src_exchTables_iff h₁).mpr ⟨hy, hind⟩))
  · intro y hy hind
    obtain ⟨hyR, hyI⟩ := Finset.mem_sdiff.mp hy
    have hyV : y ∈ V.toFinset := hRV' hyR
    have := htgt y (List.mem_toFinset.mp hyR)
    rw [← Bool.not_eq_true, tgt_exchTables_iff h₂] at this
    exact this ⟨Finset.mem_sdiff.mpr ⟨hyV, hyI⟩, hind⟩
  · intro x hx y hy hind
    obtain ⟨hxR, hxI⟩ := Finset.mem_inter.mp hx
    exact List.mem_toFinset.mpr (hcl x (List.mem_toFinset.mp hxR) y
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hy).1)
      ((arc_exchTables_iff h₁ h₂ hIV).mpr (.inl ⟨hxI, hy, hind⟩)))
  · intro y hy x hx hind
    obtain ⟨hyR, hyI⟩ := Finset.mem_sdiff.mp hy
    exact List.mem_toFinset.mpr (hcl y (List.mem_toFinset.mp hyR) x
      (List.mem_toFinset.mp (hIV hx))
      ((arc_exchTables_iff h₁ h₂ hIV).mpr
        (.inr ⟨Finset.mem_sdiff.mpr ⟨hRV' hyR, hyI⟩, hx, hind⟩)))

private theorem maxCommonIndepLoop_spec (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) (V : List α) :
    ∀ (fuel : ℕ) (I : Finset α), I ⊆ V.toFinset → IsCommonIndep M₁ M₂ I →
      V.toFinset.card - I.card < fuel →
      IsMaxCommonIndep M₁ M₂ V.toFinset (maxCommonIndepLoop indep₁ indep₂ V fuel I).1 ∧
        (maxCommonIndepLoop indep₁ indep₂ V fuel I).2 ⊆ V.toFinset ∧
        ((maxCommonIndepLoop indep₁ indep₂ V fuel I).1.card : ℕ∞) =
          M₁.eRk ((maxCommonIndepLoop indep₁ indep₂ V fuel I).2 : Set α) +
            M₂.eRk ((V.toFinset \ (maxCommonIndepLoop indep₁ indep₂ V fuel I).2 : Finset α) :
              Set α) := by
  intro fuel
  induction fuel with
  | zero => intro I _ _ h; omega
  | succ fuel ih =>
    intro I hIV hI hfuel
    rcases hs : exchSearch V (exchTables indep₁ indep₂ V I) with p | R
    · obtain ⟨hI'V, hI', hcard⟩ := augment_of_exchSearch_eq_inl h₁ h₂ hIV hs
      have hle := Finset.card_le_card hI'V
      simp only [maxCommonIndepLoop, hs]
      exact ih _ hI'V hI' (by omega)
    · have heq := card_eq_of_exchSearch_eq_inr h₁ h₂ hIV hI hs
      simp only [maxCommonIndepLoop, hs]
      exact ⟨isMaxCommonIndep_of_card_eq_eRk_add_eRk hIV hI heq, Finset.sdiff_subset, heq⟩

/-- **Correctness of matroid intersection** ([Schrijver2017], Theorem 10.8; [Edmonds1970]): if
`indep₁` and `indep₂` decide independence in `M₁` and `M₂`, then `maxCommonIndep indep₁ indep₂ es`
is a pair `(I, U)` such that `I` is a maximum common independent subset of the candidates
`E = es.toFinset`, `U ⊆ E`, and `I.card = M₁.eRk U + M₂.eRk (E \ U)`. By weak duality the
separator `U` certifies maximality, and it attains the minimum in Edmonds' min–max theorem. -/
theorem maxCommonIndep_spec (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) (es : List α) :
    IsMaxCommonIndep M₁ M₂ es.toFinset (maxCommonIndep indep₁ indep₂ es).1 ∧
      (maxCommonIndep indep₁ indep₂ es).2 ⊆ es.toFinset ∧
      ((maxCommonIndep indep₁ indep₂ es).1.card : ℕ∞) =
        M₁.eRk ((maxCommonIndep indep₁ indep₂ es).2 : Set α) +
          M₂.eRk ((es.toFinset \ (maxCommonIndep indep₁ indep₂ es).2 : Finset α) : Set α) := by
  have h := maxCommonIndepLoop_spec h₁ h₂ es.eraseDups (es.eraseDups.length + 1) ∅
    (Finset.empty_subset _) (isCommonIndep_empty M₁ M₂)
    (by rw [List.length_eraseDups, List.toFinset_eraseDups]; omega)
  rwa [List.toFinset_eraseDups] at h

end Correctness

end Cslib.Algorithms.Lean.Matroid
