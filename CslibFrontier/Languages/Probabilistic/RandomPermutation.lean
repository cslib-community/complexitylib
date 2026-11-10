/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.UntilBad
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lazy sampling of random permutations and the PRP/PRF switching lemma

A bidirectional permutation oracle (`PermOracleSpec α`) answers forward queries (`.forward x`) and
inverse queries (`.inverse y`) on a type `α`. Over an association-list cache
`Cache α = List (α × α)`, we provide two lazy stateful samplers on finite nonempty types together
with polymorphic bidirectional query deduplication over arbitrary `[DecidableEq α]`:

1. **Exact without-replacement lazy permutation (`RandomPermutation.answer`)**: on a cache hit,
   return the recorded image or preimage; on a cache miss, sample uniformly from the remaining
   unused range elements (`unusedRange cache`) for a forward query or from the remaining unused
   domain elements (`unusedDomain cache`) for an inverse query. Using
   `OracleComp.run_interpret_simulation_of_invariant` and uniform completion `complete` over the
   set `extPerms cache` of permutations extending the partial bijection, we prove that adaptive
   execution against `answer` followed by `complete` has the exact same joint distribution as
   sampling `π ← PMF.uniformOfFintype (Equiv.Perm α)` eagerly (`run_interpret_answer_complete`,
   `uniform_interpret_eq_lazy`).
2. **Forgetful with-replacement lazy permutation (`RandomPermutation.forgetfulAnswer`,
   [BonehShoup2023], Section 4.7)**: on a cache miss, sample uniformly from all of `α` without
   domain or range exclusion. By coupling `answer` and `forgetfulAnswer` via resampling and
   `OracleComp.IdenticalUntilBad`, any `Q`-query adaptive distinguisher has distinguishing
   advantage at most `Q.choose 2 / |α|` between a uniformly random permutation
   `π ← PMF.uniformOfFintype (Equiv.Perm α)` and `forgetfulAnswer`
   (`abs_sub_uniformPerm_forgetful_le`). On forward-only programs (`liftForward`),
   `forgetfulAnswer` coincides with `memoize (fun _ => PMF.uniformOfFintype α)` and therefore with
   a uniformly random function `f ← PMF.uniformOfFintype (α → α)`, yielding the classical
   **PRP/PRF switching lemma** (`abs_sub_uniformPerm_uniformFunc_le`, [BonehShoup2023],
   Section 4.4, Theorem 4.4).
3. **Bidirectional query deduplication (`RandomPermutation.bidirDedupStep`,
   `RandomPermutation.bidirDedup`)**: for any `[DecidableEq α]`, wrap a bidirectional oracle
   program so that forward hits in `dom(cache)` and inverse hits in `ran(cache)` are answered from
   `cache` without invoking the underlying oracle, preserving the output distribution against
   `evalPerm π` (`map_fst_interpret_bidirDedup_evalPerm`), preserving query bounds
   (`isQueryBounded_bidirDedup`), recording non-repeating underlying queries and the exact
   reverse-chronological transcript (`nodup_transcript_of_mem_support_withTranscript_bidirDedup`,
   `cache_eq_of_mem_support_withTranscript_bidirDedup`), and maintaining pairwise-distinct domain
   and range entries under `evalPerm π` (`agreesWith_and_pairwise_of_mem_support_bidirDedup`).

## Main definitions

* `Cslib.RandomPermutation.PermQuery`, `PermQuery.ofBoolProd`, `PermQuery.toCacheEntry`,
  `PermOracleSpec`, `evalPerm`, `liftForward`, `liftBoolProd`: bidirectional permutation queries,
  oracle specification, deterministic evaluation, and query liftings.
* `Cslib.RandomPermutation.Cache`, `invLookup`, `AgreesWith`, `IsPartialBijection`, `extPerms`,
  `unusedDomain`, `unusedRange`: partial bijection caches and extension sets.
* `Cslib.RandomPermutation.bidirDedupStep`, `bidirDedup`: stateful bidirectional query
  deduplication over a partial-permutation cache.
* `Cslib.RandomPermutation.answer`, `complete`, `forgetfulAnswer`: exact and forgetful lazy
  bidirectional permutation samplers and uniform completion.

## Main results

* `Cslib.RandomPermutation.map_fst_interpret_bidirDedupStep_evalPerm`,
  `Cslib.RandomPermutation.map_fst_interpret_bidirDedup_evalPerm`,
  `Cslib.RandomPermutation.isQueryBounded_bidirDedupStep`,
  `Cslib.RandomPermutation.isQueryBounded_bidirDedup`,
  `Cslib.RandomPermutation.cache_eq_of_mem_support_withTranscript_bidirDedup`,
  `Cslib.RandomPermutation.nodup_transcript_of_mem_support_withTranscript_bidirDedup`,
  `Cslib.RandomPermutation.length_cache_le_of_mem_support_bidirDedup`,
  `Cslib.RandomPermutation.agreesWith_and_pairwise_of_mem_support_bidirDedup`,
  `Cslib.RandomPermutation.interpret_bidirDedup_uniformOfFintype`: exact `evalPerm` equivalence,
  query-bound preservation, transcript-cache provenance and query non-repetition, cache-length and
  pairwise-uniqueness invariants, and `forgetfulAnswer` correspondence for bidirectional query
  deduplication.
* `Cslib.RandomPermutation.answer_complete`,
  `Cslib.RandomPermutation.run_interpret_answer_complete`,
  `Cslib.RandomPermutation.uniform_interpret_eq_lazy`: exact eager/lazy equivalence for
  bidirectional random permutations.
* `Cslib.RandomPermutation.toOuterMeasure_bad_choose_two_le`: quadratic union bound
  `(n * size s + n.choose 2) * δ` for bad events with linearly growing step probability.
* `Cslib.RandomPermutation.uniformPerm_bind_apply_le_forgetful`,
  `Cslib.RandomPermutation.forgetfulAnswer_bind_apply_le_uniformPerm`,
  `Cslib.RandomPermutation.toOuterMeasure_forgetfulAnswer_le_pairwise_and_length_le_add`,
  `Cslib.RandomPermutation.abs_sub_uniformPerm_forgetful_le`: bidirectional random-permutation
  switching bounds (`Q.choose 2 / |α|`).
* `Cslib.RandomPermutation.abs_sub_uniformPerm_uniformFunc_le`: the PRP/PRF switching lemma
  ([BonehShoup2023], Section 4.4, Theorem 4.4).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 4.4 and 4.7 (Theorems 4.4 and 4.7).
-/

@[expose] public section

namespace Cslib.RandomPermutation

open Probability OracleComp
open scoped ENNReal NNReal BigOperators

/-! ### Bidirectional permutation query interface -/

/-- A bidirectional query to a permutation on `α`: either evaluate in the forward direction or
evaluate the inverse permutation. -/
inductive PermQuery (α : Type) where
  /-- Forward query `x ↦ π(x)`. -/
  | forward (x : α)
  /-- Inverse query `y ↦ π⁻¹(y)`. -/
  | inverse (y : α)
  deriving DecidableEq

/-- The oracle specification of a bidirectional permutation on `α`. -/
abbrev PermOracleSpec (α : Type) : OracleSpec (PermQuery α) :=
  fun _ => α

/-- Deterministically answer a bidirectional permutation query using `π : Equiv.Perm α`. -/
def evalPerm {α : Type} (π : Equiv.Perm α) : PermQuery α → α
  | .forward x => π x
  | .inverse y => π.symm y

/-- Evaluating `evalPerm π` on a forward query `.forward x` applies `π` to `x`. -/
@[simp] theorem evalPerm_forward {α : Type} (π : Equiv.Perm α) (x : α) :
    evalPerm π (.forward x) = π x := rfl

/-- Evaluating `evalPerm π` on an inverse query `.inverse y` applies `π.symm` to `y`. -/
@[simp] theorem evalPerm_inverse {α : Type} (π : Equiv.Perm α) (y : α) :
    evalPerm π (.inverse y) = π.symm y := rfl

/-- Lift a forward-only oracle program into a bidirectional permutation oracle program. -/
def liftForward {α β : Type} (program : OracleComp (fun _ : α => α) β) :
    OracleComp (PermOracleSpec α) β :=
  OracleComp.interpret (fun x => OracleComp.query (spec := PermOracleSpec α) (.forward x)) program

/-- Interpreting `liftForward program` against `evalPerm π` is interpreting `program` against
`π`. -/
theorem interpret_evalPerm_liftForward {α β : Type} (π : Equiv.Perm α)
    (program : OracleComp (fun _ : α => α) β) :
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (liftForward program) =
      OracleComp.interpret (fun x => PMF.pure (π x)) program := by
  rw [liftForward, OracleComp.interpret_interpret]
  simp

/-- Lifting a forward-only program preserves query bounds. -/
theorem isQueryBounded_liftForward {α β : Type} {program : OracleComp (fun _ : α => α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) : IsQueryBounded (liftForward program) Q := by
  induction hQ with
  | pure a n => exact IsCostBounded.pure a n
  | liftBind x cont n _ ih =>
    change IsQueryBounded (OracleComp.query (spec := PermOracleSpec α) (.forward x) >>=
      fun y => liftForward (cont y)) (n + 1)
    simpa [Nat.add_comm] using
      (IsCostBounded.query (spec := PermOracleSpec α) (.forward x)).bind ih

/-- Convert a boolean-tagged query `(false, x)` (forward) or `(true, y)` (inverse) into a
`PermQuery α`. -/
def PermQuery.ofBoolProd {α : Type} : Bool × α → PermQuery α
  | (false, x) => .forward x
  | (true, y) => .inverse y

/-- Tag `false` converts `(false, x)` into the forward query `.forward x`. -/
@[simp] theorem PermQuery.ofBoolProd_false {α : Type} (x : α) :
    PermQuery.ofBoolProd (false, x) = .forward x := rfl

/-- Tag `true` converts `(true, y)` into the inverse query `.inverse y`. -/
@[simp] theorem PermQuery.ofBoolProd_true {α : Type} (y : α) :
    PermQuery.ofBoolProd (true, y) = .inverse y := rfl

/-- Lift a `Bool × α` bidirectional oracle program into a `PermOracleSpec α` program. -/
def liftBoolProd {α β : Type} (program : OracleComp (fun _ : Bool × α => α) β) :
    OracleComp (PermOracleSpec α) β :=
  OracleComp.interpret
    (fun q => OracleComp.query (spec := PermOracleSpec α) (PermQuery.ofBoolProd q)) program

/-- Lifting a `Bool × α` program preserves query bounds. -/
theorem isQueryBounded_liftBoolProd {α β : Type}
    {program : OracleComp (fun _ : Bool × α => α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) : IsQueryBounded (liftBoolProd program) Q := by
  induction hQ with
  | pure a n => exact IsCostBounded.pure a n
  | liftBind q cont n _ ih =>
    change IsQueryBounded
      (OracleComp.query (spec := PermOracleSpec α) (PermQuery.ofBoolProd q) >>=
        fun y => liftBoolProd (cont y)) (n + 1)
    simpa [Nat.add_comm] using
      (IsCostBounded.query (spec := PermOracleSpec α) (PermQuery.ofBoolProd q)).bind ih

/-- Orient a bidirectional query-answer pair `⟨q, a⟩` into an `(input, output)` cache entry:
`⟨.forward x, y⟩ ↦ (x, y)` and `⟨.inverse y, x⟩ ↦ (x, y)`. -/
def PermQuery.toCacheEntry {α : Type} : (q : PermQuery α) × PermOracleSpec α q → α × α
  | ⟨.forward x, y⟩ => (x, y)
  | ⟨.inverse y, x⟩ => (x, y)

/-- A forward query-answer pair `⟨.forward x, y⟩` records the cache entry `(x, y)`. -/
@[simp] theorem PermQuery.toCacheEntry_forward {α : Type} (x y : α) :
    PermQuery.toCacheEntry ⟨.forward x, y⟩ = (x, y) := rfl

/-- An inverse query-answer pair `⟨.inverse y, x⟩` records the cache entry `(x, y)`. -/
@[simp] theorem PermQuery.toCacheEntry_inverse {α : Type} (y x : α) :
    PermQuery.toCacheEntry ⟨.inverse y, x⟩ = (x, y) := rfl

/-! ### Partial bijection cache and lookup lemmas -/

/-- A partial permutation table stored as a list of input-output pairs `(x, y)`. -/
abbrev Cache (α : Type) := List (α × α)

variable {α : Type} [DecidableEq α]

/-- Lookup the preimage `x` of `y` in `cache` by searching `(y, x)` in `cache.map Prod.swap`. -/
def invLookup (cache : Cache α) (y : α) : Option α :=
  (cache.map Prod.swap).lookup y

/-- Inverse lookup in the empty cache returns `none`. -/
@[simp] theorem invLookup_nil (y : α) : invLookup ([] : Cache α) y = none := rfl

/-- Unfolding `invLookup` on a non-empty cache `e :: cache`. -/
theorem invLookup_cons (e : α × α) (cache : Cache α) (y : α) :
    invLookup (e :: cache) y =
      match y == e.2 with
      | true => some e.1
      | false => invLookup cache y := rfl

/-- If `cache.lookup x = some y`, then the pair `(x, y)` belongs to `cache`. -/
theorem mem_of_lookup_eq_some {cache : Cache α} {x y : α} (h : cache.lookup x = some y) :
    (x, y) ∈ cache := by
  obtain ⟨_, _, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- If `invLookup cache y = some x`, then the pair `(x, y)` belongs to `cache`. -/
theorem mem_of_invLookup_eq_some {cache : Cache α} {y x : α} (h : invLookup cache y = some x) :
    (x, y) ∈ cache := by
  simpa using mem_of_lookup_eq_some h

/-- Forward lookup of `x` in `cache` returns `none` iff no entry in `cache` has first component
`x`. -/
theorem lookup_eq_none_iff {cache : Cache α} {x : α} :
    cache.lookup x = none ↔ ∀ e ∈ cache, e.1 ≠ x := by
  simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_comm]

/-- Inverse lookup of `y` in `cache` returns `none` iff no entry in `cache` has second component
`y`. -/
theorem invLookup_eq_none_iff {cache : Cache α} {y : α} :
    invLookup cache y = none ↔ ∀ e ∈ cache, e.2 ≠ y := by
  simp only [invLookup, List.lookup_eq_none_iff, bne_iff_ne, ne_comm, List.forall_mem_map,
    Prod.fst_swap]

/-- A permutation `π : Equiv.Perm α` agrees with `cache` if `π e.1 = e.2` for all `e ∈ cache`. -/
def AgreesWith (cache : Cache α) (π : Equiv.Perm α) : Prop :=
  ∀ e ∈ cache, π e.1 = e.2

/-- Decidability of `AgreesWith cache π`. -/
instance decidableAgreesWith (cache : Cache α) (π : Equiv.Perm α) :
    Decidable (AgreesWith cache π) :=
  inferInstanceAs (Decidable (∀ e ∈ cache, π e.1 = e.2))

omit [DecidableEq α] in
/-- Every permutation agrees with the empty cache. -/
@[simp] theorem agreesWith_nil (π : Equiv.Perm α) : AgreesWith ([] : Cache α) π :=
  fun _ h => False.elim (List.not_mem_nil h)

omit [DecidableEq α] in
/-- A permutation `π` agrees with `e :: cache` iff `π e.1 = e.2` and `π` agrees with `cache`. -/
@[simp] theorem agreesWith_cons (e : α × α) (cache : Cache α) (π : Equiv.Perm α) :
    AgreesWith (e :: cache) π ↔ π e.1 = e.2 ∧ AgreesWith cache π :=
  List.forall_mem_cons

/-- If `π` agrees with `cache` and `cache.lookup x = some y`, then `π x = y`. -/
theorem AgreesWith.apply_of_lookup_eq_some {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {x y : α} (h : cache.lookup x = some y) :
    π x = y :=
  hπ (x, y) (mem_of_lookup_eq_some h)

/-- If `π` agrees with `cache` and `invLookup cache y = some x`, then `π.symm y = x`. -/
theorem AgreesWith.symm_apply_of_invLookup_eq_some {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {y x : α} (h : invLookup cache y = some x) :
    π.symm y = x := by
  have hxy := hπ (x, y) (mem_of_invLookup_eq_some h)
  exact π.symm_apply_eq.mpr hxy.symm

/-- If `π` agrees with `cache` and `x` is not in the domain of `cache`, then `π x` is not in the
range of `cache`. -/
theorem AgreesWith.invLookup_apply_eq_none {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {x : α} (hx : cache.lookup x = none) :
    invLookup cache (π x) = none := by
  rw [invLookup_eq_none_iff]
  intro e he heq
  have h1 : π e.1 = π x := (hπ e he).trans heq
  exact lookup_eq_none_iff.mp hx e he (π.injective h1)

/-- If `π` agrees with `cache` and `y` is not in the range of `cache`, then `π.symm y` is not in
the domain of `cache`. -/
theorem AgreesWith.lookup_symm_apply_eq_none {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {y : α} (hy : invLookup cache y = none) :
    cache.lookup (π.symm y) = none := by
  rw [lookup_eq_none_iff]
  intro e he heq
  have h1 : e.2 = y := by
    rw [← hπ e he, heq, Equiv.apply_symm_apply]
  exact invLookup_eq_none_iff.mp hy e he h1

/-- Post-composing a permutation agreeing with `cache` by `Equiv.swap (π x) y` extends agreement
to `(x, y) :: cache` when `x` and `y` are fresh. -/
theorem AgreesWith.trans_swap_of_lookup_eq_none {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {x y : α} (hx : cache.lookup x = none)
    (hy : invLookup cache y = none) :
    AgreesWith ((x, y) :: cache) (π.trans (Equiv.swap (π x) y)) := by
  rw [agreesWith_cons]
  refine ⟨by simp, fun e he => ?_⟩
  have hne1 : e.2 ≠ π x := by
    rw [← hπ e he]
    exact fun h => lookup_eq_none_iff.mp hx e he (π.injective h)
  have hne2 : e.2 ≠ y := invLookup_eq_none_iff.mp hy e he
  simp [hπ e he, Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- Pre-composing a permutation agreeing with `cache` by `Equiv.swap (π.symm y) x` extends
agreement to `(x, y) :: cache` when `x` and `y` are fresh. -/
theorem AgreesWith.swap_trans_of_invLookup_eq_none {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {x y : α} (hx : cache.lookup x = none)
    (hy : invLookup cache y = none) :
    AgreesWith ((x, y) :: cache) ((Equiv.swap (π.symm y) x).trans π) := by
  rw [agreesWith_cons]
  refine ⟨by simp, fun e he => ?_⟩
  have hne1 : e.1 ≠ π.symm y := by
    intro h
    have h2 : e.2 = y := by rw [← hπ e he, h, Equiv.apply_symm_apply]
    exact invLookup_eq_none_iff.mp hy e he h2
  have hne2 : e.1 ≠ x := lookup_eq_none_iff.mp hx e he
  rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2, hπ e he]

/-- A cache is a partial bijection when at least one permutation on `α` extends it. -/
def IsPartialBijection (cache : Cache α) : Prop :=
  ∃ π : Equiv.Perm α, AgreesWith cache π

omit [DecidableEq α] in
/-- The empty cache is a partial bijection, witnessed by the identity permutation. -/
theorem isPartialBijection_nil : IsPartialBijection ([] : Cache α) :=
  ⟨1, agreesWith_nil 1⟩

/-- Extending a partial bijection `cache` with a fresh domain element `x` and fresh range element
`y` yields a partial bijection. -/
theorem IsPartialBijection.cons_of_lookup_eq_none {cache : Cache α}
    (h : IsPartialBijection cache) {x y : α} (hx : cache.lookup x = none)
    (hy : invLookup cache y = none) :
    IsPartialBijection ((x, y) :: cache) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π.trans (Equiv.swap (π x) y), hπ.trans_swap_of_lookup_eq_none hx hy⟩

omit [DecidableEq α] in
/-- If `π` agrees with `cache` and the domain entries of `cache` are pairwise distinct, then the
range entries of `cache` are pairwise distinct. -/
theorem AgreesWith.pairwise_snd_of_pairwise_fst {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) (hp1 : cache.Pairwise (fun a b => a.1 ≠ b.1)) :
    cache.Pairwise (fun a b => a.2 ≠ b.2) := by
  induction cache with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
    obtain ⟨he, hp1'⟩ := List.pairwise_cons.mp hp1
    obtain ⟨hπe, hπ'⟩ := (agreesWith_cons e rest π).mp hπ
    refine List.pairwise_cons.mpr ⟨fun e' he' h2 => he e' he' ?_, ih hπ' hp1'⟩
    exact π.injective (hπe.trans (h2.trans (hπ' e' he').symm))

/-! Most arguments below treat forward and inverse queries alike: a query either hits `cache`,
or misses it and records the cache entry `PermQuery.toCacheEntry ⟨q, a⟩` for its answer `a`. The
private `cachedAnswer` and the facts about it below put both directions in this form. -/

/-- The recorded answer to `q` in `cache`: its image for a forward query, its preimage for an
inverse query. -/
private def cachedAnswer (cache : Cache α) : PermQuery α → Option α
  | .forward x => cache.lookup x
  | .inverse y => invLookup cache y

private theorem AgreesWith.evalPerm_eq_of_cachedAnswer_eq_some {cache : Cache α}
    {π : Equiv.Perm α} (hπ : AgreesWith cache π) {q : PermQuery α} {a : α}
    (h : cachedAnswer cache q = some a) : evalPerm π q = a := by
  cases q with
  | forward x => exact hπ.apply_of_lookup_eq_some h
  | inverse y => exact hπ.symm_apply_of_invLookup_eq_some h

omit [DecidableEq α] in
/-- `π` agrees with the entry recording the answer `a` to `q` iff `π` answers `q` with `a`. -/
private theorem agreesWith_cons_toCacheEntry_iff {cache : Cache α} {π : Equiv.Perm α}
    {q : PermQuery α} {a : α} :
    AgreesWith (PermQuery.toCacheEntry ⟨q, a⟩ :: cache) π ↔
      evalPerm π q = a ∧ AgreesWith cache π := by
  cases q with
  | forward x => exact agreesWith_cons _ _ _
  | inverse y =>
    rw [agreesWith_cons]
    exact and_congr_left' (π.symm_apply_eq.trans eq_comm).symm

/-! ### Bidirectional query deduplication -/

/-- One step of stateful bidirectional query deduplication over a partial-permutation cache
`cache`: answer `.forward x` from `cache.lookup x` and `.inverse y` from `invLookup cache y` on
hits, and otherwise forward the query to the underlying `PermOracleSpec α` oracle and prepend
`(x, y)` to `cache`. -/
def bidirDedupStep (q : PermQuery α) :
    StateT (Cache α) (OracleComp (PermOracleSpec α)) α := fun cache =>
  match q with
  | .forward x =>
    match cache.lookup x with
    | some y => pure (y, cache)
    | none => do
      let y ← OracleComp.query (spec := PermOracleSpec α) (.forward x)
      pure (y, (x, y) :: cache)
  | .inverse y =>
    match invLookup cache y with
    | some x => pure (x, cache)
    | none => do
      let x ← OracleComp.query (spec := PermOracleSpec α) (.inverse y)
      pure (x, (x, y) :: cache)

/-- On a forward cache hit `cache.lookup x = some y`, `bidirDedupStep` returns `(y, cache)` without
issuing an oracle query. -/
theorem bidirDedupStep_forward_of_some {x y : α} {cache : Cache α}
    (h : cache.lookup x = some y) :
    bidirDedupStep (.forward x) cache = pure (y, cache) := by
  simp [bidirDedupStep, h]

/-- On a forward cache miss `cache.lookup x = none`, `bidirDedupStep` queries `.forward x` and
prepends `(x, y)` to `cache`. -/
theorem bidirDedupStep_forward_of_none {x : α} {cache : Cache α}
    (h : cache.lookup x = none) :
    bidirDedupStep (.forward x) cache = (do
      let y ← OracleComp.query (spec := PermOracleSpec α) (.forward x)
      pure (y, (x, y) :: cache)) := by
  simp [bidirDedupStep, h]

/-- On an inverse cache hit `invLookup cache y = some x`, `bidirDedupStep` returns `(x, cache)`
without issuing an oracle query. -/
theorem bidirDedupStep_inverse_of_some {y x : α} {cache : Cache α}
    (h : invLookup cache y = some x) :
    bidirDedupStep (.inverse y) cache = pure (x, cache) := by
  simp [bidirDedupStep, h]

/-- On an inverse cache miss `invLookup cache y = none`, `bidirDedupStep` queries `.inverse y` and
prepends `(x, y)` to `cache`. -/
theorem bidirDedupStep_inverse_of_none {y : α} {cache : Cache α}
    (h : invLookup cache y = none) :
    bidirDedupStep (.inverse y) cache = (do
      let x ← OracleComp.query (spec := PermOracleSpec α) (.inverse y)
      pure (x, (x, y) :: cache)) := by
  simp [bidirDedupStep, h]

private theorem bidirDedupStep_of_cachedAnswer_eq_some {q : PermQuery α} {cache : Cache α}
    {a : α} (h : cachedAnswer cache q = some a) :
    bidirDedupStep q cache = pure (a, cache) := by
  cases q with
  | forward x => exact bidirDedupStep_forward_of_some h
  | inverse y => exact bidirDedupStep_inverse_of_some h

private theorem bidirDedupStep_of_cachedAnswer_eq_none {q : PermQuery α} {cache : Cache α}
    (h : cachedAnswer cache q = none) :
    bidirDedupStep q cache = (do
      let a ← OracleComp.query (spec := PermOracleSpec α) q
      pure (a, PermQuery.toCacheEntry ⟨q, a⟩ :: cache)) := by
  cases q with
  | forward x => exact bidirDedupStep_forward_of_none h
  | inverse y => exact bidirDedupStep_inverse_of_none h

/-- Deduplicate a bidirectional permutation program starting from the empty cache `[]`, returning
both the program output and the final `(input, output)` cache. Forward queries in `dom(cache)` and
inverse queries in `ran(cache)` are answered from `cache` without calling the underlying oracle. -/
def bidirDedup {β : Type} (program : OracleComp (PermOracleSpec α) β) :
    OracleComp (PermOracleSpec α) (β × Cache α) :=
  (OracleComp.interpret bidirDedupStep program).run []

/-- One step of `bidirDedupStep` issues at most `1` underlying oracle query. -/
theorem isQueryBounded_bidirDedupStep (q : PermQuery α) (cache : Cache α) :
    IsQueryBounded (bidirDedupStep q cache) 1 := by
  cases h : cachedAnswer cache q with
  | some a =>
    rw [bidirDedupStep_of_cachedAnswer_eq_some h]
    exact IsCostBounded.pure (a, cache) 1
  | none =>
    rw [bidirDedupStep_of_cachedAnswer_eq_none h]
    simpa using (IsCostBounded.query (spec := PermOracleSpec α) q).bind
      fun a => IsCostBounded.pure (a, PermQuery.toCacheEntry ⟨q, a⟩ :: cache) 0

/-- Running `bidirDedupStep` from any initial `cache` preserves `Q`-query bounds. -/
theorem isQueryBounded_run_bidirDedupStep {β : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (cache : Cache α) :
    IsQueryBounded ((OracleComp.interpret bidirDedupStep program).run cache) Q :=
  hQ.run_interpret isQueryBounded_bidirDedupStep cache

/-- Bidirectional query deduplication `bidirDedup` preserves `Q`-query bounds. -/
theorem isQueryBounded_bidirDedup {β : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) :
    IsQueryBounded (bidirDedup program) Q :=
  isQueryBounded_run_bidirDedupStep hQ []

/-- Evaluating a `bidirDedupStep`-wrapped program against `evalPerm π` from any cache agreeing with
`π` produces the exact same output distribution as evaluating the original program against
`evalPerm π`. -/
theorem map_fst_interpret_bidirDedupStep_evalPerm {β : Type} (π : Equiv.Perm α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache : Cache α} (hcache : AgreesWith cache π) :
    (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
      ((OracleComp.interpret bidirDedupStep program).run cache)).map Prod.fst =
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program := by
  induction program using OracleComp.induction generalizing cache with
  | pure a =>
    simp [PMF.pure_map]
  | query_bind q cont ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    change (((OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
      (bidirDedupStep q cache)).bind fun p =>
        OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
          ((OracleComp.interpret bidirDedupStep (cont p.1)).run p.2)).map Prod.fst) =
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (cont (evalPerm π q))
    cases h : cachedAnswer cache q with
    | some a =>
      rw [bidirDedupStep_of_cachedAnswer_eq_some h]
      simp only [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind, hcache.evalPerm_eq_of_cachedAnswer_eq_some h]
      exact ih a hcache
    | none =>
      rw [bidirDedupStep_of_cachedAnswer_eq_none h]
      simp only [pmf_norm, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure]
      exact ih (evalPerm π q) (agreesWith_cons_toCacheEntry_iff.mpr ⟨rfl, hcache⟩)

/-- **Exact `evalPerm` equivalence for `bidirDedup`**: deduplicating a bidirectional permutation
program does not change its output distribution against `evalPerm π`. -/
theorem map_fst_interpret_bidirDedup_evalPerm {β : Type} (π : Equiv.Perm α)
    (program : OracleComp (PermOracleSpec α) β) :
    (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
      (bidirDedup program)).map Prod.fst =
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program :=
  map_fst_interpret_bidirDedupStep_evalPerm π program (agreesWith_nil π)

private theorem bidirDedupStep_transcript_inv {β σ : Type}
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache cache' : Cache α} {s s' : σ} {result : β}
    {transcript : OracleComp.Transcript (PermOracleSpec α)}
    (hmem : ((result, cache'), (s', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        ((OracleComp.interpret bidirDedupStep program).run cache)).run (s, [])).support) :
    cache' = transcript.map PermQuery.toCacheEntry ++ cache ∧
      (transcript.map Sigma.fst).Nodup ∧
      ∀ q ∈ transcript.map Sigma.fst, cachedAnswer cache q = none := by
  induction program using OracleComp.induction generalizing cache s transcript with
  | pure a =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨_, rfl⟩, _, rfl⟩
    exact ⟨rfl, List.nodup_nil, fun _ h => False.elim (List.not_mem_nil h)⟩
  | query_bind q cont ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind] at hmem
    change ((result, cache'), (s', transcript)) ∈
      (((OracleComp.interpret (OracleComp.withTranscript oracle) (bidirDedupStep q cache)).run
        (s, [])).bind fun p =>
          (OracleComp.interpret (OracleComp.withTranscript oracle)
            ((OracleComp.interpret bidirDedupStep (cont p.1.1)).run p.1.2)).run p.2).support at hmem
    cases hq : cachedAnswer cache q with
    | some a =>
      rw [bidirDedupStep_of_cachedAnswer_eq_some hq] at hmem
      simp only [OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.pure_bind] at hmem
      exact ih a hmem
    | none =>
      rw [bidirDedupStep_of_cachedAnswer_eq_none hq] at hmem
      simp only [pmf_norm, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
        PMF.mem_support_bind_iff] at hmem
      obtain ⟨⟨a, s₁, tr₁⟩, hfirst, hrest⟩ := hmem
      simp only [StateT.run, OracleComp.withTranscript, PMF.mem_support_map_iff] at hfirst
      obtain ⟨⟨a', s₁'⟩, -, heq⟩ := hfirst
      cases heq
      rw [OracleComp.run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
      obtain ⟨⟨⟨res', c'⟩, s₂', fresh⟩, hfresh, heq'⟩ := hrest
      cases heq'
      obtain ⟨hceq, hnodup, hmiss⟩ := ih a' hfresh
      have hold (q' : PermQuery α) (hq' : q' ∈ fresh.map Sigma.fst) :
          q' ≠ q ∧ cachedAnswer cache q' = none := by
        have h := hmiss q' hq'
        cases q' with
        | forward x =>
          obtain ⟨hne, h⟩ := List.forall_mem_cons.mp (lookup_eq_none_iff.mp h)
          exact ⟨by rintro rfl; exact hne rfl, lookup_eq_none_iff.mpr h⟩
        | inverse y =>
          obtain ⟨hne, h⟩ := List.forall_mem_cons.mp (invLookup_eq_none_iff.mp h)
          exact ⟨by rintro rfl; exact hne rfl, invLookup_eq_none_iff.mpr h⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append, hceq]
      · rw [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨hnodup, List.nodup_singleton _, fun q' hq' q'' hq'' => ?_⟩
        rw [List.mem_singleton] at hq''
        exact hq'' ▸ (hold q' hq').1
      · intro q' hq'
        rw [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton] at hq'
        rcases hq' with hq' | rfl
        · exact (hold q' hq').2
        · exact hq

/-- Against any stateful handler `oracle`, the final deduplication cache after running
`bidirDedupStep` from `cache` equals `transcript.map PermQuery.toCacheEntry ++ cache`. -/
theorem cache_eq_of_mem_support_withTranscript_bidirDedupStep {β σ : Type}
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache cache' : Cache α} {s s' : σ} {result : β}
    {transcript : OracleComp.Transcript (PermOracleSpec α)}
    (hmem : ((result, cache'), (s', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        ((OracleComp.interpret bidirDedupStep program).run cache)).run (s, [])).support) :
    cache' = transcript.map PermQuery.toCacheEntry ++ cache :=
  (bidirDedupStep_transcript_inv oracle program hmem).1

/-- Against any stateful handler `oracle`, the final deduplication cache produced by `bidirDedup`
equals `transcript.map PermQuery.toCacheEntry`. -/
theorem cache_eq_of_mem_support_withTranscript_bidirDedup {β σ : Type}
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache' : Cache α} {s s' : σ} {result : β}
    {transcript : OracleComp.Transcript (PermOracleSpec α)}
    (hmem : ((result, cache'), (s', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        (bidirDedup program)).run (s, [])).support) :
    cache' = transcript.map PermQuery.toCacheEntry := by
  simpa only [List.append_nil] using
    cache_eq_of_mem_support_withTranscript_bidirDedupStep oracle program hmem

/-- Against any stateful handler `oracle`, `bidirDedupStep` never forwards the same underlying
`PermQuery α` twice. -/
theorem nodup_transcript_of_mem_support_withTranscript_bidirDedupStep {β σ : Type}
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache cache' : Cache α} {s s' : σ} {result : β}
    {transcript : OracleComp.Transcript (PermOracleSpec α)}
    (hmem : ((result, cache'), (s', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        ((OracleComp.interpret bidirDedupStep program).run cache)).run (s, [])).support) :
    (transcript.map Sigma.fst).Nodup :=
  (bidirDedupStep_transcript_inv oracle program hmem).2.1

/-- Against any stateful handler `oracle`, `bidirDedup` never forwards the same underlying
`PermQuery α` twice. -/
theorem nodup_transcript_of_mem_support_withTranscript_bidirDedup {β σ : Type}
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    (program : OracleComp (PermOracleSpec α) β)
    {cache' : Cache α} {s s' : σ} {result : β}
    {transcript : OracleComp.Transcript (PermOracleSpec α)}
    (hmem : ((result, cache'), (s', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle)
        (bidirDedup program)).run (s, [])).support) :
    (transcript.map Sigma.fst).Nodup :=
  nodup_transcript_of_mem_support_withTranscript_bidirDedupStep oracle program hmem

/-- Against any stateful handler `oracle`, running `bidirDedupStep` on a `Q`-query-bounded program
from `cache` adds at most `Q` entries to `cache`. -/
theorem length_cache_le_of_mem_support_run_bidirDedupStep {β σ : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q)
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    {cache cache' : Cache α} {s s' : σ} {result : β}
    (hmem : ((result, cache'), s') ∈
      ((OracleComp.interpret oracle
        ((OracleComp.interpret bidirDedupStep program).run cache)).run s).support) :
    cache'.length ≤ cache.length + Q := by
  rw [← OracleComp.run_interpret_withTranscript oracle
    ((OracleComp.interpret bidirDedupStep program).run cache) s [],
    PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨⟨res', c'⟩, s'', transcript⟩, htr, heq⟩ := hmem
  cases heq
  have hceq := cache_eq_of_mem_support_withTranscript_bidirDedupStep oracle program htr
  have hlen := (isQueryBounded_run_bidirDedupStep hQ cache).length_transcript_le oracle htr
  rw [hceq, List.length_append, List.length_map, Nat.add_comm]
  exact Nat.add_le_add_left hlen cache.length

/-- Against any stateful handler `oracle`, running `bidirDedup` on a `Q`-query-bounded program
produces a cache of length at most `Q`. -/
theorem length_cache_le_of_mem_support_bidirDedup {β σ : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q)
    (oracle : (q : PermQuery α) → StateT σ PMF α)
    {cache' : Cache α} {s s' : σ} {result : β}
    (hmem : ((result, cache'), s') ∈
      ((OracleComp.interpret oracle (bidirDedup program)).run s).support) :
    cache'.length ≤ Q := by
  simpa only [List.length_nil, Nat.zero_add] using
    length_cache_le_of_mem_support_run_bidirDedupStep hQ oracle hmem

/-- Evaluating `bidirDedupStep` against `evalPerm π` from any cache agreeing with `π` whose domain
entries are pairwise distinct preserves `AgreesWith` and maintains pairwise-distinct domain and
range entries. -/
theorem agreesWith_and_pairwise_of_mem_support_run_bidirDedupStep {β : Type} (π : Equiv.Perm α)
    (program : OracleComp (PermOracleSpec α) β) {cache cache' : Cache α} {result : β}
    (hπ : AgreesWith cache π) (hp1 : cache.Pairwise (fun a b => a.1 ≠ b.1))
    (hmem : (result, cache') ∈
      (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
        ((OracleComp.interpret bidirDedupStep program).run cache)).support) :
    AgreesWith cache' π ∧
      cache'.Pairwise (fun a b => a.1 ≠ b.1) ∧
      cache'.Pairwise (fun a b => a.2 ≠ b.2) := by
  induction program using OracleComp.induction generalizing cache with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact ⟨hπ, hp1, hπ.pairwise_snd_of_pairwise_fst hp1⟩
  | query_bind q cont ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind] at hmem
    change (result, cache') ∈
      ((OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
        (bidirDedupStep q cache)).bind fun p =>
          OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
            ((OracleComp.interpret bidirDedupStep (cont p.1)).run p.2)).support at hmem
    cases hq : cachedAnswer cache q with
    | some a =>
      rw [bidirDedupStep_of_cachedAnswer_eq_some hq] at hmem
      simp only [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind] at hmem
      exact ih a hπ hp1 hmem
    | none =>
      rw [bidirDedupStep_of_cachedAnswer_eq_none hq] at hmem
      simp only [pmf_norm, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure] at hmem
      have hx : cache.lookup (PermQuery.toCacheEntry ⟨q, evalPerm π q⟩).1 = none := by
        cases q with
        | forward x => exact hq
        | inverse y => exact hπ.lookup_symm_apply_eq_none hq
      exact ih (evalPerm π q) (agreesWith_cons_toCacheEntry_iff.mpr ⟨rfl, hπ⟩)
        (List.pairwise_cons.mpr ⟨fun e he => (lookup_eq_none_iff.mp hx e he).symm, hp1⟩) hmem

/-- Evaluating `bidirDedup` against `evalPerm π` produces a cache agreeing with `π` whose domain and
range entries are both pairwise distinct. -/
theorem agreesWith_and_pairwise_of_mem_support_bidirDedup {β : Type} (π : Equiv.Perm α)
    (program : OracleComp (PermOracleSpec α) β) {cache' : Cache α} {result : β}
    (hmem : (result, cache') ∈
      (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
        (bidirDedup program)).support) :
    AgreesWith cache' π ∧
      cache'.Pairwise (fun a b => a.1 ≠ b.1) ∧
      cache'.Pairwise (fun a b => a.2 ≠ b.2) :=
  agreesWith_and_pairwise_of_mem_support_run_bidirDedupStep π program (agreesWith_nil π)
    List.Pairwise.nil hmem

/-! ### Finite domain/range complements and extension finsets -/

section Finite

variable [Fintype α]

/-- Elements of `α` not yet present in the domain of `cache`. -/
def unusedDomain (cache : Cache α) : Finset α :=
  Finset.univ.filter fun x => cache.lookup x = none

/-- Elements of `α` not yet present in the range of `cache`. -/
def unusedRange (cache : Cache α) : Finset α :=
  Finset.univ.filter fun y => invLookup cache y = none

/-- Permutations `π : Equiv.Perm α` that agree with every entry in `cache`. -/
def extPerms (cache : Cache α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun π => AgreesWith cache π

/-- An element `x` belongs to `unusedDomain cache` iff `cache.lookup x = none`. -/
@[simp] theorem mem_unusedDomain_iff {cache : Cache α} {x : α} :
    x ∈ unusedDomain cache ↔ cache.lookup x = none := by
  simp [unusedDomain]

/-- An element `y` belongs to `unusedRange cache` iff `invLookup cache y = none`. -/
@[simp] theorem mem_unusedRange_iff {cache : Cache α} {y : α} :
    y ∈ unusedRange cache ↔ invLookup cache y = none := by
  simp [unusedRange]

/-- A permutation `π` belongs to `extPerms cache` iff `AgreesWith cache π`. -/
@[simp] theorem mem_extPerms_iff {cache : Cache α} {π : Equiv.Perm α} :
    π ∈ extPerms cache ↔ AgreesWith cache π := by
  simp [extPerms]

/-- Every permutation extends the empty cache. -/
@[simp] theorem extPerms_nil : extPerms ([] : Cache α) = Finset.univ := by
  ext π
  simp

/-- The extension finset `extPerms cache` is nonempty iff `cache` is a partial bijection. -/
theorem extPerms_nonempty_iff {cache : Cache α} :
    (extPerms cache).Nonempty ↔ IsPartialBijection cache := by
  simp [Finset.Nonempty, IsPartialBijection]

/-- When `cache` is a partial bijection and `x` is outside its domain, `unusedRange cache` is
nonempty. -/
theorem IsPartialBijection.unusedRange_nonempty {cache : Cache α}
    (h : IsPartialBijection cache) {x : α} (hx : cache.lookup x = none) :
    (unusedRange cache).Nonempty := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π x, mem_unusedRange_iff.mpr (hπ.invLookup_apply_eq_none hx)⟩

/-- When `cache` is a partial bijection and `y` is outside its range, `unusedDomain cache` is
nonempty. -/
theorem IsPartialBijection.unusedDomain_nonempty {cache : Cache α}
    (h : IsPartialBijection cache) {y : α} (hy : invLookup cache y = none) :
    (unusedDomain cache).Nonempty := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π.symm y, mem_unusedDomain_iff.mpr (hπ.lookup_symm_apply_eq_none hy)⟩

/-- Post-composing with `Equiv.swap y₁ y₂` bijects extensions of `(x, y₁) :: cache` onto
extensions of `(x, y₂) :: cache` whenever `y₁, y₂ ∈ unusedRange cache`. -/
private theorem card_extPerms_cons_eq_of_unusedRange {cache : Cache α} (x : α)
    {y₁ y₂ : α} (hy₁ : y₁ ∈ unusedRange cache) (hy₂ : y₂ ∈ unusedRange cache) :
    (extPerms ((x, y₁) :: cache)).card = (extPerms ((x, y₂) :: cache)).card := by
  refine Finset.card_equiv (Equiv.mulLeft (Equiv.swap y₁ y₂)) fun π => ?_
  have hfix (e : α × α) (he : e ∈ cache) : Equiv.swap y₁ y₂ e.2 = e.2 :=
    Equiv.swap_apply_of_ne_of_ne (invLookup_eq_none_iff.mp (mem_unusedRange_iff.mp hy₁) e he)
      (invLookup_eq_none_iff.mp (mem_unusedRange_iff.mp hy₂) e he)
  simp only [mem_extPerms_iff, agreesWith_cons, Equiv.coe_mulLeft, Equiv.Perm.mul_apply,
    Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  exact and_congr_right' (forall₂_congr fun e he => by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, hfix e he])

/-- Pre-composing with `Equiv.swap x₁ x₂` bijects extensions of `(x₁, y) :: cache` onto
extensions of `(x₂, y) :: cache` whenever `x₁, x₂ ∈ unusedDomain cache`. -/
private theorem card_extPerms_cons_eq_of_unusedDomain {cache : Cache α} (y : α)
    {x₁ x₂ : α} (hx₁ : x₁ ∈ unusedDomain cache) (hx₂ : x₂ ∈ unusedDomain cache) :
    (extPerms ((x₁, y) :: cache)).card = (extPerms ((x₂, y) :: cache)).card := by
  refine Finset.card_equiv (Equiv.mulRight (Equiv.swap x₁ x₂)) fun π => ?_
  have hfix (e : α × α) (he : e ∈ cache) : Equiv.swap x₁ x₂ e.1 = e.1 :=
    Equiv.swap_apply_of_ne_of_ne (lookup_eq_none_iff.mp (mem_unusedDomain_iff.mp hx₁) e he)
      (lookup_eq_none_iff.mp (mem_unusedDomain_iff.mp hx₂) e he)
  simp only [mem_extPerms_iff, agreesWith_cons, Equiv.coe_mulRight, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right]
  exact and_congr_right' (forall₂_congr fun e he => by rw [Equiv.Perm.mul_apply, hfix e he])

/-- The answers still available to a query that misses `cache`: `unusedRange cache` for a forward
query and `unusedDomain cache` for an inverse query. -/
private def freshAnswers (cache : Cache α) : PermQuery α → Finset α
  | .forward _ => unusedRange cache
  | .inverse _ => unusedDomain cache

private theorem AgreesWith.evalPerm_mem_freshAnswers {cache : Cache α} {π : Equiv.Perm α}
    (hπ : AgreesWith cache π) {q : PermQuery α} (hq : cachedAnswer cache q = none) :
    evalPerm π q ∈ freshAnswers cache q := by
  cases q with
  | forward x => exact mem_unusedRange_iff.mpr (hπ.invLookup_apply_eq_none hq)
  | inverse y => exact mem_unusedDomain_iff.mpr (hπ.lookup_symm_apply_eq_none hq)

private theorem IsPartialBijection.freshAnswers_nonempty {cache : Cache α}
    (h : IsPartialBijection cache) {q : PermQuery α} (hq : cachedAnswer cache q = none) :
    (freshAnswers cache q).Nonempty :=
  let ⟨_, hπ⟩ := h
  ⟨_, hπ.evalPerm_mem_freshAnswers hq⟩

/-- Recording a fresh answer `a` to a query `q` that misses `cache` adds an entry whose input and
output are both new to `cache`. -/
private theorem lookup_and_invLookup_toCacheEntry_eq_none {cache : Cache α} {q : PermQuery α}
    (hq : cachedAnswer cache q = none) {a : α} (ha : a ∈ freshAnswers cache q) :
    cache.lookup (PermQuery.toCacheEntry ⟨q, a⟩).1 = none ∧
      invLookup cache (PermQuery.toCacheEntry ⟨q, a⟩).2 = none := by
  cases q with
  | forward x => exact ⟨hq, mem_unusedRange_iff.mp ha⟩
  | inverse y => exact ⟨mem_unusedDomain_iff.mp ha, hq⟩

private theorem IsPartialBijection.cons_toCacheEntry {cache : Cache α}
    (h : IsPartialBijection cache) {q : PermQuery α} (hq : cachedAnswer cache q = none) {a : α}
    (ha : a ∈ freshAnswers cache q) :
    IsPartialBijection (PermQuery.toCacheEntry ⟨q, a⟩ :: cache) :=
  h.cons_of_lookup_eq_none (lookup_and_invLookup_toCacheEntry_eq_none hq ha).1
    (lookup_and_invLookup_toCacheEntry_eq_none hq ha).2

/-- Partitioning `extPerms cache` by the answer `evalPerm π q` to a query `q` that misses `cache`
shows that all fibers over `freshAnswers cache q` have equal size. -/
private theorem card_extPerms_eq_card_freshAnswers_mul {cache : Cache α} {q : PermQuery α}
    (hq : cachedAnswer cache q = none) {a : α} (ha : a ∈ freshAnswers cache q) :
    (extPerms cache).card =
      (freshAnswers cache q).card * (extPerms (PermQuery.toCacheEntry ⟨q, a⟩ :: cache)).card := by
  have hmaps : ∀ π ∈ extPerms cache, evalPerm π q ∈ freshAnswers cache q := fun π hπ =>
    (mem_extPerms_iff.mp hπ).evalPerm_mem_freshAnswers hq
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (a' : α) (ha' : a' ∈ freshAnswers cache q) :
      {π ∈ extPerms cache | evalPerm π q = a'}.card =
        (extPerms (PermQuery.toCacheEntry ⟨q, a⟩ :: cache)).card := by
    have hset : {π ∈ extPerms cache | evalPerm π q = a'} =
        extPerms (PermQuery.toCacheEntry ⟨q, a'⟩ :: cache) := by
      ext π
      simp only [Finset.mem_filter, mem_extPerms_iff, agreesWith_cons_toCacheEntry_iff, and_comm]
    rw [hset]
    cases q with
    | forward x => exact card_extPerms_cons_eq_of_unusedRange x ha' ha
    | inverse y => exact card_extPerms_cons_eq_of_unusedDomain y ha' ha
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]

/-- Partitioning `extPerms cache` by the image `π x` of a fresh input `x` shows that all fibers over
`unusedRange cache` have equal size. -/
theorem card_extPerms_eq_card_unusedRange_mul {cache : Cache α} {x y : α}
    (hx : cache.lookup x = none) (hy : y ∈ unusedRange cache) :
    (extPerms cache).card = (unusedRange cache).card * (extPerms ((x, y) :: cache)).card :=
  card_extPerms_eq_card_freshAnswers_mul (q := .forward x) hx hy

/-- Partitioning `extPerms cache` by the preimage `π.symm y` of a fresh output `y` shows that all
fibers over `unusedDomain cache` have equal size. -/
theorem card_extPerms_eq_card_unusedDomain_mul {cache : Cache α} {x y : α}
    (hx : x ∈ unusedDomain cache) (hy : invLookup cache y = none) :
    (extPerms cache).card = (unusedDomain cache).card * (extPerms ((x, y) :: cache)).card :=
  card_extPerms_eq_card_freshAnswers_mul (q := .inverse y) hy hx

/-! ### Exact lazy bidirectional permutation sampler and eager/lazy equivalence -/

variable [Nonempty α]

/-- Exact without-replacement lazy bidirectional permutation oracle: return cached answers on hits,
and sample uniformly from `unusedRange cache` (for `.forward`) or `unusedDomain cache` (for
`.inverse`) on misses. -/
noncomputable def answer (q : PermQuery α) : StateT (Cache α) PMF α := fun cache =>
  match q with
  | .forward x =>
    match cache.lookup x with
    | some y => PMF.pure (y, cache)
    | none =>
      if h : (unusedRange cache).Nonempty then
        (PMF.uniformOfFinset (unusedRange cache) h).map fun y => (y, (x, y) :: cache)
      else
        (PMF.uniformOfFintype α).map fun y => (y, (x, y) :: cache)
  | .inverse y =>
    match invLookup cache y with
    | some x => PMF.pure (x, cache)
    | none =>
      if h : (unusedDomain cache).Nonempty then
        (PMF.uniformOfFinset (unusedDomain cache) h).map fun x => (x, (x, y) :: cache)
      else
        (PMF.uniformOfFintype α).map fun x => (x, (x, y) :: cache)

/-- Uniformly sample a full permutation `π : Equiv.Perm α` extending `cache`. -/
noncomputable def complete (cache : Cache α) : PMF (Equiv.Perm α) :=
  if h : (extPerms cache).Nonempty then
    PMF.uniformOfFinset (extPerms cache) h
  else
    PMF.uniformOfFintype (Equiv.Perm α)

omit [Nonempty α] in
/-- Completing the empty cache samples a uniformly random permutation on `α`. -/
@[simp] theorem complete_nil :
    complete ([] : Cache α) = PMF.uniformOfFintype (Equiv.Perm α) := by
  ext π
  simp [complete, PMF.uniformOfFinset_apply, PMF.uniformOfFintype_apply]

private theorem answer_of_cachedAnswer_eq_some {q : PermQuery α} {cache : Cache α} {a : α}
    (h : cachedAnswer cache q = some a) : answer q cache = PMF.pure (a, cache) := by
  cases q <;> simp_all [answer, cachedAnswer]

private theorem answer_of_cachedAnswer_eq_none {q : PermQuery α} {cache : Cache α}
    (h : cachedAnswer cache q = none) (hne : (freshAnswers cache q).Nonempty) :
    answer q cache = (PMF.uniformOfFinset _ hne).map fun a =>
      (a, PermQuery.toCacheEntry ⟨q, a⟩ :: cache) := by
  cases q with
  | forward x =>
    have hne' : (unusedRange cache).Nonempty := hne
    simp [answer, show cache.lookup x = none from h, dite_eq_left hne', freshAnswers]
  | inverse y =>
    have hne' : (unusedDomain cache).Nonempty := hne
    simp [answer, show invLookup cache y = none from h, dite_eq_left hne', freshAnswers]

/-- `answer` preserves `IsPartialBijection` on every supported transition. -/
theorem answer_preserve_isPartialBijection (q : PermQuery α) (cache : Cache α)
    (hcache : IsPartialBijection cache) (a : α) (cache' : Cache α)
    (hmem : (a, cache') ∈ (answer q cache).support) :
    IsPartialBijection cache' := by
  cases hq : cachedAnswer cache q with
  | some b =>
    rw [answer_of_cachedAnswer_eq_some hq, PMF.mem_support_pure_iff] at hmem
    exact (Prod.mk.inj hmem).2 ▸ hcache
  | none =>
    rw [answer_of_cachedAnswer_eq_none hq (hcache.freshAnswers_nonempty hq),
      PMF.mem_support_map_iff] at hmem
    obtain ⟨b, hb, heq⟩ := hmem
    rw [PMF.mem_support_uniformOfFinset_iff] at hb
    obtain ⟨_, rfl⟩ := Prod.mk.inj heq
    exact hcache.cons_toCacheEntry hq hb

private theorem map_pair_apply {β γ : Type*} [DecidableEq β]
    (p : PMF γ) (f : γ → β) (b : β) (c : γ) :
    (p.map fun x => (f x, x)) (b, c) = if b = f c then p c else 0 := by
  classical
  rw [PMF.map_apply, tsum_eq_single c]
  · simp
  · intro x hxc
    exact ite_eq_right (fun h => hxc (Prod.mk.inj h).2.symm)

/-- Answering one bidirectional query lazily and then completing the partial bijection has the exact
same joint distribution on `(answer, π)` as completing first and evaluating `evalPerm π q`. -/
theorem answer_complete (q : PermQuery α) (cache : Cache α) (hcache : IsPartialBijection cache) :
    (answer q cache).bind (fun (a, cache') => (complete cache').map (a, ·)) =
      (complete cache).map (fun π => (evalPerm π q, π)) := by
  have hzero {c : Cache α} {π : Equiv.Perm α} (hc : (extPerms c).Nonempty)
      (hπ : π ∉ extPerms c) : complete c π = 0 := by
    simp [complete, dite_eq_left hc, PMF.uniformOfFinset_apply, hπ]
  have hext_ne : (extPerms cache).Nonempty := extPerms_nonempty_iff.mpr hcache
  cases hq : cachedAnswer cache q with
  | some b =>
    rw [answer_of_cachedAnswer_eq_some hq, PMF.pure_bind]
    ext ⟨a, π⟩
    rw [map_pair_apply, map_pair_apply]
    by_cases hmem : π ∈ extPerms cache
    · rw [(mem_extPerms_iff.mp hmem).evalPerm_eq_of_cachedAnswer_eq_some hq]
    · simp [hzero hext_ne hmem]
  | none =>
    have hne := hcache.freshAnswers_nonempty hq
    rw [answer_of_cachedAnswer_eq_none hq hne]
    simp only [PMF.bind_map, Function.comp_def]
    ext ⟨a, π⟩
    rw [map_pair_apply, PMF.bind_apply]
    have hterm (b : α) :
        PMF.uniformOfFinset _ hne b *
          ((complete (PermQuery.toCacheEntry ⟨q, b⟩ :: cache)).map (b, ·)) (a, π) =
        if b = a then
          PMF.uniformOfFinset _ hne a * complete (PermQuery.toCacheEntry ⟨q, a⟩ :: cache) π
        else 0 := by
      rw [map_pair_apply]
      by_cases hba : b = a
      · subst hba; simp
      · simp [hba, Ne.symm hba]
    simp_rw [hterm, tsum_ite_eq]
    by_cases hπ : π ∈ extPerms cache ∧ a = evalPerm π q
    · obtain ⟨hπ_mem, rfl⟩ := hπ
      have ha := (mem_extPerms_iff.mp hπ_mem).evalPerm_mem_freshAnswers hq
      have hcons_mem : π ∈ extPerms (PermQuery.toCacheEntry ⟨q, evalPerm π q⟩ :: cache) :=
        mem_extPerms_iff.mpr (agreesWith_cons_toCacheEntry_iff.mpr
          ⟨rfl, mem_extPerms_iff.mp hπ_mem⟩)
      have hcons_ne : (extPerms (PermQuery.toCacheEntry ⟨q, evalPerm π q⟩ :: cache)).Nonempty :=
        ⟨π, hcons_mem⟩
      rw [complete, dite_eq_left hcons_ne, complete, dite_eq_left hext_ne]
      simp only [PMF.uniformOfFinset_apply, ha, hcons_mem, hπ_mem, ↓reduceIte]
      rw [card_extPerms_eq_card_freshAnswers_mul hq ha, Nat.cast_mul,
        ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr hne.card_pos.ne'))
          (Or.inl (ENNReal.natCast_ne_top _))]
    · have hrhs : (if a = evalPerm π q then complete cache π else 0) = 0 :=
        ite_eq_right_iff.mpr fun h => hzero hext_ne fun hm => hπ ⟨hm, h⟩
      rw [hrhs]
      by_cases ha : a ∈ freshAnswers cache q
      · have hnot_cons : π ∉ extPerms (PermQuery.toCacheEntry ⟨q, a⟩ :: cache) := fun h => by
          obtain ⟨h1, h2⟩ := agreesWith_cons_toCacheEntry_iff.mp (mem_extPerms_iff.mp h)
          exact hπ ⟨mem_extPerms_iff.mpr h2, h1.symm⟩
        rw [hzero (extPerms_nonempty_iff.mpr (hcache.cons_toCacheEntry hq ha)) hnot_cons,
          mul_zero]
      · simp [PMF.uniformOfFinset_apply, ha]

/-- **Eager/lazy equivalence for bidirectional permutations**: running an adaptive program against
`answer` from any partial bijection `cache` and then completing `cache'` to a full permutation gives
the same joint distribution on `(result, π)` as completing `cache` first and answering queries via
`evalPerm π`. -/
theorem run_interpret_answer_complete {β : Type}
    (program : OracleComp (PermOracleSpec α) β) (cache : Cache α)
    (hcache : IsPartialBijection cache) :
    (do
      let (result, cache') ← (OracleComp.interpret answer program).run cache
      (complete cache').map (result, ·)) =
    (do
      let π ← complete cache
      (OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program).map (·, π)) := by
  simp only [PMF.monad_bind_eq_bind]
  have h := OracleComp.run_interpret_simulation_of_invariant answer
    (fun q π => (·, π) <$> PMF.pure (evalPerm π q)) complete IsPartialBijection
    answer_preserve_isPartialBijection
    (fun q c hc => by
      simpa only [pmf_norm, PMF.map] using answer_complete q c hc)
    program cache hcache
  refine h.trans (congrArg ((complete cache).bind) (funext fun π => ?_))
  simpa only [PMF.monad_map_eq_map] using OracleComp.run_interpret_readOnly
    (fun q (π : Equiv.Perm α) => PMF.pure (evalPerm π q)) program π

/-- **Uniform random permutation equals lazy bidirectional sampling**: sampling a uniform
permutation `π ← PMF.uniformOfFintype (Equiv.Perm α)` and answering bidirectional queries via
`evalPerm π` has the exact same output distribution as running `answer` from the empty cache
`[]`. -/
theorem uniform_interpret_eq_lazy {β : Type} (program : OracleComp (PermOracleSpec α) β) :
    (do
      let π ← PMF.uniformOfFintype (Equiv.Perm α)
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program) =
    ((OracleComp.interpret answer program).run []).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_answer_complete program [] isPartialBijection_nil)
  simpa only [pmf_norm, complete_nil, PMF.map, PMF.bind_const] using h.symm

/-! ### Forgetful lazy permutation sampler and bidirectional switching bound -/

/-- **Forgetful lazy bidirectional permutation oracle** ([BonehShoup2023], Section 4.7): return the
cached image/preimage on a hit, and sample uniformly from all of `α` (with replacement) on a
miss. -/
noncomputable def forgetfulAnswer (q : PermQuery α) : StateT (Cache α) PMF α := fun cache =>
  match q with
  | .forward x =>
    match cache.lookup x with
    | some y => PMF.pure (y, cache)
    | none => (PMF.uniformOfFintype α).map fun y => (y, (x, y) :: cache)
  | .inverse y =>
    match invLookup cache y with
    | some x => PMF.pure (x, cache)
    | none => (PMF.uniformOfFintype α).map fun x => (x, (x, y) :: cache)

/-- On a forward cache hit `cache.lookup x = some y`, `forgetfulAnswer` returns `(y, cache)`. -/
theorem forgetfulAnswer_forward_of_some {x y : α} {cache : Cache α}
    (h : cache.lookup x = some y) :
    forgetfulAnswer (.forward x) cache = PMF.pure (y, cache) := by
  simp [forgetfulAnswer, h]

/-- On a forward cache miss `cache.lookup x = none`, `forgetfulAnswer` samples `y` uniformly from
`α` and prepends `(x, y)` to `cache`. -/
theorem forgetfulAnswer_forward_of_none {x : α} {cache : Cache α}
    (h : cache.lookup x = none) :
    forgetfulAnswer (.forward x) cache =
      (PMF.uniformOfFintype α).map fun y => (y, (x, y) :: cache) := by
  simp [forgetfulAnswer, h]

/-- On an inverse cache hit `invLookup cache y = some x`, `forgetfulAnswer` returns `(x, cache)`. -/
theorem forgetfulAnswer_inverse_of_some {y x : α} {cache : Cache α}
    (h : invLookup cache y = some x) :
    forgetfulAnswer (.inverse y) cache = PMF.pure (x, cache) := by
  simp [forgetfulAnswer, h]

/-- On an inverse cache miss `invLookup cache y = none`, `forgetfulAnswer` samples `x` uniformly
from `α` and prepends `(x, y)` to `cache`. -/
theorem forgetfulAnswer_inverse_of_none {y : α} {cache : Cache α}
    (h : invLookup cache y = none) :
    forgetfulAnswer (.inverse y) cache =
      (PMF.uniformOfFintype α).map fun x => (x, (x, y) :: cache) := by
  simp [forgetfulAnswer, h]

private theorem forgetfulAnswer_of_cachedAnswer_eq_some {q : PermQuery α} {cache : Cache α}
    {a : α} (h : cachedAnswer cache q = some a) :
    forgetfulAnswer q cache = PMF.pure (a, cache) := by
  cases q with
  | forward x => exact forgetfulAnswer_forward_of_some h
  | inverse y => exact forgetfulAnswer_inverse_of_some h

private theorem forgetfulAnswer_of_cachedAnswer_eq_none {q : PermQuery α} {cache : Cache α}
    (h : cachedAnswer cache q = none) :
    forgetfulAnswer q cache =
      (PMF.uniformOfFintype α).map fun a => (a, PermQuery.toCacheEntry ⟨q, a⟩ :: cache) := by
  cases q with
  | forward x => exact forgetfulAnswer_forward_of_none h
  | inverse y => exact forgetfulAnswer_inverse_of_none h

/-- Interpreting a `bidirDedupStep`-wrapped program against i.i.d. uniform answers from `α` produces
the exact same joint result and cache distribution as `forgetfulAnswer`. -/
theorem interpret_run_bidirDedupStep_uniformOfFintype {β : Type}
    (program : OracleComp (PermOracleSpec α) β) (cache : Cache α) :
    OracleComp.interpret (fun _ : PermQuery α => PMF.uniformOfFintype α)
      ((OracleComp.interpret bidirDedupStep program).run cache) =
    (OracleComp.interpret forgetfulAnswer program).run cache := by
  induction program using OracleComp.induction generalizing cache with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
    change ((OracleComp.interpret (fun _ : PermQuery α => PMF.uniformOfFintype α)
      (bidirDedupStep q cache)).bind fun p =>
        OracleComp.interpret (fun _ : PermQuery α => PMF.uniformOfFintype α)
          ((OracleComp.interpret bidirDedupStep (cont p.1)).run p.2)) =
      ((forgetfulAnswer q cache).bind fun p =>
        (OracleComp.interpret forgetfulAnswer (cont p.1)).run p.2)
    cases h : cachedAnswer cache q with
    | some a =>
      rw [bidirDedupStep_of_cachedAnswer_eq_some h, forgetfulAnswer_of_cachedAnswer_eq_some h]
      simp only [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
      exact ih a cache
    | none =>
      rw [bidirDedupStep_of_cachedAnswer_eq_none h, forgetfulAnswer_of_cachedAnswer_eq_none h]
      simp only [pmf_norm, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure]
      exact congrArg (PMF.bind _) (funext fun a => ih a (PermQuery.toCacheEntry ⟨q, a⟩ :: cache))

/-- Interpreting `bidirDedup program` against i.i.d. uniform answers from `α` produces the exact
same joint result and cache distribution as `(OracleComp.interpret forgetfulAnswer program).run []`.
-/
theorem interpret_bidirDedup_uniformOfFintype {β : Type}
    (program : OracleComp (PermOracleSpec α) β) :
    OracleComp.interpret (fun _ : PermQuery α => PMF.uniformOfFintype α)
      (bidirDedup program) =
    (OracleComp.interpret forgetfulAnswer program).run [] :=
  interpret_run_bidirDedupStep_uniformOfFintype program []

/-- On forward-only programs (`liftForward`), `forgetfulAnswer` never queries `invLookup`, so its
joint result and cache distribution is identical to `memoize (fun _ => PMF.uniformOfFintype α)`. -/
theorem run_interpret_forgetfulAnswer_liftForward {β : Type}
    (program : OracleComp (fun _ : α => α) β) (cache : Cache α) :
    (OracleComp.interpret forgetfulAnswer (liftForward program)).run cache =
      (OracleComp.interpret (memoize (fun _ : α => PMF.uniformOfFintype α)) program).run cache := by
  rw [liftForward, OracleComp.interpret_interpret]
  congr 2
  funext x c
  cases h : c.lookup x <;>
    simp [forgetfulAnswer, h, memoize_of_none, memoize_of_some, PMF.map, Function.comp_def,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- Forgetful lazy handler instrumented with a `bad` flag that records whether a fresh draw fell
outside `freshAnswers`: a forward draw collided with `ran(cache)` or an inverse draw collided with
`dom(cache)`. -/
private noncomputable def forgetfulWithBad (q : PermQuery α) :
    StateT (Cache α × Bool) PMF α := fun (cache, bad) =>
  match cachedAnswer cache q with
  | some a => PMF.pure (a, (cache, bad))
  | none =>
    (PMF.uniformOfFintype α).map fun a =>
      (a, (PermQuery.toCacheEntry ⟨q, a⟩ :: cache, bad || decide (a ∉ freshAnswers cache q)))

/-- Coupled exact lazy handler with a `bad` flag: draw a candidate uniformly from `α`; if it lies in
`freshAnswers` (`unusedRange` for a forward query, `unusedDomain` for an inverse one), use it
directly, and otherwise set `bad := true` and resample with `answer`. -/
private noncomputable def exactWithBad (q : PermQuery α) :
    StateT (Cache α × Bool) PMF α := fun (cache, bad) =>
  match cachedAnswer cache q with
  | some a => PMF.pure (a, (cache, bad))
  | none => do
    let a₀ ← PMF.uniformOfFintype α
    if a₀ ∈ freshAnswers cache q then
      PMF.pure (a₀, (PermQuery.toCacheEntry ⟨q, a₀⟩ :: cache, bad))
    else
      (answer q cache).map fun (a, cache') => (a, (cache', true))

private theorem forgetfulWithBad_map_fst (q : PermQuery α) (st : Cache α × Bool) :
    (forgetfulWithBad q st).map (fun (a, st') => (a, st'.1)) = forgetfulAnswer q st.1 := by
  rcases st with ⟨cache, bad⟩
  cases h : cachedAnswer cache q with
  | some a => simp [forgetfulWithBad, forgetfulAnswer_of_cachedAnswer_eq_some h, h, PMF.pure_map]
  | none =>
    simp [forgetfulWithBad, forgetfulAnswer_of_cachedAnswer_eq_none h, h, PMF.map_comp,
      Function.comp_def]

private theorem run_interpret_forgetfulWithBad_map_fst {β : Type}
    (program : OracleComp (PermOracleSpec α) β) (cache : Cache α) (bad : Bool) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret forgetfulAnswer program).run cache :=
  OracleComp.run_interpret_map_state forgetfulWithBad forgetfulAnswer Prod.fst
    forgetfulWithBad_map_fst program (cache, bad)

/-- **Finite-set resampling identity**: drawing `a₀ ← PMF.uniformOfFintype α` and returning `a₀` if
`a₀ ∈ S` or resampling from `PMF.uniformOfFinset S hS` if `a₀ ∉ S` produces
`PMF.uniformOfFinset S hS`. -/
private theorem uniformOfFintype_bind_ite_uniformOfFinset (S : Finset α) (hS : S.Nonempty) :
    ((PMF.uniformOfFintype α).bind fun a₀ =>
      if a₀ ∈ S then PMF.pure a₀ else PMF.uniformOfFinset S hS) =
    PMF.uniformOfFinset S hS := by
  ext a
  rw [PMF.bind_apply, tsum_fintype, PMF.uniformOfFinset_apply]
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte]
    have hsplit :
        (∑ a₀ : α, PMF.uniformOfFintype α a₀ *
          (if a₀ ∈ S then PMF.pure a₀ else PMF.uniformOfFinset S hS) a) =
        (∑ a₀ ∈ S, PMF.uniformOfFintype α a₀ * PMF.pure a₀ a) +
          (∑ a₀ ∈ Sᶜ, PMF.uniformOfFintype α a₀ * PMF.uniformOfFinset S hS a) := by
      rw [← Finset.sum_add_sum_compl S]
      congr 1
      · refine Finset.sum_congr rfl fun a₀ ha₀ => by simp [ha₀]
      · refine Finset.sum_congr rfl fun a₀ ha₀ => by
          rw [Finset.mem_compl] at ha₀
          simp [ha₀]
    rw [hsplit]
    have h1 : (∑ a₀ ∈ S, PMF.uniformOfFintype α a₀ * PMF.pure a₀ a) =
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
      have hterm (a₀ : α) : PMF.uniformOfFintype α a₀ * PMF.pure a₀ a =
          if a₀ = a then (Fintype.card α : ℝ≥0∞)⁻¹ else 0 := by
        by_cases h0 : a₀ = a
        · subst h0; simp [PMF.uniformOfFintype_apply]
        · simp [PMF.pure_apply, h0, Ne.symm h0]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq' S a, ite_eq_left ha]
    have h2 : (∑ a₀ ∈ Sᶜ, PMF.uniformOfFintype α a₀ * PMF.uniformOfFinset S hS a) =
        (Sᶜ.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * (S.card : ℝ≥0∞)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply, ha, ↓reduceIte,
        Finset.sum_const, nsmul_eq_mul, mul_assoc]
    rw [h1, h2]
    have hcard : (S.card : ℝ≥0∞) + Sᶜ.card = Fintype.card α := by
      exact_mod_cast Finset.card_add_card_compl S
    have hS_ne : (S.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
    have hS_top : (S.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hα_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc (Fintype.card α : ℝ≥0∞)⁻¹ +
          (Sᶜ.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * (S.card : ℝ≥0∞)⁻¹
        = (S.card : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ * (Fintype.card α : ℝ≥0∞)⁻¹ +
            (Sᶜ.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * (S.card : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hS_ne hS_top, one_mul]
      _ = ((S.card : ℝ≥0∞) + Sᶜ.card) * (Fintype.card α : ℝ≥0∞)⁻¹ * (S.card : ℝ≥0∞)⁻¹ := by
          ring
      _ = (S.card : ℝ≥0∞)⁻¹ := by
          rw [hcard, ENNReal.mul_inv_cancel hα_ne hα_top, one_mul]
  · simp only [ha, ↓reduceIte]
    refine Finset.sum_eq_zero fun a₀ _ => ?_
    by_cases ha₀ : a₀ ∈ S
    · have hne : a ≠ a₀ := fun h => ha (h ▸ ha₀)
      simp [ha₀, PMF.pure_apply, hne]
    · simp [ha₀, PMF.uniformOfFinset_apply, ha]

private theorem exactWithBad_preserve_isPartialBijection (q : PermQuery α) (st : Cache α × Bool)
    (hst : IsPartialBijection st.1) (a : α) (st' : Cache α × Bool)
    (hmem : (a, st') ∈ (exactWithBad q st).support) :
    IsPartialBijection st'.1 := by
  rcases st with ⟨cache, bad⟩
  cases hq : cachedAnswer cache q with
  | some b =>
    simp only [exactWithBad, hq, PMF.mem_support_pure_iff] at hmem
    exact (Prod.mk.inj hmem).2 ▸ hst
  | none =>
    simp only [exactWithBad, hq, Probability.PMF.monad_bind_eq_bind,
      PMF.mem_support_bind_iff] at hmem
    obtain ⟨a₀, -, ha₀⟩ := hmem
    by_cases hfresh : a₀ ∈ freshAnswers cache q
    · rw [ite_eq_left hfresh, PMF.mem_support_pure_iff] at ha₀
      obtain ⟨_, rfl⟩ := Prod.mk.inj ha₀
      exact hst.cons_toCacheEntry hq hfresh
    · rw [ite_eq_right hfresh, PMF.mem_support_map_iff] at ha₀
      obtain ⟨⟨b, cache'⟩, hmem', heq⟩ := ha₀
      obtain ⟨_, rfl⟩ := Prod.mk.inj heq
      exact answer_preserve_isPartialBijection q cache hst b cache' hmem'

private theorem exactWithBad_map_fst (q : PermQuery α) (st : Cache α × Bool)
    (hst : IsPartialBijection st.1) :
    (exactWithBad q st).map (fun (a, st') => (a, st'.1)) = answer q st.1 := by
  rcases st with ⟨cache, bad⟩
  cases hq : cachedAnswer cache q with
  | some a => simp [exactWithBad, answer_of_cachedAnswer_eq_some hq, hq, PMF.pure_map]
  | none =>
    have hne := hst.freshAnswers_nonempty hq
    have hans := answer_of_cachedAnswer_eq_none hq hne
    simp only [exactWithBad, hq, Probability.PMF.monad_bind_eq_bind]
    conv_rhs =>
      rw [hans, ← uniformOfFintype_bind_ite_uniformOfFinset (freshAnswers cache q) hne,
        PMF.map_bind]
    rw [PMF.map_bind]
    congr 1 with a₀ : 1
    by_cases ha₀ : a₀ ∈ freshAnswers cache q
    · simp [ha₀, PMF.pure_map]
    · simp [ha₀, hans, PMF.map_comp, Function.comp_def]

private theorem run_interpret_exactWithBad_map_fst {β : Type}
    (program : OracleComp (PermOracleSpec α) β) (cache : Cache α) (bad : Bool)
    (hcache : IsPartialBijection cache) :
    ((OracleComp.interpret exactWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret answer program).run cache :=
  OracleComp.run_interpret_map_state_of_invariant exactWithBad answer Prod.fst
    (fun st => IsPartialBijection st.1) exactWithBad_preserve_isPartialBijection
    exactWithBad_map_fst program (cache, bad) hcache

/-- `exactWithBad` and `forgetfulWithBad` are identical until `bad = true`. -/
private theorem identicalUntilBad_exactWithBad_forgetfulWithBad :
    IdenticalUntilBad (spec := PermOracleSpec α) exactWithBad forgetfulWithBad
      (fun st : Cache α × Bool => st.2 = true) where
  agree q st hst a st' hst' := by
    rcases st with ⟨cache, bad⟩
    rcases st' with ⟨cache', bad'⟩
    have hbad : bad = false := Bool.eq_false_iff.mpr hst
    have hbad' : bad' = false := Bool.eq_false_iff.mpr hst'
    subst hbad hbad'
    cases hq : cachedAnswer cache q with
    | some b => simp only [exactWithBad, forgetfulWithBad, hq]
    | none =>
      simp only [exactWithBad, forgetfulWithBad, hq, Probability.PMF.monad_bind_eq_bind]
      rw [PMF.bind_apply, PMF.map_apply]
      refine tsum_congr fun a₀ => ?_
      by_cases ha₀ : a₀ ∈ freshAnswers cache q
      · rw [ite_eq_left ha₀, PMF.pure_apply]
        simp [ha₀]
      · have h0 : ((answer q cache).map fun p => (p.1, p.2, true)) (a, cache', false) = 0 := by
          rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
          rintro ⟨p, -, hp⟩
          exact Bool.noConfusion (Prod.mk.inj (Prod.mk.inj hp).2).2
        rw [ite_eq_right ha₀, h0]
        simp [ha₀]
  absorb_first q st hst p hp := by
    rcases st with ⟨cache, bad⟩
    dsimp at hst
    subst hst
    cases hq : cachedAnswer cache q with
    | some b =>
      simp only [exactWithBad, hq, PMF.mem_support_pure_iff] at hp
      rw [hp]
    | none =>
      simp only [exactWithBad, hq, Probability.PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hp
      obtain ⟨a₀, -, ha₀⟩ := hp
      by_cases hfresh : a₀ ∈ freshAnswers cache q
      · rw [ite_eq_left hfresh, PMF.mem_support_pure_iff] at ha₀
        rw [ha₀]
      · rw [ite_eq_right hfresh, PMF.mem_support_map_iff] at ha₀
        obtain ⟨_, -, rfl⟩ := ha₀
        rfl
  absorb_second q st hst p hp := by
    rcases st with ⟨cache, bad⟩
    dsimp at hst
    subst hst
    cases hq : cachedAnswer cache q with
    | some b =>
      simp only [forgetfulWithBad, hq, PMF.mem_support_pure_iff] at hp
      rw [hp]
    | none =>
      simp only [forgetfulWithBad, hq, PMF.mem_support_map_iff] at hp
      obtain ⟨a₀, -, rfl⟩ := hp
      simp

/-! ### Quadratic union bound for linearly growing collision sets -/

/-- If each oracle call from a good state `s` turns bad with probability at most `size s * δ` and
increases `size` by at most `1`, then an adaptive program making at most `n` queries reaches a bad
state from `s` with probability at most `(n * size s + n.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_le {ι σ β : Type} {spec : ι → Type}
    {handler : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}
    (size : σ → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s → (handler q s).toOuterMeasure {x | bad x.2} ≤ size s * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 → size x.2 ≤ size s + 1)
    {program : OracleComp spec β} {n : ℕ} (hn : IsQueryBounded program n)
    {s : σ} (hs : ¬bad s) :
    ((OracleComp.interpret handler program).run s).toOuterMeasure {x | bad x.2} ≤
      (n * size s + n.choose 2 : ℕ) * δ := by
  induction hn generalizing s with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right (show (a, s) ∉ {x : β × σ | bad x.2} from hs)]
    exact zero_le
  | liftBind q cont n _ ih =>
    classical
    simp only [run_interpret_bind, run_interpret_query,
      Probability.PMF.monad_bind_eq_bind, PMF.toOuterMeasure_bind_apply]
    set K : ℝ≥0∞ := (n * (size s + 1) + n.choose 2 : ℕ) * δ
    have hterm (y : spec q × σ) :
        (handler q s) y *
          ((OracleComp.interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2} ≤
        (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) := by
      by_cases hmem : y ∈ (handler q s).support
      · refine mul_le_mul_of_nonneg_left ?_ zero_le
        by_cases hy : bad y.2
        · have : y ∈ {x : spec q × σ | bad x.2} := hy
          rw [Set.indicator_of_mem this, Pi.one_apply]
          exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
        · have : y ∉ {x : spec q × σ | bad x.2} := hy
          rw [Set.indicator_of_notMem this, zero_add]
          refine (ih y.1 hy).trans ?_
          simp only [K]
          gcongr
          exact hgrow q s hs y hmem hy
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
    calc ∑' y, (handler q s) y *
          ((OracleComp.interpret handler (cont y.1)).run y.2).toOuterMeasure {x | bad x.2}
        ≤ ∑' y, (handler q s) y * ({x : spec q × σ | bad x.2}.indicator 1 y + K) :=
          tsum_le_tsum hterm
      _ = (handler q s).toOuterMeasure {x | bad x.2} + K := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
      _ ≤ size s * δ + K := add_le_add (hstep q s hs) le_rfl
      _ = ((n + 1) * size s + (n + 1).choose 2 : ℕ) * δ := by
          simp only [K, Nat.choose_succ_succ' n 1, Nat.choose_one_right, Nat.cast_add,
            Nat.cast_mul, Nat.cast_one]
          ring

/-- Over an `n`-query-bounded program starting from `(cache, false)`, `forgetfulWithBad` reaches
`bad = true` with probability at most `(n * cache.length + n.choose 2) * |α|⁻¹`. -/
private theorem toOuterMeasure_bad_forgetfulWithBad_le {β : Type}
    {program : OracleComp (PermOracleSpec α) β} {n : ℕ}
    (hn : IsQueryBounded program n) (cache : Cache α) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, false)).toOuterMeasure
      {x | x.2.2 = true} ≤
      (n * cache.length + n.choose 2 : ℕ) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  refine toOuterMeasure_bad_choose_two_le (bad := fun st : Cache α × Bool => st.2 = true)
    (fun st : Cache α × Bool => st.1.length)
    (Fintype.card α : ℝ≥0∞)⁻¹ ?_ ?_ hn Bool.false_ne_true
  · intro q ⟨c, b⟩ hb
    have hb' : b = false := Bool.eq_false_iff.mpr hb
    subst hb'
    cases hq : cachedAnswer c q with
    | some a => simp [forgetfulWithBad, hq, PMF.toOuterMeasure_pure_apply]
    | none =>
      have hpre : (fun a : α => (a, (PermQuery.toCacheEntry ⟨q, a⟩ :: c,
          false || decide (a ∉ freshAnswers c q)))) ⁻¹'
          {x : α × (Cache α × Bool) | x.2.2 = true} = {a : α | a ∉ freshAnswers c q} := by
        ext a
        simp
      have hcard : (Finset.univ.filter fun a : α => a ∉ freshAnswers c q).card ≤ c.length := by
        cases q with
        | forward x =>
          simpa [freshAnswers, invLookup, Option.ne_none_iff_isSome] using
            RandomOracle.card_filter_lookup_isSome_le (c.map Prod.swap)
        | inverse y =>
          simpa [freshAnswers, Option.ne_none_iff_isSome] using
            RandomOracle.card_filter_lookup_isSome_le c
      simp only [forgetfulWithBad, hq]
      rw [PMF.toOuterMeasure_map_apply, hpre, PMF.toOuterMeasure_uniformOfFintype]
      gcongr
      exact Nat.cast_le.mpr hcard
  · intro q ⟨c, b⟩ _ p hp _
    cases hq : cachedAnswer c q with
    | some a =>
      simp only [forgetfulWithBad, hq, PMF.mem_support_pure_iff] at hp
      rw [hp]
      exact Nat.le_succ _
    | none =>
      simp only [forgetfulWithBad, hq, PMF.mem_support_map_iff] at hp
      obtain ⟨a₀, -, rfl⟩ := hp
      simp

/-- **Bidirectional random-permutation switching inequality (`ℝ≥0∞`, one-sided)**: for any
`Q`-query adaptive program, evaluating against a uniform permutation accepts within
`Q.choose 2 * |α|⁻¹` of evaluating against `forgetfulAnswer`. -/
theorem uniformPerm_bind_apply_le_forgetful {β γ : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    ((do
      let π ← PMF.uniformOfFintype (Equiv.Perm α)
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program).bind next) c ≤
    ((((OracleComp.interpret forgetfulAnswer program).run []).map Prod.fst).bind next) c +
      (Q.choose 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniform_interpret_eq_lazy,
    ← run_interpret_exactWithBad_map_fst program [] false isPartialBijection_nil,
    ← run_interpret_forgetfulWithBad_map_fst program [] false]
  simp only [pmf_norm]
  have hdiff := identicalUntilBad_exactWithBad_forgetfulWithBad.bind_apply_le
    program ([], false) (fun x => next x.1) c
  rw [identicalUntilBad_exactWithBad_forgetfulWithBad.bad_eq] at hdiff
  refine hdiff.trans (add_le_add le_rfl ?_)
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ []
  simpa only [List.length_nil, mul_zero, zero_add] using hbad

/-- **Reverse bidirectional random-permutation switching inequality (`ℝ≥0∞`, one-sided)**: for any
`Q`-query adaptive program, evaluating against `forgetfulAnswer` accepts within
`Q.choose 2 * |α|⁻¹` of evaluating against a uniform permutation. -/
theorem forgetfulAnswer_bind_apply_le_uniformPerm {β γ : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    ((((OracleComp.interpret forgetfulAnswer program).run []).map Prod.fst).bind next) c ≤
    ((do
      let π ← PMF.uniformOfFintype (Equiv.Perm α)
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program).bind next) c +
      (Q.choose 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniform_interpret_eq_lazy,
    ← run_interpret_exactWithBad_map_fst program [] false isPartialBijection_nil,
    ← run_interpret_forgetfulWithBad_map_fst program [] false]
  simp only [pmf_norm]
  have hdiff := identicalUntilBad_exactWithBad_forgetfulWithBad.symm.bind_apply_le
    program ([], false) (fun x => next x.1) c
  refine hdiff.trans (add_le_add le_rfl ?_)
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ []
  simpa only [List.length_nil, mul_zero, zero_add] using hbad

private theorem forgetfulWithBad_step_good (q : PermQuery α) (c c' : Cache α) (a : α)
    (hmem : (a, (c', false)) ∈ (forgetfulWithBad q (c, false)).support)
    (hp1 : c.Pairwise (fun x y => x.1 ≠ y.1)) (hp2 : c.Pairwise (fun x y => x.2 ≠ y.2)) :
    c'.Pairwise (fun x y => x.1 ≠ y.1) ∧ c'.Pairwise (fun x y => x.2 ≠ y.2) ∧
      c'.length ≤ c.length + 1 := by
  cases hq : cachedAnswer c q with
  | some b =>
    simp only [forgetfulWithBad, hq, PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, heq⟩ := Prod.mk.inj hmem
    obtain ⟨rfl, _⟩ := Prod.mk.inj heq
    exact ⟨hp1, hp2, Nat.le_succ _⟩
  | none =>
    simp only [forgetfulWithBad, hq, PMF.mem_support_map_iff] at hmem
    obtain ⟨a₀, -, heq⟩ := hmem
    obtain ⟨rfl, heq'⟩ := Prod.mk.inj heq
    obtain ⟨rfl, hbad⟩ := Prod.mk.inj heq'
    have hfresh : a₀ ∈ freshAnswers c q := by simpa using hbad
    obtain ⟨h1, h2⟩ := lookup_and_invLookup_toCacheEntry_eq_none hq hfresh
    exact ⟨List.pairwise_cons.mpr ⟨fun e he => (lookup_eq_none_iff.mp h1 e he).symm, hp1⟩,
      List.pairwise_cons.mpr ⟨fun e he => (invLookup_eq_none_iff.mp h2 e he).symm, hp2⟩,
      le_rfl⟩

private theorem forgetfulWithBad_pairwise_and_length_le {β : Type}
    {program : OracleComp (PermOracleSpec α) β} {n : ℕ}
    (hn : IsQueryBounded program n) {c c' : Cache α} {a : β}
    (hp1 : c.Pairwise (fun x y => x.1 ≠ y.1)) (hp2 : c.Pairwise (fun x y => x.2 ≠ y.2))
    (hmem : (a, (c', false)) ∈
      ((OracleComp.interpret forgetfulWithBad program).run (c, false)).support) :
    c'.Pairwise (fun x y => x.1 ≠ y.1) ∧ c'.Pairwise (fun x y => x.2 ≠ y.2) ∧
      c'.length ≤ c.length + n := by
  induction hn generalizing c with
  | pure b n =>
    change (a, (c', false)) ∈ (PMF.pure (b, (c, false))).support at hmem
    rw [PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, heq⟩ := Prod.mk.inj hmem
    obtain ⟨rfl, _⟩ := Prod.mk.inj heq
    exact ⟨hp1, hp2, Nat.le_add_right _ _⟩
  | liftBind q cont n _ ih =>
    change (a, (c', false)) ∈
      ((forgetfulWithBad q (c, false)).bind fun y =>
        (OracleComp.interpret forgetfulWithBad (cont y.1)).run y.2).support at hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨r, c₁, b₁⟩, hstep, hcont⟩ := hmem
    cases b₁ with
    | false =>
      obtain ⟨hp1', hp2', hlen₁⟩ := forgetfulWithBad_step_good q c c₁ r hstep hp1 hp2
      obtain ⟨hp1'', hp2'', hlen₂⟩ := ih r hp1' hp2' hcont
      exact ⟨hp1'', hp2'', by omega⟩
    | true =>
      have hbad := bad_of_mem_support_run
        identicalUntilBad_exactWithBad_forgetfulWithBad.absorb_second (cont r) rfl _ hcont
      exact Bool.noConfusion hbad

/-- Any final-cache event `P` under `forgetfulAnswer` on a `Q`-query-bounded program has
probability at most that of `(c.Pairwise (fun a b => a.1 ≠ b.1) ∧ c.Pairwise (fun a b => a.2 ≠ b.2)
∧ c.length ≤ Q) ∧ P c` plus the `Q.choose 2 * |α|⁻¹` collision probability of
`forgetfulWithBad`. -/
theorem toOuterMeasure_forgetfulAnswer_le_pairwise_and_length_le_add {β : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (P : Cache α → Prop) :
    ((OracleComp.interpret forgetfulAnswer program).run []).toOuterMeasure {x | P x.2} ≤
      ((OracleComp.interpret forgetfulAnswer program).run []).toOuterMeasure
        {x | (x.2.Pairwise (fun a b => a.1 ≠ b.1) ∧
          x.2.Pairwise (fun a b => a.2 ≠ b.2) ∧ x.2.length ≤ Q) ∧ P x.2} +
      (Q.choose 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  rw [← run_interpret_forgetfulWithBad_map_fst program [] false,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ []
  simp only [List.length_nil, mul_zero, zero_add] at hbad
  refine le_trans ?_ (add_le_add le_rfl hbad)
  set q := (OracleComp.interpret forgetfulWithBad program).run ([], false)
  change q.toOuterMeasure ((fun x : β × (Cache α × Bool) => (x.1, x.2.1)) ⁻¹' {x | P x.2}) ≤
    q.toOuterMeasure ((fun x : β × (Cache α × Bool) => (x.1, x.2.1)) ⁻¹'
      {x | (x.2.Pairwise (fun a b => a.1 ≠ b.1) ∧
        x.2.Pairwise (fun a b => a.2 ≠ b.2) ∧ x.2.length ≤ Q) ∧ P x.2}) +
      q.toOuterMeasure {x | x.2.2 = true}
  simp only [PMF.toOuterMeasure_apply, ← tsum_add]
  refine tsum_le_tsum fun ⟨a, c, b⟩ => ?_
  by_cases hmem : (a, (c, b)) ∈ q.support
  · by_cases hP : P c
    · cases b with
      | false =>
        obtain ⟨hp1, hp2, hlen⟩ := forgetfulWithBad_pairwise_and_length_le hQ
          List.Pairwise.nil List.Pairwise.nil hmem
        have hg : c.Pairwise (fun a b => a.1 ≠ b.1) ∧
            c.Pairwise (fun a b => a.2 ≠ b.2) ∧ c.length ≤ Q :=
          ⟨hp1, hp2, by simpa using hlen⟩
        simp [hP, hg]
      | true =>
        simp [hP]
    · simp [hP]
  · have hz : q (a, (c, b)) = 0 := (PMF.apply_eq_zero_iff _ _).mpr hmem
    simp [Set.indicator_apply, hz]

/-- **Bidirectional random-permutation switching bound (`ℝ`, two-sided, [BonehShoup2023],
Section 4.7)**: for any `Q`-query adaptive program, the output distributions under a uniform
permutation `π ← PMF.uniformOfFintype (Equiv.Perm α)` and under the forgetful lazy sampler
`forgetfulAnswer` differ in probability on every event by at most `Q.choose 2 / |α|`. -/
theorem abs_sub_uniformPerm_forgetful_le {β γ : Type}
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    |(((do
        let π ← PMF.uniformOfFintype (Equiv.Perm α)
        OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program).bind next) c).toReal -
      (((((OracleComp.interpret forgetfulAnswer program).run []).map
        Prod.fst).bind next) c).toReal| ≤
      (Q.choose 2 : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
  rw [uniform_interpret_eq_lazy,
    ← run_interpret_exactWithBad_map_fst program [] false isPartialBijection_nil,
    ← run_interpret_forgetfulWithBad_map_fst program [] false]
  simp only [pmf_norm]
  have hdiff := identicalUntilBad_exactWithBad_forgetfulWithBad.abs_sub_le
    program ([], false) (fun x => next x.1) c
  rw [identicalUntilBad_exactWithBad_forgetfulWithBad.bad_eq] at hdiff
  refine hdiff.trans ?_
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ []
  simp only [List.length_nil, mul_zero, zero_add] at hbad
  have htop : ((Q.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv] using
    ENNReal.toReal_mono htop hbad

/-- **The PRP/PRF switching lemma (`ℝ`, two-sided, [BonehShoup2023], Section 4.4, Theorem 4.4)**:
for any `Q`-query forward-only adaptive program `program : OracleComp (fun _ : α => α) β`, the
acceptance probabilities under a uniformly random permutation
`π ← PMF.uniformOfFintype (Equiv.Perm α)` and under a uniformly random function
`f ← PMF.uniformOfFintype (α → α)` differ by at most `Q.choose 2 / |α|`. -/
theorem abs_sub_uniformPerm_uniformFunc_le {β γ : Type}
    {program : OracleComp (fun _ : α => α) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    |(((do
        let π ← PMF.uniformOfFintype (Equiv.Perm α)
        OracleComp.interpret (fun x => PMF.pure (π x)) program).bind next) c).toReal -
      (((do
        let f ← PMF.uniformOfFintype (α → α)
        OracleComp.interpret (fun x => PMF.pure (f x)) program).bind next) c).toReal| ≤
      (Q.choose 2 : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
  have h := abs_sub_uniformPerm_forgetful_le (isQueryBounded_liftForward hQ) next c
  have hperm :
      (do
        let π ← PMF.uniformOfFintype (Equiv.Perm α)
        OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (liftForward program)) =
      (do
        let π ← PMF.uniformOfFintype (Equiv.Perm α)
        OracleComp.interpret (fun x => PMF.pure (π x)) program) := by
    simp only [interpret_evalPerm_liftForward]
  have hfunc :
      (((OracleComp.interpret forgetfulAnswer (liftForward program)).run []).map Prod.fst) =
      (do
        let f ← PMF.uniformOfFintype (α → α)
        OracleComp.interpret (fun x => PMF.pure (f x)) program) := by
    rw [run_interpret_forgetfulAnswer_liftForward]
    have hm := RandomOracle.interpret_eq_memoize
      (fun _ : α => PMF.uniformOfFintype α) program
    rw [Probability.PMF.pi_uniformOfFintype] at hm
    exact hm.symm
  rwa [hperm, hfunc] at h

end Finite

end Cslib.RandomPermutation
