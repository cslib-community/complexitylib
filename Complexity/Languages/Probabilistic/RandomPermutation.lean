/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Languages.Probabilistic.UntilBad
public import Mathlib.Data.Fintype.Perm
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lazy sampling of random permutations and the PRP/PRF switching lemma

A bidirectional permutation oracle (`PermOracleSpec α`) answers forward queries (`.forward x`) and
inverse queries (`.inverse y`) on a finite type `α`. We provide two lazy stateful samplers over an
association-list cache `Cache α = List (α × α)`:

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

## Main definitions

* `Cslib.RandomPermutation.PermQuery`, `PermQuery.ofBoolProd`, `PermOracleSpec`, `evalPerm`,
  `liftForward`, `liftBoolProd`: bidirectional permutation queries, oracle specification,
  deterministic evaluation, and query liftings.
* `Cslib.RandomPermutation.Cache`, `invLookup`, `AgreesWith`, `IsPartialBijection`, `extPerms`,
  `unusedDomain`, `unusedRange`: partial bijection caches and extension sets.
* `Cslib.RandomPermutation.answer`, `complete`, `forgetfulAnswer`: exact and forgetful lazy
  bidirectional permutation samplers and uniform completion.

## Main results

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
  induction cache with
  | nil => cases h
  | cons e rest ih =>
    rw [List.lookup_cons] at h
    cases hxe : x == e.1 with
    | true =>
      rw [hxe] at h
      dsimp at h
      obtain rfl : e.2 = y := Option.some.inj h
      obtain rfl : x = e.1 := eq_of_beq hxe
      exact List.mem_cons_self
    | false =>
      rw [hxe] at h
      exact List.mem_cons_of_mem e (ih h)

/-- If `invLookup cache y = some x`, then the pair `(x, y)` belongs to `cache`. -/
theorem mem_of_invLookup_eq_some {cache : Cache α} {y x : α} (h : invLookup cache y = some x) :
    (x, y) ∈ cache := by
  have hswap := mem_of_lookup_eq_some h
  rw [List.mem_map] at hswap
  obtain ⟨⟨a, b⟩, hmem, heq⟩ := hswap
  dsimp [Prod.swap] at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact hmem

/-- Forward lookup of `x` in `cache` returns `none` iff no entry in `cache` has first component
`x`. -/
theorem lookup_eq_none_iff {cache : Cache α} {x : α} :
    cache.lookup x = none ↔ ∀ e ∈ cache, e.1 ≠ x := by
  induction cache with
  | nil => simp
  | cons e rest ih =>
    rw [List.lookup_cons, List.forall_mem_cons]
    cases hxe : x == e.1 with
    | true =>
      have hx : e.1 = x := (eq_of_beq hxe).symm
      simp [hx]
    | false =>
      have hx : e.1 ≠ x := Ne.symm (beq_eq_false_iff_ne.mp hxe)
      simp [hx, ih]

/-- Inverse lookup of `y` in `cache` returns `none` iff no entry in `cache` has second component
`y`. -/
theorem invLookup_eq_none_iff {cache : Cache α} {y : α} :
    invLookup cache y = none ↔ ∀ e ∈ cache, e.2 ≠ y := by
  induction cache with
  | nil => simp
  | cons e rest ih =>
    rw [invLookup_cons, List.forall_mem_cons]
    cases hye : y == e.2 with
    | true =>
      have hy : e.2 = y := (eq_of_beq hye).symm
      simp [hy]
    | false =>
      have hy : e.2 ≠ y := Ne.symm (beq_eq_false_iff_ne.mp hye)
      simp [hy, ih]

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
  have hy₁' := mem_unusedRange_iff.mp hy₁
  have hy₂' := mem_unusedRange_iff.mp hy₂
  refine Finset.card_bij (fun π _ => π.trans (Equiv.swap y₁ y₂)) ?_ ?_ ?_
  · intro π hπ
    obtain ⟨hπx, hπc⟩ := (agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp hπ)
    rw [mem_extPerms_iff, agreesWith_cons]
    refine ⟨by simp [hπx], fun e he => ?_⟩
    have h1 : e.2 ≠ y₁ := invLookup_eq_none_iff.mp hy₁' e he
    have h2 : e.2 ≠ y₂ := invLookup_eq_none_iff.mp hy₂' e he
    simp [hπc e he, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · intro π₁ _ π₂ _ heq
    ext z
    have hz := Equiv.congr_fun heq z
    simpa using (Equiv.swap y₁ y₂).injective hz
  · intro π hπ
    obtain ⟨hπx, hπc⟩ := (agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp hπ)
    refine ⟨π.trans (Equiv.swap y₁ y₂), ?_, ?_⟩
    · rw [mem_extPerms_iff, agreesWith_cons]
      refine ⟨by simp [hπx], fun e he => ?_⟩
      have h1 : e.2 ≠ y₁ := invLookup_eq_none_iff.mp hy₁' e he
      have h2 : e.2 ≠ y₂ := invLookup_eq_none_iff.mp hy₂' e he
      simp [hπc e he, Equiv.swap_apply_of_ne_of_ne h1 h2]
    · ext z
      simp

/-- Pre-composing with `Equiv.swap x₁ x₂` bijects extensions of `(x₁, y) :: cache` onto
extensions of `(x₂, y) :: cache` whenever `x₁, x₂ ∈ unusedDomain cache`. -/
private theorem card_extPerms_cons_eq_of_unusedDomain {cache : Cache α} (y : α)
    {x₁ x₂ : α} (hx₁ : x₁ ∈ unusedDomain cache) (hx₂ : x₂ ∈ unusedDomain cache) :
    (extPerms ((x₁, y) :: cache)).card = (extPerms ((x₂, y) :: cache)).card := by
  have hx₁' := mem_unusedDomain_iff.mp hx₁
  have hx₂' := mem_unusedDomain_iff.mp hx₂
  refine Finset.card_bij (fun π _ => (Equiv.swap x₁ x₂).trans π) ?_ ?_ ?_
  · intro π hπ
    obtain ⟨hπx, hπc⟩ := (agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp hπ)
    rw [mem_extPerms_iff, agreesWith_cons]
    refine ⟨by simp [hπx], fun e he => ?_⟩
    have h1 : e.1 ≠ x₁ := lookup_eq_none_iff.mp hx₁' e he
    have h2 : e.1 ≠ x₂ := lookup_eq_none_iff.mp hx₂' e he
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, hπc e he]
  · intro π₁ _ π₂ _ heq
    ext z
    have hz := Equiv.congr_fun heq (Equiv.swap x₁ x₂ z)
    simpa using hz
  · intro π hπ
    obtain ⟨hπx, hπc⟩ := (agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp hπ)
    refine ⟨(Equiv.swap x₁ x₂).trans π, ?_, ?_⟩
    · rw [mem_extPerms_iff, agreesWith_cons]
      refine ⟨by simp [hπx], fun e he => ?_⟩
      have h1 : e.1 ≠ x₁ := lookup_eq_none_iff.mp hx₁' e he
      have h2 : e.1 ≠ x₂ := lookup_eq_none_iff.mp hx₂' e he
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, hπc e he]
    · ext z
      simp

/-- Partitioning `extPerms cache` by the image `π x` of a fresh input `x` shows that all fibers over
`unusedRange cache` have equal size. -/
theorem card_extPerms_eq_card_unusedRange_mul {cache : Cache α} {x y : α}
    (hx : cache.lookup x = none) (hy : y ∈ unusedRange cache) :
    (extPerms cache).card = (unusedRange cache).card * (extPerms ((x, y) :: cache)).card := by
  have hmaps : ∀ π ∈ extPerms cache, π x ∈ unusedRange cache := fun π hπ =>
    mem_unusedRange_iff.mpr ((mem_extPerms_iff.mp hπ).invLookup_apply_eq_none hx)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (y' : α) (hy' : y' ∈ unusedRange cache) :
      {π ∈ extPerms cache | π x = y'}.card = (extPerms ((x, y) :: cache)).card := by
    have hset : {π ∈ extPerms cache | π x = y'} = extPerms ((x, y') :: cache) := by
      ext π
      simp [And.comm]
    rw [hset]
    exact card_extPerms_cons_eq_of_unusedRange x hy' hy
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]

/-- Partitioning `extPerms cache` by the preimage `π.symm y` of a fresh output `y` shows that all
fibers over `unusedDomain cache` have equal size. -/
theorem card_extPerms_eq_card_unusedDomain_mul {cache : Cache α} {x y : α}
    (hx : x ∈ unusedDomain cache) (hy : invLookup cache y = none) :
    (extPerms cache).card = (unusedDomain cache).card * (extPerms ((x, y) :: cache)).card := by
  have hmaps : ∀ π ∈ extPerms cache, π.symm y ∈ unusedDomain cache := fun π hπ =>
    mem_unusedDomain_iff.mpr ((mem_extPerms_iff.mp hπ).lookup_symm_apply_eq_none hy)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (x' : α) (hx' : x' ∈ unusedDomain cache) :
      {π ∈ extPerms cache | π.symm y = x'}.card = (extPerms ((x, y) :: cache)).card := by
    have hset : {π ∈ extPerms cache | π.symm y = x'} = extPerms ((x', y) :: cache) := by
      ext π
      simp only [Finset.mem_filter, mem_extPerms_iff, agreesWith_cons, Equiv.symm_apply_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, h2.symm⟩⟩
    rw [hset]
    exact card_extPerms_cons_eq_of_unusedDomain y hx' hx
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]

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

/-- `answer` preserves `IsPartialBijection` on every supported transition. -/
theorem answer_preserve_isPartialBijection (q : PermQuery α) (cache : Cache α)
    (hcache : IsPartialBijection cache) (a : α) (cache' : Cache α)
    (hmem : (a, cache') ∈ (answer q cache).support) :
    IsPartialBijection cache' := by
  cases q with
  | forward x =>
    dsimp [answer] at hmem
    cases hx : cache.lookup x with
    | some y =>
      rw [hx, PMF.mem_support_pure_iff] at hmem
      exact (Prod.mk.inj hmem).2 ▸ hcache
    | none =>
      have hne := hcache.unusedRange_nonempty hx
      rw [hx, dite_eq_left hne, PMF.mem_support_map_iff] at hmem
      obtain ⟨y, hy, heq⟩ := hmem
      rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedRange_iff] at hy
      obtain ⟨_, rfl⟩ := Prod.mk.inj heq
      exact hcache.cons_of_lookup_eq_none hx hy
  | inverse y =>
    dsimp [answer] at hmem
    cases hy : invLookup cache y with
    | some x =>
      rw [hy, PMF.mem_support_pure_iff] at hmem
      exact (Prod.mk.inj hmem).2 ▸ hcache
    | none =>
      have hne := hcache.unusedDomain_nonempty hy
      rw [hy, dite_eq_left hne, PMF.mem_support_map_iff] at hmem
      obtain ⟨x, hx, heq⟩ := hmem
      rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedDomain_iff] at hx
      obtain ⟨_, rfl⟩ := Prod.mk.inj heq
      exact hcache.cons_of_lookup_eq_none hx hy

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
  have hext_ne : (extPerms cache).Nonempty := extPerms_nonempty_iff.mpr hcache
  cases q with
  | forward x =>
    dsimp [answer]
    cases hx : cache.lookup x with
    | some y =>
      simp only [PMF.pure_bind]
      ext ⟨a, π⟩
      rw [map_pair_apply, map_pair_apply]
      by_cases hmem : π ∈ extPerms cache
      · have hπx : π x = y := (mem_extPerms_iff.mp hmem).apply_of_lookup_eq_some hx
        simp [hπx]
      · have hzero : complete cache π = 0 := by
          simp [complete, dite_eq_left hext_ne, PMF.uniformOfFinset_apply, hmem]
        simp [hzero]
    | none =>
      have hne := hcache.unusedRange_nonempty hx
      simp only [dite_eq_left hne, PMF.bind_map, Function.comp_def]
      ext ⟨a, π⟩
      rw [map_pair_apply, PMF.bind_apply]
      have hterm (y : α) :
          PMF.uniformOfFinset (unusedRange cache) hne y *
            ((complete ((x, y) :: cache)).map (y, ·)) (a, π) =
          if y = a then
            PMF.uniformOfFinset (unusedRange cache) hne a * complete ((x, a) :: cache) π
          else 0 := by
        rw [map_pair_apply]
        by_cases hya : y = a
        · subst hya; simp
        · simp [hya, Ne.symm hya]
      simp_rw [hterm, tsum_ite_eq]
      by_cases hπ : π ∈ extPerms cache ∧ a = π x
      · obtain ⟨hπ_mem, rfl⟩ := hπ
        have ha : π x ∈ unusedRange cache :=
          mem_unusedRange_iff.mpr ((mem_extPerms_iff.mp hπ_mem).invLookup_apply_eq_none hx)
        have hcons_mem : π ∈ extPerms ((x, π x) :: cache) := by
          rw [mem_extPerms_iff, agreesWith_cons]
          exact ⟨rfl, mem_extPerms_iff.mp hπ_mem⟩
        have hcons_ne : (extPerms ((x, π x) :: cache)).Nonempty := ⟨π, hcons_mem⟩
        rw [complete, dite_eq_left hcons_ne, complete, dite_eq_left hext_ne]
        simp only [PMF.uniformOfFinset_apply, ha, hcons_mem, hπ_mem, ↓reduceIte]
        rw [card_extPerms_eq_card_unusedRange_mul hx ha, Nat.cast_mul,
          ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr hne.card_pos.ne'))
            (Or.inl (ENNReal.natCast_ne_top _))]
      · rw [not_and_or] at hπ
        rcases hπ with hπ_not | hne_ax
        · have h0 : complete cache π = 0 := by
            simp [complete, dite_eq_left hext_ne, PMF.uniformOfFinset_apply, hπ_not]
          rw [h0, ite_self]
          by_cases ha : a ∈ unusedRange cache
          · have hcons_ne : (extPerms ((x, a) :: cache)).Nonempty :=
              extPerms_nonempty_iff.mpr
                (hcache.cons_of_lookup_eq_none hx (mem_unusedRange_iff.mp ha))
            have hnot_cons : π ∉ extPerms ((x, a) :: cache) := fun h =>
              hπ_not (mem_extPerms_iff.mpr ((agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp h)).2)
            simp [complete, dite_eq_left hcons_ne, PMF.uniformOfFinset_apply, hnot_cons]
          · simp [PMF.uniformOfFinset_apply, ha]
        · simp only [hne_ax, ↓reduceIte]
          by_cases ha : a ∈ unusedRange cache
          · have hcons_ne : (extPerms ((x, a) :: cache)).Nonempty :=
              extPerms_nonempty_iff.mpr
                (hcache.cons_of_lookup_eq_none hx (mem_unusedRange_iff.mp ha))
            have hnot_cons : π ∉ extPerms ((x, a) :: cache) := fun h =>
              hne_ax ((agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp h)).1.symm
            simp [complete, dite_eq_left hcons_ne, PMF.uniformOfFinset_apply, hnot_cons]
          · simp [PMF.uniformOfFinset_apply, ha]
  | inverse y =>
    dsimp [answer]
    cases hy : invLookup cache y with
    | some x =>
      simp only [PMF.pure_bind]
      ext ⟨a, π⟩
      rw [map_pair_apply, map_pair_apply]
      by_cases hmem : π ∈ extPerms cache
      · have hπy : π.symm y = x := (mem_extPerms_iff.mp hmem).symm_apply_of_invLookup_eq_some hy
        simp [hπy]
      · have hzero : complete cache π = 0 := by
          simp [complete, dite_eq_left hext_ne, PMF.uniformOfFinset_apply, hmem]
        simp [hzero]
    | none =>
      have hne := hcache.unusedDomain_nonempty hy
      simp only [dite_eq_left hne, PMF.bind_map, Function.comp_def]
      ext ⟨a, π⟩
      rw [map_pair_apply, PMF.bind_apply]
      have hterm (x : α) :
          PMF.uniformOfFinset (unusedDomain cache) hne x *
            ((complete ((x, y) :: cache)).map (x, ·)) (a, π) =
          if x = a then
            PMF.uniformOfFinset (unusedDomain cache) hne a * complete ((a, y) :: cache) π
          else 0 := by
        rw [map_pair_apply]
        by_cases hxa : x = a
        · subst hxa; simp
        · simp [hxa, Ne.symm hxa]
      simp_rw [hterm, tsum_ite_eq]
      by_cases hπ : π ∈ extPerms cache ∧ a = π.symm y
      · obtain ⟨hπ_mem, rfl⟩ := hπ
        have ha : π.symm y ∈ unusedDomain cache :=
          mem_unusedDomain_iff.mpr ((mem_extPerms_iff.mp hπ_mem).lookup_symm_apply_eq_none hy)
        have hcons_mem : π ∈ extPerms ((π.symm y, y) :: cache) := by
          rw [mem_extPerms_iff, agreesWith_cons]
          exact ⟨Equiv.apply_symm_apply π y, mem_extPerms_iff.mp hπ_mem⟩
        have hcons_ne : (extPerms ((π.symm y, y) :: cache)).Nonempty := ⟨π, hcons_mem⟩
        rw [complete, dite_eq_left hcons_ne, complete, dite_eq_left hext_ne]
        simp only [PMF.uniformOfFinset_apply, ha, hcons_mem, hπ_mem, ↓reduceIte]
        rw [card_extPerms_eq_card_unusedDomain_mul ha hy, Nat.cast_mul,
          ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr hne.card_pos.ne'))
            (Or.inl (ENNReal.natCast_ne_top _))]
      · rw [not_and_or] at hπ
        rcases hπ with hπ_not | hne_ay
        · have h0 : complete cache π = 0 := by
            simp [complete, dite_eq_left hext_ne, PMF.uniformOfFinset_apply, hπ_not]
          rw [h0, ite_self]
          by_cases ha : a ∈ unusedDomain cache
          · have hcons_ne : (extPerms ((a, y) :: cache)).Nonempty :=
              extPerms_nonempty_iff.mpr
                (hcache.cons_of_lookup_eq_none (mem_unusedDomain_iff.mp ha) hy)
            have hnot_cons : π ∉ extPerms ((a, y) :: cache) := fun h =>
              hπ_not (mem_extPerms_iff.mpr ((agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp h)).2)
            simp [complete, dite_eq_left hcons_ne, PMF.uniformOfFinset_apply, hnot_cons]
          · simp [PMF.uniformOfFinset_apply, ha]
        · simp only [hne_ay, ↓reduceIte]
          by_cases ha : a ∈ unusedDomain cache
          · have hcons_ne : (extPerms ((a, y) :: cache)).Nonempty :=
              extPerms_nonempty_iff.mpr
                (hcache.cons_of_lookup_eq_none (mem_unusedDomain_iff.mp ha) hy)
            have hnot_cons : π ∉ extPerms ((a, y) :: cache) := fun h =>
              hne_ay (π.symm_apply_eq.mpr
                ((agreesWith_cons _ _ _).mp (mem_extPerms_iff.mp h)).1.symm).symm
            simp [complete, dite_eq_left hcons_ne, PMF.uniformOfFinset_apply, hnot_cons]
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
      simpa only [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.pure_map, PMF.map,
        Function.comp_def, PMF.pure_bind] using answer_complete q c hc)
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
  simpa only [PMF.monad_bind_eq_bind, complete_nil, PMF.map_bind, PMF.map_comp, PMF.map,
    Function.comp_def, PMF.bind_const, PMF.bind_pure, PMF.bind_bind, PMF.pure_bind] using h.symm

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

/-- Forgetful lazy handler instrumented with a `bad` flag that records whether a fresh forward draw
collided with `ran(cache)` or a fresh inverse draw collided with `dom(cache)`. -/
private noncomputable def forgetfulWithBad (q : PermQuery α) :
    StateT (Cache α × Bool) PMF α := fun (cache, bad) =>
  match q with
  | .forward x =>
    match cache.lookup x with
    | some y => PMF.pure (y, (cache, bad))
    | none =>
      (PMF.uniformOfFintype α).map fun y =>
        (y, ((x, y) :: cache, bad || (invLookup cache y).isSome))
  | .inverse y =>
    match invLookup cache y with
    | some x => PMF.pure (x, (cache, bad))
    | none =>
      (PMF.uniformOfFintype α).map fun x =>
        (x, ((x, y) :: cache, bad || (cache.lookup x).isSome))

/-- Coupled exact lazy handler with a `bad` flag: draw a candidate uniformly from `α`; if it lies in
`unusedRange` (resp. `unusedDomain`), use it directly, and otherwise set `bad := true` and resample
uniformly from `unusedRange` (resp. `unusedDomain`). -/
private noncomputable def exactWithBad (q : PermQuery α) :
    StateT (Cache α × Bool) PMF α := fun (cache, bad) =>
  match q with
  | .forward x =>
    match cache.lookup x with
    | some y => PMF.pure (y, (cache, bad))
    | none => do
      let y₀ ← PMF.uniformOfFintype α
      if (invLookup cache y₀).isSome then
        (answer (.forward x) cache).map fun (y, cache') => (y, (cache', true))
      else
        PMF.pure (y₀, ((x, y₀) :: cache, bad))
  | .inverse y =>
    match invLookup cache y with
    | some x => PMF.pure (x, (cache, bad))
    | none => do
      let x₀ ← PMF.uniformOfFintype α
      if (cache.lookup x₀).isSome then
        (answer (.inverse y) cache).map fun (x, cache') => (x, (cache', true))
      else
        PMF.pure (x₀, ((x₀, y) :: cache, bad))

private theorem forgetfulWithBad_map_fst (q : PermQuery α) (st : Cache α × Bool) :
    (forgetfulWithBad q st).map (fun (a, st') => (a, st'.1)) = forgetfulAnswer q st.1 := by
  rcases st with ⟨cache, bad⟩
  cases q with
  | forward x =>
    cases h : cache.lookup x <;>
      simp [forgetfulWithBad, forgetfulAnswer, h, PMF.pure_map, PMF.map_comp, Function.comp_def]
  | inverse y =>
    cases h : invLookup cache y <;>
      simp [forgetfulWithBad, forgetfulAnswer, h, PMF.pure_map, PMF.map_comp, Function.comp_def]

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
  cases q with
  | forward x =>
    dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind] at hmem
    cases hx : cache.lookup x with
    | some y =>
      rw [hx, PMF.mem_support_pure_iff] at hmem
      exact (Prod.mk.inj hmem).2 ▸ hst
    | none =>
      rw [hx, PMF.mem_support_bind_iff] at hmem
      obtain ⟨y₀, -, hy₀⟩ := hmem
      by_cases his : (invLookup cache y₀).isSome
      · rw [ite_eq_left his, PMF.mem_support_map_iff] at hy₀
        obtain ⟨⟨y, cache'⟩, hmem', heq⟩ := hy₀
        obtain ⟨_, rfl⟩ := Prod.mk.inj heq
        exact answer_preserve_isPartialBijection (.forward x) cache hst y cache' hmem'
      · rw [ite_eq_right his, PMF.mem_support_pure_iff] at hy₀
        obtain ⟨_, rfl⟩ := Prod.mk.inj hy₀
        exact hst.cons_of_lookup_eq_none hx (Option.not_isSome_iff_eq_none.mp his)
  | inverse y =>
    dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind] at hmem
    cases hy : invLookup cache y with
    | some x =>
      rw [hy, PMF.mem_support_pure_iff] at hmem
      exact (Prod.mk.inj hmem).2 ▸ hst
    | none =>
      rw [hy, PMF.mem_support_bind_iff] at hmem
      obtain ⟨x₀, -, hx₀⟩ := hmem
      by_cases his : (cache.lookup x₀).isSome
      · rw [ite_eq_left his, PMF.mem_support_map_iff] at hx₀
        obtain ⟨⟨x, cache'⟩, hmem', heq⟩ := hx₀
        obtain ⟨_, rfl⟩ := Prod.mk.inj heq
        exact answer_preserve_isPartialBijection (.inverse y) cache hst x cache' hmem'
      · rw [ite_eq_right his, PMF.mem_support_pure_iff] at hx₀
        obtain ⟨_, rfl⟩ := Prod.mk.inj hx₀
        exact hst.cons_of_lookup_eq_none (Option.not_isSome_iff_eq_none.mp his) hy

private theorem exactWithBad_map_fst (q : PermQuery α) (st : Cache α × Bool)
    (hst : IsPartialBijection st.1) :
    (exactWithBad q st).map (fun (a, st') => (a, st'.1)) = answer q st.1 := by
  rcases st with ⟨cache, bad⟩
  cases q with
  | forward x =>
    dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind]
    cases hx : cache.lookup x with
    | some y => simp [answer, hx, PMF.pure_map]
    | none =>
      have hne := hst.unusedRange_nonempty hx
      have hans : answer (.forward x) cache =
          (PMF.uniformOfFinset (unusedRange cache) hne).map fun y => (y, (x, y) :: cache) := by
        simp [answer, hx, dite_eq_left hne]
      conv_rhs =>
        rw [hans, ← uniformOfFintype_bind_ite_uniformOfFinset (unusedRange cache) hne,
          PMF.map_bind]
      rw [PMF.map_bind]
      congr 1
      funext y₀
      by_cases hy₀ : y₀ ∈ unusedRange cache
      · have his : (invLookup cache y₀).isSome = false := by
          rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
          exact mem_unusedRange_iff.mp hy₀
        simp [hy₀, his, PMF.pure_map]
      · have his : (invLookup cache y₀).isSome = true := by
          rw [← Option.ne_none_iff_isSome]
          exact fun h => hy₀ (mem_unusedRange_iff.mpr h)
        simp [hy₀, his, hans, PMF.map_comp, Function.comp_def]
  | inverse y =>
    dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind]
    cases hy : invLookup cache y with
    | some x => simp [answer, hy, PMF.pure_map]
    | none =>
      have hne := hst.unusedDomain_nonempty hy
      have hans : answer (.inverse y) cache =
          (PMF.uniformOfFinset (unusedDomain cache) hne).map fun x => (x, (x, y) :: cache) := by
        simp [answer, hy, dite_eq_left hne]
      conv_rhs =>
        rw [hans, ← uniformOfFintype_bind_ite_uniformOfFinset (unusedDomain cache) hne,
          PMF.map_bind]
      rw [PMF.map_bind]
      congr 1
      funext x₀
      by_cases hx₀ : x₀ ∈ unusedDomain cache
      · have his : (cache.lookup x₀).isSome = false := by
          rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
          exact mem_unusedDomain_iff.mp hx₀
        simp [hx₀, his, PMF.pure_map]
      · have his : (cache.lookup x₀).isSome = true := by
          rw [← Option.ne_none_iff_isSome]
          exact fun h => hx₀ (mem_unusedDomain_iff.mpr h)
        simp [hx₀, his, hans, PMF.map_comp, Function.comp_def]

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
    cases q with
    | forward x =>
      dsimp [exactWithBad, forgetfulWithBad, Probability.PMF.monad_bind_eq_bind]
      cases hx : cache.lookup x with
      | some y => rfl
      | none =>
        rw [PMF.bind_apply, PMF.map_apply]
        refine tsum_congr fun y₀ => ?_
        by_cases his : (invLookup cache y₀).isSome = true
        · rw [ite_eq_left his, his, Bool.false_or]
          have h0 : ((answer (.forward x) cache).map fun x => (x.1, x.2, true))
              (a, cache', false) = 0 := by
            rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
            rintro ⟨p, -, hp⟩
            exact Bool.noConfusion (Prod.mk.inj (Prod.mk.inj hp).2).2
          have hne : (a, cache', false) ≠ (y₀, (x, y₀) :: cache, true) := fun h =>
            Bool.noConfusion (Prod.mk.inj (Prod.mk.inj h).2).2
          simp [h0, hne]
        · have his' : (invLookup cache y₀).isSome = false := Bool.eq_false_iff.mpr his
          rw [ite_eq_right his, his', Bool.false_or, PMF.pure_apply]
          by_cases heq : (a, cache', false) = (y₀, (x, y₀) :: cache, false) <;> simp [heq]
    | inverse y =>
      dsimp [exactWithBad, forgetfulWithBad, Probability.PMF.monad_bind_eq_bind]
      cases hy : invLookup cache y with
      | some x => rfl
      | none =>
        rw [PMF.bind_apply, PMF.map_apply]
        refine tsum_congr fun x₀ => ?_
        by_cases his : (cache.lookup x₀).isSome = true
        · rw [ite_eq_left his, his, Bool.false_or]
          have h0 : ((answer (.inverse y) cache).map fun x => (x.1, x.2, true))
              (a, cache', false) = 0 := by
            rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
            rintro ⟨p, -, hp⟩
            exact Bool.noConfusion (Prod.mk.inj (Prod.mk.inj hp).2).2
          have hne : (a, cache', false) ≠ (x₀, (x₀, y) :: cache, true) := fun h =>
            Bool.noConfusion (Prod.mk.inj (Prod.mk.inj h).2).2
          simp [h0, hne]
        · have his' : (cache.lookup x₀).isSome = false := Bool.eq_false_iff.mpr his
          rw [ite_eq_right his, his', Bool.false_or, PMF.pure_apply]
          by_cases heq : (a, cache', false) = (x₀, (x₀, y) :: cache, false) <;> simp [heq]
  absorb_first q st hst p hp := by
    rcases st with ⟨cache, bad⟩
    dsimp at hst
    subst hst
    cases q with
    | forward x =>
      dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind] at hp
      cases hx : cache.lookup x with
      | some y =>
        rw [hx, PMF.mem_support_pure_iff] at hp
        rw [hp]
      | none =>
        rw [hx, PMF.mem_support_bind_iff] at hp
        obtain ⟨y₀, -, hy₀⟩ := hp
        by_cases his : (invLookup cache y₀).isSome
        · rw [ite_eq_left his, PMF.mem_support_map_iff] at hy₀
          obtain ⟨_, -, rfl⟩ := hy₀
          rfl
        · rw [ite_eq_right his, PMF.mem_support_pure_iff] at hy₀
          rw [hy₀]
    | inverse y =>
      dsimp [exactWithBad, Probability.PMF.monad_bind_eq_bind] at hp
      cases hy : invLookup cache y with
      | some x =>
        rw [hy, PMF.mem_support_pure_iff] at hp
        rw [hp]
      | none =>
        rw [hy, PMF.mem_support_bind_iff] at hp
        obtain ⟨x₀, -, hx₀⟩ := hp
        by_cases his : (cache.lookup x₀).isSome
        · rw [ite_eq_left his, PMF.mem_support_map_iff] at hx₀
          obtain ⟨_, -, rfl⟩ := hx₀
          rfl
        · rw [ite_eq_right his, PMF.mem_support_pure_iff] at hx₀
          rw [hx₀]
  absorb_second q st hst p hp := by
    rcases st with ⟨cache, bad⟩
    dsimp at hst
    subst hst
    cases q with
    | forward x =>
      dsimp [forgetfulWithBad] at hp
      cases hx : cache.lookup x with
      | some y =>
        rw [hx, PMF.mem_support_pure_iff] at hp
        rw [hp]
      | none =>
        rw [hx, PMF.mem_support_map_iff] at hp
        obtain ⟨y₀, -, rfl⟩ := hp
        simp
    | inverse y =>
      dsimp [forgetfulWithBad] at hp
      cases hy : invLookup cache y with
      | some x =>
        rw [hy, PMF.mem_support_pure_iff] at hp
        rw [hp]
      | none =>
        rw [hy, PMF.mem_support_map_iff] at hp
        obtain ⟨x₀, -, rfl⟩ := hp
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
          ENNReal.tsum_le_tsum hterm
      _ = (handler q s).toOuterMeasure {x | bad x.2} + K := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun y => ?_
          by_cases hy : y ∈ {x : spec q × σ | bad x.2}
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
      _ ≤ size s * δ + K := add_le_add (hstep q s hs) le_rfl
      _ = ((n + 1) * size s + (n + 1).choose 2 : ℕ) * δ := by
          simp only [K, Nat.choose_succ_succ' n 1, Nat.choose_one_right, Nat.cast_add,
            Nat.cast_mul, Nat.cast_one]
          ring

omit [Nonempty α] in
private theorem card_filter_lookup_isSome_le (cache : Cache α) :
    (Finset.univ.filter fun x : α => (cache.lookup x).isSome = true).card ≤ cache.length := by
  have hsub : (Finset.univ.filter fun x : α => (cache.lookup x).isSome = true) ⊆
      (cache.map Prod.fst).toFinset := by
    intro x hx
    rw [Finset.mem_filter, Option.isSome_iff_exists] at hx
    obtain ⟨_, y, hy⟩ := hx
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨(x, y), mem_of_lookup_eq_some hy, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (by simp))

omit [Nonempty α] in
private theorem card_filter_invLookup_isSome_le (cache : Cache α) :
    (Finset.univ.filter fun y : α => (invLookup cache y).isSome = true).card ≤ cache.length := by
  simpa [invLookup] using card_filter_lookup_isSome_le (cache.map Prod.swap)

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
    cases q with
    | forward x =>
      dsimp [forgetfulWithBad]
      cases hx : c.lookup x with
      | some y => simp [PMF.toOuterMeasure_pure_apply]
      | none =>
        have hpre : (fun y : α => (y, ((x, y) :: c, false || (invLookup c y).isSome))) ⁻¹'
            {x : α × (Cache α × Bool) | x.2.2 = true} =
            {y : α | (invLookup c y).isSome = true} := by
          ext y
          simp
        rw [PMF.toOuterMeasure_map_apply, hpre, PMF.toOuterMeasure_uniformOfFintype]
        gcongr
        exact Nat.cast_le.mpr (card_filter_invLookup_isSome_le c)
    | inverse y =>
      dsimp [forgetfulWithBad]
      cases hy : invLookup c y with
      | some x => simp [PMF.toOuterMeasure_pure_apply]
      | none =>
        have hpre : (fun x : α => (x, ((x, y) :: c, false || (c.lookup x).isSome))) ⁻¹'
            {x : α × (Cache α × Bool) | x.2.2 = true} =
            {x : α | (c.lookup x).isSome = true} := by
          ext x
          simp
        rw [PMF.toOuterMeasure_map_apply, hpre, PMF.toOuterMeasure_uniformOfFintype]
        gcongr
        exact Nat.cast_le.mpr (card_filter_lookup_isSome_le c)
  · intro q ⟨c, b⟩ _ p hp _
    cases q with
    | forward x =>
      dsimp [forgetfulWithBad] at hp
      cases hx : c.lookup x with
      | some y =>
        rw [hx, PMF.mem_support_pure_iff] at hp
        rw [hp]
        exact Nat.le_succ _
      | none =>
        rw [hx, PMF.mem_support_map_iff] at hp
        obtain ⟨y₀, -, rfl⟩ := hp
        simp
    | inverse y =>
      dsimp [forgetfulWithBad] at hp
      cases hy : invLookup c y with
      | some x =>
        rw [hy, PMF.mem_support_pure_iff] at hp
        rw [hp]
        exact Nat.le_succ _
      | none =>
        rw [hy, PMF.mem_support_map_iff] at hp
        obtain ⟨x₀, -, rfl⟩ := hp
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
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_map]
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
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_map]
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
  cases q with
  | forward x =>
    dsimp [forgetfulWithBad] at hmem
    cases hx : c.lookup x with
    | some y =>
      rw [hx, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, heq⟩ := Prod.mk.inj hmem
      obtain ⟨rfl, _⟩ := Prod.mk.inj heq
      exact ⟨hp1, hp2, Nat.le_succ _⟩
    | none =>
      rw [hx, PMF.mem_support_map_iff] at hmem
      obtain ⟨y, -, heq⟩ := hmem
      obtain ⟨rfl, heq'⟩ := Prod.mk.inj heq
      obtain ⟨rfl, hbad⟩ := Prod.mk.inj heq'
      rw [Bool.false_or, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hbad
      exact ⟨List.pairwise_cons.mpr ⟨fun e he => (lookup_eq_none_iff.mp hx e he).symm, hp1⟩,
        List.pairwise_cons.mpr ⟨fun e he => (invLookup_eq_none_iff.mp hbad e he).symm, hp2⟩,
        le_rfl⟩
  | inverse y =>
    dsimp [forgetfulWithBad] at hmem
    cases hy : invLookup c y with
    | some x =>
      rw [hy, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, heq⟩ := Prod.mk.inj hmem
      obtain ⟨rfl, _⟩ := Prod.mk.inj heq
      exact ⟨hp1, hp2, Nat.le_succ _⟩
    | none =>
      rw [hy, PMF.mem_support_map_iff] at hmem
      obtain ⟨x, -, heq⟩ := hmem
      obtain ⟨rfl, heq'⟩ := Prod.mk.inj heq
      obtain ⟨rfl, hbad⟩ := Prod.mk.inj heq'
      rw [Bool.false_or, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hbad
      exact ⟨List.pairwise_cons.mpr ⟨fun e he => (lookup_eq_none_iff.mp hbad e he).symm, hp1⟩,
        List.pairwise_cons.mpr ⟨fun e he => (invLookup_eq_none_iff.mp hy e he).symm, hp2⟩,
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
  simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun ⟨a, c, b⟩ => ?_
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
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_map]
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
