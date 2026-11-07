/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Matroid.Greedy
public import Mathlib.Combinatorics.Matroid.Constructions

/-!
# Independence-Oracle Query Lower Bound for Matroid Optimization

Any deterministic independence-oracle algorithm (`FreeM (IndepQuery α)`) that finds a basis—or even
merely a maximum-cardinality independent subset—of `{x | x ∈ xs}` must make at least
`xs.toFinset.card` oracle queries in the worst case (`xs.length` when `xs.Nodup`), matching the
exact `n`-query upper bound of `matroidGreedySelect`, `matroidGreedyMaxBasis`,
`matroidGreedyMinBasis`, and `matroidGreedyMaxIndep` with constant factor `1`.

## Proof overview

Consider the all-loops oracle `IndepQuery.loopyOracle` (`S = ∅`), which implements
`Matroid.loopyOn E` where `E := {x | x ∈ xs}`, and for each `e ∈ xs` consider the rank-`1` oracle
`IndepQuery.singletonOracle e` (`S ⊆ {e}`), which implements `Matroid.uniqueBaseOn {e} E`.
1. Under `loopyOn E`, the unique independent subset is `∅`, so a correct algorithm returns `∅`.
2. Under `uniqueBaseOn {e} E`, `{e}` is an independent subset of `E` of cardinality `1`, whereas
   `∅` has cardinality `0`, so any maximum-cardinality independent subset (and in particular any
   basis) of `E` is `{e} ≠ ∅`.
3. Yet `loopyOracle (.indep S)` and `singletonOracle e (.indep S)` agree on **every** finite set
   `S : Finset α` except the singleton `S = {e}`! Hence if `{e}` is not among the sets queried along
   `loopyOracle`'s execution path (`IndepQuery.queriedSets`), the program evaluates identically on
   both oracles, a contradiction.
4. Injectivity of `e ↦ ({e} : Finset α)` yields `xs.toFinset.card` distinct queried sets along the
   single `loopyOracle` run, bounding `countQueries` from below.

## Main definitions

* `Cslib.Query.IndepQuery.queriedSets`: the `Finset (Finset α)` of candidate sets queried along an
  oracle's execution path.
* `Cslib.Query.IndepQuery.loopyOracle`, `singletonOracle`: computable oracles for `Matroid.loopyOn`
  and `Matroid.uniqueBaseOn {e}`.
* `Cslib.Query.IsMatroidBasisAlg`: specification of a `FreeM (IndepQuery α)` basis-finding
  algorithm.
* `Cslib.Query.IsMaxCardIndepAlg`: weaker specification requiring only an independent output of
  maximum cardinality in `{x | x ∈ xs}` (satisfied by both basis algorithms and unit-weight
  independent-set maximizers).

## Main results

* `IsMaxCardIndepAlg.card_toFinset_le_countQueries`, `IsMaxCardIndepAlg.length_le_countQueries`,
  `IsMaxCardIndepAlg.lowerBound_infinite`: tight `n`-query lower bounds.
* `IsMatroidBasisAlg.card_toFinset_le_countQueries`, `IsMatroidBasisAlg.length_le_countQueries`,
  `IsMatroidBasisAlg.lowerBound_infinite`: specialization to basis algorithms.
-/

public section

open Cslib
open Cslib.Algorithms.Lean.Matroid

namespace Cslib.Query

variable {α : Type}

/-! ## Queried-set trace along an oracle path -/

/-- The finite collection of candidate sets `S : Finset α` queried along the execution path of `p`
determined by `oracle`. -/
@[expose] def IndepQuery.queriedSets [DecidableEq α] {γ : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι) :
    FreeM (IndepQuery α) γ → Finset (Finset α)
  | .pure _ => ∅
  | .liftBind (.indep S) cont =>
    insert S (IndepQuery.queriedSets oracle (cont (oracle (.indep S))))

@[simp] theorem IndepQuery.queriedSets_pure [DecidableEq α] {γ : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι) (a : γ) :
    IndepQuery.queriedSets oracle (pure a : FreeM (IndepQuery α) γ) = ∅ := rfl

@[simp] theorem IndepQuery.queriedSets_liftBind [DecidableEq α] {γ : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι)
    (S : Finset α) (cont : Bool → FreeM (IndepQuery α) γ) :
    IndepQuery.queriedSets oracle (FreeM.lift (.indep S) >>= cont) =
      insert S (IndepQuery.queriedSets oracle (cont (oracle (.indep S)))) := rfl

/-- The number of distinct queried sets never exceeds the total number of queries made. -/
theorem IndepQuery.card_queriedSets_le_countQueries [DecidableEq α] {γ : Type}
    (oracle : {ι : Type} → IndepQuery α ι → ι) (p : FreeM (IndepQuery α) γ) :
    (IndepQuery.queriedSets oracle p).card ≤ p.countQueries oracle := by
  induction p with
  | pure a => simp
  | @lift_bind ρ op cont ih =>
    cases op with
    | indep S =>
      change (insert S (IndepQuery.queriedSets oracle (cont (oracle (.indep S))))).card ≤
        (FreeM.lift (.indep S) >>= cont).countQueries oracle
      rw [FreeM.countQueries_liftBind]
      calc (insert S (IndepQuery.queriedSets oracle (cont (oracle (.indep S))))).card
          ≤ (IndepQuery.queriedSets oracle (cont (oracle (.indep S)))).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (cont (oracle (.indep S))).countQueries oracle + 1 :=
            Nat.add_le_add_right (ih (oracle (.indep S))) 1
        _ = 1 + (cont (oracle (.indep S))).countQueries oracle := Nat.add_comm _ 1

/-- If `oracle₁` and `oracle₂` agree on every set queried along `oracle₁`'s path, then `p`
evaluates to the exact same result under both oracles. -/
theorem IndepQuery.eval_eq_of_agree_on_queriedSets [DecidableEq α] {γ : Type}
    (oracle₁ oracle₂ : {ι : Type} → IndepQuery α ι → ι) (p : FreeM (IndepQuery α) γ)
    (hagree : ∀ S ∈ IndepQuery.queriedSets oracle₁ p, oracle₁ (.indep S) = oracle₂ (.indep S)) :
    p.eval oracle₁ = p.eval oracle₂ := by
  induction p with
  | pure a => rfl
  | @lift_bind ρ op cont ih =>
    cases op with
    | indep S =>
      change (FreeM.lift (.indep S) >>= cont).eval oracle₁ =
        (FreeM.lift (.indep S) >>= cont).eval oracle₂
      have hS : oracle₁ (.indep S) = oracle₂ (.indep S) :=
        hagree S (Finset.mem_insert_self S _)
      rw [FreeM.eval_liftBind, FreeM.eval_liftBind, ← hS]
      refine ih (oracle₁ (.indep S)) fun T hT => ?_
      exact hagree T (Finset.mem_insert_of_mem hT)

/-! ## Adversarial loopy and singleton-base oracles -/

/-- Computable oracle where only `∅` is independent, implementing `Matroid.loopyOn E` for every
ground set `E : Set α`. -/
@[expose] def IndepQuery.loopyOracle [DecidableEq α] : {ι : Type} → IndepQuery α ι → ι :=
  IndepQuery.oracleOf fun S => decide (S = ∅)

/-- Computable oracle where only subsets of `{e}` are independent, implementing
`Matroid.uniqueBaseOn {e} E` whenever `e ∈ E`. -/
@[expose] def IndepQuery.singletonOracle [DecidableEq α] (e : α) :
    {ι : Type} → IndepQuery α ι → ι :=
  IndepQuery.oracleOf fun S => decide (S ⊆ {e})

theorem IndepQuery.implementsMatroid_loopyOracle [DecidableEq α] (E : Set α) :
    IndepQuery.ImplementsMatroid (IndepQuery.loopyOracle (α := α)) (Matroid.loopyOn E) := by
  intro S
  simp [IndepQuery.loopyOracle]

theorem IndepQuery.implementsMatroid_singletonOracle [DecidableEq α] {e : α} {E : Set α}
    (he : e ∈ E) :
    IndepQuery.ImplementsMatroid (IndepQuery.singletonOracle e)
      (Matroid.uniqueBaseOn ({e} : Set α) E) := by
  intro S
  have hsub : ({e} : Set α) ⊆ E := Set.singleton_subset_iff.mpr he
  rw [Matroid.uniqueBaseOn_indep_iff hsub]
  simp [IndepQuery.singletonOracle, ← Finset.coe_singleton]

private theorem loopyOracle_eq_singletonOracle_of_ne [DecidableEq α] {e : α} {S : Finset α}
    (hne : S ≠ {e}) :
    IndepQuery.loopyOracle (.indep S) = IndepQuery.singletonOracle e (.indep S) := by
  simp only [IndepQuery.loopyOracle, IndepQuery.singletonOracle, IndepQuery.oracleOf_indep,
    Finset.subset_singleton_iff]
  by_cases h0 : S = ∅ <;> simp [h0, hne]

/-! ## Correctness specifications and exact `n`-query lower bounds -/

/-- `IsMaxCardIndepAlg alg` asserts that whenever `oracle` implements `M : Matroid α`, `alg xs`
returns an `M`-independent finite set whose cardinality is at least that of every `M`-independent
finite subset of `{x | x ∈ xs}`. -/
structure IsMaxCardIndepAlg [DecidableEq α]
    (alg : List α → FreeM (IndepQuery α) (Finset α)) : Prop where
  /-- The output is independent in `M`. -/
  indep : ∀ (xs : List α) (M : Matroid α) (oracle : {ι : Type} → IndepQuery α ι → ι),
    IndepQuery.ImplementsMatroid oracle M →
    M.Indep (((alg xs).eval oracle : Finset α) : Set α)
  /-- The output has maximum cardinality among all independent subsets of `{x | x ∈ xs}`. -/
  card_max : ∀ (xs : List α) (M : Matroid α) (oracle : {ι : Type} → IndepQuery α ι → ι),
    IndepQuery.ImplementsMatroid oracle M →
    ∀ I : Finset α, M.Indep (I : Set α) → (I : Set α) ⊆ {x | x ∈ xs} →
      I.card ≤ ((alg xs).eval oracle).card

/-- `IsMatroidBasisAlg alg` asserts that whenever `oracle` implements `M : Matroid α`, `alg xs`
computes a basis (`Matroid.IsBasis'`) of `{x | x ∈ xs}`. -/
structure IsMatroidBasisAlg [DecidableEq α]
    (alg : List α → FreeM (IndepQuery α) (Finset α)) : Prop where
  /-- The output is a basis of `{x | x ∈ xs}` in `M`. -/
  isBasis' : ∀ (xs : List α) (M : Matroid α) (oracle : {ι : Type} → IndepQuery α ι → ι),
    IndepQuery.ImplementsMatroid oracle M →
    M.IsBasis' (((alg xs).eval oracle : Finset α) : Set α) {x | x ∈ xs}

/-- Every basis algorithm satisfies `IsMaxCardIndepAlg` (by matroid augmentation). -/
theorem IsMatroidBasisAlg.toIsMaxCardIndepAlg [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMatroidBasisAlg alg) :
    IsMaxCardIndepAlg alg where
  indep xs M oracle horacle := (halg.isBasis' xs M oracle horacle).indep
  card_max xs M oracle horacle I hI hIsub := by
    have hB := halg.isBasis' xs M oracle horacle
    by_contra hlt
    push Not at hlt
    obtain ⟨e, heI, heB, hind⟩ := hB.indep.augment_finset hI hlt
    exact hB.insert_not_indep ⟨hIsub heI, heB⟩ hind

/-- `matroidGreedySelect` is a correct `IsMatroidBasisAlg`. -/
theorem matroidGreedySelect_isMatroidBasisAlg [DecidableEq α] :
    IsMatroidBasisAlg (matroidGreedySelect (α := α)) where
  isBasis' xs _ _ horacle := eval_matroidGreedySelect_isBasis' horacle xs

/-- `matroidGreedyMaxBasis w` is a correct `IsMatroidBasisAlg`. -/
theorem matroidGreedyMaxBasis_isMatroidBasisAlg [DecidableEq α] {β : Type*} [LinearOrder β]
    (w : α → β) :
    IsMatroidBasisAlg (matroidGreedyMaxBasis (α := α) w) where
  isBasis' xs _ _ horacle := eval_matroidGreedyMaxBasis_isBasis' horacle w xs

/-- `matroidGreedyMinBasis w` is a correct `IsMatroidBasisAlg`. -/
theorem matroidGreedyMinBasis_isMatroidBasisAlg [DecidableEq α] {β : Type*} [LinearOrder β]
    (w : α → β) :
    IsMatroidBasisAlg (matroidGreedyMinBasis (α := α) w) where
  isBasis' xs _ _ horacle := eval_matroidGreedyMinBasis_isBasis' horacle w xs

/-- `matroidGreedyMaxIndep` at unit weight `fun _ => (1 : ℕ)` satisfies `IsMaxCardIndepAlg`. -/
theorem matroidGreedyMaxIndep_unit_isMaxCardIndepAlg [DecidableEq α] :
    IsMaxCardIndepAlg (matroidGreedyMaxIndep (α := α) (fun _ => (1 : ℕ))) where
  indep xs _ _ horacle := eval_matroidGreedyMaxIndep_indep horacle _ xs
  card_max xs _ _ horacle I hI hIsub := by
    simpa using sum_le_eval_matroidGreedyMaxIndep horacle (fun _ => (1 : ℕ)) xs hI hIsub

/-- Every element `e ∈ xs` must have its singleton `{e}` queried during the execution of `alg xs`
against `IndepQuery.loopyOracle`. -/
theorem IsMaxCardIndepAlg.singleton_mem_queriedSets [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMaxCardIndepAlg alg)
    {xs : List α} {e : α} (he : e ∈ xs) :
    ({e} : Finset α) ∈ IndepQuery.queriedSets IndepQuery.loopyOracle (alg xs) := by
  set E : Set α := {x | x ∈ xs}
  have heE : e ∈ E := he
  have h0_ind := halg.indep xs (Matroid.loopyOn E) IndepQuery.loopyOracle
    (IndepQuery.implementsMatroid_loopyOracle E)
  have heval0 : (alg xs).eval IndepQuery.loopyOracle = ∅ := by
    simpa using h0_ind
  have he_impl := IndepQuery.implementsMatroid_singletonOracle heE
  have he_ind := halg.indep xs (Matroid.uniqueBaseOn ({e} : Set α) E)
    (IndepQuery.singletonOracle e) he_impl
  have he_card : 1 ≤ ((alg xs).eval (IndepQuery.singletonOracle e)).card := by
    have h1_ind : (Matroid.uniqueBaseOn ({e} : Set α) E).Indep (({e} : Finset α) : Set α) := by
      rw [Matroid.uniqueBaseOn_indep_iff (Set.singleton_subset_iff.mpr heE)]
      simp
    have h1_sub : (({e} : Finset α) : Set α) ⊆ E := by
      simp [heE]
    simpa using halg.card_max xs _ _ he_impl {e} h1_ind h1_sub
  have heval_ne : (alg xs).eval IndepQuery.loopyOracle ≠
      (alg xs).eval (IndepQuery.singletonOracle e) := by
    intro heq
    rw [heval0] at heq
    rw [← heq] at he_card
    simp at he_card
  by_contra hnot_mem
  apply heval_ne
  refine IndepQuery.eval_eq_of_agree_on_queriedSets _ _ (alg xs) fun S hS => ?_
  have hne : S ≠ {e} := fun h => hnot_mem (h ▸ hS)
  exact loopyOracle_eq_singletonOracle_of_ne hne

/-- **Universal per-input independence-oracle lower bound**: for any candidate list `xs : List α`,
running `alg xs` against `IndepQuery.loopyOracle` makes at least `xs.toFinset.card` queries. -/
theorem IsMaxCardIndepAlg.card_toFinset_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMaxCardIndepAlg alg)
    (xs : List α) :
    xs.toFinset.card ≤ (alg xs).countQueries IndepQuery.loopyOracle := by
  have hsub : xs.toFinset.image (fun e : α => ({e} : Finset α)) ⊆
      IndepQuery.queriedSets IndepQuery.loopyOracle (alg xs) := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hS
    exact halg.singleton_mem_queriedSets (List.mem_toFinset.mp he)
  have hinj : Function.Injective (fun e : α => ({e} : Finset α)) := fun _ _ h =>
    Finset.singleton_injective h
  calc xs.toFinset.card
      = (xs.toFinset.image (fun e : α => ({e} : Finset α))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (IndepQuery.queriedSets IndepQuery.loopyOracle (alg xs)).card :=
        Finset.card_le_card hsub
    _ ≤ (alg xs).countQueries IndepQuery.loopyOracle :=
        IndepQuery.card_queriedSets_le_countQueries _ _

/-- On any duplicate-free list `xs`, `alg xs` makes at least `xs.length` independence queries
against `IndepQuery.loopyOracle`. -/
theorem IsMaxCardIndepAlg.length_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMaxCardIndepAlg alg)
    {xs : List α} (hnodup : xs.Nodup) :
    xs.length ≤ (alg xs).countQueries IndepQuery.loopyOracle := by
  rw [← List.toFinset_card_of_nodup hnodup]
  exact halg.card_toFinset_le_countQueries xs

/-- On an infinite ground type `α`, any `IsMaxCardIndepAlg` has query complexity lower bound `n`
(`LowerBound alg List.length id`). -/
theorem IsMaxCardIndepAlg.lowerBound_infinite [DecidableEq α] [Infinite α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMaxCardIndepAlg alg) :
    LowerBound alg List.length id := by
  intro n
  let xs : List α := (List.finRange n).map (Infinite.natEmbedding α ∘ Fin.val)
  have hlen : xs.length = n := by simp [xs]
  have hnodup : xs.Nodup :=
    (List.nodup_finRange n).map
      ((Infinite.natEmbedding α).injective.comp Fin.val_injective)
  refine ⟨xs, hlen.le, IndepQuery.loopyOracle, ?_⟩
  simpa [hlen] using halg.length_le_countQueries hnodup

/-! ### Specializations to `IsMatroidBasisAlg` -/

theorem IsMatroidBasisAlg.card_toFinset_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMatroidBasisAlg alg)
    (xs : List α) :
    xs.toFinset.card ≤ (alg xs).countQueries IndepQuery.loopyOracle :=
  halg.toIsMaxCardIndepAlg.card_toFinset_le_countQueries xs

theorem IsMatroidBasisAlg.length_le_countQueries [DecidableEq α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMatroidBasisAlg alg)
    {xs : List α} (hnodup : xs.Nodup) :
    xs.length ≤ (alg xs).countQueries IndepQuery.loopyOracle :=
  halg.toIsMaxCardIndepAlg.length_le_countQueries hnodup

/-- Any correct `IsMatroidBasisAlg` on an infinite ground type has query lower bound `id`,
matching `matroidGreedySelect_upperBound`, `matroidGreedyMaxBasis_upperBound`, and
`matroidGreedyMinBasis_upperBound` with exact leading constant `1`. -/
theorem IsMatroidBasisAlg.lowerBound_infinite [DecidableEq α] [Infinite α]
    {alg : List α → FreeM (IndepQuery α) (Finset α)} (halg : IsMatroidBasisAlg alg) :
    LowerBound alg List.length id :=
  halg.toIsMaxCardIndepAlg.lowerBound_infinite

end Cslib.Query
