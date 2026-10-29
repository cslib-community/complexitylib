/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.LinearAlgebra.CopyPlacement
public import Complexity.Computability.PolyTime.LinearAlgebra.ExchangeReplacement
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Polynomial-time replacement design builder (Lemma 4.7)

Executable neutral-singleton scope augmentation (`withNeutralScopesList`) and deterministic
polynomial-time Lemma 4.7 replacement-design construction (`buildReplacementDesignData`) from
§4.6 (Lemma 4.7, pp. 33–34) and §§5.3, 5.5 (pp. 37–38) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]. Plain `@[fun_prop]`
`Turing.MultiTapeTM.ComputableInPolyTime` certificates cover the tape-encoded routines
(`withNeutralScopesList`, `scopeIncidencesList`, `normalizeVarSchedules`,
`normalizeScopeSchedules`, `incidenceLabelsList`, `buildReplacementDesignData`,
`ReplacementDesignData` projections, and `ReplacementDesignData.lookupReplacementRow`, with
`encUnary` on `(n_free, D_cap, Q, r, A₀, R)` and binary/list encodings on scopes, schedules,
and `ReplacementDesignData`), while `listScopeFamily`, `withNeutralScopesIndexEquiv`,
`finToScopeIncidence`, `scopeIncidenceEquivFin`, `varAssignOfList`, `factorAssignOfList`,
`BalancedSchedule`, `placeFinOfBalanced`, `constructedReplacementDesign`, and
`ReplacementDesignData.Refines` serve as unencoded semantic specification bridges. All
executable routines are total: scopes ignore variable indices `≥ n_free`; schedule words
truncate/pad with `0` to length `Q` modulo `max r 1` with missing rows and empty in-range
scopes normalized to `List.replicate Q 0`; auxiliary tables cap at `min D_cap (r ^ (2 * Q))`
(`copyCount = 0` when `r = 0` and `Q > 0`); and for data produced by the builder,
`lookupReplacementRow` returns `[]` when `(f, v)` is absent.

## Main definitions

* `Cslib.LinearAlgebra.withNeutralScopesList`, `Cslib.LinearAlgebra.listScopeFamily`,
  `Cslib.LinearAlgebra.withNeutralScopesIndexEquiv`, `Cslib.LinearAlgebra.scopeIncidencesList`,
  `Cslib.LinearAlgebra.scopeIncidenceEquivFin`, `Cslib.LinearAlgebra.BalancedSchedule`.
* `Cslib.LinearAlgebra.ReplacementDesignData`, `Cslib.LinearAlgebra.encReplacementDesignData`,
  `Cslib.LinearAlgebra.buildReplacementDesignData`,
  `Cslib.LinearAlgebra.ReplacementDesignData.lookupReplacementRow`,
  `Cslib.LinearAlgebra.constructedReplacementDesign`,
  `Cslib.LinearAlgebra.ReplacementDesignData.Refines`.

## Main results

* `Cslib.LinearAlgebra.listScopeFamily_withNeutralScopesList`,
  `Cslib.LinearAlgebra.varIncidence_listScopeFamily_withNeutralScopesList`,
  `Cslib.LinearAlgebra.totalIncidence_listScopeFamily_withNeutralScopesList`,
  `Cslib.LinearAlgebra.computableInPolyTime_withNeutralScopesList`.
* `Cslib.LinearAlgebra.balancedSchedule_iff_exec`,
  `Cslib.LinearAlgebra.exists_balancedSchedule_of_scopes`,
  `Cslib.LinearAlgebra.computableInPolyTime_buildReplacementDesignData`,
  `Cslib.LinearAlgebra.computableInPolyTime_lookupReplacementRow`,
  `Cslib.LinearAlgebra.buildReplacementDesignData_spec`,
  `Cslib.LinearAlgebra.exists_replacementDesign_of_buildReplacementDesignData`,
  `Cslib.LinearAlgebra.exists_replacementDesign_withNeutralScopesList`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §4.6 and §§5.3, 5.5.
-/

@[expose] public section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial
open Cslib.BalancedSchedules Cslib.BitString Cslib.LinearAlgebra.CopyPlacement Turing.MultiTapeTM
open scoped BigOperators

/-! ### 1. Executable neutral-singleton scope augmentation (`withNeutralScopesList`) -/

/-- Executable neutral-padding scope augmentation appending `[0], …, [n_free - 1]` to `scopes`
([OpenAI2026ETH], §§5.3, 5.5, pp. 37–38). -/
def withNeutralScopesList (scopes : List (List ℕ)) (n_free : ℕ) : List (List ℕ) :=
  scopes ++ (List.range n_free).map fun v => [v]

@[simp] theorem length_withNeutralScopesList (scopes : List (List ℕ)) (n_free : ℕ) :
    (withNeutralScopesList scopes n_free).length = scopes.length + n_free := by
  simp only [withNeutralScopesList, List.length_append, List.length_map, List.length_range]

/-- Semantic `Fin`-indexed scope family induced by `scopes : List (List ℕ)`. -/
def listScopeFamily (n_free : ℕ) (scopes : List (List ℕ)) (f : Fin scopes.length) :
    Finset (Fin n_free) := univ.filter fun v : Fin n_free => v.1 ∈ scopes[f]

@[simp] theorem mem_listScopeFamily {n_free : ℕ} {scopes : List (List ℕ)} {f : Fin scopes.length}
    {v : Fin n_free} : v ∈ listScopeFamily n_free scopes f ↔ v.1 ∈ scopes[f] := by
  simp only [listScopeFamily, mem_filter, mem_univ, true_and]

/-- Every semantic scope `listScopeFamily n_free scopes f` has size at most `scopes[f].length`. -/
theorem card_listScopeFamily_le (n_free : ℕ) (scopes : List (List ℕ)) (f : Fin scopes.length) :
    #(listScopeFamily n_free scopes f) ≤ scopes[f].length := by
  have hsub : (listScopeFamily n_free scopes f).map ⟨Fin.val, Fin.val_injective⟩ ⊆
      scopes[f].toFinset := fun x hx => by
    rcases mem_map.mp hx with ⟨v, hv, rfl⟩; exact List.mem_toFinset.mpr (mem_listScopeFamily.mp hv)
  exact (card_map ⟨Fin.val, Fin.val_injective⟩).symm.trans_le
    ((card_le_card hsub).trans (List.toFinset_card_le _))

/-- Factor-index equivalence `Fin scopes.length ⊕ Fin n_free ≃ Fin augScopes.length`. -/
def withNeutralScopesIndexEquiv (scopes : List (List ℕ)) (n_free : ℕ) :
    Fin scopes.length ⊕ Fin n_free ≃ Fin (withNeutralScopesList scopes n_free).length :=
  finSumFinEquiv.trans (finCongr (length_withNeutralScopesList scopes n_free).symm)
@[simp] theorem val_withNeutralScopesIndexEquiv_inl (scopes : List (List ℕ)) (n_free : ℕ)
    (f : Fin scopes.length) : (withNeutralScopesIndexEquiv scopes n_free (Sum.inl f)).1 = f.1 := by
  simp only [withNeutralScopesIndexEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left,
    finCongr_apply, Fin.val_cast, Fin.val_castAdd]
@[simp] theorem val_withNeutralScopesIndexEquiv_inr (scopes : List (List ℕ)) (n_free : ℕ)
    (v : Fin n_free) :
    (withNeutralScopesIndexEquiv scopes n_free (Sum.inr v)).1 = scopes.length + v.1 := by
  simp only [withNeutralScopesIndexEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right,
    finCongr_apply, Fin.val_cast, Fin.val_natAdd]

/-- Exact agreement between `withNeutralScopesList` and `Cslib.BitString.withNeutralScope`. -/
@[simp] theorem listScopeFamily_withNeutralScopesList (scopes : List (List ℕ)) (n_free : ℕ)
    (s : Fin scopes.length ⊕ Fin n_free) :
    listScopeFamily n_free (withNeutralScopesList scopes n_free)
        (withNeutralScopesIndexEquiv scopes n_free s) =
      withNeutralScope (listScopeFamily n_free scopes) s := by
  cases s with
  | inl f =>
    ext u; rw [mem_listScopeFamily, Fin.getElem_fin, ← List.getD_eq_getElem _ [],
      val_withNeutralScopesIndexEquiv_inl, withNeutralScopesList,
      List.getD_append scopes _ [] f.1 f.2, List.getD_eq_getElem _ [] f.2]
    simp only [withNeutralScope, mem_listScopeFamily, Fin.getElem_fin]
  | inr v =>
    ext u; rw [mem_listScopeFamily, Fin.getElem_fin, ← List.getD_eq_getElem _ [],
      val_withNeutralScopesIndexEquiv_inr, withNeutralScopesList,
      List.getD_append_right scopes _ [] (scopes.length + v.1) (by omega),
      Nat.add_sub_cancel_left, List.getD_map_range _ [] v.2]
    simp only [List.mem_singleton, withNeutralScope, mem_singleton, Fin.ext_iff]

/-- Variable incidence increases by `1` at every free variable under `withNeutralScopesList`. -/
theorem varIncidence_listScopeFamily_withNeutralScopesList (scopes : List (List ℕ)) (n_free : ℕ)
    (v : Fin n_free) :
    varIncidence univ (listScopeFamily n_free (withNeutralScopesList scopes n_free)) v =
      varIncidence univ (listScopeFamily n_free scopes) v + 1 := by
  let eqv := withNeutralScopesIndexEquiv scopes n_free
  have hbij : varIncidence univ (listScopeFamily n_free (withNeutralScopesList scopes n_free)) v =
      varIncidence (withNeutralFactors (univ : Finset (Fin scopes.length)))
        (withNeutralScope (listScopeFamily n_free scopes)) v := by
    rw [withNeutralFactors_univ]
    refine Finset.card_bij (fun f _ => eqv.symm f) (fun f hf => ?_)
      (fun _ _ _ _ h => eqv.symm.injective h) (fun s hs => ⟨eqv s, ?_, eqv.symm_apply_apply s⟩)
    · simp only [mem_filter, mem_univ, true_and] at hf ⊢
      simpa only [eqv, ← listScopeFamily_withNeutralScopesList, Equiv.apply_symm_apply] using hf
    · simp only [mem_filter, mem_univ, true_and] at hs ⊢
      rwa [listScopeFamily_withNeutralScopesList]
  exact hbij.trans (varIncidence_withNeutralFactors univ (listScopeFamily n_free scopes) v)

/-- Total incidence increases by `n_free` under `withNeutralScopesList`. -/
theorem totalIncidence_listScopeFamily_withNeutralScopesList (scopes : List (List ℕ)) (n_free : ℕ) :
    totalIncidence univ (listScopeFamily n_free (withNeutralScopesList scopes n_free)) =
      totalIncidence univ (listScopeFamily n_free scopes) + n_free := by
  unfold totalIncidence; rw [← Equiv.sum_comp (withNeutralScopesIndexEquiv scopes n_free)]
  simp only [listScopeFamily_withNeutralScopesList]
  simpa only [totalIncidence, withNeutralFactors_univ, Fintype.card_fin] using
    totalIncidence_withNeutralFactors (univ : Finset (Fin scopes.length))
      (listScopeFamily n_free scopes)

/-! ### 2. Canonical scope incidences and Lemma 4.5 schedule balance -/

/-- Sorted duplicate-free list of variable indices `< n_free` belonging to `s : List ℕ`. -/
def canonicalScopeVars (n_free : ℕ) (s : List ℕ) : List ℕ :=
  (List.range n_free).filter fun v => decide (v ∈ s)

@[simp] theorem mem_canonicalScopeVars {n_free v : ℕ} {s : List ℕ} :
    v ∈ canonicalScopeVars n_free s ↔ v < n_free ∧ v ∈ s := by
  simp only [canonicalScopeVars, List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem nodup_canonicalScopeVars (n_free : ℕ) (s : List ℕ) : (canonicalScopeVars n_free s).Nodup :=
  (List.pairwise_lt_range.filter _).imp ne_of_lt

theorem canonicalScopeVars_isEmpty_iff (n_free : ℕ) (scopes : List (List ℕ))
    (f : Fin scopes.length) :
    (canonicalScopeVars n_free (scopes.getD f.1 [])).isEmpty = true ↔
      listScopeFamily n_free scopes f = ∅ := by
  rw [List.getD_eq_getElem _ _ f.2, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
    Finset.eq_empty_iff_forall_notMem]
  simp only [mem_canonicalScopeVars, mem_listScopeFamily]
  exact ⟨fun h v hv => h v.1 ⟨v.2, hv⟩, fun h v ⟨hv_lt, hv_mem⟩ => h ⟨v, hv_lt⟩ hv_mem⟩

/-- Canonical ordered list of factor–variable incidences `(f, v)`. -/
def scopeIncidencesList (n_free : ℕ) (scopes : List (List ℕ)) : List (ℕ × ℕ) :=
  (List.range scopes.length).flatMap fun f =>
    (canonicalScopeVars n_free (scopes.getD f [])).map fun v => (f, v)

@[simp] theorem mem_scopeIncidencesList {n_free : ℕ} {scopes : List (List ℕ)} {p : ℕ × ℕ} :
    p ∈ scopeIncidencesList n_free scopes ↔
      p.1 < scopes.length ∧ p.2 < n_free ∧ p.2 ∈ scopes.getD p.1 [] := by
  rcases p with ⟨f, v⟩
  simp only [scopeIncidencesList, List.mem_flatMap, List.mem_range, List.mem_map,
    mem_canonicalScopeVars, Prod.mk.injEq]
  exact ⟨fun ⟨_, hf, _, ⟨hv_lt, hv_mem⟩, rfl, rfl⟩ => ⟨hf, hv_lt, hv_mem⟩,
    fun ⟨hf, hv_lt, hv_mem⟩ => ⟨f, hf, v, ⟨hv_lt, hv_mem⟩, rfl, rfl⟩⟩

theorem nodup_scopeIncidencesList (n_free : ℕ) (scopes : List (List ℕ)) :
    (scopeIncidencesList n_free scopes).Nodup := by
  unfold scopeIncidencesList; rw [List.nodup_flatMap]
  refine ⟨fun f _ => (nodup_canonicalScopeVars n_free _).map fun _ _ h => (Prod.mk.inj h).2, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun f₁ _ f₂ _ hne => ?_
  rw [Function.onFun, List.disjoint_left]; intro p hp₁ hp₂
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp₁; obtain ⟨_, _, heq⟩ := List.mem_map.mp hp₂
  exact hne (Prod.mk.inj heq).1.symm

/-- Map an index in `Fin (scopeIncidencesList n_free scopes).length` to `ScopeIncidence`. -/
def finToScopeIncidence (n_free : ℕ) (scopes : List (List ℕ))
    (i : Fin (scopeIncidencesList n_free scopes).length) :
    ScopeIncidence (listScopeFamily n_free scopes) :=
  have hm := mem_scopeIncidencesList.mp (List.getElem_mem i.2)
  ⟨⟨(scopeIncidencesList n_free scopes)[i.1].1, hm.1⟩,
   ⟨⟨(scopeIncidencesList n_free scopes)[i.1].2, hm.2.1⟩, by
    rw [mem_listScopeFamily]
    simpa only [Fin.getElem_fin, List.getD_eq_getElem _ _ hm.1] using hm.2.2⟩⟩

theorem bijective_finToScopeIncidence (n_free : ℕ) (scopes : List (List ℕ)) :
    Function.Bijective (finToScopeIncidence n_free scopes) := by
  refine ⟨fun i j hij => Fin.ext (((nodup_scopeIncidencesList n_free scopes).getElem_inj_iff
      (hi := i.2) (hj := j.2)).mp (Prod.ext (congrArg (·.1.1) hij) (congrArg (·.2.1.1) hij))),
    fun ⟨f, ⟨v, hv⟩⟩ => ?_⟩
  have hmem : (f.1, v.1) ∈ scopeIncidencesList n_free scopes := by
    rw [mem_scopeIncidencesList, List.getD_eq_getElem _ _ f.2]
    exact ⟨f.2, v.2, mem_listScopeFamily.mp hv⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hf_eq : (finToScopeIncidence n_free scopes ⟨i, hi⟩).1 = f := Fin.ext (congrArg Prod.fst hget)
  have hv_eq : (finToScopeIncidence n_free scopes ⟨i, hi⟩).2.1 = v :=
    Fin.ext (congrArg Prod.snd hget)
  refine ⟨⟨i, hi⟩, ?_⟩
  rcases hx : finToScopeIncidence n_free scopes ⟨i, hi⟩ with ⟨f', ⟨v', hv'⟩⟩
  rw [hx] at hf_eq hv_eq; dsimp only at hf_eq hv_eq; subst hf_eq; subst hv_eq; rfl

/-- Canonical bijection `ScopeIncidence (listScopeFamily n_free scopes) ≃ Fin M`. -/
noncomputable def scopeIncidenceEquivFin (n_free : ℕ) (scopes : List (List ℕ)) :
    ScopeIncidence (listScopeFamily n_free scopes) ≃
      Fin (scopeIncidencesList n_free scopes).length :=
  (Equiv.ofBijective _ (bijective_finToScopeIncidence n_free scopes)).symm
@[simp] theorem finToScopeIncidence_scopeIncidenceEquivFin (n_free : ℕ) (scopes : List (List ℕ))
    (e : ScopeIncidence (listScopeFamily n_free scopes)) :
    finToScopeIncidence n_free scopes (scopeIncidenceEquivFin n_free scopes e) = e :=
  (Equiv.ofBijective _ (bijective_finToScopeIncidence n_free scopes)).right_inv e
@[simp] theorem scopeIncidenceEquivFin_finToScopeIncidence (n_free : ℕ) (scopes : List (List ℕ))
    (i : Fin (scopeIncidencesList n_free scopes).length) :
    scopeIncidenceEquivFin n_free scopes (finToScopeIncidence n_free scopes i) = i :=
  (Equiv.ofBijective _ (bijective_finToScopeIncidence n_free scopes)).left_inv i
@[simp] theorem getElem_scopeIncidencesList_equiv (n_free : ℕ) (scopes : List (List ℕ))
    (e : ScopeIncidence (listScopeFamily n_free scopes)) :
    (scopeIncidencesList n_free scopes)[(scopeIncidenceEquivFin n_free scopes e).1] =
      ((scopeFactorOf (listScopeFamily n_free scopes) e).1,
       (scopeVarOf (listScopeFamily n_free scopes) e).1) := by
  have h := finToScopeIncidence_scopeIncidenceEquivFin n_free scopes e
  exact Prod.ext (congrArg (·.1.1) h) (congrArg (·.2.1.1) h)
theorem val_scopeIncidenceEquivFin_eq_idxOf (n_free : ℕ) (scopes : List (List ℕ))
    (e : ScopeIncidence (listScopeFamily n_free scopes)) :
    (scopeIncidenceEquivFin n_free scopes e).1 = (scopeIncidencesList n_free scopes).idxOf
      ((scopeFactorOf (listScopeFamily n_free scopes) e).1,
       (scopeVarOf (listScopeFamily n_free scopes) e).1) := by
  rw [← getElem_scopeIncidencesList_equiv n_free scopes e]
  exact ((nodup_scopeIncidencesList n_free scopes).idxOf_getElem _ _).symm
theorem length_scopeIncidencesList (n_free : ℕ) (scopes : List (List ℕ)) :
    (scopeIncidencesList n_free scopes).length =
      ∑ f : Fin scopes.length, #(listScopeFamily n_free scopes f) := by
  rw [← card_scopeIncidence, Fintype.card_congr (scopeIncidenceEquivFin n_free scopes),
    Fintype.card_fin]

/-- Normalize a schedule word `w : List ℕ` to length `Q` with entries `< max r 1`. -/
def normalizeScheduleWord (Q r : ℕ) (w : List ℕ) : List ℕ :=
  (List.range Q).map fun t => w.getD t 0 % max r 1
@[simp] theorem length_normalizeScheduleWord (Q r : ℕ) (w : List ℕ) :
    (normalizeScheduleWord Q r w).length = Q := by
  simp only [normalizeScheduleWord, List.length_map, List.length_range]

/-- Normalize `schedVar` to `n_free` length-`Q` words over `{0, …, max r 1 - 1}`. -/
def normalizeVarSchedules (n_free Q r : ℕ) (schedVar : List (List ℕ)) : List (List ℕ) :=
  (List.range n_free).map fun v => normalizeScheduleWord Q r (schedVar.getD v [])
@[simp] theorem length_normalizeVarSchedules (n_free Q r : ℕ) (schedVar : List (List ℕ)) :
    (normalizeVarSchedules n_free Q r schedVar).length = n_free := by
  simp only [normalizeVarSchedules, List.length_map, List.length_range]

/-- Normalize `schedScope` to `scopes.length` length-`Q` words, mapping empty in-range scopes to
`List.replicate Q 0` ([OpenAI2026ETH], §4.1 & Lemma 4.5, pp. 27, 30–31). -/
def normalizeScopeSchedules (n_free Q r : ℕ) (scopes schedScope : List (List ℕ)) : List (List ℕ) :=
  (List.range scopes.length).map fun f =>
    if (canonicalScopeVars n_free (scopes.getD f [])).isEmpty then List.replicate Q 0
    else normalizeScheduleWord Q r (schedScope.getD f [])
@[simp] theorem length_normalizeScopeSchedules (n_free Q r : ℕ)
    (scopes schedScope : List (List ℕ)) :
    (normalizeScopeSchedules n_free Q r scopes schedScope).length = scopes.length := by
  simp only [normalizeScopeSchedules, List.length_map, List.length_range]

/-- Typed variable group schedule `Fin n_free → Fin Q → Fin r` extracted from `schedVar`. -/
def varAssignOfList {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ) (schedVar : List (List ℕ))
    (v : Fin n_free) (t : Fin Q) : Fin r :=
  ⟨((normalizeVarSchedules n_free Q r schedVar).getD v.1 []).getD t.1 0 % r, Nat.mod_lt _ hr⟩
/-- Typed factor group schedule `Fin scopes.length → Fin Q → Fin r` extracted from `schedScope`. -/
def factorAssignOfList {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ) (scopes schedScope : List (List ℕ))
    (f : Fin scopes.length) (t : Fin Q) : Fin r :=
  ⟨((normalizeScopeSchedules n_free Q r scopes schedScope).getD f.1 []).getD t.1 0 % r,
   Nat.mod_lt _ hr⟩
@[simp] theorem val_varAssignOfList {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ) (schedVar : List (List ℕ))
    (v : Fin n_free) (t : Fin Q) :
    (varAssignOfList hr n_free Q schedVar v t).1 =
      ((normalizeVarSchedules n_free Q r schedVar).getD v.1 []).getD t.1 0 := by
  simp only [varAssignOfList, normalizeVarSchedules, List.getD_map_range _ [] v.2,
    normalizeScheduleWord, List.getD_map_range _ 0 t.2, Nat.max_eq_left hr,
    Nat.mod_eq_of_lt (Nat.mod_lt _ hr)]
@[simp] theorem val_factorAssignOfList {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedScope : List (List ℕ)) (f : Fin scopes.length) (t : Fin Q) :
    (factorAssignOfList hr n_free Q scopes schedScope f t).1 =
      ((normalizeScopeSchedules n_free Q r scopes schedScope).getD f.1 []).getD t.1 0 := by
  simp only [factorAssignOfList, normalizeScopeSchedules, List.getD_map_range _ [] f.2]
  split_ifs
  · have ht : t.1 < (List.replicate Q 0).length := by simp only [List.length_replicate]; exact t.2
    rw [List.getD_eq_getElem _ _ ht, List.getElem_replicate, Nat.zero_mod]
  · simp only [normalizeScheduleWord, List.getD_map_range _ 0 t.2, Nat.max_eq_left hr,
      Nat.mod_eq_of_lt (Nat.mod_lt _ hr)]
theorem factorAssignOfList_of_empty {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedScope : List (List ℕ)) {f : Fin scopes.length}
    (hf : listScopeFamily n_free scopes f = ∅) (t : Fin Q) :
    (factorAssignOfList hr n_free Q scopes schedScope f t).1 = 0 := by
  rw [val_factorAssignOfList, normalizeScopeSchedules, List.getD_map_range _ [] f.2,
    ite_eq_left ((canonicalScopeVars_isEmpty_iff n_free scopes f).mpr hf)]
  have ht : t.1 < (List.replicate Q 0).length := by simp only [List.length_replicate]; exact t.2
  rw [List.getD_eq_getElem _ _ ht, List.getElem_replicate]

/-- Executable list of packed auxiliary incidence labels `u_{f,v} < r ^ (2 * Q)`. -/
def incidenceLabelsList (n_free Q r : ℕ) (scopes schedVar schedScope : List (List ℕ)) : List ℕ :=
  let varScheds := normalizeVarSchedules n_free Q r schedVar
  let facScheds := normalizeScopeSchedules n_free Q r scopes schedScope
  (scopeIncidencesList n_free scopes).map fun fv =>
    encodeAuxDigits r (varScheds.getD fv.2 [], facScheds.getD fv.1 [])
@[simp] theorem length_incidenceLabelsList (n_free Q r : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) :
    (incidenceLabelsList n_free Q r scopes schedVar schedScope).length =
      (scopeIncidencesList n_free scopes).length := by
  simp only [incidenceLabelsList, List.length_map]

/-- `incidenceLabelsList` equals `List.ofFn` of `encodeAuxLabel ∘ u ∘ finToScopeIncidence`. -/
theorem incidenceLabelsList_eq_ofFn {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) :
    incidenceLabelsList n_free Q r scopes schedVar schedScope =
      List.ofFn fun i : Fin (scopeIncidencesList n_free scopes).length =>
        encodeAuxLabel (incidenceLabel (scopeVarOf (listScopeFamily n_free scopes))
          (scopeFactorOf (listScopeFamily n_free scopes)) (varAssignOfList hr n_free Q schedVar)
          (factorAssignOfList hr n_free Q scopes schedScope)
          (finToScopeIncidence n_free scopes i)) := by
  refine List.ext_getElem (by simp only [length_incidenceLabelsList, List.length_ofFn])
    fun i hi _ => ?_
  rw [length_incidenceLabelsList] at hi
  have hp := mem_scopeIncidencesList.mp (List.getElem_mem hi)
  simp only [incidenceLabelsList, List.getElem_map, List.getElem_ofFn, encodeAuxLabel,
    auxLabelToDigits, incidenceLabel, scopeVarOf, scopeFactorOf, finToScopeIncidence]
  congr 1; ext : 1
  · refine List.ext_getElem ?_ fun t ht₁ _ => ?_
    · simp only [normalizeVarSchedules, List.getD_map_range _ [] hp.2.1,
        length_normalizeScheduleWord, List.length_ofFn]
    · simp only [List.getElem_ofFn, val_varAssignOfList]; exact (List.getD_eq_getElem _ 0 ht₁).symm
  · refine List.ext_getElem ?_ fun t ht₁ _ => ?_
    · simp only [normalizeScopeSchedules, List.getD_map_range _ [] hp.1]
      split_ifs <;>
        simp only [List.length_replicate, length_normalizeScheduleWord, List.length_ofFn]
    · simp only [List.getElem_ofFn, val_factorAssignOfList]
      exact (List.getD_eq_getElem _ 0 ht₁).symm

/-- Lemma 4.5 balance predicate on executable schedule lists `(schedVar, schedScope)`
([OpenAI2026ETH], Lemma 4.5 & Lemma 4.7, pp. 30–31, 33–34). -/
def BalancedSchedule {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) : Prop :=
  let scope := listScopeFamily n_free scopes
  let a := varAssignOfList hr n_free Q schedVar
  let d := factorAssignOfList hr n_free Q scopes schedScope
  (∀ u : AuxLabel Q r,
    occupancy (incidenceLabel (scopeVarOf scope) (scopeFactorOf scope) a d) u *
      r ^ (2 * Q) ≤ 2 * Fintype.card (ScopeIncidence scope)) ∧
  (∀ (t : Fin Q) (g : Fin r), occupancy (fun v => a v t) g * r ≤ 2 * n_free)

private theorem count_incidenceLabelsList_eq_occupancy {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) (u : AuxLabel Q r) :
    (incidenceLabelsList n_free Q r scopes schedVar schedScope).count (encodeAuxLabel u) =
      occupancy (incidenceLabel (scopeVarOf (listScopeFamily n_free scopes))
        (scopeFactorOf (listScopeFamily n_free scopes)) (varAssignOfList hr n_free Q schedVar)
        (factorAssignOfList hr n_free Q scopes schedScope)) u := by
  have hD : 0 < r ^ (2 * Q) := pow_pos hr (2 * Q)
  have hinj : Function.Injective (encodeAuxLabel (Q := Q) (r := r)) := fun x y h => by
    have := congrArg (decodeAuxLabel hD) h
    rwa [decodeAuxLabel_encodeAuxLabel, decodeAuxLabel_encodeAuxLabel] at this
  rw [incidenceLabelsList_eq_ofFn hr, List.count_eq_countP, List.countP_ofFn]
  unfold occupancy; rw [Fintype.card_subtype, Finset.card_filter,
    ← Equiv.sum_comp (scopeIncidenceEquivFin n_free scopes).symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  let lbl := incidenceLabel (scopeVarOf (listScopeFamily n_free scopes))
    (scopeFactorOf (listScopeFamily n_free scopes)) (varAssignOfList hr n_free Q schedVar)
    (factorAssignOfList hr n_free Q scopes schedScope)
  have hiff : ((encodeAuxLabel (lbl (finToScopeIncidence n_free scopes i)) == encodeAuxLabel u) =
      true) ↔ lbl ((scopeIncidenceEquivFin n_free scopes).symm i) = u := by
    rw [beq_iff_eq, hinj.eq_iff]; rfl
  by_cases hm : lbl ((scopeIncidenceEquivFin n_free scopes).symm i) = u
  · rw [ite_eq_left (hiff.mpr hm), ite_eq_left hm]
  · rw [ite_eq_right (mt hiff.mp hm), ite_eq_right hm]

private theorem card_varGroup_eq_occupancy {n Q r : ℕ} (a : Fin n → Fin Q → Fin r)
    (t : Fin Q) (g : Fin r) : #(varGroup a t g) = occupancy (fun v => a v t) g := by
  unfold varGroup occupancy; rw [Fintype.card_subtype]

private theorem length_varGroupList_eq_occupancy {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (schedVar : List (List ℕ)) (t : Fin Q) (g : Fin r) :
    (varGroupList (normalizeVarSchedules n_free Q r schedVar) t.1 g.1).length =
      occupancy (fun v => varAssignOfList hr n_free Q schedVar v t) g := by
  unfold varGroupList occupancy
  rw [length_normalizeVarSchedules, ← List.countP_eq_length_filter,
    List.countP_range_eq_card_filter, Fintype.card_subtype]
  congr 1; ext v
  simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, Fin.ext_iff, val_varAssignOfList]

/-- Pure executable list characterization of `BalancedSchedule`, enabling `decide` verification. -/
theorem balancedSchedule_iff_exec {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) :
    BalancedSchedule hr n_free Q scopes schedVar schedScope ↔
      (∀ idx < r ^ (2 * Q),
        (incidenceLabelsList n_free Q r scopes schedVar schedScope).count idx * r ^ (2 * Q) ≤
          2 * (scopeIncidencesList n_free scopes).length) ∧
      (∀ t < Q, ∀ g < r,
        (varGroupList (normalizeVarSchedules n_free Q r schedVar) t g).length * r ≤
          2 * n_free) := by
  have hD : 0 < r ^ (2 * Q) := pow_pos hr (2 * Q)
  have hcard : Fintype.card (ScopeIncidence (listScopeFamily n_free scopes)) =
      (scopeIncidencesList n_free scopes).length := by
    rw [Fintype.card_congr (scopeIncidenceEquivFin n_free scopes), Fintype.card_fin]
  refine ⟨fun ⟨hinc, hgrp⟩ => ⟨fun idx hidx => ?_, fun t ht g hg => ?_⟩,
    fun ⟨hinc, hgrp⟩ => ⟨fun u => ?_, fun t g => ?_⟩⟩
  · have hu := hinc (decodeAuxLabel hD idx)
    rwa [← count_incidenceLabelsList_eq_occupancy, encodeAuxLabel_decodeAuxLabel hD hidx,
      hcard] at hu
  · rw [length_varGroupList_eq_occupancy hr n_free Q schedVar ⟨t, ht⟩ ⟨g, hg⟩]; exact hgrp _ _
  · rw [← count_incidenceLabelsList_eq_occupancy, hcard]; exact hinc _ (encodeAuxLabel_lt u)
  · rw [← length_varGroupList_eq_occupancy hr n_free Q schedVar t g]; exact hgrp t.1 t.2 g.1 g.2

/-- **Lemma 4.5 schedule existence on executable scope lists**: under Lemma 4.7's size hypotheses,
there exist executable schedule lists `(schedVar, schedScope)` satisfying `BalancedSchedule`. -/
theorem exists_balancedSchedule_of_scopes {n_free Q r b w : ℕ} (scopes : List (List ℕ))
    (hn : 1 ≤ n_free) (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hbw : 0 < b + w)
    (hb : ∀ v : Fin n_free, #{f : Fin scopes.length | v ∈ listScopeFamily n_free scopes f} ≤ b)
    (hw : ∀ f : Fin scopes.length, #(listScopeFamily n_free scopes f) ≤ w)
    (hincidenceSize : 2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤
      ∑ f : Fin scopes.length, #(listScopeFamily n_free scopes f))
    (hgroupSize : 2 * Q * r ^ 2 ≤ n_free) :
    ∃ schedVar schedScope : List (List ℕ),
      schedVar.length = n_free ∧ schedScope.length = scopes.length ∧
      BalancedSchedule hr n_free Q scopes schedVar schedScope := by
  let scope := listScopeFamily n_free scopes
  have : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have : Nonempty (Fin n_free) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hinc_c :
      2 * (b + w) * Fintype.card (AuxLabel Q r) ^ 2 ≤ Fintype.card (ScopeIncidence scope) := by
    simpa only [card_scopeIncidence, card_auxLabel] using hincidenceSize
  have hgrp_c : 2 * Fintype.card (Fin Q) * Fintype.card (Fin r) ^ 2 ≤ Fintype.card (Fin n_free) :=
    by simpa only [Fintype.card_fin] using hgroupSize
  obtain ⟨a, d, hempty, hocc_inc, hocc_grp⟩ :=
    exists_balanced_schedules_of_scopes scope hb hw hbw hinc_c hgrp_c ⟨0, hr⟩
  let schedVar := List.ofFn fun v : Fin n_free => List.ofFn fun t : Fin Q => (a v t).1
  let schedScope := List.ofFn fun f : Fin scopes.length => List.ofFn fun t : Fin Q => (d f t).1
  have ha_eq : varAssignOfList hr n_free Q schedVar = a := by
    funext v t; apply Fin.ext
    simp only [val_varAssignOfList, normalizeVarSchedules, List.getD_map_range _ [] v.2, schedVar,
      List.getD_ofFn, normalizeScheduleWord, List.getD_map_range _ 0 t.2, Nat.max_eq_left hr,
      Nat.mod_eq_of_lt (a v t).2]
  have hd_eq : factorAssignOfList hr n_free Q scopes schedScope = d := by
    funext f t; apply Fin.ext; by_cases hemp : scope f = ∅
    · rw [factorAssignOfList_of_empty hr n_free Q scopes schedScope hemp t, hempty f hemp]
    · simp only [val_factorAssignOfList, normalizeScopeSchedules, List.getD_map_range _ [] f.2]
      have hfalse : (canonicalScopeVars n_free (scopes.getD f.1 [])).isEmpty = false :=
        Bool.eq_false_iff.mpr fun h => hemp ((canonicalScopeVars_isEmpty_iff n_free scopes f).mp h)
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, schedScope, List.getD_ofFn,
        normalizeScheduleWord, List.getD_map_range _ 0 t.2, Nat.max_eq_left hr,
        Nat.mod_eq_of_lt (d f t).2]
  refine ⟨schedVar, schedScope, List.length_ofFn, List.length_ofFn, fun u => ?_, fun t g => ?_⟩
  · have hu := hocc_inc u; rwa [card_auxLabel, ← ha_eq, ← hd_eq] at hu
  · have hg := hocc_grp t g; simpa only [Fintype.card_fin, ← ha_eq] using hg

/-! ### 3. Bundled Lemma 4.7 design data and executable constructor -/

/-- Bundled executable Lemma 4.7 replacement-design arrays ([OpenAI2026ETH], Lemma 4.7). -/
structure ReplacementDesignData where
  /-- Step-and-group variable partitions `V_0, …, V_{r - 1}` for `t < Q`. -/
  varGroups : List (List (List ℕ))
  /-- Normalized factor group schedules `σ_f ∈ {0, …, r - 1}^Q` for `f < scopes.length`. -/
  factorGroups : List (List ℕ)
  /-- Canonical ordered list of factor–variable incidences `(f, v)`. -/
  incidences : List (ℕ × ℕ)
  /-- Copy count `h = 2 * incidences.length / r ^ (2 * Q)`. -/
  copyCount : ℕ
  /-- Injective incidence copy placements `(c_e, u_e)` for `e < incidences.length`. -/
  placements : List (ℕ × ℕ)
  /-- Pulled-back `(copyCount * c_B) × n_free` integer measurement matrix `Ĉ = C̃ ι`. -/
  measurementMatrix : List (List ℤ)
  /-- Step-and-group restricted integer measurement matrices `C_{t,g} = Ĉ|_{S_{t,g}}`. -/
  groupMeasurementMatrices : List (List (List (List ℤ)))
  /-- Cleared common denominator `d_den = (R - 1)! * Q!` as an integer. -/
  denom : ℤ
  /-- Per-incidence `n_free × R` cleared replacement-row coefficient tables `d_den · P⃗_e(T)`. -/
  replacementRows : List (List (List ℤ))
  deriving DecidableEq, Repr

/-- Underlying nested product representation of `ReplacementDesignData` for tape encoding. -/
abbrev ReplacementDesignTuple :=
  (List (List (List ℕ)) × List (List ℕ) × List (ℕ × ℕ)) × (ℕ × List (ℕ × ℕ) × List (List ℤ)) ×
    (List (List (List (List ℤ))) × ℤ × List (List (List ℤ)))

/-- Canonical equivalence between `ReplacementDesignData` and `ReplacementDesignTuple`. -/
def ReplacementDesignData.equivTuple : ReplacementDesignData ≃ ReplacementDesignTuple where
  toFun d := ((d.varGroups, d.factorGroups, d.incidences),
    (d.copyCount, d.placements, d.measurementMatrix),
    (d.groupMeasurementMatrices, d.denom, d.replacementRows))
  invFun t :=
    { varGroups := t.1.1, factorGroups := t.1.2.1, incidences := t.1.2.2,
      copyCount := t.2.1.1, placements := t.2.1.2.1, measurementMatrix := t.2.1.2.2,
      groupMeasurementMatrices := t.2.2.1, denom := t.2.2.2.1, replacementRows := t.2.2.2.2 }
  left_inv d := by cases d; rfl
  right_inv _ := rfl

/-- Standard multi-tape Turing machine encoding of `ReplacementDesignTuple`. -/
def encReplacementDesignTuple : ReplacementDesignTuple ↪ List Bool :=
  encPair (encPair (encList (encList (encList encNat)))
      (encPair (encList (encList encNat)) (encList (encPair encNat encNat))))
    (encPair (encPair encNat (encPair (encList (encPair encNat encNat))
        (encList (encList encIntBin))))
      (encPair (encList (encList (encList (encList encIntBin))))
        (encPair encIntBin (encList (encList (encList encIntBin))))))

/-- Standard multi-tape Turing machine encoding of `ReplacementDesignData`. -/
def encReplacementDesignData : ReplacementDesignData ↪ List Bool :=
  ReplacementDesignData.equivTuple.toEmbedding.trans encReplacementDesignTuple

/-- Executable Lemma 4.7 replacement-design constructor assembling `ExchangeReplacement` and
`CopyPlacement` over `(schedVar, schedScope)` ([OpenAI2026ETH], §4.6, Lemma 4.7, pp. 33–34). -/
def buildReplacementDesignData (n_free D_cap Q r A₀ R : ℕ)
    (scopes schedVar schedScope : List (List ℕ)) : ReplacementDesignData :=
  let varScheds := normalizeVarSchedules n_free Q r schedVar
  let facScheds := normalizeScopeSchedules n_free Q r scopes schedScope
  let incs := scopeIncidencesList n_free scopes
  let incVars := incs.map Prod.snd
  let labels := incidenceLabelsList n_free Q r scopes schedVar schedScope
  let h := (2 * incs.length) / (r ^ (2 * Q))
  let pls := (fiberRanks labels).zip labels
  let measMat := pullbackMeasurementMatrix n_free h pls incVars
    (auxMeasurementRowsBounded D_cap Q r A₀ R)
  let vGroups := (List.range Q).map fun t => (List.range r).map fun g => varGroupList varScheds t g
  let grpMeas := vGroups.map fun gs => gs.map fun Vg => restrictGroupColumns Vg measMat
  let replRows := (List.range incs.length).map fun e =>
    pullbackReplacementRow n_free R pls incVars e (auxReplacementTableBounded D_cap Q r A₀ R)
  { varGroups := vGroups, factorGroups := facScheds, incidences := incs, copyCount := h,
    placements := pls, measurementMatrix := measMat, groupMeasurementMatrices := grpMeas,
    denom := (commonDenom Q R : ℤ), replacementRows := replRows }

/-- Look up the `n_free × R` cleared replacement-row coefficient table for `(f, v)`. -/
def ReplacementDesignData.lookupReplacementRow (data : ReplacementDesignData) (f v : ℕ) :
    List (List ℤ) := data.replacementRows.getD (data.incidences.idxOf (f, v)) []

/-! ### 4. Plain polynomial-time certificates (`ComputableInPolyTime`) -/

section PolyTime
open ComputableInPolyTime
variable {Input : Type} {encIn : Input ↪ List Bool}

private theorem rdb_listAppend {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) := by fun_prop

private theorem rdb_cons {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc) := by fun_prop

private theorem rdb_listIsEmpty {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (List.isEmpty (α := α)) (encList enc) encBool := by fun_prop

private theorem rdb_listZip {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by fun_prop

private theorem rdb_idxOf {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by fun_prop

private theorem rdb_two_mul_unary :
    ComputableInPolyTime (fun n : ℕ => 2 * n) encUnary encUnary := by fun_prop

/-- Compositional plain polynomial-time certificate for `withNeutralScopesList`. -/
@[fun_prop] theorem computableInPolyTime_withNeutralScopesListWithInput
    {scopes : Input → List (List ℕ)} {n_free : Input → ℕ}
    (hscopes : ComputableInPolyTime scopes encIn (encList (encList encNat)))
    (hn : ComputableInPolyTime n_free encIn encUnary) :
    ComputableInPolyTime (fun x => withNeutralScopesList (scopes x) (n_free x))
      encIn (encList (encList encNat)) := by
  unfold withNeutralScopesList
  refine (rdb_listAppend (encList encNat)).comp (hscopes.prod (mapWithInput (range.comp hn) ?_))
  exact (rdb_cons encNat).comp ((unary_to_binary.comp (snd encIn encUnary)).prod (const []))

/-- `withNeutralScopesList` is computable in polynomial time with `n_free` in `encUnary`. -/
@[fun_prop] theorem computableInPolyTime_withNeutralScopesList :
    ComputableInPolyTime (fun p : List (List ℕ) × ℕ => withNeutralScopesList p.1 p.2)
      (encPair (encList (encList encNat)) encUnary) (encList (encList encNat)) := by fun_prop

@[local fun_prop] private theorem rdb_canonicalScopeVars {n_free : Input → ℕ} {s : Input → List ℕ}
    (hn : ComputableInPolyTime n_free encIn encUnary)
    (hs : ComputableInPolyTime s encIn (encList encNat)) :
    ComputableInPolyTime (fun x => canonicalScopeVars (n_free x) (s x))
      encIn (encList encNat) := by
  have hfilt : ComputableInPolyTime (fun x => canonicalScopeVars (n_free x) (s x))
      encIn (encList encUnary) :=
    filterWithInput (range.comp hn)
      (decide_mem (hs.comp (fst encIn encUnary)) (unary_to_binary.comp (snd encIn encUnary)))
  exact (mapWithInput hfilt (unary_to_binary.comp (snd encIn encUnary))).of_enc_eq fun x =>
    congrArg (encList encNat) (List.map_id' (canonicalScopeVars (n_free x) (s x))).symm

@[fun_prop] theorem computableInPolyTime_scopeIncidencesList
    {n_free : Input → ℕ} {scopes : Input → List (List ℕ)}
    (hn : ComputableInPolyTime n_free encIn encUnary)
    (hscopes : ComputableInPolyTime scopes encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => scopeIncidencesList (n_free x) (scopes x))
      encIn (encList (encPair encNat encNat)) :=
  flatMapWithInput (range.comp ((length_list (encList encNat)).comp hscopes)) <|
    mapWithInput (rdb_canonicalScopeVars (hn.comp (fst encIn encUnary))
      ((listGetD []).comp ((hscopes.comp (fst encIn encUnary)).prod (snd encIn encUnary))))
      ((unary_to_binary.comp ((snd encIn encUnary).comp (fst _ _))).prod (snd _ _))

@[local fun_prop] private theorem rdb_normalizeScheduleWord
    {Q r : Input → ℕ} {w : Input → List ℕ}
    (hQ : ComputableInPolyTime Q encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat)
    (hw : ComputableInPolyTime w encIn (encList encNat)) :
    ComputableInPolyTime (fun x => normalizeScheduleWord (Q x) (r x) (w x))
      encIn (encList encNat) := by
  have hmax : ComputableInPolyTime (fun x => max (r x) 1) encIn encNat := by
    have heq : (fun x => max (r x) 1) = fun x => if decide (r x = 0) then 1 else r x := by
      funext x; by_cases h : r x = 0
      · simp only [h, decide_true, ↓reduceIte, Nat.zero_max]
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact Nat.max_eq_left (Nat.pos_of_ne_zero h)
    rw [heq]; fun_prop
  exact mapWithInput (range.comp hQ) (binary_mod.comp
    (((listGetD 0).comp ((hw.comp (fst encIn encUnary)).prod (snd encIn encUnary))).prod
      (hmax.comp (fst encIn encUnary))))

@[fun_prop] theorem computableInPolyTime_normalizeVarSchedules
    {n_free Q r : Input → ℕ} {schedVar : Input → List (List ℕ)}
    (hn : ComputableInPolyTime n_free encIn encUnary) (hQ : ComputableInPolyTime Q encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat)
    (hsched : ComputableInPolyTime schedVar encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => normalizeVarSchedules (n_free x) (Q x) (r x) (schedVar x))
      encIn (encList (encList encNat)) :=
  mapWithInput (range.comp hn) <|
    rdb_normalizeScheduleWord (hQ.comp (fst _ _)) (hr.comp (fst _ _))
      ((listGetD []).comp ((hsched.comp (fst encIn encUnary)).prod (snd encIn encUnary)))

@[fun_prop] theorem computableInPolyTime_normalizeScopeSchedules
    {n_free Q r : Input → ℕ} {scopes schedScope : Input → List (List ℕ)}
    (hn : ComputableInPolyTime n_free encIn encUnary) (hQ : ComputableInPolyTime Q encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat)
    (hscopes : ComputableInPolyTime scopes encIn (encList (encList encNat)))
    (hsched : ComputableInPolyTime schedScope encIn (encList (encList encNat))) :
    ComputableInPolyTime
      (fun x => normalizeScopeSchedules (n_free x) (Q x) (r x) (scopes x) (schedScope x))
      encIn (encList (encList encNat)) := by
  have hempty := (rdb_listIsEmpty encNat).comp
    (rdb_canonicalScopeVars (hn.comp (fst encIn encUnary))
      ((listGetD []).comp ((hscopes.comp (fst encIn encUnary)).prod (snd encIn encUnary))))
  have hrep : ComputableInPolyTime (fun p : Input × ℕ => List.replicate (Q p.1) (0 : ℕ))
      (encPair encIn encUnary) (encList encNat) := by
    simpa only [Function.comp_def, List.map_const', List.length_range] using
      mapWithInput (f := fun (_ : Input × ℕ) (_ : ℕ) => (0 : ℕ))
        (range.comp (hQ.comp (fst encIn encUnary))) (const 0)
  exact mapWithInput (range.comp ((length_list (encList encNat)).comp hscopes)) <|
    hempty.ite' hrep
      (rdb_normalizeScheduleWord (hQ.comp (fst encIn encUnary))
        (hr.comp (fst encIn encUnary))
        ((listGetD []).comp ((hsched.comp (fst encIn encUnary)).prod (snd encIn encUnary))))

@[fun_prop] theorem computableInPolyTime_incidenceLabelsList
    {n_free Q r : Input → ℕ} {scopes schedVar schedScope : Input → List (List ℕ)}
    (hn : ComputableInPolyTime n_free encIn encUnary) (hQ : ComputableInPolyTime Q encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat)
    (hscopes : ComputableInPolyTime scopes encIn (encList (encList encNat)))
    (hschedVar : ComputableInPolyTime schedVar encIn (encList (encList encNat)))
    (hschedScope : ComputableInPolyTime schedScope encIn (encList (encList encNat))) :
    ComputableInPolyTime
      (fun x => incidenceLabelsList (n_free x) (Q x) (r x) (scopes x) (schedVar x) (schedScope x))
      encIn (encList encNat) := by
  have hvs := computableInPolyTime_normalizeVarSchedules hn hQ hr hschedVar
  have hfs := computableInPolyTime_normalizeScopeSchedules hn hQ hr hscopes hschedScope
  refine mapWithInput (computableInPolyTime_scopeIncidencesList hn hscopes) ?_
  exact computableInPolyTime_encodeAuxDigits
    (hr.comp (fst encIn (encPair encNat encNat)))
    ((listGetD_binary [] (hvs.comp (fst encIn (encPair encNat encNat)))
      ((snd encNat encNat).comp (snd _ _))).prod
      (listGetD_binary [] (hfs.comp (fst encIn (encPair encNat encNat)))
        ((fst encNat encNat).comp (snd _ _))))

private theorem computableInPolyTime_equivTuple :
    ComputableInPolyTime ReplacementDesignData.equivTuple
      encReplacementDesignData encReplacementDesignTuple := .of_eq fun _ => rfl
private theorem computableInPolyTime_equivTuple_symm :
    ComputableInPolyTime ReplacementDesignData.equivTuple.symm
      encReplacementDesignTuple encReplacementDesignData := .of_eq fun _ => by
  simp only [encReplacementDesignData, Equiv.toEmbedding_apply, Function.Embedding.trans_apply,
    Equiv.apply_symm_apply]
private theorem proj_poly {Out : Type} {encOut : Out ↪ List Bool}
    (f : ReplacementDesignTuple → Out)
    (hf : ComputableInPolyTime f encReplacementDesignTuple encOut)
    {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => f (ReplacementDesignData.equivTuple (d x))) encIn encOut :=
  (hf.comp computableInPolyTime_equivTuple).comp hd

@[fun_prop] theorem computableInPolyTime_varGroups {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).varGroups) encIn (encList (encList (encList encNat))) :=
  proj_poly (·.1.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_factorGroups {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).factorGroups) encIn (encList (encList encNat)) :=
  proj_poly (·.1.2.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_incidences {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).incidences) encIn (encList (encPair encNat encNat)) :=
  proj_poly (·.1.2.2) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_copyCount {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).copyCount) encIn encNat :=
  proj_poly (·.2.1.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_placements {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).placements) encIn (encList (encPair encNat encNat)) :=
  proj_poly (·.2.1.2.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_measurementMatrix {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).measurementMatrix) encIn (encList (encList encIntBin)) :=
  proj_poly (·.2.1.2.2) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_groupMeasurementMatrices
    {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).groupMeasurementMatrices)
      encIn (encList (encList (encList (encList encIntBin)))) :=
  proj_poly (·.2.2.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_denom {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).denom) encIn encIntBin :=
  proj_poly (·.2.2.2.1) (by unfold encReplacementDesignTuple; fun_prop) hd
@[fun_prop] theorem computableInPolyTime_replacementRows {d : Input → ReplacementDesignData}
    (hd : ComputableInPolyTime d encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => (d x).replacementRows)
      encIn (encList (encList (encList encIntBin))) :=
  proj_poly (·.2.2.2.2) (by unfold encReplacementDesignTuple; fun_prop) hd

/-- **Lemma 4.7 polynomial-time certificate (`buildReplacementDesignData`)**:
`buildReplacementDesignData` is computable in polynomial time from unary parameters
`(n_free, D_cap, Q, r, A₀, R)` and list-encoded `(scopes, schedVar, schedScope)`. -/
@[fun_prop] theorem computableInPolyTime_buildReplacementDesignData
    {n_free D_cap Q r A₀ R : Input → ℕ} {scopes schedVar schedScope : Input → List (List ℕ)}
    (hn : ComputableInPolyTime n_free encIn encUnary)
    (hD : ComputableInPolyTime D_cap encIn encUnary)
    (hQ : ComputableInPolyTime Q encIn encUnary) (hr : ComputableInPolyTime r encIn encUnary)
    (hA₀ : ComputableInPolyTime A₀ encIn encUnary) (hR : ComputableInPolyTime R encIn encUnary)
    (hscopes : ComputableInPolyTime scopes encIn (encList (encList encNat)))
    (hschedVar : ComputableInPolyTime schedVar encIn (encList (encList encNat)))
    (hschedScope : ComputableInPolyTime schedScope encIn (encList (encList encNat))) :
    ComputableInPolyTime
      (fun x => buildReplacementDesignData (n_free x) (D_cap x) (Q x) (r x) (A₀ x) (R x)
        (scopes x) (schedVar x) (schedScope x)) encIn encReplacementDesignData := by
  let incsFn := fun x => scopeIncidencesList (n_free x) (scopes x)
  let incVarsFn := fun x => (incsFn x).map Prod.snd
  let labelsFn := fun x =>
    incidenceLabelsList (n_free x) (Q x) (r x) (scopes x) (schedVar x) (schedScope x)
  let hFn := fun x => (2 * (incsFn x).length) / (r x ^ (2 * Q x))
  let plsFn := fun x => (fiberRanks (labelsFn x)).zip (labelsFn x)
  let vGroupsFn := fun x => (List.range (Q x)).map fun t => (List.range (r x)).map fun g =>
    varGroupList (normalizeVarSchedules (n_free x) (Q x) (r x) (schedVar x)) t g
  let measMatFn := fun x => pullbackMeasurementMatrix (n_free x) (hFn x) (plsFn x) (incVarsFn x)
    (auxMeasurementRowsBounded (D_cap x) (Q x) (r x) (A₀ x) (R x))
  let grpMeasFn := fun x =>
    (vGroupsFn x).map fun gs => gs.map fun Vg => restrictGroupColumns Vg (measMatFn x)
  let replRowsFn := fun x => (List.range (incsFn x).length).map fun e =>
    pullbackReplacementRow (n_free x) (R x) (plsFn x) (incVarsFn x) e
      (auxReplacementTableBounded (D_cap x) (Q x) (r x) (A₀ x) (R x))
  have hr_bin : ComputableInPolyTime r encIn encNat := unary_to_binary.comp hr
  have hvs := computableInPolyTime_normalizeVarSchedules hn hQ hr_bin hschedVar
  have hfs := computableInPolyTime_normalizeScopeSchedules hn hQ hr_bin hscopes hschedScope
  have hincs := computableInPolyTime_scopeIncidencesList hn hscopes
  have hincVars : ComputableInPolyTime incVarsFn encIn (encList encNat) :=
    mapWithInput hincs ((snd encNat encNat).comp (snd encIn (encPair encNat encNat)))
  have hlabels :=
    computableInPolyTime_incidenceLabelsList hn hQ hr_bin hscopes hschedVar hschedScope
  have hh_unary : ComputableInPolyTime hFn encIn encUnary := by
    have h2M_u : ComputableInPolyTime (fun x => 2 * (incsFn x).length) encIn encUnary :=
      rdb_two_mul_unary.comp ((length_list (encPair encNat encNat)).comp hincs)
    have hdiv_b : ComputableInPolyTime hFn encIn encNat :=
      binary_div.comp ((unary_to_binary.comp h2M_u).prod
        (binary_pow' hr_bin (rdb_two_mul_unary.comp hQ)))
    have hmin := binary_min_unary' h2M_u hdiv_b
    have heq : (fun x => min (2 * (incsFn x).length) (hFn x)) = hFn :=
      funext fun _ => Nat.min_eq_right (Nat.div_le_self _ _)
    rwa [heq] at hmin
  have hh_bin : ComputableInPolyTime hFn encIn encNat := unary_to_binary.comp hh_unary
  have hpls : ComputableInPolyTime plsFn encIn (encList (encPair encNat encNat)) :=
    (rdb_listZip encNat encNat).comp
      ((computableInPolyTime_fiberRanksWithInput hlabels).prod hlabels)
  have hbMeas := computableInPolyTime_auxMeasurementRowsBounded hD hQ hr hA₀ hR
  have hbRepl := computableInPolyTime_auxReplacementTableBounded hD hQ hr hA₀ hR
  have hmeasMat :=
    computableInPolyTime_pullbackMeasurementMatrixWithInput hn hh_unary hpls hincVars hbMeas
  have hvGroups : ComputableInPolyTime vGroupsFn encIn
      (encList (encList (encList encNat))) := by
    refine mapWithInput (range.comp hQ)
      (mapWithInput (range.comp (hr.comp (fst encIn encUnary))) ?_)
    have hxin : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => p.1.1)
        (encPair (encPair encIn encUnary) encUnary) encIn :=
      (fst encIn encUnary).comp (fst _ _)
    exact computableInPolyTime_varGroupListWithInput (hvs.comp hxin)
      (unary_to_binary.comp ((snd encIn encUnary).comp (fst _ _)))
      (unary_to_binary.comp (snd _ _))
  have hgrpMeas : ComputableInPolyTime grpMeasFn encIn
      (encList (encList (encList (encList encIntBin)))) :=
    mapWithInput hvGroups (mapWithInput (snd encIn (encList (encList encNat))) <|
      computableInPolyTime_restrictGroupColumnsWithInput (snd _ _)
        (hmeasMat.comp ((fst encIn (encList (encList encNat))).comp (fst _ _))))
  have hdenom := computableInPolyTime_commonDenom_int hQ hR
  have hreplRows : ComputableInPolyTime replRowsFn encIn
      (encList (encList (encList encIntBin))) := by
    refine mapWithInput (range.comp ((length_list (encPair encNat encNat)).comp hincs)) ?_
    have hxin : ComputableInPolyTime (fun p : Input × ℕ => p.1) (encPair encIn encUnary) encIn :=
      fst encIn encUnary
    exact computableInPolyTime_pullbackReplacementRowWithInput (hn.comp hxin) (hR.comp hxin)
      (hpls.comp hxin) (hincVars.comp hxin) (unary_to_binary.comp (snd encIn encUnary))
      (hbRepl.comp hxin)
  have htuple : ComputableInPolyTime
      (fun x => ReplacementDesignData.equivTuple
        (buildReplacementDesignData (n_free x) (D_cap x) (Q x) (r x) (A₀ x) (R x)
          (scopes x) (schedVar x) (schedScope x))) encIn encReplacementDesignTuple :=
    (hvGroups.prod (hfs.prod hincs)).prod
      ((hh_bin.prod (hpls.prod hmeasMat)).prod
        (hgrpMeas.prod (hdenom.prod hreplRows)))
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using
    computableInPolyTime_equivTuple_symm.comp htuple

/-- Compositional plain polynomial-time certificate for `lookupReplacementRow`. -/
@[fun_prop] theorem computableInPolyTime_lookupReplacementRow
    {data : Input → ReplacementDesignData} {f v : Input → ℕ}
    (hdata : ComputableInPolyTime data encIn encReplacementDesignData)
    (hf : ComputableInPolyTime f encIn encNat) (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => (data x).lookupReplacementRow (f x) (v x))
      encIn (encList (encList encIntBin)) := by
  have hincs := computableInPolyTime_incidences hdata
  have hrows := computableInPolyTime_replacementRows hdata
  unfold ReplacementDesignData.lookupReplacementRow
  exact (listGetD []).comp (hrows.prod
    ((rdb_idxOf (encPair encNat encNat)).comp (hincs.prod (hf.prod hv))))

end PolyTime

/-! ### 5. Semantic bridge from `buildReplacementDesignData` to `ReplacementDesign` -/

private theorem varMeasurementMatrix_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (Q r A₀ R : ℕ) (K : Type*) [CommRing K] {n h : ℕ}
    (equiv : A ≃ B) (placeB : B → Fin h × AuxLabel Q r) (varOfB : B → Fin n)
    (p : Fin h × measurementIndices Q r A₀ R) (v : Fin n) :
    varMeasurementMatrix Q r A₀ R K (placeB ∘ equiv) (varOfB ∘ equiv) p v =
      varMeasurementMatrix Q r A₀ R K placeB varOfB p v := by
  classical
  simp only [varMeasurementMatrix, Finset.sum_filter, Function.comp_apply]
  exact Equiv.sum_comp equiv fun b =>
    if (placeB b).1 = p.1 ∧ varOfB b = v then measurementMatrix Q r A₀ R K p.2 (placeB b).2 else 0

private theorem varReplacementRowScaledInt_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (Q r A₀ R : ℕ) {n h : ℕ}
    (equiv : A ≃ B) (placeB : B → Fin h × AuxLabel Q r) (varOfB : B → Fin n) (e : A) (v : Fin n) :
    varReplacementRowScaledInt Q r A₀ R (placeB ∘ equiv) (varOfB ∘ equiv) e v =
      varReplacementRowScaledInt Q r A₀ R placeB varOfB (equiv e) v := by
  classical
  simp only [varReplacementRowScaledInt, Finset.sum_filter, Function.comp_apply]
  exact Equiv.sum_comp equiv fun b =>
    if (placeB b).1 = (placeB (equiv e)).1 ∧ varOfB b = v then
      auxReplacementRowScaledInt Q r A₀ R (placeB (equiv e)).2 (placeB b).2 else 0

theorem fiberBound_of_balancedSchedule {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ))
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    let scope := listScopeFamily n_free scopes
    let u := incidenceLabel (scopeVarOf scope) (scopeFactorOf scope)
      (varAssignOfList hr n_free Q schedVar) (factorAssignOfList hr n_free Q scopes schedScope)
    let M := (scopeIncidencesList n_free scopes).length
    ∀ y : AuxLabel Q r,
      #{i : Fin M | u (finToScopeIncidence n_free scopes i) = y} ≤ 2 * M / r ^ (2 * Q) := by
  intro scope u M y
  have hD : 0 < r ^ (2 * Q) := pow_pos hr (2 * Q)
  have hocc := hbal.1 y
  have hcard : Fintype.card (ScopeIncidence scope) = M := by
    rw [Fintype.card_congr (scopeIncidenceEquivFin n_free scopes), Fintype.card_fin]
  rw [hcard] at hocc
  have heq_card : #{i : Fin M | u (finToScopeIncidence n_free scopes i) = y} = occupancy u y := by
    unfold occupancy; rw [Fintype.card_subtype]
    refine Finset.card_bij (fun i _ => finToScopeIncidence n_free scopes i)
      (fun i hi => by simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact hi)
      (fun i₁ _ i₂ _ h12 => (bijective_finToScopeIncidence n_free scopes).1 h12)
      (fun e he => ⟨scopeIncidenceEquivFin n_free scopes e, ?_,
        finToScopeIncidence_scopeIncidenceEquivFin n_free scopes e⟩)
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    rwa [finToScopeIncidence_scopeIncidenceEquivFin]
  rw [heq_card]; exact (Nat.le_div_iff_mul_le hD).mpr hocc

/-- Concrete `Fin M`-indexed placement `Fin M → Fin h × AuxLabel Q r` from `BalancedSchedule`. -/
noncomputable def placeFinOfBalanced {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ))
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    let M := (scopeIncidencesList n_free scopes).length
    Fin M → Fin (2 * M / r ^ (2 * Q)) × AuxLabel Q r :=
  let scope := listScopeFamily n_free scopes
  let uFin : Fin (scopeIncidencesList n_free scopes).length → AuxLabel Q r :=
    fun i => incidenceLabel (scopeVarOf scope) (scopeFactorOf scope)
      (varAssignOfList hr n_free Q schedVar) (factorAssignOfList hr n_free Q scopes schedScope)
      (finToScopeIncidence n_free scopes i)
  fun i => (fiberRankCopy uFin
    (fiberBound_of_balancedSchedule hr n_free Q scopes schedVar schedScope hbal) i, uFin i)

/-- **Concrete `ReplacementDesign` induced by `BalancedSchedule` (Lemma 4.7, pp. 33–34)**:
constructs `ReplacementDesign (listScopeFamily n_free scopes) Q r A₀ R τ` from balanced schedules
`(schedVar, schedScope)` and Lemma 4.7's numerical and binomial-tail hypotheses. -/
noncomputable def constructedReplacementDesign {n_free Q r A₀ R b : ℕ} {τ : ℚ}
    (scopes schedVar schedScope : List (List ℕ)) (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hb_pos : 1 ≤ b)
    (hτ : 0 ≤ τ) (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hM_le : (∑ f : Fin scopes.length, #(listScopeFamily n_free scopes f)) ≤ b * n_free)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ)))
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    ReplacementDesign (listScopeFamily n_free scopes) Q r A₀ R τ :=
  let scope := listScopeFamily n_free scopes
  let a := varAssignOfList hr n_free Q schedVar
  let d := factorAssignOfList hr n_free Q scopes schedScope
  let h := 2 * (scopeIncidencesList n_free scopes).length / r ^ (2 * Q)
  let place := placeFinOfBalanced hr n_free Q scopes schedVar schedScope hbal ∘
    scopeIncidenceEquivFin n_free scopes
  have hinj_place : Function.Injective place :=
    (injective_fiberRankCopy_prod _
      (fiberBound_of_balancedSchedule hr n_free Q scopes schedVar schedScope hbal)).comp
      (scopeIncidenceEquivFin n_free scopes).injective
  have hplace_snd : ∀ e : ScopeIncidence scope,
      (place e).2 = (a (scopeVarOf scope e), d (scopeFactorOf scope e)) := fun e => by
    dsimp only [place, placeFinOfBalanced, incidenceLabel, Function.comp_apply, a, d, scope]
    rw [finToScopeIncidence_scopeIncidenceEquivFin]
  have hhD : h * r ^ (2 * Q) ≤ 2 * ∑ f : Fin scopes.length, #(scope f) := by
    rw [← length_scopeIncidencesList]; exact Nat.div_mul_le_self _ _
  { varAssign := a, factorAssign := d, h := h, place := place
    card_varGroup_le := fun t g => by
      rw [card_varGroup_eq_occupancy]; exact (Nat.le_div_iff_mul_le hr).mpr (hbal.2 t g)
    factorAssign_of_empty := fun _ hf =>
      factorAssignOfList_of_empty hr n_free Q scopes schedScope hf
    injective_place := hinj_place, place_snd := hplace_snd, h_mul_D_le := hhD
    total_measurement_rows_le :=
      card_allGroupMeasurementRows_le_two_mul_tau_mul_n hr hb_pos hτ hhD hM_le htail
    sum_abs_measurement_row_le :=
      sum_abs_varMeasurementMatrix_le Q r A₀ R hinj_place (scopeVarOf scope)
    natDegree_replacementRow_le := natDegree_varReplacementRow_le Q r A₀ R place (scopeVarOf scope)
    eval_replacementRow_zero := eval_varReplacementRow_zero Q r A₀ R hinj_place (scopeVarOf scope)
    evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
      evalVarReplacementRow_nodePoint_eq_zero_of_kernel Q r A₀ R place (scopeVarOf scope) a
        (fun e' => congrArg Prod.fst (hplace_snd e')) e t g
        (by rwa [congrArg Prod.snd (hplace_snd e)]) ξ hsupp hker
    map_replacementRowScaledInt := map_varReplacementRowScaledInt Q r A₀ R place (scopeVarOf scope)
    sum_coeffNorm1_replacementRowScaledInt_le :=
      sum_coeffNorm1_varReplacementRowScaledInt_le hQ hinj_place (scopeVarOf scope) hI }

private theorem placements_eq_ofFn_placeFin {r : ℕ} (hr : 1 ≤ r) (n_free Q : ℕ)
    (scopes schedVar schedScope : List (List ℕ))
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    let labels := incidenceLabelsList n_free Q r scopes schedVar schedScope
    let plFin := placeFinOfBalanced hr n_free Q scopes schedVar schedScope hbal
    (fiberRanks labels).zip labels =
      List.ofFn fun i : Fin (scopeIncidencesList n_free scopes).length =>
        ((plFin i).1.1, encodeAuxLabel (plFin i).2) := by
  intro labels plFin
  have hD : 0 < r ^ (2 * Q) := pow_pos hr (2 * Q)
  have hinj : Function.Injective (encodeAuxLabel (Q := Q) (r := r)) := fun x y h => by
    have := congrArg (decodeAuxLabel hD) h
    rwa [decodeAuxLabel_encodeAuxLabel, decodeAuxLabel_encodeAuxLabel] at this
  have hof : labels = List.ofFn fun j => encodeAuxLabel (plFin j).2 :=
    incidenceLabelsList_eq_ofFn hr n_free Q scopes schedVar schedScope
  have hlen : ((fiberRanks labels).zip labels).length =
      (scopeIncidencesList n_free scopes).length := by
    simp only [List.length_zip, length_fiberRanks, Nat.min_self, labels, length_incidenceLabelsList]
  refine List.ext_getElem (hlen.trans List.length_ofFn.symm) fun i hi _ => ?_
  rw [hlen] at hi
  have hl : i < labels.length := by simpa only [labels, length_incidenceLabelsList] using hi
  have hlbl : ∀ j : Fin labels.length, labels[j] = encodeAuxLabel
      (plFin ⟨j.1, by simpa only [labels, length_incidenceLabelsList] using j.2⟩).2 := fun j => by
    conv_lhs => rw [Fin.getElem_fin]; simp only [hof, List.getElem_ofFn]
  rw [List.getElem_zip, List.getElem_ofFn, getElem_fiberRanks_eq_fiberRank labels ⟨i, hl⟩]
  refine Prod.ext ?_ (hlbl ⟨i, hl⟩)
  dsimp only [plFin, placeFinOfBalanced, fiberRankCopy, fiberRank]
  refine Finset.card_bij
    (fun (j : Fin labels.length) _ =>
      (⟨j.1, by simpa only [labels, length_incidenceLabelsList] using j.2⟩ :
        Fin (scopeIncidencesList n_free scopes).length))
    (fun j hj => ?_) (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
    (fun k hk => ⟨⟨k.1, by simpa only [labels, length_incidenceLabelsList] using k.2⟩, ?_, rfl⟩)
  · simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hj ⊢
    exact ⟨hinj ((hlbl j).symm.trans (hj.1.trans (hlbl ⟨i, hl⟩))), hj.2⟩
  · simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hk ⊢
    exact ⟨(hlbl _).trans ((congrArg encodeAuxLabel hk.1).trans (hlbl ⟨i, hl⟩).symm), hk.2⟩

private theorem incVars_eq_ofFn (n_free : ℕ) (scopes : List (List ℕ)) :
    (scopeIncidencesList n_free scopes).map Prod.snd =
      List.ofFn fun i : Fin (scopeIncidencesList n_free scopes).length =>
        (scopeVarOf (listScopeFamily n_free scopes) (finToScopeIncidence n_free scopes i)).1 := by
  refine List.ext_getElem (by simp only [List.length_map, List.length_ofFn]) fun i hi _ => ?_
  rw [List.length_map] at hi
  simp only [List.getElem_map, List.getElem_ofFn, scopeVarOf, finToScopeIncidence]

/-- Componentwise refinement predicate asserting that `data : ReplacementDesignData` represents
`D : ReplacementDesign (listScopeFamily n_free scopes) Q r A₀ R τ` across all Definition 3.1
components, including global `ℚ`-kernel equivalence and restricted-kernel evaluation annihilation
from `C_{t,g}`. -/
def ReplacementDesignData.Refines {n_free Q r A₀ R : ℕ} {τ : ℚ}
    (scopes : List (List ℕ)) (data : ReplacementDesignData)
    (D : ReplacementDesign (listScopeFamily n_free scopes) Q r A₀ R τ) : Prop :=
  let scope := listScopeFamily n_free scopes
  data.copyCount = D.h ∧ data.denom = (commonDenom Q R : ℤ) ∧
  (∀ (t : Fin Q) (g : Fin r),
    ((data.varGroups.getD t.1 []).getD g.1 []).Nodup ∧
    ((data.varGroups.getD t.1 []).getD g.1 []).length ≤ 2 * n_free / r ∧
      ∀ v : Fin n_free,
        v.1 ∈ (data.varGroups.getD t.1 []).getD g.1 [] ↔ v ∈ varGroup D.varAssign t g) ∧
  (∀ (f : Fin scopes.length) (t : Fin Q),
    (data.factorGroups.getD f.1 []).getD t.1 0 = (D.factorAssign f t).1) ∧
  (∀ (e : ScopeIncidence scope),
    let rowTable := data.lookupReplacementRow (scopeFactorOf scope e).1 (scopeVarOf scope e).1
    rowTable = data.replacementRows.getD (scopeIncidenceEquivFin n_free scopes e).1 [] ∧
    Cslib.IsTableShape n_free R rowTable ∧
    ∀ i : Fin n_free, Polynomial.ofCoeffList (rowTable.getD i.1 []) =
      varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) e i) ∧
  (∀ ξ : Fin n_free → ℚ,
    ((varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ = 0 ↔
      ∀ row ∈ data.measurementMatrix, (∑ i : Fin n_free, (row.getD i.1 0 : ℚ) * ξ i) = 0)) ∧
  (∀ (t : Fin Q) (g : Fin r) (ξ : Fin n_free → ℚ),
    (∀ i ∉ varGroup D.varAssign t g, ξ i = 0) →
    (∀ r_row ∈ (data.groupMeasurementMatrices.getD t.1 []).getD g.1 [],
      (∑ j ∈ Finset.range ((data.varGroups.getD t.1 []).getD g.1 []).length,
        (r_row.getD j 0 : ℚ) *
          (if h : ((data.varGroups.getD t.1 []).getD g.1 []).getD j 0 < n_free then
            ξ ⟨((data.varGroups.getD t.1 []).getD g.1 []).getD j 0, h⟩ else 0)) = 0) →
    ∀ e : ScopeIncidence scope, g ≠ D.factorAssign (scopeFactorOf scope e) t →
      evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) e (nodePoint t) ξ = 0)

/-- **Main Lemma 4.7 semantic specification (`buildReplacementDesignData_spec`)**:
under Lemma 4.7's cap, interval, binomial-tail, and `BalancedSchedule` hypotheses,
`buildReplacementDesignData` refines `constructedReplacementDesign`. -/
theorem buildReplacementDesignData_spec {n_free D_cap Q r A₀ R b : ℕ} {τ : ℚ}
    (scopes schedVar schedScope : List (List ℕ)) (hD_cap : r ^ (2 * Q) ≤ D_cap)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hb_pos : 1 ≤ b) (hτ : 0 ≤ τ)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q) (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ)))
    (hM_le : (∑ f : Fin scopes.length, #(listScopeFamily n_free scopes f)) ≤ b * n_free)
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    (buildReplacementDesignData n_free D_cap Q r A₀ R scopes schedVar schedScope).Refines scopes
      (constructedReplacementDesign scopes schedVar schedScope hr hQ hb_pos hτ hI hM_le htail
        hbal) := by
  let data := buildReplacementDesignData n_free D_cap Q r A₀ R scopes schedVar schedScope
  let D :=
    constructedReplacementDesign scopes schedVar schedScope hr hQ hb_pos hτ hI hM_le htail hbal
  let scope := listScopeFamily n_free scopes
  let h := 2 * (scopeIncidencesList n_free scopes).length / r ^ (2 * Q)
  let eqv := scopeIncidenceEquivFin n_free scopes; have hD_pos : 0 < r ^ (2 * Q) := pow_pos hr _
  have hinj_enc : Function.Injective (encodeAuxLabel (Q := Q) (r := r)) := fun x y heq => by
    have := congrArg (decodeAuxLabel hD_pos) heq
    rwa [decodeAuxLabel_encodeAuxLabel, decodeAuxLabel_encodeAuxLabel] at this
  let plFin := placeFinOfBalanced hr n_free Q scopes schedVar schedScope hbal
  let varOfFin : Fin (scopeIncidencesList n_free scopes).length → Fin n_free :=
    fun i => scopeVarOf scope (finToScopeIncidence n_free scopes i)
  let plsOf := List.ofFn fun k => ((plFin k).1.1, encodeAuxLabel (plFin k).2)
  let varsOf := List.ofFn fun k => (varOfFin k).1; have hinc_list := incVars_eq_ofFn n_free scopes
  have hpl_list := placements_eq_ofFn_placeFin hr n_free Q scopes schedVar schedScope hbal
  have hvarOf_comp : scopeVarOf scope = varOfFin ∘ eqv := funext fun e => by
    simp only [Function.comp_apply, varOfFin, eqv, finToScopeIncidence_scopeIncidenceEquivFin]
  have hbMeas_eq :=
    auxMeasurementRowsBounded_eq_auxMeasurementRows (r := r) (A₀ := A₀) (R := R) hD_cap
  have hbRepl_eq :=
    auxReplacementTableBounded_eq_auxReplacementTable (r := r) (A₀ := A₀) (R := R) hD_cap
  have hVtg_eq : ∀ (t : Fin Q) (g : Fin r), (data.varGroups.getD t.1 []).getD g.1 [] =
      varGroupList (normalizeVarSchedules n_free Q r schedVar) t.1 g.1 := fun t g => by
    dsimp only [data, buildReplacementDesignData]
    rw [List.getD_map_range _ [] t.2, List.getD_map_range _ [] g.2]
  have hVtg_mem : ∀ (t : Fin Q) (g : Fin r) (v : Fin n_free),
      v.1 ∈ varGroupList (normalizeVarSchedules n_free Q r schedVar) t.1 g.1 ↔
        v ∈ varGroup D.varAssign t g := fun t g v => by
    rw [mem_varGroupList, length_normalizeVarSchedules, mem_varGroup, Fin.ext_iff]
    dsimp only [D, constructedReplacementDesign]; simp only [val_varAssignOfList, v.2, true_and]
  have hker_iff : ∀ ξ : Fin n_free → ℚ,
      (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ = 0 ↔
        ∀ row ∈ data.measurementMatrix, (∑ i : Fin n_free, (row.getD i.1 0 : ℚ) * ξ i) = 0 := by
    intro ξ
    let xExec : ℕ → ℚ := fun v => if hv : v < n_free then ξ ⟨v, hv⟩ else 0
    have hmat_eq : varMeasurementMatrix Q r A₀ R ℚ (plFin ∘ eqv) (scopeVarOf scope) =
        varMeasurementMatrix Q r A₀ R ℚ plFin varOfFin := by
      ext p v; rw [hvarOf_comp]
      exact varMeasurementMatrix_comp_equiv Q r A₀ R ℚ eqv plFin varOfFin p v
    have hmeas_def : data.measurementMatrix =
        pullbackMeasurementMatrix n_free h plsOf varsOf (auxMeasurementRows Q r A₀ R) := by
      dsimp only [data, buildReplacementDesignData, h]; rw [hpl_list, hinc_list, hbMeas_eq]
    have hvars_lt : ∀ v ∈ varsOf, v < n_free := fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact (varOfFin i).2
    have hD_lt : ∀ p ∈ plsOf, p.2 < r ^ (2 * Q) := fun p hp => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact encodeAuxLabel_lt (plFin i).2
    have hrow_sum : ∀ (c : Fin h) (auxRow : List ℤ),
        (∑ i : Fin n_free,
          ((pullbackMeasurementRow n_free plsOf varsOf c.1 auxRow).getD i.1 0 : ℚ) * ξ i) =
        ∑ u : AuxLabel Q r,
          (auxRow.getD (encodeAuxLabel u) 0 : ℚ) * copyProj c (copyEmbed plFin varOfFin ξ) u := by
      intro c auxRow
      have hlhs : (∑ i : Fin n_free,
            ((pullbackMeasurementRow n_free plsOf varsOf c.1 auxRow).getD i.1 0 : ℚ) * ξ i) =
          ∑ v ∈ Finset.range n_free,
            ((pullbackMeasurementRow n_free plsOf varsOf c.1 auxRow).getD v 0 : ℚ) * xExec v := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun i _ => by simp only [xExec, i.2, ↓reduceDIte]
      rw [hlhs, sum_pullbackMeasurementRow_mul hvars_lt hD_lt]; symm
      refine Finset.sum_bij (fun u _ => encodeAuxLabel u)
        (fun u _ => Finset.mem_range.mpr (encodeAuxLabel_lt u)) (fun _ _ _ _ heq => hinj_enc heq)
        (fun y hy => ⟨decodeAuxLabel hD_pos y, mem_univ _,
          encodeAuxLabel_decodeAuxLabel hD_pos (Finset.mem_range.mp hy)⟩)
        fun u _ => congrArg ((auxRow.getD (encodeAuxLabel u) 0 : ℚ) * ·)
          (copyEmbedExec_ofFn_eq_copyProj_copyEmbed plFin varOfFin hinj_enc ξ xExec
            (fun v => by simp only [xExec, v.2, ↓reduceDIte]) c u).symm
    change (varMeasurementMatrix Q r A₀ R ℚ (plFin ∘ eqv) (scopeVarOf scope)).mulVec ξ = 0 ↔ _
    rw [hmat_eq, varMeasurementMatrix_mulVec_eq_zero_iff, hmeas_def]
    simp only [measurementMatrix_mulVec_eq_zero_iff_auxMeasurementRows, pullbackMeasurementMatrix,
      List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨by rintro hker _ ⟨c, hc, auxRow, haux, rfl⟩
              rw [hrow_sum ⟨c, hc⟩ auxRow]; exact hker ⟨c, hc⟩ auxRow haux,
      fun hrows c auxRow haux => by
        rw [← hrow_sum c auxRow]; exact hrows _ ⟨c.1, c.2, auxRow, haux, rfl⟩⟩
  refine ⟨rfl, rfl, fun t g => ?_, fun f t => ?_, fun e => ?_, hker_iff,
    fun t g ξ hsupp hker_ctg e hg => ?_⟩
  · rw [hVtg_eq t g, length_varGroupList_eq_occupancy hr n_free Q schedVar t g]
    exact ⟨nodup_varGroupList _ t.1 g.1, (Nat.le_div_iff_mul_le hr).mpr (hbal.2 t g), hVtg_mem t g⟩
  · dsimp only [data, D, buildReplacementDesignData, constructedReplacementDesign]
    exact (val_factorAssignOfList hr n_free Q scopes schedScope f t).symm
  · dsimp only [scope]
    have hlkp : data.lookupReplacementRow (scopeFactorOf (listScopeFamily n_free scopes) e).1
          (scopeVarOf (listScopeFamily n_free scopes) e).1 =
        data.replacementRows.getD (eqv e).1 [] := by
      dsimp only [ReplacementDesignData.lookupReplacementRow, data, buildReplacementDesignData, eqv]
      rw [← val_scopeIncidenceEquivFin_eq_idxOf n_free scopes e]
    have hrow_eq : data.replacementRows.getD (eqv e).1 [] =
        pullbackReplacementRow n_free R plsOf varsOf (eqv e).1 (auxReplacementTable Q r A₀ R) := by
      dsimp only [data, buildReplacementDesignData]
      rw [List.getD_map_range _ [] (eqv e).2, hpl_list, hinc_list, hbRepl_eq]
    rw [hlkp]
    refine ⟨rfl, hrow_eq ▸ isTableShape_pullbackReplacementRow n_free R _ _ _ _, fun i => ?_⟩
    rw [hrow_eq]
    have hrepl_spec : ∀ (y : AuxLabel Q r) {k : ℕ}, k < R →
        Cslib.rowEntry ((auxReplacementTable Q r A₀ R).getD (encodeAuxLabel (plFin (eqv e)).2) [])
          (encodeAuxLabel y) k =
          (auxReplacementRowScaledInt Q r A₀ R (plFin (eqv e)).2 y).coeff k := fun y _ _ => by
      rw [Cslib.rowEntry, getD_auxReplacementTable (encodeAuxLabel_lt _) (encodeAuxLabel_lt _),
        decodeAuxLabel_encodeAuxLabel, decodeAuxLabel_encodeAuxLabel, getD_auxReplacementRowCoeffs]
    rw [ofCoeffList_pullbackReplacementRow_ofFn_eq_varReplacementRowScaledInt hR plFin varOfFin
      encodeAuxLabel (auxReplacementTable Q r A₀ R) (eqv e) hrepl_spec i]
    have hcomp := (varReplacementRowScaledInt_comp_equiv Q r A₀ R eqv plFin varOfFin e i).symm
    rwa [← hvarOf_comp] at hcomp
  · let Vtg := varGroupList (normalizeVarSchedules n_free Q r schedVar) t.1 g.1
    have hCtg_d : (data.groupMeasurementMatrices.getD t.1 []).getD g.1 [] =
        restrictGroupColumns Vtg data.measurementMatrix := by
      dsimp only [data, buildReplacementDesignData, Vtg]
      rw [List.map_map, List.getD_map_range _ [] t.2, Function.comp_apply, List.map_map,
        List.getD_map_range _ [] g.2, Function.comp_apply]
    rw [hVtg_eq t g, hCtg_d] at hker_ctg
    let xExec : ℕ → ℚ := fun v => if hv : v < n_free then ξ ⟨v, hv⟩ else 0
    have hVtg_lt : ∀ v ∈ Vtg, v < n_free := fun v hv => by
      simpa only [length_normalizeVarSchedules] using (mem_varGroupList.mp hv).1
    have hsupp_exec : ∀ v < n_free, v ∉ Vtg → xExec v = 0 := fun v hv hnot => by
      simp only [xExec, hv, ↓reduceDIte]
      exact hsupp ⟨v, hv⟩ fun hmem => hnot ((hVtg_mem t g ⟨v, hv⟩).mpr hmem)
    have hmulVec : (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ = 0 := by
      rw [hker_iff]; intro row hrow
      have hrow_len : row.length = n_free := by
        dsimp only [data, buildReplacementDesignData] at hrow
        exact length_row_of_mem_pullbackMeasurementMatrix hrow
      have hsum_eq : (∑ i : Fin n_free, (row.getD i.1 0 : ℚ) * ξ i) =
          ∑ v ∈ Finset.range row.length, (row.getD v 0 : ℚ) * xExec v := by
        rw [hrow_len, ← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun i _ => by simp only [xExec, i.2, ↓reduceDIte]
      rw [hsum_eq, ← sum_restrictGroupRow_mul (nodup_varGroupList _ t.1 g.1)
        (by simpa only [hrow_len] using hVtg_lt) (by simpa only [hrow_len] using hsupp_exec)]
      exact hker_ctg (Vtg.map fun v => row.getD v 0) (List.mem_map.mpr ⟨row, hrow, rfl⟩)
    exact D.evalReplacementRow_nodePoint_eq_zero_of_kernel e t g hg ξ hsupp hmulVec

/-- Bundled existential packaging of `buildReplacementDesignData_spec`. -/
theorem exists_replacementDesign_of_buildReplacementDesignData {n_free D_cap Q r A₀ R b : ℕ}
    {τ : ℚ} (scopes schedVar schedScope : List (List ℕ)) (hD_cap : r ^ (2 * Q) ≤ D_cap)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hb_pos : 1 ≤ b) (hτ : 0 ≤ τ)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q) (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ)))
    (hM_le : (∑ f : Fin scopes.length, #(listScopeFamily n_free scopes f)) ≤ b * n_free)
    (hbal : BalancedSchedule hr n_free Q scopes schedVar schedScope) :
    ∃ D : ReplacementDesign (listScopeFamily n_free scopes) Q r A₀ R τ,
      (buildReplacementDesignData n_free D_cap Q r A₀ R scopes schedVar schedScope).Refines
        scopes D :=
  ⟨constructedReplacementDesign scopes schedVar schedScope hr hQ hb_pos hτ hI hM_le htail hbal,
   buildReplacementDesignData_spec scopes schedVar schedScope hD_cap hr hR hQ hb_pos hτ hI htail
     hM_le hbal⟩

/-- **Neutral-padded Lemma 4.7 specialization (`exists_replacementDesign_withNeutralScopesList`)**:
when each free variable belongs to at most `b₀` scopes of `scopes` and `(schedVar, schedScope)`
satisfies `BalancedSchedule` on `withNeutralScopesList scopes n_free`, `buildReplacementDesignData`
refines a concrete `ReplacementDesign` on the augmented scope family with occurrence bound
`b = b₀ + 1`. -/
theorem exists_replacementDesign_withNeutralScopesList {n_free D_cap Q r A₀ R b₀ : ℕ} {τ : ℚ}
    (scopes schedVar schedScope : List (List ℕ)) (hD_cap : r ^ (2 * Q) ≤ D_cap)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hτ : 0 ≤ τ) (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hb₀ : ∀ v : Fin n_free, varIncidence univ (listScopeFamily n_free scopes) v ≤ b₀)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * ((b₀ + 1 : ℕ) : ℚ)))
    (hbal :
      BalancedSchedule hr n_free Q (withNeutralScopesList scopes n_free) schedVar schedScope) :
    let augScopes := withNeutralScopesList scopes n_free
    ∃ D : ReplacementDesign (listScopeFamily n_free augScopes) Q r A₀ R τ,
      (buildReplacementDesignData n_free D_cap Q r A₀ R augScopes schedVar schedScope).Refines
        augScopes D := by
  have hM_le : (∑ f : Fin (withNeutralScopesList scopes n_free).length,
      #(listScopeFamily n_free (withNeutralScopesList scopes n_free) f)) ≤ (b₀ + 1) * n_free := by
    change totalIncidence univ (listScopeFamily n_free (withNeutralScopesList scopes n_free)) ≤ _
    rw [totalIncidence_listScopeFamily_withNeutralScopesList]
    have h := totalIncidence_withNeutralFactors_le (I := (univ : Finset (Fin scopes.length))) hb₀
    rwa [totalIncidence_withNeutralFactors, Fintype.card_fin] at h
  exact exists_replacementDesign_of_buildReplacementDesignData
    (withNeutralScopesList scopes n_free) schedVar schedScope hD_cap hr hR hQ
    (Nat.le_add_left 1 b₀) hτ hI htail hM_le hbal

end Cslib.LinearAlgebra
