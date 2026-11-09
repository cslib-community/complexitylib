/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.CellProbe.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sort
import Mathlib.Logic.Equiv.Embedding

/-!
# Hard Operational Sequence Distributions and Yao Setup for Dynamic Dictionaries

This module formalizes the hard operational distributions, uniform dictionary marginals,
zero-error Yao coin-fixing specializations, and parallel single-timestamp state decoder used in the
dynamic succinct dictionary cell-probe lower bounds of Li, Liang, Yu, and Zhou
([LiLiangYuZhou2023]; locators below follow `arXiv:2306.02253v3`, where printed page `p` is PDF
page `p + 1`).

1. **Finite operation alphabet (`validOps U V`):** Because `Dynamic.Op.insert u v` carries an
   unbounded `v : ℕ` constrained to `v < V` by `(Dynamic.spec U V n).valid`, `Dynamic.Op U` is not
   finite. `validOps U V` restricts to all `.query u`, `.delete u`, and `.insert u v` with `v < V`
   (cardinality `2 * U + U * V`), containing every admissible operation history.
2. **Hard operational distributions (`insertQueryDeleteDist` and `insertDeleteDist`):**
   For `2 * n ≤ U` and `1 ≤ V`, sampling an injective key sequence `keys : Fin (2 * n) ↪ Fin U` and
   independent value vector `vals : Fin (2 * n) → Fin V` uniformly produces:
   * `insertQueryDeleteDist U V n hU hV` ([LiLiangYuZhou2023], Section 3, `Distribution 1`, p. 11 /
     PDF p. 12, extended with independent uniform values in `Fin V` as in Section 7, Definition 7.1,
     p. 25 / PDF p. 26 and Section 8, p. 28 / PDF p. 29; `V = 1` recovers key-only membership): `n`
     initial insertions followed by `n` three-step `[query, delete, insert]` meta-operations
     (`4 * n` elementary operations).
   * `insertDeleteDist U V n hU hV` ([LiLiangYuZhou2023], Section 8, proof of Theorem 1.3, p. 28 /
     PDF p. 29): `n` initial insertions followed by `n` two-step `[delete, insert]` update-only
     meta-operations (`3 * n` elementary operations, issuing zero `.query` operations).
3. **Admissibility and exact uniform size-`n` state marginals (`SizedDict`, `sizedDictEquiv`):**
   Every supported sequence of either distribution is admissible for `Dynamic.spec U V n` from
   `Dictionary.empty U`, and after the `n` initial insertions plus any `t ≤ n` complete
   meta-operations, the reached dictionary state has `n` keys, values `< V`, and uniform marginal
   distribution over the `U.choose n * V ^ n` valid size-`n` dictionaries (`SizedDict U V n`,
   bijecting via `sizedDictEquiv` with `{ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)`).
4. **All-history zero-error Yao reduction and `decodeDict`:**
   Specializing `DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes`
   (and its `ObliviousSequenceImpl` and `StateTransitionImpl` companions) over `validOps U V` with
   correctness horizon `4 * n + 1` (resp. `3 * n + 1`) yields a deterministic step-indexed
   `IndexedScheme` exact on *every* admissible history of length `≤ 4 * n + 1`
   (resp. `≤ 3 * n + 1`), not merely on the hard distribution's support. Evaluating single-step
   `.query u` mathematically at fixed step index `t` (`decodeDict D_det t C_t`, a formalization
   adaptation making time-indexed state recovery explicit without advancing the step clock across
   keys) recovers the exact abstract state `s_t` after any admissible prefix of length `t ≤ 4 * n`
   (resp. `≤ 3 * n`).

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.validOps`: finite alphabet of `2 * U + U * V`
  value-bounded dynamic dictionary operations.
* `Cslib.DataStructure.Dictionary.CellProbe.SizedDict`,
  `Cslib.DataStructure.Dictionary.CellProbe.sizedDictEquiv`,
  `Cslib.DataStructure.Dictionary.CellProbe.extractKeySetVals`: finite subtype of size-`n`,
  `V`-bounded dictionary states and its canonical equivalence with key-set / value-vector pairs.
* `Cslib.DataStructure.Dictionary.CellProbe.initInsertSeq`,
  `Cslib.DataStructure.Dictionary.CellProbe.queryDeleteInsertMetaOp`,
  `Cslib.DataStructure.Dictionary.CellProbe.deleteInsertMetaOp`,
  `Cslib.DataStructure.Dictionary.CellProbe.insertQueryDeleteSeq`,
  `Cslib.DataStructure.Dictionary.CellProbe.insertDeleteSeq`: deterministic sequence builders.
* `Cslib.DataStructure.Dictionary.CellProbe.insertQueryDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.insertDeleteDist`: hard operational distributions.
* `Cslib.DataStructure.Dictionary.CellProbe.validHistoriesUpTo`,
  `Cslib.DataStructure.Dictionary.CellProbe.decodeDict`: bounded-length admissible history family
  and single-timestamp parallel state decoder on `IndexedScheme`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.card_validOps`,
  `Cslib.DataStructure.Dictionary.CellProbe.forall_mem_validOps_of_validHistory`: cardinality and
  completeness of `validOps U V` for admissible histories.
* `Cslib.DataStructure.Dictionary.CellProbe.card_sizedDict`: `Fintype.card (SizedDict U V n) =
  U.choose n * V ^ n`.
* `Cslib.DataStructure.Dictionary.CellProbe.validHistory_of_mem_support_insertQueryDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.validHistory_of_mem_support_insertDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.not_isQuery_of_mem_support_insertDeleteDist`:
  admissibility, lengths (`4 * n` and `3 * n`), and absence of queries in `insertDeleteDist`.
* `Cslib.DataStructure.Dictionary.CellProbe.map_run_take_insertQueryDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.map_run_take_insertDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.map_extractKeySetVals_insertQueryDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.map_extractKeySetVals_insertDeleteDist`: exact uniform
  marginal distribution after `n` initial insertions and `t ≤ n` complete meta-operations.
* `Cslib.DataStructure.Dictionary.CellProbe.decodeDict_runSeq_eq`,
  `Cslib.DataStructure.Dictionary.CellProbe.step_query_eq_none_of_notMem_dom`,
  `Cslib.DataStructure.Dictionary.CellProbe.exists_det_indexedScheme_insertQueryDeleteDist`,
  `Cslib.DataStructure.Dictionary.CellProbe.exists_det_indexedScheme_insertDeleteDist`: parallel
  state decoding, out-of-domain query rejection, and all-history zero-error Yao specializations.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 3, 7, and 8 (`arXiv:2306.02253v3`).
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapters 11 and 17][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.Probability
open scoped ENNReal

instance instInhabitedDynamicOpResult {U : ℕ} (o : Dynamic.Op U) :
    Inhabited (Dynamic.Op.Result o) := by
  cases o <;> dsimp [Dynamic.Op.Result] <;> infer_instance

/-! ### Finite alphabet of value-bounded dynamic dictionary operations -/

private def queryOps (U : ℕ) : Finset (Dynamic.Op U) :=
  Finset.univ.image Dynamic.Op.query

private def deleteOps (U : ℕ) : Finset (Dynamic.Op U) :=
  Finset.univ.image Dynamic.Op.delete

private def insertOps (U V : ℕ) : Finset (Dynamic.Op U) :=
  (Finset.univ ×ˢ Finset.range V).image fun p : Fin U × ℕ => Dynamic.Op.insert p.1 p.2

/-- Finite operation alphabet of all `.query u`, `.delete u`, and `.insert u v` with `u : Fin U`
and `v < V` (size `2 * U + U * V`). -/
def validOps (U V : ℕ) : Finset (Dynamic.Op U) :=
  queryOps U ∪ deleteOps U ∪ insertOps U V

@[simp]
theorem query_mem_validOps (U V : ℕ) (u : Fin U) : .query u ∈ validOps U V := by
  simp [validOps, queryOps]

@[simp]
theorem delete_mem_validOps (U V : ℕ) (u : Fin U) : .delete u ∈ validOps U V := by
  simp [validOps, deleteOps]

@[simp]
theorem insert_mem_validOps_iff {U V : ℕ} {u : Fin U} {v : ℕ} :
    .insert u v ∈ validOps U V ↔ v < V := by
  simp [validOps, queryOps, deleteOps, insertOps]

/-- Membership characterization for `validOps U V`. -/
theorem mem_validOps_iff {U V : ℕ} {o : Dynamic.Op U} :
    o ∈ validOps U V ↔
      (∃ u, o = .query u) ∨ (∃ u, o = .delete u) ∨ (∃ u v, v < V ∧ o = .insert u v) := by
  cases o with
  | query u => simp
  | delete u => simp
  | insert u v =>
    simp only [insert_mem_validOps_iff, reduceCtorEq, exists_false, Dynamic.Op.insert.injEq,
      false_or]
    exact ⟨fun hv => ⟨u, v, hv, rfl, rfl⟩,
      fun ⟨_, _, hv, rfl, rfl⟩ => hv⟩

/-- `validOps U V` contains `2 * U + U * V` distinct operations. -/
theorem card_validOps (U V : ℕ) : (validOps U V).card = 2 * U + U * V := by
  have hdisj₁ : Disjoint (queryOps U) (deleteOps U) := by
    rw [Finset.disjoint_left]
    rintro _ hq hd
    simp only [queryOps, Finset.mem_image, Finset.mem_univ, true_and] at hq
    simp only [deleteOps, Finset.mem_image, Finset.mem_univ, true_and] at hd
    obtain ⟨_, rfl⟩ := hq
    obtain ⟨_, h⟩ := hd
    cases h
  have hdisj₂ : Disjoint (queryOps U ∪ deleteOps U) (insertOps U V) := by
    rw [Finset.disjoint_left]
    rintro _ hqd hins
    simp only [insertOps, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Prod.exists] at hins
    obtain ⟨_, _, _, rfl⟩ := hins
    simp only [Finset.mem_union, queryOps, deleteOps, Finset.mem_image, Finset.mem_univ,
      true_and] at hqd
    rcases hqd with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  have hcard_q : (queryOps U).card = U := by
    rw [queryOps, Finset.card_image_of_injective _ (fun _ _ h => by injection h)]
    simp
  have hcard_d : (deleteOps U).card = U := by
    rw [deleteOps, Finset.card_image_of_injective _ (fun _ _ h => by injection h)]
    simp
  have hcard_i : (insertOps U V).card = U * V := by
    rw [insertOps, Finset.card_image_of_injective _ (fun p₁ p₂ h => by
      cases p₁; cases p₂; injection h with h₁ h₂; subst h₁ h₂; rfl)]
    simp
  rw [validOps, Finset.card_union_of_disjoint hdisj₂, Finset.card_union_of_disjoint hdisj₁,
    hcard_q, hcard_d, hcard_i]
  ring

/-- Every operation admissible under `Dynamic.spec U V n_max` from any state `s` belongs to
`validOps U V`. -/
theorem mem_validOps_of_valid {U V n_max : ℕ} {s : Dictionary.State U} {o : Dynamic.Op U}
    (hv : (Dynamic.spec U V n_max).valid s o) : o ∈ validOps U V := by
  cases o with
  | query u => exact query_mem_validOps U V u
  | delete u => exact delete_mem_validOps U V u
  | insert u v => exact insert_mem_validOps_iff.mpr hv.2

/-- Every operation along an admissible `Dynamic.spec U V n_max` history belongs to
`validOps U V`. -/
theorem forall_mem_validOps_of_validHistory {U V n_max : ℕ} {s : Dictionary.State U}
    {ops : List (Dynamic.Op U)} (hvh : (Dynamic.spec U V n_max).ValidHistory s ops) :
    ∀ o ∈ ops, o ∈ validOps U V := by
  induction ops generalizing s with
  | nil => intro _ h; cases h
  | cons o rest ih =>
    intro o' ho'
    rcases List.mem_cons.mp ho' with rfl | hmem
    · exact mem_validOps_of_valid hvh.1
    · exact ih hvh.2 o' hmem

/-! ### Finite subtype of size-`n`, `V`-bounded dictionary states -/

/-- Subtype of `Dictionary.State U` storing `n` keys with all values strictly below `V`. -/
abbrev SizedDict (U V n : ℕ) : Type :=
  { s : Dictionary.State U // (Dictionary.dom s).card = n ∧ Dictionary.ValuesBounded V s }

/-- Reconstruct a `Dictionary.State U` from a size-`n` key set `K` and a value vector
`vals : Fin n → Fin V` indexed along the strictly increasing enumeration `K.1.orderEmbOfFin K.2`. -/
def dictOfKeySetVals {U V n : ℕ}
    (K : { K : Finset (Fin U) // K.card = n }) (vals : Fin n → Fin V) :
    Dictionary.State U :=
  fun u =>
    if hu : u ∈ K.1 then
      some (vals ((K.1.orderIsoOfFin K.2).symm ⟨u, hu⟩)).1
    else
      none

@[simp]
theorem dom_dictOfKeySetVals {U V n : ℕ}
    (K : { K : Finset (Fin U) // K.card = n }) (vals : Fin n → Fin V) :
    Dictionary.dom (dictOfKeySetVals K vals) = K.1 := by
  ext u
  by_cases hu : u ∈ K.1 <;> simp [Dictionary.dom, dictOfKeySetVals, hu]

theorem valuesBounded_dictOfKeySetVals {U V n : ℕ}
    (K : { K : Finset (Fin U) // K.card = n }) (vals : Fin n → Fin V) :
    Dictionary.ValuesBounded V (dictOfKeySetVals K vals) := by
  intro u w hw
  by_cases hu : u ∈ K.1
  · simp only [dictOfKeySetVals, hu, ↓reduceDIte, Option.some.injEq] at hw
    subst hw
    exact (vals _).2
  · simp [dictOfKeySetVals, hu] at hw

@[simp]
theorem dictOfKeySetVals_orderEmbOfFin {U V n : ℕ}
    (K : { K : Finset (Fin U) // K.card = n }) (vals : Fin n → Fin V) (i : Fin n) :
    dictOfKeySetVals K vals (K.1.orderEmbOfFin K.2 i) = some (vals i).1 := by
  have hu : K.1.orderEmbOfFin K.2 i ∈ K.1 := K.1.orderEmbOfFin_mem K.2 i
  simp only [dictOfKeySetVals, hu, ↓reduceDIte, Option.some.injEq]
  have hiso : (K.1.orderIsoOfFin K.2).symm ⟨K.1.orderEmbOfFin K.2 i, hu⟩ = i :=
    (OrderIso.symm_apply_eq (K.1.orderIsoOfFin K.2)).mpr (Subtype.ext rfl)
  rw [hiso]

/-- Canonical bijection between size-`n`, `V`-bounded dictionary states (`SizedDict U V n`) and
pairs `(K, vals)` consisting of a size-`n` key subset `K ⊆ Fin U` and its ordered value vector
`vals : Fin n → Fin V`. -/
def sizedDictEquiv (U V n : ℕ) :
    SizedDict U V n ≃ { K : Finset (Fin U) // K.card = n } × (Fin n → Fin V) where
  toFun s :=
    (⟨Dictionary.dom s.1, s.2.1⟩,
     fun i =>
       let u := (Dictionary.dom s.1).orderEmbOfFin s.2.1 i
       have his : (s.1 u).isSome :=
         Dictionary.mem_dom_iff_isSome.mp ((Dictionary.dom s.1).orderEmbOfFin_mem s.2.1 i)
       ⟨(s.1 u).get his, s.2.2 u ((s.1 u).get his) (Option.some_get his).symm⟩)
  invFun kv :=
    ⟨dictOfKeySetVals kv.1 kv.2,
     (congrArg Finset.card (dom_dictOfKeySetVals kv.1 kv.2)).trans kv.1.2,
     valuesBounded_dictOfKeySetVals kv.1 kv.2⟩
  left_inv := fun ⟨s, hcard, hval⟩ => by
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ Dictionary.dom s
    · simp only [dictOfKeySetVals, hu, ↓reduceDIte]
      set i := ((Dictionary.dom s).orderIsoOfFin hcard).symm ⟨u, hu⟩
      have hui : (Dictionary.dom s).orderEmbOfFin hcard i = u :=
        congrArg Subtype.val (((Dictionary.dom s).orderIsoOfFin hcard).apply_symm_apply ⟨u, hu⟩)
      simp only [hui]
      exact Option.some_get (Dictionary.mem_dom_iff_isSome.mp hu)
    · simp only [dictOfKeySetVals, hu, ↓reduceDIte]
      exact (Dictionary.notMem_dom_iff.mp hu).symm
  right_inv := fun ⟨K, vals⟩ => by
    have hdom : Dictionary.dom (dictOfKeySetVals K vals) = K.1 := dom_dictOfKeySetVals K vals
    refine Prod.ext (Subtype.ext hdom) (funext fun i => Fin.ext ?_)
    have hemb :
        ∀ (D : Finset (Fin U)) (hD : D = K.1) (hc : D.card = n),
          D.orderEmbOfFin hc i = K.1.orderEmbOfFin K.2 i := by
      rintro _ rfl hc
      rfl
    dsimp only
    simp only [hemb (Dictionary.dom (dictOfKeySetVals K vals)) hdom _,
      dictOfKeySetVals_orderEmbOfFin, Option.get_some]

instance instFintypeSizedDict (U V n : ℕ) : Fintype (SizedDict U V n) :=
  Fintype.ofEquiv _ (sizedDictEquiv U V n).symm

instance instDecidableEqSizedDict (U V n : ℕ) : DecidableEq (SizedDict U V n) :=
  Equiv.decidableEq (sizedDictEquiv U V n)

/-- There are `U.choose n * V ^ n` valid size-`n`, `V`-bounded dictionaries over `Fin U`. -/
theorem card_sizedDict (U V n : ℕ) :
    Fintype.card (SizedDict U V n) = U.choose n * V ^ n := by
  rw [Fintype.card_congr (sizedDictEquiv U V n), Fintype.card_prod, Fintype.card_finset_len,
    Fintype.card_fun]
  simp only [Fintype.card_fin]

/-- `SizedDict U V n` is nonempty whenever `n ≤ U` and `1 ≤ V`. -/
theorem nonempty_sizedDict {U V n : ℕ} (hU : n ≤ U) (hV : 1 ≤ V) :
    Nonempty (SizedDict U V n) :=
  ⟨(sizedDictEquiv U V n).symm
    (⟨Finset.univ.map (Fin.castLEEmb hU), by simp⟩, fun _ => ⟨0, hV⟩)⟩

/-- Total projection extracting the `(keySet, orderedVals)` pair in the finite type
`{ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)` from any `s : Dictionary.State U`
(agreeing with `sizedDictEquiv U V n` whenever `(dom s).card = n` and `ValuesBounded V s`). -/
noncomputable def extractKeySetVals {U V n : ℕ} (hU : n ≤ U) (hV : 1 ≤ V)
    (s : Dictionary.State U) :
    { K : Finset (Fin U) // K.card = n } × (Fin n → Fin V) :=
  open Classical in
  if hs : (Dictionary.dom s).card = n ∧ Dictionary.ValuesBounded V s then
    sizedDictEquiv U V n ⟨s, hs⟩
  else
    (⟨Finset.univ.map (Fin.castLEEmb hU), by simp⟩, fun _ => ⟨0, hV⟩)

@[simp]
theorem extractKeySetVals_coe {U V n : ℕ} (hU : n ≤ U) (hV : 1 ≤ V) (s : SizedDict U V n) :
    extractKeySetVals hU hV s.1 = sizedDictEquiv U V n s := by
  simp [extractKeySetVals, s.2]

/-! ### Deterministic hard operational sequence builders and sliding-window state -/

/-- Prefix dictionary constructed by inserting the first `k` pairs `(f i, (v i).1)` into
`Dictionary.empty U`. -/
def dictOfPrefix {U V m : ℕ} (f : Fin m ↪ Fin U) (v : Fin m → Fin V) :
    (k : ℕ) → k ≤ m → Dictionary.State U
  | 0, _ => Dictionary.empty U
  | k + 1, hk =>
      Function.update (dictOfPrefix f v k (Nat.le_of_succ_le hk))
        (f ⟨k, hk⟩) (some (v ⟨k, hk⟩).1)

/-- Dictionary state mapping `f i ↦ some (v i).1` for `i : Fin n` and `none` elsewhere. -/
def dictOfEmb {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V) : Dictionary.State U :=
  dictOfPrefix f v n le_rfl

theorem dictOfPrefix_apply_lt {U V m : ℕ} (f : Fin m ↪ Fin U) (v : Fin m → Fin V)
    {k : ℕ} (hk : k ≤ m) {i : ℕ} (hi : i < k) :
    dictOfPrefix f v k hk (f ⟨i, hi.trans_le hk⟩) = some (v ⟨i, hi.trans_le hk⟩).1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hik : i = k
    · subst hik
      simp [dictOfPrefix]
    · have hlt : i < k := by omega
      have hne : f ⟨i, hi.trans_le hk⟩ ≠ f ⟨k, hk⟩ := fun heq =>
        hik (congrArg Fin.val (f.injective heq))
      simp only [dictOfPrefix, Function.update_of_ne hne]
      exact ih (Nat.le_of_succ_le hk) hlt

theorem dictOfPrefix_apply_eq_none {U V m : ℕ} (f : Fin m ↪ Fin U) (v : Fin m → Fin V)
    {k : ℕ} (hk : k ≤ m) {u : Fin U} (hu : ∀ (i : ℕ) (hi : i < k), f ⟨i, hi.trans_le hk⟩ ≠ u) :
    dictOfPrefix f v k hk u = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : u ≠ f ⟨k, hk⟩ := (hu k (Nat.lt_succ_self k)).symm
    simp only [dictOfPrefix, Function.update_of_ne hne]
    exact ih (Nat.le_of_succ_le hk) fun i hi => hu i (Nat.lt_succ_of_lt hi)

@[simp]
theorem dom_dictOfPrefix {U V m : ℕ} (f : Fin m ↪ Fin U) (v : Fin m → Fin V)
    (k : ℕ) (hk : k ≤ m) :
    Dictionary.dom (dictOfPrefix f v k hk) =
      (Finset.range k).attach.map
        ⟨fun i => f ⟨i.1, (Finset.mem_range.mp i.2).trans_le hk⟩,
         fun _ _ h => Subtype.ext (congrArg Fin.val (f.injective h))⟩ := by
  induction k with
  | zero => simp [dictOfPrefix]
  | succ k ih =>
    simp only [dictOfPrefix, Dictionary.dom_insert, ih (Nat.le_of_succ_le hk)]
    ext u
    simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      Finset.mem_range]
    constructor
    · rintro (rfl | ⟨i, hik, rfl⟩)
      · exact ⟨k, Nat.lt_succ_self k, rfl⟩
      · exact ⟨i, Nat.lt_succ_of_lt hik, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases hik : i = k
      · subst hik; exact Or.inl rfl
      · exact Or.inr ⟨i, by omega, rfl⟩

theorem card_dom_dictOfPrefix {U V m : ℕ} (f : Fin m ↪ Fin U) (v : Fin m → Fin V)
    (k : ℕ) (hk : k ≤ m) :
    (Dictionary.dom (dictOfPrefix f v k hk)).card = k := by
  rw [dom_dictOfPrefix, Finset.card_map, Finset.card_attach, Finset.card_range]

@[simp]
theorem dictOfEmb_apply_self {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V) (i : Fin n) :
    dictOfEmb f v (f i) = some (v i).1 :=
  dictOfPrefix_apply_lt f v le_rfl i.2

theorem dictOfEmb_apply_eq_none {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V)
    {u : Fin U} (hu : ∀ i : Fin n, f i ≠ u) :
    dictOfEmb f v u = none :=
  dictOfPrefix_apply_eq_none f v le_rfl fun i hi => hu ⟨i, hi⟩

@[simp]
theorem dom_dictOfEmb {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V) :
    Dictionary.dom (dictOfEmb f v) = Finset.univ.map f := by
  ext u
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := Dictionary.mem_dom_iff.mp hu
    by_contra hnot
    simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] at hnot
    rw [dictOfEmb_apply_eq_none f v hnot] at hw
    cases hw
  · simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rintro ⟨i, rfl⟩
    simp

theorem card_dom_dictOfEmb {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V) :
    (Dictionary.dom (dictOfEmb f v)).card = n := by
  simp

theorem valuesBounded_dictOfEmb {U V n : ℕ} (f : Fin n ↪ Fin U) (v : Fin n → Fin V) :
    Dictionary.ValuesBounded V (dictOfEmb f v) := by
  intro u w hw
  have hu : u ∈ Dictionary.dom (dictOfEmb f v) := Dictionary.mem_dom_iff.mpr ⟨w, hw⟩
  rw [dom_dictOfEmb, Finset.mem_map] at hu
  obtain ⟨i, _, rfl⟩ := hu
  rw [dictOfEmb_apply_self, Option.some.injEq] at hw
  subst hw
  exact (v i).2

/-- Active size-`n` key embedding `[t, t + n)` inside `keys : Fin (2 * n) ↪ Fin U` after `t ≤ n`
meta-operations. -/
def windowEmb {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (t : ℕ) (ht : t ≤ n) : Fin n ↪ Fin U where
  toFun k := keys ⟨t + k.1, by omega⟩
  inj' a b h := Fin.ext (by
    have := congrArg Fin.val (keys.injective h)
    dsimp only at this
    omega)

@[simp]
theorem windowEmb_apply {U n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (t : ℕ) (ht : t ≤ n) (k : Fin n) :
    windowEmb keys t ht k = keys ⟨t + k.1, by omega⟩ := by rfl

/-- Active size-`n` value slice `[t, t + n)` inside `vals : Fin (2 * n) → Fin V` after `t ≤ n`
meta-operations. -/
def windowVals {V n : ℕ} (vals : Fin (2 * n) → Fin V) (t : ℕ) (ht : t ≤ n) : Fin n → Fin V :=
  fun k => vals ⟨t + k.1, by omega⟩

@[simp]
theorem windowVals_apply {V n : ℕ} (vals : Fin (2 * n) → Fin V) (t : ℕ) (ht : t ≤ n)
    (k : Fin n) :
    windowVals vals t ht k = vals ⟨t + k.1, by omega⟩ := by rfl

/-- Dictionary state reached after the `n` initial insertions and `t ≤ n` meta-operations. -/
def windowDict {U V n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V)
    (t : ℕ) (ht : t ≤ n) : SizedDict U V n :=
  ⟨dictOfEmb (windowEmb keys t ht) (windowVals vals t ht),
   card_dom_dictOfEmb _ _,
   valuesBounded_dictOfEmb _ _⟩

@[simp]
theorem windowDict_coe {U V n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V)
    (t : ℕ) (ht : t ≤ n) :
    (windowDict keys vals t ht).1 = dictOfEmb (windowEmb keys t ht) (windowVals vals t ht) := by
  rfl

/-- Initial phase of `n` key-value insertions `keys 0, …, keys (n - 1)`. -/
def initInsertSeq {U V n : ℕ} (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    List (Dynamic.Op U) :=
  (List.finRange n).map fun i =>
    .insert (keys ⟨i.1, by omega⟩) (vals ⟨i.1, by omega⟩).1

/-- Single three-step `[query, delete, insert]` meta-operation `j : Fin n` from `Distribution 1`
([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12). -/
def queryDeleteInsertMetaOp {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) (j : Fin n) :
    List (Dynamic.Op U) :=
  [.query (keys ⟨j.1, by omega⟩),
   .delete (keys ⟨j.1, by omega⟩),
   .insert (keys ⟨n + j.1, by omega⟩) (vals ⟨n + j.1, by omega⟩).1]

/-- Single two-step `[delete, insert]` update-only meta-operation `j : Fin n`
([LiLiangYuZhou2023], Section 8, p. 28 / PDF p. 29). -/
def deleteInsertMetaOp {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) (j : Fin n) :
    List (Dynamic.Op U) :=
  [.delete (keys ⟨j.1, by omega⟩),
   .insert (keys ⟨n + j.1, by omega⟩) (vals ⟨n + j.1, by omega⟩).1]

/-- Full `4 * n`-operation sequence for `Distribution 1`: `n` initial insertions followed by `n`
`[query, delete, insert]` meta-operations. -/
def insertQueryDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    List (Dynamic.Op U) :=
  initInsertSeq keys vals ++ (List.finRange n).flatMap (queryDeleteInsertMetaOp keys vals)

/-- Full `3 * n`-operation update-only sequence: `n` initial insertions followed by `n`
`[delete, insert]` meta-operations (containing zero `.query` operations). -/
def insertDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    List (Dynamic.Op U) :=
  initInsertSeq keys vals ++ (List.finRange n).flatMap (deleteInsertMetaOp keys vals)

@[simp]
theorem length_initInsertSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (initInsertSeq keys vals).length = n := by
  simp [initInsertSeq]

private theorem length_flatMap_const {α β : Type*} (c : ℕ) (xs : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = c) :
    (xs.flatMap f).length = c * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, hf, ih, List.length_cons]
    ring

@[simp]
theorem length_insertQueryDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (insertQueryDeleteSeq keys vals).length = 4 * n := by
  rw [insertQueryDeleteSeq, List.length_append, length_initInsertSeq,
    length_flatMap_const 3 _ _ (fun _ => rfl), List.length_finRange]
  ring

@[simp]
theorem length_insertDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (insertDeleteSeq keys vals).length = 3 * n := by
  rw [insertDeleteSeq, List.length_append, length_initInsertSeq,
    length_flatMap_const 2 _ _ (fun _ => rfl), List.length_finRange]
  ring

/-- `insertDeleteSeq` issues zero `.query` operations. -/
theorem not_isQuery_of_mem_insertDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V)
    {o : Dynamic.Op U} (ho : o ∈ insertDeleteSeq keys vals) :
    ¬ ∃ u, o = .query u := by
  rw [insertDeleteSeq, List.mem_append] at ho
  rcases ho with hinit | hmeta
  · simp only [initInsertSeq, List.mem_map] at hinit
    obtain ⟨_, _, rfl⟩ := hinit
    rintro ⟨_, h⟩; cases h
  · simp only [List.mem_flatMap, deleteInsertMetaOp, List.mem_cons, List.not_mem_nil, or_false]
      at hmeta
    obtain ⟨_, _, rfl | rfl⟩ := hmeta <;> rintro ⟨_, h⟩ <;> cases h

/-! ### Admissibility and sliding-window state evolution -/

private theorem finRange_take_succ {n k : ℕ} (hk : k < n) :
    (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
  have hlen : k < (List.finRange n).length := by simpa using hk
  rw [List.take_add_one, List.getElem?_eq_getElem hlen, List.getElem_finRange]
  rfl

private theorem validHistory_run_initInsertSeq_take {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    ∀ {k : ℕ} (hk : k ≤ n),
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
        (((List.finRange n).take k).map fun i =>
          .insert (keys ⟨i.1, by omega⟩) (vals ⟨i.1, by omega⟩).1) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U)
        (((List.finRange n).take k).map fun i =>
          .insert (keys ⟨i.1, by omega⟩) (vals ⟨i.1, by omega⟩).1)).1 =
        dictOfPrefix (windowEmb keys 0 (Nat.zero_le n))
          (windowVals vals 0 (Nat.zero_le n)) k hk
  | 0, _ => by simp [dictOfPrefix]
  | k + 1, hk => by
    obtain ⟨hvh, hrun⟩ := validHistory_run_initInsertSeq_take keys vals (Nat.le_of_succ_le hk)
    rw [finRange_take_succ hk, List.map_append, List.map_cons, List.map_nil,
      StateTransitionSpec.validHistory_append, StateTransitionSpec.run_append, hrun]
    set s_k := dictOfPrefix (windowEmb keys 0 (Nat.zero_le n))
      (windowVals vals 0 (Nat.zero_le n)) k (Nat.le_of_succ_le hk)
    have hcard : (Dictionary.dom s_k).card < n := by
      rw [card_dom_dictOfPrefix]
      exact hk
    refine ⟨⟨hvh, ⟨Or.inl hcard, (vals ⟨k, by omega⟩).2⟩, trivial⟩, ?_⟩
    change Function.update s_k (keys ⟨k, by omega⟩) (some (vals ⟨k, by omega⟩).1) =
      Function.update s_k (windowEmb keys 0 (Nat.zero_le n) ⟨k, hk⟩)
        (some (windowVals vals 0 (Nat.zero_le n) ⟨k, hk⟩).1)
    have hidx : (⟨0 + k, by omega⟩ : Fin (2 * n)) = ⟨k, by omega⟩ :=
      Fin.ext (Nat.zero_add k)
    simp only [windowEmb_apply, windowVals_apply, hidx]

theorem validHistory_initInsertSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) (initInsertSeq keys vals) := by
  have htake : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  simpa only [initInsertSeq, htake] using
    (validHistory_run_initInsertSeq_take keys vals le_rfl).1

theorem run_initInsertSeq_fst {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    ((Dynamic.spec U V n).run (Dictionary.empty U) (initInsertSeq keys vals)).1 =
      (windowDict keys vals 0 (Nat.zero_le n)).1 := by
  have htake : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  simpa only [initInsertSeq, htake, windowDict, dictOfEmb] using
    (validHistory_run_initInsertSeq_take keys vals le_rfl).2

private theorem step_windowDict_deleteInsertMetaOp {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) {j : ℕ} (hj : j < n) :
    (Dynamic.spec U V n).ValidHistory (windowDict keys vals j hj.le).1
      (deleteInsertMetaOp keys vals ⟨j, hj⟩) ∧
    ((Dynamic.spec U V n).run (windowDict keys vals j hj.le).1
      (deleteInsertMetaOp keys vals ⟨j, hj⟩)).1 =
      (windowDict keys vals (j + 1) hj).1 := by
  set s_j := (windowDict keys vals j hj.le).1
  have hn_pos : 0 < n := by omega
  have heq₀ : windowEmb keys j hj.le ⟨0, hn_pos⟩ = keys ⟨j, by omega⟩ := by
    simp only [windowEmb_apply]
    exact congrArg keys (Fin.ext (Nat.add_zero j))
  have hs_j_at : s_j (keys ⟨j, by omega⟩) = some (vals ⟨j, by omega⟩).1 := by
    rw [← heq₀]
    exact (dictOfEmb_apply_self (windowEmb keys j hj.le) (windowVals vals j hj.le)
      ⟨0, hn_pos⟩).trans (congrArg (fun idx => some (vals idx).1) (Fin.ext (Nat.add_zero j)))
  have hisSome : (s_j (keys ⟨j, by omega⟩)).isSome := by
    rw [hs_j_at]; rfl
  have hcard_del :
      (Dictionary.dom (Function.update s_j (keys ⟨j, by omega⟩) none)).card < n := by
    rw [Dynamic.card_dom_delete_eq_of_isSome hisSome, (windowDict keys vals j hj.le).2.1]
    omega
  refine ⟨⟨trivial, ⟨Or.inl hcard_del, (vals ⟨n + j, by omega⟩).2⟩, trivial⟩, ?_⟩
  change Function.update (Function.update s_j (keys ⟨j, by omega⟩) none)
      (keys ⟨n + j, by omega⟩) (some (vals ⟨n + j, by omega⟩).1) =
    dictOfEmb (windowEmb keys (j + 1) hj) (windowVals vals (j + 1) hj)
  funext u
  by_cases hex : ∃ k : Fin n, windowEmb keys (j + 1) hj k = u
  · obtain ⟨k, rfl⟩ := hex
    rw [dictOfEmb_apply_self]
    by_cases hlast : k.1 = n - 1
    · have hidx : (⟨j + 1 + k.1, by omega⟩ : Fin (2 * n)) = ⟨n + j, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      simp only [windowEmb_apply, windowVals_apply, hidx, Function.update_self]
    · have hk_lt : k.1 + 1 < n := by omega
      have hne_ins : keys ⟨j + 1 + k.1, by omega⟩ ≠ keys ⟨n + j, by omega⟩ := fun heq => by
        have := congrArg Fin.val (keys.injective heq); dsimp only at this; omega
      have hne_del : keys ⟨j + 1 + k.1, by omega⟩ ≠ keys ⟨j, by omega⟩ := fun heq => by
        have := congrArg Fin.val (keys.injective heq); dsimp only at this; omega
      simp only [windowEmb_apply, windowVals_apply,
        Function.update_of_ne hne_ins, Function.update_of_ne hne_del]
      have hshift : (⟨j + 1 + k.1, by omega⟩ : Fin (2 * n)) = ⟨j + (k.1 + 1), by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [hshift]
      exact dictOfEmb_apply_self (windowEmb keys j hj.le) (windowVals vals j hj.le)
        ⟨k.1 + 1, hk_lt⟩
  · push Not at hex
    rw [dictOfEmb_apply_eq_none _ _ hex]
    have hne_ins : u ≠ keys ⟨n + j, by omega⟩ := by
      intro rfl
      refine hex ⟨n - 1, by omega⟩ ?_
      rw [windowEmb_apply]
      exact congrArg keys (Fin.ext (by dsimp only; omega))
    rw [Function.update_of_ne hne_ins]
    by_cases hudel : u = keys ⟨j, by omega⟩
    · subst hudel; simp
    · rw [Function.update_of_ne hudel]
      refine dictOfEmb_apply_eq_none (windowEmb keys j hj.le) (windowVals vals j hj.le) ?_
      intro k'
      by_cases hk0 : k'.1 = 0
      · rw [windowEmb_apply]
        intro heq
        refine hudel ?_
        rw [← heq]
        exact congrArg keys (Fin.ext (by dsimp only; omega))
      · have hprev : k'.1 - 1 < n := by omega
        intro heq
        refine hex ⟨k'.1 - 1, hprev⟩ ?_
        rw [← heq, windowEmb_apply, windowEmb_apply]
        exact congrArg keys (Fin.ext (by dsimp only; omega))

private theorem step_windowDict_queryDeleteInsertMetaOp {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) {j : ℕ} (hj : j < n) :
    (Dynamic.spec U V n).ValidHistory (windowDict keys vals j hj.le).1
      (queryDeleteInsertMetaOp keys vals ⟨j, hj⟩) ∧
    ((Dynamic.spec U V n).run (windowDict keys vals j hj.le).1
      (queryDeleteInsertMetaOp keys vals ⟨j, hj⟩)).1 =
      (windowDict keys vals (j + 1) hj).1 := by
  have h := step_windowDict_deleteInsertMetaOp (V := V) keys vals hj
  exact ⟨⟨trivial, h.1⟩, h.2⟩

private theorem take_mul_flatMap {α β : Type*} (c : ℕ) (xs : List α) (f : α → List β)
    (hf : ∀ x, (f x).length = c) :
    ∀ t : ℕ, (xs.flatMap f).take (c * t) = (xs.take t).flatMap f := by
  induction xs with
  | nil => intro t; simp
  | cons x rest ih =>
    intro t
    cases t with
    | zero => simp
    | succ t =>
      have hmul : c * (t + 1) = (f x).length + c * t := by rw [hf x]; ring
      rw [List.flatMap_cons, hmul, List.take_append,
        List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        ih t, List.take_succ_cons, List.flatMap_cons]

private theorem validHistory_run_metaPrefix {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V)
    (metaOp : Fin n → List (Dynamic.Op U))
    (hstep : ∀ {j : ℕ} (hj : j < n),
      (Dynamic.spec U V n).ValidHistory (windowDict keys vals j hj.le).1 (metaOp ⟨j, hj⟩) ∧
      ((Dynamic.spec U V n).run (windowDict keys vals j hj.le).1 (metaOp ⟨j, hj⟩)).1 =
        (windowDict keys vals (j + 1) hj).1) :
    ∀ {t : ℕ} (ht : t ≤ n),
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
        (initInsertSeq keys vals ++ ((List.finRange n).take t).flatMap metaOp) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U)
        (initInsertSeq keys vals ++ ((List.finRange n).take t).flatMap metaOp)).1 =
        (windowDict keys vals t ht).1
  | 0, _ => by
    simp only [List.take_zero, List.flatMap_nil, List.append_nil]
    exact ⟨validHistory_initInsertSeq keys vals, run_initInsertSeq_fst keys vals⟩
  | t + 1, ht => by
    obtain ⟨hvh, hrun⟩ := validHistory_run_metaPrefix keys vals metaOp hstep
      (Nat.le_of_succ_le ht)
    set pref := initInsertSeq keys vals ++ ((List.finRange n).take t).flatMap metaOp
    have hconcat :
        initInsertSeq keys vals ++ ((List.finRange n).take (t + 1)).flatMap metaOp =
          pref ++ metaOp ⟨t, ht⟩ := by
      rw [finRange_take_succ ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
    rw [hconcat, StateTransitionSpec.validHistory_append,
      (Dynamic.spec U V n).run_append (Dictionary.empty U) pref (metaOp ⟨t, ht⟩), hrun]
    obtain ⟨hvh_step, hrun_step⟩ := hstep ht
    exact ⟨⟨hvh, hvh_step⟩, hrun_step⟩

theorem take_insertQueryDeleteSeq {U V n t : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (insertQueryDeleteSeq keys vals).take (n + 3 * t) =
      initInsertSeq keys vals ++
        ((List.finRange n).take t).flatMap (queryDeleteInsertMetaOp keys vals) := by
  have hlen : n + 3 * t = (initInsertSeq keys vals).length + 3 * t := by simp
  rw [insertQueryDeleteSeq, hlen, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    take_mul_flatMap 3 _ _ (fun _ => rfl) t]

theorem take_insertDeleteSeq {U V n t : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (insertDeleteSeq keys vals).take (n + 2 * t) =
      initInsertSeq keys vals ++
        ((List.finRange n).take t).flatMap (deleteInsertMetaOp keys vals) := by
  have hlen : n + 2 * t = (initInsertSeq keys vals).length + 2 * t := by simp
  rw [insertDeleteSeq, hlen, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    take_mul_flatMap 2 _ _ (fun _ => rfl) t]

/-- Every `insertQueryDeleteSeq` is an admissible history for `Dynamic.spec U V n`. -/
theorem validHistory_insertQueryDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
      (insertQueryDeleteSeq keys vals) := by
  have h := (validHistory_run_metaPrefix keys vals (queryDeleteInsertMetaOp keys vals)
    (fun hj => step_windowDict_queryDeleteInsertMetaOp keys vals hj) le_rfl).1
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  rwa [htake] at h

/-- Every `insertDeleteSeq` is an admissible history for `Dynamic.spec U V n`. -/
theorem validHistory_insertDeleteSeq {U V n : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
      (insertDeleteSeq keys vals) := by
  have h := (validHistory_run_metaPrefix keys vals (deleteInsertMetaOp keys vals)
    (fun hj => step_windowDict_deleteInsertMetaOp keys vals hj) le_rfl).1
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  rwa [htake] at h

/-- Prefix admissibility and exact state `windowDict keys vals t ht` after `n` initial insertions
and `t ≤ n` complete meta-operations of `insertQueryDeleteSeq`. -/
theorem validHistory_and_run_take_insertQueryDeleteSeq {U V n t : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) (ht : t ≤ n) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
      ((insertQueryDeleteSeq keys vals).take (n + 3 * t)) ∧
    ((Dynamic.spec U V n).run (Dictionary.empty U)
      ((insertQueryDeleteSeq keys vals).take (n + 3 * t))).1 =
      (windowDict keys vals t ht).1 := by
  rw [take_insertQueryDeleteSeq]
  exact validHistory_run_metaPrefix keys vals (queryDeleteInsertMetaOp keys vals)
    (fun hj => step_windowDict_queryDeleteInsertMetaOp keys vals hj) ht

/-- Prefix admissibility and exact state `windowDict keys vals t ht` after `n` initial insertions
and `t ≤ n` complete meta-operations of `insertDeleteSeq`. -/
theorem validHistory_and_run_take_insertDeleteSeq {U V n t : ℕ}
    (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) (ht : t ≤ n) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
      ((insertDeleteSeq keys vals).take (n + 2 * t)) ∧
    ((Dynamic.spec U V n).run (Dictionary.empty U)
      ((insertDeleteSeq keys vals).take (n + 2 * t))).1 =
      (windowDict keys vals t ht).1 := by
  rw [take_insertDeleteSeq]
  exact validHistory_run_metaPrefix keys vals (deleteInsertMetaOp keys vals)
    (fun hj => step_windowDict_deleteInsertMetaOp keys vals hj) ht

/-! ### Hard operational distributions and uniform size-`n` state marginals -/

/-- `Distribution 1` of [LiLiangYuZhou2023], Section 3, p. 11 (PDF p. 12), extended with
independent uniform values in `Fin V` (Section 7, Definition 7.1, p. 25 / PDF p. 26 and Section 8,
p. 28 / PDF p. 29): samples `keys : Fin (2 * n) ↪ Fin U` and `vals : Fin (2 * n) → Fin V`
independently and uniformly, then emits `insertQueryDeleteSeq keys vals` (`4 * n` operations). -/
noncomputable def insertQueryDeleteDist (U V n : ℕ) (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    PMF (List (Dynamic.Op U)) :=
  letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  do
    let keys ← PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)
    let vals ← PMF.uniformOfFintype (Fin (2 * n) → Fin V)
    return insertQueryDeleteSeq keys vals

/-- Update-only hard distribution of [LiLiangYuZhou2023], Section 8, proof of Theorem 1.3, p. 28
(PDF p. 29): samples `keys : Fin (2 * n) ↪ Fin U` and `vals : Fin (2 * n) → Fin V` independently
and uniformly, then emits `insertDeleteSeq keys vals` (`3 * n` operations, zero `.query` calls). -/
noncomputable def insertDeleteDist (U V n : ℕ) (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    PMF (List (Dynamic.Op U)) :=
  letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  do
    let keys ← PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)
    let vals ← PMF.uniformOfFintype (Fin (2 * n) → Fin V)
    return insertDeleteSeq keys vals

theorem insertQueryDeleteDist_eq_uniformOfFintype_map {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    insertQueryDeleteDist U V n hU hV =
      (PMF.uniformOfFintype ((Fin (2 * n) ↪ Fin U) × (Fin (2 * n) → Fin V))).map
        (fun p => insertQueryDeleteSeq p.1 p.2) := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  simpa only [insertQueryDeleteDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    ← _root_.PMF.bind_pure_comp, Function.comp_def] using
    PMF.uniformOfFintype_bind_map (fun keys vals => insertQueryDeleteSeq keys vals)

theorem insertDeleteDist_eq_uniformOfFintype_map {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    insertDeleteDist U V n hU hV =
      (PMF.uniformOfFintype ((Fin (2 * n) ↪ Fin U) × (Fin (2 * n) → Fin V))).map
        (fun p => insertDeleteSeq p.1 p.2) := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  simpa only [insertDeleteDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    ← _root_.PMF.bind_pure_comp, Function.comp_def] using
    PMF.uniformOfFintype_bind_map (fun keys vals => insertDeleteSeq keys vals)

theorem mem_support_insertQueryDeleteDist_iff {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {ops : List (Dynamic.Op U)} :
    ops ∈ (insertQueryDeleteDist U V n hU hV).support ↔
      ∃ (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V),
        insertQueryDeleteSeq keys vals = ops := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  rw [insertQueryDeleteDist_eq_uniformOfFintype_map hU hV, _root_.PMF.mem_support_map_iff]
  simp only [PMF.mem_support_uniformOfFintype, true_and, Prod.exists]

theorem mem_support_insertDeleteDist_iff {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {ops : List (Dynamic.Op U)} :
    ops ∈ (insertDeleteDist U V n hU hV).support ↔
      ∃ (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V),
        insertDeleteSeq keys vals = ops := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  rw [insertDeleteDist_eq_uniformOfFintype_map hU hV, _root_.PMF.mem_support_map_iff]
  simp only [PMF.mem_support_uniformOfFintype, true_and, Prod.exists]

/-- Every sequence in `(insertQueryDeleteDist U V n hU hV).support` has length `4 * n`. -/
theorem length_of_mem_support_insertQueryDeleteDist {U V n : ℕ} {hU : 2 * n ≤ U} {hV : 1 ≤ V}
    {ops : List (Dynamic.Op U)} (hops : ops ∈ (insertQueryDeleteDist U V n hU hV).support) :
    ops.length = 4 * n := by
  obtain ⟨keys, vals, rfl⟩ := (mem_support_insertQueryDeleteDist_iff hU hV).mp hops
  exact length_insertQueryDeleteSeq keys vals

/-- Every sequence in `(insertDeleteDist U V n hU hV).support` has length `3 * n`. -/
theorem length_of_mem_support_insertDeleteDist {U V n : ℕ} {hU : 2 * n ≤ U} {hV : 1 ≤ V}
    {ops : List (Dynamic.Op U)} (hops : ops ∈ (insertDeleteDist U V n hU hV).support) :
    ops.length = 3 * n := by
  obtain ⟨keys, vals, rfl⟩ := (mem_support_insertDeleteDist_iff hU hV).mp hops
  exact length_insertDeleteSeq keys vals

/-- Every sequence in `(insertDeleteDist U V n hU hV).support` issues zero `.query` operations. -/
theorem not_isQuery_of_mem_support_insertDeleteDist {U V n : ℕ} {hU : 2 * n ≤ U} {hV : 1 ≤ V}
    {ops : List (Dynamic.Op U)} (hops : ops ∈ (insertDeleteDist U V n hU hV).support)
    {o : Dynamic.Op U} (ho : o ∈ ops) :
    ¬ ∃ u, o = .query u := by
  obtain ⟨keys, vals, rfl⟩ := (mem_support_insertDeleteDist_iff hU hV).mp hops
  exact not_isQuery_of_mem_insertDeleteSeq keys vals ho

/-- Every sequence in `(insertQueryDeleteDist U V n hU hV).support` is an admissible history for
`Dynamic.spec U V n` from `Dictionary.empty U` and uses only operations in `validOps U V`. -/
theorem validHistory_of_mem_support_insertQueryDeleteDist {U V n : ℕ} {hU : 2 * n ≤ U}
    {hV : 1 ≤ V} {ops : List (Dynamic.Op U)}
    (hops : ops ∈ (insertQueryDeleteDist U V n hU hV).support) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops ∧
      ∀ o ∈ ops, o ∈ validOps U V := by
  obtain ⟨keys, vals, rfl⟩ := (mem_support_insertQueryDeleteDist_iff hU hV).mp hops
  have hvh := validHistory_insertQueryDeleteSeq (V := V) keys vals
  exact ⟨hvh, forall_mem_validOps_of_validHistory hvh⟩

/-- Every sequence in `(insertDeleteDist U V n hU hV).support` is an admissible history for
`Dynamic.spec U V n` from `Dictionary.empty U` and uses only operations in `validOps U V`. -/
theorem validHistory_of_mem_support_insertDeleteDist {U V n : ℕ} {hU : 2 * n ≤ U}
    {hV : 1 ≤ V} {ops : List (Dynamic.Op U)}
    (hops : ops ∈ (insertDeleteDist U V n hU hV).support) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops ∧
      ∀ o ∈ ops, o ∈ validOps U V := by
  obtain ⟨keys, vals, rfl⟩ := (mem_support_insertDeleteDist_iff hU hV).mp hops
  have hvh := validHistory_insertDeleteSeq (V := V) keys vals
  exact ⟨hvh, forall_mem_validOps_of_validHistory hvh⟩

private def splitWindow {n : ℕ} (t : ℕ) (ht : t ≤ n) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun
    | .inl k => ⟨t + k.1, by omega⟩
    | .inr r => if r.1 < t then ⟨r.1, by omega⟩ else ⟨r.1 + n, by omega⟩
  invFun m :=
    if hm1 : m.1 < t then .inr ⟨m.1, by omega⟩
    else if hm2 : m.1 < t + n then .inl ⟨m.1 - t, by omega⟩
    else .inr ⟨m.1 - n, by omega⟩
  left_inv x := by
    rcases x with k | r
    · dsimp only
      have h1 : ¬ t + k.1 < t := by omega
      have h2 : t + k.1 < t + n := by omega
      simp only [h1, ↓reduceDIte, h2]
      exact congrArg Sum.inl (Fin.ext (by dsimp only; omega))
    · by_cases hrt : r.1 < t
      · dsimp only; simp [hrt]
      · dsimp only
        have h1 : ¬ r.1 + n < t := by omega
        have h2 : ¬ r.1 + n < t + n := by omega
        simp only [hrt, ↓reduceIte, h1, ↓reduceDIte, h2]
        exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
  right_inv m := by
    by_cases h1 : m.1 < t
    · simp [h1]
    · by_cases h2 : m.1 < t + n
      · simp only [h1, ↓reduceDIte, h2]
        exact Fin.ext (by dsimp only; omega)
      · have h3 : ¬ m.1 - n < t := by omega
        simp only [h1, ↓reduceDIte, h2, h3, ↓reduceIte]
        exact Fin.ext (by dsimp only; omega)

private noncomputable def windowEmbEquiv {U n : ℕ} (t : ℕ) (ht : t ≤ n) :
    (Fin (2 * n) ↪ Fin U) ≃ (Fin n ↪ Fin U) × (Fin n ↪ Fin (U - n)) := by
  classical
  have hcard : ∀ f : Fin n ↪ Fin U, Fintype.card ↥(Set.range f)ᶜ = U - n := fun f => by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f.injective,
      Fintype.card_fin, Fintype.card_fin]
  exact ((Equiv.embeddingCongr (splitWindow t ht).symm (.refl (Fin U))).trans
    Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted).trans
    ((Equiv.sigmaCongrRight fun f =>
      Equiv.embeddingCongr (.refl (Fin n)) (Fintype.equivFinOfCardEq (hcard f))).trans
      (Equiv.sigmaEquivProd (Fin n ↪ Fin U) (Fin n ↪ Fin (U - n))))

private theorem windowEmbEquiv_fst {U n : ℕ} (t : ℕ) (ht : t ≤ n)
    (keys : Fin (2 * n) ↪ Fin U) :
    (windowEmbEquiv t ht keys).1 = windowEmb keys t ht :=
  Function.Embedding.ext fun _ => rfl

private def windowValsEquiv {V n : ℕ} (t : ℕ) (ht : t ≤ n) :
    (Fin (2 * n) → Fin V) ≃ (Fin n → Fin V) × (Fin n → Fin V) :=
  (Equiv.arrowCongr (splitWindow t ht).symm (.refl (Fin V))).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin n) (Fin V))

private theorem windowValsEquiv_fst {V n : ℕ} (t : ℕ) (ht : t ≤ n)
    (vals : Fin (2 * n) → Fin V) :
    (windowValsEquiv t ht vals).1 = windowVals vals t ht := by
  funext k
  change vals ((splitWindow t ht).symm.symm (.inl k)) = vals ⟨t + k.1, by omega⟩
  rfl

private noncomputable def embToPerm {U n : ℕ} (f : Fin n ↪ Fin U) : Equiv.Perm (Fin n) :=
  let K : Finset (Fin U) := Finset.univ.map f
  have hK : K.card = n := by simp [K]
  let g : Fin n → Fin n := fun i =>
    (K.orderIsoOfFin hK).symm ⟨f i, Finset.mem_map_of_mem f (Finset.mem_univ i)⟩
  have hinj : Function.Injective g := fun i j hij => by
    have hsub := (K.orderIsoOfFin hK).symm.injective hij
    exact f.injective (congrArg Subtype.val hsub)
  Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)

private noncomputable def embValsEquiv (U V n : ℕ) :
    ((Fin n ↪ Fin U) × (Fin n → Fin V)) ≃
      ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) × Equiv.Perm (Fin n) where
  toFun p :=
    let σ := embToPerm p.1
    ((⟨Finset.univ.map p.1, by simp⟩, p.2 ∘ σ.symm), σ)
  invFun q :=
    (q.2.toEmbedding.trans (q.1.1.1.orderEmbOfFin q.1.1.2).toEmbedding,
     q.1.2 ∘ q.2)
  left_inv := fun ⟨f, v⟩ => by
    set K : Finset (Fin U) := Finset.univ.map f
    have hK : K.card = n := by simp [K]
    set σ := embToPerm f
    have hσ_apply : ∀ i : Fin n, K.orderEmbOfFin hK (σ i) = f i := fun i => by
      have h1 : σ i = (K.orderIsoOfFin hK).symm
          ⟨f i, Finset.mem_map_of_mem f (Finset.mem_univ i)⟩ := rfl
      rw [h1]
      exact congrArg Subtype.val
        ((K.orderIsoOfFin hK).apply_symm_apply ⟨f i, Finset.mem_map_of_mem f (Finset.mem_univ i)⟩)
    refine Prod.ext (Function.Embedding.ext fun i => hσ_apply i) (funext fun i => ?_)
    dsimp only [Function.comp_apply]
    rw [σ.symm_apply_apply]
  right_inv := fun ⟨⟨K, v_sorted⟩, σ⟩ => by
    set f : Fin n ↪ Fin U := σ.toEmbedding.trans (K.1.orderEmbOfFin K.2).toEmbedding
    have hcard_f : (Finset.univ.map f).card = n := by simp
    have hmap : Finset.univ.map f = K.1 := by
      have hperm : (Finset.univ : Finset (Fin n)).map σ.toEmbedding = Finset.univ := by
        ext x; simp
      rw [← Finset.map_map, hperm, K.1.map_orderEmbOfFin_univ K.2]
    have hσ : embToPerm f = σ := by
      ext i
      have hval : (embToPerm f i : Fin n) = σ i := by
        change ((Finset.univ.map f).orderIsoOfFin hcard_f).symm
            ⟨f i, Finset.mem_map_of_mem f (Finset.mem_univ i)⟩ = σ i
        have helper : ∀ (D : Finset (Fin U)) (hD : D = K.1) (hc : D.card = n)
            (hmem : K.1.orderEmbOfFin K.2 (σ i) ∈ D),
            (D.orderIsoOfFin hc).symm ⟨K.1.orderEmbOfFin K.2 (σ i), hmem⟩ = σ i := by
          rintro _ rfl hc hmem
          have hsub : (⟨K.1.orderEmbOfFin K.2 (σ i), hmem⟩ : K.1) = K.1.orderIsoOfFin hc (σ i) :=
            Subtype.ext rfl
          rw [hsub]
          exact (K.1.orderIsoOfFin hc).symm_apply_apply (σ i)
        exact helper (Finset.univ.map f) hmap hcard_f (Finset.mem_map_of_mem f (Finset.mem_univ i))
      exact congrArg Fin.val hval
    refine Prod.ext (Prod.ext (Subtype.ext hmap) ?_) hσ
    funext k
    dsimp only [Function.comp_apply]
    rw [hσ, σ.apply_symm_apply]

private theorem sizedDictEquiv_symm_embValsEquiv_fst {U V n : ℕ}
    (f : Fin n ↪ Fin U) (v : Fin n → Fin V) :
    (sizedDictEquiv U V n).symm (embValsEquiv U V n (f, v)).1 =
      ⟨dictOfEmb f v, card_dom_dictOfEmb f v, valuesBounded_dictOfEmb f v⟩ := by
  apply Subtype.ext
  change dictOfKeySetVals ⟨Finset.univ.map f, _⟩ (v ∘ (embToPerm f).symm) = dictOfEmb f v
  set K : { K : Finset (Fin U) // K.card = n } := ⟨Finset.univ.map f, by simp⟩
  set σ := embToPerm f
  funext u
  by_cases hu : u ∈ K.1
  · have hmem := hu
    rw [Finset.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have hfi : K.1.orderEmbOfFin K.2 (σ i) = f i :=
      congrArg Subtype.val ((K.1.orderIsoOfFin K.2).apply_symm_apply ⟨f i, hu⟩)
    rw [dictOfEmb_apply_self, ← hfi, dictOfKeySetVals_orderEmbOfFin]
    dsimp only [Function.comp_apply]
    rw [σ.symm_apply_apply]
  · have hnot : ∀ i : Fin n, f i ≠ u := fun i heq => by
      subst heq
      exact hu (Finset.mem_map_of_mem f (Finset.mem_univ i))
    rw [dictOfEmb_apply_eq_none f v hnot]
    simp [dictOfKeySetVals, hu]

private theorem map_windowDict_uniformOfFintype {U V n t : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht : t ≤ n) :
    letI : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
    letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
    letI : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
    (PMF.uniformOfFintype ((Fin (2 * n) ↪ Fin U) × (Fin (2 * n) → Fin V))).map
      (fun p => windowDict p.1 p.2 t ht) =
      PMF.uniformOfFintype (SizedDict U V n) := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  let _ : Nonempty (Fin n ↪ Fin U) := ⟨Fin.castLEEmb (by omega)⟩
  let _ : Nonempty (Fin n ↪ Fin (U - n)) := ⟨Fin.castLEEmb (by omega)⟩
  let _ : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
  let _ : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
    ⟨sizedDictEquiv U V n (Classical.arbitrary _)⟩
  have hkeys :
      (PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)).map
        (fun keys : Fin (2 * n) ↪ Fin U => windowEmb keys t ht) =
        PMF.uniformOfFintype (Fin n ↪ Fin U) := by
    have hcomp :
        (fun keys : Fin (2 * n) ↪ Fin U => windowEmb keys t ht) =
          Prod.fst ∘ windowEmbEquiv (U := U) t ht :=
      funext fun keys => (windowEmbEquiv_fst t ht keys).symm
    rw [hcomp, ← _root_.PMF.map_comp,
      PMF.uniformOfFintype_map_equiv (windowEmbEquiv (U := U) t ht)]
    exact PMF.uniformOfFintype_prod_map_fst
  have hvals :
      (PMF.uniformOfFintype (Fin (2 * n) → Fin V)).map
        (fun vals : Fin (2 * n) → Fin V => windowVals vals t ht) =
        PMF.uniformOfFintype (Fin n → Fin V) := by
    have hcomp :
        (fun vals : Fin (2 * n) → Fin V => windowVals vals t ht) =
          Prod.fst ∘ windowValsEquiv (V := V) t ht :=
      funext fun vals => (windowValsEquiv_fst t ht vals).symm
    rw [hcomp, ← _root_.PMF.map_comp,
      PMF.uniformOfFintype_map_equiv (windowValsEquiv (V := V) t ht)]
    exact PMF.uniformOfFintype_prod_map_fst
  let mkDict : (Fin n ↪ Fin U) → (Fin n → Fin V) → SizedDict U V n := fun f v =>
    ⟨dictOfEmb f v, card_dom_dictOfEmb f v, valuesBounded_dictOfEmb f v⟩
  calc
    (PMF.uniformOfFintype ((Fin (2 * n) ↪ Fin U) × (Fin (2 * n) → Fin V))).map
        (fun p => windowDict p.1 p.2 t ht)
      = ((PMF.uniformOfFintype (Fin (2 * n) ↪ Fin U)).bind fun keys =>
          (PMF.uniformOfFintype (Fin (2 * n) → Fin V)).map fun vals =>
            mkDict (windowEmb keys t ht) (windowVals vals t ht)) := by
          exact (PMF.uniformOfFintype_bind_map
            (fun (keys : Fin (2 * n) ↪ Fin U) (vals : Fin (2 * n) → Fin V) =>
              mkDict (windowEmb keys t ht) (windowVals vals t ht))).symm
    _ = ((PMF.uniformOfFintype (Fin n ↪ Fin U)).bind fun f =>
          (PMF.uniformOfFintype (Fin n → Fin V)).map fun v => mkDict f v) := by
          rw [← hkeys, ← hvals, _root_.PMF.bind_map]
          refine congrArg (_root_.PMF.bind _) (funext fun keys => ?_)
          dsimp only [Function.comp_def]
          rw [_root_.PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype ((Fin n ↪ Fin U) × (Fin n → Fin V))).map
          (fun p => (sizedDictEquiv U V n).symm (embValsEquiv U V n p).1) := by
          rw [PMF.uniformOfFintype_bind_map]
          refine congrArg (_root_.PMF.map · _) (funext fun ⟨f, v⟩ => ?_)
          exact (sizedDictEquiv_symm_embValsEquiv_fst f v).symm
    _ = (((PMF.uniformOfFintype ((Fin n ↪ Fin U) × (Fin n → Fin V))).map
          (embValsEquiv U V n)).map Prod.fst).map (sizedDictEquiv U V n).symm := by
          rw [_root_.PMF.map_comp, _root_.PMF.map_comp]; rfl
    _ = PMF.uniformOfFintype (SizedDict U V n) := by
          rw [PMF.uniformOfFintype_map_equiv (embValsEquiv U V n),
            PMF.uniformOfFintype_prod_map_fst,
            PMF.uniformOfFintype_map_equiv (sizedDictEquiv U V n).symm]

/-- After the `n` initial insertions and any `t ≤ n` complete meta-operations under
`insertQueryDeleteDist`, the induced dictionary state is uniformly distributed over the
`U.choose n * V ^ n` valid size-`n`, `V`-bounded dictionaries (`SizedDict U V n`). -/
theorem map_run_take_insertQueryDeleteDist {U V n t : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht : t ≤ n) :
    letI : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
    (insertQueryDeleteDist U V n hU hV).map
      (fun ops => ((Dynamic.spec U V n).run (Dictionary.empty U) (ops.take (n + 3 * t))).1) =
      (PMF.uniformOfFintype (SizedDict U V n)).map Subtype.val := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  let _ : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
  rw [insertQueryDeleteDist_eq_uniformOfFintype_map hU hV, _root_.PMF.map_comp,
    ← map_windowDict_uniformOfFintype hU hV ht, _root_.PMF.map_comp]
  refine congrArg (_root_.PMF.map · _) (funext fun ⟨keys, vals⟩ => ?_)
  exact (validHistory_and_run_take_insertQueryDeleteSeq keys vals ht).2

/-- After the `n` initial insertions and any `t ≤ n` complete meta-operations under
`insertDeleteDist`, the induced dictionary state is uniformly distributed over `SizedDict U V n`. -/
theorem map_run_take_insertDeleteDist {U V n t : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht : t ≤ n) :
    letI : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
    (insertDeleteDist U V n hU hV).map
      (fun ops => ((Dynamic.spec U V n).run (Dictionary.empty U) (ops.take (n + 2 * t))).1) =
      (PMF.uniformOfFintype (SizedDict U V n)).map Subtype.val := by
  let _ : Nonempty (Fin (2 * n) ↪ Fin U) := ⟨Fin.castLEEmb hU⟩
  let _ : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  let _ : Nonempty (SizedDict U V n) := nonempty_sizedDict (by omega) hV
  rw [insertDeleteDist_eq_uniformOfFintype_map hU hV, _root_.PMF.map_comp,
    ← map_windowDict_uniformOfFintype hU hV ht, _root_.PMF.map_comp]
  refine congrArg (_root_.PMF.map · _) (funext fun ⟨keys, vals⟩ => ?_)
  exact (validHistory_and_run_take_insertDeleteSeq keys vals ht).2

/-- Finite-type `(keySet, orderedVals)` marginal version of `map_run_take_insertQueryDeleteDist`,
typed directly in `{ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)` for finite-PMF Shannon
entropy calculations. -/
theorem map_extractKeySetVals_insertQueryDeleteDist {U V n t : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht : t ≤ n) (hnU : n ≤ U := by omega) :
    letI : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
      ⟨sizedDictEquiv U V n (nonempty_sizedDict hnU hV).some⟩
    (insertQueryDeleteDist U V n hU hV).map
      (fun ops => extractKeySetVals hnU hV
        ((Dynamic.spec U V n).run (Dictionary.empty U) (ops.take (n + 3 * t))).1) =
      PMF.uniformOfFintype ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) := by
  let _ : Nonempty (SizedDict U V n) := nonempty_sizedDict hnU hV
  let _ : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
    ⟨sizedDictEquiv U V n (Classical.arbitrary _)⟩
  have hmap := congrArg (_root_.PMF.map (extractKeySetVals hnU hV))
    (map_run_take_insertQueryDeleteDist hU hV ht)
  rw [_root_.PMF.map_comp, _root_.PMF.map_comp] at hmap
  dsimp only [Function.comp_def] at hmap
  refine hmap.trans ?_
  have heq : (fun s : SizedDict U V n => extractKeySetVals hnU hV s.1) = sizedDictEquiv U V n :=
    funext fun s => extractKeySetVals_coe hnU hV s
  rw [heq, PMF.uniformOfFintype_map_equiv (sizedDictEquiv U V n)]

/-- Finite-type `(keySet, orderedVals)` marginal version of `map_run_take_insertDeleteDist`. -/
theorem map_extractKeySetVals_insertDeleteDist {U V n t : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht : t ≤ n) (hnU : n ≤ U := by omega) :
    letI : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
      ⟨sizedDictEquiv U V n (nonempty_sizedDict hnU hV).some⟩
    (insertDeleteDist U V n hU hV).map
      (fun ops => extractKeySetVals hnU hV
        ((Dynamic.spec U V n).run (Dictionary.empty U) (ops.take (n + 2 * t))).1) =
      PMF.uniformOfFintype ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) := by
  let _ : Nonempty (SizedDict U V n) := nonempty_sizedDict hnU hV
  let _ : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
    ⟨sizedDictEquiv U V n (Classical.arbitrary _)⟩
  have hmap := congrArg (_root_.PMF.map (extractKeySetVals hnU hV))
    (map_run_take_insertDeleteDist hU hV ht)
  rw [_root_.PMF.map_comp, _root_.PMF.map_comp] at hmap
  dsimp only [Function.comp_def] at hmap
  refine hmap.trans ?_
  have heq : (fun s : SizedDict U V n => extractKeySetVals hnU hV s.1) = sizedDictEquiv U V n :=
    funext fun s => extractKeySetVals_coe hnU hV s
  rw [heq, PMF.uniformOfFintype_map_equiv (sizedDictEquiv U V n)]

/-! ### Parallel single-timestamp state decoder (`decodeDict`) and all-history Yao reduction -/

/-- Set of all admissible `Dynamic.spec U V n` histories from `Dictionary.empty U` of length at
most `M` (automatically contained in `validOps U V` by `forall_mem_validOps_of_validHistory`). -/
@[expose] def validHistoriesUpTo (U V n M : ℕ) : Set (List (Dynamic.Op U)) :=
  { ops | (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops ∧ ops.length ≤ M }

theorem validHistoriesUpTo_spec {U V n M : ℕ} {ops : List (Dynamic.Op U)}
    (hops : ops ∈ validHistoriesUpTo U V n M) :
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops ∧
      ops.length ≤ M ∧ ∀ o ∈ ops, o ∈ validOps U V :=
  ⟨hops.1, hops.2, forall_mem_validOps_of_validHistory hops.1⟩

/-- Single-timestamp parallel dictionary state decoder: evaluates single-step `.query u` on `D_det`
from memory `C_t` at fixed step index `t` for every `u : Fin U`, without advancing `t` or mutating
`C_t` across keys (formalization adaptation making time-indexed state recovery explicit in
[LiLiangYuZhou2023], Sections 4.2, 5.1, and 8.1). -/
@[expose] def decodeDict {U cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t : ℕ) (C_t : Mem cells w) : Dictionary.State U :=
  fun u => ((D_det.step t (.query u)).run C_t).1

/-- If `D_det` is exact on all admissible histories up to length `M + 1`, then after *any*
admissible prefix `pref` of length `≤ M` reaching memory `C_t := (D_det.runSeq pref).2` and
abstract state `s_t := ((Dynamic.spec U V n).run (Dictionary.empty U) pref).1`,
`decodeDict D_det pref.length C_t` equals `s_t` identically. -/
theorem decodeDict_runSeq_eq {U V n M cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (M + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    {pref : List (Dynamic.Op U)}
    (hpref_vh : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref)
    (hpref_len : pref.length ≤ M) :
    decodeDict D_det pref.length (D_det.runSeq pref).2 =
      ((Dynamic.spec U V n).run (Dictionary.empty U) pref).1 := by
  funext u
  have hops_mem : pref ++ [.query u] ∈ validHistoriesUpTo U V n (M + 1) := by
    refine ⟨?_, by simp; omega⟩
    rw [StateTransitionSpec.validHistory_append]
    exact ⟨hpref_vh, trivial, trivial⟩
  have heq := hcorr (pref ++ [.query u]) hops_mem
  rw [IndexedScheme.runSeq, IndexedScheme.runInterval_append, Nat.zero_add,
    StateTransitionSpec.run_append] at heq
  change (D_det.runSeq pref).1 ++
      [⟨Dynamic.Op.query u, ((D_det.step pref.length (.query u)).run (D_det.runSeq pref).2).1⟩] =
    ((Dynamic.spec U V n).run (Dictionary.empty U) pref).2 ++
      [⟨Dynamic.Op.query u, ((Dynamic.spec U V n).run (Dictionary.empty U) pref).1 u⟩] at heq
  have htail := List.append_inj_right' heq rfl
  injection htail with hhead _
  exact eq_of_heq (Sigma.mk.inj hhead).2

/-- Out-of-domain query rejection: after any admissible prefix `pref` of length `≤ M`, querying any
absent key `u ∉ Dictionary.dom s_t` at step `pref.length` returns `none`. -/
theorem step_query_eq_none_of_notMem_dom {U V n M cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (M + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    {pref : List (Dynamic.Op U)}
    (hpref_vh : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref)
    (hpref_len : pref.length ≤ M)
    {u : Fin U}
    (hu : u ∉ Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref).1) :
    ((D_det.step pref.length (.query u)).run (D_det.runSeq pref).2).1 = none := by
  have hdec := congrFun (decodeDict_runSeq_eq hcorr hpref_vh hpref_len) u
  exact hdec.trans (Dictionary.notMem_dom_iff.mp hu)

/-- Zero-error Yao coin-fixing on `insertQueryDeleteDist` preserving exactness across **all**
admissible histories up to horizon `4 * n + 1` (so `decodeDict` is exact after every prefix of
length `≤ 4 * n`). -/
theorem exists_det_indexedScheme_insertQueryDeleteDist {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst)) :
    ∃ D_det ∈ (P.indexedSchemeLaw (4 * n + 1) (validOps U V)).support,
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) ∧
      (∑' ops, insertQueryDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, insertQueryDeleteDist U V n hU hV ops * P.expectedSeqProbes ops :=
  DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes
    (D := Dynamic.spec U V n) (Dictionary.empty U) P (validOps U V) (4 * n + 1)
    (validHistoriesUpTo U V n (4 * n + 1)) (fun _ hops => validHistoriesUpTo_spec hops) hcorr
    (insertQueryDeleteDist U V n hU hV) fun _ hops =>
      ⟨(length_of_mem_support_insertQueryDeleteDist hops).trans_le (Nat.le_succ _),
       (validHistory_of_mem_support_insertQueryDeleteDist hops).2⟩

/-- Zero-error Yao coin-fixing on `insertDeleteDist` preserving exactness across **all** admissible
histories up to horizon `3 * n + 1` (including `.query` extensions outside `insertDeleteDist`'s
update-only support, so `decodeDict` remains exact after every prefix of length `≤ 3 * n`). -/
theorem exists_det_indexedScheme_insertDeleteDist {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst)) :
    ∃ D_det ∈ (P.indexedSchemeLaw (3 * n + 1) (validOps U V)).support,
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) ∧
      (∑' ops, insertDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) ≤
        ∑' ops, insertDeleteDist U V n hU hV ops * P.expectedSeqProbes ops :=
  DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes
    (D := Dynamic.spec U V n) (Dictionary.empty U) P (validOps U V) (3 * n + 1)
    (validHistoriesUpTo U V n (3 * n + 1)) (fun _ hops => validHistoriesUpTo_spec hops) hcorr
    (insertDeleteDist U V n hU hV) fun _ hops =>
      ⟨(length_of_mem_support_insertDeleteDist hops).trans_le (Nat.le_succ _),
       (validHistory_of_mem_support_insertDeleteDist hops).2⟩

/-- Lower-bound transfer for `ObliviousSequenceImpl` on `Dynamic.spec U V n` over
`insertQueryDeleteDist`. -/
theorem le_expected_charge_insertQueryDeleteDist_of_det_indexedScheme {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (C : DataStructure.CellProbe.Randomized.ObliviousSequenceImpl
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)) P)
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w,
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      L ≤ ∑' ops, insertQueryDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, insertQueryDeleteDist U V n hU hV ops *
            (((ops.map C.charge).sum : ℕ) : ℝ≥0∞) :=
  C.le_expected_charge_of_det_indexedScheme (validOps U V) (4 * n + 1)
    (validHistoriesUpTo U V n (4 * n + 1))
    (fun _ hops => validHistoriesUpTo_spec hops)
    (insertQueryDeleteDist U V n hU hV)
    (fun _ hops => by
      obtain ⟨hvh, halph⟩ := validHistory_of_mem_support_insertQueryDeleteDist hops
      exact ⟨hvh, (length_of_mem_support_insertQueryDeleteDist hops).trans_le (Nat.le_succ _),
        halph⟩)
    hlb

/-- Lower-bound transfer for `ObliviousSequenceImpl` on `Dynamic.spec U V n` over
`insertDeleteDist`. -/
theorem le_expected_charge_insertDeleteDist_of_det_indexedScheme {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (C : DataStructure.CellProbe.Randomized.ObliviousSequenceImpl
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)) P)
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w,
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      L ≤ ∑' ops, insertDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, insertDeleteDist U V n hU hV ops *
            (((ops.map C.charge).sum : ℕ) : ℝ≥0∞) :=
  C.le_expected_charge_of_det_indexedScheme (validOps U V) (3 * n + 1)
    (validHistoriesUpTo U V n (3 * n + 1))
    (fun _ hops => validHistoriesUpTo_spec hops)
    (insertDeleteDist U V n hU hV)
    (fun _ hops => by
      obtain ⟨hvh, halph⟩ := validHistory_of_mem_support_insertDeleteDist hops
      exact ⟨hvh, (length_of_mem_support_insertDeleteDist hops).trans_le (Nat.le_succ _), halph⟩)
    hlb

/-- Lower-bound transfer for `Randomized.StateTransitionImpl` on `Dynamic.spec U V n` over
`insertQueryDeleteDist`. -/
theorem le_expected_totalCost_insertQueryDeleteDist_of_det_indexedScheme {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (C : DataStructure.CellProbe.Randomized.StateTransitionImpl
      (Dynamic.spec U V n) P (Dictionary.empty U))
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w,
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      L ≤ ∑' ops, insertQueryDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, insertQueryDeleteDist U V n hU hV ops *
            ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) :=
  C.le_expected_totalCost_of_det_indexedScheme (validOps U V) (4 * n + 1)
    (validHistoriesUpTo U V n (4 * n + 1))
    (fun _ hops => validHistoriesUpTo_spec hops)
    (insertQueryDeleteDist U V n hU hV)
    (fun _ hops => by
      obtain ⟨hvh, halph⟩ := validHistory_of_mem_support_insertQueryDeleteDist hops
      exact ⟨hvh, (length_of_mem_support_insertQueryDeleteDist hops).trans_le (Nat.le_succ _),
        halph⟩)
    hlb

/-- Lower-bound transfer for `Randomized.StateTransitionImpl` on `Dynamic.spec U V n` over
`insertDeleteDist`. -/
theorem le_expected_totalCost_insertDeleteDist_of_det_indexedScheme {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (C : DataStructure.CellProbe.Randomized.StateTransitionImpl
      (Dynamic.spec U V n) P (Dictionary.empty U))
    {L : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w,
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      L ≤ ∑' ops, insertDeleteDist U V n hU hV ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    L ≤ (C.initPotential : ℝ≥0∞) +
          ∑' ops, insertDeleteDist U V n hU hV ops *
            ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) :=
  C.le_expected_totalCost_of_det_indexedScheme (validOps U V) (3 * n + 1)
    (validHistoriesUpTo U V n (3 * n + 1))
    (fun _ hops => validHistoriesUpTo_spec hops)
    (insertDeleteDist U V n hU hV)
    (fun _ hops => by
      obtain ⟨hvh, halph⟩ := validHistory_of_mem_support_insertDeleteDist hops
      exact ⟨hvh, (length_of_mem_support_insertDeleteDist hops).trans_le (Nat.le_succ _), halph⟩)
    hlb

end Cslib.DataStructure.Dictionary.CellProbe
