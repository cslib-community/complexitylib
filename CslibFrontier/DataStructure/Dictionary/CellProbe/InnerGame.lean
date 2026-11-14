/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.Consistency
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.Coding.PrefixFreeEntropy
import CslibFrontier.Probability.Coding.SetSeparator
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.GroupTheory.Perm.Support

/-!
# Inner Communication Game and Consistency Probability Bound

Section 5's single-segment inner communication game and entropy compression argument from Li, Liang,
Yu, and Zhou ([LiLiangYuZhou2023]; locators follow `arXiv:2306.02253v3`, printed page `p` = PDF page
`p + 1`), proving Lemma 5.1, Lemma 4.4, and Claim 4.2's far-candidate expectation bound.

Pinned source: [LiLiangYuZhou2023] (`arXiv:2306.02253v3`), Section 4.2, pp. 14–16 (PDF pp. 15–17);
Section 4.3, Claim 4.2, pp. 17–18 (PDF pp. 18–19), Definition 4.3, p. 17 (PDF p. 18), and
Lemma 4.4, p. 18 (PDF p. 19); Section 5, Lemma 5.1, p. 21 (PDF p. 22); Section 5.1, Steps 1–6 and
Eq. (10), pp. 22–23 (PDF pp. 23–24); Section 5.2, Eqs. (11)–(14) and binomial log estimates,
pp. 24–25 (PDF pp. 25–26).

Original formalization adaptations: (1) `IsCappedConsistent` and `IsSeedConsistent` incorporate the
deterministic `c = 1` probe cap `|S_A|, |S_B| ≤ m * t` on `{W = 1}`, avoiding conditional probe
inflation in Eq. (11); (2) Step 3 uses `exists_prefixFree_separator_code` (`β = 2`, expected length
`≤ 4 * m * t + 7`), yielding `6 * m * t` in `hbudget`; (3) key-value assignments are tracked on
`Fin V` (`1 ≤ V`) so the `+ (n + m) * log₂ V` value entropy cancels in Eq. (12).

## Main definitions

* `IsSeedConsistent`: single-segment probe-capped consistency on `HardKeyValSeed`.
* `section5Dist`, `section5LtHalfDist`, `segmentRestDist`, `segmentRestLtHalfDist`: conditional
  `(seed, B)` distributions over `Finset.univ \ K` and over the remaining multi-round pool.

## Main results

* `prob_isCappedConsistent_section5_le`, `prob_isCappedConsistent_section5_lt_half_le`: Lemma 5.1
  and Lemma 4.4 over `Finset.univ \ K`.
* `prob_isCappedConsistent_segmentRest_le`, `prob_isCappedConsistent_segmentRest_lt_half_le`,
  `expected_card_cappedConsistent_segmentRest_lt_half_le`: Lemma 5.1, Lemma 4.4, and Claim 4.2 over
  the remaining multi-round pool `s.insertedSet t₀ r_rest`.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 4.2, 4.3, and 5 (`arXiv:2306.02253v3`).
-/

public section

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.BitString Cslib.Probability Cslib.Probability.Coding InformationTheory
open Finset (orderSubset orderSubset_apply image_orderSubset orderSubset_congr
  orderSubset_eq_of_embSetPermEquiv_fst image_perm_trans embSetPermEquiv
  embSetPermEquiv_symm_apply embSetPermEquiv_fst embSetPermEquiv_perm_trans)
open scoped BigOperators ENNReal

private def candPrefix {U V m : ℕ} (d b : Fin m → Fin U) (kv : Fin U → Fin V) (r : ℕ) :
    List (Dynamic.Op U) :=
  ((List.finRange m).take r).flatMap fun i =>
    [Dynamic.Op.query (d i), Dynamic.Op.delete (d i), Dynamic.Op.insert (b i) (kv (b i)).val]

private theorem length_candPrefix {U V m r : ℕ} (d b : Fin m → Fin U) (kv : Fin U → Fin V)
    (hr : r ≤ m) : (candPrefix d b kv r).length = 3 * r := by
  rw [candPrefix, List.length_flatMap_of_forall_length_eq (k := 3) (fun _ _ => rfl),
    List.length_take, List.length_finRange, Nat.min_eq_left hr, Nat.mul_comm]

private theorem candPrefix_succ {U V m r : ℕ} (d b : Fin m → Fin U) (kv : Fin U → Fin V)
    (hr : r < m) : candPrefix d b kv (r + 1) = candPrefix d b kv r ++
      [Dynamic.Op.query (d ⟨r, hr⟩), Dynamic.Op.delete (d ⟨r, hr⟩),
        Dynamic.Op.insert (b ⟨r, hr⟩) (kv (b ⟨r, hr⟩)).val] := by
  have hget : (List.finRange m)[r]'(by simpa using hr) = ⟨r, hr⟩ := by simp
  rw [candPrefix, List.take_add_one, List.getElem?_eq_getElem (by simpa using hr), hget]
  simp [candPrefix]

private def queryOutAt {U : ℕ} (outs : List (Σ o : Dynamic.Op U, Dynamic.Op.Result o)) (r : ℕ) :
    Option ℕ :=
  match outs[3 * r]? with | some ⟨.query _, res⟩ => res | _ => none

private theorem queryOutAt_runInterval {U V m cells w : ℕ}
    (D : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (t_start : ℕ) (mem : Mem cells w)
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) (r : Fin m) :
    queryOutAt (D.runInterval t_start mem (candidateQueryDeleteInsertOps d b kv)).1 r.val =
      ((D.step (t_start + 3 * r.val) (.query (d r))).run
        (D.runInterval t_start mem (candPrefix d b kv r.val)).2).1 := by
  have hsplit : candidateQueryDeleteInsertOps d b kv = candPrefix d b kv r.val ++
      ([Dynamic.Op.query (d r), Dynamic.Op.delete (d r), Dynamic.Op.insert (b r) (kv (b r)).val] ++
        ((List.finRange m).drop (r.val + 1)).flatMap fun i =>
          [.query (d i), .delete (d i), .insert (b i) (kv (b i)).val]) := by
    have hfr : List.finRange m = (List.finRange m).take r.val ++
        (r :: (List.finRange m).drop (r.val + 1)) := by
      conv_lhs => rw [← List.take_append_drop r.val (List.finRange m)]
      rw [List.drop_eq_getElem_cons (by simp [r.isLt])]; simp
    simp only [candidateQueryDeleteInsertOps, candPrefix]
    conv_lhs => rw [hfr]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [hsplit, IndexedScheme.runInterval_append]
  have hlen_c := length_candPrefix d b kv r.isLt.le
  have hlen_l : (D.runInterval t_start mem (candPrefix d b kv r.val)).1.length = 3 * r.val :=
    (D.length_runInterval_fst t_start mem _).trans hlen_c
  rw [hlen_c, queryOutAt, List.getElem?_append_right hlen_l.le]
  simp [hlen_l, IndexedScheme.runInterval_cons]

private noncomputable def passesDeletionTest {U V m cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (step₀ : ℕ)
    (C_mix : Mem cells w) (mask : Finset (Fin cells)) (B : Finset (Fin U)) (hB : B.card = m)
    (π σ : Equiv.Perm (Fin m)) (kv : Fin U → Fin V)
    (D_cand : Finset (Fin U)) (hD : D_cand.card = m) : Prop :=
  let ops_cand := candidateQueryDeleteInsertOps (orderSubset D_cand hD σ) (orderSubset B hB π) kv
  D_det.probedCellsInterval step₀ C_mix ops_cand ⊆ mask ∧
    ∀ r : Fin m, (queryOutAt (D_det.runInterval step₀ C_mix ops_cand).1 r.val).isSome

private theorem step_candPrefix {U V n m k : ℕ}
    {pref_bef : List (Dynamic.Op U)} {d b : Fin m → Fin U} {kv : Fin U → Fin V} (hk : k < m)
    (hvh_k : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
      (pref_bef ++ candPrefix d b kv k))
    (hcard_k : (Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U)
      (pref_bef ++ candPrefix d b kv k)).1).card ≤ n)
    (hd_some : (((Dynamic.spec U V n).run (Dictionary.empty U)
      (pref_bef ++ candPrefix d b kv k)).1 (d ⟨k, hk⟩)).isSome) :
    let s_k := ((Dynamic.spec U V n).run (Dictionary.empty U) (pref_bef ++ candPrefix d b kv k)).1
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
        (pref_bef ++ candPrefix d b kv (k + 1)) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U) (pref_bef ++ candPrefix d b kv (k + 1))).1 =
        Function.update (Function.update s_k (d ⟨k, hk⟩) none) (b ⟨k, hk⟩)
          (some (kv (b ⟨k, hk⟩)).val) ∧
      (Dictionary.dom (Function.update (Function.update s_k (d ⟨k, hk⟩) none) (b ⟨k, hk⟩)
        (some (kv (b ⟨k, hk⟩)).val))).card ≤ n := by
  set pref_k := pref_bef ++ candPrefix d b kv k
  set s_k := ((Dynamic.spec U V n).run (Dictionary.empty U) pref_k).1
  obtain ⟨v₀, hv₀⟩ := Option.isSome_iff_exists.mp hd_some
  have hpos : 1 ≤ (Dictionary.dom s_k).card :=
    Finset.card_pos.mpr ⟨d ⟨k, hk⟩, Dictionary.mem_dom_iff.mpr ⟨v₀, hv₀⟩⟩
  have hcard_del : (Dictionary.dom (Function.update s_k (d ⟨k, hk⟩) none)).card < n := by
    rw [Dynamic.card_dom_delete_eq_of_isSome hd_some]; omega
  have hupd_le (s : Dictionary.State U) (u : Fin U) (v : ℕ) :
      (Dictionary.dom (Function.update s u (some v))).card ≤ (Dictionary.dom s).card + 1 := by
    refine (Finset.card_le_card fun x hx => ?_).trans (Finset.card_insert_le u (Dictionary.dom s))
    by_cases hxu : x = u
    · subst hxu; exact Finset.mem_insert_self _ _
    · rw [Dictionary.mem_dom_iff, Function.update_of_ne hxu, ← Dictionary.mem_dom_iff] at hx
      exact Finset.mem_insert_of_mem hx
  dsimp only; rw [candPrefix_succ d b kv hk, ← List.append_assoc,
    StateTransitionSpec.validHistory_append,
    (Dynamic.spec U V n).run_append (Dictionary.empty U) pref_k]
  dsimp only
  exact ⟨⟨hvh_k, trivial, trivial, ⟨Or.inl hcard_del, (kv (b ⟨k, hk⟩)).isLt⟩, trivial⟩, rfl,
    (hupd_le _ _ _).trans (by omega)⟩

private theorem subset_union_of_passesDeletionTest {U V n t₀ m cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    {pref_bef : List (Dynamic.Op U)}
    (hvh_bef : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref_bef)
    (hlen_bef : pref_bef.length = n + 3 * t₀) (ht : t₀ + m ≤ n)
    (hK_le : (Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1).card ≤ n)
    {C_after : Mem cells w} {mask : Finset (Fin cells)} {B D_cand : Finset (Fin U)}
    (hB : B.card = m) (hD : D_cand.card = m) {π σ : Equiv.Perm (Fin m)} {kv : Fin U → Fin V}
    (hpass : passesDeletionTest D_det (n + 3 * t₀)
      (mixMem (D_det.runSeq pref_bef).2 C_after mask) mask B hB π σ kv D_cand hD) :
    D_cand ⊆ Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1 ∪ B := by
  set C_bef := (D_det.runSeq pref_bef).2
  set s₀ := ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1
  set d_c := orderSubset D_cand hD σ; set b_c := orderSubset B hB π
  obtain ⟨hsub_mask, hqs⟩ := hpass
  have hrun_eq := (D_det.runInterval_eq_of_eq_on_probedCellsInterval (n + 3 * t₀)
    (candidateQueryDeleteInsertOps d_c b_c kv) fun _ hj => (mixMem_of_mem (hsub_mask hj)).symm).1
  have hind : ∀ k ≤ m,
      let pref_k := pref_bef ++ candPrefix d_c b_c kv k
      let s_k := ((Dynamic.spec U V n).run (Dictionary.empty U) pref_k).1
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref_k ∧
        (Dictionary.dom s_k).card ≤ n ∧ Dictionary.dom s_k ⊆ Dictionary.dom s₀ ∪ B ∧
        ∀ r : Fin m, r.val < k → d_c r ∈ Dictionary.dom s₀ ∪ B := fun k hk => by
    induction k with
    | zero =>
      simp only [candPrefix, List.take_zero, List.flatMap_nil, List.append_nil]
      exact ⟨hvh_bef, hK_le, Finset.subset_union_left, fun _ hr => (Nat.not_lt_zero _ hr).elim⟩
    | succ k ih =>
      obtain ⟨hvh_k, hcard_k, hdom_k, hmem_k⟩ := ih (Nat.le_of_succ_le hk)
      let r₀ : Fin m := ⟨k, hk⟩
      set pref_k := pref_bef ++ candPrefix d_c b_c kv k
      set s_k := ((Dynamic.spec U V n).run (Dictionary.empty U) pref_k).1
      have hlen_k : pref_k.length = n + 3 * t₀ + 3 * k := by
        rw [List.length_append, hlen_bef, length_candPrefix d_c b_c kv (Nat.le_of_succ_le hk)]
      have hmem_seq : (D_det.runSeq pref_k).2 =
          (D_det.runInterval (n + 3 * t₀) C_bef (candPrefix d_c b_c kv k)).2 := by
        rw [IndexedScheme.runSeq, IndexedScheme.runInterval_append, Nat.zero_add, hlen_bef]; rfl
      have hsk_some : (s_k (d_c r₀)).isSome := by
        dsimp only [s_k]
        have hdec := congrFun (decodeDict_runSeq_eq (M := 4 * n) hcorr hvh_k
          (by rw [hlen_k]; omega)) (d_c r₀)
        dsimp only [decodeDict] at hdec
        rw [← hdec, hlen_k, hmem_seq,
          ← queryOutAt_runInterval D_det (n + 3 * t₀) C_bef d_c b_c kv r₀, hrun_eq]
        exact hqs r₀
      have hd_in_sk : d_c r₀ ∈ Dictionary.dom s_k :=
        Dictionary.mem_dom_iff.mpr (Option.isSome_iff_exists.mp hsk_some)
      obtain ⟨hvh_s, hrun_s, hcard_s⟩ := step_candPrefix hk hvh_k hcard_k hsk_some
      dsimp only; rw [hrun_s]; refine ⟨hvh_s, hcard_s, fun x hx => ?_, fun r hr =>
        (Nat.lt_succ_iff_lt_or_eq.mp hr).elim (hmem_k r)
          fun heq => (Fin.ext heq : r = r₀) ▸ hdom_k hd_in_sk⟩
      by_cases hxb : x = b_c r₀
      · exact hxb ▸ Finset.mem_union_right _
          (by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem _ _ _)
      · rw [Dictionary.mem_dom_iff, Function.update_of_ne hxb] at hx
        by_cases hxd : x = d_c r₀
        · subst hxd; rw [Function.update_self] at hx; obtain ⟨_, hx⟩ := hx; cases hx
        · rw [Function.update_of_ne hxd, ← Dictionary.mem_dom_iff] at hx; exact hdom_k hx
  intro x hx; rw [← image_orderSubset D_cand hD σ, Finset.mem_image] at hx
  obtain ⟨r, _, rfl⟩ := hx; exact (hind m le_rfl).2.2.2 r r.isLt

private theorem passesDeletionTest_and_queryOutAt_eq {U V n t₀ m cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    {pref_bef : List (Dynamic.Op U)}
    (hvh_bef : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref_bef)
    (hlen_bef : pref_bef.length = n + 3 * t₀) (ht : t₀ + m ≤ n)
    (hK_le : (Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1).card ≤ n)
    {B D : Finset (Fin U)} (hB : B.card = m) (hD : D.card = m)
    (hDK : D ⊆ Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1)
    (hBK : Disjoint B (Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1))
    {kv : Fin U → Fin V}
    (hs₀_val : ∀ u ∈ Dictionary.dom ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1,
      ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1 u = some (kv u).val)
    {C_after : Mem cells w} {mask : Finset (Fin cells)} {π σ : Equiv.Perm (Fin m)}
    (hmask : D_det.probedCellsInterval (n + 3 * t₀) (D_det.runSeq pref_bef).2
      (candidateQueryDeleteInsertOps (orderSubset D hD σ) (orderSubset B hB π) kv) ⊆ mask) :
    let C_mix := mixMem (D_det.runSeq pref_bef).2 C_after mask
    let ops_B := candidateQueryDeleteInsertOps (orderSubset D hD σ) (orderSubset B hB π) kv
    passesDeletionTest D_det (n + 3 * t₀) C_mix mask B hB π σ kv D hD ∧
      ∀ r : Fin m, queryOutAt (D_det.runInterval (n + 3 * t₀) C_mix ops_B).1 r.val =
        some (kv (orderSubset D hD σ r)).val := by
  dsimp only
  set C_bef := (D_det.runSeq pref_bef).2; set C_mix := mixMem C_bef C_after mask
  set d := orderSubset D hD σ; set b := orderSubset B hB π
  set ops_B := candidateQueryDeleteInsertOps d b kv
  obtain ⟨hout_eq, _, hcells_eq, _⟩ :=
    runInterval_mixMem_eq_of_probedCellsInterval_subset D_det (n + 3 * t₀) C_bef C_after mask
      ops_B hmask
  have hind : ∀ k ≤ m,
      let pref_k := pref_bef ++ candPrefix d b kv k
      let s_k := ((Dynamic.spec U V n).run (Dictionary.empty U) pref_k).1
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref_k ∧
        (Dictionary.dom s_k).card ≤ n ∧
        ∀ r : Fin m, k ≤ r.val → s_k (d r) = some (kv (d r)).val := fun k hk => by
    induction k with
    | zero =>
      simp only [candPrefix, List.take_zero, List.flatMap_nil, List.append_nil, Nat.zero_le,
        forall_const]
      exact ⟨hvh_bef, hK_le, fun r =>
        hs₀_val (d r) (hDK (by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem D hD (σ r)))⟩
    | succ k ih =>
      obtain ⟨hvh_k, hcard_k, hval_k⟩ := ih (Nat.le_of_succ_le hk)
      let r₀ : Fin m := ⟨k, hk⟩
      have hsk_some : (((Dynamic.spec U V n).run (Dictionary.empty U)
          (pref_bef ++ candPrefix d b kv k)).1 (d r₀)).isSome := by rw [hval_k r₀ le_rfl]; rfl
      obtain ⟨hvh_s, hrun_s, hcard_s⟩ := step_candPrefix hk hvh_k hcard_k hsk_some
      dsimp only; rw [hrun_s]; refine ⟨hvh_s, hcard_s, fun r hr => ?_⟩
      have hne_d : d r ≠ d r₀ := fun heq => by
        have := congrArg Fin.val (d.injective heq); dsimp [r₀] at this; omega
      have hbr₀ : b r₀ ∈ B := by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B hB (π r₀)
      have hdr : d r ∈ D := by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem D hD (σ r)
      have hne_b : d r ≠ b r₀ := fun heq => Finset.disjoint_left.mp hBK (heq ▸ hbr₀) (hDK hdr)
      rw [Function.update_of_ne hne_b, Function.update_of_ne hne_d]
      exact hval_k r (Nat.le_of_succ_le hr)
  have hq_eq : ∀ r : Fin m,
      queryOutAt (D_det.runInterval (n + 3 * t₀) C_mix ops_B).1 r.val = some (kv (d r)).val := by
    intro r; obtain ⟨hvh_r, _, hval_r⟩ := hind r.val r.isLt.le
    set pref_r := pref_bef ++ candPrefix d b kv r.val
    have hlen_r : pref_r.length = n + 3 * t₀ + 3 * r.val := by
      rw [List.length_append, hlen_bef, length_candPrefix d b kv r.isLt.le]
    have hmem_r : (D_det.runSeq pref_r).2 =
        (D_det.runInterval (n + 3 * t₀) C_bef (candPrefix d b kv r.val)).2 := by
      rw [IndexedScheme.runSeq, IndexedScheme.runInterval_append, Nat.zero_add, hlen_bef]; rfl
    have hdec := congrFun (decodeDict_runSeq_eq (M := 4 * n) hcorr hvh_r
      (by have := r.isLt; rw [hlen_r]; omega)) (d r)
    dsimp only [decodeDict] at hdec
    rw [hout_eq, queryOutAt_runInterval D_det (n + 3 * t₀) C_bef d b kv r, ← hmem_r, ← hlen_r,
      hdec]
    exact hval_r r le_rfl
  exact ⟨⟨hcells_eq ▸ hmask, fun r => by rw [hq_eq r]; rfl⟩, hq_eq⟩

@[ext]
private structure InnerKeyConfig (U n m g : ℕ) where
  K : Finset (Fin U)
  D : Finset (Fin U)
  A : Finset (Fin U)
  B : Finset (Fin U)
  card_K : K.card = n
  D_sub : D ⊆ K
  card_D : D.card = m
  disj_AK : Disjoint A K
  card_A : A.card = m
  disj_BK : Disjoint B K
  card_B : B.card = m
  card_inter : (A ∩ B).card = g
  deriving DecidableEq

private abbrev innerKeySigma (U n m g : ℕ) :=
  Σ (K : ↥((Finset.univ : Finset (Fin U)).powersetCard n)),
    ↥(K.val.powersetCard m) ×
      Σ (A : ↥((Finset.univ \ K.val).powersetCard m)),
        ↥(((Finset.univ \ K.val).powersetCard m).filter fun B => (A.val ∩ B).card = g)

private def innerKeyEquivSigma (U n m g : ℕ) :
    InnerKeyConfig U n m g ≃ innerKeySigma U n m g where
  toFun c :=
    ⟨⟨c.K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, c.card_K⟩⟩,
      ⟨c.D, Finset.mem_powersetCard.mpr ⟨c.D_sub, c.card_D⟩⟩,
      ⟨c.A, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, c.disj_AK⟩, c.card_A⟩⟩,
      ⟨c.B, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, c.disj_BK⟩, c.card_B⟩, c.card_inter⟩⟩⟩
  invFun s :=
    match s with
    | ⟨⟨K, hK⟩, ⟨D, hD⟩, ⟨A, hA⟩, ⟨B, hB⟩⟩ =>
      let ⟨_, hKc⟩ := Finset.mem_powersetCard.mp hK
      let ⟨hDK, hDc⟩ := Finset.mem_powersetCard.mp hD
      let ⟨hAs, hAc⟩ := Finset.mem_powersetCard.mp hA
      let ⟨hBm, hBi⟩ := Finset.mem_filter.mp hB
      let ⟨hBs, hBc⟩ := Finset.mem_powersetCard.mp hBm
      ⟨K, D, A, B, hKc, hDK, hDc, (Finset.subset_sdiff.mp hAs).2, hAc,
        (Finset.subset_sdiff.mp hBs).2, hBc, hBi⟩
  left_inv c := by cases c; rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl

private instance (U n m g : ℕ) : Fintype (InnerKeyConfig U n m g) :=
  Fintype.ofEquiv (innerKeySigma U n m g) (innerKeyEquivSigma U n m g).symm

private abbrev InnerTarget (U V n m g : ℕ) :=
  Σ c : InnerKeyConfig U n m g, (↥(c.K ∪ c.B) → Fin V)

private theorem card_innerTarget (U V n m g : ℕ) (_hn : n ≤ U) :
    Fintype.card (InnerTarget U V n m g) = U.choose n * n.choose m * (U - n).choose m *
      m.choose g * (U - n - m).choose (m - g) * V ^ (n + m) := by
  have hcfg : Fintype.card (InnerKeyConfig U n m g) =
      U.choose n * n.choose m * (U - n).choose m * m.choose g * (U - n - m).choose (m - g) := by
    rw [Fintype.card_congr (innerKeyEquivSigma U n m g), Fintype.card_sigma]
    have hK (K : ↥((Finset.univ : Finset (Fin U)).powersetCard n)) :
        Fintype.card (↥(K.val.powersetCard m) × Σ (A : ↥((Finset.univ \ K.val).powersetCard m)),
          ↥(((Finset.univ \ K.val).powersetCard m).filter fun B => (A.val ∩ B).card = g)) =
        n.choose m * ((U - n).choose m * (m.choose g * (U - n - m).choose (m - g))) := by
      have hKc := (Finset.mem_powersetCard.mp K.property).2
      have hsdiff : (Finset.univ \ K.val).card = U - n := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ K.val)
        simp only [Finset.card_univ, Fintype.card_fin, hKc] at h; omega
      rw [Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard, hKc, Fintype.card_sigma]
      have hA (A : ↥((Finset.univ \ K.val).powersetCard m)) :
          Fintype.card ↥(((Finset.univ \ K.val).powersetCard m).filter
            fun B => (A.val ∩ B).card = g) = m.choose g * (U - n - m).choose (m - g) := by
        obtain ⟨hAsub, hAc⟩ := Finset.mem_powersetCard.mp A.property
        rw [Fintype.card_coe, card_inter_filter_powersetCard hAsub hAc, hsdiff]
      simp_rw [hA, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe,
        Finset.card_powersetCard, hsdiff]
    simp_rw [hK, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    ring
  rw [Fintype.card_sigma]
  have hval (c : InnerKeyConfig U n m g) : Fintype.card (↥(c.K ∪ c.B) → Fin V) = V ^ (n + m) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      Finset.card_union_of_disjoint c.disj_BK.symm, c.card_K, c.card_B]
  simp_rw [hval, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcfg]

private def InnerKeyConfig.perm {U n m g : ℕ} (τ : Equiv.Perm (Fin U))
    (c : InnerKeyConfig U n m g) : InnerKeyConfig U n m g where
  K := c.K.map τ.toEmbedding
  D := c.D.map τ.toEmbedding
  A := c.A.map τ.toEmbedding
  B := c.B.map τ.toEmbedding
  card_K := by simp [c.card_K]
  D_sub := Finset.map_subset_map.mpr c.D_sub
  card_D := by simp [c.card_D]
  disj_AK := (Finset.disjoint_map τ.toEmbedding).mpr c.disj_AK
  card_A := by simp [c.card_A]
  disj_BK := (Finset.disjoint_map τ.toEmbedding).mpr c.disj_BK
  card_B := by simp [c.card_B]
  card_inter := by rw [← Finset.map_inter, Finset.card_map, c.card_inter]

private def cfgTag {U n m g : ℕ} (c : InnerKeyConfig U n m g) (x : Fin U) :
    Bool × Bool × Bool × Bool :=
  (decide (x ∈ c.K), decide (x ∈ c.D), decide (x ∈ c.A), decide (x ∈ c.B))

private def cfgFiberCard (U n m g : ℕ) : Bool × Bool × Bool × Bool → ℕ
  | (true, true, false, false) => m
  | (true, false, false, false) => n - m
  | (false, false, true, true) => g
  | (false, false, true, false) => m - g
  | (false, false, false, true) => m - g
  | (false, false, false, false) => U - (n + (2 * m - g))
  | _ => 0

private theorem card_cfgTag_fiber {U n m g : ℕ} (c : InnerKeyConfig U n m g)
    (b : Bool × Bool × Bool × Bool) :
    Fintype.card {x : Fin U // cfgTag c x = b} = cfgFiberCard U n m g b := by
  rw [Fintype.card_subtype]
  have hDK (x : Fin U) : x ∈ c.D → x ∈ c.K := fun h => c.D_sub h
  have hAK (x : Fin U) : x ∈ c.A → x ∉ c.K := fun h => Finset.disjoint_left.mp c.disj_AK h
  have hBK (x : Fin U) : x ∈ c.B → x ∉ c.K := fun h => Finset.disjoint_left.mp c.disj_BK h
  rcases b with ⟨bK, bD, bA, bB⟩
  have hemp {b' : Bool × Bool × Bool × Bool} (hb : ∀ x, cfgTag c x = b' → False) :
      (Finset.univ.filter fun x => cfgTag c x = b').card = 0 :=
    Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun x _ => hb x)
  have hbad {b₁ b₂ b₃ b₄ : Bool}
      (hc_imp : ∀ x, (decide (x ∈ c.K) = b₁ ∧ decide (x ∈ c.D) = b₂ ∧
        decide (x ∈ c.A) = b₃ ∧ decide (x ∈ c.B) = b₄) → False) :
      (Finset.univ.filter fun x => cfgTag c x = (b₁, b₂, b₃, b₄)).card = 0 :=
    hemp fun x h => hc_imp x (by simpa only [cfgTag, Prod.mk.injEq] using h)
  cases bK <;> cases bD <;> cases bA <;> cases bB
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (false, false, false, false)) =
        Finset.univ \ (c.K ∪ (c.A ∪ c.B)) := by
      ext x; have := hDK x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag,
        Prod.mk.injEq, decide_eq_false_iff_not, Finset.mem_sdiff, Finset.mem_union]; tauto
    have huAB : (c.A ∪ c.B).card = 2 * m - g := by
      have := Finset.card_union_add_card_inter c.A c.B
      have := Finset.card_le_card (Finset.inter_subset_left (s₁ := c.A) (s₂ := c.B))
      rw [c.card_A, c.card_B, c.card_inter] at *; omega
    have hu : (c.K ∪ (c.A ∪ c.B)).card = n + (2 * m - g) := by
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_right.mpr ⟨c.disj_AK.symm, c.disj_BK.symm⟩), c.card_K, huAB]
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (c.K ∪ (c.A ∪ c.B)))
    rw [hS, cfgFiberCard]; simp only [Finset.card_univ, Fintype.card_fin, hu] at hs; omega
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (false, false, false, true)) =
        c.B \ (c.A ∩ c.B) := by
      ext x; have := hBK x; have := hDK x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag, Prod.mk.injEq,
        decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_sdiff, Finset.mem_inter]; tauto
    have hs := Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_right (s₁ := c.A) (s₂ := c.B))
    rw [hS, cfgFiberCard]; rw [c.card_inter, c.card_B] at hs; omega
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (false, false, true, false)) =
        c.A \ (c.A ∩ c.B) := by
      ext x; have := hAK x; have := hDK x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag, Prod.mk.injEq,
        decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_sdiff, Finset.mem_inter]; tauto
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := c.A) (s₂ := c.B))
    rw [hS, cfgFiberCard]; rw [c.card_inter, c.card_A] at hs; omega
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (false, false, true, true)) =
        c.A ∩ c.B := by
      ext x; have := hAK x; have := hDK x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag, Prod.mk.injEq,
        decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_inter]; tauto
    rw [hS, cfgFiberCard, c.card_inter]
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact h.1 (hDK x h.2.1)
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact h.1 (hDK x h.2.1)
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact h.1 (hDK x h.2.1)
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact h.1 (hDK x h.2.1)
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (true, false, false, false)) =
        c.K \ c.D := by
      ext x; have := hAK x; have := hBK x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag, Prod.mk.injEq,
        decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_sdiff]; tauto
    have hs := Finset.card_sdiff_add_card_eq_card c.D_sub
    rw [hS, cfgFiberCard]; rw [c.card_D, c.card_K] at hs; omega
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact hBK x h.2.2.2 h.1
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact hAK x h.2.2.1 h.1
  · exact hbad fun x h => by simp only [decide_eq_true_eq] at h; exact hAK x h.2.2.1 h.1
  · have hS : (Finset.univ.filter fun x => cfgTag c x = (true, true, false, false)) = c.D := by
      ext x; have := hDK x; have := hAK x; have := hBK x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cfgTag, Prod.mk.injEq,
        decide_eq_true_eq, decide_eq_false_iff_not]; tauto
    rw [hS, cfgFiberCard, c.card_D]
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact hBK x h.2.2.2 h.1
  · exact hbad fun x h => by
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h; exact hAK x h.2.2.1 h.1
  · exact hbad fun x h => by simp only [decide_eq_true_eq] at h; exact hAK x h.2.2.1 h.1

private theorem exists_perm_innerKeyConfig {U n m g : ℕ}
    (c₁ c₂ : InnerKeyConfig U n m g) : ∃ τ : Equiv.Perm (Fin U), c₁.perm τ = c₂ := by
  have hc (b : Bool × Bool × Bool × Bool) :
      Fintype.card {x // cfgTag c₁ x = b} = Fintype.card {x // cfgTag c₂ x = b} :=
    (card_cfgTag_fiber c₁ b).trans (card_cfgTag_fiber c₂ b).symm
  let τ : Equiv.Perm (Fin U) :=
    (Equiv.sigmaFiberEquiv (cfgTag c₁)).symm.trans
      ((Equiv.sigmaCongrRight fun b => Fintype.equivOfCardEq (hc b)).trans
        (Equiv.sigmaFiberEquiv (cfgTag c₂)))
  have htag (x : Fin U) : cfgTag c₂ (τ x) = cfgTag c₁ x :=
    ((Fintype.equivOfCardEq (hc (cfgTag c₁ x))) ⟨x, rfl⟩).property
  have hiff (y : Fin U) :
      (τ.symm y ∈ c₁.K ↔ y ∈ c₂.K) ∧ (τ.symm y ∈ c₁.D ↔ y ∈ c₂.D) ∧
        (τ.symm y ∈ c₁.A ↔ y ∈ c₂.A) ∧ (τ.symm y ∈ c₁.B ↔ y ∈ c₂.B) := by
    have h := htag (τ.symm y); rw [τ.apply_symm_apply] at h
    simpa only [cfgTag, Prod.mk.injEq, decide_eq_decide] using h.symm
  refine ⟨τ, InnerKeyConfig.ext ?_ ?_ ?_ ?_⟩
  · ext y; dsimp only [InnerKeyConfig.perm]; rw [Finset.mem_map_equiv]; exact (hiff y).1
  · ext y; dsimp only [InnerKeyConfig.perm]; rw [Finset.mem_map_equiv]; exact (hiff y).2.1
  · ext y; dsimp only [InnerKeyConfig.perm]; rw [Finset.mem_map_equiv]; exact (hiff y).2.2.1
  · ext y; dsimp only [InnerKeyConfig.perm]; rw [Finset.mem_map_equiv]; exact (hiff y).2.2.2

private def segSlotEquiv (off m N : ℕ) (h : off + m ≤ N) :
    Fin m ≃ {i : Fin N // off ≤ i.val ∧ i.val < off + m} where
  toFun r := ⟨⟨off + r.val, by have := r.isLt; omega⟩, by have := r.isLt; dsimp; omega⟩
  invFun i := ⟨i.1.val - off, by have := i.2; omega⟩
  left_inv r := Fin.ext (by dsimp; omega)
  right_inv i := Subtype.ext (Fin.ext (by have := i.2; dsimp; omega))

private def slotPerm {n : ℕ} (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (α β : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 * n)) :=
  (Equiv.Perm.ofSubtype ((segSlotEquiv t₀ m (2 * n) (by omega)).symm.trans
    (α.trans (segSlotEquiv t₀ m (2 * n) (by omega))))).trans
  (Equiv.Perm.ofSubtype ((segSlotEquiv (n + t₀) m (2 * n) (by omega)).symm.trans
    (β.trans (segSlotEquiv (n + t₀) m (2 * n) (by omega)))))

private theorem slotPerm_del {n : ℕ} (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (α β : Equiv.Perm (Fin m)) (r : Fin m) :
    slotPerm t₀ m ht α β ⟨t₀ + r.val, by have := r.isLt; omega⟩ =
      ⟨t₀ + (α r).val, by have := (α r).isLt; omega⟩ := by
  have hr := r.isLt; have hα := (α r).isLt
  dsimp only [slotPerm]; rw [Equiv.trans_apply]
  have h₁ : t₀ ≤ (⟨t₀ + r.val, by omega⟩ : Fin (2 * n)).val ∧
      (⟨t₀ + r.val, by omega⟩ : Fin (2 * n)).val < t₀ + m := by dsimp; omega
  rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun i : Fin (2 * n) => t₀ ≤ i.val ∧ i.val < t₀ + m)
    _ h₁]
  have hmid : (((segSlotEquiv t₀ m (2 * n) (by omega)).symm.trans
      (α.trans (segSlotEquiv t₀ m (2 * n) (by omega)))) ⟨⟨t₀ + r.val, by omega⟩, h₁⟩).val =
      ⟨t₀ + (α r).val, by omega⟩ := by
    apply Fin.ext; dsimp [segSlotEquiv]; congr 1
    exact congrArg Fin.val (congrArg α (Fin.ext (by dsimp; omega)))
  rw [hmid, Equiv.Perm.ofSubtype_apply_of_not_mem
    (p := fun i : Fin (2 * n) => n + t₀ ≤ i.val ∧ i.val < n + t₀ + m) _ (by dsimp; omega)]

private theorem slotPerm_ins {n : ℕ} (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (α β : Equiv.Perm (Fin m)) (r : Fin m) :
    slotPerm t₀ m ht α β ⟨n + t₀ + r.val, by have := r.isLt; omega⟩ =
      ⟨n + t₀ + (β r).val, by have := (β r).isLt; omega⟩ := by
  have hr := r.isLt; have hβ := (β r).isLt
  dsimp only [slotPerm]
  have h₁ : ¬(t₀ ≤ (⟨n + t₀ + r.val, by omega⟩ : Fin (2 * n)).val ∧
      (⟨n + t₀ + r.val, by omega⟩ : Fin (2 * n)).val < t₀ + m) := by dsimp; omega
  have h₂ : n + t₀ ≤ (⟨n + t₀ + r.val, by omega⟩ : Fin (2 * n)).val ∧
      (⟨n + t₀ + r.val, by omega⟩ : Fin (2 * n)).val < n + t₀ + m := by dsimp; omega
  rw [Equiv.trans_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun i : Fin (2 * n) => t₀ ≤ i.val ∧ i.val < t₀ + m)
      _ h₁,
    Equiv.Perm.ofSubtype_apply_of_mem
      (p := fun i : Fin (2 * n) => n + t₀ ≤ i.val ∧ i.val < n + t₀ + m) _ h₂]
  apply Fin.ext; dsimp [segSlotEquiv]; congr 1
  exact congrArg Fin.val (congrArg β (Fin.ext (by dsimp; omega)))

private theorem ofSubtype_mem_Ico {N L R : ℕ} {p : Fin N → Prop} [DecidablePred p]
    (e : Equiv.Perm {i : Fin N // p i}) {b₀ : Prop}
    (hp : ∀ i : Fin N, p i → ((L ≤ i.val ∧ i.val < R) ↔ b₀)) (i : Fin N) :
    (L ≤ (Equiv.Perm.ofSubtype e i).val ∧ (Equiv.Perm.ofSubtype e i).val < R) ↔
      (L ≤ i.val ∧ i.val < R) := by
  by_cases h : p i
  · have h' : p (Equiv.Perm.ofSubtype e i) := by
      rw [Equiv.Perm.ofSubtype_apply_of_mem e h]; exact (e ⟨i, h⟩).property
    exact (hp _ h').trans (hp _ h).symm
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem e h]

private theorem slotPerm_mem_Ico {n : ℕ} (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (α β : Equiv.Perm (Fin m)) {L R : ℕ} {b₁ b₂ : Prop}
    (h₁ : ∀ i : Fin (2 * n), t₀ ≤ i.val ∧ i.val < t₀ + m → ((L ≤ i.val ∧ i.val < R) ↔ b₁))
    (h₂ : ∀ i : Fin (2 * n), n + t₀ ≤ i.val ∧ i.val < n + t₀ + m → ((L ≤ i.val ∧ i.val < R) ↔ b₂))
    (i : Fin (2 * n)) :
    (L ≤ (slotPerm t₀ m ht α β i).val ∧ (slotPerm t₀ m ht α β i).val < R) ↔
      (L ≤ i.val ∧ i.val < R) :=
  (ofSubtype_mem_Ico _ h₂ _).trans (ofSubtype_mem_Ico _ h₁ i)

private theorem map_uniform_apply_equiv {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → β) (eΩ : Ω ≃ Ω) (eβ : β ≃ β) (hcomm : ∀ ω, f (eΩ ω) = eβ (f ω)) (b : β) :
    ((PMF.uniformOfFintype Ω).map f) (eβ b) = ((PMF.uniformOfFintype Ω).map f) b := by
  classical
  rw [_root_.PMF.map_apply, _root_.PMF.map_apply, tsum_fintype, tsum_fintype, ← eΩ.sum_comp]
  exact Finset.sum_congr rfl fun ω _ => by
    simp [PMF.uniformOfFintype_apply, hcomm ω, eβ.injective.eq_iff]

private theorem toReal_le_inv_card_of_const {β : Type*} [Fintype β] (q : PMF β)
    (hconst : ∀ y₁ y₂, (q y₁).toReal = (q y₂).toReal) (y₀ : β) :
    (q y₀).toReal ≤ (Fintype.card β : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨y₀⟩)
  have hsum := PMF.sum_toReal q
  simp_rw [fun y => hconst y y₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [inv_eq_one_div, le_div_iff₀ hpos, mul_comm, hsum]

/-- Single-segment probe-capped consistency on `HardKeyValSeed` ([LiLiangYuZhou2023], Definition 4.3
and Section 5.1, adapted with the deterministic `c = 1` probe cap `|S_A|, |S_B| ≤ m * t`). -/
@[expose] def IsSeedConsistent {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n) (γ t : ℝ) (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    Prop :=
  ∃ hB : B.card = m,
    IsCappedConsistent D_det (n + 3 * t₀) (D_det.runSeq (s.ops.take (n + 3 * t₀))).2 γ m t
      (elemSlice n 3 s.ops t₀ (t₀ + m)) (s.candidateOps t₀ m ht₀ B hB)

private def pkeyActive {U n : ℕ} (pk : Fin (2 * n) ↪ Fin U) (t₀ : ℕ) (ht : t₀ ≤ n) :
    Finset (Fin U) := Finset.univ.map (windowEmb pk t₀ ht)

private def pkeyDelEmb {U n : ℕ} (pk : Fin (2 * n) ↪ Fin U) (t₀ m : ℕ) (ht : t₀ + m ≤ n) :
    Fin m ↪ Fin U := segDeletedKeys pk (1 : Equiv.Perm (Fin n)) t₀ m ht

private def pkeyInsEmb {U n : ℕ} (pk : Fin (2 * n) ↪ Fin U) (t₀ r : ℕ) (ht : t₀ + r ≤ n) :
    Fin r ↪ Fin U :=
  ⟨fun j => pk ⟨n + t₀ + j.val, by have := j.isLt; omega⟩,
    fun j₁ j₂ h => Fin.ext (by have := congrArg Fin.val (pk.injective h); dsimp at this; omega)⟩

private theorem insertedSet_eq_pkeyInsEmb {U V n t₀ r : ℕ} (s : HardKeyValSeed U V n)
    (ht : t₀ + r ≤ n) :
    s.insertedSet t₀ r ht = Finset.univ.image (pkeyInsEmb s.permKeyEmb t₀ r ht) := by
  ext u; simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, pkeyInsEmb,
    HardKeyValSeed.permKeyEmb, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Function.Embedding.trans_apply]
  refine ⟨fun ⟨j, hj⟩ => ⟨j, ?_⟩, fun ⟨j, hj⟩ => ⟨j, ?_⟩⟩ <;>
    [rw [← hj]; rw [← hj]] <;>
    rw [liftDelPerm_apply_ge s.delPerm (by have := j.isLt; omega) (by omega)] <;>
    exact congrArg s.keys (Fin.ext (by dsimp; omega))

private theorem pkeyActive_perm_eq {U n t₀ : ℕ} (ht : t₀ ≤ n) (γp : Equiv.Perm (Fin (2 * n)))
    (hγ : ∀ i : Fin (2 * n),
      (t₀ ≤ (γp i).val ∧ (γp i).val < t₀ + n) ↔ (t₀ ≤ i.val ∧ i.val < t₀ + n))
    (pk : Fin (2 * n) ↪ Fin U) :
    pkeyActive (γp.toEmbedding.trans pk) t₀ ht = pkeyActive pk t₀ ht := by
  ext u; simp only [pkeyActive, Finset.mem_map, Finset.mem_univ, true_and, windowEmb_apply,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨k, rfl⟩
    have hi : t₀ ≤ (γp ⟨t₀ + k.val, by have := k.isLt; omega⟩).val ∧
        (γp ⟨t₀ + k.val, by have := k.isLt; omega⟩).val < t₀ + n :=
      (hγ _).mpr (by have := k.isLt; dsimp; omega)
    exact ⟨⟨(γp ⟨t₀ + k.val, by have := k.isLt; omega⟩).val - t₀, by omega⟩,
      congrArg pk (Fin.ext (by dsimp; omega))⟩
  · rintro ⟨k, rfl⟩
    let j : Fin (2 * n) := γp.symm ⟨t₀ + k.val, by have := k.isLt; omega⟩
    have hj : t₀ ≤ j.val ∧ j.val < t₀ + n := by
      rw [← hγ j]; dsimp [j]; rw [Equiv.apply_symm_apply]; have := k.isLt; dsimp; omega
    refine ⟨⟨j.val - t₀, by omega⟩, ?_⟩
    have heq : (⟨t₀ + (j.val - t₀), by omega⟩ : Fin (2 * n)) = j := Fin.ext (by dsimp; omega)
    rw [heq]; dsimp [j]; rw [Equiv.apply_symm_apply]

open Classical in
private noncomputable def innerPoolDist {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (F : HardKeyValSeed U V n → Finset (Finset (Fin U))) (hne : ∀ s, (F s).Nonempty) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  (PMF.uniformOfFintype (HardKeyValSeed U V n)).bind fun s =>
    letI : Nonempty ↥(F s) := (hne s).to_subtype
    (PMF.uniformOfFintype ↥(F s)).map fun B => (s, B.val)

open Classical in
private theorem prob_innerPoolDist_eq {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (F : HardKeyValSeed U V n → Finset (Finset (Fin U))) {C : ℕ}
    (hC : ∀ s, (F s).card = C) (hne : ∀ s, (F s).Nonempty)
    (ev : HardKeyValSeed U V n → Finset (Fin U) → Prop) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    (((innerPoolDist hU hV F hne).map fun sb => decide (ev sb.1 sb.2)) true).toReal =
      (C : ℝ)⁻¹ * ∑ s, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        (((F s).filter (ev s)).card : ℝ) := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  rw [innerPoolDist, _root_.PMF.map_bind, PMF.bind_apply_toReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : Nonempty ↥(F s) := (hne s).to_subtype
  rw [_root_.PMF.map_comp, PMF.map_apply_toReal]
  have hinner : (∑ b : ↥(F s),
      if true = decide (ev s b.val) then ((PMF.uniformOfFintype ↥(F s)) b).toReal else 0) =
      (C : ℝ)⁻¹ * (((F s).filter (ev s)).card : ℝ) := by
    simp only [PMF.uniformOfFintype_apply, Fintype.card_coe, hC s, ENNReal.toReal_inv,
      true_eq_decide_iff]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]; congr 1
    exact_mod_cast Finset.card_bij (fun (b : ↥(F s)) _ => b.val)
      (fun b hb => Finset.mem_filter.mpr ⟨b.property, (Finset.mem_filter.mp hb).2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun B hB => ⟨⟨B, (Finset.mem_filter.mp hB).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hB).2⟩, rfl⟩)
  dsimp only [Function.comp_def]; rw [hinner]; ring

open Classical in
private theorem toReal_innerPoolDist_apply {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (F : HardKeyValSeed U V n → Finset (Finset (Fin U))) (hne : ∀ s, (F s).Nonempty)
    (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    ((innerPoolDist hU hV F hne) (s, B)).toReal =
      if B ∈ F s then
        ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal / ((F s).card : ℝ)
      else 0 := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  rw [innerPoolDist, PMF.bind_apply_toReal]
  have hs : ∑ s' : HardKeyValSeed U V n,
      ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s').toReal *
        (((haveI : Nonempty ↥(F s') := (hne s').to_subtype
           (PMF.uniformOfFintype ↥(F s')).map fun b => (s', b.val)) (s, B)).toReal) =
      ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        (((haveI : Nonempty ↥(F s) := (hne s).to_subtype
           (PMF.uniformOfFintype ↥(F s)).map fun b => (s, b.val)) (s, B)).toReal) := by
    refine Finset.sum_eq_single s (fun s' _ hs' => ?_) (fun h => absurd (Finset.mem_univ s) h)
    have : Nonempty ↥(F s') := (hne s').to_subtype
    rw [PMF.map_apply_toReal]
    have h0 : (∑ b : ↥(F s'),
        if (s, B) = (s', b.val) then ((PMF.uniformOfFintype ↥(F s')) b).toReal else 0) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne_pair : (s, B) ≠ (s', b.val) := fun heq => hs' (Prod.mk.inj heq).1.symm
      simp [hne_pair]
    rw [h0, mul_zero]
  rw [hs]
  have : Nonempty ↥(F s) := (hne s).to_subtype
  rw [PMF.map_apply_toReal]
  by_cases hB : B ∈ F s
  · simp only [hB, ↓reduceIte]
    rw [Finset.sum_eq_single ⟨B, hB⟩]
    · simp [PMF.uniformOfFintype_apply, Fintype.card_coe, div_eq_mul_inv]
    · intro b _ hb
      have hne_pair : (s, B) ≠ (s, b.val) := fun heq => hb (Subtype.ext (Prod.mk.inj heq).2.symm)
      simp [hne_pair]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hB, ↓reduceIte]
    have h0 : (∑ b : ↥(F s),
        if (s, B) = (s, b.val) then ((PMF.uniformOfFintype ↥(F s)) b).toReal else 0) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne_pair : (s, B) ≠ (s, b.val) := fun heq => by
        have hBeq : B = b.val := (Prod.mk.inj heq).2
        exact hB (hBeq ▸ b.property)
      simp [hne_pair]
    rw [h0, mul_zero]

private def IsSlotPerm {n : ℕ} (t₀ m : ℕ) (γp : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i : Fin (2 * n), (t₀ ≤ (γp i).val ∧ (γp i).val < t₀ + m) ↔ (t₀ ≤ i.val ∧ i.val < t₀ + m)) ∧
    (∀ i : Fin (2 * n),
      (n + t₀ ≤ (γp i).val ∧ (γp i).val < n + t₀ + m) ↔ (n + t₀ ≤ i.val ∧ i.val < n + t₀ + m)) ∧
    ∀ i : Fin (2 * n), ¬(t₀ ≤ i.val ∧ i.val < t₀ + m) →
      ¬(n + t₀ ≤ i.val ∧ i.val < n + t₀ + m) → γp i = i

private theorem IsSlotPerm.symm {n t₀ m : ℕ} {γp : Equiv.Perm (Fin (2 * n))}
    (h : IsSlotPerm t₀ m γp) : IsSlotPerm t₀ m γp.symm :=
  ⟨fun i => by have h1 := h.1 (γp.symm i); rw [Equiv.apply_symm_apply] at h1; exact h1.symm,
    fun i => by have h2 := h.2.1 (γp.symm i); rw [Equiv.apply_symm_apply] at h2; exact h2.symm,
    fun i hn1 hn2 => (h.2.2 (γp.symm i) (by rwa [← h.1, Equiv.apply_symm_apply])
      (by rwa [← h.2.1, Equiv.apply_symm_apply])).symm.trans (Equiv.apply_symm_apply γp i)⟩

private theorem isSlotPerm_slotPerm {n : ℕ} (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (α β : Equiv.Perm (Fin m)) : IsSlotPerm t₀ m (slotPerm t₀ m ht α β) :=
  ⟨slotPerm_mem_Ico t₀ m ht α β (b₁ := True) (b₂ := False)
      (fun _ h => iff_of_true h trivial) (fun _ h => iff_of_false (by omega) not_false),
    slotPerm_mem_Ico t₀ m ht α β (b₁ := False) (b₂ := True)
      (fun _ h => iff_of_false (by omega) not_false) (fun _ h => iff_of_true h trivial),
    fun i hn1 hn2 => by
      dsimp only [slotPerm]
      rw [Equiv.trans_apply,
        Equiv.Perm.ofSubtype_apply_of_not_mem
          (p := fun j : Fin (2 * n) => t₀ ≤ j.val ∧ j.val < t₀ + m) _ hn1,
        Equiv.Perm.ofSubtype_apply_of_not_mem
          (p := fun j : Fin (2 * n) => n + t₀ ≤ j.val ∧ j.val < n + t₀ + m) _ hn2]⟩

private theorem sdiff_union_sdiff_cancel {α : Type*} [DecidableEq α] {K D A : Finset α}
    (hDK : D ⊆ K) (hAK : Disjoint A K) : (((K \ D) ∪ A) \ A) ∪ D = K := by
  ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
  have h1 : x ∈ A → x ∉ K := fun h => Finset.disjoint_left.mp hAK h
  have h2 : x ∈ D → x ∈ K := fun h => hDK h
  tauto

private theorem innerTarget_mk_eq {U V n m g : ℕ} {c₁ c₂ : InnerKeyConfig U n m g}
    {kv₁ kv₂ : Fin U → Fin V} (hc : c₁ = c₂) (hv : ∀ u ∈ c₁.K ∪ c₁.B, kv₁ u = kv₂ u) :
    (⟨c₁, fun u => kv₁ u.val⟩ : InnerTarget U V n m g) = ⟨c₂, fun u => kv₂ u.val⟩ := by
  subst hc; exact congrArg (Sigma.mk c₁) (funext fun ⟨u, hu⟩ => hv u hu)

private theorem logb_card_innerTarget {U V n m g : ℕ} (hU : 4 * n ≤ U) (hV : 1 ≤ V)
    (hm_n : 2 * m ≤ n) (hg : g < m / 2) :
    Real.logb 2 (Fintype.card (InnerTarget U V n m g)) =
      Real.logb 2 (U.choose n) + Real.logb 2 (n.choose m) + Real.logb 2 ((U - n).choose m) +
        Real.logb 2 (m.choose g) + Real.logb 2 ((U - n - m).choose (m - g)) +
        ((n + m : ℕ) : ℝ) * Real.logb 2 V := by
  rw [card_innerTarget U V n m g (by omega)]
  have hc1 : (0 : ℝ) < (U.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc3 : (0 : ℝ) < ((U - n).choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc4 : (0 : ℝ) < (m.choose g : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc5 : (0 : ℝ) < ((U - n - m).choose (m - g) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hcV : (0 : ℝ) < (V : ℝ) ^ (n + m) := pow_pos (by exact_mod_cast hV) _
  push_cast
  rw [Real.logb_mul (by positivity) hcV.ne', Real.logb_mul (by positivity) hc5.ne',
    Real.logb_mul (by positivity) hc4.ne', Real.logb_mul (by positivity) hc3.ne',
    Real.logb_mul hc1.ne' hc2.ne', Real.logb_pow]
  push_cast; ring

private theorem log_innerPool_budget_le {U V n m g w : ℕ} {γ R t pW : ℝ}
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm_n : 2 * m ≤ n) (hg : g < m / 2)
    (hγ : 0 < γ) (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (m : ℝ))
    (hbudget : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      (3 / 2) * γ * (m : ℝ) * Real.logb 2 U ≤ ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    (hpW_pos : 0 < pW)
    (hineq : Real.logb 2 pW + Real.logb 2 (Fintype.card (InnerTarget U V n m g)) ≤
      Real.logb 2 (U.choose m) + Real.logb 2 (U.choose n) + ((n + m : ℕ) : ℝ) * Real.logb 2 V +
        R + Real.logb 2 ((n + m).choose m) + Real.logb 2 (n.choose m) +
        6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + 11) :
    pW ≤ (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have hlog_tgt := logb_card_innerTarget hU hV hm_n hg
  have h_mg : (0 : ℝ) ≤ Real.logb 2 (m.choose g) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.choose_pos (by omega))
  have h_Um : Real.logb 2 (U.choose m) - Real.logb 2 ((U - n).choose m) ≤ (m : ℝ) :=
    logb_choose_sub_logb_choose_sub_le (by omega) (by omega)
  have h_Umg1 : Real.logb 2 ((U - m).choose (m - g)) -
      Real.logb 2 ((U - n - m).choose (m - g)) ≤ ((m - g : ℕ) : ℝ) := by
    simpa [Nat.sub_right_comm U m n] using
      logb_choose_sub_logb_choose_sub_le (U := U - m) (d := n) (k := m - g) (by omega) (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
  have h_Umg2 : ((m - g : ℕ) : ℝ) * (Real.logb 2 U - 1 - Real.logb 2 m) ≤
      Real.logb 2 ((U - m).choose (m - g)) := by
    have h1 := mul_logb_div_le_logb_choose (k := m - g) (N := U - m) (by omega) (by omega)
    have hmg_pos : (0 : ℝ) < ((m - g : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - g by omega)
    have h2 : (U : ℝ) / (2 * (m : ℝ)) ≤ ((U - m : ℕ) : ℝ) / ((m - g : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hmg_pos]
      have hUm_ge : (U : ℝ) ≤ 2 * ((U - m : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        have : (2 : ℝ) * (m : ℝ) ≤ (U : ℝ) := by exact_mod_cast (show 2 * m ≤ U by omega)
        linarith
      have hmg_le : ((m - g : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m g
      calc (U : ℝ) * ((m - g : ℕ) : ℝ)
          ≤ (2 * ((U - m : ℕ) : ℝ)) * (m : ℝ) :=
            mul_le_mul hUm_ge hmg_le (Nat.cast_nonneg _) (by positivity)
        _ = ((U - m : ℕ) : ℝ) * (2 * (m : ℝ)) := by ring
    have hlog2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h2
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by norm_num) hm_pos.ne',
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog2
    exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (m - g))).trans h1
  have h_nm : Real.logb 2 ((n + m).choose m) ≤
      (m : ℝ) * Real.logb 2 n - (m : ℝ) * Real.logb 2 m + 3 * (m : ℝ) := by
    have h := logb_add_choose_le (n := n) (m := m) (by omega) (by omega)
    rw [Real.logb_div hn_pos.ne' hm_pos.ne'] at h; linarith
  have hm_ge_half : ((m : ℝ) / 2) ≤ ((m - g : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have : (2 : ℝ) * (g : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (show 2 * g + 1 ≤ m by omega)
    linarith
  have hlog_Um_ge : 0 ≤ Real.logb 2 U - 1 - Real.logb 2 m := by
    have h4m : 4 * (m : ℝ) ≤ (U : ℝ) := by exact_mod_cast (show 4 * m ≤ U by omega)
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h4m
    rw [Real.logb_mul (by norm_num) hm_pos.ne', show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hl
    norm_num at hl; linarith
  have hhalf_Umg : (1 / 2) * ((m : ℝ) * Real.logb 2 U) - (1 / 2) * (m : ℝ) -
      (1 / 2) * ((m : ℝ) * Real.logb 2 m) ≤ Real.logb 2 ((U - m).choose (m - g)) := by
    calc (1 / 2) * ((m : ℝ) * Real.logb 2 U) - (1 / 2) * (m : ℝ) -
          (1 / 2) * ((m : ℝ) * Real.logb 2 m)
        = ((m : ℝ) / 2) * (Real.logb 2 U - 1 - Real.logb 2 m) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hm_ge_half hlog_Um_ge).trans h_Umg2
  have hlog_m_ge : (1 - γ / 2) * Real.logb 2 n ≤ Real.logb 2 m := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (Real.rpow_pos_of_pos hn_pos _) hm_lo
    rwa [Real.logb_rpow_eq_mul_logb_of_pos hn_pos] at hl
  have hm_logm : (1 / 2) * ((m : ℝ) * Real.logb 2 n) - (1 / 4) * (γ * (m : ℝ) * Real.logb 2 n) ≤
      (1 / 2) * ((m : ℝ) * Real.logb 2 m) := by
    calc (1 / 2) * ((m : ℝ) * Real.logb 2 n) - (1 / 4) * (γ * (m : ℝ) * Real.logb 2 n)
        = ((m : ℝ) / 2) * ((1 - γ / 2) * Real.logb 2 n) := by ring
      _ ≤ ((m : ℝ) / 2) * Real.logb 2 m := mul_le_mul_of_nonneg_left hlog_m_ge (by positivity)
      _ = (1 / 2) * ((m : ℝ) * Real.logb 2 m) := by ring
  have hlog_Un : Real.logb 2 ((U : ℝ) / (n : ℝ)) = Real.logb 2 U - Real.logb 2 n :=
    Real.logb_div hU_pos.ne' hn_pos.ne'
  have hbudget' : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      (3 / 2) * (γ * (m : ℝ) * Real.logb 2 U) ≤
      (1 / 2) * ((m : ℝ) * Real.logb 2 U) - (1 / 2) * ((m : ℝ) * Real.logb 2 n) :=
    calc R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
          (3 / 2) * (γ * (m : ℝ) * Real.logb 2 U)
        = R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
          (3 / 2) * γ * (m : ℝ) * Real.logb 2 U := by ring
      _ ≤ ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := hbudget
      _ = (1 / 2) * ((m : ℝ) * Real.logb 2 U) - (1 / 2) * ((m : ℝ) * Real.logb 2 n) := by
          rw [hlog_Un]; ring
  have hlog_nU : Real.logb 2 n ≤ Real.logb 2 U :=
    Real.logb_le_logb_of_le (by norm_num) hn_pos (by exact_mod_cast (show n ≤ U by omega))
  have hlogU_nn : 0 ≤ Real.logb 2 U :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ U by omega))
  have hγ_nU : (1 / 4) * (γ * (m : ℝ) * Real.logb 2 n) ≤
      (1 / 2) * (γ * (m : ℝ) * Real.logb 2 U) := by
    have h1 := mul_le_mul_of_nonneg_left hlog_nU (show 0 ≤ (1 / 4) * (γ * (m : ℝ)) by positivity)
    have h2 := mul_le_mul_of_nonneg_right
      (show (1 / 4) * (γ * (m : ℝ)) ≤ (1 / 2) * (γ * (m : ℝ)) by linarith [mul_pos hγ hm_pos])
      hlogU_nn
    linarith [show (1 / 4) * (γ * (m : ℝ)) * Real.logb 2 n =
      (1 / 4) * (γ * (m : ℝ) * Real.logb 2 n) by ring,
      show (1 / 4) * (γ * (m : ℝ)) * Real.logb 2 U =
      (1 / 4) * (γ * (m : ℝ) * Real.logb 2 U) by ring,
      show (1 / 2) * (γ * (m : ℝ)) * Real.logb 2 U =
      (1 / 2) * (γ * (m : ℝ) * Real.logb 2 U) by ring]
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
  have hmg_le_m : ((m - g : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m g
  have hlog_pW : Real.logb 2 pW ≤ (-γ * (m : ℝ)) * Real.logb 2 U := by
    have hlin : Real.logb 2 pW ≤ -(γ * (m : ℝ) * Real.logb 2 U) := by
      linarith [hineq, hlog_tgt, h_mg, h_Um, h_Umg1, hhalf_Umg, h_nm, hm_logm, hbudget', hγ_nU,
        hm_ge2, hmg_le_m]
    exact hlin.trans_eq (by ring)
  rw [← Real.logb_rpow_eq_mul_logb_of_pos hU_pos] at hlog_pW
  have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlog_pW
  rwa [Real.rpow_logb (by norm_num) (by norm_num) hpW_pos,
    Real.rpow_logb (by norm_num) (by norm_num) (Real.rpow_pos_of_pos hU_pos _)] at hrpow

open Classical in
private theorem prob_innerPool_eq_le {U V n t₀ m g cells w : ℕ} {γ R t : ℝ}
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm_n : 2 * m ≤ n) (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (hγ : 0 < γ) (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (m : ℝ))
    (hspace : ((cells * w : ℕ) : ℝ) ≤ Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 V + R)
    (hbudget : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      (3 / 2) * γ * (m : ℝ) * Real.logb 2 U ≤ ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (poolPk : (Fin (2 * n) ↪ Fin U) → Finset (Fin U)) {P : ℕ}
    (hcard_pool : ∀ pk, (poolPk pk).card = P)
    (hA_pool : ∀ pk, Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ poolPk pk)
    (hdisj_pool : ∀ pk, Disjoint (poolPk pk) (pkeyActive pk t₀ (by omega)))
    (hslot_pool : ∀ γp, IsSlotPerm t₀ m γp → ∀ pk, poolPk (γp.toEmbedding.trans pk) = poolPk pk)
    (huniv_pool : ∀ (τ : Equiv.Perm (Fin U)) pk,
      poolPk (pk.trans τ.toEmbedding) = (poolPk pk).map τ.toEmbedding)
    (_hP_ge : 2 * m - g ≤ P) :
    let F_s : HardKeyValSeed U V n → Finset (Finset (Fin U)) := fun s =>
      ((poolPk s.permKeyEmb).powersetCard m).filter fun B => (s.insertedSet t₀ m ht₀ ∩ B).card = g
    ∀ hne : ∀ s, (F_s s).Nonempty,
      (((innerPoolDist (by omega) hV F_s hne).map fun sb =>
        decide (IsSeedConsistent D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
        (U : ℝ) ^ (-γ * (m : ℝ)) := by
  dsimp only; intro hne
  set F_s : HardKeyValSeed U V n → Finset (Finset (Fin U)) := fun s =>
    ((poolPk s.permKeyEmb).powersetCard m).filter fun B => (s.insertedSet t₀ m ht₀ ∩ B).card = g
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let F_pk (pk : Fin (2 * n) ↪ Fin U) : Finset (Finset (Fin U)) :=
    ((poolPk pk).powersetCard m).filter fun B =>
      (Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ∩ B).card = g
  have hins_eq (s : HardKeyValSeed U V n) :
      segInsertedKeys s.keys t₀ m ht₀ = pkeyInsEmb s.permKeyEmb t₀ m ht₀ := by
    apply Function.Embedding.ext; intro r; have := r.isLt
    simp only [pkeyInsEmb, HardKeyValSeed.permKeyEmb, segInsertedKeys_apply,
      Function.Embedding.coeFn_mk, Function.Embedding.trans_apply]
    rw [liftDelPerm_apply_ge s.delPerm (by omega) (by omega)]
    exact congrArg s.keys (Fin.ext (by dsimp; omega))
  have hdel_eq (s : HardKeyValSeed U V n) :
      segDeletedKeys s.keys s.delPerm t₀ m ht₀ = pkeyDelEmb s.permKeyEmb t₀ m ht₀ := by
    apply Function.Embedding.ext; intro r; have := r.isLt
    simp only [pkeyDelEmb, HardKeyValSeed.permKeyEmb, segDeletedKeys_apply, Equiv.Perm.coe_one,
      id_eq, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [liftDelPerm_apply_lt s.delPerm (by omega)]
  have hFs_eq (s : HardKeyValSeed U V n) : F_s s = F_pk s.permKeyEmb := by
    simp only [F_s, F_pk, insertedSet_eq_pkeyInsEmb]
  set cg := m.choose g * (P - m).choose (m - g)
  have hcard_Fpk (pk : Fin (2 * n) ↪ Fin U) : (F_pk pk).card = cg := by
    rw [card_inter_filter_powersetCard (hA_pool pk)
      (by simp [Finset.card_image_of_injective _ (pkeyInsEmb pk t₀ m ht₀).injective]), hcard_pool]
  let Ω := Σ s : HardKeyValSeed U V n, ↥(F_s s)
  have : Nonempty Ω := ⟨⟨Classical.arbitrary _, ⟨(hne _).choose, (hne _).choose_spec⟩⟩⟩
  have omega_ext {s₁ s₂ : HardKeyValSeed U V n} {b₁ : ↥(F_s s₁)} {b₂ : ↥(F_s s₂)}
      (hs : s₁ = s₂) (hb : b₁.val = b₂.val) : (⟨s₁, b₁⟩ : Ω) = ⟨s₂, b₂⟩ := by
    cases hs; exact congrArg (Sigma.mk s₁) (Subtype.ext hb)
  let μ : PMF Ω := PMF.uniformOfFintype Ω
  let cfgOfPk (pk : Fin (2 * n) ↪ Fin U) (B : ↥(F_pk pk)) : InnerKeyConfig U n m g :=
    have hBm := Finset.mem_filter.mp B.property
    have hBp := Finset.mem_powersetCard.mp hBm.1
    { K := pkeyActive pk t₀ (by omega), D := Finset.univ.image (pkeyDelEmb pk t₀ m ht₀)
      A := Finset.univ.image (pkeyInsEmb pk t₀ m ht₀), B := B.val
      card_K := by simp [pkeyActive]
      D_sub := fun u hu => by
        simp only [pkeyDelEmb, pkeyActive, Finset.mem_image, Finset.mem_map, Finset.mem_univ,
          true_and, segDeletedKeys_apply, windowEmb_apply, Equiv.Perm.coe_one, id_eq] at hu ⊢
        obtain ⟨r, rfl⟩ := hu; exact ⟨⟨r.val, by have := r.isLt; omega⟩, rfl⟩
      card_D := by simp [Finset.card_image_of_injective _ (pkeyDelEmb pk t₀ m ht₀).injective]
      disj_AK := Finset.disjoint_of_subset_left (hA_pool pk) (hdisj_pool pk)
      card_A := by simp [Finset.card_image_of_injective _ (pkeyInsEmb pk t₀ m ht₀).injective]
      disj_BK := Finset.disjoint_of_subset_left hBp.1 (hdisj_pool pk)
      card_B := hBp.2, card_inter := hBm.2 }
  let cfg (ω : Ω) : InnerKeyConfig U n m g :=
    cfgOfPk ω.1.permKeyEmb ⟨ω.2.val, hFs_eq ω.1 ▸ ω.2.property⟩
  let π (ω : Ω) : Equiv.Perm (Fin m) :=
    (embSetPermEquiv (Fin U) m (segInsertedKeys ω.1.keys t₀ m ht₀)).2
  let σ (ω : Ω) : Equiv.Perm (Fin m) :=
    (embSetPermEquiv (Fin U) m (segDeletedKeys ω.1.keys ω.1.delPerm t₀ m ht₀)).2
  let pref_bef (ω : Ω) : List (Dynamic.Op U) := ω.1.ops.take (n + 3 * t₀)
  have hod_eq (ω : Ω) : orderSubset (cfg ω).D (cfg ω).card_D (σ ω) =
      segDeletedKeys ω.1.keys ω.1.delPerm t₀ m ht₀ :=
    orderSubset_eq_of_embSetPermEquiv_fst
      (Subtype.ext (by rw [embSetPermEquiv_fst]; dsimp [cfg, cfgOfPk]; rw [hdel_eq]))
  have hoa_eq (ω : Ω) :
      orderSubset (cfg ω).A (cfg ω).card_A (π ω) = segInsertedKeys ω.1.keys t₀ m ht₀ :=
    orderSubset_eq_of_embSetPermEquiv_fst
      (Subtype.ext (by rw [embSetPermEquiv_fst]; dsimp [cfg, cfgOfPk]; rw [hins_eq]))
  let ObsT := Equiv.Perm (Fin m) × Equiv.Perm (Fin m)
  let TgtT := InnerTarget U V n m g
  let obs (ω : Ω) : ObsT := (π ω, σ ω)
  let target (ω : Ω) : TgtT := ⟨cfg ω, fun u => ω.1.kv u.val⟩
  let g_ot (ω : Ω) : ObsT × TgtT := (obs ω, target ω)
  let q : PMF (ObsT × TgtT) := μ.map g_ot
  have hmass : ∀ ot, (q ot).toReal ≤ (Fintype.card (ObsT × TgtT) : ℝ)⁻¹ := by
    have hval_eq (o₀ : ObsT) (c₀ : InnerKeyConfig U n m g) (v₁ v₂ : ↥(c₀.K ∪ c₀.B) → Fin V) :
        q (o₀, ⟨c₀, v₂⟩) = q (o₀, ⟨c₀, v₁⟩) := by
      let ψ (u : Fin U) : Equiv.Perm (Fin V) :=
        if hu : u ∈ c₀.K ∪ c₀.B then Equiv.swap (v₁ ⟨u, hu⟩) (v₂ ⟨u, hu⟩) else Equiv.refl _
      let valSeed (s : HardKeyValSeed U V n) : HardKeyValSeed U V n :=
        ⟨s.keys, fun u => ψ u (s.kv u), s.delPerm⟩
      have hv_inv (s : HardKeyValSeed U V n) : valSeed (valSeed s) = s :=
        HardKeyValSeed.ext rfl (funext fun u => by
          dsimp [valSeed, ψ]; split_ifs <;> simp [Equiv.swap_apply_self]) rfl
      let eΩ₁ : Ω ≃ Ω :=
        { toFun := fun ⟨s, b⟩ => ⟨valSeed s, b⟩, invFun := fun ⟨s, b⟩ => ⟨valSeed s, b⟩
          left_inv := fun ⟨s, _⟩ => omega_ext (hv_inv s) rfl
          right_inv := fun ⟨s, _⟩ => omega_ext (hv_inv s) rfl }
      let eβ₁ : (ObsT × TgtT) ≃ (ObsT × TgtT) :=
        Equiv.prodCongr (Equiv.refl ObsT)
          (Equiv.sigmaCongrRight fun c => Equiv.piCongrRight fun u : ↥(c.K ∪ c.B) => ψ u.val)
      have hcomm (ω : Ω) : g_ot (eΩ₁ ω) = eβ₁ (g_ot ω) := by rcases ω with ⟨_, _⟩; rfl
      have hb : eβ₁ (o₀, ⟨c₀, v₁⟩) = (o₀, ⟨c₀, v₂⟩) := by
        change (o₀, (⟨c₀, fun u : ↥(c₀.K ∪ c₀.B) => ψ u.val (v₁ u)⟩ : TgtT)) =
          (o₀, (⟨c₀, v₂⟩ : TgtT))
        congr 2; funext ⟨u, hu⟩; dsimp [ψ]; simp only [hu, ↓reduceDIte, Equiv.swap_apply_left]
      rw [← hb]; exact map_uniform_apply_equiv g_ot eΩ₁ eβ₁ hcomm (o₀, ⟨c₀, v₁⟩)
    have hslot_eq (o₁ o₂ : ObsT) (tgt : TgtT) : q (o₂, tgt) = q (o₁, tgt) := by
      let α := o₂.2.trans o₁.2.symm; let β := o₂.1.trans o₁.1.symm
      let γ_sl := slotPerm t₀ m ht₀ α β
      have hγ_sl : IsSlotPerm t₀ m γ_sl := isSlotPerm_slotPerm t₀ m ht₀ α β
      have himg_perm (γp : Equiv.Perm (Fin m)) (f : Fin m ↪ Fin U) :
          Finset.univ.image (γp.toEmbedding.trans f) = Finset.univ.image f ∧
            (embSetPermEquiv (Fin U) m (γp.toEmbedding.trans f)).2 =
              γp.trans (embSetPermEquiv (Fin U) m f).2 :=
        ⟨image_perm_trans γp f, embSetPermEquiv_perm_trans γp f⟩
      let slSeed (γp : Equiv.Perm (Fin (2 * n))) (s : HardKeyValSeed U V n) :
          HardKeyValSeed U V n :=
        ⟨((liftDelPerm s.delPerm).symm.trans (γp.trans (liftDelPerm s.delPerm))).toEmbedding.trans
          s.keys, s.kv, s.delPerm⟩
      have hsl_pk (γp : Equiv.Perm (Fin (2 * n))) (s : HardKeyValSeed U V n) :
          (slSeed γp s).permKeyEmb = γp.toEmbedding.trans s.permKeyEmb := by
        apply Function.Embedding.ext; intro i
        change s.keys ((liftDelPerm s.delPerm) (γp
          ((liftDelPerm s.delPerm).symm ((liftDelPerm s.delPerm) i)))) =
          s.keys ((liftDelPerm s.delPerm) (γp i))
        rw [Equiv.symm_apply_apply]
      have hsl_inv (γp : Equiv.Perm (Fin (2 * n))) (s : HardKeyValSeed U V n) :
          slSeed γp.symm (slSeed γp s) = s :=
        HardKeyValSeed.ext (Function.Embedding.ext fun i => by
          change s.keys ((liftDelPerm s.delPerm) (γp
            ((liftDelPerm s.delPerm).symm ((liftDelPerm s.delPerm)
              (γp.symm ((liftDelPerm s.delPerm).symm i)))))) = s.keys i
          rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]) rfl rfl
      have hFs_sl (γp : Equiv.Perm (Fin (2 * n))) (hγ : IsSlotPerm t₀ m γp)
          (s : HardKeyValSeed U V n) {B : Finset (Fin U)} (hB : B ∈ F_s s) :
          B ∈ F_s (slSeed γp s) := by
        rw [hFs_eq] at hB ⊢; rw [hsl_pk]
        obtain ⟨hBp, hBi⟩ := Finset.mem_filter.mp hB
        have hsub (δ : Equiv.Perm (Fin (2 * n))) (hδ : IsSlotPerm t₀ m δ)
            (pk : Fin (2 * n) ↪ Fin U) :
            Finset.univ.image (pkeyInsEmb (δ.toEmbedding.trans pk) t₀ m ht₀) ⊆
              Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) := fun u hu => by
          simp only [pkeyInsEmb, Finset.mem_image, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk, Function.Embedding.trans_apply] at hu ⊢
          obtain ⟨r, rfl⟩ := hu
          have hj := (hδ.2.1 ⟨n + t₀ + r.val, by have := r.isLt; omega⟩).mpr
            (by have := r.isLt; dsimp; omega)
          exact ⟨⟨(δ ⟨n + t₀ + r.val, by have := r.isLt; omega⟩).val - (n + t₀), by omega⟩,
            congrArg pk (Fin.ext (by change n + t₀ + (_ - (n + t₀)) = _; omega))⟩
        have hA_eq : Finset.univ.image (pkeyInsEmb (γp.toEmbedding.trans s.permKeyEmb) t₀ m ht₀) =
            Finset.univ.image (pkeyInsEmb s.permKeyEmb t₀ m ht₀) :=
          Finset.Subset.antisymm (hsub γp hγ s.permKeyEmb) (by
            have h2 := hsub γp.symm hγ.symm (γp.toEmbedding.trans s.permKeyEmb)
            have heq : γp.symm.toEmbedding.trans (γp.toEmbedding.trans s.permKeyEmb) =
                s.permKeyEmb := by ext i; simp
            rwa [heq] at h2)
        exact Finset.mem_filter.mpr ⟨by rwa [hslot_pool γp hγ s.permKeyEmb], by rwa [hA_eq]⟩
      let eΩ₂ : Ω ≃ Ω :=
        { toFun := fun ⟨s, ⟨B, hB⟩⟩ => ⟨slSeed γ_sl s, ⟨B, hFs_sl γ_sl hγ_sl s hB⟩⟩
          invFun := fun ⟨s, ⟨B, hB⟩⟩ =>
            ⟨slSeed γ_sl.symm s, ⟨B, hFs_sl γ_sl.symm hγ_sl.symm s hB⟩⟩
          left_inv := fun ⟨s, _⟩ => omega_ext (hsl_inv γ_sl s) rfl
          right_inv := fun ⟨s, _⟩ => omega_ext (by simpa using hsl_inv γ_sl.symm s) rfl }
      let transLeft (δ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) :=
        { toFun := fun p => δ.trans p, invFun := fun p => δ.symm.trans p
          left_inv := fun p => by ext r; simp
          right_inv := fun p => by ext r; simp }
      let eβ₂ : (ObsT × TgtT) ≃ (ObsT × TgtT) :=
        Equiv.prodCongr (Equiv.prodCongr (transLeft β) (transLeft α)) (Equiv.refl TgtT)
      have hcomm (ω : Ω) : g_ot (eΩ₂ ω) = eβ₂ (g_ot ω) := by
        rcases ω with ⟨s, ⟨B, hB⟩⟩
        have hdel_s : pkeyDelEmb (γ_sl.toEmbedding.trans s.permKeyEmb) t₀ m ht₀ =
            α.toEmbedding.trans (pkeyDelEmb s.permKeyEmb t₀ m ht₀) := by
          apply Function.Embedding.ext; intro r
          simp only [pkeyDelEmb, segDeletedKeys_apply, Equiv.Perm.coe_one, id_eq,
            Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
          exact congrArg s.permKeyEmb (slotPerm_del t₀ m ht₀ α β r)
        have hins_s : pkeyInsEmb (γ_sl.toEmbedding.trans s.permKeyEmb) t₀ m ht₀ =
            β.toEmbedding.trans (pkeyInsEmb s.permKeyEmb t₀ m ht₀) := by
          apply Function.Embedding.ext; intro r
          simp only [pkeyInsEmb, Function.Embedding.coeFn_mk, Function.Embedding.trans_apply]
          exact congrArg s.permKeyEmb (slotPerm_ins t₀ m ht₀ α β r)
        have hact_s : pkeyActive (γ_sl.toEmbedding.trans s.permKeyEmb) t₀ (by omega) =
            pkeyActive s.permKeyEmb t₀ (by omega) :=
          pkeyActive_perm_eq (by omega) γ_sl (fun i =>
            slotPerm_mem_Ico t₀ m ht₀ α β (b₁ := True) (b₂ := False)
              (fun _ _ => iff_of_true (by omega) trivial)
              (fun _ _ => iff_of_false (by omega) not_false) i) s.permKeyEmb
        have hc_eq : cfg (eΩ₂ ⟨s, ⟨B, hB⟩⟩) = cfg ⟨s, ⟨B, hB⟩⟩ := by
          refine InnerKeyConfig.ext ?_ ?_ ?_ rfl
          · change pkeyActive (slSeed γ_sl s).permKeyEmb t₀ _ = _; rw [hsl_pk, hact_s]
          · change Finset.univ.image (pkeyDelEmb (slSeed γ_sl s).permKeyEmb t₀ m ht₀) = _
            rw [hsl_pk, hdel_s, (himg_perm α _).1]
          · change Finset.univ.image (pkeyInsEmb (slSeed γ_sl s).permKeyEmb t₀ m ht₀) = _
            rw [hsl_pk, hins_s, (himg_perm β _).1]
        refine Prod.ext (Prod.ext ?_ ?_) (innerTarget_mk_eq hc_eq fun _ _ => rfl)
        · change (embSetPermEquiv (Fin U) m (segInsertedKeys (slSeed γ_sl s).keys t₀ m ht₀)).2 =
            β.trans (embSetPermEquiv (Fin U) m (segInsertedKeys s.keys t₀ m ht₀)).2
          rw [hins_eq, hins_eq, hsl_pk, hins_s, (himg_perm β _).2]
        · change (embSetPermEquiv (Fin U) m
              (segDeletedKeys (slSeed γ_sl s).keys s.delPerm t₀ m ht₀)).2 =
            α.trans (embSetPermEquiv (Fin U) m (segDeletedKeys s.keys s.delPerm t₀ m ht₀)).2
          rw [hdel_eq, hdel_eq, hsl_pk, hdel_s, (himg_perm α _).2]
      have hb : eβ₂ (o₁, tgt) = (o₂, tgt) :=
        Prod.ext (Prod.ext (by change β.trans o₁.1 = o₂.1; ext r; simp [β])
          (by change α.trans o₁.2 = o₂.2; ext r; simp [α])) rfl
      rw [← hb]; exact map_uniform_apply_equiv g_ot eΩ₂ eβ₂ hcomm (o₁, tgt)
    have hcfg_eq (c₁ c₂ : InnerKeyConfig U n m g) : (μ.map cfg) c₂ = (μ.map cfg) c₁ := by
      obtain ⟨τ, rfl⟩ := exists_perm_innerKeyConfig c₁ c₂
      let unSeed (τ' : Equiv.Perm (Fin U)) (s : HardKeyValSeed U V n) : HardKeyValSeed U V n :=
        ⟨s.keys.trans τ'.toEmbedding, s.kv ∘ τ'.symm, s.delPerm⟩
      have himg_u (τ' : Equiv.Perm (Fin U)) {k : ℕ} (f : Fin k ↪ Fin U) :
          Finset.univ.image (f.trans τ'.toEmbedding) =
            (Finset.univ.image f).map τ'.toEmbedding := by
        ext v; simp only [Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and,
          Function.Embedding.trans_apply]
        exact ⟨fun ⟨i, h⟩ => ⟨f i, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩
      have hFs_u (τ' : Equiv.Perm (Fin U)) (s : HardKeyValSeed U V n) {B : Finset (Fin U)}
          (hB : B ∈ F_s s) : B.map τ'.toEmbedding ∈ F_s (unSeed τ' s) := by
        rw [hFs_eq] at hB ⊢
        change B.map τ'.toEmbedding ∈ F_pk (s.permKeyEmb.trans τ'.toEmbedding)
        obtain ⟨hBp, hBi⟩ := Finset.mem_filter.mp hB
        obtain ⟨hBsub, hBc⟩ := Finset.mem_powersetCard.mp hBp
        have hins_u : pkeyInsEmb (s.permKeyEmb.trans τ'.toEmbedding) t₀ m ht₀ =
            (pkeyInsEmb s.permKeyEmb t₀ m ht₀).trans τ'.toEmbedding := rfl
        refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨by rw [huniv_pool]; exact Finset.map_subset_map.mpr hBsub, by simp [hBc]⟩, ?_⟩
        rw [hins_u, himg_u, ← Finset.map_inter, Finset.card_map, hBi]
      have hun_inv (τ' : Equiv.Perm (Fin U)) (s : HardKeyValSeed U V n) :
          unSeed τ'.symm (unSeed τ' s) = s :=
        HardKeyValSeed.ext (Function.Embedding.ext fun i => by simp [unSeed])
          (funext fun u => by simp [unSeed, Function.comp_def]) rfl
      let eΩ₃ : Ω ≃ Ω :=
        { toFun := fun ⟨s, ⟨B, hB⟩⟩ => ⟨unSeed τ s, ⟨B.map τ.toEmbedding, hFs_u τ s hB⟩⟩
          invFun := fun ⟨s, ⟨B, hB⟩⟩ =>
            ⟨unSeed τ.symm s, ⟨B.map τ.symm.toEmbedding, hFs_u τ.symm s hB⟩⟩
          left_inv := fun ⟨s, _⟩ => omega_ext (hun_inv τ s) (by ext x; simp)
          right_inv := fun ⟨s, _⟩ => omega_ext (by simpa using hun_inv τ.symm s) (by ext x; simp) }
      let eCfg : InnerKeyConfig U n m g ≃ InnerKeyConfig U n m g :=
        { toFun := InnerKeyConfig.perm τ, invFun := InnerKeyConfig.perm τ.symm
          left_inv := fun c => InnerKeyConfig.ext (by ext x; simp [InnerKeyConfig.perm])
            (by ext x; simp [InnerKeyConfig.perm]) (by ext x; simp [InnerKeyConfig.perm])
            (by ext x; simp [InnerKeyConfig.perm])
          right_inv := fun c => InnerKeyConfig.ext (by ext x; simp [InnerKeyConfig.perm])
            (by ext x; simp [InnerKeyConfig.perm]) (by ext x; simp [InnerKeyConfig.perm])
            (by ext x; simp [InnerKeyConfig.perm]) }
      have hcomm_c (ω : Ω) : cfg (eΩ₃ ω) = eCfg (cfg ω) := by
        rcases ω with ⟨s, ⟨B, hB⟩⟩
        refine InnerKeyConfig.ext ?_ ?_ ?_ rfl
        · ext x; simp [cfg, cfgOfPk, eΩ₃, eCfg, unSeed, InnerKeyConfig.perm, pkeyActive,
            HardKeyValSeed.permKeyEmb, ← Equiv.eq_symm_apply]
        · ext x; simp [cfg, cfgOfPk, eΩ₃, eCfg, unSeed, InnerKeyConfig.perm, pkeyDelEmb,
            HardKeyValSeed.permKeyEmb, ← Equiv.eq_symm_apply]
        · ext x; simp [cfg, cfgOfPk, eΩ₃, eCfg, unSeed, InnerKeyConfig.perm, pkeyInsEmb,
            HardKeyValSeed.permKeyEmb, ← Equiv.eq_symm_apply]
      exact map_uniform_apply_equiv cfg eΩ₃ eCfg hcomm_c c₁
    have hmul_cfg (o₀ : ObsT) (c₀ : InnerKeyConfig U n m g) (v₀ : ↥(c₀.K ∪ c₀.B) → Fin V) :
        ((Fintype.card ObsT * V ^ (n + m) : ℕ) : ℝ) * (q (o₀, ⟨c₀, v₀⟩)).toReal =
          ((μ.map cfg) c₀).toReal := by
      have hmap_c : q.map (fun ot => ot.2.1) = μ.map cfg := by
        dsimp [q]; rw [_root_.PMF.map_comp]; rfl
      rw [← hmap_c, PMF.map_apply_toReal q, Fintype.sum_prod_type]
      have hinner (o : ObsT) :
          (∑ cv : TgtT, if c₀ = cv.1 then (q (o, cv)).toReal else 0) =
            (V ^ (n + m) : ℝ) * (q (o₀, ⟨c₀, v₀⟩)).toReal := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single c₀
          (fun c _ hc => Finset.sum_eq_zero fun _ _ => by simp only [hc.symm, ↓reduceIte])
          (fun h => (h (Finset.mem_univ c₀)).elim)]
        simp only [↓reduceIte]
        have hv_eq (v : ↥(c₀.K ∪ c₀.B) → Fin V) :
            (q (o, ⟨c₀, v⟩)).toReal = (q (o₀, ⟨c₀, v₀⟩)).toReal := by
          rw [hval_eq o c₀ v₀ v, hslot_eq o₀ o]
        simp_rw [hv_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
          Finset.card_union_of_disjoint c₀.disj_BK.symm, c₀.card_K, c₀.card_B, Nat.cast_pow]
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_pow, mul_assoc]
    have hpos_m : (0 : ℝ) < ((Fintype.card ObsT * V ^ (n + m) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]; positivity
    refine toReal_le_inv_card_of_const q (fun ⟨o₁, ⟨c₁, v₁⟩⟩ ⟨o₂, ⟨c₂, v₂⟩⟩ => ?_)
    exact mul_left_cancel₀ hpos_m.ne' ((hmul_cfg o₁ c₁ v₁).trans
      ((congrArg ENNReal.toReal (hcfg_eq c₂ c₁)).trans (hmul_cfg o₂ c₂ v₂).symm))
  set step₀ := n + 3 * t₀
  let ops_A (ω : Ω) := candidateQueryDeleteInsertOps
    (orderSubset (cfg ω).D (cfg ω).card_D (σ ω)) (orderSubset (cfg ω).A (cfg ω).card_A (π ω)) ω.1.kv
  let ops_B (ω : Ω) := candidateQueryDeleteInsertOps
    (orderSubset (cfg ω).D (cfg ω).card_D (σ ω)) (orderSubset (cfg ω).B (cfg ω).card_B (π ω)) ω.1.kv
  have hopsA_eq (ω : Ω) : ops_A ω = elemSlice n 3 ω.1.ops t₀ (t₀ + m) := by
    dsimp only [ops_A, HardKeyValSeed.ops]
    rw [hod_eq, hoa_eq, elemSlice_insertQueryDeleteSeq_eq_candidate]
  have hopsB_eq (ω : Ω) : ops_B ω = ω.1.candidateOps t₀ m ht₀ ω.2.val (cfg ω).card_B := by
    dsimp only [ops_B]; rw [HardKeyValSeed.candidateOps_eq, hod_eq]
  let W (ω : Ω) : Bool := decide (IsCappedConsistent D_det step₀
    (D_det.runSeq (pref_bef ω)).2 γ m t (ops_A ω) (ops_B ω))
  have hprob_μ : (((innerPoolDist (by omega) hV F_s hne).map fun sb =>
      decide (IsSeedConsistent D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal =
      ((μ.map W) true).toReal := by
    have hcard_Ω : Fintype.card Ω = Fintype.card (HardKeyValSeed U V n) * cg := by
      simp only [Ω, Fintype.card_sigma, Fintype.card_coe, hFs_eq, hcard_Fpk,
        Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [prob_innerPoolDist_eq (by omega) hV F_s (fun s => by rw [hFs_eq, hcard_Fpk]) hne,
      PMF.map_apply_toReal μ, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hw_iff (b : ↥(F_s s)) :
        (true = W ⟨s, b⟩) ↔ IsSeedConsistent D_det t₀ m ht₀ γ t s b.val := by
      simp only [W, true_eq_decide_iff, IsSeedConsistent, hopsA_eq ⟨s, b⟩, hopsB_eq ⟨s, b⟩]
      exact ⟨fun h => ⟨(cfg ⟨s, b⟩).card_B, h⟩, fun ⟨_, h⟩ => h⟩
    simp only [μ, PMF.uniformOfFintype_apply, hcard_Ω, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      hw_iff]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hbij : (Finset.univ.filter fun b : ↥(F_s s) =>
        IsSeedConsistent D_det t₀ m ht₀ γ t s b.val).card =
        ((F_s s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card :=
      Finset.card_bij (fun b _ => b.val)
        (fun b hb => Finset.mem_filter.mpr ⟨b.property, (Finset.mem_filter.mp hb).2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun B hB => ⟨⟨B, (Finset.mem_filter.mp hB).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hB).2⟩, rfl⟩)
    rw [hbij]; push_cast; rw [mul_inv]; ring
  rw [hprob_μ]
  by_cases hW0 : (μ.map W) true = 0
  · rw [hW0, ENNReal.toReal_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg U) _
  have hW_mem : true ∈ ((μ.map fun ω => (W ω, ω)).map Prod.fst).support := by
    rw [_root_.PMF.map_comp]; exact (_root_.PMF.mem_support_iff _ _).mpr hW0
  set p : PMF Ω := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
  have hp_supp (ω : Ω) (hω : ω ∈ p.support) :
      IsCappedConsistent D_det step₀ (D_det.runSeq (pref_bef ω)).2 γ m t (ops_A ω) (ops_B ω) := by
    have hmem := (PMF.mem_support_conditionalSnd_iff (μ.map fun ω => (W ω, ω)) true hW_mem ω).mp hω
    obtain ⟨_, _, heq⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hmem
    rcases Prod.mk.inj heq with ⟨hw, rfl⟩
    exact of_decide_eq_true (by simpa [W] using hw.symm)
  let C_bef (ω : Ω) := (D_det.runSeq (pref_bef ω)).2
  let S_A (ω : Ω) := D_det.probedCellsInterval step₀ (C_bef ω) (ops_A ω)
  let C_A (ω : Ω) := (D_det.runInterval step₀ (C_bef ω) (ops_A ω)).2
  let S_B (ω : Ω) := D_det.probedCellsInterval step₀ (C_bef ω) (ops_B ω)
  let C_B (ω : Ω) := (D_det.runInterval step₀ (C_bef ω) (ops_B ω)).2
  let s_after (ω : Ω) :=
    (windowDict ω.1.permKeyEmb (fun idx => ω.1.kv (ω.1.permKeyEmb idx)) (t₀ + m) ht₀).1
  have hstate (ω : Ω) :
      let s₀ := ((Dynamic.spec U V n).run (Dictionary.empty U) (pref_bef ω)).1
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) (pref_bef ω) ∧
        (pref_bef ω).length = n + 3 * t₀ ∧ Dictionary.dom s₀ = (cfg ω).K ∧
        (∀ u ∈ (cfg ω).K, s₀ u = some (ω.1.kv u).val) ∧
        decodeDict D_det (n + 3 * (t₀ + m)) (C_A ω) = s_after ω ∧
        Dictionary.dom (s_after ω) = ((cfg ω).K \ (cfg ω).D) ∪ (cfg ω).A ∧
        (∀ u ∈ Dictionary.dom (s_after ω), s_after ω u = some (ω.1.kv u).val) := by
    dsimp only; set s := ω.1
    have hvh_0 := (validHistory_and_run_take_insertQueryDeleteSeq s.keys
      (fun idx => s.kv (s.keys idx)) s.delPerm (by omega : t₀ ≤ n)).1
    have hvh_m := (validHistory_and_run_take_insertQueryDeleteSeq s.keys
      (fun idx => s.kv (s.keys idx)) s.delPerm ht₀).1
    have hwval (t_k : ℕ) (ht_k : t_k ≤ n) (u : Fin U)
        (hu : u ∈ Dictionary.dom (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx))
          t_k ht_k).1) :
        (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) t_k ht_k).1 u =
          some (s.kv u).val := by
      rw [windowDict_coe, dom_dictOfEmb, Finset.mem_map] at hu
      obtain ⟨i, _, rfl⟩ := hu; rw [windowDict_coe, dictOfEmb_apply_self]; simp
    have hCA_mem : C_A ω = (D_det.runSeq (s.ops.take (n + 3 * (t₀ + m)))).2 := by
      dsimp only [C_A, C_bef]; rw [hopsA_eq]
      exact (memAt_eq_runInterval_elemSlice D_det n 3 s.ops (Nat.le_add_right t₀ m)).symm
    have hlen_m :
        ((insertQueryDeleteSeq s.keys (fun idx => s.kv (s.keys idx)) s.delPerm).take
          (n + 3 * (t₀ + m))).length = n + 3 * (t₀ + m) := by
      rw [List.length_take, length_insertQueryDeleteSeq]; omega
    refine ⟨hvh_0, by rw [List.length_take, HardKeyValSeed.ops, length_insertQueryDeleteSeq]; omega,
      by dsimp only [pref_bef, s]; rw [ω.1.run_take_ops_fst (t := t₀) (by omega)]
         simp [cfg, cfgOfPk, pkeyActive],
      fun u hu => by
        dsimp only [pref_bef]; rw [s.run_take_ops_fst (t := t₀) (by omega)]
        exact hwval t₀ (by omega) u (by simpa [cfg, cfgOfPk, pkeyActive, s] using hu),
      by rw [hCA_mem]; dsimp only [HardKeyValSeed.ops]
         have hd := decodeDict_runSeq_eq hcorr hvh_m (by rw [hlen_m]; omega)
         rw [hlen_m] at hd; exact hd.trans (s.run_take_ops_fst (t := t₀ + m) ht₀),
      ?_, fun u hu => hwval (t₀ + m) ht₀ u hu⟩
    simp only [s_after, windowDict_coe, dom_dictOfEmb, cfg, cfgOfPk, pkeyActive, pkeyDelEmb,
      pkeyInsEmb]
    ext u; simp only [Finset.mem_map, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_univ, true_and, windowEmb_apply, segDeletedKeys_apply, Equiv.Perm.coe_one, id_eq]
    constructor
    · rintro ⟨k, rfl⟩
      have hk_lt := k.isLt
      by_cases hk : k.val < n - m
      · refine Or.inl ⟨⟨⟨m + k.val, by omega⟩,
          congrArg ω.1.permKeyEmb (Fin.ext (by dsimp; omega))⟩, ?_⟩
        rintro ⟨r, hr⟩; have := r.isLt
        have := congrArg Fin.val (ω.1.permKeyEmb.injective hr); dsimp at this; omega
      · exact Or.inr ⟨⟨k.val - (n - m), by omega⟩,
          congrArg ω.1.permKeyEmb (Fin.ext (by dsimp; omega))⟩
    · rintro (⟨⟨k, rfl⟩, hnotD⟩ | ⟨r, rfl⟩)
      · have hk_lt := k.isLt
        have hge : m ≤ k.val := by
          by_contra hlt
          exact hnotD ⟨⟨k.val, by omega⟩, congrArg ω.1.permKeyEmb (Fin.ext (by dsimp))⟩
        exact ⟨⟨k.val - m, by omega⟩, congrArg ω.1.permKeyEmb (Fin.ext (by dsimp; omega))⟩
      · have hr_lt := r.isLt
        exact ⟨⟨n - m + r.val, by omega⟩, congrArg ω.1.permKeyEmb (Fin.ext (by dsimp; omega))⟩
  obtain ⟨enc_sep, sep, hpf_sep, hsep_corr, hsep_len⟩ :=
    exists_prefixFree_separator_code cells (p.map fun ω => (S_B ω, S_A ω \ S_B ω)) (by
      rintro ab hab; obtain ⟨_, _, rfl⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hab
      exact Finset.disjoint_sdiff)
  let mask (ω : Ω) := sepSet sep (enc_sep (S_B ω, S_A ω \ S_B ω))
  let C_mix (ω : Ω) := mixMem (C_bef ω) (C_A ω) (mask ω)
  have hmask_prop (ω : Ω) : S_B ω ⊆ mask ω ∧ Disjoint (S_A ω \ S_B ω) (mask ω) :=
    let hs := hsep_corr (S_B ω) (S_A ω \ S_B ω) Finset.disjoint_sdiff
    subset_sepSet_and_disjoint hs.1 hs.2
  let F_pass (ω : Ω) : Finset (Finset (Fin U)) :=
    ((Finset.univ : Finset (Fin U)).powersetCard m).filter fun D_c =>
      ∃ hD : D_c.card = m, passesDeletionTest D_det step₀ (C_mix ω) (mask ω)
        (cfg ω).B (cfg ω).card_B (π ω) (σ ω) ω.1.kv D_c hD
  have hpass_all (ω : Ω) :
      (cfg ω).D ∈ F_pass ω ∧ (F_pass ω).card ≤ (n + m).choose m ∧
        ∀ r : Fin m, queryOutAt (D_det.runInterval step₀ (C_mix ω) (ops_B ω)).1 r.val =
          some (ω.1.kv (orderSubset (cfg ω).D (cfg ω).card_D (σ ω) r)).val := by
    obtain ⟨hvh_b, hlen_b, hdom_b, hval_b, _, _, _⟩ := hstate ω
    have hK_le :
        (Dictionary.dom ((Dynamic.spec U V n).run
          (Dictionary.empty U) (pref_bef ω)).1).card ≤ n := by
      rw [hdom_b, (cfg ω).card_K]
    obtain ⟨hpass_D, hq_D⟩ := passesDeletionTest_and_queryOutAt_eq hcorr hvh_b hlen_b ht₀ hK_le
      (cfg ω).card_B (cfg ω).card_D (by rw [hdom_b]; exact (cfg ω).D_sub)
      (by rw [hdom_b]; exact (cfg ω).disj_BK) (by rwa [hdom_b]) (hmask_prop ω).1
    have hsub_KB : F_pass ω ⊆ ((cfg ω).K ∪ (cfg ω).B).powersetCard m := fun D_c hDc => by
      simp only [F_pass, Finset.mem_filter, Finset.mem_powersetCard] at hDc ⊢
      obtain ⟨⟨_, hDc_m⟩, _, hpc⟩ := hDc
      exact ⟨hdom_b ▸ subset_union_of_passesDeletionTest hcorr hvh_b hlen_b ht₀ hK_le
        (cfg ω).card_B hDc_m hpc, hDc_m⟩
    have hcard_KB : ((cfg ω).K ∪ (cfg ω).B).card = n + m := by
      rw [Finset.card_union_of_disjoint (cfg ω).disj_BK.symm, (cfg ω).card_K, (cfg ω).card_B]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (cfg ω).card_D⟩, ⟨(cfg ω).card_D, hpass_D⟩⟩,
      (Finset.card_le_card hsub_KB).trans_eq (by rw [Finset.card_powersetCard, hcard_KB]), hq_D⟩
  let SB_sim (ω : Ω) := D_det.probedCellsInterval step₀ (C_mix ω) (ops_B ω)
  let I_AB (ω : Ω) := S_A ω ∩ SB_sim ω
  let Δ_set (ω : Ω) :=
    (I_AB ω).filter fun j => C_A ω j ≠ (D_det.runInterval step₀ (C_mix ω) (ops_B ω)).2 j
  let K_after (ω : Ω) := Dictionary.dom (decodeDict D_det (n + 3 * (t₀ + m)) (C_A ω))
  let m₁ (ω : Ω) :=
    encodeMemFinset ((Finset.univ : Finset (Fin U)).powersetCard m) (U.choose m) (cfg ω).B
  let m₂ (ω : Ω) := encodeRestr (cfg ω).B ω.1.kv
  let m₃ (ω : Ω) := encodeFintype (C_mix ω)
  let m₄ (ω : Ω) := enc_sep (S_B ω, S_A ω \ S_B ω)
  let m₅ (ω : Ω) := encodeMemFinset (F_pass ω) ((n + m).choose m) (cfg ω).D
  let m₆ (ω : Ω) := encodeRestr (SB_sim ω) (fun j => decide (j ∈ I_AB ω))
  let m₇ (ω : Ω) := encodeRestr (I_AB ω) (fun j => decide (j ∈ Δ_set ω))
  let m₈ (ω : Ω) := encodeRestr (Δ_set ω) (C_A ω)
  let m₉ (ω : Ω) := encodeMemFinset ((K_after ω).powersetCard m) (n.choose m) (cfg ω).A
  let msg (ω : Ω) :=
    m₁ ω ++ (m₂ ω ++ (m₃ ω ++ (m₄ ω ++ (m₅ ω ++ (m₆ ω ++ (m₇ ω ++ (m₈ ω ++ m₉ ω)))))))
  have hdecode : ∀ ω₁ ∈ p.support, ∀ ω₂ ∈ p.support,
      obs ω₁ = obs ω₂ → msg ω₁ <+: msg ω₂ → msg ω₁ = msg ω₂ ∧ target ω₁ = target ω₂ := by
    intro ω₁ hω₁ ω₂ hω₂ hobs hp_all
    rcases Prod.mk.inj hobs with ⟨hπ, hσ⟩
    obtain ⟨hm₁, hp2⟩ := prefix_append_of_length_eq (by simp [m₁, length_encodeMemFinset]) hp_all
    obtain ⟨hm₂, hp3⟩ := prefix_append_of_length_eq
      (by simp [m₂, length_encodeRestr, (cfg ω₁).card_B, (cfg ω₂).card_B]) hp2
    obtain ⟨hm₃, hp4⟩ := prefix_append_of_length_eq (by simp [m₃, length_encodeFintype]) hp3
    obtain ⟨hm₄, hp5⟩ := prefix_append_of_isPrefixFree hpf_sep ⟨_, rfl⟩ ⟨_, rfl⟩ hp4
    obtain ⟨hm₅, hp6⟩ := prefix_append_of_length_eq (by simp [m₅, length_encodeMemFinset]) hp5
    have hB : (cfg ω₁).B = (cfg ω₂).B := encodeMemFinset_inj
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (cfg ω₁).card_B⟩)
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (cfg ω₂).card_B⟩) (by simp) hm₁
    have hkvB : ∀ x ∈ (cfg ω₁).B, ω₁.1.kv x = ω₂.1.kv x := encodeRestr_inj hB hm₂
    have hcm : C_mix ω₁ = C_mix ω₂ := encodeFintype_injective hm₃
    have hmask_eq : mask ω₁ = mask ω₂ := congrArg (sepSet sep) hm₄
    have hF_eq : F_pass ω₁ = F_pass ω₂ := by
      ext D_c; simp only [F_pass, Finset.mem_filter]; refine and_congr_right fun _ => ?_
      refine exists_congr fun hD => ?_
      have hc : candidateQueryDeleteInsertOps (orderSubset D_c hD (σ ω₁))
          (orderSubset (cfg ω₁).B (cfg ω₁).card_B (π ω₁)) ω₁.1.kv =
          candidateQueryDeleteInsertOps (orderSubset D_c hD (σ ω₂))
          (orderSubset (cfg ω₂).B (cfg ω₂).card_B (π ω₂)) ω₂.1.kv := by
        rw [candidateQueryDeleteInsertOps_congr _ (cfg ω₁).card_B (π ω₁) hkvB,
          orderSubset_congr rfl hσ, orderSubset_congr hB hπ]
      simp only [passesDeletionTest, hc, hcm, hmask_eq]
    obtain ⟨hD₁, hFcard₁, hq₁_all⟩ := hpass_all ω₁; obtain ⟨hD₂, _, hq₂_all⟩ := hpass_all ω₂
    have hD : (cfg ω₁).D = (cfg ω₂).D := encodeMemFinset_inj hD₁ (hF_eq ▸ hD₂) hFcard₁
      (by simpa only [m₅, hF_eq] using hm₅)
    have hopsB : ops_B ω₁ = ops_B ω₂ := by
      dsimp only [ops_B]; rw [candidateQueryDeleteInsertOps_congr _ (cfg ω₁).card_B (π ω₁) hkvB,
        orderSubset_congr hD hσ, orderSubset_congr hB hπ]
    have hSB_sim : SB_sim ω₁ = SB_sim ω₂ := by dsimp only [SB_sim]; rw [hcm, hopsB]
    obtain ⟨hm₆, hp7⟩ := prefix_append_of_length_eq (by simp [m₆, length_encodeRestr, hSB_sim]) hp6
    have hI_AB : I_AB ω₁ = I_AB ω₂ := by
      have hr := encodeRestr_inj hSB_sim hm₆
      ext j; by_cases hj : j ∈ SB_sim ω₁
      · exact decide_eq_decide.mp (hr j hj)
      · exact iff_of_false (fun h => hj (Finset.inter_subset_right h))
          (fun h => (hSB_sim ▸ hj) (Finset.inter_subset_right h))
    obtain ⟨hm₇, hp8⟩ := prefix_append_of_length_eq (by simp [m₇, length_encodeRestr, hI_AB]) hp7
    have hΔ : Δ_set ω₁ = Δ_set ω₂ := by
      have hr := encodeRestr_inj hI_AB hm₇
      ext j; by_cases hj : j ∈ I_AB ω₁
      · exact decide_eq_decide.mp (hr j hj)
      · exact iff_of_false (fun h => hj (Finset.filter_subset _ _ h))
          (fun h => (hI_AB ▸ hj) (Finset.filter_subset _ _ h))
    obtain ⟨hm₈, hp9⟩ := prefix_append_of_length_eq (by simp [m₈, length_encodeRestr, hΔ]) hp8
    have hm₉ : m₉ ω₁ = m₉ ω₂ := (prefix_append_of_length_eq (v₁ := []) (v₂ := [])
      (by simp [m₉, length_encodeMemFinset]) (by simpa using hp9)).1
    have hCA : C_A ω₁ = C_A ω₂ := by
      funext j; by_cases hjΔ : j ∈ Δ_set ω₁
      · exact encodeRestr_inj hΔ hm₈ j hjΔ
      · by_cases hjI : j ∈ I_AB ω₁
        · have hj₁ : ¬ C_A ω₁ j ≠ (D_det.runInterval step₀ (C_mix ω₁) (ops_B ω₁)).2 j :=
            fun hne => hjΔ (Finset.mem_filter.mpr ⟨hjI, hne⟩)
          have hj₂ : ¬ C_A ω₂ j ≠ (D_det.runInterval step₀ (C_mix ω₂) (ops_B ω₂)).2 j :=
            fun hne => (hΔ ▸ hjΔ) (Finset.mem_filter.mpr ⟨hI_AB ▸ hjI, hne⟩)
          push Not at hj₁ hj₂; rw [hj₁, hj₂, hcm, hopsB]
        · have hrec (ω : Ω) (hnot : j ∉ I_AB ω) : C_A ω j = C_mix ω j := by
            obtain ⟨_, _, hSB_eq, _⟩ := runInterval_mixMem_eq_of_probedCellsInterval_subset D_det
              step₀ (C_bef ω) (C_A ω) (mask ω) (ops_B ω) (hmask_prop ω).1
            have hsep_sub : mask ω ∩ S_A ω ⊆ S_B ω := fun x hx => by
              obtain ⟨hxm, hxA⟩ := Finset.mem_inter.mp hx; by_contra hnxB
              exact Finset.disjoint_left.mp (hmask_prop ω).2 (Finset.mem_sdiff.mpr ⟨hxA, hnxB⟩) hxm
            exact (mixMem_eq_postMem_of_notMem_inter D_det step₀ (C_bef ω) (ops_A ω) (mask ω)
              (S_B ω) hsep_sub
              (by dsimp only [I_AB, S_A, SB_sim, C_mix] at hnot; rwa [hSB_eq] at hnot)).symm
          rw [hrec ω₁ hjI, hrec ω₂ (hI_AB ▸ hjI), hcm]
    have hKa_eq : K_after ω₁ = K_after ω₂ := congrArg
      (fun C => Dictionary.dom (decodeDict D_det (n + 3 * (t₀ + m)) C)) hCA
    have hKa_prop (ω : Ω) :
        (cfg ω).A ∈ (K_after ω).powersetCard m ∧ ((K_after ω).powersetCard m).card ≤ n.choose m ∧
          (cfg ω).K = (K_after ω \ (cfg ω).A) ∪ (cfg ω).D := by
      obtain ⟨_, _, _, _, hdec_a, hdom_a, _⟩ := hstate ω
      have hKa : K_after ω = ((cfg ω).K \ (cfg ω).D) ∪ (cfg ω).A := by
        change Dictionary.dom (decodeDict D_det (n + 3 * (t₀ + m)) (C_A ω)) = _
        rw [hdec_a, hdom_a]
      have hdisj_KDA : Disjoint ((cfg ω).K \ (cfg ω).D) (cfg ω).A :=
        Finset.disjoint_of_subset_left Finset.sdiff_subset (cfg ω).disj_AK.symm
      have hKa_card : (K_after ω).card = n := by
        have hs := Finset.card_sdiff_add_card_eq_card (cfg ω).D_sub
        rw [(cfg ω).card_D, (cfg ω).card_K] at hs
        rw [hKa, Finset.card_union_of_disjoint hdisj_KDA, (cfg ω).card_A]; omega
      refine ⟨Finset.mem_powersetCard.mpr ⟨hKa ▸ Finset.subset_union_right, (cfg ω).card_A⟩,
        by rw [Finset.card_powersetCard, hKa_card],
        by rw [hKa, sdiff_union_sdiff_cancel (cfg ω).D_sub (cfg ω).disj_AK]⟩
    obtain ⟨hA₁, hKcard₁, hKeq₁⟩ := hKa_prop ω₁; obtain ⟨hA₂, _, hKeq₂⟩ := hKa_prop ω₂
    have hA : (cfg ω₁).A = (cfg ω₂).A := encodeMemFinset_inj hA₁ (hKa_eq ▸ hA₂) hKcard₁
      (by simpa only [m₉, hKa_eq] using hm₉)
    have hK : (cfg ω₁).K = (cfg ω₂).K := by rw [hKeq₁, hKeq₂, hKa_eq, hA, hD]
    have hcfg : cfg ω₁ = cfg ω₂ := InnerKeyConfig.ext hK hD hA hB
    have hvals : ∀ u ∈ (cfg ω₁).K ∪ (cfg ω₁).B, ω₁.1.kv u = ω₂.1.kv u := fun u hu => by
      by_cases huB : u ∈ (cfg ω₁).B
      · exact hkvB u huB
      · have huK : u ∈ (cfg ω₁).K := (Finset.mem_union.mp hu).resolve_right huB
        by_cases huD : u ∈ (cfg ω₁).D
        · let r₁ := (σ ω₁).symm (((cfg ω₁).D.orderIsoOfFin (cfg ω₁).card_D).symm ⟨u, huD⟩)
          have hdr₁ : orderSubset (cfg ω₁).D (cfg ω₁).card_D (σ ω₁) r₁ = u := by
            simp only [orderSubset_apply, r₁, Equiv.apply_symm_apply]
            exact congrArg Subtype.val
              (((cfg ω₁).D.orderIsoOfFin (cfg ω₁).card_D).apply_symm_apply _)
          have hdr₂ : orderSubset (cfg ω₂).D (cfg ω₂).card_D (σ ω₂) r₁ = u := by
            rw [← congrArg (fun f : Fin m ↪ Fin U => f r₁)
              (orderSubset_congr (h₁ := (cfg ω₁).card_D) (h₂ := (cfg ω₂).card_D) hD hσ), hdr₁]
          have hq₁ := hq₁_all r₁; have hq₂ := hq₂_all r₁
          rw [hdr₁] at hq₁; rw [hdr₂, ← hcm, ← hopsB] at hq₂
          exact Fin.ext (Option.some.inj (hq₁.symm.trans hq₂))
        · obtain ⟨_, _, _, _, hdec₁, hdom₁, hval₁⟩ := hstate ω₁
          obtain ⟨_, _, _, _, hdec₂, hdom₂, hval₂⟩ := hstate ω₂
          have hd₁ : u ∈ Dictionary.dom (s_after ω₁) :=
            hdom₁ ▸ Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huK, huD⟩)
          have hd₂ : u ∈ Dictionary.dom (s_after ω₂) :=
            hdom₂ ▸ Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hK ▸ huK, hD ▸ huD⟩)
          have hs_eq : s_after ω₁ u = s_after ω₂ u := by
            rw [← hdec₁, ← hdec₂, show C_A ω₁ = C_A ω₂ from hCA]
          rw [hval₁ u hd₁, hval₂ u hd₂] at hs_eq; exact Fin.ext (Option.some.inj hs_eq)
    exact ⟨by dsimp only [msg]
              rw [hm₁, hm₂, hm₃, show m₄ ω₁ = m₄ ω₂ from hm₄, hm₅, hm₆, hm₇, hm₈, hm₉],
      innerTarget_mk_eq hcfg hvals⟩
  let joint_ot : PMF (ObsT × TgtT) := p.map fun ω => (obs ω, target ω)
  have hcomp_bound :
      PMF.conditionalEntropy joint_ot ≤ ∑ ω : Ω, (p ω).toReal * ((msg ω).length : ℝ) :=
    conditionalEntropy_map_le_expected_length_of_isPrefixFree p obs target msg
      (fun _ _ ⟨ω₁, ⟨hω₁, ho₁⟩, hy₁⟩ _ ⟨ω₂, ⟨hω₂, ho₂⟩, hy₂⟩ hp => by
        subst hy₁; subst hy₂; exact (hdecode _ hω₁ _ hω₂ (ho₁.trans ho₂.symm) hp).1)
      (fun ω₁ hω₁ ω₂ hω₂ hobs heq =>
        (hdecode _ hω₁ _ hω₂ hobs ⟨[], by simpa using heq⟩).2)
  have : Nonempty TgtT := ⟨target (Classical.arbitrary _)⟩
  have hent_lo : Real.logb 2 (((μ.map W) true).toReal) + Real.logb 2 (Fintype.card TgtT) ≤
      PMF.conditionalEntropy joint_ot :=
    logb_prob_add_logb_card_le_conditionalEntropy μ W obs target hW0 hmass
  have hlen_rest (ω : Ω) (hω : ω ∈ p.support) :
      ((msg ω).length : ℝ) ≤ Real.logb 2 (U.choose m) + (m : ℝ) * Real.logb 2 V +
        ((cells * w : ℕ) : ℝ) + ((m₄ ω).length : ℝ) + Real.logb 2 ((n + m).choose m) +
        Real.logb 2 (n.choose m) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + 4 := by
    obtain ⟨hΔ_le, _, hSB_cap⟩ := hp_supp ω hω
    obtain ⟨_, _, hSB_eq, hCB_on⟩ := runInterval_mixMem_eq_of_probedCellsInterval_subset D_det
      step₀ (C_bef ω) (C_A ω) (mask ω) (ops_B ω) (hmask_prop ω).1
    have hΔ_eq : (Δ_set ω).card =
        ((S_A ω ∩ S_B ω).filter fun j => C_A ω j ≠ C_B ω j).card := by
      dsimp only [Δ_set, I_AB, SB_sim, C_mix]; rw [hSB_eq]; congr 1
      exact Finset.filter_congr fun j hj => by rw [hCB_on j (Finset.inter_subset_right hj)]
    have hm1 : ((m₁ ω).length : ℝ) ≤ Real.logb 2 (U.choose m) + 1 := by
      dsimp only [m₁]; rw [length_encodeMemFinset]
      exact (clog_two_lt_logb_add_one (Nat.choose_pos (by omega))).le
    have hm2 : ((m₂ ω).length : ℝ) ≤ (m : ℝ) * Real.logb 2 V + 1 := by
      dsimp only [m₂]; rw [length_encodeRestr, Fintype.card_fin, (cfg ω).card_B]
      refine (clog_two_lt_logb_add_one (pow_pos (by omega : 0 < V) m)).le.trans ?_
      rw [Nat.cast_pow, Real.logb_pow]
    have hm3 : ((m₃ ω).length : ℝ) = ((cells * w : ℕ) : ℝ) := by
      dsimp only [m₃]
      rw [length_encodeFintype, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, Nat.clog_pow _ _ (by omega), mul_comm]
    have hm5 : ((m₅ ω).length : ℝ) ≤ Real.logb 2 ((n + m).choose m) + 1 := by
      dsimp only [m₅]; rw [length_encodeMemFinset]
      exact (clog_two_lt_logb_add_one (Nat.choose_pos (Nat.le_add_left m n))).le
    have hm6 : ((m₆ ω).length : ℝ) ≤ (m : ℝ) * t := by
      dsimp only [m₆, SB_sim, C_mix]
      rw [length_encodeRestr, Fintype.card_bool, Nat.clog_pow _ _ (by norm_num), hSB_eq]
      exact hSB_cap
    have hm7 : ((m₇ ω).length : ℝ) ≤ (m : ℝ) * t := by
      dsimp only [m₇, I_AB, SB_sim, C_mix]
      rw [length_encodeRestr, Fintype.card_bool, Nat.clog_pow _ _ (by norm_num), hSB_eq]
      exact (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans hSB_cap
    have hm8 : ((m₈ ω).length : ℝ) ≤ γ * (m : ℝ) * (w : ℝ) := by
      dsimp only [m₈]
      rw [length_encodeRestr, Fintype.card_fin, ← pow_mul, Nat.clog_pow _ _ (by norm_num),
        Nat.cast_mul, mul_comm, hΔ_eq]
      exact mul_le_mul_of_nonneg_right hΔ_le (Nat.cast_nonneg w)
    have hm9 : ((m₉ ω).length : ℝ) ≤ Real.logb 2 (n.choose m) + 1 := by
      dsimp only [m₉]; rw [length_encodeMemFinset]
      exact (clog_two_lt_logb_add_one (Nat.choose_pos (by omega))).le
    simp only [msg, List.length_append, Nat.cast_add]; linarith
  have hsep_exp : ∑ ω : Ω, (p ω).toReal * ((m₄ ω).length : ℝ) ≤ 4 * (m : ℝ) * t + 7 := by
    have hmap_eq : (∑ ab : Finset (Fin cells) × Finset (Fin cells),
        ((p.map fun ω => (S_B ω, S_A ω \ S_B ω)) ab).toReal * ((enc_sep ab).length : ℝ)) =
        ∑ ω : Ω, (p ω).toReal * ((m₄ ω).length : ℝ) := by
      simp_rw [PMF.map_apply_toReal, Finset.sum_mul]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ω _ => by simp [m₄]
    have hcard_rhs : (∑ ab : Finset (Fin cells) × Finset (Fin cells),
        ((p.map fun ω => (S_B ω, S_A ω \ S_B ω)) ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ)) ≤
        2 * (m : ℝ) * t := by
      simp_rw [PMF.map_apply_toReal, Finset.sum_mul]; rw [Finset.sum_comm]
      have h1 : (∑ x : Ω, ∑ y : Finset (Fin cells) × Finset (Fin cells),
          (if y = (S_B x, S_A x \ S_B x) then (p x).toReal else 0) *
            ((y.1.card + y.2.card : ℕ) : ℝ)) =
          ∑ x : Ω, (p x).toReal * (((S_B x).card + (S_A x \ S_B x).card : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun x _ => by simp
      rw [h1]
      calc ∑ x : Ω, (p x).toReal * (((S_B x).card + (S_A x \ S_B x).card : ℕ) : ℝ)
          ≤ ∑ x : Ω, (p x).toReal * (2 * (m : ℝ) * t) := by
            refine Finset.sum_le_sum fun x _ => ?_
            by_cases hx : (p x).toReal = 0
            · rw [hx, zero_mul, zero_mul]
            · have hxs : x ∈ p.support :=
                (_root_.PMF.mem_support_iff p x).mpr (fun h0 => hx (by simp [h0]))
              obtain ⟨_, hSA_c, hSB_c⟩ := hp_supp x hxs
              have hsd : ((S_A x \ S_B x).card : ℝ) ≤ ((S_A x).card : ℝ) :=
                Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              push_cast; linarith
        _ = 2 * (m : ℝ) * t := by rw [← Finset.sum_mul, PMF.sum_toReal p, one_mul]
    linarith [hsep_len]
  have hexp_msg : ∑ ω : Ω, (p ω).toReal * ((msg ω).length : ℝ) ≤
      Real.logb 2 (U.choose m) + Real.logb 2 (U.choose n) + ((n + m : ℕ) : ℝ) * Real.logb 2 V +
        R + Real.logb 2 ((n + m).choose m) + Real.logb 2 (n.choose m) +
        6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + 11 := by
    set C_const := Real.logb 2 (U.choose m) + (m : ℝ) * Real.logb 2 V + ((cells * w : ℕ) : ℝ) +
      Real.logb 2 ((n + m).choose m) + Real.logb 2 (n.choose m) +
      2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + 4
    have hpt : ∑ ω : Ω, (p ω).toReal * ((msg ω).length : ℝ) ≤
        ∑ ω : Ω, ((p ω).toReal * C_const + (p ω).toReal * ((m₄ ω).length : ℝ)) := by
      refine Finset.sum_le_sum fun ω _ => ?_
      by_cases h0 : (p ω).toReal = 0
      · simp [h0]
      · have hω : ω ∈ p.support :=
          (_root_.PMF.mem_support_iff p ω).mpr (fun h => h0 (by simp [h]))
        have hl := hlen_rest ω hω
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by dsimp [C_const]; linarith) ENNReal.toReal_nonneg
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal p, one_mul] at hpt
    push_cast; dsimp [C_const] at hpt; linarith [hspace, hsep_exp]
  exact log_innerPool_budget_le hU hV hm_n hg hγ hm_lo hbudget
    (ENNReal.toReal_pos hW0 (PMF.apply_ne_top (μ.map W) true))
    (hent_lo.trans (hcomp_bound.trans hexp_msg))

private theorem nonempty_pool_eq {U n t₀ m g P : ℕ} (ht₀ : t₀ + m ≤ n) (hg_le : g ≤ m)
    (hP_ge : 2 * m - g ≤ P) (poolPk : (Fin (2 * n) ↪ Fin U) → Finset (Fin U))
    (hcard_pool : ∀ pk, (poolPk pk).card = P)
    (hA_pool : ∀ pk, Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ poolPk pk)
    (pk : Fin (2 * n) ↪ Fin U) :
    (((poolPk pk).powersetCard m).filter fun B =>
      (Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ∩ B).card = g).Nonempty := by
  rw [← Finset.card_pos, card_inter_filter_powersetCard (hA_pool pk)
    (by simp [Finset.card_image_of_injective _ (pkeyInsEmb pk t₀ m ht₀).injective]), hcard_pool]
  exact mul_pos (Nat.choose_pos hg_le) (Nat.choose_pos (by omega))

private theorem nonempty_pool_lt {U n t₀ m P : ℕ} (ht₀ : t₀ + m ≤ n) (hm : 2 ≤ m)
    (hP_ge : 2 * m ≤ P) (poolPk : (Fin (2 * n) ↪ Fin U) → Finset (Fin U))
    (hcard_pool : ∀ pk, (poolPk pk).card = P)
    (hA_pool : ∀ pk, Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ poolPk pk)
    (pk : Fin (2 * n) ↪ Fin U) :
    (((poolPk pk).powersetCard m).filter fun B =>
      (Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ∩ B).card < m / 2).Nonempty := by
  obtain ⟨B, hB⟩ := nonempty_pool_eq ht₀ (Nat.zero_le m) (by omega) poolPk hcard_pool hA_pool pk
  exact ⟨B, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
    by rw [(Finset.mem_filter.mp hB).2]; omega⟩⟩

open Classical in
private theorem prob_and_expect_innerPool_lt_half_le {U V n t₀ m cells w : ℕ} {γ R t : ℝ}
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n) (ht₀ : t₀ + m ≤ n)
    (hγ : 0 < γ) (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (m : ℝ))
    (hspace : ((cells * w : ℕ) : ℝ) ≤ Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 V + R)
    (hbudget : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      (3 / 2) * γ * (m : ℝ) * Real.logb 2 U ≤ ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (poolPk : (Fin (2 * n) ↪ Fin U) → Finset (Fin U)) {P : ℕ}
    (hcard_pool : ∀ pk, (poolPk pk).card = P)
    (hA_pool : ∀ pk, Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ poolPk pk)
    (hdisj_pool : ∀ pk, Disjoint (poolPk pk) (pkeyActive pk t₀ (by omega)))
    (hslot_pool : ∀ γp, IsSlotPerm t₀ m γp → ∀ pk, poolPk (γp.toEmbedding.trans pk) = poolPk pk)
    (huniv_pool : ∀ (τ : Equiv.Perm (Fin U)) pk,
      poolPk (pk.trans τ.toEmbedding) = (poolPk pk).map τ.toEmbedding)
    (hP_ge : 2 * m ≤ P) :
    let F_lt : HardKeyValSeed U V n → Finset (Finset (Fin U)) := fun s =>
      ((poolPk s.permKeyEmb).powersetCard m).filter
        fun B => (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    ∀ hne : ∀ s, (F_lt s).Nonempty,
      (((innerPoolDist (by omega) hV F_lt hne).map fun sb =>
        decide (IsSeedConsistent D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
          (U : ℝ) ^ (-γ * (m : ℝ)) ∧
        (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
          (((F_lt s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card : ℝ)) ≤
          (P.choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  dsimp only; intro hne
  set F_lt : HardKeyValSeed U V n → Finset (Finset (Fin U)) := fun s =>
    ((poolPk s.permKeyEmb).powersetCard m).filter fun B => (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let Fg (g : ℕ) (s : HardKeyValSeed U V n) : Finset (Finset (Fin U)) :=
    ((poolPk s.permKeyEmb).powersetCard m).filter fun B => (s.insertedSet t₀ m ht₀ ∩ B).card = g
  let cg (g : ℕ) : ℕ := m.choose g * (P - m).choose (m - g)
  have hFg_card (g : ℕ) (s : HardKeyValSeed U V n) : (Fg g s).card = cg g := by
    dsimp only [Fg, cg]
    rw [insertedSet_eq_pkeyInsEmb, card_inter_filter_powersetCard (hA_pool s.permKeyEmb)
      (by simp [Finset.card_image_of_injective _ (pkeyInsEmb s.permKeyEmb t₀ m ht₀).injective]),
      hcard_pool]
  have hFlt_biUnion (s : HardKeyValSeed U V n) :
      F_lt s = (Finset.range (m / 2)).biUnion (fun g => Fg g s) := by
    dsimp only [F_lt, Fg]; ext B
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro ⟨hB, hlt⟩
      exact ⟨(s.insertedSet t₀ m ht₀ ∩ B).card, hlt, hB, rfl⟩
    · rintro ⟨g, hg, hB, heq⟩
      exact ⟨hB, heq ▸ hg⟩
  have hdisj_g (s : HardKeyValSeed U V n) :
      ((Finset.range (m / 2) : Set ℕ)).PairwiseDisjoint (fun g => Fg g s) :=
    fun g₁ _ g₂ _ hne_g => Finset.disjoint_left.mpr fun B h₁ h₂ =>
      hne_g ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
  let clt : ℕ := ∑ g ∈ Finset.range (m / 2), cg g
  have hcard_Flt (s : HardKeyValSeed U V n) : (F_lt s).card = clt := by
    rw [hFlt_biUnion s, Finset.card_biUnion (hdisj_g s)]
    exact Finset.sum_congr rfl fun g _ => hFg_card g s
  have hclt_pos : (0 : ℝ) < (clt : ℝ) := by
    obtain ⟨s₀⟩ := ‹Nonempty (HardKeyValSeed U V n)›
    rw [← hcard_Flt s₀]; exact Nat.cast_pos.mpr (Finset.card_pos.mpr (hne s₀))
  have hclt_le : (clt : ℝ) ≤ (P.choose m : ℝ) := by
    obtain ⟨s₀⟩ := ‹Nonempty (HardKeyValSeed U V n)›
    rw [← hcard_Flt s₀]
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (by rw [Finset.card_powersetCard, hcard_pool])
  have hexp_g (g : ℕ) (hg : g ∈ Finset.range (m / 2)) :
      (∑ s, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        (((Fg g s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card : ℝ)) ≤
        (cg g : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
    have hg_lt : g < m / 2 := Finset.mem_range.mp hg
    have hne_g : ∀ s, (Fg g s).Nonempty := fun s => by
      simpa only [Fg, insertedSet_eq_pkeyInsEmb] using
        nonempty_pool_eq ht₀ (by omega) (by omega) poolPk hcard_pool hA_pool s.permKeyEmb
    have hcg_pos : (0 : ℝ) < (cg g : ℝ) := by
      obtain ⟨s₀⟩ := ‹Nonempty (HardKeyValSeed U V n)›
      rw [← hFg_card g s₀]; exact Nat.cast_pos.mpr (Finset.card_pos.mpr (hne_g s₀))
    have h1 := prob_innerPool_eq_le hU hV hm_n hg_lt ht₀ hγ hm_lo hspace hbudget hcorr
      poolPk hcard_pool hA_pool hdisj_pool hslot_pool huniv_pool (by omega) hne_g
    rw [prob_innerPoolDist_eq (by omega) hV (Fg g) (hFg_card g) hne_g] at h1
    exact (inv_mul_le_iff₀ hcg_pos).mp h1
  have hexp_lt :
      (∑ s, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        (((F_lt s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card : ℝ)) ≤
        (clt : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
    have hdecomp (s : HardKeyValSeed U V n) :
        (((F_lt s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card : ℝ) =
          ∑ g ∈ Finset.range (m / 2),
            (((Fg g s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)).card : ℝ) := by
      rw [hFlt_biUnion s, Finset.filter_biUnion]
      have hd : ((Finset.range (m / 2) : Set ℕ)).PairwiseDisjoint
          (fun g => (Fg g s).filter (IsSeedConsistent D_det t₀ m ht₀ γ t s)) :=
        fun g₁ hg₁ g₂ hg₂ hne_g => Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hdisj_g s hg₁ hg₂ hne_g))
      exact_mod_cast Finset.card_biUnion hd
    simp_rw [hdecomp, Finset.mul_sum]; rw [Finset.sum_comm]
    exact (Finset.sum_le_sum hexp_g).trans_eq (by rw [← Finset.sum_mul]; simp [clt])
  refine ⟨?_, hexp_lt.trans (mul_le_mul_of_nonneg_right hclt_le
    (Real.rpow_nonneg (Nat.cast_nonneg U) _))⟩
  rw [prob_innerPoolDist_eq (by omega) hV F_lt hcard_Flt hne]
  exact (inv_mul_le_iff₀ hclt_pos).mpr hexp_lt

private def sdiffPoolPk {U n : ℕ} (t₀ : ℕ) (ht : t₀ ≤ n) (pk : Fin (2 * n) ↪ Fin U) :
    Finset (Fin U) := Finset.univ \ pkeyActive pk t₀ ht

private def segRestPoolPk {U n : ℕ} (t₀ r_rest : ℕ) (hrest : t₀ + r_rest ≤ n)
    (pk : Fin (2 * n) ↪ Fin U) : Finset (Fin U) :=
  Finset.univ.image (pkeyInsEmb pk t₀ r_rest hrest)

private theorem activeKeys_eq_pkeyActive {U V n : ℕ} (s : HardKeyValSeed U V n)
    (t₀ : ℕ) (ht : t₀ ≤ n) : s.activeKeys t₀ ht = pkeyActive s.permKeyEmb t₀ ht := by
  simp [HardKeyValSeed.activeKeys, pkeyActive]

open Classical in
private theorem toReal_map_innerPoolDist_congr {U V n : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {F₁ F₂ : HardKeyValSeed U V n → Finset (Finset (Fin U))} (hF : F₁ = F₂)
    (hne₁ : ∀ s, (F₁ s).Nonempty) (hne₂ : ∀ s, (F₂ s).Nonempty)
    (f : HardKeyValSeed U V n × Finset (Fin U) → Bool) :
    (((innerPoolDist hU hV F₁ hne₁).map f) true).toReal =
      (((innerPoolDist hU hV F₂ hne₂).map f) true).toReal := by subst hF; rfl

private theorem sdiff_active_props {U n t₀ m : ℕ} (_hU : 2 * n ≤ U) (ht₀ : t₀ + m ≤ n) :
    have ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
    (∀ pk : Fin (2 * n) ↪ Fin U, (sdiffPoolPk t₀ ht₀_n pk).card = U - n) ∧
      (∀ pk : Fin (2 * n) ↪ Fin U,
        Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ sdiffPoolPk t₀ ht₀_n pk) ∧
      (∀ pk : Fin (2 * n) ↪ Fin U, Disjoint (sdiffPoolPk t₀ ht₀_n pk) (pkeyActive pk t₀ ht₀_n)) ∧
      (∀ γp, IsSlotPerm t₀ m γp → ∀ pk : Fin (2 * n) ↪ Fin U,
        sdiffPoolPk t₀ ht₀_n (γp.toEmbedding.trans pk) = sdiffPoolPk t₀ ht₀_n pk) ∧
      (∀ (τ : Equiv.Perm (Fin U)) (pk : Fin (2 * n) ↪ Fin U),
        sdiffPoolPk t₀ ht₀_n (pk.trans τ.toEmbedding) =
          (sdiffPoolPk t₀ ht₀_n pk).map τ.toEmbedding) := by
  have ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  refine ⟨fun pk => ?_, fun pk u hu => ?_, fun _ => Finset.sdiff_disjoint,
    fun γp hγ pk => ?_, fun τ pk => ?_⟩
  · have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (pkeyActive pk t₀ ht₀_n))
    have hact : (pkeyActive pk t₀ ht₀_n).card = n := by simp [pkeyActive]
    rw [Finset.card_univ, Fintype.card_fin, hact] at h
    dsimp only [sdiffPoolPk]; omega
  · rw [sdiffPoolPk, Finset.mem_sdiff]; refine ⟨Finset.mem_univ u, ?_⟩
    simp only [pkeyInsEmb, pkeyActive, Finset.mem_image, Finset.mem_map, Finset.mem_univ,
      true_and, windowEmb_apply] at hu ⊢
    obtain ⟨r, rfl⟩ := hu; rintro ⟨k, hk⟩; have := r.isLt; have := k.isLt
    have := congrArg Fin.val (pk.injective hk); dsimp at this; omega
  · dsimp only [sdiffPoolPk]; congr 1
    refine pkeyActive_perm_eq ht₀_n γp (fun i => ?_) pk
    by_cases h1 : t₀ ≤ i.val ∧ i.val < t₀ + m
    · have h1' := (hγ.1 i).mpr h1; omega
    · by_cases h2 : n + t₀ ≤ i.val ∧ i.val < n + t₀ + m
      · have h2' := (hγ.2.1 i).mpr h2; omega
      · rw [hγ.2.2 i h1 h2]
  · ext x; simp only [sdiffPoolPk, pkeyActive, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_map, windowEmb_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    exact ⟨fun hn => ⟨τ.symm x, fun ⟨k, hk⟩ => hn ⟨k, by rw [hk, τ.apply_symm_apply]⟩,
      τ.apply_symm_apply x⟩, fun ⟨y, hy, hyx⟩ ⟨k, hk⟩ => hy ⟨k, τ.injective (hk.trans hyx.symm)⟩⟩

private theorem segRest_props {U n t₀ m r_rest : ℕ} (ht₀ : t₀ + m ≤ n)
    (hm_rest : m ≤ r_rest) (hrest : t₀ + r_rest ≤ n) :
    have ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
    (∀ pk : Fin (2 * n) ↪ Fin U, (segRestPoolPk t₀ r_rest hrest pk).card = r_rest) ∧
      (∀ pk : Fin (2 * n) ↪ Fin U,
        Finset.univ.image (pkeyInsEmb pk t₀ m ht₀) ⊆ segRestPoolPk t₀ r_rest hrest pk) ∧
      (∀ pk : Fin (2 * n) ↪ Fin U,
        Disjoint (segRestPoolPk t₀ r_rest hrest pk) (pkeyActive pk t₀ ht₀_n)) ∧
      (∀ γp, IsSlotPerm t₀ m γp → ∀ pk : Fin (2 * n) ↪ Fin U,
        segRestPoolPk t₀ r_rest hrest (γp.toEmbedding.trans pk) =
          segRestPoolPk t₀ r_rest hrest pk) ∧
      (∀ (τ : Equiv.Perm (Fin U)) (pk : Fin (2 * n) ↪ Fin U),
        segRestPoolPk t₀ r_rest hrest (pk.trans τ.toEmbedding) =
          (segRestPoolPk t₀ r_rest hrest pk).map τ.toEmbedding) := by
  refine ⟨fun pk => by
      simp [segRestPoolPk,
        Finset.card_image_of_injective _ (pkeyInsEmb pk t₀ r_rest hrest).injective],
    fun pk u hu => ?_, fun pk => Finset.disjoint_left.mpr fun u hu hk => ?_,
    fun γp hγ pk => ?_, fun τ pk => ?_⟩
  · simp only [segRestPoolPk, pkeyInsEmb, Finset.mem_image, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨r, rfl⟩ := hu; exact ⟨⟨r.val, by have := r.isLt; omega⟩, rfl⟩
  · simp only [segRestPoolPk, pkeyInsEmb, pkeyActive, Finset.mem_image, Finset.mem_map,
      Finset.mem_univ, true_and, windowEmb_apply] at hu hk
    obtain ⟨j, rfl⟩ := hu; obtain ⟨k, hk⟩ := hk; have := j.isLt; have := k.isLt
    have := congrArg Fin.val (pk.injective hk); dsimp at this; omega
  · have hmem (γ' : Equiv.Perm (Fin (2 * n))) (hγ' : IsSlotPerm t₀ m γ')
        (pk' : Fin (2 * n) ↪ Fin U) :
        segRestPoolPk t₀ r_rest hrest (γ'.toEmbedding.trans pk') ⊆
          segRestPoolPk t₀ r_rest hrest pk' := fun u hu => by
      simp only [segRestPoolPk, pkeyInsEmb, Finset.mem_image, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk, Function.Embedding.trans_apply] at hu ⊢
      obtain ⟨j, rfl⟩ := hu; have hj_lt := j.isLt
      let i₀ : Fin (2 * n) := ⟨n + t₀ + j.val, by omega⟩
      have hi₀ : n + t₀ ≤ (γ' i₀).val ∧ (γ' i₀).val < n + t₀ + r_rest := by
        by_cases h2 : n + t₀ ≤ i₀.val ∧ i₀.val < n + t₀ + m
        · have := (hγ'.2.1 i₀).mpr h2; omega
        · rw [hγ'.2.2 i₀ (by dsimp [i₀]; omega) h2]; dsimp [i₀]; omega
      exact ⟨⟨(γ' i₀).val - (n + t₀), by omega⟩,
        congrArg pk' (Fin.ext (by change n + t₀ + ((γ' i₀).val - (n + t₀)) = (γ' i₀).val; omega))⟩
    exact Finset.Subset.antisymm (hmem γp hγ pk) (by
      have h2 := hmem γp.symm hγ.symm (γp.toEmbedding.trans pk)
      have heq : γp.symm.toEmbedding.trans (γp.toEmbedding.trans pk) = pk := by ext i; simp
      rwa [heq] at h2)
  · ext u; simp only [segRestPoolPk, pkeyInsEmb, Finset.mem_image, Finset.mem_map,
      Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, Function.Embedding.trans_apply]
    exact ⟨fun ⟨j, h⟩ => ⟨pk ⟨n + t₀ + j.val, _⟩, ⟨j, rfl⟩, h⟩,
      fun ⟨_, ⟨j, rfl⟩, h⟩ => ⟨j, h⟩⟩

open Classical in
/-- Conditional joint distribution of `(seed, B)` in the Section 5 Inner Game ([LiLiangYuZhou2023],
Section 5, p. 21 / PDF p. 22): `seed` is uniform on `HardKeyValSeed U V n` and `B` is
uniform among size-`m` subsets of `Finset.univ \ s.activeKeys t₀` with `|A ∩ B| = g`. -/
noncomputable def section5Dist {U V n : ℕ} (t₀ m g : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (_hm_n : 2 * m ≤ n) (hg : g < m / 2) (ht₀ : t₀ + m ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((Finset.univ \ s.activeKeys t₀ (by omega)).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card = g))
    (fun s => by
      have hp := sdiff_active_props (U := U) (by omega) ht₀
      simpa only [sdiffPoolPk, activeKeys_eq_pkeyActive, insertedSet_eq_pkeyInsEmb] using
        nonempty_pool_eq ht₀ (by omega) (by omega) _ hp.1 hp.2.1 s.permKeyEmb)

open Classical in
/-- Conditional joint distribution of `(seed, B)` in the Section 5 Inner Game conditioned on
`|A ∩ B| < m / 2` ([LiLiangYuZhou2023], Section 4.3, Lemma 4.4, p. 18 / PDF p. 19 and Section 5,
p. 20 / PDF p. 21). -/
noncomputable def section5LtHalfDist {U V n : ℕ} (t₀ m : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (_hm_n : 2 * m ≤ n) (ht₀ : t₀ + m ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((Finset.univ \ s.activeKeys t₀ (by omega)).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2))
    (fun s => by
      have hp := sdiff_active_props (U := U) (by omega) ht₀
      simpa only [sdiffPoolPk, activeKeys_eq_pkeyActive, insertedSet_eq_pkeyInsEmb] using
        nonempty_pool_lt ht₀ hm (by omega) _ hp.1 hp.2.1 s.permKeyEmb)

open Classical in
/-- Conditional joint distribution of `(seed, B)` when `B` is drawn uniformly from size-`m` subsets
of the remaining multi-round pool `s.insertedSet t₀ r_rest` with `|A ∩ B| = g`
([LiLiangYuZhou2023], Section 4.2, p. 15 / PDF p. 16 and Section 4.3, Lemma 4.4, p. 18 /
PDF p. 19). -/
noncomputable def segmentRestDist {U V n : ℕ} (t₀ m r_rest g : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hg : g < m / 2) (_hrest_ge : 2 * m ≤ r_rest)
    (hrest : t₀ + r_rest ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m (by omega) ∩ B).card = g))
    (fun s => by
      have hp := segRest_props (U := U) (m := m) (by omega) (by omega) hrest
      simpa only [segRestPoolPk, insertedSet_eq_pkeyInsEmb] using
        nonempty_pool_eq (by omega) (by omega) (by omega) _ hp.1 hp.2.1 s.permKeyEmb)

open Classical in
/-- Conditional joint distribution of `(seed, B)` when `B` is drawn uniformly from size-`m` subsets
of `s.insertedSet t₀ r_rest` with `|A ∩ B| < m / 2` ([LiLiangYuZhou2023], Section 4.3, Lemma 4.4,
p. 18 / PDF p. 19). -/
noncomputable def segmentRestLtHalfDist {U V n : ℕ} (t₀ m r_rest : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hrest_ge : 2 * m ≤ r_rest)
    (hrest : t₀ + r_rest ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m (by omega) ∩ B).card < m / 2))
    (fun s => by
      have hp := segRest_props (U := U) (m := m) (by omega) (by omega) hrest
      simpa only [segRestPoolPk, insertedSet_eq_pkeyInsEmb] using
        nonempty_pool_lt (by omega) hm hrest_ge _ hp.1 hp.2.1 s.permKeyEmb)

open Classical in
/-- Pointwise probability density of `section5Dist` on seed-candidate pair `(s, B)`. -/
theorem toReal_section5Dist_apply {U V n : ℕ} (t₀ m g : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm_n : 2 * m ≤ n) (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    let pool := ((Finset.univ \ s.activeKeys t₀ (by omega)).powersetCard m).filter fun B' =>
      (s.insertedSet t₀ m ht₀ ∩ B').card = g
    ((section5Dist t₀ m g hU hV hm_n hg ht₀) (s, B)).toReal =
      if B ∈ pool then
        ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal / (pool.card : ℝ)
      else 0 :=
  toReal_innerPoolDist_apply (by omega) hV _ _ s B

open Classical in
/-- Pointwise probability density of `section5LtHalfDist` on seed-candidate pair `(s, B)`. -/
theorem toReal_section5LtHalfDist_apply {U V n : ℕ} (t₀ m : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n) (ht₀ : t₀ + m ≤ n)
    (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    let pool := ((Finset.univ \ s.activeKeys t₀ (by omega)).powersetCard m).filter fun B' =>
      (s.insertedSet t₀ m ht₀ ∩ B').card < m / 2
    ((section5LtHalfDist t₀ m hU hV hm hm_n ht₀) (s, B)).toReal =
      if B ∈ pool then
        ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal / (pool.card : ℝ)
      else 0 :=
  toReal_innerPoolDist_apply (by omega) hV _ _ s B

open Classical in
/-- Pointwise probability density of `segmentRestDist` on seed-candidate pair `(s, B)`. -/
theorem toReal_segmentRestDist_apply {U V n : ℕ} (t₀ m r_rest g : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hg : g < m / 2) (hrest_ge : 2 * m ≤ r_rest)
    (hrest : t₀ + r_rest ≤ n) (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    let pool := ((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B' =>
      (s.insertedSet t₀ m (by omega) ∩ B').card = g
    ((segmentRestDist t₀ m r_rest g hU hV hg hrest_ge hrest) (s, B)).toReal =
      if B ∈ pool then
        ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal / (pool.card : ℝ)
      else 0 :=
  toReal_innerPoolDist_apply (by omega) hV _ _ s B

open Classical in
/-- Pointwise probability density of `segmentRestLtHalfDist` on seed-candidate pair `(s, B)`. -/
theorem toReal_segmentRestLtHalfDist_apply {U V n : ℕ} (t₀ m r_rest : ℕ)
    (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hrest_ge : 2 * m ≤ r_rest)
    (hrest : t₀ + r_rest ≤ n) (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    let pool := ((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B' =>
      (s.insertedSet t₀ m (by omega) ∩ B').card < m / 2
    ((segmentRestLtHalfDist t₀ m r_rest hU hV hm hrest_ge hrest) (s, B)).toReal =
      if B ∈ pool then
        ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal / (pool.card : ℝ)
      else 0 :=
  toReal_innerPoolDist_apply (by omega) hV _ _ s B

section PublicBounds

variable {U V n t₀ m cells w : ℕ} {γ R t : ℝ}
  (hU : 4 * n ≤ U) (hV : 1 ≤ V) (hm_n : 2 * m ≤ n)
  (hγ : 0 < γ) (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (m : ℝ))
  (hspace : ((cells * w : ℕ) : ℝ) ≤ Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 V + R)
  (hbudget : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
    (3 / 2) * γ * (m : ℝ) * Real.logb 2 U ≤ ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
  {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
  (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
    (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)

include hU hV hm_n hγ hm_lo hspace hbudget hcorr

open Classical in
/-- Inner Lemma ([LiLiangYuZhou2023], Section 5, Lemma 5.1, p. 21 / PDF p. 22, adapted with the
`c = 1` deterministic probe cap and Elias-gamma `β = 2` separator): conditioned on `|A ∩ B| = g`
(`g < m / 2`) for uniform size-`m` `B ⊆ Finset.univ \ K`, `Pr[IsSeedConsistent] ≤ U ^ (-γ * m)`.

In the paper setting where `w = Θ(log U)`, hypothesis `hbudget` corresponds
to Lemma 5.1's premise `(1/2) * γ * m * log₂ U ≥ R + 5 * m + 2 * (β + 1) * m * t` (p. 21 / PDF
p. 22) and Eq. (14) (p. 24 / PDF p. 25) with `6 * m * t + 11 * m` separator and prefix-free
overhead, which holds for sufficiently small constant `γ > 0`. -/
theorem prob_isCappedConsistent_section5_le {g : ℕ} (hg : g < m / 2) (ht₀ : t₀ + m ≤ n) :
    (((section5Dist t₀ m g hU hV hm_n hg ht₀).map fun sb =>
      decide (IsSeedConsistent D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have hp := sdiff_active_props (U := U) (by omega) ht₀
  have hne : ∀ s : HardKeyValSeed U V n,
      (((sdiffPoolPk t₀ (by omega) s.permKeyEmb).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card = g).Nonempty := fun s => by
    simpa only [insertedSet_eq_pkeyInsEmb] using
      nonempty_pool_eq ht₀ (by omega) (by omega) _ hp.1 hp.2.1 s.permKeyEmb
  rw [section5Dist, toReal_map_innerPoolDist_congr (by omega) hV
    (funext fun s => by simp only [sdiffPoolPk, activeKeys_eq_pkeyActive]) _ hne]
  exact prob_innerPool_eq_le hU hV hm_n hg ht₀ hγ hm_lo hspace hbudget hcorr
    (sdiffPoolPk t₀ (by omega)) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 (by omega) hne

open Classical in
/-- Inner Lemma for `|A ∩ B| < m / 2` ([LiLiangYuZhou2023], Section 4.3, Lemma 4.4, p. 18 /
PDF p. 19 and Section 5.2, p. 25 / PDF p. 26): over `B ⊆ Finset.univ \ K` conditioned on
`|A ∩ B| < m / 2`, `Pr[IsSeedConsistent] ≤ U ^ (-γ * m)`.

Under `w = Θ(log U)`, `hbudget` reflects Lemma 5.1's premise
`(1/2) * γ * m * log₂ U ≥ R + 5 * m + 2 * (β + 1) * m * t` (p. 21 / PDF p. 22) and Eq. (14)
(p. 24 / PDF p. 25). -/
theorem prob_isCappedConsistent_section5_lt_half_le (hm : 2 ≤ m) (ht₀ : t₀ + m ≤ n) :
    (((section5LtHalfDist t₀ m hU hV hm hm_n ht₀).map fun sb =>
      decide (IsSeedConsistent D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have hp := sdiff_active_props (U := U) (by omega) ht₀
  have hne : ∀ s : HardKeyValSeed U V n,
      (((sdiffPoolPk t₀ (by omega) s.permKeyEmb).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).Nonempty := fun s => by
    simpa only [insertedSet_eq_pkeyInsEmb] using
      nonempty_pool_lt ht₀ hm (by omega) _ hp.1 hp.2.1 s.permKeyEmb
  rw [section5LtHalfDist, toReal_map_innerPoolDist_congr (by omega) hV
    (funext fun s => by simp only [sdiffPoolPk, activeKeys_eq_pkeyActive]) _ hne]
  exact (prob_and_expect_innerPool_lt_half_le hU hV hm hm_n ht₀ hγ hm_lo hspace hbudget hcorr
    (sdiffPoolPk t₀ (by omega)) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 (by omega) hne).1

open Classical in
/-- Inner Lemma on the multi-round remaining pool ([LiLiangYuZhou2023], Section 4.2, p. 15 /
PDF p. 16 and Section 5, Lemma 5.1, p. 21 / PDF p. 22): conditioned on `|A ∩ B| = g` (`g < m / 2`)
for uniform `B ⊆ s.insertedSet t₀ r_rest` (`2 * m ≤ r_rest`),
`Pr[IsSeedConsistent] ≤ U ^ (-γ * m)`. -/
theorem prob_isCappedConsistent_segmentRest_le {r_rest g : ℕ} (hg : g < m / 2)
    (hrest_ge : 2 * m ≤ r_rest) (hrest : t₀ + r_rest ≤ n) :
    (((segmentRestDist t₀ m r_rest g hU hV hg hrest_ge hrest).map fun sb =>
      decide (IsSeedConsistent D_det t₀ m (by omega) γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have ht₀ : t₀ + m ≤ n := by omega
  have hp := segRest_props (U := U) ht₀ (by omega) hrest
  have hne : ∀ s : HardKeyValSeed U V n,
      (((segRestPoolPk t₀ r_rest hrest s.permKeyEmb).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card = g).Nonempty := fun s => by
    simpa only [insertedSet_eq_pkeyInsEmb] using
      nonempty_pool_eq ht₀ (by omega) (by omega) _ hp.1 hp.2.1 s.permKeyEmb
  rw [segmentRestDist, toReal_map_innerPoolDist_congr (by omega) hV
    (funext fun s => by simp only [segRestPoolPk, insertedSet_eq_pkeyInsEmb]) _ hne]
  exact prob_innerPool_eq_le hU hV hm_n hg ht₀ hγ hm_lo hspace hbudget hcorr
    (segRestPoolPk t₀ r_rest hrest) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 (by omega) hne

open Classical in
/-- Inner Lemma on the multi-round remaining pool for `|A ∩ B| < m / 2` ([LiLiangYuZhou2023],
Section 4.3, Lemma 4.4, p. 18 / PDF p. 19): conditioned on `|A ∩ B| < m / 2` for uniform
`B ⊆ s.insertedSet t₀ r_rest` (`2 * m ≤ r_rest`), `Pr[IsSeedConsistent] ≤ U ^ (-γ * m)`. -/
theorem prob_isCappedConsistent_segmentRest_lt_half_le {r_rest : ℕ} (hm : 2 ≤ m)
    (hrest_ge : 2 * m ≤ r_rest) (hrest : t₀ + r_rest ≤ n) :
    (((segmentRestLtHalfDist t₀ m r_rest hU hV hm hrest_ge hrest).map fun sb =>
      decide (IsSeedConsistent D_det t₀ m (by omega) γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have ht₀ : t₀ + m ≤ n := by omega
  have hp := segRest_props (U := U) ht₀ (by omega) hrest
  have hne : ∀ s : HardKeyValSeed U V n,
      (((segRestPoolPk t₀ r_rest hrest s.permKeyEmb).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).Nonempty := fun s => by
    simpa only [insertedSet_eq_pkeyInsEmb] using
      nonempty_pool_lt ht₀ hm hrest_ge _ hp.1 hp.2.1 s.permKeyEmb
  rw [segmentRestLtHalfDist, toReal_map_innerPoolDist_congr (by omega) hV
    (funext fun s => by simp only [segRestPoolPk, insertedSet_eq_pkeyInsEmb]) _ hne]
  exact (prob_and_expect_innerPool_lt_half_le hU hV hm hm_n ht₀ hγ hm_lo hspace hbudget hcorr
    (segRestPoolPk t₀ r_rest hrest) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hrest_ge hne).1

open Classical in
/-- Expected far-consistent candidate count ([LiLiangYuZhou2023], Section 4.3, Claim 4.2 and
Lemma 4.4, pp. 17–18 / PDF pp. 18–19): over uniform `s : HardKeyValSeed U V n`, the expected
number of size-`m` subsets `B ⊆ s.insertedSet t₀ r_rest` with `|A ∩ B| < m / 2` that satisfy
`IsSeedConsistent` is at most `(r_rest.choose m : ℝ) * (U : ℝ) ^ (-γ * m)`. -/
theorem expected_card_cappedConsistent_segmentRest_lt_half_le {r_rest : ℕ} (hm : 2 ≤ m)
    (hrest_ge : 2 * m ≤ r_rest) (hrest : t₀ + r_rest ≤ n) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
      ((((((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m (by omega) ∩ B).card < m / 2)).filter
          (IsSeedConsistent D_det t₀ m (by omega) γ t s)).card : ℝ)) ≤
      (r_rest.choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  have ht₀ : t₀ + m ≤ n := by omega
  have hp := segRest_props (U := U) ht₀ (by omega) hrest
  have hne : ∀ s : HardKeyValSeed U V n,
      (((segRestPoolPk t₀ r_rest hrest s.permKeyEmb).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).Nonempty := fun s => by
    simpa only [insertedSet_eq_pkeyInsEmb] using
      nonempty_pool_lt ht₀ hm hrest_ge _ hp.1 hp.2.1 s.permKeyEmb
  have h2 := (prob_and_expect_innerPool_lt_half_le hU hV hm hm_n ht₀ hγ hm_lo hspace hbudget
    hcorr (segRestPoolPk t₀ r_rest hrest) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hrest_ge hne).2
  simpa only [segRestPoolPk, insertedSet_eq_pkeyInsEmb] using h2

end PublicBounds

end Cslib.DataStructure.Dictionary.CellProbe
