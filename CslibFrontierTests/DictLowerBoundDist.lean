/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.HardDist
public import CslibFrontier.DataStructure.Dictionary.CellProbe.MetaTree

/-!
# FOCS 2023 Dictionary Hard Distributions and LCA Meta-Operation Tree Tests

Kernel-checked non-vacuity and edge-case witnesses for
`CslibFrontier.DataStructure.Dictionary.CellProbe.HardDist` and
`CslibFrontier.DataStructure.Dictionary.CellProbe.MetaTree`:

1. Concrete small-parameter instances `(U = 4, V = 2, n = 2)` and edge case `n = 0` for `validOps`,
   `SizedDict`, `insertQueryDeleteDist` (`4 * n` operations), and `insertDeleteDist` (`3 * n`
   update-only operations with zero `.query` steps), verifying admissibility and exact uniform
   size-`n` state marginals.
2. Direct-mapped deterministic `CellProbe.Scheme` implementing `Dynamic.spec 4 2 2` across **all**
   admissible histories (`validHistoriesUpTo`), exercising `decodeDict`,
   `step_query_eq_none_of_notMem_dom`, and zero-error Yao coin-fixing
   (`exists_det_indexedScheme_insertQueryDeleteDist` and
   `exists_det_indexedScheme_insertDeleteDist`).
3. Adversarial soundness witness: a `0`-probe scheme returning `some 0` on every `.query` agrees
   with `Dynamic.spec 4 2 2` on every update-only sequence in
   `(insertDeleteDist 4 2 2 ...).support`, yet is rejected by
   `validHistoriesUpTo 4 2 2 (3 * 2 + 1)`.
4. Divisibility-free `MetaTree` packing (`horizon = 9`), `geomMetaTree` and `iterLogMetaTree`
   properties, global LCA probe conservation (`sum_nodeCost_le_seqProbes`), Eq. (5) bad-cell
   intersection bound on a `3`-hit (`s = 3`) witness, post-memory qualification soundness, and
   `mixMem` replay + non-intersection recovery.
-/

public section

namespace CslibFrontierTests.DictLowerBoundDist

open Cslib Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.CellProbe
open scoped ENNReal

/-! ### 1. Finite operation alphabet, `SizedDict`, and hard distributions -/

example : (validOps 4 2).card = 16 := by
  rw [card_validOps]

example : Fintype.card (SizedDict 4 2 2) = 24 := by
  rw [card_sizedDict]
  decide

example : Fintype.card (SizedDict 4 1 0) = 1 := by
  rw [card_sizedDict]
  decide

theorem zero_horizon_dists_valid :
    (validOps 4 1).card = 12 ∧
    (∀ ops ∈ (insertQueryDeleteDist 4 1 0 (by omega) (by omega)).support,
      ops = [] ∧ (Dynamic.spec 4 1 0).ValidHistory (Dictionary.empty 4) ops) ∧
    (∀ ops ∈ (insertDeleteDist 4 1 0 (by omega) (by omega)).support,
      ops = [] ∧ (Dynamic.spec 4 1 0).ValidHistory (Dictionary.empty 4) ops) := by
  refine ⟨by rw [card_validOps], fun ops hops => ?_, fun ops hops => ?_⟩
  · exact ⟨List.length_eq_zero_iff.mp (length_of_mem_support_insertQueryDeleteDist hops),
      (validHistory_of_mem_support_insertQueryDeleteDist hops).1⟩
  · exact ⟨List.length_eq_zero_iff.mp (length_of_mem_support_insertDeleteDist hops),
      (validHistory_of_mem_support_insertDeleteDist hops).1⟩

theorem insertQueryDeleteDist_four_two_valid :
    ∀ ops ∈ (insertQueryDeleteDist 4 2 2 (by omega) (by omega)).support,
      ops.length = 8 ∧
      (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) ops ∧
      (∀ o ∈ ops, o ∈ validOps 4 2) := by
  intro ops hops
  obtain ⟨hvh, halph⟩ := validHistory_of_mem_support_insertQueryDeleteDist hops
  exact ⟨length_of_mem_support_insertQueryDeleteDist hops, hvh, halph⟩

theorem insertDeleteDist_four_two_update_only :
    ∀ ops ∈ (insertDeleteDist 4 2 2 (by omega) (by omega)).support,
      ops.length = 6 ∧
      (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) ops ∧
      (∀ o ∈ ops, ¬ ∃ u, o = .query u) := by
  intro ops hops
  exact ⟨length_of_mem_support_insertDeleteDist hops,
    (validHistory_of_mem_support_insertDeleteDist hops).1,
     fun _ ho => not_isQuery_of_mem_support_insertDeleteDist hops ho⟩

theorem marginal_uniform_at_all_boundaries (t : ℕ) (ht : t ≤ 2) :
    letI : Nonempty ({ K : Finset (Fin 4) // K.card = 2 } × (Fin 2 → Fin 2)) :=
      ⟨⟨⟨{0, 1}, by decide⟩, fun _ => 0⟩⟩
    (insertQueryDeleteDist 4 2 2 (by omega) (by omega)).map
      (fun ops => extractKeySetVals (U := 4) (V := 2) (n := 2) (by omega) (by omega)
        ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) (ops.take (2 + 3 * t))).1) =
    (insertDeleteDist 4 2 2 (by omega) (by omega)).map
      (fun ops => extractKeySetVals (U := 4) (V := 2) (n := 2) (by omega) (by omega)
        ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) (ops.take (2 + 2 * t))).1) := by
  rw [map_extractKeySetVals_insertQueryDeleteDist (by omega) (by omega) ht,
    map_extractKeySetVals_insertDeleteDist (by omega) (by omega) ht]

/-! ### 2. Concrete direct-mapped `Scheme` for `Dynamic.spec 4 2 2` and `decodeDict` -/

/-- Encode `Option ℕ` (for values `< 2`) into `Fin (2 ^ 2)`: `none ↦ 0`, `some v ↦ (v % 2) + 1`. -/
@[expose] def encodeSlot : Option ℕ → Fin (2 ^ 2)
  | none => ⟨0, by decide⟩
  | some v => ⟨(v % 2) + 1, by omega⟩

/-- Decode `Fin (2 ^ 2)` back to `Option ℕ`: `0 ↦ none`, `c + 1 ↦ some c`. -/
@[expose] def decodeSlot (w : Fin (2 ^ 2)) : Option ℕ :=
  if w.1 = 0 then none else some (w.1 - 1)

/-- Direct-mapped 4-cell, 2-bit deterministic cell-probe dictionary for `U = 4, V = 2`. -/
@[expose] def directDictScheme : Scheme (Dynamic.Op 4) Dynamic.Op.Result 4 2 where
  init := zeroMem 4 2
  step
    | .insert u v => ProbeTree.write u ⟨(v % 2) + 1, by omega⟩
    | .delete u => ProbeTree.write u ⟨0, by decide⟩
    | .query u => do
        let w ← ProbeTree.read u
        return decodeSlot w

/-- Representation invariant: cell `u` holds `encodeSlot (s u)` for every `V = 2`-bounded state. -/
def DirectRep (s : Dictionary.State 4) (m : Mem 4 2) : Prop :=
  Dictionary.ValuesBounded 2 s ∧ ∀ u : Fin 4, m u = encodeSlot (s u)

private theorem directRep_empty : DirectRep (Dictionary.empty 4) (zeroMem 4 2) :=
  ⟨Dictionary.valuesBounded_empty 4 2, fun _ => rfl⟩

private theorem directDictScheme_step_correct {s : Dictionary.State 4} {m : Mem 4 2}
    (hrep : DirectRep s m) (o : Dynamic.Op 4)
    (hvalid : (Dynamic.spec 4 2 2).valid s o) :
    let out := (directDictScheme.step o).run m
    out.1 = (Dynamic.step s o).2 ∧
      DirectRep ((Dynamic.step s o).1) out.2 := by
  have hbnd' : Dictionary.ValuesBounded 2 ((Dynamic.spec 4 2 2).stepFn s o).1 :=
    Dynamic.valuesBounded_step_of_valid hrep.1 hvalid
  rcases hrep with ⟨hbnd, hcells⟩
  cases o with
  | insert u v =>
    refine ⟨rfl, ⟨hbnd', fun x => ?_⟩⟩
    change Function.update m u ⟨(v % 2) + 1, _⟩ x = encodeSlot (Function.update s u (some v) x)
    by_cases hxu : x = u
    · subst hxu
      simp [encodeSlot]
    · simp [Function.update_of_ne hxu, hcells x]
  | delete u =>
    refine ⟨rfl, ⟨hbnd', fun x => ?_⟩⟩
    change Function.update m u ⟨0, _⟩ x = encodeSlot (Function.update s u none x)
    by_cases hxu : x = u
    · subst hxu
      simp [encodeSlot]
    · simp [Function.update_of_ne hxu, hcells x]
  | query u =>
    have hread : ((directDictScheme.step (.query u)).run m) = (decodeSlot (m u), m) := rfl
    rw [hread, hcells u]
    refine ⟨?_, ⟨hbnd, hcells⟩⟩
    cases hsu : s u with
    | none => simp [encodeSlot, decodeSlot, hsu]
    | some val =>
      have hval_lt : val < 2 := hbnd u val hsu
      have hmod : val % 2 = val := Nat.mod_eq_of_lt hval_lt
      simp [encodeSlot, decodeSlot, hsu, hmod]

private theorem directDictScheme_runInterval_correct :
    ∀ (ops : List (Dynamic.Op 4)) (t₀ : ℕ) (s : Dictionary.State 4) (m : Mem 4 2),
      DirectRep s m →
      (Dynamic.spec 4 2 2).ValidHistory s ops →
      (directDictScheme.toIndexed.runInterval t₀ m ops).1 = ((Dynamic.spec 4 2 2).run s ops).2 := by
  intro ops
  induction ops with
  | nil => intros; rfl
  | cons o rest ih =>
    intro t₀ s m hrep hvh
    obtain ⟨hvalid, hvh_rest⟩ := hvh
    obtain ⟨hout, hrep'⟩ := directDictScheme_step_correct hrep o hvalid
    have hcons : directDictScheme.toIndexed.runInterval t₀ m (o :: rest) =
        (⟨o, ((directDictScheme.step o).run m).1⟩ ::
          (directDictScheme.toIndexed.runInterval (t₀ + 1)
            ((directDictScheme.step o).run m).2 rest).1,
         (directDictScheme.toIndexed.runInterval (t₀ + 1)
            ((directDictScheme.step o).run m).2 rest).2) := rfl
    rw [hcons, StateTransitionSpec.run_cons]
    dsimp only
    rw [hout, ih (t₀ + 1) _ _ hrep' hvh_rest]

/-- `directDictScheme.toIndexed` satisfies `validHistoriesUpTo` for every horizon `M`. -/
theorem directDictScheme_all_histories (M : ℕ) :
    ∀ ops ∈ validHistoriesUpTo 4 2 2 M,
      (directDictScheme.toIndexed.runSeq ops).1 =
        ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2 := by
  intro ops hops
  exact directDictScheme_runInterval_correct ops 0 _ _ directRep_empty hops.1

/-- Sequential `insert → insert → query → delete → insert` composition test exercising
`decodeDict_runSeq_eq` and `step_query_eq_none_of_notMem_dom`. -/
theorem decodeDict_sequential_trace :
    let keys : Fin 4 ↪ Fin 4 := Function.Embedding.refl (Fin 4)
    let vals : Fin 4 → Fin 2 := ![1, 0, 1, 0]
    let pref : List (Dynamic.Op 4) := (insertQueryDeleteSeq (n := 2) keys vals).take 5
    decodeDict directDictScheme.toIndexed pref.length (directDictScheme.toIndexed.runSeq pref).2 =
      ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) pref).1 ∧
    ((directDictScheme.toIndexed.step pref.length (.query 0)).run
      (directDictScheme.toIndexed.runSeq pref).2).1 = none := by
  intro keys vals pref
  have htake := validHistory_and_run_take_insertQueryDeleteSeq (n := 2) keys vals
    (t := 1) (by omega)
  have hlen : pref.length ≤ 5 := List.length_take_le 5 _
  refine ⟨decodeDict_runSeq_eq (directDictScheme_all_histories 6) htake.1 hlen, ?_⟩
  refine step_query_eq_none_of_notMem_dom (directDictScheme_all_histories 6) htake.1 hlen ?_
  rw [htake.2, windowDict_coe, dom_dictOfEmb]
  simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists, windowEmb_apply]
  intro k hk
  have hk_val : 1 + k.1 = 0 := congrArg Fin.val hk
  omega

/-- Certified `StateTransitionImpl` bundling `directDictScheme` with worst-case charge `1`. -/
def directDictImpl :
    DataStructure.CellProbe.StateTransitionImpl (Dynamic.spec 4 2 2) directDictScheme
      (Dictionary.empty 4) :=
  DataStructure.CellProbe.StateTransitionImpl.ofFn DirectRep (fun _ _ => 1) directRep_empty
    (step_exec := fun s m o hrep hvalid => by
      obtain ⟨hout, hrep'⟩ := directDictScheme_step_correct hrep o hvalid
      refine ⟨hout, hrep', ?_⟩
      cases o <;> exact le_rfl)

@[simp]
private theorem directDictImpl_charge (s : Dictionary.State 4) (o : Dynamic.Op 4) :
    directDictImpl.charge s o = 1 := by
  rfl

/-- Direct instantiation of `exists_det_indexedScheme_insertQueryDeleteDist` and
`exists_det_indexedScheme_insertDeleteDist` on `directDictImpl.toRandomized`. -/
theorem yao_coin_fixing_directDict :
    let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic directDictScheme
    (∃ D_det ∈ (P.indexedSchemeLaw 9 (validOps 4 2)).support,
      ∀ ops ∈ validHistoriesUpTo 4 2 2 9,
        (D_det.runSeq ops).1 = ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) ∧
    (∃ D_det ∈ (P.indexedSchemeLaw 7 (validOps 4 2)).support,
      ∀ ops ∈ validHistoriesUpTo 4 2 2 7,
        (D_det.runSeq ops).1 = ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) := by
  set P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic directDictScheme
  have hC :=
    (directDictImpl.toObliviousSequenceImpl (fun _ => 1) (fun _ _ _ => by simp)).contract_runSeq
  obtain ⟨D₁, hD₁_mem, hD₁_corr, _⟩ :=
    exists_det_indexedScheme_insertQueryDeleteDist (n := 2) (by omega) (by omega) P
      (fun _ hops => hC (by simpa [StateTransitionSpec.toObliviousSequenceSpec] using hops.1))
  obtain ⟨D₂, hD₂_mem, hD₂_corr, _⟩ :=
    exists_det_indexedScheme_insertDeleteDist (n := 2) (by omega) (by omega) P
      (fun _ hops => hC (by simpa [StateTransitionSpec.toObliviousSequenceSpec] using hops.1))
  exact ⟨⟨D₁, hD₁_mem, hD₁_corr⟩, ⟨D₂, hD₂_mem, hD₂_corr⟩⟩

private theorem one_le_seqProbes_of_two_postStates {cells w M : ℕ}
    (D_det : IndexedScheme (Dynamic.Op 4) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo 4 2 2 (M + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2)
    {opsA opsB : List (Dynamic.Op 4)}
    (hlenA : opsA.length = M) (hlenB : opsB.length = M)
    (hvhA : (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) opsA)
    (hvhB : (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) opsB)
    (hne : ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) opsA).1 0 ≠
      ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) opsB).1 0) :
    1 ≤ D_det.seqProbes opsA ∨ 1 ≤ D_det.seqProbes opsB := by
  by_contra hboth
  push Not at hboth
  have hmem_init : ∀ {ops : List (Dynamic.Op 4)}, D_det.seqProbes ops < 1 →
      (D_det.runSeq ops).2 = D_det.init := by
    intro ops h0
    have hcard := D_det.card_probedCellsInterval_le_probesInterval 0 D_det.init ops
    change (D_det.probedCellsSeq ops).card ≤ D_det.seqProbes ops at hcard
    have hemp : D_det.probedCellsSeq ops = ∅ := Finset.card_eq_zero.mp (by omega)
    funext j
    exact D_det.nextMem_runSeq_eq_of_notMem_probedCellsSeq ops (by simp [hemp])
  have hdecA := decodeDict_runSeq_eq hcorr hvhA hlenA.le
  have hdecB := decodeDict_runSeq_eq hcorr hvhB hlenB.le
  rw [hlenA, hmem_init hboth.1] at hdecA
  rw [hlenB, hmem_init hboth.2] at hdecB
  exact hne (congrFun (hdecA.symm.trans hdecB) 0)

/-- Non-vacuous Yao lower-bound transfer with a **strictly positive** bound `0 < L` derived from
`validHistoriesUpTo` and `decodeDict_runSeq_eq` on both `insertQueryDeleteDist` and
`insertDeleteDist`. -/
theorem yao_transfer_positive_lower_bound :
    ∃ (L₁ L₂ : ℝ≥0∞), 0 < L₁ ∧ 0 < L₂ ∧
      L₁ ≤ (directDictImpl.toRandomized.initPotential : ℝ≥0∞) +
        ∑' ops, insertQueryDeleteDist 4 2 2 (by omega) (by omega) ops *
          ((Dynamic.spec 4 2 2).totalCost directDictImpl.toRandomized.charge
            (Dictionary.empty 4) ops : ℝ≥0∞) ∧
      L₂ ≤ ((directDictImpl.toObliviousSequenceImpl (fun _ => 1)
            (fun _ _ _ => by simp)).initPotential : ℝ≥0∞) +
        ∑' ops, insertDeleteDist 4 2 2 (by omega) (by omega) ops *
          (((ops.map (directDictImpl.toObliviousSequenceImpl (fun _ => 1)
            (fun _ _ _ => by simp)).charge).sum : ℕ) : ℝ≥0∞) := by
  let keysA : Fin 4 ↪ Fin 4 := Function.Embedding.refl (Fin 4)
  let keysB : Fin 4 ↪ Fin 4 := ⟨![2, 3, 0, 1], by decide⟩
  let valsZ : Fin 4 → Fin 2 := fun _ => 0
  let distQ := insertQueryDeleteDist 4 2 2 (by omega) (by omega)
  let distU := insertDeleteDist 4 2 2 (by omega) (by omega)
  let qA := insertQueryDeleteSeq (n := 2) keysA valsZ
  let qB := insertQueryDeleteSeq (n := 2) keysB valsZ
  let uA := insertDeleteSeq (n := 2) keysA valsZ
  let uB := insertDeleteSeq (n := 2) keysB valsZ
  have hqA_mem : qA ∈ distQ.support :=
    (mem_support_insertQueryDeleteDist_iff (by omega) (by omega)).mpr ⟨keysA, valsZ, rfl⟩
  have hqB_mem : qB ∈ distQ.support :=
    (mem_support_insertQueryDeleteDist_iff (by omega) (by omega)).mpr ⟨keysB, valsZ, rfl⟩
  have huA_mem : uA ∈ distU.support :=
    (mem_support_insertDeleteDist_iff (by omega) (by omega)).mpr ⟨keysA, valsZ, rfl⟩
  have huB_mem : uB ∈ distU.support :=
    (mem_support_insertDeleteDist_iff (by omega) (by omega)).mpr ⟨keysB, valsZ, rfl⟩
  have hstateA_zero : (windowDict (n := 2) keysA valsZ 2 (by omega)).1 0 = none := by
    rw [windowDict_coe]
    refine dictOfEmb_apply_eq_none _ _ fun i => ?_
    rw [windowEmb_apply]
    fin_cases i <;> decide
  have hstateB_zero : (windowDict (n := 2) keysB valsZ 2 (by omega)).1 0 = some 0 := by
    rw [windowDict_coe]
    have h0 : windowEmb (n := 2) keysB 2 (by omega) (⟨0, by decide⟩ : Fin 2) = 0 := by
      rw [windowEmb_apply]; decide
    rw [← h0, dictOfEmb_apply_self, windowVals_apply]
    rfl
  refine ⟨min (distQ qA) (distQ qB), min (distU uA) (distU uB),
    lt_min ((_root_.PMF.apply_pos_iff distQ qA).mpr hqA_mem)
      ((_root_.PMF.apply_pos_iff distQ qB).mpr hqB_mem),
    lt_min ((_root_.PMF.apply_pos_iff distU uA).mpr huA_mem)
      ((_root_.PMF.apply_pos_iff distU uB).mpr huB_mem), ?_, ?_⟩
  · refine le_expected_totalCost_insertQueryDeleteDist_of_det_indexedScheme (U := 4) (V := 2)
      (n := 2) (by omega) (by omega) directDictImpl.toRandomized fun D_det hcorr => ?_
    have hqA_run : ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) qA).1 =
        (windowDict (n := 2) keysA valsZ 2 (by omega)).1 := by
      have htake := (validHistory_and_run_take_insertQueryDeleteSeq (n := 2) keysA valsZ
        (t := 2) le_rfl).2
      rwa [List.take_of_length_le (by rw [length_insertQueryDeleteSeq])] at htake
    have hqB_run : ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) qB).1 =
        (windowDict (n := 2) keysB valsZ 2 (by omega)).1 := by
      have htake := (validHistory_and_run_take_insertQueryDeleteSeq (n := 2) keysB valsZ
        (t := 2) le_rfl).2
      rwa [List.take_of_length_le (by rw [length_insertQueryDeleteSeq])] at htake
    rcases one_le_seqProbes_of_two_postStates D_det hcorr
        (length_insertQueryDeleteSeq (n := 2) keysA valsZ)
        (length_insertQueryDeleteSeq (n := 2) keysB valsZ)
        (validHistory_insertQueryDeleteSeq (U := 4) (V := 2) (n := 2) keysA valsZ)
        (validHistory_insertQueryDeleteSeq (U := 4) (V := 2) (n := 2) keysB valsZ)
        (by rw [hqA_run, hqB_run, hstateA_zero, hstateB_zero]; decide) with h1 | h1
    · calc
        min (distQ qA) (distQ qB) ≤ distQ qA * 1 := by simp
        _ ≤ distQ qA * (D_det.seqProbes qA : ℝ≥0∞) := by gcongr; exact_mod_cast h1
        _ ≤ ∑' ops, distQ ops * (D_det.seqProbes ops : ℝ≥0∞) :=
          le_tsum (fun ops => distQ ops * (D_det.seqProbes ops : ℝ≥0∞)) qA
    · calc
        min (distQ qA) (distQ qB) ≤ distQ qB * 1 := by simp
        _ ≤ distQ qB * (D_det.seqProbes qB : ℝ≥0∞) := by gcongr; exact_mod_cast h1
        _ ≤ ∑' ops, distQ ops * (D_det.seqProbes ops : ℝ≥0∞) :=
          le_tsum (fun ops => distQ ops * (D_det.seqProbes ops : ℝ≥0∞)) qB
  · refine le_expected_charge_insertDeleteDist_of_det_indexedScheme (U := 4) (V := 2)
      (n := 2) (by omega) (by omega)
      (directDictImpl.toObliviousSequenceImpl (fun _ => 1) (fun _ _ _ => by simp))
      fun D_det hcorr => ?_
    have huA_run : ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) uA).1 =
        (windowDict (n := 2) keysA valsZ 2 (by omega)).1 := by
      have htake := (validHistory_and_run_take_insertDeleteSeq (n := 2) keysA valsZ
        (t := 2) le_rfl).2
      rwa [List.take_of_length_le (by rw [length_insertDeleteSeq])] at htake
    have huB_run : ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) uB).1 =
        (windowDict (n := 2) keysB valsZ 2 (by omega)).1 := by
      have htake := (validHistory_and_run_take_insertDeleteSeq (n := 2) keysB valsZ
        (t := 2) le_rfl).2
      rwa [List.take_of_length_le (by rw [length_insertDeleteSeq])] at htake
    rcases one_le_seqProbes_of_two_postStates D_det hcorr
        (length_insertDeleteSeq (n := 2) keysA valsZ)
        (length_insertDeleteSeq (n := 2) keysB valsZ)
        (validHistory_insertDeleteSeq (U := 4) (V := 2) (n := 2) keysA valsZ)
        (validHistory_insertDeleteSeq (U := 4) (V := 2) (n := 2) keysB valsZ)
        (by rw [huA_run, huB_run, hstateA_zero, hstateB_zero]; decide) with h1 | h1
    · calc
        min (distU uA) (distU uB) ≤ distU uA * 1 := by simp
        _ ≤ distU uA * (D_det.seqProbes uA : ℝ≥0∞) := by gcongr; exact_mod_cast h1
        _ ≤ ∑' ops, distU ops * (D_det.seqProbes ops : ℝ≥0∞) :=
          le_tsum (fun ops => distU ops * (D_det.seqProbes ops : ℝ≥0∞)) uA
    · calc
        min (distU uA) (distU uB) ≤ distU uB * 1 := by simp
        _ ≤ distU uB * (D_det.seqProbes uB : ℝ≥0∞) := by gcongr; exact_mod_cast h1
        _ ≤ ∑' ops, distU ops * (D_det.seqProbes ops : ℝ≥0∞) :=
          le_tsum (fun ops => distU ops * (D_det.seqProbes ops : ℝ≥0∞)) uB

/-! ### 3. Adversarial 0-probe soundness test (`validHistoriesUpTo` vs `insertDeleteDist`) -/

/-- Bogus `0`-probe scheme that ignores updates and answers `some 0` to every `.query`. -/
@[expose] def bogusZeroProbeScheme : Scheme (Dynamic.Op 4) Dynamic.Op.Result 4 2 where
  init := zeroMem 4 2
  step
    | .insert _ _ => .pure ()
    | .delete _ => .pure ()
    | .query _ => .pure (some 0)

private theorem bogus_agrees_on_no_queries :
    ∀ (ops : List (Dynamic.Op 4)) (t₀ : ℕ) (s : Dictionary.State 4) (m : Mem 4 2),
      (∀ o ∈ ops, ¬ ∃ u, o = .query u) →
      (bogusZeroProbeScheme.toIndexed.runInterval t₀ m ops).1 =
        ((Dynamic.spec 4 2 2).run s ops).2 := by
  intro ops
  induction ops with
  | nil => intros; rfl
  | cons o rest ih =>
    intro t₀ s m hnoq
    have ho : ¬ ∃ u, o = .query u := hnoq o List.mem_cons_self
    have hrest : ∀ o' ∈ rest, ¬ ∃ u, o' = .query u :=
      fun o' hm => hnoq o' (List.mem_cons_of_mem _ hm)
    cases o with
    | insert u v =>
      change ⟨Dynamic.Op.insert u v, ()⟩ ::
          (bogusZeroProbeScheme.toIndexed.runInterval (t₀ + 1) m rest).1 =
        ⟨Dynamic.Op.insert u v, ()⟩ ::
          ((Dynamic.spec 4 2 2).run (Function.update s u (some v)) rest).2
      rw [ih (t₀ + 1) _ _ hrest]
    | delete u =>
      change ⟨Dynamic.Op.delete u, ()⟩ ::
          (bogusZeroProbeScheme.toIndexed.runInterval (t₀ + 1) m rest).1 =
        ⟨Dynamic.Op.delete u, ()⟩ ::
          ((Dynamic.spec 4 2 2).run (Function.update s u none) rest).2
      rw [ih (t₀ + 1) _ _ hrest]
    | query u => exact absurd ⟨u, rfl⟩ ho

/-- `bogusZeroProbeScheme` passes on `insertDeleteDist.support` with `0` probes, yet is rejected by
`validHistoriesUpTo 4 2 2 (3 * 2 + 1)`. -/
theorem bogusZeroProbeScheme_agrees_on_insertDeleteDist_but_rejected :
    (∀ ops ∈ (insertDeleteDist 4 2 2 (by omega) (by omega)).support,
      (bogusZeroProbeScheme.toIndexed.runSeq ops).1 =
        ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) ∧
    ¬ (∀ ops ∈ validHistoriesUpTo 4 2 2 (3 * 2 + 1),
      (bogusZeroProbeScheme.toIndexed.runSeq ops).1 =
        ((Dynamic.spec 4 2 2).run (Dictionary.empty 4) ops).2) := by
  refine ⟨fun ops hops => bogus_agrees_on_no_queries ops 0 _ _
    (fun _ ho => not_isQuery_of_mem_support_insertDeleteDist hops ho), ?_⟩
  intro hall
  have hvh_q : (Dynamic.spec 4 2 2).ValidHistory (Dictionary.empty 4) [.query 0] :=
    ⟨by trivial, by trivial⟩
  have hmem : ([Dynamic.Op.query 0] : List (Dynamic.Op 4)) ∈ validHistoriesUpTo 4 2 2 7 :=
    ⟨hvh_q, by decide⟩
  have heq := hall [.query 0] hmem
  have hhead : Sigma.mk (β := Dynamic.Op.Result) (.query (0 : Fin 4)) (some 0) =
      Sigma.mk (β := Dynamic.Op.Result) (.query (0 : Fin 4)) none :=
    List.head_eq_of_cons_eq heq
  exact absurd (eq_of_heq (Sigma.mk.inj hhead).2) (by decide)

/-! ### 4. `MetaTree`, `sum_nodeCost_le_seqProbes`, Eq. (5) `3`-hit witness, and `mixMem` -/

private theorem nineFanout_pos : ∀ ℓ, 1 ≤ ℓ → 0 < (fun _ : ℕ => 2) ℓ :=
  fun _ _ => Nat.two_pos

private theorem nineFanout_even : ∀ ℓ, 1 ≤ ℓ → 2 ∣ (fun _ : ℕ => 2) ℓ :=
  fun _ _ => ⟨1, rfl⟩

/-- Non-power-of-two horizon `9` exercising divisibility-free `ofFanout` and packing. -/
def nineTree : MetaTree :=
  MetaTree.ofFanout 9 (fun _ => 2) nineFanout_pos nineFanout_even

theorem nineTree_height_and_packing :
    nineTree.height = 2 ∧ nineTree.nodeCount 2 = 2 ∧
    9 ≤ 2 * (nineTree.nodeCount 2 * nineTree.blockSize 2) := by
  have hhor : nineTree.horizon = 9 := MetaTree.ofFanout_horizon 9 _ _ _
  have hfan : nineTree.fanout = fun _ => 2 := MetaTree.ofFanout_fanout 9 _ _ _
  have hb2 : nineTree.blockSize 2 = 4 := by
    rw [nineTree.blockSize_succ 1, nineTree.blockSize_succ 0, nineTree.blockSize_zero, hfan]
    rfl
  have hb3 : nineTree.blockSize 3 = 8 := by
    rw [nineTree.blockSize_succ 2, hb2, hfan]
    rfl
  have hh_ge : 2 ≤ nineTree.height :=
    (MetaTree.le_height_ofFanout_iff (horizon := 9) (by omega) (fun _ => 2)
      nineFanout_pos nineFanout_even 2).mpr (by change nineTree.blockSize 2 ≤ 4; omega)
  have hh_lt : ¬ 3 ≤ nineTree.height := by
    intro h3
    have hle := (MetaTree.le_height_ofFanout_iff (horizon := 9) (by omega) (fun _ => 2)
      nineFanout_pos nineFanout_even 3).mp h3
    change nineTree.blockSize 3 ≤ 4 at hle
    omega
  have hh : nineTree.height = 2 := by omega
  have hnc : nineTree.nodeCount 2 = 2 := by
    simp only [MetaTree.nodeCount, hhor, hb2]
  have hpack : 9 ≤ 2 * (nineTree.nodeCount 2 * nineTree.blockSize 2) := by
    have hp := nineTree.horizon_le_two_mul_nodeCount_mul_blockSize (ℓ := 2) (by omega)
    rwa [hhor] at hp
  exact ⟨hh, hnc, hpack⟩

/-- Step-indexed 2-cell scheme on `Unit` operations that writes `(t + 1) % 4` to cell `0` during
steps `0, 1, 2` and makes `0` probes at step `3`, hitting cell `0` in `s = 3` of `4` segments. -/
@[expose] def threeHitScheme : IndexedScheme Unit (fun _ => PUnit) 2 2 where
  init := zeroMem 2 2
  step t _ :=
    if t < 3 then ProbeTree.write 0 ⟨(t + 1) % 4, by omega⟩ else .pure PUnit.unit

def fourSegTree : MetaTree where
  horizon := 4
  height := 1
  fanout _ := 4
  fanout_pos _ _ := by omega
  even_fanout _ _ := ⟨2, rfl⟩

theorem geomMetaTree_and_iterLogMetaTree_checks :
    (geomMetaTree 100 3).blockSize 1 = 6 ∧
    Nat.log 2 (100 / 12) ≤ 64 * (geomMetaTree 100 3).height ∧
    2 ^ 64 ≤ (iterLogMetaTree 16 1 2).fanout 2 ∧
    2 * 16 * Nat.iterLog 1 16 ≤
      (iterLogMetaTree 16 1 2).blockSize 1 * Nat.iterLog 1 16 + 2 * Nat.iterLog 1 16 := by
  refine ⟨by rw [blockSize_geomMetaTree 100 3 le_rfl]; norm_num,
    by simpa using log_div_le_mul_height_geomMetaTree 100 3,
    two_pow_le_fanout_iterLogMetaTree 16 1 2 le_rfl,
    mul_iterLog_le_blockSize_one_add_iterLogMetaTree (by omega) 1 2⟩

theorem threeHit_badCell_bound_and_conservation :
    let ops : List Unit := [(), (), (), ()]
    (0 : Fin 2) ∈ fourSegTree.badCells threeHitScheme 0 1 ops 0 0 ∧
    fourSegTree.nodeCost threeHitScheme 0 1 ops 0 0 = 2 ∧
    (∑ i : Fin (fourSegTree.fanout 1),
      (fourSegTree.segProbedCells threeHitScheme 0 1 ops 0 0 i ∩
        fourSegTree.badCells threeHitScheme 0 1 ops 0 0).card) ≤
      2 * fourSegTree.nodeCost threeHitScheme 0 1 ops 0 0 ∧
    (∑ ℓ ∈ Finset.range fourSegTree.height,
      ∑ b ∈ Finset.range (fourSegTree.nodeCount (ℓ + 1)),
        fourSegTree.nodeCost threeHitScheme 0 1 ops ℓ b) ≤
      threeHitScheme.seqProbes ops := by
  intro ops
  have hb0 : fourSegTree.blockSize 0 = 1 := fourSegTree.blockSize_zero
  have hb1 : fourSegTree.blockSize 1 = 4 := by
    rw [fourSegTree.blockSize_succ 0, hb0]; rfl
  have hseg0 :
      (0 : Fin 2) ∈ fourSegTree.segProbedCells threeHitScheme 0 1 ops 0 0 ⟨0, by decide⟩ := by
    simp only [MetaTree.segProbedCells, MetaTree.nodeProbedCells, MetaTree.nodeStart,
      MetaTree.nodeStop, hb0]
    decide
  have hpost_ne :
      memAt threeHitScheme ops
        (0 + 1 * fourSegTree.nodeStop 0 (0 * fourSegTree.fanout 1 + 0)) 0 ≠
      memAt threeHitScheme ops
        (0 + 1 * fourSegTree.nodeStop 1 0) 0 := by
    simp only [MetaTree.nodeStop, hb0, hb1]
    decide
  have hbad0 : (0 : Fin 2) ∈ fourSegTree.badCells threeHitScheme 0 1 ops 0 0 :=
    fourSegTree.mem_badCells_of_seg_postMem_ne_node_postMem threeHitScheme 0 1 ops 0 0
      ⟨0, by decide⟩ hseg0 hpost_ne
  have htel := fourSegTree.nodeCost_add_card_nodeProbedCells threeHitScheme 0 1 ops 0 0
  have hparent : (fourSegTree.nodeProbedCells threeHitScheme 0 1 ops (0 + 1) 0).card = 1 := by
    change (fourSegTree.nodeProbedCells threeHitScheme 0 1 ops 1 0).card = 1
    simp only [MetaTree.nodeProbedCells, MetaTree.nodeStart, MetaTree.nodeStop, hb1]
    decide
  have hchildren : (∑ i : Fin (fourSegTree.fanout 1),
      (fourSegTree.segProbedCells threeHitScheme 0 1 ops 0 0 i).card) = 3 := by
    simp only [MetaTree.segProbedCells, MetaTree.nodeProbedCells, MetaTree.nodeStart,
      MetaTree.nodeStop, hb0]
    decide
  rw [hparent, hchildren] at htel
  have hcost : fourSegTree.nodeCost threeHitScheme 0 1 ops 0 0 = 2 := by omega
  exact ⟨hbad0, hcost,
    fourSegTree.sum_card_segProbedCells_inter_badCells_le_two_mul_nodeCost
      threeHitScheme 0 1 ops 0 0,
    fourSegTree.sum_nodeCost_le_seqProbes threeHitScheme 0 1 ops⟩

theorem mixMem_replay_and_recovery_example :
    let ops_A : List (Dynamic.Op 4) := [.insert 0 1, .insert 1 0]
    let ops_B : List (Dynamic.Op 4) := [.insert 2 1, .query 2]
    let m_bef : Mem 4 2 := zeroMem 4 2
    let m_A : Mem 4 2 := (directDictScheme.toIndexed.runInterval 0 m_bef ops_A).2
    let S_B := directDictScheme.toIndexed.probedCellsInterval 0 m_bef ops_B
    (directDictScheme.toIndexed.runInterval 0 (mixMem m_bef m_A S_B) ops_B).1 =
      (directDictScheme.toIndexed.runInterval 0 m_bef ops_B).1 ∧
    mixMem m_bef m_A S_B 0 = m_A 0 := by
  intro ops_A ops_B m_bef m_A S_B
  refine ⟨(runInterval_mixMem_eq_of_probedCellsInterval_subset
    directDictScheme.toIndexed 0 m_bef m_A S_B ops_B Finset.Subset.rfl).1, ?_⟩
  refine mixMem_eq_postMem_of_notMem_inter
    directDictScheme.toIndexed 0 m_bef ops_A S_B S_B Finset.inter_subset_left ?_
  decide

/-- Cross-module check of symbolic and concrete meta-operation slicing, `sizedDictEquiv` equations,
`geomMetaTree` / `iterLogMetaTree` horizon/height APIs, and
`mem_badCells_of_seg_preMem_ne_node_preMem`. -/
theorem cross_module_slicing_equiv_and_preMem_checks :
    let keys : Fin 4 ↪ Fin 4 := Function.Embedding.refl (Fin 4)
    let vals : Fin 4 → Fin 2 := fun _ => 0
    (∀ {U V n : ℕ} (k : Fin (2 * n) ↪ Fin U) (v : Fin (2 * n) → Fin V) (j : Fin n),
      elemSlice n 3 (insertQueryDeleteSeq k v) j.1 (j.1 + 1) = queryDeleteInsertMetaOp k v j ∧
      elemSlice n 2 (insertDeleteSeq k v) j.1 (j.1 + 1) = deleteInsertMetaOp k v j) ∧
    elemSlice 2 3 (insertQueryDeleteSeq (n := 2) keys vals) 1 2 =
      [.query 1, .delete 1, .insert 3 0] ∧
    elemSlice 2 2 (insertDeleteSeq (n := 2) keys vals) 1 2 =
      [.delete 1, .insert 3 0] ∧
    ((sizedDictEquiv 4 2 2 (windowDict (n := 2) keys vals 0 (by omega))).1 : Finset (Fin 4)) =
      Dictionary.dom (windowDict (n := 2) keys vals 0 (by omega)).1 ∧
    (geomMetaTree 8 1).horizon = 8 ∧
    (iterLogMetaTree 8 2 1).horizon = 8 ∧
    ((1 ≤ (geomMetaTree 8 1).height) ↔ (geomMetaTree 8 1).blockSize 1 ≤ 4) ∧
    (0 : Fin 2) ∈ fourSegTree.badCells threeHitScheme 0 1 [(), (), (), ()] 0 0 := by
  refine ⟨fun k v j => ⟨by simp [elemSlice], by simp [elemSlice]⟩,
    by simpa [elemSlice, queryDeleteInsertMetaOp] using
      drop_take_insertQueryDeleteSeq (n := 2) (Function.Embedding.refl (Fin 4))
        (fun _ => (0 : Fin 2)) ⟨1, by decide⟩,
    by simpa [elemSlice, deleteInsertMetaOp] using
      drop_take_insertDeleteSeq (n := 2) (Function.Embedding.refl (Fin 4))
        (fun _ => (0 : Fin 2)) ⟨1, by decide⟩,
    by simp, by simp, by simp, le_height_geomMetaTree_iff (by omega) 1 1, ?_⟩
  let ops : List Unit := [(), (), (), ()]
  have hb0 : fourSegTree.blockSize 0 = 1 := fourSegTree.blockSize_zero
  have hb1 : fourSegTree.blockSize 1 = 4 := by
    rw [fourSegTree.blockSize_succ 0, hb0]; rfl
  have hseg2 :
      (0 : Fin 2) ∈ fourSegTree.segProbedCells threeHitScheme 0 1 ops 0 0 ⟨2, by decide⟩ := by
    simp only [MetaTree.segProbedCells, MetaTree.nodeProbedCells, MetaTree.nodeStart,
      MetaTree.nodeStop, hb0]
    decide
  have hpre_ne :
      memAt threeHitScheme ops
        (0 + 1 * fourSegTree.nodeStart 0 (0 * fourSegTree.fanout 1 + 2)) 0 ≠
      memAt threeHitScheme ops
        (0 + 1 * fourSegTree.nodeStart 1 0) 0 := by
    simp only [MetaTree.nodeStart, hb0, hb1]
    decide
  exact fourSegTree.mem_badCells_of_seg_preMem_ne_node_preMem threeHitScheme 0 1 ops 0 0
    ⟨2, by decide⟩ hseg2 hpre_ne

end CslibFrontierTests.DictLowerBoundDist
