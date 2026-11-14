/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.Consistency
public import CslibFrontier.DataStructure.Dictionary.CellProbe.InnerGame
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dictionary Cell-Probe Consistency, Claim 4.1, and Section 5 Inner Game Tests

Kernel-checked non-vacuity, concrete evaluation, and adversarial soundness witnesses for
`CslibFrontier.DataStructure.Dictionary.CellProbe.Consistency` and
`CslibFrontier.DataStructure.Dictionary.CellProbe.InnerGame`:

1. Direct-mapped cell-probe witnesses verifying `IsQualified` and `IsCappedConsistent`, together
   with negative witnesses confirming that violating either the `c = 1` probe cap `|S_B| ≤ m * t`
   or the cell-difference bound `|{j ∈ S_A ∩ S_B | C_A j ≠ C_B j}| ≤ γ * m` refutes
   `IsCappedConsistent`.
2. Concrete instantiation of Claim 4.1 (`MetaTree.quarter_fanout_le_sum_prob_isGoodSeg`),
   `map_ops_uniformOfFintype_hardKeyValSeed`, `card_inter_filter_powersetCard`, and Claim 4.6
   (`quarter_mul_logb_le_logb_powersetCard_sub_nbr`).
3. Compact `n`-cell `(k + 1)`-bit deterministic slot-array dictionary `slotArrayScheme` exact on all
   admissible histories of `Dynamic.spec (2 ^ k) 1 (2 ^ e)`, unconditionally instantiating Lemma
   5.1, Lemma 4.4, and Claim 4.2 (`prob_isCappedConsistent_section5_le`,
   `prob_isCappedConsistent_segmentRest_lt_half_le`, and
   `expected_card_cappedConsistent_segmentRest_lt_half_le`) at `(e = 20, k = 400)` with
   `|S_A|, |S_B| ≤ m * t` holding on every execution, plus a `0`-probe adversarial check.
-/

public section

namespace CslibFrontierTests.DictLowerBoundInner

open Cslib Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.CellProbe
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ### 1. Qualification, `c = 1` probe cap, and Claim 4.1 -/

/-- Direct-mapped 4-cell, 1-bit dictionary scheme for `V = 1` over `Fin 4`. -/
@[expose] def bitmapScheme4 : Scheme (Dynamic.Op 4) Dynamic.Op.Result 4 1 where
  init := zeroMem 4 1
  step
    | .insert u _ => ProbeTree.write u ⟨1, by decide⟩
    | .delete u => ProbeTree.write u ⟨0, by decide⟩
    | .query u => do
        let b ← ProbeTree.read u
        return if b.val = 1 then some 0 else none

/-- Positive and negative witnesses for `IsQualified` and `IsCappedConsistent`:
(a) two qualified 1-probe segments are capped-consistent when `t = 1`;
(b) tightening the `c = 1` probe cap to `t = 1 / 2` refutes `IsCappedConsistent` even on identical
    operations; and
(c) writing distinct values to the same cell refutes `IsCappedConsistent` when `γ = 1 / 2`. -/
theorem cappedConsistent_pos_and_neg_witnesses :
    let D := bitmapScheme4.toIndexed
    let C₀ := zeroMem 4 1
    let opsA : List (Dynamic.Op 4) := [.insert 0 0]
    let opsB_same : List (Dynamic.Op 4) := [.insert 0 0]
    let opsB_diff : List (Dynamic.Op 4) := [.delete 0]
    IsQualified D 0 C₀ (D.runInterval 0 C₀ opsA).2 (1 / 2) 1 1 opsA ∧
      IsCappedConsistent D 0 C₀ (1 / 2) 1 1 opsA opsB_same ∧
      ¬ IsCappedConsistent D 0 C₀ (1 / 2) 1 (1 / 2) opsA opsB_same ∧
      ¬ IsCappedConsistent D 0 C₀ (1 / 2) 1 1 opsA opsB_diff := by
  dsimp only
  have hcardA : (bitmapScheme4.toIndexed.probedCellsInterval 0 (zeroMem 4 1)
      [Dynamic.Op.insert 0 0]).card = 1 := by decide
  have hdiff0 : ((bitmapScheme4.toIndexed.probedCellsInterval 0 (zeroMem 4 1)
      [Dynamic.Op.insert 0 0]).filter fun j =>
        (bitmapScheme4.toIndexed.runInterval 0 (zeroMem 4 1) [Dynamic.Op.insert 0 0]).2 j ≠
          (bitmapScheme4.toIndexed.runInterval 0 (zeroMem 4 1) [Dynamic.Op.insert 0 0]).2 j).card =
      0 := by simp
  have hdiff1 : (((bitmapScheme4.toIndexed.probedCellsInterval 0 (zeroMem 4 1)
      [Dynamic.Op.insert 0 0] ∩ bitmapScheme4.toIndexed.probedCellsInterval 0 (zeroMem 4 1)
      [Dynamic.Op.delete 0]).filter fun j =>
        (bitmapScheme4.toIndexed.runInterval 0 (zeroMem 4 1) [Dynamic.Op.insert 0 0]).2 j ≠
          (bitmapScheme4.toIndexed.runInterval 0 (zeroMem 4 1) [Dynamic.Op.delete 0]).2 j).card) =
      1 := by decide
  have hq : IsQualified bitmapScheme4.toIndexed 0 (zeroMem 4 1)
      (bitmapScheme4.toIndexed.runInterval 0 (zeroMem 4 1) [Dynamic.Op.insert 0 0]).2
      (1 / 2) 1 1 [Dynamic.Op.insert 0 0] := by
    refine ⟨?_, ?_⟩ <;> [rw [hdiff0]; rw [hcardA]] <;> norm_num
  refine ⟨hq, hq.isCappedConsistent hq, fun h => ?_, fun h => ?_⟩
  · have hc := h.2.1; rw [hcardA] at hc; norm_num at hc
  · have hd := h.1; rw [hdiff1] at hd; norm_num at hd

open Classical in
/-- Claim 4.1 non-vacuity on `T` with `fanout 1 = 4`, `blockSize 1 = 4`, and 4 distinct-cell
inserts: `nodeCost = 0`, `nodeProbes ≤ 4 < (1 / 16) * 4 * 64`, and expected good segments among the
first `2` children is at least `4 / 4 = 1`. -/
theorem claim4_1_quarter_fanout_nonvacuous :
    let T : MetaTree := ⟨4, 1, fun _ => 4, fun _ _ => by omega, fun _ _ => ⟨2, rfl⟩⟩
    let p : _root_.PMF Unit := _root_.PMF.pure ()
    let opsOf : Unit → List (Dynamic.Op 4) :=
      fun _ => [.insert 0 0, .insert 1 0, .insert 2 0, .insert 3 0]
    ((T.fanout 1 : ℝ) / 4) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (T.fanout 1) => i.val < T.fanout 1 / 2),
        ∑ ω : Unit, (p ω).toReal *
          (if T.IsGoodSeg bitmapScheme4.toIndexed 0 1 (opsOf ω) (1 / 2) 64 0 0 i
            then 1 else 0) := by
  intro T p opsOf
  have hb0 : T.blockSize 0 = 1 := T.blockSize_zero
  have hb1 : T.blockSize 1 = 4 := by rw [T.blockSize_succ 0, hb0]; rfl
  refine T.quarter_fanout_le_sum_prob_isGoodSeg bitmapScheme4.toIndexed 0 1 p opsOf
    (by norm_num) (by norm_num) 0 0 ?_ ?_
  · have hc : T.nodeCost bitmapScheme4.toIndexed 0 1 (opsOf ()) 0 0 = 0 := by
      simp only [MetaTree.nodeCost, MetaTree.segHitCount, MetaTree.segProbedCells,
        MetaTree.nodeProbedCells, MetaTree.nodeStart, MetaTree.nodeStop, hb0]
      decide
    simp [p, hc]
  · have hp : T.nodeProbes bitmapScheme4.toIndexed 0 1 (opsOf ()) 1 0 ≤ 4 := by
      refine (rangeProbes_le_seqProbes bitmapScheme4.toIndexed 0 1 (opsOf ()) _ _).trans ?_
      decide
    simp only [Fintype.univ_punit, Finset.sum_singleton, p, _root_.PMF.pure_apply_self,
      ENNReal.toReal_one, one_mul, hb1, Nat.cast_ofNat]
    have hp_r : (T.nodeProbes bitmapScheme4.toIndexed 0 1 (opsOf ()) 1 0 : ℝ) ≤ 4 := by
      exact_mod_cast hp
    linarith

/-! ### 2. `C_mix` candidate replay, `HardKeyValSeed`, and Claim 4.6 -/

instance : Nonempty (HardKeyValSeed 4 2 1) :=
  ⟨⟨Fin.castLEEmb (by decide), fun _ => 0, 1⟩⟩

instance : Nonempty (Fin 2 ↪ Fin 4) :=
  ⟨Fin.castLEEmb (by decide)⟩

theorem hardKeyValSeed_cmix_and_combinatorics_checks :
    let D := bitmapScheme4.toIndexed
    let C₀ := zeroMem 4 1
    let opsA := candidateQueryDeleteInsertOps (m := 1) (fun _ => (0 : Fin 4)) (fun _ => 1)
      (fun _ => (0 : Fin 1))
    let opsB := candidateQueryDeleteInsertOps (m := 1) (fun _ => (2 : Fin 4)) (fun _ => 3)
      (fun _ => (0 : Fin 1))
    let S_B := D.probedCellsInterval 0 C₀ opsB
    let R6 : Finset (Fin 6) := Finset.univ
    let A2 : Finset (Fin 6) := {0, 1}
    (D.runInterval 0 (mixMem C₀ (D.runInterval 0 C₀ opsA).2 S_B) opsB).1 =
      (D.runInterval 0 C₀ opsB).1 ∧
      mixMem C₀ (D.runInterval 0 C₀ opsA).2 S_B 1 = (D.runInterval 0 C₀ opsA).2 1 ∧
      ((R6.powersetCard 2).filter fun B => (A2 ∩ B).card = 1).card = 8 ∧
      (PMF.uniformOfFintype (HardKeyValSeed 4 2 1)).map HardKeyValSeed.ops =
        insertQueryDeleteDist 4 2 1 (by omega) (by omega) ∧
      insertDeleteDist 4 2 1 (by omega) (by omega) =
        ((PMF.uniformOfFintype (Fin 2 ↪ Fin 4)).bind fun keys =>
          (PMF.uniformOfFintype (Fin 4 → Fin 2)).bind fun kv =>
            (PMF.uniformOfFintype (Equiv.Perm (Fin 1))).map fun delPerm =>
              insertDeleteSeq keys (fun idx => kv (keys idx)) delPerm) ∧
      elemSlice 1 2
        (insertDeleteSeq (n := 1) (Fin.castLEEmb (by decide : 2 * 1 ≤ 4))
          (fun _ => (0 : Fin 2)) 1) 0 1 =
        candidateDeleteInsertOps
          (segDeletedKeys (n := 1) (Fin.castLEEmb (by decide : 2 * 1 ≤ 4)) 1 0 1 le_rfl)
          (segInsertedKeys (n := 1) (Fin.castLEEmb (by decide : 2 * 1 ≤ 4)) 0 1 le_rfl)
          (fun _ => (0 : Fin 2)) ∧
      ((1 / 2 : ℝ) * Real.logb 2 (2 ^ 20 : ℕ) ≤
        Real.logb 2 ((Finset.univ : Finset (Fin (2 ^ 21))).powersetCard 2).card -
          Real.logb 2 (((Finset.univ : Finset (Fin (2 ^ 21))).powersetCard 2).filter
            fun B => 1 ≤ (({⟨0, by positivity⟩, ⟨1, Nat.one_lt_two_pow (by decide)⟩} :
              Finset (Fin (2 ^ 21))) ∩ B).card).card) := by
  intro D C₀ opsA opsB S_B R6 A2
  refine ⟨(runInterval_mixMem_eq_of_probedCellsInterval_subset D 0 C₀
      (D.runInterval 0 C₀ opsA).2 S_B opsB Finset.Subset.rfl).1,
    mixMem_eq_postMem_of_notMem_inter D 0 C₀ opsA S_B S_B Finset.inter_subset_left ?_,
    ?_, map_ops_uniformOfFintype_hardKeyValSeed (U := 4) (V := 2) (n := 1) (by omega) (by omega),
    insertDeleteDist_eq_bind_keyVals (U := 4) (V := 2) (n := 1) (by omega) (by omega),
    elemSlice_insertDeleteSeq_eq_candidate (n := 1) (t₀ := 0) (m := 1)
      (Fin.castLEEmb (by decide : 2 * 1 ≤ 4)) (fun _ => (0 : Fin 2)) 1 le_rfl,
    ?_⟩
  · decide
  · rw [card_inter_filter_powersetCard (Finset.subset_univ _) (by decide)]; decide
  · have hA : ({⟨0, by positivity⟩, ⟨1, Nat.one_lt_two_pow (by decide)⟩} :
        Finset (Fin (2 ^ 21))).card = 2 :=
      Finset.card_pair (fun h => by injection h with h'; omega)
    have hR_lo : (2 ^ 20 / 2) * 2 ≤ (Finset.univ : Finset (Fin (2 ^ 21))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Nat.div_mul_le_self _ _).trans (Nat.pow_le_pow_right (by decide) (by decide))
    have hR_hi : (Finset.univ : Finset (Fin (2 ^ 21))).card ≤ 2 ^ 20 * 2 := by
      rw [Finset.card_univ, Fintype.card_fin, pow_succ]
    have h := quarter_mul_logb_le_logb_powersetCard_sub_nbr
      (R := (Finset.univ : Finset (Fin (2 ^ 21))))
      (A := ({⟨0, by positivity⟩, ⟨1, Nat.one_lt_two_pow (by decide)⟩} : Finset (Fin (2 ^ 21))))
      (m := 2) (F := 2 ^ 20) ⟨1, rfl⟩ (by decide) ⟨2 ^ 19, by ring⟩ le_rfl (Finset.subset_univ _)
      hA hR_lo hR_hi
    have h12 : (1 / 2 : ℝ) * Real.logb 2 (2 ^ 20 : ℕ) =
        (1 / 4 : ℝ) * (2 : ℝ) * Real.logb 2 (2 ^ 20 : ℕ) := by ring
    rw [h12]; exact h

/-! ### 3. Compact `n`-cell slot-array dictionary and unconditional Section 5 Inner Game bounds -/

private def readPrefix {S w : ℕ} : (k : ℕ) → k ≤ S → ProbeTree S w (Mem S w)
  | 0, _ => pure (zeroMem S w)
  | k + 1, hk => do
      let f ← readPrefix k (Nat.le_of_succ_le hk)
      let v ← ProbeTree.read ⟨k, hk⟩
      pure (Function.update f ⟨k, hk⟩ v)

private theorem run_readPrefix {S w : ℕ} (m : Mem S w) :
    ∀ (k : ℕ) (hk : k ≤ S),
      (readPrefix k hk).run m = (fun i => if i.val < k then m i else ⟨0, Nat.two_pow_pos w⟩, m)
  | 0, _ => rfl
  | k + 1, hk => by
      simp only [readPrefix, ProbeTree.run_bind, run_readPrefix m k (Nat.le_of_succ_le hk),
        ProbeTree.run_read, ProbeTree.run_pure, Prod.mk.injEq, and_true]
      funext i
      by_cases hi : i = ⟨k, hk⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi]
        have hne : i.val ≠ k := fun h => hi (Fin.ext h)
        by_cases hlt : i.val < k
        · have hlt' : i.val < k + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ i.val < k + 1 := by omega
          simp [hlt, hlt']

private theorem run_readPrefix_self {S w : ℕ} (m : Mem S w) :
    (readPrefix S le_rfl).run m = (m, m) := by
  rw [run_readPrefix]; exact Prod.ext (funext fun i => by simp [i.isLt]) rfl

private def writePrefix {S w : ℕ} (m' : Mem S w) : (k : ℕ) → k ≤ S → ProbeTree S w PUnit
  | 0, _ => pure PUnit.unit
  | k + 1, hk => do
      writePrefix m' k (Nat.le_of_succ_le hk)
      ProbeTree.write ⟨k, hk⟩ (m' ⟨k, hk⟩)

private theorem run_writePrefix {S w : ℕ} (m m' : Mem S w) :
    ∀ (k : ℕ) (hk : k ≤ S),
      (writePrefix m' k hk).run m = (PUnit.unit, fun i => if i.val < k then m' i else m i)
  | 0, _ => rfl
  | k + 1, hk => by
      simp only [writePrefix, ProbeTree.run_bind, run_writePrefix m m' k (Nat.le_of_succ_le hk),
        ProbeTree.run_write, Prod.mk.injEq, true_and]
      funext i
      by_cases hi : i = ⟨k, hk⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi]
        have hne : i.val ≠ k := fun h => hi (Fin.ext h)
        by_cases hlt : i.val < k
        · have hlt' : i.val < k + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ i.val < k + 1 := by omega
          simp [hlt, hlt']

private theorem run_writePrefix_self {S w : ℕ} (m m' : Mem S w) :
    (writePrefix m' S le_rfl).run m = (PUnit.unit, m') := by
  rw [run_writePrefix]; exact Prod.ext rfl (funext fun i => by simp [i.isLt])

private noncomputable def encodeUnitDict {U : ℕ} (n : ℕ) {k : ℕ} (hU : U ≤ 2 ^ k)
    (s : Dictionary.State U) : Mem n (k + 1) := fun j =>
  if hj : j.val < (Dictionary.dom s).card then
    ⟨(((Dictionary.dom s).orderIsoOfFin rfl ⟨j.val, hj⟩) : Fin U).val + 1, by
      have := (((Dictionary.dom s).orderIsoOfFin rfl ⟨j.val, hj⟩) : Fin U).isLt
      rw [Nat.pow_succ]; omega⟩
  else ⟨0, Nat.two_pow_pos _⟩

private noncomputable def decodeUnitDict {U n k : ℕ} (_hU : U ≤ 2 ^ k) (m : Mem n (k + 1)) :
    Dictionary.State U := fun u =>
  open Classical in
  if ∃ j : Fin n, (m j).val = u.val + 1 then some 0 else none

private theorem decodeUnitDict_encodeUnitDict {U n k : ℕ} (hU : U ≤ 2 ^ k)
    {s : Dictionary.State U} (hcard : (Dictionary.dom s).card ≤ n)
    (hbnd : Dictionary.ValuesBounded 1 s) :
    decodeUnitDict hU (encodeUnitDict n hU s) = s := by
  classical
  funext u; dsimp only [decodeUnitDict]
  by_cases hu : u ∈ Dictionary.dom s
  · let r := ((Dictionary.dom s).orderIsoOfFin rfl).symm ⟨u, hu⟩
    have hex : ∃ j : Fin n, (encodeUnitDict n hU s j).val = u.val + 1 := by
      refine ⟨⟨r.val, by have := r.isLt; omega⟩, ?_⟩
      simp only [encodeUnitDict, r.isLt, ↓reduceDIte, Fin.eta]
      exact congrArg (fun x : Fin U => x.val + 1) (congrArg Subtype.val
        (((Dictionary.dom s).orderIsoOfFin rfl).apply_symm_apply ⟨u, hu⟩))
    obtain ⟨v, hv⟩ := Dictionary.mem_dom_iff.mp hu
    have hv0 : v = 0 := Nat.lt_one_iff.mp (hbnd u v hv)
    simp [hex, hv, hv0]
  · have hno : ¬ ∃ j : Fin n, (encodeUnitDict n hU s j).val = u.val + 1 := by
      rintro ⟨j, hj⟩
      by_cases hjc : j.val < (Dictionary.dom s).card
      · simp only [encodeUnitDict, hjc, ↓reduceDIte] at hj
        let x := (Dictionary.dom s).orderIsoOfFin rfl ⟨j.val, hjc⟩
        have heq : (x : Fin U) = u := Fin.ext (Nat.add_right_cancel hj)
        exact hu (heq ▸ x.prop)
      · simp only [encodeUnitDict, hjc, ↓reduceDIte] at hj
        omega
    simp [hno, Dictionary.notMem_dom_iff.mp hu]

/-- Compact `n`-cell `(k + 1)`-bit deterministic scheme implementing `Dynamic.spec U 1 n`. -/
noncomputable def slotArrayScheme (U n k : ℕ) (hU : U ≤ 2 ^ k) :
    Scheme (Dynamic.Op U) Dynamic.Op.Result n (k + 1) where
  init := encodeUnitDict n hU (Dictionary.empty U)
  step o := do
    let m ← readPrefix n le_rfl
    let stepOut := Dynamic.step (decodeUnitDict hU m) o
    writePrefix (encodeUnitDict n hU stepOut.1) n le_rfl
    pure stepOut.2

private theorem slotArrayScheme_all_histories {U n k : ℕ} (hU : U ≤ 2 ^ k) (M : ℕ) :
    ∀ ops ∈ validHistoriesUpTo U 1 n M,
      ((slotArrayScheme U n k hU).toIndexed.runSeq ops).1 =
        ((Dynamic.spec U 1 n).run (Dictionary.empty U) ops).2 := by
  have hind : ∀ (ops : List (Dynamic.Op U)) (t₀ : ℕ) (s : Dictionary.State U),
      (Dictionary.dom s).card ≤ n → Dictionary.ValuesBounded 1 s →
      (Dynamic.spec U 1 n).ValidHistory s ops →
      ((slotArrayScheme U n k hU).toIndexed.runInterval t₀ (encodeUnitDict n hU s) ops).1 =
        ((Dynamic.spec U 1 n).run s ops).2 := by
    intro ops; induction ops with
    | nil => intros; rfl
    | cons o rest ih =>
      intro t₀ s hcard hbnd ⟨hval, hvh⟩
      have hrun : ((slotArrayScheme U n k hU).step o).run (encodeUnitDict n hU s) =
          ((Dynamic.step s o).2, encodeUnitDict n hU (Dynamic.step s o).1) := by
        simp [slotArrayScheme, ProbeTree.run_bind, run_readPrefix_self,
          decodeUnitDict_encodeUnitDict hU hcard hbnd, run_writePrefix_self]
      have hcons : (slotArrayScheme U n k hU).toIndexed.runInterval t₀ (encodeUnitDict n hU s)
          (o :: rest) =
          (⟨o, (Dynamic.step s o).2⟩ ::
            ((slotArrayScheme U n k hU).toIndexed.runInterval (t₀ + 1)
              (encodeUnitDict n hU (Dynamic.step s o).1) rest).1,
           ((slotArrayScheme U n k hU).toIndexed.runInterval (t₀ + 1)
             (encodeUnitDict n hU (Dynamic.step s o).1) rest).2) := by
        simp [IndexedScheme.runInterval_cons, Scheme.toIndexed, hrun]
      rw [hcons, StateTransitionSpec.run_cons]; dsimp only
      rw [ih (t₀ + 1) _ (Dynamic.card_dom_step_le_of_valid hcard hval)
        (Dynamic.valuesBounded_step_of_valid hbnd hval) hvh]
  intro ops hops
  exact hind ops 0 (Dictionary.empty U) (by simp) (Dictionary.valuesBounded_empty U 1) hops.1

open Classical in
/-- Family of unconditional instantiations of Lemma 5.1, Lemma 4.4, and Claim 4.2 on
`slotArrayScheme (2 ^ k) (2 ^ e) k` whenever `20 ≤ e` and `20 * e ≤ k`, with `|S_A|, |S_B| ≤ m * t`
holding on every execution. -/
theorem inner_game_slotArray_family {e k : ℕ} (he : 20 ≤ e) (hk : 20 * e ≤ k) :
    let U := 2 ^ k
    let n := 2 ^ e
    let m := 2 ^ (e - 1)
    let γ : ℝ := 2 / (e : ℝ)
    let t : ℝ := 2
    let D := (slotArrayScheme U n k le_rfl).toIndexed
    ∀ (hU : 4 * n ≤ U) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n),
      (((section5Dist (V := 1) 0 m 0 hU le_rfl hm_n (by omega) (by omega)).map fun sb =>
          decide (IsSeedConsistent D 0 m (by omega) γ t sb.1 sb.2)) true).toReal ≤
        (U : ℝ) ^ (-γ * (m : ℝ)) ∧
      (((section5LtHalfDist (V := 1) 0 m hU le_rfl hm hm_n (by omega)).map fun sb =>
          decide (IsSeedConsistent D 0 m (by omega) γ t sb.1 sb.2)) true).toReal ≤
        (U : ℝ) ^ (-γ * (m : ℝ)) ∧
      (((segmentRestLtHalfDist (V := 1) 0 m n hU le_rfl hm hm_n (by omega)).map fun sb =>
          decide (IsSeedConsistent D 0 m (by omega) γ t sb.1 sb.2)) true).toReal ≤
        (U : ℝ) ^ (-γ * (m : ℝ)) ∧
      (haveI : Nonempty (HardKeyValSeed U 1 n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => 0, 1⟩⟩
       (∑ s : HardKeyValSeed U 1 n, ((PMF.uniformOfFintype (HardKeyValSeed U 1 n)) s).toReal *
         ((((((s.insertedSet 0 n (by omega)).powersetCard m).filter fun B =>
           (s.insertedSet 0 m (by omega) ∩ B).card < m / 2)).filter
             (IsSeedConsistent D 0 m (by omega) γ t s)).card : ℝ)) ≤
         (n.choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ))) ∧
      (∀ step₀ mem ops, ((D.probedCellsInterval step₀ mem ops).card : ℝ) ≤ (m : ℝ) * t) := by
  intro U n m γ t D hU hm hm_n
  have hn_eq : n = 2 * m := by
    dsimp [n, m]; conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ']
  have he_pos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (show 0 < e by omega)
  have hγ_pos : 0 < γ := by dsimp [γ]; positivity
  have hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (m : ℝ) := by
    have hn_r : (n : ℝ) = (2 : ℝ) ^ (e : ℝ) := by
      dsimp [n]; rw [Real.rpow_natCast]; push_cast; rfl
    have hm_r : (m : ℝ) = (2 : ℝ) ^ (((e - 1 : ℕ) : ℝ)) := by
      dsimp [m]; rw [Real.rpow_natCast]; push_cast; rfl
    have hexp : (e : ℝ) * (1 - γ / 2) = ((e - 1 : ℕ) : ℝ) := by
      dsimp [γ]; rw [Nat.cast_sub (by omega), Nat.cast_one]; field_simp
    rw [hn_r, ← Real.rpow_mul (by norm_num), hexp, hm_r]
  have hlog_U : Real.logb 2 (U : ℝ) = (k : ℝ) := by
    dsimp [U]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlog_div : Real.logb 2 ((U : ℝ) / (n : ℝ)) = (k : ℝ) - (e : ℝ) := by
    have hdiv : (U : ℝ) / (n : ℝ) = (2 : ℝ) ^ (k - e) := by
      dsimp [U, n]; push_cast
      rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hdiv, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_sub (by omega)]
  set R : ℝ := (2 * (e : ℝ) + 2) * (m : ℝ)
  have hspace : ((n * (k + 1) : ℕ) : ℝ) ≤
      Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 (1 : ℕ) + R := by
    have hch := mul_logb_div_le_logb_choose (N := U) (k := n) Nat.one_le_two_pow (by omega)
    rw [hlog_div] at hch; simp only [Nat.cast_one, Real.logb_one, mul_zero, add_zero]
    have hident : ((n * (k + 1) : ℕ) : ℝ) = (n : ℝ) * ((k : ℝ) - (e : ℝ)) + R := by
      rw [Nat.cast_mul, hn_eq]; push_cast; dsimp [R]; ring
    linarith
  have hbudget : R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * ((k + 1 : ℕ) : ℝ) +
      (3 / 2) * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
    have hγ_le : γ ≤ 1 / 10 := by
      dsimp [γ]; rw [div_le_div_iff₀ he_pos (by norm_num)]
      have : (20 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
      linarith
    have hk1 : γ * ((k + 1 : ℕ) : ℝ) ≤ (1 / 10) * ((k : ℝ) + 1) := by
      push_cast; exact mul_le_mul_of_nonneg_right hγ_le (by positivity)
    have hk2 : (3 / 2) * γ * (k : ℝ) ≤ (3 / 20) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg k)
    have he20 : (20 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have hk20 : 20 * (e : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hcoef : (2 * (e : ℝ) + 2) + 11 + 6 * t + γ * ((k + 1 : ℕ) : ℝ) +
        (3 / 2) * γ * (k : ℝ) ≤ ((k : ℝ) - (e : ℝ)) / 2 := by
      dsimp [t]; linarith
    calc R + 11 * (m : ℝ) + 6 * (m : ℝ) * t + γ * (m : ℝ) * ((k + 1 : ℕ) : ℝ) +
          (3 / 2) * γ * (m : ℝ) * Real.logb 2 U
        = ((2 * (e : ℝ) + 2) + 11 + 6 * t + γ * ((k + 1 : ℕ) : ℝ) +
            (3 / 2) * γ * (k : ℝ)) * (m : ℝ) := by rw [hlog_U]; dsimp [R]; ring
      _ ≤ (((k : ℝ) - (e : ℝ)) / 2) * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg m)
      _ = ((m : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by rw [hlog_div]; ring
  have hcorr := slotArrayScheme_all_histories (U := U) (n := n) (k := k) le_rfl (4 * n + 1)
  refine ⟨prob_isCappedConsistent_section5_le hU le_rfl hm_n hγ_pos hm_lo hspace hbudget hcorr
      (by omega) (by omega),
    prob_isCappedConsistent_section5_lt_half_le hU le_rfl hm_n hγ_pos hm_lo hspace hbudget hcorr
      hm (by omega),
    prob_isCappedConsistent_segmentRest_lt_half_le hU le_rfl hm_n hγ_pos hm_lo hspace hbudget hcorr
      hm hm_n (by omega),
    expected_card_cappedConsistent_segmentRest_lt_half_le hU le_rfl hm_n hγ_pos hm_lo hspace
      hbudget hcorr hm hm_n (by omega),
    fun step₀ mem ops => ?_⟩
  have hle : (D.probedCellsInterval step₀ mem ops).card ≤ n :=
    (Finset.card_le_univ _).trans_eq (by simp)
  exact (Nat.cast_le.mpr hle).trans_eq (by rw [hn_eq]; dsimp [t]; push_cast; ring)

private theorem h4n_20_400 : 4 * 2 ^ 20 ≤ 2 ^ 400 :=
  Eq.trans_le (by decide : 4 * 2 ^ 20 = 2 ^ 22)
    (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by decide : 22 ≤ 400))

private theorem hm2_19 : 2 ≤ 2 ^ 19 :=
  le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 1 ≤ 19))

private theorem hm_n_19_20 : 2 * 2 ^ 19 ≤ 2 ^ 20 :=
  (pow_succ' 2 19).symm.le

open Classical in
/-- Closed ground instance at `(e = 20, k = 400)` (`U = 2 ^ 400, n = 2 ^ 20, m = 2 ^ 19`) for both
Lemma 5.1 (`|A ∩ B| = 0`) and Lemma 4.4 (`|A ∩ B| < m / 2`), plus a `0`-probe adversarial
non-soundness check on `validHistoriesUpTo`. -/
theorem section5_inner_game_concrete_and_zero_probe_guard :
    (((section5Dist (V := 1) 0 (2 ^ 19) 0
        (Eq.trans_le (by decide : 4 * 2 ^ 20 = 2 ^ 22)
          (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by decide : 22 ≤ 400)))
        le_rfl
        (by decide : 2 * 2 ^ 19 ≤ 2 ^ 20)
        (by decide : 0 < 2 ^ 19 / 2)
        (by decide : 0 + 2 ^ 19 ≤ 2 ^ 20)).map
        fun sb => decide (IsSeedConsistent (slotArrayScheme (2 ^ 400) (2 ^ 20) 400 le_rfl).toIndexed
          0 (2 ^ 19) (by decide : 0 + 2 ^ 19 ≤ 2 ^ 20) (2 / (20 : ℝ)) 2 sb.1 sb.2)) true).toReal ≤
      ((2 ^ 400 : ℕ) : ℝ) ^ (-(2 / (20 : ℝ)) * ((2 ^ 19 : ℕ) : ℝ)) ∧
    (((section5LtHalfDist (V := 1) 0 (2 ^ 19)
        (Eq.trans_le (by decide : 4 * 2 ^ 20 = 2 ^ 22)
          (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by decide : 22 ≤ 400)))
        le_rfl
        (by decide : 2 ≤ 2 ^ 19)
        (by decide : 2 * 2 ^ 19 ≤ 2 ^ 20)
        (by decide : 0 + 2 ^ 19 ≤ 2 ^ 20)).map
        fun sb => decide (IsSeedConsistent (slotArrayScheme (2 ^ 400) (2 ^ 20) 400 le_rfl).toIndexed
          0 (2 ^ 19) (by decide : 0 + 2 ^ 19 ≤ 2 ^ 20) (2 / (20 : ℝ)) 2 sb.1 sb.2)) true).toReal ≤
      ((2 ^ 400 : ℕ) : ℝ) ^ (-(2 / (20 : ℝ)) * ((2 ^ 19 : ℕ) : ℝ)) ∧
    ¬ (∀ ops ∈ validHistoriesUpTo 4 1 1 5,
        ((⟨zeroMem 1 1, fun o => match o with
          | .query _ => pure (some 0)
          | .insert _ _ => pure ()
          | .delete _ => pure ()⟩ :
            Scheme (Dynamic.Op 4) Dynamic.Op.Result 1 1).toIndexed.runSeq ops).1 =
          ((Dynamic.spec 4 1 1).run (Dictionary.empty 4) ops).2) := by
  have hfam := inner_game_slotArray_family (e := 20) (k := 400) le_rfl (by decide)
    h4n_20_400 hm2_19 hm_n_19_20
  refine ⟨hfam.1, hfam.2.1, fun h0 => ?_⟩
  have hmem : [Dynamic.Op.query (0 : Fin 4)] ∈ validHistoriesUpTo 4 1 1 5 :=
    ⟨⟨trivial, trivial⟩, by decide⟩
  have heq := h0 _ hmem
  simp [IndexedScheme.runSeq, IndexedScheme.runInterval_cons, IndexedScheme.runInterval_nil,
    Scheme.toIndexed, StateTransitionSpec.run_cons, StateTransitionSpec.run_nil,
    Dictionary.empty] at heq

end CslibFrontierTests.DictLowerBoundInner
