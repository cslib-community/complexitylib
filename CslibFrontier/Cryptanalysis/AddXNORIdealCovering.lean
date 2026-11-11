/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealCutBounds
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
public import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Hidden-word marginals for the actual source cut

The prefix and reversed-suffix words are projections of one uniform source operator string.
Their uniform laws are derived by finite equivalences, not supplied as independence contracts.
This completes the hidden-word averaging step of [WangLvShenZhang2027], Lemma 12 (PDF p. 27),
for the actual independently sampled source word and the old visible ledger.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Covering.source_cut_length`: all auxiliary calls
  are included in the source's `q`-call reveal budget.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Covering.uniform_cut_covering`: the two covering
  fractions for one uniform full hidden word.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Covering.uniform_cut_covering_run`: averaging over
  actual adaptive private-coin execution, with ledger size derived from its query budget.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Covering

open Probability OracleComp RandomPermutation
open scoped ENNReal

/-- A prefix projection of the full uniform hidden word is uniform. -/
theorem uniform_take {q h : ℕ} (hle : h ≤ q) :
    (PMF.uniformOfFintype (Operators q)).map (Fin.take h hle) =
      PMF.uniformOfFintype (Operators h) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have he := Probability.PMF.uniformOfFintype_map_equiv (Fin.appendEquiv (α := Bool) h d).symm
  have hp := congrArg (PMF.map Prod.fst) he
  have ht : (Fin.take h hle : Operators (h + d) → Operators h) =
      (fun bits i => bits (i.castAdd d)) := rfl
  rw [ht]
  simpa only [PMF.map_comp, Function.comp_def, Fin.appendEquiv_symm_apply,
    Probability.PMF.uniformOfFintype_prod_map_fst] using hp

/-- Reversing the full uniform hidden word preserves its law. -/
theorem uniform_reverse (q : ℕ) :
    (PMF.uniformOfFintype (Operators q)).map (fun bits i => bits i.rev) =
      PMF.uniformOfFintype (Operators q) := by
  have he := Probability.PMF.uniformOfFintype_map_equiv
    (Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin q)) (Equiv.refl Bool))
  have hf : (⇑(Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin q)) (Equiv.refl Bool))) =
      (fun bits i => bits i.rev) := by
    funext bits i
    simp
  rw [hf] at he
  exact he

private theorem reverse_ofFn {α : Type} {q : ℕ} (f : Fin q → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_reverse, List.length_ofFn] at hi
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- The source cut's prefix is the layer-labelled prefix projection of the hidden word. -/
theorem source_front {q : ℕ} (bits : Operators q) (k : Fin q) :
    (sourceCut bits k).left ++ [(sourceCut bits k).edge] =
      Forest.binaryLabels (fun i : Fin (k.val + 1) => i.castLE (by omega))
        (Fin.take (k.val + 1) (by omega) bits) := by
  change (List.ofFn fun i => (i, bits i)).take k.val ++
    [(List.ofFn fun i => (i, bits i))[k.val]] = _
  rw [← List.take_succ_eq_append_getElem (by simp)]
  rw [← Fin.ofFn_take_eq_take_ofFn (by omega)]
  rfl

/-- The reversed source suffix is a prefix projection of the reversed hidden word. -/
theorem source_back {q : ℕ} (bits : Operators q) (k : Fin q) :
    (sourceCut bits k).right.reverse =
      Forest.binaryLabels
        (fun i : Fin (q - (k.val + 1)) => (i.castLE (by omega)).rev)
        (Fin.take (q - (k.val + 1)) (by omega) (fun i => bits i.rev)) := by
  change ((List.ofFn fun i => (i, bits i)).drop (k.val + 1)).reverse = _
  rw [List.reverse_drop, List.length_ofFn, reverse_ofFn,
    ← Fin.ofFn_take_eq_take_ofFn (by omega)]
  rfl

/-- The concrete source cut's auxiliary prefix/suffix reveal makes exactly `q` calls. -/
theorem source_cut_length {q : ℕ} (bits : Operators q) (k : Fin q) :
    (sourceCut bits k).left.length + 1 + (sourceCut bits k).right.length = q := by
  have hp : (sourceCut bits k).left ++ (sourceCut bits k).edge :: (sourceCut bits k).right =
      List.ofFn (fun i => (i, bits i)) := by
    simp only [sourceCut, Cut.ofPath_path]
  have hl := congrArg List.length hp
  simp only [List.length_append, List.length_cons, List.length_ofFn] at hl
  omega

/-- The actual source prefix and reversed suffix have the two forest-covering fractions.
They are projected from the same independent full hidden operator string. -/
theorem uniform_cut_covering {Word : Type} [Fintype Word] [DecidableEq Word] {q : ℕ} (k : Fin q)
    (hd : 0 < q - (k.val + 1)) (seed target : Word)
    (records : List (Forest.Record (Label q) Word))
    (hc : Forest.NoCollision {seed, target} records) :
    ((PMF.uniformOfFintype (Operators q)).map
      (fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records)) true ≤
      (records.length : ℝ≥0∞) / 2 ^ (k.val + 1) +
        records.length / 2 ^ (q - (k.val + 1)) := by
  classical
  let A := fun bits : Operators q => decide
    (∃ endpoint, Forest.Follows records seed
      ((sourceCut bits k).left ++ [(sourceCut bits k).edge]) endpoint)
  let B := fun bits : Operators q => decide
    (∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
      (sourceCut bits k).right.reverse endpoint)
  have hf : (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      {bits | ∃ endpoint, Forest.Follows records seed
        ((sourceCut bits k).left ++ [(sourceCut bits k).edge]) endpoint} ≤
      (records.length : ℝ≥0∞) / 2 ^ (k.val + 1) := by
    simp only [source_front]
    change (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      ((Fin.take (k.val + 1) (by omega)) ⁻¹'
        {bits | ∃ endpoint, Forest.Follows records seed
          (Forest.binaryLabels (fun i => i.castLE (by omega)) bits) endpoint}) ≤ _
    rw [← PMF.toOuterMeasure_map_apply, uniform_take]
    exact Forest.uniform_binary_covered_le (by omega) _ {seed, target} seed
      (Finset.mem_insert_self ..) records hc
  have hb : (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      {bits | ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
        (sourceCut bits k).right.reverse endpoint} ≤
      (records.length : ℝ≥0∞) / 2 ^ (q - (k.val + 1)) := by
    simp only [source_back]
    change (PMF.uniformOfFintype (Operators q)).toOuterMeasure
      (((Fin.take (q - (k.val + 1)) (by omega)) ∘ (fun bits i => bits i.rev)) ⁻¹'
        {bits | ∃ endpoint, Forest.Follows (records.map Forest.Record.reverse) target
          (Forest.binaryLabels (fun i => (i.castLE (by omega)).rev) bits) endpoint}) ≤ _
    rw [← PMF.toOuterMeasure_map_apply, ← PMF.map_comp, uniform_reverse, uniform_take]
    simpa only [List.length_map] using Forest.uniform_binary_covered_le hd _ {seed, target}
      target (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (records.map Forest.Record.reverse) ((Forest.noCollision_reverse _ _).mpr hc)
  have hA : ((PMF.uniformOfFintype (Operators q)).map A) true ≤
      (records.length : ℝ≥0∞) / 2 ^ (k.val + 1) := by
    simpa only [A, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hf
  have hB : ((PMF.uniformOfFintype (Operators q)).map B) true ≤
      (records.length : ℝ≥0∞) / 2 ^ (q - (k.val + 1)) := by
    simpa only [B, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hb
  have h := PMF.map_true_le_add (PMF.uniformOfFintype (Operators q)) (A := A) (B := B)
    (E := fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records)
    (fun bits _ hh => by
      simp only [CutBounds.coveredRecords, decide_eq_true_eq] at hh
      simpa only [A, B, decide_eq_true_eq] using hh.2)
  exact h.trans (add_le_add hA hB)

/-- Average covering over an actual visible sampler run and one independent source word.
Collision freedom is part of the event, and ledger size follows from the real query budget. -/
theorem uniform_cut_covering_run {Word Output : Type} [Fintype Word] [DecidableEq Word]
    [Nonempty Word] {q : ℕ} (k : Fin q) (hd : 0 < q - (k.val + 1))
    (seed target : Word) (program : ProbOracleComp (Spec q Word) Output) (T : ℕ)
    (hbudget : ProbOracleComp.IsQueryBounded program T) :
    ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) =>
          CutBounds.coveredRecords (sourceCut bits k) seed target records)) true ≤
      (T : ℝ≥0∞) / 2 ^ (k.val + 1) + T / 2 ^ (q - (k.val + 1)) := by
  classical
  have he : ((PMF.uniformOfFintype (Operators q)).bind fun bits =>
      (ProbOracleComp.runWith Ledger.answer program []).map
        (fun (_, records) => CutBounds.coveredRecords (sourceCut bits k) seed target records)) =
      (ProbOracleComp.runWith Ledger.answer program []).bind fun (_, records) =>
        (PMF.uniformOfFintype (Operators q)).map
          (fun bits => CutBounds.coveredRecords (sourceCut bits k) seed target records) := by
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  rw [he]
  apply Probability.PMF.bind_apply_le_on_support
  rintro ⟨out, records⟩ hout
  by_cases hc : Forest.NoCollision {seed, target} records
  · have h := uniform_cut_covering k hd seed target records hc
    have hn := Ledger.run_length program T hbudget out records hout
    apply h.trans
    simp only [div_eq_mul_inv]
    exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) zero_le)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) zero_le)
  · simp [CutBounds.coveredRecords, hc]

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Covering
