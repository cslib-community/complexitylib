/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP.Oracle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Clients of relativized counting and strict majority -/

@[expose] public section

namespace Cslib.Complexity.Tests.RelativizedCounting

open Turing.MultiTapeTM

open Classical in
/-- Query the input word; the witness is ignored. -/
noncomputable def queryVerifier (A : Set (List Bool)) (x : List Bool × List Bool) : Bool :=
  decide (x.1 ∈ A)

theorem queryVerifier_polyTime (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (queryVerifier A) (encPair encBits encBits) encBool :=
  (computableInPolyTimeWithOracle_mem A).preprocess
    (.of_tidy (ComputableTidilyInPolyTime.fst encBits encBits))

/-- A genuine query counts one empty witness on members and zero on nonmembers. -/
noncomputable def queryCount (A : Set (List Bool)) (w : List Bool) : ℕ :=
  acceptCount (queryVerifier A) w 0

theorem queryCount_mem (A : Set (List Bool)) : queryCount A ∈ SharpPWithOracle A encBits :=
  ⟨0, queryVerifier A, queryVerifier_polyTime A, fun _ => by simp [queryCount]⟩

example (A : Set (List Bool)) : A ∈ PPWithOracle A encBits := by
  classical
  refine ⟨0, queryVerifier A, queryVerifier_polyTime A, fun w => ?_⟩
  simp only [Polynomial.eval_zero, pow_zero, acceptCount_zero, queryVerifier]
  by_cases hw : w ∈ A <;> simp [hw]

/-- The complement of every oracle: the negated query accepts the single empty witness exactly
off the oracle. -/
example (A : Set (List Bool)) : Aᶜ ∈ PPWithOracle A encBits := by
  refine ⟨0, fun x => !queryVerifier A x,
    (queryVerifier_polyTime A).map (.of_tidy ComputableTidilyInPolyTime.bool_not), fun w => ?_⟩
  simp only [Polynomial.eval_zero, pow_zero, acceptCount_zero, queryVerifier]
  by_cases hw : w ∈ A <;> simp [hw]

/-- A problem in `PP` without the oracle, the empty word, is in `PP` relative to every oracle. -/
example (A : Set (List Bool)) : {w : List Bool | w.isEmpty = true} ∈ PPWithOracle A encBits :=
  PP_subset_PPWithOracle A encBits ⟨0, fun x => x.1.isEmpty, by fun_prop, fun w => by
    cases w <;> simp [acceptCount_zero]⟩

example : queryCount {w | w = [true]} [true] = 1 ∧
    queryCount {w | w = [true]} [false] = 0 := by
  simp [queryCount, acceptCount_zero, queryVerifier]

/-- One bit selects the oracle answer or its negation: exactly one of two witnesses accepts. -/
noncomputable def tieVerifier (A : Set (List Bool)) : List Bool × List Bool → Bool :=
  selectVerifier (queryVerifier A) (fun x => !queryVerifier A x)

theorem tieVerifier_polyTime (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (tieVerifier A) (encPair encBits encBits) encBool :=
  computableInPolyTimeWithOracle_selectVerifier (queryVerifier_polyTime A)
    ((queryVerifier_polyTime A).map (.of_tidy ComputableTidilyInPolyTime.bool_not))

theorem tieVerifier_count (A : Set (List Bool)) (w : List Bool) :
    acceptCount (tieVerifier A) w 1 = 1 := by
  change acceptCount (selectVerifier _ _) w (0 + 1) = 1
  rw [acceptCount_selectVerifier, acceptCount_add_acceptCount_not, pow_zero]

example (A : Set (List Bool)) : DecidesByMajority encBits 1 (tieVerifier A) ∅ := by
  intro w
  simp [Polynomial.eval_one, tieVerifier_count]

/-- The zero gap produces exact rejection, including when both witnesses have zero width. -/
example (A : Set (List Bool)) : (∅ : Set (List Bool)) ∈ PPWithOracle A encBits := by
  apply mem_PPWithOracle_iff_exists_GapPWithOracle.2
  refine ⟨fun _ => 0, ⟨queryCount A, queryCount_mem A,
    queryCount A, queryCount_mem A, fun _ => by simp⟩, fun _ => by simp⟩

/-- Swapping the two zero-width counts supplies positive and negative oracle-dependent gaps. -/
noncomputable def queryGap (A : Set (List Bool)) (w : List Bool) : ℤ :=
  (queryCount A w : ℤ) - acceptCount (fun x => !queryVerifier A x) w 0

theorem queryGap_mem (A : Set (List Bool)) : queryGap A ∈ GapPWithOracle A encBits :=
  ⟨queryCount A, queryCount_mem A, _,
    ⟨0, fun x => !queryVerifier A x,
      (queryVerifier_polyTime A).map (.of_tidy ComputableTidilyInPolyTime.bool_not), fun _ => rfl⟩,
    fun _ => by simp [queryGap]⟩

example : queryGap {w | w = [true]} [true] = 1 ∧
    queryGap {w | w = [true]} [false] = -1 := by
  simp [queryGap, queryCount, acceptCount_zero, queryVerifier]

example (A : Set (List Bool)) : (fun _ : List Bool => 1) ∈ SharpPWithOracle A encBits :=
  SharpP_subset_SharpPWithOracle A encBits
    ⟨0, fun _ => true, .const true, fun _ => by simp [acceptCount_true]⟩

example : SharpPWithOracle ∅ encBits = SharpP encBits ∧
    GapPWithOracle ∅ encBits = GapP encBits ∧ PPWithOracle ∅ encBits = PP encBits := by
  have h : (∅ : Set (List Bool)) ∈ P encBits :=
    ⟨fun _ => false, .const false, fun _ => by simp⟩
  exact ⟨SharpPWithOracle_eq_SharpP h _, GapPWithOracle_eq_GapP h _, PPWithOracle_eq_PP h _⟩

/-- A nonempty oracle in P is eliminated by the existing machine simulation. -/
example : PPWithOracle {w : List Bool | w.isEmpty = true} encBits = PP encBits := by
  apply PPWithOracle_eq_PP
  exact ⟨List.isEmpty, by fun_prop, fun _ => Iff.rfl⟩

/-- info: 'Cslib.Complexity.mem_PPWithOracle_iff_exists_GapPWithOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_PPWithOracle_iff_exists_GapPWithOracle
/-- info: 'Cslib.Complexity.SharpPWithOracle_eq_SharpP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SharpPWithOracle_eq_SharpP
/-- info: 'Cslib.Complexity.GapPWithOracle_eq_GapP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GapPWithOracle_eq_GapP
/-- info: 'Cslib.Complexity.PPWithOracle_eq_PP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PPWithOracle_eq_PP

end Cslib.Complexity.Tests.RelativizedCounting
