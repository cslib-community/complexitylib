/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORJoinedDissection
public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatchBounds
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatchBounds
import all Complexity.Cryptanalysis.AddXNORJoinedDissection
import all Complexity.Cryptanalysis.AddXNORClassBatches
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Computability.GenericRAM.Native.Combinators

/-!
# Original-width clocks of restarted dissection matching

Normalize the installed two-orientation matcher, including its argument copies,
tagging, radix sorting and witness scan. The original-input corollaries sum the
actual matching certificate fields over generated class/batch labels and bound
simultaneous matching workspace from computed balance. Counts, division, quarter
regeneration and window/full-state producer callbacks remain separate clock
obligations; this is not a global source running-time theorem.

This is resource accounting for the sorted-list route to
[WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22. It does not establish
those source asymptotics or the reachable-state-DP all-count prepass.

## Main definitions

* `restartTime`, `restartSpace`: installed matching profiles at one generated label.
* `restartWork`: matching-clock sum over generated labels before early exits.

## Main results

* `matchCertificate_bounds`: actual two-orientation matching in physical widths.
* `original_restart_bounds`: original-input global fallback matching sum and prefix space.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.MatcherResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er

private def arguments (parameter : BatchedAccess.Parameter) (batch : List (ℕ × ℕ)) :
    SortedMatch.Input :=
  let (width, (right, kept)) := parameter
  (width, if right then (batch, kept) else (kept, batch))

private theorem profile_eq (parameter : BatchedAccess.Parameter) (batch : List (ℕ × ℕ)) :
    BatchedAccess.matchCertificate.time (parameter, batch) =
        4 * (encPair BatchedAccess.parameterEncoding el (parameter, batch)).length +
          SortedMatch.runCertificate.time (arguments parameter batch) ∧
    BatchedAccess.matchCertificate.space (parameter, batch) =
        4 * (encPair BatchedAccess.parameterEncoding el (parameter, batch)).length +
          SortedMatch.runCertificate.space (arguments parameter batch) := by
  rcases parameter with ⟨w, right, kept⟩
  cases right <;> constructor <;>
    dsimp only [BatchedAccess.matchCertificate, NativeCertificate.congr,
      NativeCertificate.comp, NativeCertificate.branch, NativeCertificate.prod,
      NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
      NativeCertificate.linear, Bool.false_eq_true, ↓reduceIte,
      Function.comp_def, id_eq, arguments] <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The actual installed matcher costs linear record volume times a fixed polynomial
in physical key/record width, in either computed orientation. The hypotheses are only
encoding bounds; original-input clients below derive them from actual generated records. -/
theorem matchCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (w B : ℕ) (right : Bool) (kept batch : List (ℕ × ℕ)),
      w ≤ B → (∀ r ∈ kept ++ batch, (RadixPartition.recordEncoding r).length ≤ B) →
      BatchedAccess.matchCertificate.time ((w, (right, kept)), batch) +
        BatchedAccess.matchCertificate.space ((w, (right, kept)), batch) ≤
          (kept.length + batch.length + 1) * P B := by
  obtain ⟨Q, hQ, mQ, bound⟩ := SortedMatch.runCertificate_bounds
  let P := fun B => 100 * (B+1) + Q (2*B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have h := mQ (by omega : 2*a+1 ≤ 2*b+1)
    dsimp only [P]; omega
  · intro w B right kept batch hw rows
    let parameter : BatchedAccess.Parameter := (w, (right, kept))
    let n := kept.length + batch.length + 1
    have hk := length_encList_le er kept (fun r hr => rows r (List.mem_append_left _ hr))
    have hb := length_encList_le er batch (fun r hr => rows r (List.mem_append_right _ hr))
    have wire : (encPair BatchedAccess.parameterEncoding el (parameter, batch)).length ≤
        10 * n * (B+1) := by
      simp only [BatchedAccess.parameterEncoding, parameter, length_encPair,
        encUnary_apply, List.length_replicate, encBool_apply, List.length_singleton]
      dsimp only [el] at hk hb ⊢
      dsimp only [n]
      nlinarith only [hk, hb, hw]
    have width : SortedMatch.inputWidth (arguments parameter batch) ≤ 2*B+1 := by
      have forward : streamRecordLength er (kept ++ batch) ≤ B := listMax_le rows
      have backward : streamRecordLength er (batch ++ kept) ≤ B := by
        apply listMax_le
        intro r hr
        exact rows r (by simpa only [List.mem_append, or_comm] using hr)
      cases right <;>
        simp only [arguments, parameter, SortedMatch.inputWidth, Bool.false_eq_true, ↓reduceIte]
        <;> change w + streamRecordLength er _ + 1 ≤ _ <;> omega
    have actual := bound (arguments parameter batch)
    have lengthEq : (arguments parameter batch).2.1.length +
        (arguments parameter batch).2.2.length + 1 = n := by
      cases right <;> simp [arguments, parameter, n, Nat.add_comm]
    dsimp only at actual
    rw [lengthEq] at actual
    have normalized := actual.trans (Nat.mul_le_mul_left n (mQ width))
    obtain ⟨ht, hs⟩ := profile_eq parameter batch
    change _ + _ ≤ n * P B
    rw [ht, hs]
    dsimp only [P]
    nlinarith only [normalized, wire]

/-- Matching time at one generated restart label. Producer/count/loop clocks are separate. -/
noncomputable def restartTime (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  BatchedAccess.matchCertificate.time
    (BatchedAccess.parameters (JoinedDissection.probeTask input g),
      ClassBatches.batch (JoinedDissection.probeContext input g) g i)

/-- Matching's all-prefix workspace allowance at one generated restart label. -/
noncomputable def restartSpace (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  BatchedAccess.matchCertificate.space
    (BatchedAccess.parameters (JoinedDissection.probeTask input g),
      ClassBatches.batch (JoinedDissection.probeContext input g) g i)

/-- Sum of installed matching clocks over the actual generated labels, before early exits.
This intentionally excludes generation, count, division and loop-control clocks. -/
noncomputable def restartWork (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  ((ClassBatches.labels (JoinedDissection.probeContext input g) g).map
    (restartTime input g)).sum

/-- Original-width normalization of actual matching clocks across all classes and batches,
and simultaneous matching workspace for every batch (including padding/empty batches).
Early exits can only omit calls from this conservative sum. The space field bounds every
prefix of the matching machine, including argument copies and internal sorting/scan tapes.
This theorem does not bound the other callbacks of the assembled dissection machine. -/
theorem original_restart_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length + bs.length + cs.length + ds.length
      (∑ g : BitVec p, restartWork input g.toNat) ≤
        4 * (6 * (2 ^ (as.length+bs.length) + 2 ^ (cs.length+ds.length)) +
          4 * 2 ^ p * (JoinedDissection.quarterBudget input+1)) * P (2*m+1+q) ∧
      ∀ (g : BitVec p) (i : ℕ), restartSpace input g.toNat i ≤
        2 * (ClassBalance.balance input + JoinedDissection.quarterBudget input + 1) *
          P (2*m+1+q) := by
  obtain ⟨P, hP, mono, bound⟩ := matchCertificate_bounds
  refine ⟨P, hP, mono, ?_⟩
  intro m p hp as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length+bs.length+cs.length+ds.length
  let B := 2*m+1+q
  have installed (g : BitVec p) (i : ℕ) :
      restartTime input g.toNat i + restartSpace input g.toNat i ≤
        ((ClassBalance.retain input g.toNat).length +
          (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length+1)
            * P B := by
    let batch := ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i
    have rows (r : ℕ × ℕ) (hr : r ∈ ClassBalance.retain input g.toNat ++ batch) :
        (er r).length ≤ B := by
      rcases List.mem_append.mp hr with kept | produced
      · exact ClassBalance.record_wire hp as bs cs ds s _ g r kept
      · exact ClassBalance.record_wire hp as bs cs ds s _ g r
          (ClassBatches.batch_sound (JoinedDissection.probeContext input g.toNat) _ i r produced)
    exact bound m B _ (ClassBalance.retain input g.toNat) batch (by dsimp only [B]; omega) rows
  have classBound (g : BitVec p) : restartWork input g.toNat ≤
      4 * JoinedDissection.restartCopyWork input g.toNat * P B := by
    let context := JoinedDissection.probeContext input g.toNat
    let C := ClassBatches.capacity context
    have each (i : ℕ) : restartTime input g.toNat i ≤ 4*C*P B := by
      have actual := installed g i
      have batch := ClassBatches.batch_length context g.toNat i
      have capacity := JoinedDissection.restart_capacity_eq input g.toNat
      have volume : (ClassBalance.retain input g.toNat).length +
          (ClassBatches.batch context g.toNat i).length+1 ≤ 4*C := by
        change C = (ClassBalance.retain input g.toNat).length + 1 +
          ClassBatches.quarterVolume context at capacity
        change _ ≤ C + _ at batch
        omega
      exact (Nat.le_add_right _ _).trans
        (actual.trans (Nat.mul_le_mul_right (P B) volume))
    have sumBound (labels : List ℕ) :
        (labels.map (restartTime input g.toNat)).sum ≤ labels.length*(4*C*P B) := by
      induction labels with
      | nil => simp
      | cons i labels ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have step := Nat.add_le_add (each i) ih
        exact step.trans_eq (by ring)
    exact (sumBound (ClassBatches.labels context g.toNat)).trans_eq (by
      dsimp only [JoinedDissection.restartCopyWork, context, C]; ring)
  constructor
  · have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => classBound g)
    have copies := JoinedDissection.sum_restartCopyWork hp as bs cs ds s
    have summed : (∑ g : BitVec p, 4 * JoinedDissection.restartCopyWork input g.toNat * P B) =
        4 * (∑ g : BitVec p, JoinedDissection.restartCopyWork input g.toNat) * P B := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [summed] at total
    exact total.trans (Nat.mul_le_mul_right (P B) (Nat.mul_le_mul_left 4 copies))
  · intro g i
    have actual := installed g i
    have prefixBound := JoinedDissection.restart_prefix_records input g.toNat i
      (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length g.isLt
    rw [List.take_length] at prefixBound
    have volume : (ClassBalance.retain input g.toNat).length +
        (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length+1 ≤
          2*(ClassBalance.balance input + JoinedDissection.quarterBudget input+1) := by omega
    exact (Nat.le_add_left _ _).trans
      (actual.trans (Nat.mul_le_mul_right (P B) volume))

end Cslib.Cryptanalysis.AddXNOR.MatcherResources
