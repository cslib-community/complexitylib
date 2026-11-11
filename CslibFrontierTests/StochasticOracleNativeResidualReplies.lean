/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualReplies
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Actual raw reports on five overlapping-triple X3C blocks

The original binary WSC has thirty points. Every hidden missing block drives
both raw replies, with no independent resampling. Actual packet parsing and
runtime updates produce a six-point residual, a live first guard, then a
weight-one decoded output and a stopped guard. Invoice magnitudes are arbitrary.
Canceled and inactive concurrent slots contribute no candidates.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualReplies
open Cslib.Probability Cslib.Probability.StochasticOracle NativeRetention ResidualCover
open NativeResidualReplies ConcurrentBatch Finset

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm

-- Both reports depend on the same arbitrary hidden j. The first actual raw
-- report is parsed and retained; its runtime residual is the six-point block.
example (j : Fin 5) (bits : ℕ) :
    (NativeResidualSelector.residual
      (afterNear blocks points candidates j (2 ^ bits))).toFinset.card = 6 ∧
      RuntimeControl.stopped (afterNear blocks points candidates j (2 ^ bits)) = false := by
  constructor
  · rw [near_residual blocks points candidates (by norm_num), card_map]
    rw [groundBlock, card_map, card_univ, Fintype.card_fin]
    rfl
  · exact near_live blocks points candidates (by norm_num) j _

-- After the matching actual raw specialist report, the source decoder reads
-- an optimal cover from RuntimeControl.result, and the real stop guard is set.
example (j : Fin 5) (nearBits specialistBits : ℕ) :
    let state := afterSpecialist blocks points candidates j (2 ^ nearBits) (2 ^ specialistBits)
    let I := NativeResidualEncoding.nativeInstance blocks points candidates (by norm_num)
    RuntimeControl.stopped state = true ∧
      ∃ F, decodeFamily (SourceEncoding.toNative
        (NativeResidualEncoding.source blocks points candidates)).rows.length
          (RuntimeControl.result state) = some F ∧
        I.covered (F.image Fin.val) = I.ground ∧ I.cost (F.image Fin.val) = 1 := by
  obtain ⟨_, houtput⟩ := completed_output blocks points candidates (by norm_num) j
    (2 ^ nearBits) (2 ^ specialistBits)
  exact ⟨specialist_stopped blocks points candidates (by norm_num) j _ _, houtput⟩

private def canceled (bits : ℕ) : Answers blocks 6 :=
  fun i => some (none, 2 ^ bits + i.val)

-- Arbitrary invoice bits survive the wire codec but cannot become candidates.
example (bits : ℕ) :
    (Packets.families 6
      (SourceEncoding.toNative (NativeResidualEncoding.source blocks points candidates)).rows.length
      (encodeReport (report blocks candidates (canceled bits)))).map
        (fun P => (normalize (SourceEncoding.toNative
          (NativeResidualEncoding.source blocks points candidates)) P).toFinset) = [] := by
  rw [normalized_report]
  simp [returned, canceled]

-- Cancellation in the near-cover slot plus all five concurrent specialist
-- replies: original candidate provenance and opportunity order are preserved.
private def mixed (bits : ℕ) : Answers blocks 6 :=
  Fin.cases (some (none, 2 ^ bits)) (fun j => some (some (specialist blocks j), j.val + 1))

example (bits : ℕ) :
    (Packets.families 6
      (SourceEncoding.toNative (NativeResidualEncoding.source blocks points candidates)).rows.length
      (encodeReport (report blocks candidates (mixed bits)))).map
        (fun P => (normalize (SourceEncoding.toNative
          (NativeResidualEncoding.source blocks points candidates)) P).toFinset) =
      (List.ofFn fun j : Fin 5 => (specialist blocks j).map
        (NativeResidualEncoding.candidateLabel blocks candidates)) := by
  rw [normalized_report]
  simp [returned, mixed, List.ofFn_succ]

private def allBatch : ConcurrentBatch.Batch 6 :=
  ⟨fun _ => some [], ⟨0, by simp [active]⟩⟩

private def unitLimits : Limits 6 := ⟨fun _ => 1, by intro _; norm_num, 2, 2⟩
private def sourceFamilies : Fin 6 → Option (Finset (Candidate blocks)) :=
  Fin.cases none (fun j => some (specialist blocks j))

-- This time the raw word is read from an actual observe/replyOf receipt with
-- five simultaneous source families and a billed canceled call, rather than
-- constructed as a decoded-report assumption.
example (bits : ℕ) :
    (Packets.families 6
      (SourceEncoding.toNative (NativeResidualEncoding.source blocks points candidates)).rows.length
      (replyOf (observe unitLimits 2 allBatch
        (fun i => path blocks candidates (sourceFamilies i) (2 ^ bits + i.val)))).word).map
          (fun P => (normalize (SourceEncoding.toNative
            (NativeResidualEncoding.source blocks points candidates)) P).toFinset) =
      (List.ofFn fun j : Fin 5 => (specialist blocks j).map
        (NativeResidualEncoding.candidateLabel blocks candidates)) := by
  rw [observed_proposals blocks points candidates unitLimits 2 allBatch sourceFamilies
    (fun i => 2 ^ bits + i.val) (fun _ => rfl) (by norm_num)]
  simp [returned, answersFor, allBatch, sourceFamilies, List.ofFn_succ]

-- The exact same receipt has additive accrued invoices and maximum concurrent
-- unit latency, even though the canceled opportunity returned no family.
example (bits : ℕ) :
    let receipt := observe unitLimits 2 allBatch
      (fun i => path blocks candidates (sourceFamilies i) (2 ^ bits + i.val))
    receipt.tokens = (∑ i : Fin 6, (2 ^ bits + i.val)) ∧ receipt.duration = 1 := by
  have h := observed_resources blocks candidates unitLimits 2 allBatch sourceFamilies
    (fun i => 2 ^ bits + i.val) (fun _ => rfl) (by norm_num)
  simpa only [active, allBatch, Option.isSome_some, filter_true] using h

-- Sampling the hidden missing component once gives correlated raw replies.
-- The actual runtime completion/stop decision is certain under this mixture.
example (nearBits specialistBits : ℕ) :
    (PMF.uniformOfFintype (Fin 5)).map (fun j =>
      RuntimeControl.stopped (afterSpecialist blocks points candidates j
        (2 ^ nearBits) (2 ^ specialistBits))) = PMF.pure true := by
  simp only [specialist_stopped blocks points candidates (by norm_num)]
  exact PMF.map_const _ _

-- The zero-interface edge has no proposal despite its canonical report tag.
example : returned blocks (fun i : Fin 0 => Fin.elim0 i) = [] := rfl

end CslibFrontierTests.StochasticOracleNativeResidualReplies
