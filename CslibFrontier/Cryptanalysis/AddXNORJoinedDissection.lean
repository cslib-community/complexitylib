/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
public import CslibFrontier.Cryptanalysis.AddXNORClassBalance
public import CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
public import CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
public import CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Original-input dissection with generated class retention

Actual forward/backward quarter-query counts determine the retained side.
Its generated full-state class feeds either one whole-class match (when computed
counts give a quarter-plus-retained record allowance) or restarted row-aligned
opposite-quarter batches. The fixed outer class counter then releases it. The source
frontend computes the cut, capped projection depth, first-operand seed and zero
target. Count-only balance preprocessing and original witness readback are
included in the uniform bit execution.

This assembles the class producer with an executable search endpoint for
[WangLvShenZhang2027], Lemma 8/Theorem 7, pp. 21–22. No opposite half-space scan
is executed. Both installed branches avoid per-pair dictionary/buffer state. Restarted
windows keep the dictionary outside pair generation and release completed batches.
Actual per-batch copies, quarter rescans and all callback tapes remain charged.
Balance reduction uses one
scalar. Preparation/readback have derived polynomial physical-input resource
bounds. Logical list occupancy does not imply sharp internal TM workspace.
Sharp global bit resources remain open.

## Main definitions

* `materialize`, `directSearch`, `search`: count-selected direct or restarted class matching.
* `allSearch`: uniform all-class search and release.
* `run`: original-input preprocessing, computed balance, search and witness readback.

## Main results

* `original_correct`, `original_balance`: original witness/miss and exact computed balance.
* `direct_prefix_wire`, `restart_prefix_wire`: physical logical-prefix storage.
* `restart_prefix_records`, `sum_restartCopyWork`: actual batch size and global copy allowance.
* `quarterBudget_source`: derived quarter allowance, including every residue.
* `sum_directRecordWork`: single-match record volume, distinct from bit time.
* `allSearch_wire`, `preparation_readback_bounds`: actual result size and boundary resource costs.
* `halvesCertificate`, `readbackCertificate`: installed boundary machines.
* `sum_pairVisits`: produced-class pair populations are bounded by the two half populations.
* `allSearch_eq_fold`: the fixed counter agrees with actual class-index streaming.
* `sourceCertificate`: actual uniform bit execution, including batch copies and callback tapes.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.JoinedDissection
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Combine actual original quarters into the two halves used by the existing probe/readback. -/
def halves (input : ClassBalance.Input) : SortedMeet.Input :=
  let (((width, _), (seed, _)), ((first, second), (third, fourth))) := input
  ((width, seed), (first ++ second, third ++ fourth))

/-- Existing probe task, with actual original halves and runtime selected class. -/
def classInput (input : ClassBalance.Input) (g : ℕ) : ClassStreaming.Input :=
  (halves input, (ClassBalance.depth input, g))

/-- Only the computed smaller class is generated; its count determines bounded-batch capacity. -/
def probeTask (input : ClassBalance.Input) (g : ℕ) : BatchedAccess.Task :=
  let right := ClassBalance.retainRight input g
  (((classInput input g, right), ClassBalance.retain input g), ClassBalance.count input right g + 1)

/-- The produced side is opposite the computed retained dictionary, with its actual capacity. -/
def probeContext (input : ClassBalance.Input) (g : ℕ) : JoinedProbe.Context :=
  let task := probeTask input g
  let (((_, right), _), capacity) := task
  ((input, !right), (BatchedAccess.parameters task, capacity))

/-- A physical quarter-scale record allowance, derived from the original arrays. -/
def quarterBudget (input : ClassBalance.Input) : ℕ :=
  let (_, ((first, second), (third, fourth))) := input
  2 ^ first.length + 2 ^ second.length + 2 ^ third.length + 2 ^ fourth.length

/-- The concrete source cut contributes at most eleven quarter populations, including
all fourth-quarter residue cases. The capped projection depth is not a memory advice input. -/
theorem quarterBudget_source {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    quarterBudget (Source.prepare (Source.ofWords p s tail)) ≤ 11 * 2 ^ (tail.length / 4) := by
  rw [Source.prepare_ofWords]
  have lengths := Source.quarters_lengths tail
  dsimp only at lengths
  simp only [quarterBudget, ProgramGeneration.originalSource, BitInput.words, List.length_map,
    lengths.1, lengths.2.1, lengths.2.2.1, lengths.2.2.2]
  have residue : tail.length - 3 * (tail.length / 4) ≤ tail.length / 4 + 3 := by omega
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) residue
  rw [pow_add] at power
  norm_num at power
  omega

/-- Actual counts permit a single match when the opposite class fits quarter-plus-retained space.
An empty retained class uses the existing proved generation skip. -/
def materialize (input : ClassBalance.Input) (g : ℕ) : Bool :=
  let right := ClassBalance.retainRight input g
  decide (0 < ClassBalance.count input right g ∧
    ClassBalance.count input (!right) g ≤ ClassBalance.count input right g + quarterBudget input)

/-- Full opposite-class generation followed by one radix match; no per-pair dictionary/buffer
state is threaded through this branch. The count test bounds its materialized list. -/
def directSearch (input : ClassBalance.Input) (g : ℕ) : Option (ℕ × ℕ) :=
  let task := probeTask input g
  BatchedAccess.matchBatch (BatchedAccess.parameters task)
    (ClassBalance.records input (!(ClassBalance.retainRight input g)) g)

/-- Use one match when computed populations permit it, otherwise the bounded streaming route. -/
def search (input : ClassBalance.Input) (g : ℕ) : Option (ℕ × ℕ) :=
  if materialize input g then directSearch input g else ClassBatches.run (probeContext input g) g

/-- Logical output prefix of the directly materialized opposite class, empty in the
streaming branch. The actual producer's internal temporaries are charged separately. -/
def directPrefix (input : ClassBalance.Input) (g n : ℕ) : List (ℕ × ℕ) :=
  if materialize input g then
    (ClassBalance.records input (!(ClassBalance.retainRight input g)) g).take n else []

/-- Matching input record volume of the single-match branch; zero when it is not selected. -/
def directRecordWork (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  if materialize input g then (ClassBalance.retain input g).length +
    ClassBalance.count input (!(ClassBalance.retainRight input g)) g else 0

/-- Every direct-generation prefix fits the computed retained balance plus the actual
quarter allowance. No desired class-memory bound is supplied as a premise. -/
theorem direct_prefix_records (input : ClassBalance.Input) (g n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (ClassBalance.retain input g).length + (directPrefix input g n).length ≤
      2 * ClassBalance.balance input + quarterBudget input := by
  have hk := ClassBalance.class_le_balance input g hg
  by_cases h : materialize input g = true
  · have test := of_decide_eq_true h
    change 0 < ClassBalance.count input (ClassBalance.retainRight input g) g ∧
      ClassBalance.count input (!(ClassBalance.retainRight input g)) g ≤
        ClassBalance.count input (ClassBalance.retainRight input g) g + quarterBudget input at test
    have hl : ((ClassBalance.records input (!(ClassBalance.retainRight input g)) g).take n).length ≤
        ClassBalance.count input (!(ClassBalance.retainRight input g)) g := by
      rw [List.length_take, ClassBalance.records_length]
      exact Nat.min_le_right _ _
    simp only [directPrefix, h, ite_true]
    rw [ClassBalance.retain, ClassBalance.records_length] at hk ⊢
    omega
  · simp only [directPrefix, h, Bool.false_eq_true, ite_false, List.length_nil, Nat.add_zero]
    omega

/-- The actual produced quarter input is part of the original four-quarter allowance. -/
theorem restart_quarter_le (input : ClassBalance.Input) (g : ℕ) :
    ClassBatches.quarterVolume (probeContext input g) ≤ quarterBudget input := by
  rcases input with ⟨⟨⟨width, depth⟩, seed, target⟩, ⟨first, second⟩, third, fourth⟩
  have ha := Nat.zero_le (2 ^ first.length)
  have hb := Nat.zero_le (2 ^ second.length)
  have hc := Nat.zero_le (2 ^ third.length)
  have hd := Nat.zero_le (2 ^ fourth.length)
  cases h : ClassBalance.retainRight (((width, depth), (seed, target)),
    ((first, second), (third, fourth))) g <;>
    simp only [ClassBatches.quarterVolume, probeContext, probeTask, h, Bool.not_true,
      Bool.not_false, ClassBalance.halfInput, Bool.false_eq_true, ite_false, ite_true,
      List.length_reverse, quarterBudget] <;> omega

private theorem restart_capacity_eq (input : ClassBalance.Input) (g : ℕ) :
    ClassBatches.capacity (probeContext input g) = (ClassBalance.retain input g).length + 1 +
      ClassBatches.quarterVolume (probeContext input g) := by
  change ClassBalance.count input (ClassBalance.retainRight input g) g + 1 + _ = _
  rw [ClassBalance.retain, ClassBalance.records_length]

/-- Dictionary and every actual restarted-batch output prefix fit computed balance plus
quarter volume. No growing per-pair buffer is executed by this fallback. -/
theorem restart_prefix_records (input : ClassBalance.Input) (g i n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (ClassBalance.retain input g).length +
      ((ClassBatches.batch (probeContext input g) g i).take n).length ≤
        2 * ClassBalance.balance input + 2 * quarterBudget input + 1 := by
  have hk := ClassBalance.class_le_balance input g hg
  have hb := ClassBatches.batch_length (probeContext input g) g i
  have htake : ((ClassBatches.batch (probeContext input g) g i).take n).length ≤
      (ClassBatches.batch (probeContext input g) g i).length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  rw [restart_capacity_eq] at hb
  have hq := restart_quarter_le input g
  omega

/-- Capacity volume copied per generated restart label, including quarter regeneration.
Direct and empty classes may skip this budget; it conservatively covers all classes. -/
def restartCopyWork (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  let context := probeContext input g
  (ClassBatches.labels context g).length * ClassBatches.capacity context

private theorem search_none_records (input : ClassBalance.Input) (g : ℕ)
    (fits : let (((width, _), _), _) := input
      ∀ r ∈ ClassBalance.retain input g ++
        ClassBalance.records input (!(ClassBalance.retainRight input g)) g, r.1 < 2 ^ width) :
    search input g = none ↔ ¬ BatchedAccess.Meets (ClassBalance.retain input g)
      (ClassBalance.records input (!(ClassBalance.retainRight input g)) g) := by
  let parameter := BatchedAccess.parameters (probeTask input g)
  let rows := ClassBalance.records input (!(ClassBalance.retainRight input g)) g
  have hd := BatchedAccess.match_none parameter rows fits
  have hs := ClassBatches.run_none (probeContext input g) g fits
  rw [search]
  split
  · exact hd
  · exact hs

private theorem search_sound_records (input : ClassBalance.Input) (g : ℕ) (out : ℕ × ℕ)
    (hit : search input g = some out) :
    ∃ a ∈ ClassBalance.retain input g,
      ∃ b ∈ ClassBalance.records input (!(ClassBalance.retainRight input g)) g,
        a.1 = b.1 ∧ out = if ClassBalance.retainRight input g then (b.2, a.2) else (a.2, b.2) := by
  rw [search] at hit
  split at hit
  · exact BatchedAccess.match_sound (BatchedAccess.parameters (probeTask input g)) _ out hit
  · exact ClassBatches.run_sound (probeContext input g) g out hit

private theorem halves_original {m p : ℕ} (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    halves (ProgramGeneration.originalSource p as bs cs ds s 0) =
      ((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)) := by
  simp only [halves, ProgramGeneration.originalSource, BitInput.words, List.map_append]

private theorem classInput_original {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : ℕ) :
    classInput (ProgramGeneration.originalSource p as bs cs ds s 0) g =
      (((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)), (p, g)) := by
  rw [classInput, halves_original]
  rfl

private theorem produced_mem {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (right : Bool) (r : ℕ × ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    r ∈ ClassBalance.records input right g.toNat ↔
      r ∈ ClassStreaming.records (classInput input g.toNat) right
        (ClassStreaming.limit (classInput input g.toNat) right) := by
  have h := ClassBalance.records_mem_counter hp as bs cs ds s right g r
  dsimp only at h ⊢
  simpa only [classInput_original] using h

private theorem kept_mem {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (r : ℕ × ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    r ∈ ClassBalance.retain input g.toNat ↔
      r ∈ ClassStreaming.records (classInput input g.toNat)
        (ClassBalance.retainRight input g.toNat)
        (ClassStreaming.limit (classInput input g.toNat)
          (ClassBalance.retainRight input g.toNat)) := by
  dsimp only
  rw [ClassBalance.retain]
  exact produced_mem hp as bs cs ds s g _ r

private theorem probe_fits {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let right := ClassBalance.retainRight input g.toNat
    ∀ r ∈ ClassBalance.retain input g.toNat ++ ClassBalance.records input (!right) g.toNat,
      r.1 < 2 ^ m := by
  dsimp only
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [ClassBalance.retain] at hr
    exact (ClassBalance.records_fit hp as bs cs ds s 0 _ g r hr).1
  · exact (ClassBalance.records_fit hp as bs cs ds s 0 _ g r hr).1

/-- The generated retained dictionary gives exactly the original selected-class miss semantics,
independently of how its computed orientation differs from the old counter orientation. -/
theorem search_none {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    search input g.toNat = none ↔ ClassStreaming.search (classInput input g.toNat) = none := by
  dsimp only
  have hm := search_none_records (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
    (probe_fits hp as bs cs ds s g)
  rw [hm, ClassStreaming.search_none]
  have hkept (r : ℕ × ℕ) := kept_mem hp as bs cs ds s g r
  have hproduced (right : Bool) (r : ℕ × ℕ) := produced_mem hp as bs cs ds s g right r
  dsimp only at hkept hproduced
  simp only [BatchedAccess.Meets, hkept, hproduced]
  cases h : ClassBalance.retainRight (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
  · simp only [Bool.not_false]
  · simp only [Bool.not_true]
    constructor <;> intro hno hex
    · obtain ⟨a, ha, b, hb, he⟩ := hex
      exact hno ⟨b, hb, a, ha, he.symm⟩
    · obtain ⟨b, hb, a, ha, he⟩ := hex
      exact hno ⟨a, ha, b, hb, he.symm⟩

/-- Every returned pair has actual forward/backward original-class provenance. -/
theorem search_sound {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (out : ℕ × ℕ)
    (hit : search (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat = some out) :
    let input := classInput (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
    ∃ a ∈ ClassStreaming.records input false (ClassStreaming.limit input false),
      ∃ b ∈ ClassStreaming.records input true (ClassStreaming.limit input true),
        a.1 = b.1 ∧ out = (a.2, b.2) := by
  have h := search_sound_records (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
    out hit
  obtain ⟨a, ha, b, hb, hk, ho⟩ := h
  have hkept := kept_mem hp as bs cs ds s g a
  have hproduced := produced_mem hp as bs cs ds s g
    (!ClassBalance.retainRight (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat) b
  dsimp only at hkept hproduced
  rw [hkept] at ha
  rw [hproduced] at hb
  cases h : ClassBalance.retainRight (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
  · exact ⟨a, by simpa only [h] using ha, b, by simpa only [h, Bool.not_false] using hb,
      hk, by simpa only [h, Bool.false_eq_true, ite_false] using ho⟩
  · exact ⟨b, by simpa only [h, Bool.not_true] using hb, a, by simpa only [h] using ha,
      hk.symm, by simpa only [h, ite_true] using ho⟩

/-- Produced-class pair domain (the preserved per-pair consumer's iteration slots).
Restarted-machine costs are bounded separately by `sum_restartCopyWork`. -/
def pairVisits (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  JoinedProbe.visits (probeContext input g) g

private theorem counter_sum (source : SortedMeet.Input) (p : ℕ) (right : Bool) :
    (∑ g : BitVec p, ClassStreaming.count (source, (p, g.toNat)) right) =
      ClassStreaming.limit (source, (p, 0)) right := by
  let n := ClassStreaming.limit (source, (p, 0)) right
  let key := fun u => BitVec.ofNat p (ClassStreaming.row (source, (p, 0)) right u).1
  let keys : Multiset (BitVec p) := ↑((List.range n).map key)
  have count (g : BitVec p) : ClassStreaming.count (source, (p, g.toNat)) right = keys.count g := by
    rw [ClassStreaming.count_eq]
    simp only [ClassStreaming.records, List.length_map, ← List.countP_eq_length_filter]
    change (List.range n).countP _ = keys.count g
    dsimp only [keys]
    rw [Multiset.coe_count, List.count_eq_countP, List.countP_map]
    congr 1
  simp_rw [count]
  have h := Multiset.sum_count_eq_card (s := Finset.univ) (m := keys) (fun _ _ => Finset.mem_univ _)
  simpa only [keys, Multiset.coe_card, List.length_map, List.length_range] using h

private theorem sum_counts {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (right : Bool) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (∑ g : BitVec p, ClassBalance.count input right g.toNat) =
      2 ^ (if right then cs.length + ds.length else as.length + bs.length) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have h := counter_sum ((m, s.toNat),
    ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)) p right
  have hc (g : BitVec p) := ClassBalance.count_eq_counter hp as bs cs ds s right g
  dsimp only at hc
  dsimp only [input]
  simp_rw [hc]
  rw [h]
  cases right <;>
    simp [ClassStreaming.limit, ClassStreaming.sideInput, SortedMeet.inverseInput, Nat.add_comm]

/-- Across all classes, the generated opposite traversal has at most the two actual half-space
populations in total. This removes the repeated half scans; copying/bit costs remain separate. -/
theorem sum_pairVisits {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (∑ g : BitVec p, pairVisits input g.toNat) ≤
      2 ^ (as.length + bs.length) + 2 ^ (cs.length + ds.length) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have counts := sum_counts hp as bs cs ds s
  have bound (g : BitVec p) : pairVisits input g.toNat ≤
      ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat := by
    have hv := JoinedProbe.visits_le_count (probeContext input g.toNat) g.toNat
    change pairVisits input g.toNat ≤ _ at hv
    cases h : ClassBalance.retainRight input g.toNat <;>
      simp only [h, Bool.not_true, Bool.not_false] at hv <;> omega
  have h := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => bound g)
  rw [Finset.sum_add_distrib, counts false, counts true] at h
  exact h

/-- All directly matched record volumes together are bounded by the actual two half
populations. This charges dictionary reads once per selected class, not once per pair;
it is record volume, not a bit-time or internal-space theorem. -/
theorem sum_directRecordWork {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (∑ g : BitVec p, directRecordWork input g.toNat) ≤
      2 ^ (as.length + bs.length) + 2 ^ (cs.length + ds.length) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have bound (g : BitVec p) : directRecordWork input g.toNat ≤
      ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat := by
    dsimp only [directRecordWork]
    split
    · rw [ClassBalance.retain, ClassBalance.records_length]
      cases ClassBalance.retainRight input g.toNat <;>
        simp [Bool.not_true, Bool.not_false, Nat.add_comm]
    · exact Nat.zero_le _
  have h := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => bound g)
  rw [Finset.sum_add_distrib, sum_counts hp as bs cs ds s false,
    sum_counts hp as bs cs ds s true] at h
  exact h

/-- Global repeated quarter/retained input volume of the installed fallback is bounded by
the half populations and class count times quarter volume. This is not yet a bit-time theorem:
actual scalar widths, sorting and callback profiles remain separately charged. -/
theorem sum_restartCopyWork {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (∑ g : BitVec p, restartCopyWork input g.toNat) ≤
      6 * (2 ^ (as.length+bs.length) + 2 ^ (cs.length+ds.length)) +
        4 * 2 ^ p * (quarterBudget input+1) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have bound (g : BitVec p) : restartCopyWork input g.toNat ≤
      6 * (ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat) +
        4 * (quarterBudget input+1) := by
    have charge := ClassBatches.copyAllowance (probeContext input g.toNat) g.toNat
    change restartCopyWork input g.toNat ≤ _ at charge
    rw [restart_capacity_eq, ClassBalance.retained_length] at charge
    have q := restart_quarter_le input g.toNat
    have pop : ClassBatches.population (probeContext input g.toNat) g.toNat ≤
        ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat := by
      cases h : ClassBalance.retainRight input g.toNat <;>
        simp only [ClassBatches.population, probeContext, probeTask, h, Bool.not_true,
          Bool.not_false] <;> omega
    omega
  have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => bound g)
  have populations : (∑ g : BitVec p,
      (ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat)) =
        2 ^ (as.length+bs.length) + 2 ^ (cs.length+ds.length) := by
    rw [Finset.sum_add_distrib, sum_counts hp as bs cs ds s false,
      sum_counts hp as bs cs ds s true]
    simp only [Bool.false_eq_true, ite_false, ite_true]
  have constant : (∑ _g : BitVec p, 4 * (quarterBudget input+1)) =
      2 ^ p * (4 * (quarterBudget input+1)) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin, Nat.cast_id]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, populations, constant] at total
  exact total.trans_eq (by ring)

/-- Each class releases its retained dictionary and live batch; only a found pair survives. -/
def allStep (input : ClassBalance.Input) (state : ℕ × Option (ℕ × ℕ)) :
    ℕ × Option (ℕ × ℕ) :=
  let (g, found) := state
  (g + 1, found.orElse (fun _ => search input g))

/-- Fixed-size runtime outer class counter, including early-hit parking. -/
def allSearch (input : ClassBalance.Input) : Option (ℕ × ℕ) :=
  ((allStep input)^[2 ^ ClassBalance.depth input] (0, none)).2

/-- The fixed class counter is the fold over the exactly generated class-index data. -/
theorem allSearch_eq_fold (input : ClassBalance.Input) :
    allSearch input = (List.range (2 ^ ClassBalance.depth input)).foldl
      (fun found g => found.orElse (fun _ => search input g)) none := by
  rw [allSearch, show allStep input = ClassStreaming.advance
    (fun g found => found.orElse (fun _ => search input g)) from rfl,
    ClassStreaming.advance_eq]

private theorem all_none (input : ClassBalance.Input) : allSearch input = none ↔
    ∀ g < 2 ^ ClassBalance.depth input, search input g = none := by
  have h (n : ℕ) : ((allStep input)^[n] (0, none)).2 = none ↔
      ∀ g < n, search input g = none := by
    rw [show allStep input = ClassStreaming.advance (fun g found =>
      found.orElse (fun _ => search input g)) from rfl, ClassStreaming.advance_eq]
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (_ <|> _) = none ↔ _
      rw [Option.orElse_eq_none, ih]
      constructor
      · rintro ⟨h, hn⟩ g hg
        rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
        · exact h g hg
        · exact hn
      · intro h
        exact ⟨fun g hg => h g (by omega), h n (by omega)⟩
  exact h _

private theorem all_sound (input : ClassBalance.Input) (out : ℕ × ℕ)
    (hit : allSearch input = some out) :
    ∃ g < 2 ^ ClassBalance.depth input, search input g = some out := by
  have h (n : ℕ) (hit : ((allStep input)^[n] (0, none)).2 = some out) :
      ∃ g < n, search input g = some out := by
    rw [show allStep input = ClassStreaming.advance (fun g found =>
      found.orElse (fun _ => search input g)) from rfl, ClassStreaming.advance_eq] at hit
    induction n with
    | zero => simp at hit
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hit
      change (_ <|> _) = some out at hit
      rcases (Option.orElse_eq_some _ _ _).mp hit with old | ⟨_, fresh⟩
      · obtain ⟨g, hg, hs⟩ := ih old
        exact ⟨g, by omega, hs⟩
      · exact ⟨n, by omega, fresh⟩
  exact h _ hit

/-- Returned packed payloads have original half-word width. This derives physical readback
input size from actual search provenance, including the empty/miss result. -/
theorem allSearch_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encNatPairOption (allSearch input)).length ≤ 3 * q + 2 := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length + bs.length + cs.length + ds.length
  change (encNatPairOption (allSearch input)).length ≤ 3 * q + 2
  cases h : allSearch input with
  | none => simp
  | some out =>
    obtain ⟨g, hg, hit⟩ := all_sound input out h
    obtain ⟨a, ha, b, hb, _, ho⟩ := search_sound_records input g out hit
    have hg' : g < 2 ^ p := hg
    have size (right : Bool) (r : ℕ × ℕ) (hr : r ∈ ClassBalance.records input right g) :
        (encNat r.2).length ≤ q := by
      have fits := (ClassBalance.records_fit hp as bs cs ds s 0 right (BitVec.ofNat p g) r)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg'] at fits
      have hw := (Nat.size_le.mpr (fits hr).2)
      have hl : (if right then cs.length + ds.length else as.length + bs.length) ≤ q := by
        split <;> dsimp only [q] <;> omega
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using hw.trans hl
    have ha' : a ∈ ClassBalance.records input (ClassBalance.retainRight input g) g := ha
    have sa := size _ a ha'
    have sb := size _ b hb
    simp only [encOption_some, List.length_cons, ho]
    split <;> simp only [length_encPair] <;> omega

/-- Read back original-order prefix and reversed-suffix payloads. -/
def solve (input : ClassBalance.Input) : Option (List Bool) :=
  (allSearch input).map (SortedMeet.decodeWitness (halves input))

private theorem solve_none {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) :
    solve (ProgramGeneration.originalSource p as bs cs ds s 0) = none ↔
      ¬ Solvable ((as ++ bs) ++ (cs ++ ds)) s 0 := by
  rw [solve, Option.map_eq_none_iff, all_none]
  have he : (∀ g < 2 ^ p,
      search (ProgramGeneration.originalSource p as bs cs ds s 0) g = none) ↔
      ∀ g < 2 ^ p, ClassStreaming.search
        ((((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)), (p, g))) =
          none := by
    apply forall_congr'
    intro g
    apply forall_congr'
    intro hg
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg, classInput_original] using
      search_none hp as bs cs ds s (BitVec.ofNat p g)
  exact he.trans ((ClassStreaming.all_none _).symm.trans
    (ClassStreaming.allSearch_none (as ++ bs) (cs ++ ds) s p))

private theorem solve_sound {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (ops : List Bool)
    (hit : solve (ProgramGeneration.originalSource p as bs cs ds s 0) = some ops) :
    ops.length = ((as ++ bs) ++ (cs ++ ds)).length ∧
      eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = 0 := by
  let input := ProgramGeneration.originalSource p as bs cs ds s (0 : BitVec m)
  change (allSearch input).map (SortedMeet.decodeWitness (halves input)) = some ops at hit
  cases h : allSearch input with
  | none => rw [h] at hit; contradiction
  | some out =>
    simp only [h, Option.map_some, Option.some.injEq] at hit
    obtain ⟨g, hg, hs⟩ := all_sound _ out h
    have hg' : g < 2 ^ p := hg
    have hsource := search_sound hp as bs cs ds s (BitVec.ofNat p g) out
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg'] at hsource
    obtain ⟨a, ha, b, hb, hk, ho⟩ := hsource hs
    have haf := (ClassStreaming.allRecords_mem _ _ _).mp
      ((ClassStreaming.mem_records _ _ _).mp ha).1
    have hbf := (ClassStreaming.allRecords_mem _ _ _).mp
      ((ClassStreaming.mem_records _ _ _).mp hb).1
    simp only [classInput_original, Bool.false_eq_true, ite_false, ite_true] at haf hbf
    have hf := (SortedQuarterMachine.correct (as ++ bs) s).2.2 a |>.mp haf
    have hi := (SortedMeet.mem_inverse (cs ++ ds) 0 b).mp hbf
    subst ops
    rw [ho]
    dsimp only [input]
    rw [halves_original]
    constructor
    · simp [SortedMeet.decodeWitness, Nat.add_assoc]
    · simp only [SortedMeet.decodeWitness, List.length_map]
      rw [List.zip_append (by simp :
        (Native.Quarter.decode (as ++ bs).length a.2).length = (as ++ bs).length)]
      apply (eval_append_eq_iff _ _ _ _).mpr
      apply BitVec.eq_of_toNat_eq
      exact hf.2.symm.trans (hk.trans hi.2)

/-- Actual count-only preprocessing precedes class retention/search; no balance advice is input. -/
def run (input : Source.Input) : ℕ × Option (List Bool) :=
  let prepared := Source.prepare input
  (ClassBalance.balance prepared, solve prepared)

/-- Original-input witness/miss correctness, including capped depths, zero width, empty tails
and every fourth-quarter residue. No generated dictionary or execution conclusion is a premise. -/
theorem original_correct {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    let (_, result) := run (Source.ofWords p s tail)
    (result = none ↔ ¬ Solvable tail s 0) ∧
      ∀ ops, result = some ops → ops.length = tail.length ∧ eval (ops.zip tail) s = 0 := by
  have hp : min p (min m (tail.length / 4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have cut := Source.quarters_append tail
  simp only [run, Source.prepare_ofWords]
  constructor
  · rw [solve_none hp, cut]
  · intro ops hit
    simpa only [cut] using solve_sound hp _ _ _ _ s ops hit

/-- The returned prepass value equals the existing computed original-half counter balance.
This derives the connection from actual unique generated class words in both directions. -/
theorem original_balance {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    (run (Source.ofWords p s tail)).1 = (ClassStreaming.run (Source.ofWords p s tail)).1 := by
  have hp : min p (min m (tail.length / 4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  unfold run ClassStreaming.run ClassStreaming.prepare
  rw [Source.prepare_ofWords, SortedMeet.prepare_ofWords]
  exact ClassBalance.balance_eq_counter hp _ _ _ _ s

/-- Every actual count-table prefix from original source input has quarter-scale physical
encoding, including both binary counts and framing. Internal TM temporaries remain charged
separately by the composed machine profile. -/
theorem source_count_prefix_wire {m : ℕ} (p : ℕ) (s : BitVec m)
    (tail : List (BitVec m)) (n : ℕ)
    (hn : n ≤ 2 ^ ClassBalance.depth (Source.prepare (Source.ofWords p s tail))) :
    let input := Source.prepare (Source.ofWords p s tail)
    let k := tail.length / 4
    (encNatPairList (((ClassBalance.countStep input)^[n] (0, [])).2)).length ≤
      2 ^ ClassBalance.depth input * (12 * k + 15) := by
  dsimp only
  rw [Source.prepare_ofWords] at hn ⊢
  have hp : min p (min m (tail.length / 4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have h := ClassBalance.table_prefix_wire hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
    (Source.quarters tail).2.1 (Source.quarters tail).2.2 s n hn
  obtain ⟨ha, hb, hc, hd⟩ := Source.quarters_lengths tail
  have coeff : 4 * ((Source.quarters tail).1.1.length + (Source.quarters tail).1.2.length) +
      2 * ((Source.quarters tail).2.1.length + (Source.quarters tail).2.2.length) + 9 ≤
        12 * (tail.length / 4) + 15 := by
    rw [ha, hb, hc, hd]
    omega
  exact h.trans (Nat.mul_le_mul hn coeff)

/-- Buffer observer of the preserved older `JoinedProbe` component. The installed fallback
uses restarted `ClassBatches` and does not execute this per-pair buffer path. -/
def buffer (input : ClassBalance.Input) (g n : ℕ) : List (ℕ × ℕ) :=
  JoinedProbe.buffer (probeContext input g) g n

/-- The preserved per-pair consumer has this logical prefix bound. It is not the installed
fallback; restarted-batch prefix bounds are provided separately below. -/
theorem buffer_bound (input : ClassBalance.Input) (g n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (buffer input g n).length ≤ ClassBalance.balance input := by
  let right := ClassBalance.retainRight input g
  let cap := ClassBalance.count input right g + 1
  have hv := JoinedProbe.buffer_valid (probeContext input g) g n
    (by dsimp [probeContext, probeTask]; omega)
  have hc : cap = (ClassBalance.retain input g).length + 1 := by
    rw [ClassBalance.retain, ClassBalance.records_length]
  have hb : (buffer input g n).length < cap := hv
  have hl := ClassBalance.class_le_balance input g hg
  omega

/-- Preserved per-pair dictionary/buffer bound, separate from the installed restarted batches. -/
theorem simultaneous_records (input : ClassBalance.Input) (g n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (ClassBalance.retain input g).length + (buffer input g n).length ≤
      2 * ClassBalance.balance input := by
  have hk := ClassBalance.class_le_balance input g hg
  have hb := buffer_bound input g n hg
  omega

/-- Every simultaneously retained/live buffered record has its derived full-state/payload
width. This bounds the preserved older `JoinedProbe` component's dictionary/buffer wire;
internal bit-machine callback tapes remain separately charged by the actual certificate. -/
theorem simultaneous_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (n : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encNatPairList (ClassBalance.retain input g.toNat)).length +
      (encNatPairList (buffer input g.toNat n)).length ≤
        2 * ClassBalance.balance input * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let right := ClassBalance.retainRight input g.toNat
  let q := as.length + bs.length + cs.length + ds.length
  have source (r : ℕ × ℕ) (hr : r ∈ buffer input g.toNat n) :
      r ∈ ClassBalance.records input (!right) g.toNat :=
    JoinedProbe.buffer_mem (probeContext input g.toNat) g.toNat n r hr
  have recordBound (r : ℕ × ℕ) (hr : r ∈ buffer input g.toNat n) :
      (encPair encNat encNat r).length ≤ 2 * m + 1 + q := by
    have hs := source r hr
    obtain ⟨hk, hv⟩ := ClassBalance.records_fit hp as bs cs ds s 0 (!right) g r hs
    have key : (encNat r.1).length ≤ m := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hk
    have value : (encNat r.2).length ≤ q := by
      have hl : (if !right then cs.length + ds.length else as.length + bs.length) ≤ q := by
        split <;> dsimp only [q] <;> omega
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using (Nat.size_le.mpr hv).trans hl
    simp only [length_encPair]
    omega
  have hg : g.toNat < 2 ^ ClassBalance.depth input := g.isLt
  have hb := length_encList_le (encPair encNat encNat) (buffer input g.toNat n) recordBound
  have hlen := buffer_bound input g.toNat n hg
  have hbuffer := hb.trans (Nat.mul_le_mul_right (2 * (2 * m + 1 + q) + 1) hlen)
  have hkept := ClassBalance.retained_prefix_wire hp as bs cs ds s g
    (ClassBalance.retain input g.toNat).length
  change (encNatPairList
    ((ClassBalance.retain input g.toNat).take (ClassBalance.retain input g.toNat).length)).length ≤
      ClassBalance.balance input * (4 * m + 2 * q + 3) at hkept
  rw [List.take_length] at hkept
  have hbuffer' : (encNatPairList (buffer input g.toNat n)).length ≤
      ClassBalance.balance input * (4 * m + 2 * q + 3) := hbuffer.trans_eq (by ring)
  exact (Nat.add_le_add hkept hbuffer').trans_eq (by ring)

/-- Actual direct-branch dictionary/opposite prefix encodings fit quarter-plus-balance
record space at every logical output prefix. Matcher/producer internal tapes remain separate. -/
theorem direct_prefix_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (n : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encNatPairList (ClassBalance.retain input g.toNat)).length +
      (encNatPairList (directPrefix input g.toNat n)).length ≤
        (2 * ClassBalance.balance input + quarterBudget input) * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let right := ClassBalance.retainRight input g.toNat
  let q := as.length + bs.length + cs.length + ds.length
  have kept := ClassBalance.records_prefix_wire hp as bs cs ds s right g
    (ClassBalance.retain input g.toNat).length
  dsimp only [right] at kept
  rw [← ClassBalance.retain] at kept
  rw [List.take_length] at kept
  have opposite : (encNatPairList (directPrefix input g.toNat n)).length ≤
      (directPrefix input g.toNat n).length * (4 * m + 2 * q + 3) := by
    by_cases h : materialize input g.toNat = true
    · simpa only [directPrefix, h, ite_true] using
        ClassBalance.records_prefix_wire hp as bs cs ds s (!right) g n
    · simp [directPrefix, h]
  have records := direct_prefix_records input g.toNat n g.isLt
  have joined := Nat.add_le_add kept opposite
  rw [← Nat.add_mul] at joined
  exact joined.trans (Nat.mul_le_mul_right _ records)

/-- Physical dictionary and restarted output-prefix wire for original inputs. Internal
producer/matcher tapes remain included in the actual certificate's separate prefix-space profile. -/
theorem restart_prefix_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (i n : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encNatPairList (ClassBalance.retain input g.toNat)).length +
      (encNatPairList
        ((ClassBatches.batch (probeContext input g.toNat) g.toNat i).take n)).length ≤
          (2 * ClassBalance.balance input + 2 * quarterBudget input + 1) * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let context := probeContext input g.toNat
  let q := as.length + bs.length + cs.length + ds.length
  let batch := (ClassBatches.batch context g.toNat i).take n
  have row (r : ℕ × ℕ) (hr : r ∈ batch) : (encPair encNat encNat r).length ≤ 2*m+1+q := by
    have original := ClassBatches.batch_sound context g.toNat i r (List.mem_of_mem_take hr)
    exact ClassBalance.record_wire hp as bs cs ds s _ g r original
  have output := length_encList_le (encPair encNat encNat) batch row
  have kept := ClassBalance.records_prefix_wire hp as bs cs ds s
    (ClassBalance.retainRight input g.toNat) g (ClassBalance.retain input g.toNat).length
  change (encNatPairList
    ((ClassBalance.retain input g.toNat).take (ClassBalance.retain input g.toNat).length)).length ≤
      ((ClassBalance.retain input g.toNat).take (ClassBalance.retain input g.toNat).length).length *
        (4*m+2*q+3) at kept
  rw [List.take_length] at kept
  have records := restart_prefix_records input g.toNat i n g.isLt
  have joined := Nat.add_le_add kept output
  have outputFactor : 2 * (2*m+1+q)+1 = 4*m+2*q+3 := by ring
  rw [outputFactor, ← Nat.add_mul] at joined
  exact joined.trans (Nat.mul_le_mul_right _ records)

/-- Reread volume for the preserved older per-pair consumer, including its final partial batch.
The installed fallback uses `ClassBatches` instead. This is a record-volume charge only. -/
theorem probe_recordWork (input : ClassBalance.Input) (g : ℕ) (rows : List (ℕ × ℕ)) :
    let task := probeTask input g
    let parameter := BatchedAccess.parameters task
    let capacity := (ClassBalance.retain input g).length + 1
    BatchedAccess.recordWork parameter capacity ((0, []), none) rows ≤ 4 * rows.length := by
  dsimp only
  apply BatchedAccess.recordWork_bound _ _ rows (by omega)
  dsimp only [BatchedAccess.parameters, probeTask]
  omega

private abbrev classEncoding := encPair ClassBalance.encoding encNat
private abbrev recEncoding := encPair encNat encNat
private abbrev stateEncoding := encPair encNat (encOption recEncoding)

private theorem halves_polyTime : ComputableInPolyTime halves ClassBalance.encoding
    SortedMeet.encoding := by
  have width : ComputableInPolyTime (fun x : ClassBalance.Input => x.1.1.1)
      ClassBalance.encoding encUnary := by dsimp only [ClassBalance.encoding]; fun_prop
  have seed : ComputableInPolyTime (fun x : ClassBalance.Input => x.1.2.1)
      ClassBalance.encoding encNat := by dsimp only [ClassBalance.encoding]; fun_prop
  have first : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.1.1)
      ClassBalance.encoding (encList encNat) := by dsimp only [ClassBalance.encoding]; fun_prop
  have second : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.1.2)
      ClassBalance.encoding (encList encNat) := by dsimp only [ClassBalance.encoding]; fun_prop
  have third : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.2.1)
      ClassBalance.encoding (encList encNat) := by dsimp only [ClassBalance.encoding]; fun_prop
  have fourth : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.2.2)
      ClassBalance.encoding (encList encNat) := by dsimp only [ClassBalance.encoding]; fun_prop
  have append := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listAppend encNat)
  exact ((width.prod seed).prod ((append.comp (first.prod second)).prod
    (append.comp (third.prod fourth)))).of_enc_eq (fun _ => rfl)

private theorem classInput_polyTime : ComputableInPolyTime
    (fun q : ClassBalance.Input × ℕ => classInput q.1 q.2)
    classEncoding ClassStreaming.encoding := by
  have original := ComputableInPolyTime.fst ClassBalance.encoding encNat
  exact ((halves_polyTime.comp original).prod
    ((ClassBalance.depth_polyTime.comp original).prod
      (ComputableInPolyTime.snd ClassBalance.encoding encNat))).of_enc_eq (fun _ => rfl)

/-- Actual smaller-class generation and restarted row-window matching. Quarter rescans,
per-batch parameter copies, full-state reconstruction and matcher temporaries are charged. -/
private noncomputable def batchSearchCertificate : NativeCertificate
    (fun q : ClassBalance.Input × ℕ => ClassBatches.run (probeContext q.1 q.2) q.2)
    (encPair ClassBalance.encoding encNat) encNatPairOption := by
  let original : NativeCertificate (id : ClassBalance.Input × ℕ → _)
      classEncoding classEncoding := .linear (.of_eq (fun _ => rfl))
  let orientation := ClassBalance.orientationCertificate
  let streamed := NativeCertificate.ofPolyTime classInput_polyTime
  let kept := ClassBalance.retainCertificate
  let selected := (original.fst.prod orientation).prod original.snd
  let counts := ClassBalance.countCertificate.comp selected
  have increment : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let capacity := (NativeCertificate.ofPolyTime increment).comp counts
  let task := ((streamed.prod orientation).prod kept).prod capacity
  let packed := original.fst.prod task
  let pe := encPair ClassBalance.encoding BatchedAccess.taskEncoding
  let raw : NativeCertificate (id : ClassBalance.Input × BatchedAccess.Task → _) pe pe :=
    .linear (.of_eq (fun _ => rfl))
  have negation : ComputableInPolyTime Bool.not encBool encBool := by fun_prop
  let opposite := (NativeCertificate.ofPolyTime negation).comp raw.snd.fst.fst.snd
  let parameter := BatchedAccess.parametersCertificate.comp raw.snd
  let context := (raw.fst.prod opposite).prod (parameter.prod raw.snd.snd)
  let prepared := context.comp packed
  exact NativeCertificate.congr (ClassBatches.runCertificate.comp
    (prepared.prod original.snd)) (fun _ => rfl)

private theorem quarterBudget_polyTime : ComputableInPolyTime quarterBudget
    ClassBalance.encoding encNat := by
  have a : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.1.1.length)
      ClassBalance.encoding encUnary := by dsimp only [ClassBalance.encoding,
        ProgramGeneration.sourceEncoding]; fun_prop
  have b : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.1.2.length)
      ClassBalance.encoding encUnary := by dsimp only [ClassBalance.encoding,
        ProgramGeneration.sourceEncoding]; fun_prop
  have c : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.2.1.length)
      ClassBalance.encoding encUnary := by dsimp only [ClassBalance.encoding,
        ProgramGeneration.sourceEncoding]; fun_prop
  have d : ComputableInPolyTime (fun x : ClassBalance.Input => x.2.2.2.length)
      ClassBalance.encoding encUnary := by dsimp only [ClassBalance.encoding,
        ProgramGeneration.sourceEncoding]; fun_prop
  have aa := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const 2) a
  have bb := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const 2) b
  have cc := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const 2) c
  have dd := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const 2) d
  have add : ComputableInPolyTime (fun q : ℕ × ℕ => q.1 + q.2) recEncoding encNat := by
    fun_prop
  exact (add.comp ((add.comp ((add.comp (aa.prod bb)).prod cc)).prod dd)).of_enc_eq
    (fun _ => rfl)

private noncomputable def materializeCertificate : NativeCertificate
    (fun q : ClassBalance.Input × ℕ => materialize q.1 q.2) classEncoding encBool := by
  let original : NativeCertificate (id : ClassBalance.Input × ℕ → _) classEncoding classEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let right := ClassBalance.orientationCertificate
  let selected := (original.fst.prod right).prod original.snd
  let small := ClassBalance.countCertificate.comp selected
  have neg : ComputableInPolyTime Bool.not encBool encBool := by fun_prop
  let opposite := (original.fst.prod ((NativeCertificate.ofPolyTime neg).comp right)).prod
    original.snd
  let large := ClassBalance.countCertificate.comp opposite
  let budget := (NativeCertificate.ofPolyTime quarterBudget_polyTime).comp original.fst
  have test : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => decide (0 < q.1.1 ∧ q.1.2 ≤ q.1.1 + q.2))
      (encPair recEncoding encNat) encBool := by
    have positive : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => decide (0 < q.1.1))
        (encPair recEncoding encNat) encBool := by
      apply ComputableInPolyTime.of_tidy
      apply ComputableTidilyInPolyTime.binary_lt' <;> fun_prop
    have bounded : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ => decide (q.1.2 ≤ q.1.1 + q.2))
        (encPair recEncoding encNat) encBool := by
      apply ComputableInPolyTime.of_tidy
      apply ComputableTidilyInPolyTime.binary_le' <;> fun_prop
    exact ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bool_and).comp
      (positive.prod bounded)).of_enc_eq (fun q => by simp)
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime test).comp
    ((small.prod large).prod budget)) (fun _ => rfl)

private noncomputable def directSearchCertificate : NativeCertificate
    (fun q : ClassBalance.Input × ℕ => directSearch q.1 q.2) classEncoding
    (encOption recEncoding) := by
  let original : NativeCertificate (id : ClassBalance.Input × ℕ → _) classEncoding classEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let right := ClassBalance.orientationCertificate
  let kept := ClassBalance.retainCertificate
  let parameter := original.fst.fst.fst.fst.prod (right.prod kept)
  have neg : ComputableInPolyTime Bool.not encBool encBool := by fun_prop
  let opposite := (original.fst.prod ((NativeCertificate.ofPolyTime neg).comp right)).prod
    original.snd
  let generated := ClassBalance.recordsCertificate.comp opposite
  exact NativeCertificate.congr (BatchedAccess.matchCertificate.comp
    (parameter.prod generated)) (fun _ => rfl)

/-- One count-selected uniform machine uses a single match for a class that fits the
quarter-plus-retained allowance, and the bounded restarted-window machine otherwise.
All count, materialization, matching, copy and callback temporaries remain charged. -/
noncomputable def searchCertificate : NativeCertificate
    (fun q : ClassBalance.Input × ℕ => search q.1 q.2)
    (encPair ClassBalance.encoding encNat) encNatPairOption :=
  NativeCertificate.congr (NativeCertificate.branch materializeCertificate
    directSearchCertificate batchSearchCertificate) (fun _ => rfl)

private noncomputable def allStepCertificate : NativeCertificate
    (fun q : ClassBalance.Input × (ℕ × Option (ℕ × ℕ)) => allStep q.1 q.2)
    (encPair ClassBalance.encoding stateEncoding) stateEncoding := by
  let e := encPair ClassBalance.encoding stateEncoding
  let original : NativeCertificate (id : ClassBalance.Input × (ℕ × Option (ℕ × ℕ)) → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let found := original.snd.snd
  let fresh := searchCertificate.comp (original.fst.prod original.snd.fst)
  let yes : NativeCertificate
      (fun q : (ClassBalance.Input × (ℕ × Option (ℕ × ℕ))) × (ℕ × ℕ) => some q.2)
      (encPair e recEncoding) (encOption recEncoding) :=
    ((NativeCertificate.linear (.of_eq (fun _ => rfl))).snd).some
  let chosen := found.option fresh yes
  have increment : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let next := (NativeCertificate.ofPolyTime increment).comp original.snd.fst
  exact NativeCertificate.congr (next.prod chosen) (fun q => by
    dsimp only [allStep, id_eq, Function.comp_def]
    cases q.2.2 <;> rfl)

/-- A fixed uniform streaming loop consumes actually generated class-index data. Time sums
executed class rounds; peak workspace takes their actual prefix maximum and includes the index
list/setup, state copies and final readback. No maximum-class-time multiplication is used. -/
noncomputable def allCertificate : NativeCertificate allSearch ClassBalance.encoding
    encNatPairOption := by
  let e := encPair (encPair ClassBalance.encoding (encOption recEncoding)) encNat
  let original : NativeCertificate
      (id : (ClassBalance.Input × Option (ℕ × ℕ)) × ℕ → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let round := NativeCertificate.congr ((allStepCertificate.comp
    (original.fst.fst.prod (original.snd.prod original.fst.snd))).snd) (fun _ => rfl)
  let loop := NativeCertificate.foldlStream ClassBalance.encoding (encOption recEncoding) encNat
    (fun input found g => found.orElse (fun _ => search input g)) round
  let generation := (Classical.choose_spec SortedQuarterMachine.indices_computable).2.2
  let generated : NativeCertificate SortedQuarterMachine.indices encUnary (encList encNat) :=
    ⟨_, _, generation⟩
  let indices := generated.comp (NativeCertificate.ofPolyTime ClassBalance.depth_polyTime)
  let input : NativeCertificate (id : ClassBalance.Input → _)
      ClassBalance.encoding ClassBalance.encoding := .linear (.of_eq (fun _ => rfl))
  let initial : NativeCertificate (fun _ : ClassBalance.Input => (none : Option (ℕ × ℕ)))
      ClassBalance.encoding (encOption recEncoding) := .const _
  exact NativeCertificate.congr (loop.comp (input.prod (initial.prod indices))) (fun source => by
    simp only [Function.comp_def, id_eq, SortedQuarterMachine.indices_eq_range]
    exact (allSearch_eq_fold source).symm)

/-- Actual construction of the original halves for decoding; all array copying is charged. -/
noncomputable def halvesCertificate : NativeCertificate halves ClassBalance.encoding
    SortedMeet.encoding := .ofPolyTime halves_polyTime

/-- The actual packed-witness decoder used by the assembled source solver. -/
noncomputable def readbackCertificate : NativeCertificate
    (fun q : SortedMeet.Input × Option (ℕ × ℕ) => q.2.map (SortedMeet.decodeWitness q.1))
    (encPair SortedMeet.encoding encNatPairOption) (encOption encBits) :=
  .ofPolyTime SortedMeet.readback_polyTime

/-- Preparation, half-array construction and final decoding cost only a polynomial
in the physical original input
encoding. The decoder is evaluated on the actual searched witness; no witness-size premise
is supplied. These bounds do not include the search or balance prepass. -/
theorem preparation_readback_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      let result := allSearch prepared
      let input := (halves prepared, result)
      let size := (Source.encoding original).length
      Source.prepareCertificate.time original + halvesCertificate.time prepared +
        readbackCertificate.time input ≤ P size ∧
      Source.prepareCertificate.space original + halvesCertificate.space prepared +
        readbackCertificate.space input ≤ P size := by
  have halfPoly : halvesCertificate.IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial halves_polyTime
  have prepPoly : Source.prepareCertificate.IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial Source.prepare_polyTime
  have combined := halvesCertificate.comp_isPolynomial Source.prepareCertificate halfPoly prepPoly
  obtain ⟨A, hA, monoA, boundA⟩ := exists_mono_poly (combined.1.add combined.2)
  obtain ⟨B, hB, monoB, boundB⟩ := exists_mono_poly
    (halves_polyTime.comp Source.prepare_polyTime).polyBounded_length
  obtain ⟨D, hD, monoD, boundD⟩ := exists_mono_poly_cert SortedMeet.readback_polyTime
  let P := fun n => A n + D (2 * B n + 3 * n + 3)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro x y hxy
    exact Nat.add_le_add (monoA hxy) (monoD (by have := monoB hxy; omega))
  · intro m p s tail
    let original := Source.ofWords p s tail
    let prepared := Source.prepare original
    let size := (Source.encoding original).length
    have hp : min p (min m (tail.length / 4)) ≤ m :=
      (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    have hw := allSearch_wire hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
      (Source.quarters tail).2.1 (Source.quarters tail).2.2 s
    have cut := congrArg List.length (Source.quarters_append tail)
    simp only [List.length_append] at cut
    rw [← Source.prepare_ofWords] at hw
    have tailSize : tail.length ≤ size := by
      have hl := length_le_length_encList (enc := encNat) ((s :: tail).map BitVec.toNat)
      simp only [List.length_map, List.length_cons] at hl
      dsimp only [size, original, Source.ofWords, Source.encoding]
      simp only [length_encPair]
      omega
    have witnessSize : (encNatPairOption (allSearch prepared)).length ≤
        3 * size + 2 := by dsimp only [prepared, original]; omega
    have halfSize : (SortedMeet.encoding (halves prepared)).length ≤ B size := boundB original
    have inputSize : (encPair SortedMeet.encoding encNatPairOption
        (halves prepared, allSearch prepared)).length ≤ 2 * B size + 3 * size + 3 := by
      simp only [length_encPair]
      omega
    have decoded := boundD (halves prepared, allSearch prepared)
    have da := (decoded.1.trans (monoD inputSize))
    have db := (decoded.2.trans (monoD inputSize))
    have before := boundA original
    change (Source.prepareCertificate.time original + halvesCertificate.time prepared) +
      (Source.prepareCertificate.space original + halvesCertificate.space prepared) ≤
        A size at before
    have aa : Source.prepareCertificate.time original + halvesCertificate.time prepared ≤
        A size :=
      (Nat.le_add_right _ _).trans before
    have ab : Source.prepareCertificate.space original + halvesCertificate.space prepared ≤
        A size :=
      (Nat.le_add_left _ _).trans before
    exact ⟨Nat.add_le_add aa da, Nat.add_le_add ab db⟩

private noncomputable def solveCertificate : NativeCertificate solve ClassBalance.encoding
    (encOption encBits) := by
  let original : NativeCertificate (id : ClassBalance.Input → _)
      ClassBalance.encoding ClassBalance.encoding := .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (readbackCertificate.comp
    (halvesCertificate.prod allCertificate)) (fun _ => rfl)

/-- One uniform original-input bit execution computes both counts/balance, generated smaller
classes, restarted opposite windows, outer control and decoded output. Charged profiles include
per-batch copying, internal callbacks, preprocessing and control.
Sharp global resources remain open. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding
    (encPair encNat (encOption encBits)) :=
  NativeCertificate.congr ((ClassBalance.balanceCertificate.prod solveCertificate).comp
    Source.prepareCertificate) (fun _ => rfl)

end Cslib.Cryptanalysis.AddXNOR.JoinedDissection
