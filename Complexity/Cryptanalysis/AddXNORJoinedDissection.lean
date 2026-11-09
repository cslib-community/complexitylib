/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORClassBalance
public import Complexity.Cryptanalysis.AddXNORBatchedAccess
public import Complexity.Cryptanalysis.AddXNORJoinedProbe
import all Complexity.Cryptanalysis.AddXNORJoinedProbe
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Computability.GenericRAM.Native.Combinators

/-!
# Original-input dissection with generated class retention

Actual forward/backward quarter-query counts determine the retained side.
Its generated full-state class feeds a nested opposite-quarter join consumer and
bounded-batch matcher, then the fixed outer class counter releases it. The source
frontend computes the cut, capped projection depth, first-operand seed and zero
target. Count-only balance preprocessing and original witness readback are
included in the uniform bit execution.

This assembles the class producer with an executable search endpoint for
[WangLvShenZhang2027], Lemma 8/Theorem 7, pp. 21–22. No opposite half-space scan
or complete opposite-class list is executed. Quarter-list replay, captured-state
copying and preprocessing/control retain their charged overhead. Logical retained/
batch occupancy does not imply sharp
internal TM workspace. Sharp global bit resources remain open.

## Main definitions

* `search`, `allSearch`: generated retention, opposite-quarter consumption and class release.
* `run`: original-input preprocessing, computed balance, search and witness readback.

## Main results

* `original_correct`, `original_balance`: original witness/miss and exact computed balance.
* `source_count_prefix_wire`, `simultaneous_wire`: physical logical-prefix storage bounds.
* `sum_pairVisits`: total generated pair visits are bounded by the two half populations.
* `allSearch_eq_fold`: the fixed counter agrees with actual class-index streaming.
* `sourceCertificate`: actual uniform bit execution, with captured-state copying costs retained.
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

/-- Generated quarter matches feed bounded batches without an opposite half-space scan. -/
def search (input : ClassBalance.Input) (g : ℕ) : Option (ℕ × ℕ) :=
  JoinedProbe.run (probeContext input g) g

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
  rw [search]
  have hm := JoinedProbe.run_none
    (probeContext (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat) g.toNat
    (probe_fits hp as bs cs ds s g)
  dsimp only [probeContext, probeTask, BatchedAccess.parameters] at hm ⊢
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
  have h := JoinedProbe.run_sound
    (probeContext (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat) g.toNat out hit
  dsimp only [probeContext, probeTask, BatchedAccess.parameters] at h
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

/-- Matching-quarter iteration slots in one actually generated opposite class. -/
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

/-- Across all classes, the generated opposite traversal has at most the two actual half-space
populations in total. This removes the repeated half scans; copying/bit costs remain separate. -/
theorem sum_pairVisits {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (∑ g : BitVec p, pairVisits input g.toNat) ≤
      2 ^ (as.length + bs.length) + 2 ^ (cs.length + ds.length) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have counts (right : Bool) :
      (∑ g : BitVec p, ClassBalance.count input right g.toNat) =
        2 ^ (if right then cs.length+ds.length else as.length+bs.length) := by
    have h := counter_sum ((m, s.toNat),
      ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)) p right
    have hc (g : BitVec p) := ClassBalance.count_eq_counter hp as bs cs ds s right g
    dsimp only at hc
    dsimp only [input]
    simp_rw [hc]
    rw [h]
    cases right <;>
      simp [ClassStreaming.limit, ClassStreaming.sideInput, SortedMeet.inverseInput, Nat.add_comm]
  have bound (g : BitVec p) : pairVisits input g.toNat ≤
      ClassBalance.count input false g.toNat + ClassBalance.count input true g.toNat := by
    have hv := JoinedProbe.visits_le_count (probeContext input g.toNat) g.toNat
    change pairVisits input g.toNat ≤ _ at hv
    cases h : ClassBalance.retainRight input g.toNat <;>
      simp only [h, Bool.not_true, Bool.not_false] at hv <;> omega
  have h := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => bound g)
  rw [Finset.sum_add_distrib, counts false, counts true] at h
  exact h

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
    (encList (encPair encNat encNat) (((ClassBalance.countStep input)^[n] (0, [])).2)).length ≤
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

/-- Actual live batch after a prefix of generated opposite-class matches. -/
def buffer (input : ClassBalance.Input) (g n : ℕ) : List (ℕ × ℕ) :=
  JoinedProbe.buffer (probeContext input g) g n

/-- Every generated-record prefix is bounded by computed balance. The auxiliary tapes of the
actual nested-fold machine remain charged separately. -/
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

/-- Retained dictionary and live opposite buffer coexist within twice the actual computed
balance in record count, at every logical probing prefix. Other tapes remain separately charged. -/
theorem simultaneous_records (input : ClassBalance.Input) (g n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (ClassBalance.retain input g).length + (buffer input g n).length ≤
      2 * ClassBalance.balance input := by
  have hk := ClassBalance.class_le_balance input g hg
  have hb := buffer_bound input g n hg
  omega

/-- Every simultaneously retained/live buffered record has its derived full-state/payload
width. This bounds physical dictionary/buffer encodings at every executed logical prefix;
internal bit-machine callback tapes remain separately charged by the actual certificate. -/
theorem simultaneous_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (n : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encList (encPair encNat encNat) (ClassBalance.retain input g.toNat)).length +
      (encList (encPair encNat encNat) (buffer input g.toNat n)).length ≤
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
  change (encList (encPair encNat encNat)
    ((ClassBalance.retain input g.toNat).take (ClassBalance.retain input g.toNat).length)).length ≤
      ClassBalance.balance input * (4 * m + 2 * q + 3) at hkept
  rw [List.take_length] at hkept
  have hbuffer' : (encList (encPair encNat encNat) (buffer input g.toNat n)).length ≤
      ClassBalance.balance input * (4 * m + 2 * q + 3) := hbuffer.trans_eq (by ring)
  exact (Nat.add_le_add hkept hbuffer').trans_eq (by ring)

/-- The generated retained population also pays the batch reread volume, including the final
partial batch. This is a record-volume charge, not a bit-time or auxiliary-space theorem. -/
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

/-- Actual smaller-class generation and nested generated-match probing. All quarter/list
replay, captured-state copying and batch matching costs remain in the bit profile. -/
noncomputable def searchCertificate : NativeCertificate
    (fun q : ClassBalance.Input × ℕ => search q.1 q.2)
    (encPair ClassBalance.encoding encNat) (encOption (encPair encNat encNat)) := by
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
  exact NativeCertificate.congr (JoinedProbe.runCertificate.comp
    (prepared.prod original.snd)) (fun _ => rfl)

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
    (encOption (encPair encNat encNat)) := by
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

private noncomputable def solveCertificate : NativeCertificate solve ClassBalance.encoding
    (encOption encBits) := by
  let original : NativeCertificate (id : ClassBalance.Input → _)
      ClassBalance.encoding ClassBalance.encoding := .linear (.of_eq (fun _ => rfl))
  let half := (NativeCertificate.ofPolyTime halves_polyTime)
  let readback := NativeCertificate.ofPolyTime SortedMeet.readback_polyTime
  exact NativeCertificate.congr (readback.comp (half.prod allCertificate)) (fun _ => rfl)

/-- One uniform original-input bit execution computes both counts/balance, generated smaller
classes, generated opposite streams, outer control and decoded output. Charged profiles include
captured-state copying, preprocessing and control. Sharp global resources remain open. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding
    (encPair encNat (encOption encBits)) :=
  NativeCertificate.congr ((ClassBalance.balanceCertificate.prod solveCertificate).comp
    (NativeCertificate.ofPolyTime Source.prepare_polyTime)) (fun _ => rfl)

end Cslib.Cryptanalysis.AddXNOR.JoinedDissection
