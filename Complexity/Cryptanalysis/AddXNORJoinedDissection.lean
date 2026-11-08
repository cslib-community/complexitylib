/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORClassBalance
public import Complexity.Cryptanalysis.AddXNORBatchedAccess
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
Its generated full-state class feeds the existing bounded-batch opposite-side
counter probe, then the fixed outer class counter releases it. The source
frontend computes the cut, capped projection depth, first-operand seed and zero
target. Count-only balance preprocessing and original witness readback are
included in the uniform bit execution.

This assembles the class producer with an executable search endpoint for
[WangLvShenZhang2027], Lemma 8/Theorem 7, pp. 21–22. The opposite producer still
scans half words per class; grouped consumers and retained-state copying retain
their charged overhead. Logical retained/batch occupancy does not imply sharp
internal TM workspace. Sharp global bit resources remain open.

## Main definitions

* `search`, `allSearch`: generated retention and fixed-counter batch probing/release.
* `run`: original-input preprocessing, computed balance, search and witness readback.

## Main results

* `original_correct`, `original_balance`: original witness/miss and exact computed balance.
* `source_count_prefix_wire`, `simultaneous_wire`: physical logical-prefix storage bounds.
* `sourceCertificate`: actual uniform bit execution, with scan/copying costs retained.
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

/-- Generated class retention feeds the actual uniform bounded-batch counter probe. -/
def search (input : ClassBalance.Input) (g : ℕ) : Option (ℕ × ℕ) :=
  BatchedAccess.probe (probeTask input g)

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
  have h := ClassBalance.records_mem_counter hp as bs cs ds s
    (ClassBalance.retainRight (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat) g r
  dsimp only at h
  simpa only [classInput_original] using h

private theorem probe_fits {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let right := ClassBalance.retainRight input g.toNat
    ∀ r ∈ ClassBalance.retain input g.toNat ++
      ClassStreaming.records (classInput input g.toNat) (!right)
        (ClassStreaming.limit (classInput input g.toNat) (!right)), r.1 < 2 ^ m := by
  dsimp only
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [ClassBalance.retain] at hr
    exact (ClassBalance.records_fit hp as bs cs ds s 0 _ g r hr).1
  · rw [classInput_original] at hr
    exact (ClassStreaming.records_fit (as ++ bs) (cs ++ ds) s p g.toNat _ r hr).1

/-- The generated retained dictionary gives exactly the original selected-class miss semantics,
independently of how its computed orientation differs from the old counter orientation. -/
theorem search_none {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    search input g.toNat = none ↔ ClassStreaming.search (classInput input g.toNat) = none := by
  dsimp only
  rw [search, probeTask]
  have hm := BatchedAccess.probe_none
    (probeTask (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat)
    (probe_fits hp as bs cs ds s g)
  dsimp only [probeTask] at hm
  rw [hm, ClassStreaming.search_none]
  have hkept (r : ℕ × ℕ) := kept_mem hp as bs cs ds s g r
  dsimp only at hkept
  simp only [BatchedAccess.Meets, hkept]
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
  have h := BatchedAccess.probe_sound _ out hit
  dsimp only [probeTask] at h
  obtain ⟨a, ha, b, hb, hk, ho⟩ := h
  have hkept := kept_mem hp as bs cs ds s g a
  dsimp only at hkept
  rw [hkept] at ha
  cases h : ClassBalance.retainRight (ProgramGeneration.originalSource p as bs cs ds s 0) g.toNat
  · exact ⟨a, by simpa only [h] using ha, b, by simpa only [h, Bool.not_false] using hb,
      hk, by simpa only [h, Bool.false_eq_true, ite_false] using ho⟩
  · exact ⟨b, by simpa only [h, Bool.not_true] using hb, a, by simpa only [h] using ha,
      hk.symm, by simpa only [h, ite_true] using ho⟩

/-- Each class releases its retained dictionary and live batch; only a found pair survives. -/
def allStep (input : ClassBalance.Input) (state : ℕ × Option (ℕ × ℕ)) :
    ℕ × Option (ℕ × ℕ) :=
  let (g, found) := state
  (g + 1, found.orElse (fun _ => search input g))

/-- Fixed-size runtime outer class counter, including early-hit parking. -/
def allSearch (input : ClassBalance.Input) : Option (ℕ × ℕ) :=
  ((allStep input)^[2 ^ ClassBalance.depth input] (0, none)).2

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

/-- Actual live buffer after a prefix of the opposite packed-counter program. -/
def buffer (input : ClassBalance.Input) (g n : ℕ) : List (ℕ × ℕ) :=
  let task := probeTask input g
  let (_, ((_, batch), _)) := (BatchedAccess.probeStep task)^[n] (0, ((0, []), none))
  batch

/-- Every live probe buffer is bounded by the computed smaller-class maximum. This derives
capacity from generated counts; it does not identify record occupancy with auxiliary TM space. -/
theorem buffer_bound (input : ClassBalance.Input) (g n : ℕ)
    (hg : g < 2 ^ ClassBalance.depth input) :
    (buffer input g n).length ≤ ClassBalance.balance input := by
  let task := probeTask input g
  let right := ClassBalance.retainRight input g
  let cap := ClassBalance.count input right g + 1
  let rows := ClassStreaming.records (classInput input g) (!right) n
  have hv := BatchedAccess.fold_valid (BatchedAccess.parameters task) cap rows
    (by dsimp [cap]; omega)
  have hc : cap = (ClassBalance.retain input g).length + 1 := by
    rw [ClassBalance.retain, ClassBalance.records_length]
  have hb : (buffer input g n).length < cap := by
    rw [buffer, BatchedAccess.probe_prefix]
    dsimp only
    exact hv.1 ▸ hv.2
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
    (s : BitVec m) (g : BitVec p) (n : ℕ)
    (hn : let input := ProgramGeneration.originalSource p as bs cs ds s 0
      n ≤ ClassStreaming.limit (classInput input g.toNat)
        (!ClassBalance.retainRight input g.toNat)) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encList (encPair encNat encNat) (ClassBalance.retain input g.toNat)).length +
      (encList (encPair encNat encNat) (buffer input g.toNat n)).length ≤
        2 * ClassBalance.balance input * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let task := probeTask input g.toNat
  let right := ClassBalance.retainRight input g.toNat
  let rows := ClassStreaming.records (classInput input g.toNat) (!right) n
  let q := as.length + bs.length + cs.length + ds.length
  have source (r : ℕ × ℕ) (hr : r ∈ buffer input g.toNat n) :
      r ∈ ClassStreaming.records (classInput input g.toNat) (!right)
        (ClassStreaming.limit (classInput input g.toNat) (!right)) := by
    rw [buffer, BatchedAccess.probe_prefix] at hr
    dsimp only at hr
    have hm := BatchedAccess.buffer_mem (BatchedAccess.parameters task)
      (ClassBalance.count input right g.toNat + 1) rows r hr
    have sub := ((List.range_sublist.mpr hn).filter
      (ClassStreaming.accepts (classInput input g.toNat) (!right))).map
        (ClassStreaming.row (classInput input g.toNat) (!right))
    exact sub.subset hm
  have recordBound (r : ℕ × ℕ) (hr : r ∈ buffer input g.toNat n) :
      (encPair encNat encNat r).length ≤ 2 * m + 1 + q := by
    have hs := source r hr
    dsimp only [input] at hs
    rw [classInput_original] at hs
    obtain ⟨hk, hv⟩ := ClassStreaming.records_fit (as ++ bs) (cs ++ ds) s p g.toNat _ r hs
    have key : (encNat r.1).length ≤ m := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hk
    have value : (encNat r.2).length ≤ q := by
      have hl : (if !right then (cs ++ ds).length else (as ++ bs).length) ≤ q := by
        split <;> simp only [List.length_append] <;> dsimp only [q] <;> omega
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

/-- Actual smaller-class generation, count-selected capacity and the existing batch probe,
including the old opposite half scans and captured retained-state copying costs. -/
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
  exact NativeCertificate.congr (BatchedAccess.probeCertificate.comp task) (fun _ => rfl)

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

/-- Fixed outer class execution releases class buffers between rounds. All machine temporaries,
counters and copied states are present in the actual time/prefix-peak space profile. -/
noncomputable def allCertificate : NativeCertificate allSearch ClassBalance.encoding
    (encOption (encPair encNat encNat)) := by
  have clock : ComputableInPolyTime (fun input : ClassBalance.Input =>
      2 ^ ClassBalance.depth input) ClassBalance.encoding encNat :=
    ComputableInPolyTime.binary_pow' (.const 2) ClassBalance.depth_polyTime
  exact ClassStreaming.loopCertificate ClassBalance.encoding (encOption recEncoding)
    _ allStep none clock allStepCertificate

private noncomputable def solveCertificate : NativeCertificate solve ClassBalance.encoding
    (encOption encBits) := by
  let original : NativeCertificate (id : ClassBalance.Input → _)
      ClassBalance.encoding ClassBalance.encoding := .linear (.of_eq (fun _ => rfl))
  let half := (NativeCertificate.ofPolyTime halves_polyTime)
  let readback := NativeCertificate.ofPolyTime SortedMeet.readback_polyTime
  exact NativeCertificate.congr (readback.comp (half.prod allCertificate)) (fun _ => rfl)

/-- One uniform original-input bit execution computes both counts/balance, generated smaller
classes, batch probes, outer control and decoded output. Its charged profiles retain every old
scan/copying and grouped-volume polynomial cost; no sharp source resource claim is made. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding
    (encPair encNat (encOption encBits)) :=
  NativeCertificate.congr ((ClassBalance.balanceCertificate.prod solveCertificate).comp
    (NativeCertificate.ofPolyTime Source.prepare_polyTime)) (fun _ => rfl)

end Cslib.Cryptanalysis.AddXNOR.JoinedDissection
