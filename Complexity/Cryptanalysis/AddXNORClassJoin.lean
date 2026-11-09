/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORGroupedQuarter
public import Complexity.Cryptanalysis.AddXNORSortedMeet
public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyCount
import all Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSourceQuarter
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Actual quarter-query class joins and occurrence counts

Generate the forward first quarter and the genuinely inverse second-quarter
queries, tag, radix sort, and feed the one-pass equal-key writer. All witness
pairs come from these generated groups. A separate count pass sums the products
of opposite-side group populations without enumerating half words or emitting
pairs. Reversing inverse-quarter payloads restores original operator order.

This implements the class-join semantics in [WangLvShenZhang2027], Lemma 8,
PDF pp. 21–22. The source-input preparation computes the cut, projection and
zero-target conventions. Counts now consume sorted tagged records directly with
near-linear bit time and logarithmic counters, bypassing grouped materialization.
The join emitter still pays a grouped-volume polynomial; fused retention/probing
and sharp global time and simultaneous peak space remain open. The complete old
uniform solver is unchanged.

## Main definitions

* `sortedRecords`, `groups`, `count`, `fullStates`: generated quarter records, class joins,
  counts and full-state records.
* `table`: a fixed runtime-counter loop counting every computed forward class.

## Main results

* `mem_fullStates`, `original_zero_iff`: original-input witness and exhaustive-miss semantics.
* `count_streaming`: direct sorted-record counting feeds the existing class semantics.
* `fullRecords_computable`: per-pair streamed full-state reconstruction.
* `tableCertificate`, `original_table_zero_iff`: actual uniform all-class counting.
* `table_wire`: quarter-scale stored counts, separately from internal machine workspace.
* `witnesses_nodup`: generated class pairs preserve unique packed quarter words.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.ClassJoin
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Projected width, seed, two original-order quarters, and selected class. -/
abbrev Input := SortedMeet.Input × ℕ

/-- Unary width and binary seed, operands and class index. -/
def encoding : Input ↪ List Bool := encPair SortedMeet.encoding encNat

/-- Generate forward states and actual inverse queries; the suffix payload indexes its reversal. -/
def batches (input : Input) : SortedMatch.Input :=
  let (((width, seed), (first, second)), target) := input
  (width, (SortedQuarterMachine.run ((width, seed), first),
    SortedMeet.inverse ((width, target), second)))

/-- Quarter records, tagged by direction and radix sorted by projected state. -/
def sortedRecords (input : Input) : List (ℕ × ℕ) :=
  let (width, _) := batches input
  RadixSort.sort (width, SortedMatch.tagged (batches input))

/-- Actual generation, tagging, sorting and one-pass group emission. -/
def groups (input : Input) : List (List (ℕ × ℕ)) := KeyGrouping.run (sortedRecords input)

/-- Every pair of colliding quarter occurrences, without replacing inverse addition by addition. -/
def witnesses (input : Input) : List (ℕ × ℕ) := KeyJoin.join (groups input)

/-- Actual class count; Cartesian products are not constructed by this computation. -/
def count (input : Input) : ℕ := KeyJoin.count (groups input)

/-- The count equals emitted occurrence multiplicity, including collisions. -/
theorem count_eq_length (input : Input) : count input = (witnesses input).length :=
  KeyJoin.count_eq_length _

/-- Arbitrary-width completeness and soundness of the generated class join. No semantic
query, class size, sortedness or traversal conclusion is supplied as an endpoint premise. -/
theorem mem_witnesses {p : ℕ} (as bs : List (BitVec p)) (s g : BitVec p) (uv : ℕ × ℕ) :
    uv ∈ witnesses ((((p, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), g.toNat)) ↔
      uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        eval (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s = g := by
  let input : Input := (((p, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), g.toNat)
  have forward := (SortedQuarterMachine.correct as s).2.2
  have inverse := SortedMeet.mem_inverse bs g
  have fits : ∀ r ∈ (batches input).2.1 ++ (batches input).2.2, r.1 < 2 ^ p := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [(forward r).mp hr |>.2]; exact (eval _ s).isLt
    · rw [(inverse r).mp hr |>.2]; exact (backward _ g).isLt
  change uv ∈ KeyJoin.join (KeyGrouping.run
    (RadixSort.sort ((batches input).1, SortedMatch.tagged (batches input)))) ↔ _
  have hj := KeyJoin.mem_join (batches input) fits uv
  dsimp only at hj
  rw [hj]
  constructor
  · rintro ⟨a, ha, b, hb, he, huv⟩
    obtain ⟨ha, hs⟩ := (forward a).mp ha
    obtain ⟨hb, ht⟩ := (inverse b).mp hb
    rw [huv]
    refine ⟨ha, hb, (eval_append_eq_iff _ _ _ _).mpr ?_⟩
    exact BitVec.eq_of_toNat_eq (hs.symm.trans (he.trans ht))
  · rintro ⟨hu, hv, he⟩
    let a := ((eval ((Native.Quarter.decode as.length uv.1).zip as) s).toNat, uv.1)
    let b := ((backward (((Native.Quarter.decode bs.length uv.2).reverse).zip bs) g).toNat, uv.2)
    exact ⟨a, (forward a).mpr ⟨hu, rfl⟩, b, (inverse b).mpr ⟨hv, rfl⟩,
      congrArg BitVec.toNat ((eval_append_eq_iff _ _ _ _).mp he), Prod.ext rfl rfl⟩

/-- A zero count proves exhaustive absence of an original-order operator word in the class. -/
theorem count_zero_iff {p : ℕ} (as bs : List (BitVec p)) (s g : BitVec p) :
    count ((((p, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), g.toNat)) = 0 ↔
      ¬ ∃ uv : ℕ × ℕ, uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        eval (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s = g := by
  rw [count_eq_length, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  simp only [mem_witnesses, not_exists]

/-- Actual quarter generation, inverse queries, tags and radix sorting, before any groups. -/
noncomputable def sortedCertificate : NativeCertificate sortedRecords encoding
    (encList (encPair encNat encNat)) := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let quarters := SortedMeet.quarterCertificate.comp
    (original.fst.fst.prod original.fst.snd.fst)
  let queries := SortedMeet.inverseCertificate.comp
    ((original.fst.fst.fst.prod original.snd).prod original.fst.snd.snd)
  let batch := original.fst.fst.fst.prod (quarters.prod queries)
  let left := SortedMatch.tagCertificate.comp
    ((NativeCertificate.const (em := encBool) false).prod batch.snd.fst)
  let right := SortedMatch.tagCertificate.comp
    ((NativeCertificate.const (em := encBool) true).prod batch.snd.snd)
  let tag := (left.prod right).post (ComputableInO.append' (enc := (encPair encNat encNat)))
  let sort := SortedMatch.sortCertificate.comp (original.fst.fst.fst.prod tag)
  exact NativeCertificate.congr sort (fun _ => rfl)

/-- Grouped emission is used by the occurrence producer, independently of the count path. -/
noncomputable def groupsCertificate :
    NativeCertificate groups encoding KeyGrouping.outputEncoding := by
  let h := (Classical.choose_spec KeyGrouping.run_computable).2.2
  let writer : NativeCertificate KeyGrouping.run (encList (encPair encNat encNat))
      KeyGrouping.outputEncoding := ⟨_, _, h⟩
  exact NativeCertificate.congr (writer.comp sortedCertificate) (fun _ => rfl)

/-- A direct record pass computes the same class size, without constructing any groups. -/
theorem count_streaming (input : Input) : count input = KeyCount.run (sortedRecords input) :=
  (KeyCount.run_eq_count _).symm

/-- One uniform count machine bypasses grouping and Cartesian products. Its consumer charges
input volume plus record count times a polynomial of physical row and binary counter widths;
the quarter-generation and sorting phase profiles are charged separately by composition. -/
noncomputable def countCertificate : NativeCertificate count encoding encNat := by
  let h := (Classical.choose_spec KeyCount.run_computable).2.2
  let consumer : NativeCertificate KeyCount.run (encList (encPair encNat encNat)) encNat :=
    ⟨_, _, h⟩
  exact NativeCertificate.congr (consumer.comp sortedCertificate)
    (fun input => (count_streaming input).symm)

/-- The executable join, including its current polynomial grouped-list overhead. -/
noncomputable def witnessesCertificate : NativeCertificate witnesses encoding
    (encList (encPair encNat encNat)) :=
  NativeCertificate.congr ((NativeCertificate.ofPolyTime KeyJoin.join_polyTime).comp
    groupsCertificate) (fun _ => rfl)

/-- Original source operands and a runtime class index. -/
abbrev SourceInput := Source.Input × ℕ

/-- Original full-width input framing and binary class index. -/
def sourceEncoding : SourceInput ↪ List Bool := encPair Source.encoding encNat

/-- Compute the source cut and capped projection for both quarters and the class index. -/
def prepare (input : SourceInput) : Input :=
  let (original, selected) := input
  let source := Source.prepare original
  let ((_, depth), (seed, _)) := source.1
  let ((first, second), _) := source.2
  let modulus := 2 ^ depth
  (((depth, seed % modulus),
    (first.map (· % modulus), second.map (· % modulus))), selected % modulus)

/-- Original-input class occurrence count through generated quarter-query groups. -/
def run (input : SourceInput) : ℕ := count (prepare input)

/-- No semantic projection premise: preparation really executes bit arithmetic and list maps. -/
theorem prepare_polyTime : ComputableInPolyTime prepare sourceEncoding encoding := by
  have src := Source.prepare_polyTime.comp (ComputableInPolyTime.fst Source.encoding encNat)
  have depth : ComputableInPolyTime (fun x : SourceInput => (Source.prepare x.1).1.1.2)
      sourceEncoding encUnary := by
    have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.1.2)
        ProgramGeneration.sourceEncoding encUnary := by fun_prop
    exact h.comp src
  have modulus := ComputableInPolyTime.binary_pow' (.const 2) depth
  have seed : ComputableInPolyTime (fun x : SourceInput => (Source.prepare x.1).1.2.1)
      sourceEncoding encNat := by
    have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.2.1)
        ProgramGeneration.sourceEncoding encNat := by fun_prop
    exact h.comp src
  have mapped (which : Bool) : ComputableInPolyTime
      (fun x : SourceInput => (if which then (Source.prepare x.1).2.1.2
        else (Source.prepare x.1).2.1.1).map (· % 2 ^ (Source.prepare x.1).1.1.2))
      sourceEncoding (encList encNat) := by
    have ops : ComputableInPolyTime
        (fun x : SourceInput => if which then (Source.prepare x.1).2.1.2
          else (Source.prepare x.1).2.1.1) sourceEncoding (encList encNat) := by
      have h : ComputableInPolyTime (fun x : ProgramGeneration.Source =>
          if which then x.2.1.2 else x.2.1.1) ProgramGeneration.sourceEncoding
          (encList encNat) := by cases which <;> simp only [Bool.false_eq_true, ite_false,
            ite_true] <;> fun_prop
      exact h.comp src
    have body : ComputableTidilyInPolyTime
        (fun q : SourceInput × ℕ => q.2 % 2 ^ (Source.prepare q.1.1).1.1.2)
        (encPair sourceEncoding encNat) encNat :=
      ComputableInPolyTime.tidy (ComputableInPolyTime.binary_mod.comp
        ((ComputableInPolyTime.snd sourceEncoding encNat).prod
          (modulus.comp (ComputableInPolyTime.fst sourceEncoding encNat))))
    exact .of_tidy (ops.tidy.mapWithInput body)
  have selected := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.snd Source.encoding encNat).prod modulus)
  exact (((depth.prod (ComputableInPolyTime.binary_mod.comp (seed.prod modulus))).prod
    ((mapped false).prod (mapped true))).prod selected).of_enc_eq (fun _ => rfl)

/-- Original-input preparation and class counting compose to an actual uniform bit machine.
No supplied executable or simulation contract is used. -/
noncomputable def sourceCertificate : NativeCertificate run sourceEncoding encNat :=
  NativeCertificate.congr (countCertificate.comp (NativeCertificate.ofPolyTime prepare_polyTime))
    (fun _ => rfl)

/-- Exact original full-width semantics of every generated projected-class witness. -/
theorem original_witnesses {m p : ℕ} (hm : p ≤ m) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) (g : BitVec p) (uv : ℕ × ℕ) :
    let ((as, bs), _) := Source.quarters tail
    uv ∈ witnesses (prepare (Source.ofWords p s tail, g.toNat)) ↔
      uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        (eval (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s).toNat % 2 ^ p =
            g.toNat := by
  dsimp only
  have prep : prepare (Source.ofWords p s tail, g.toNat) =
      (((p, (s.setWidth p).toNat),
        ((((Source.quarters tail).1.1).map (BitVec.setWidth p)).map BitVec.toNat,
          (((Source.quarters tail).1.2).map (BitVec.setWidth p)).map BitVec.toNat)), g.toNat) := by
    simp only [prepare, Source.prepare_ofWords_admitted hm s tail hk,
      ProgramGeneration.originalSource, BitInput.words, List.map_map,
      Function.comp_def, BitVec.toNat_setWidth, Nat.mod_eq_of_lt g.isLt]
  rw [prep, mem_witnesses]
  simp only [List.length_map]
  have hz (xs : List Bool) (as : List (BitVec m)) :
      xs.zip (as.map (BitVec.setWidth p)) = project p (xs.zip as) := by
    rw [List.zip_map_right]; rfl
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [hz, hz]
  have append (xs ys : List (Bool × BitVec m)) :
      project p xs ++ project p ys = project p (xs ++ ys) := by
    simp only [project, List.map_append]
  rw [append, ← eval_project hm, BitVec.toNat_eq, BitVec.toNat_setWidth]


/-- Real source-input count zero is an exhaustive original packed-word miss. -/
theorem original_zero_iff {m p : ℕ} (hm : p ≤ m) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) (g : BitVec p) :
    let ((as, bs), _) := Source.quarters tail
    run (Source.ofWords p s tail, g.toNat) = 0 ↔
      ¬ ∃ uv : ℕ × ℕ, uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        (eval (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s).toNat % 2 ^ p =
            g.toNat := by
  dsimp only
  rw [run, count_eq_length, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  simp only [original_witnesses hm s tail hk g, not_exists, Source.quarters]

/-- Full original-width operands of the two forward quarters, before projection. -/
def fullInput (original : Source.Input) : SortedMeet.Input :=
  let source := Source.prepare original
  let ((width, _), (seed, _)) := source.1
  let ((first, second), _) := source.2
  ((width, seed), (first, second))

/-- Execute the original full-width chain for a generated pair of quarter indices. -/
def fullRecord (input : Source.Input) (uv : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  let halves := fullInput input
  let ((width, seed), (first, second)) := halves
  (natEval width ((SortedMeet.decodeWitness halves uv).zip (first ++ second)) seed, uv)

/-- Materialize one actual full-state class, rather than both unfiltered half spaces. -/
def fullStates (input : SourceInput) : List (ℕ × (ℕ × ℕ)) :=
  let (original, _) := input
  (witnesses (prepare input)).map (fullRecord original)

/-- State production preserves exactly the count pass's occurrence multiplicity. -/
theorem fullStates_length (input : SourceInput) : (fullStates input).length = run input := by
  simp only [fullStates, List.length_map, run, count_eq_length]

/-- The retained record executes original full-width words, independently of the projection. -/
theorem fullRecord_original {m p : ℕ} (hm : p ≤ m) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) (uv : ℕ × ℕ) :
    let ((as, bs), _) := Source.quarters tail
    fullRecord (Source.ofWords p s tail) uv =
      ((eval (((Native.Quarter.decode as.length uv.1).zip as) ++
        (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s).toNat, uv) := by
  dsimp only
  have hi : fullInput (Source.ofWords p s tail) =
      ((m, s.toNat), (((Source.quarters tail).1.1).map BitVec.toNat,
        ((Source.quarters tail).1.2).map BitVec.toNat)) := by
    simp only [fullInput, Source.prepare_ofWords_admitted hm s tail hk,
      ProgramGeneration.originalSource, BitInput.words]
  rw [fullRecord, hi]
  dsimp only [SortedMeet.decodeWitness]
  simp only [List.length_map]
  have hz (as bs : List (BitVec m)) :
      ((Native.Quarter.decode as.length uv.1) ++
        (Native.Quarter.decode bs.length uv.2).reverse).zip
          (as.map BitVec.toNat ++ bs.map BitVec.toNat) =
        (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)).map
            (fun q => (q.1, q.2.toNat)) := by
    rw [List.zip_append (by simp : (Native.Quarter.decode as.length uv.1).length =
      (as.map BitVec.toNat).length), List.map_append]
    congr 1 <;> (rw [List.zip_map_right]; rfl)
  rw [hz, natEval_toNat]

/-- Every actual full-state class record is an original witness, and every packed original
witness in the class is emitted. No dictionary or full-state correctness premise is required. -/
theorem mem_fullStates {m p : ℕ} (hm : p ≤ m) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) (g : BitVec p) (state u v : ℕ) :
    let ((as, bs), _) := Source.quarters tail
    (state, (u, v)) ∈ fullStates (Source.ofWords p s tail, g.toNat) ↔
      u < 2 ^ as.length ∧ v < 2 ^ bs.length ∧
        state = (eval (((Native.Quarter.decode as.length u).zip as) ++
          (((Native.Quarter.decode bs.length v).reverse).zip bs)) s).toNat ∧
            state % 2 ^ p = g.toNat := by
  dsimp only
  change (state, (u, v)) ∈ (witnesses _).map (fullRecord _) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨uv, hu, he⟩
    rw [fullRecord_original hm s tail hk] at he
    have hv := congrArg Prod.snd he
    dsimp only at hv
    subst uv
    have h := (original_witnesses hm s tail hk g (u, v)).mp hu
    have hs := congrArg Prod.fst he
    dsimp only at hs
    exact ⟨h.1, h.2.1, hs.symm,
      (congrArg (fun x => x % 2 ^ p) hs).symm.trans h.2.2⟩
  · rintro ⟨hu, hv, hs, hg⟩
    refine ⟨(u, v), (original_witnesses hm s tail hk g _).mpr ⟨hu, hv, ?_⟩, ?_⟩
    · simpa only [hs, Source.quarters] using hg
    · rw [fullRecord_original hm s tail hk]
      exact Prod.ext hs.symm rfl

private theorem fullInput_polyTime : ComputableInPolyTime fullInput Source.encoding
    SortedMeet.encoding := by
  have width : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.1.1)
      ProgramGeneration.sourceEncoding encUnary := by fun_prop
  have seed : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.2.1)
      ProgramGeneration.sourceEncoding encNat := by fun_prop
  have first : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.2.1.1)
      ProgramGeneration.sourceEncoding (encList encNat) := by fun_prop
  have second : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.2.1.2)
      ProgramGeneration.sourceEncoding (encList encNat) := by fun_prop
  exact (((width.prod seed).prod (first.prod second)).comp Source.prepare_polyTime).of_enc_eq
    (fun _ => rfl)

private theorem fullRecord_polyTime : ComputableInPolyTime
    (fun q : Source.Input × (ℕ × ℕ) => fullRecord q.1 q.2)
    (encPair Source.encoding (encPair encNat encNat)) (encPair encNat (encPair encNat encNat)) := by
  let encIn := encPair Source.encoding (encPair encNat encNat)
  have halves := fullInput_polyTime.comp
    (ComputableInPolyTime.fst Source.encoding (encPair encNat encNat))
  have index := ComputableInPolyTime.snd Source.encoding (encPair encNat encNat)
  have bits := (bits_encList_polyTime encBool).1.comp
    (SortedMeet.decodeWitness_polyTime.comp (halves.prod index))
  have params : ComputableInPolyTime (fun q : Source.Input × (ℕ × ℕ) => (fullInput q.1).1)
      encIn (encPair encUnary encNat) :=
    (ComputableInPolyTime.fst _ _).comp halves
  have operands : ComputableInPolyTime
      (fun q : Source.Input × (ℕ × ℕ) => (fullInput q.1).2.1 ++ (fullInput q.1).2.2)
      encIn (encList encNat) := by
    have h : ComputableInPolyTime (fun q : SortedMeet.Input => q.2.1 ++ q.2.2)
        SortedMeet.encoding (encList encNat) := by
      dsimp only [SortedMeet.encoding]
      fun_prop
    exact h.comp halves
  have zipped := (ComputableInPolyTime.zip encBool encNat).comp (bits.prod operands)
  exact (natEval_polyTime.comp (params.prod zipped)).prod index

private theorem state_emit_polyTime : ComputableInPolyTime
    (fun q : Source.Input × (ℕ × ℕ) => [fullRecord q.1 q.2])
    (encPair Source.encoding (encPair encNat encNat))
    (encList (encPair encNat (encPair encNat encNat))) := by
  have singleton : ComputableTidilyInPolyTime (fun row : ℕ × (ℕ × ℕ) => [row])
      (encPair encNat (encPair encNat encNat)) (encList (encPair encNat (encPair encNat encNat))) :=
    .of_linear (.of_frame (fun _ => by simp))
  exact .of_tidy (singleton.comp fullRecord_polyTime.tidy)

/-- Full-state reconstruction is a genuine per-pair streamed callback with polynomial overhead
in the original input and one packed pair, not polynomial in the complete retained class. -/
theorem fullRecords_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO (fun q : Source.Input × List (ℕ × ℕ) => q.2.map (fullRecord q.1))
      (encPair Source.encoding (encList (encPair encNat encNat)))
      (encList (encPair encNat (encPair encNat encNat)))
      (fun q => (encPair Source.encoding (encList (encPair encNat encNat)) q).length +
        (q.2.length + 1) * P (streamFilterWidth Source.encoding (encPair encNat encNat) q))
      (fun q => (encPair Source.encoding (encList (encPair encNat encNat)) q).length +
        (q.2.length + 1) * P (streamFilterWidth Source.encoding (encPair encNat encNat) q)) := by
  obtain ⟨P, hp, hm, h⟩ := ComputableInO.flatMap_stream state_emit_polyTime
  refine ⟨P, hp, hm, h.of_enc_eq ?_⟩
  intro q
  rw [List.map_eq_flatMap]

/-- Original-input grouped join followed by per-occurrence full-state emission. All phase
profiles are charged; the join consumer's grouped-volume polynomial remains visible. -/
noncomputable def fullStatesCertificate : NativeCertificate fullStates sourceEncoding
    (encList (encPair encNat (encPair encNat encNat))) := by
  let original : NativeCertificate (id : SourceInput → _) sourceEncoding sourceEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let prepared := NativeCertificate.ofPolyTime prepare_polyTime
  let indices := witnessesCertificate.comp prepared
  let h := (Classical.choose_spec fullRecords_computable).2.2
  let emit : NativeCertificate (fun q : Source.Input × List (ℕ × ℕ) =>
      q.2.map (fullRecord q.1)) (encPair Source.encoding (encList (encPair encNat encNat)))
      (encList (encPair encNat (encPair encNat encNat))) := ⟨_, _, h⟩
  exact NativeCertificate.congr (emit.comp (original.fst.prod indices)) (fun _ => rfl)

private theorem quarter_length (input : SortedQuarterMachine.Input) :
    (SortedQuarterMachine.run input).length = 2 ^ input.2.length := by
  have h := (RadixSort.prefix_invariants
    ((SortedQuarterMachine.indices input.2.length).map (SortedQuarterMachine.record input))
    input.1.1).2.length_eq
  simpa only [SortedQuarterMachine.run, RadixSort.sort,
    SortedQuarterMachine.indices_eq_range,
    List.length_map, List.length_range] using h

/-- The computed count is bounded by generated quarter volume, without enumerating half words. -/
theorem count_le_quarters (input : Input) :
    let ((_, (first, second)), _) := input
    count input ≤ (2 ^ first.length + 2 ^ second.length) ^ 2 := by
  dsimp only
  have h := KeyJoin.count_le_square (groups input)
  have hl : (groups input).flatten.length =
      2 ^ input.1.2.1.length + 2 ^ input.1.2.2.length := by
    change (KeyGrouping.run (RadixSort.sort
      ((batches input).1, SortedMatch.tagged (batches input)))).flatten.length = _
    rw [KeyGrouping.flatten_run, RadixSort.sort,
      (RadixSort.prefix_invariants (SortedMatch.tagged (batches input))
        (batches input).1).2.length_eq]
    simp only [SortedMatch.tagged, batches, List.length_append, List.length_map,
      SortedMeet.inverse, quarter_length, SortedMeet.inverseInput, List.length_reverse]
  rwa [hl] at h

private theorem source_count_le (input : Source.Input) (g : ℕ) :
    run (input, g) ≤ (2 ^ (input.2.tail.length / 4) + 2 ^ (input.2.tail.length / 4)) ^ 2 := by
  have h := count_le_quarters (prepare (input, g))
  have hf := (Source.quarters_lengths input.2.tail).1
  have hs := (Source.quarters_lengths input.2.tail).2.1
  simpa only [run, prepare, Source.prepare, List.length_map, hf, hs] using h

/-- One fixed outer-loop body computes the next class count and retains only its binary result. -/
def tableStep (input : Source.Input) (state : ℕ × List ℕ) : ℕ × List ℕ :=
  let (index, counts) := state
  (index + 1, run (input, index) :: counts)

/-- The actual capped source projection depth, also used by the quarter producers. -/
def depth (input : Source.Input) : ℕ :=
  let source := Source.prepare input
  let ((_, projected), _) := source.1
  projected

/-- Uniform all-class occurrence counting, releasing quarter/group temporaries between rounds.
The retained table contains counts, not half words or all class records. -/
def table (input : Source.Input) : List ℕ :=
  (((tableStep input)^[2 ^ depth input] (0, [])).2).reverse

private theorem table_prefix (input : Source.Input) (n : ℕ) :
    (tableStep input)^[n] (0, []) =
      (n, ((List.range n).map (fun g => run (input, g))).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [tableStep, List.range_succ, List.map_append, List.map_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append]

/-- Every computed class is visited exactly once, including the unique zero-width class. -/
theorem table_eq (input : Source.Input) :
    table input = (List.range (2 ^ depth input)).map (fun g => run (input, g)) := by
  rw [table, table_prefix, List.reverse_reverse]

/-- The all-class loop has the computed range length, not an assumed completion certificate. -/
theorem table_length (input : Source.Input) : (table input).length = 2 ^ depth input := by
  simp only [table_eq, List.length_map, List.length_range]

private theorem depth_polyTime : ComputableInPolyTime depth Source.encoding encUnary := by
  have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.1.2)
      ProgramGeneration.sourceEncoding encUnary := by fun_prop
  exact (h.comp Source.prepare_polyTime).of_enc_eq (fun _ => rfl)

private noncomputable def tableStepCertificate : NativeCertificate
    (fun q : Source.Input × (ℕ × List ℕ) => tableStep q.1 q.2)
    (encPair Source.encoding (encPair encNat (encList encNat)))
    (encPair encNat (encList encNat)) := by
  let e := encPair Source.encoding (encPair encNat (encList encNat))
  let original : NativeCertificate (id : Source.Input × (ℕ × List ℕ) → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let selected := sourceCertificate.comp (original.fst.prod original.snd.fst)
  let counts := (selected.prod original.snd.snd).post (ComputableInO.cons' (enc := encNat))
  have increment : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let next := (NativeCertificate.ofPolyTime increment).comp original.snd.fst
  exact NativeCertificate.congr (next.prod counts) (fun _ => rfl)

/-- One finite runtime-counter machine computes the complete class-count table. Its actual
profile includes all generation/count phases, loop control and table copying; no sharp global
bound or small callback-workspace hypothesis is inserted into the certificate. -/
noncomputable def tableCertificate : NativeCertificate table Source.encoding (encList encNat) := by
  have clock : ComputableInPolyTime (fun input : Source.Input => 2 ^ depth input)
      Source.encoding encNat := ComputableInPolyTime.binary_pow' (.const 2) depth_polyTime
  let loop := ClassStreaming.loopCertificate Source.encoding (encList encNat)
    (fun input => 2 ^ depth input) tableStep [] clock tableStepCertificate
  let reverse := NativeCertificate.ofPolyTime (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listReverse encNat))
  exact NativeCertificate.congr (reverse.comp loop) (fun _ => rfl)

/-- The physically encoded table is quarter-scale, including binary counts and all frames.
This is a stored-output bound, not a substitute for the certificate's internal temporary space. -/
theorem table_wire (input : Source.Input) :
    let (_, operands) := input
    let k := operands.tail.length / 4
    (encList encNat (table input)).length ≤ 2 ^ depth input * (4 * k + 7) := by
  dsimp only
  let k := input.2.tail.length / 4
  have recordBound (n : ℕ) (hn : n ∈ table input) : (encNat n).length ≤ 2 * k + 3 := by
    rw [table_eq, List.mem_map] at hn
    obtain ⟨g, _, rfl⟩ := hn
    have hc := source_count_le input g
    have he : (2 ^ k + 2 ^ k) ^ 2 < 2 ^ (2 * k + 3) := by
      rw [show 2 * k + 3 = k + k + 3 by omega, Nat.pow_add, Nat.pow_add]
      have hp := Nat.two_pow_pos k
      norm_num
      nlinarith
    have hsize := Nat.size_le.mpr (hc.trans_lt he)
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using hsize
  have hw := length_encList_le encNat (table input) recordBound
  rw [table_length] at hw
  have he : 2 * (2 * k + 3) + 1 = 4 * k + 7 := by omega
  simpa only [he] using hw

/-- The all-class machine returns each original-input exhaustive-miss count at its actual index. -/
theorem original_table_zero_iff {m p : ℕ} (hm : p ≤ m) (s : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) (g : BitVec p) :
    let ((as, bs), _) := Source.quarters tail
    (table (Source.ofWords p s tail))[g.toNat]? = some 0 ↔
      ¬ ∃ uv : ℕ × ℕ, uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        (eval (((Native.Quarter.decode as.length uv.1).zip as) ++
          (((Native.Quarter.decode bs.length uv.2).reverse).zip bs)) s).toNat % 2 ^ p =
            g.toNat := by
  have hd : depth (Source.ofWords p s tail) = p := by
    simp only [depth, Source.prepare_ofWords_admitted hm s tail hk,
      ProgramGeneration.originalSource]
  rw [table_eq, hd, List.getElem?_map, List.getElem?_range g.isLt]
  simp only [Option.map_some, Option.some.injEq]
  exact original_zero_iff hm s tail hk g

private theorem quarter_payloads_nodup (input : SortedQuarterMachine.Input) :
    ((SortedQuarterMachine.run input).map Prod.snd).Nodup := by
  rcases input with ⟨⟨m, s⟩, as⟩
  have perm := (RadixSort.prefix_invariants
    ((SortedQuarterMachine.indices as.length).map (SortedQuarterMachine.record ((m, s), as))) m).2
  have hp := (perm.map Prod.snd).nodup_iff
  have he : ((SortedQuarterMachine.indices as.length).map
      (SortedQuarterMachine.record ((m, s), as))).map Prod.snd =
        SortedQuarterMachine.indices as.length := by
    simp only [List.map_map, SortedQuarterMachine.record, Function.comp_def]
    exact List.map_id _
  rw [he, SortedQuarterMachine.indices_eq_range] at hp
  simpa only [SortedQuarterMachine.run, RadixSort.sort, SortedQuarterMachine.indices_eq_range]
    using hp.mpr List.nodup_range

/-- Packed quarter indices remain unique through tagging, sorting and grouping. Consequently
class witness pairs have no duplicates, even when all evaluated state keys collide. -/
theorem witnesses_nodup (input : Input) : (witnesses input).Nodup := by
  let first := (batches input).2.1
  let second := (batches input).2.2
  have hl : (first.map Prod.snd).Nodup :=
    quarter_payloads_nodup (input.1.1, input.1.2.1)
  have hr : (second.map Prod.snd).Nodup := by
    have h := quarter_payloads_nodup (SortedMeet.inverseInput ((input.1.1.1, input.2), input.1.2.2))
    simpa only [second, batches, SortedMeet.inverse, SortedMeet.reflect, List.map_map,
      Function.comp_def] using h
  have he : (((first.map Prod.snd).map (fun n => 2 * n)) ++
      ((second.map Prod.snd).map (fun n => 2 * n + 1))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hl.map (fun _ _ h => by omega), hr.map (fun _ _ h => by omega), ?_⟩
    intro a ha b hb hab
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    omega
  have ht : ((SortedMatch.tagged (batches input)).map Prod.snd).Nodup := by
    simpa only [SortedMatch.tagged, SortedMatch.tag, List.map_append, List.map_map,
      Function.comp_def, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] using he
  apply KeyJoin.join_nodup
  rw [groups, KeyGrouping.flatten_run]
  exact ((SortedMatch.sorted_perm (batches input)).map Prod.snd).nodup_iff.mpr ht

end Cslib.Cryptanalysis.AddXNOR.ClassJoin
