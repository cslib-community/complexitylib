/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
public import Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
public import Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Generated forward/inverse full-state matching

The forward generator is reused for inverse execution by actual input reversal,
complementing the target before generation and complementing each emitted state.
Tagged full-state batch matching retains the original packed witnesses. The
returned suffix operators are reversed back before witness output.

This is a direct multitape route from original operands to a witness or exhaustive
miss, using the source cut/seed/zero-target convention. It materializes both half
spaces. Its certificates charge that materialization and every intermediate tape;
it does not supply the source's smaller-class peak space or class-count/reuse loop.
The sorted batch matcher is the matching stage for such a later batched route.
[WangLvShenZhang2027], Section 5 and Lemma 8/Theorem 7, PDF pp. 20–22.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SortedMeet
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Complement the target and reverse the actual original operands for inverse generation. -/
def inverseInput (input : SortedQuarterMachine.Input) : SortedQuarterMachine.Input :=
  let ((width, target), operands) := input
  ((width, 2 ^ width - 1 - target), operands.reverse)

/-- Reflect an emitted state; its packed word still indexes the reversed operand order. -/
def reflect (width : ℕ) (r : ℕ × ℕ) : ℕ × ℕ :=
  let (state, index) := r
  (2 ^ width - 1 - state, index)

/-- Actual forward generation plus input/output conjugation implements the inverse direction. -/
def inverse (input : SortedQuarterMachine.Input) : List (ℕ × ℕ) :=
  let ((width, _), _) := input
  (SortedQuarterMachine.run (inverseInput input)).map (reflect width)

/-- Width/seed and two original-order operand arrays. Target is the source's zero word. -/
abbrev Input := (ℕ × ℕ) × (List ℕ × List ℕ)

/-- Original binary operands and seed, with unary physical width. -/
def encoding : Input ↪ List Bool :=
  encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat))

/-- Both actual full-state arrays are generated before the batch matcher runs. -/
def matching (input : Input) : Option (ℕ × ℕ) :=
  let ((width, seed), (left, right)) := input
  SortedMatch.run (width, (SortedQuarterMachine.run ((width, seed), left),
    inverse ((width, 0), right)))

/-- Read back both original-order operator words, including leading zero operators. -/
def decodeWitness (input : Input) (witness : ℕ × ℕ) : List Bool :=
  let (_, (left, right)) := input
  let (u, v) := witness
  Native.Quarter.decode left.length u ++ (Native.Quarter.decode right.length v).reverse

/-- A concrete returned operator list, rather than an assumed witness-decoder contract. -/
def solve (input : Input) : Option (List Bool) := (matching input).map (decodeWitness input)

/-- Construct the half cut from the computed source quarters, preserving all residual operands. -/
def prepare (input : Source.Input) : Input :=
  let source := Source.prepare input
  let ((width, _), (seed, _)) := source.1
  let ((a, b), (c, d)) := source.2
  ((width, seed), (a ++ b, c ++ d))

/-- Original single-list source input to an actual bit-machine witness/miss route. -/
def run (input : Source.Input) : Option (List Bool) := solve (prepare input)

private theorem backward_key {m : ℕ} (as : List (BitVec m)) (t : BitVec m) (u : ℕ) :
    (reflect m ((eval ((Native.Quarter.decode as.length u).zip as.reverse) (~~~t)).toNat, u)).1 =
      (backward (((Native.Quarter.decode as.length u).reverse).zip as) t).toNat := by
  have hz : (((Native.Quarter.decode as.length u).reverse).zip as).reverse =
      (Native.Quarter.decode as.length u).zip as.reverse := by
    simpa only [List.reverse_reverse, List.zip_eq_zipWith] using
      (List.reverse_zipWith (f := Prod.mk) (by simp :
        (Native.Quarter.decode as.length u).reverse.length = as.length))
  rw [backward_eq_not_eval_reverse, hz]
  simp only [reflect, BitVec.toNat_not]

/-- All inverse records are derived from real reversed/complemented execution. The operator
word is explicitly reversed back; forward addition is never used as its own inverse. -/
theorem mem_inverse {m : ℕ} (as : List (BitVec m)) (t : BitVec m) (r : ℕ × ℕ) :
    r ∈ inverse ((m, t.toNat), as.map BitVec.toNat) ↔
      r.2 < 2 ^ as.length ∧
        r.1 = (backward (((Native.Quarter.decode as.length r.2).reverse).zip as) t).toNat := by
  have hi : inverseInput ((m, t.toNat), as.map BitVec.toNat) =
      ((m, (~~~t).toNat), as.reverse.map BitVec.toNat) := by
    simp only [inverseInput, BitVec.toNat_not, List.map_reverse]
  have hf := (SortedQuarterMachine.correct as.reverse (~~~t)).2.2
  simp only [inverse, hi, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h := (hf q).mp hq
    simp only [List.length_reverse] at h
    refine ⟨h.1, ?_⟩
    rw [show q = ((eval ((Native.Quarter.decode as.length q.2).zip as.reverse) (~~~t)).toNat, q.2)
      from Prod.ext h.2 rfl]
    exact backward_key as t _
  · rintro ⟨hu, hs⟩
    let q := ((eval ((Native.Quarter.decode as.length r.2).zip as.reverse) (~~~t)).toNat, r.2)
    refine ⟨q, (hf q).mpr ?_, ?_⟩
    · constructor
      · simpa only [q, List.length_reverse] using hu
      · simp only [q, List.length_reverse]
    · apply Prod.ext
      · exact (backward_key as t r.2).trans hs.symm
      · rfl

private theorem mem_forward {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (r : ℕ × ℕ) :
    r ∈ SortedQuarterMachine.run ((m, s.toNat), as.map BitVec.toNat) ↔
      r.2 < 2 ^ as.length ∧
        r.1 = (eval ((Native.Quarter.decode as.length r.2).zip as) s).toNat :=
  (SortedQuarterMachine.correct as s).2.2 r

/-- A matching pair of actual generated states is exactly a solution at the original cut. -/
theorem meeting_iff {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) :
    (∃ a ∈ SortedQuarterMachine.run ((m, s.toNat), as.map BitVec.toNat),
      ∃ b ∈ inverse ((m, 0), bs.map BitVec.toNat), a.1 = b.1) ↔ Solvable (as ++ bs) s 0 := by
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    have hf := (mem_forward as s a).mp ha
    have hi := (mem_inverse bs 0 b).mp hb
    refine ⟨Native.Quarter.decode as.length a.2 ++ (Native.Quarter.decode bs.length b.2).reverse,
      by simp, ?_⟩
    rw [List.zip_append (by simp : (Native.Quarter.decode as.length a.2).length = as.length)]
    apply (eval_append_eq_iff _ _ _ _).mpr
    apply BitVec.eq_of_toNat_eq
    exact hf.2.symm.trans (heq.trans hi.2)
  · rintro ⟨ops, hlen, hsol⟩
    let left := ops.take as.length
    let right := ops.drop as.length
    have hl : left.length = as.length := by
      simp only [left, List.length_take, List.length_append] at *
      omega
    have hr : right.length = bs.length := by
      simp only [right, List.length_drop, List.length_append] at *
      omega
    have hlDecode : Native.Quarter.decode as.length (Native.Quarter.encode left) = left := by
      rw [← hl, Native.Quarter.decode_encode]
    have hrDecode :
        (Native.Quarter.decode bs.length (Native.Quarter.encode right.reverse)).reverse =
          right := by
      rw [← hr, ← List.length_reverse (as := right), Native.Quarter.decode_encode,
        List.reverse_reverse]
    let a := ((eval (left.zip as) s).toNat, Native.Quarter.encode left)
    let b := ((backward (right.zip bs) 0).toNat, Native.Quarter.encode right.reverse)
    refine ⟨a, (mem_forward as s a).mpr ?_, b, (mem_inverse bs 0 b).mpr ?_, ?_⟩
    · exact ⟨by simpa only [a, hl] using Native.Quarter.encode_lt left,
        by simp only [a, hlDecode]⟩
    · exact ⟨by simpa only [b, List.length_reverse, hr] using
        Native.Quarter.encode_lt right.reverse,
        by simp only [b, hrDecode]⟩
    · apply congrArg BitVec.toNat
      apply (eval_append_eq_iff _ _ _ _).mp
      rw [← List.zip_append hl, show left ++ right = ops from List.take_append_drop ..]
      exact hsol

/-- The generated batches fit their actual full-state width, without a fit conclusion premise. -/
theorem generated_fit {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) :
    ∀ r ∈ SortedQuarterMachine.run ((m, s.toNat), as.map BitVec.toNat) ++
        inverse ((m, 0), bs.map BitVec.toNat), r.1 < 2 ^ m := by
  intro r hr
  rcases List.mem_append.mp hr with hf | hb
  · rw [(mem_forward as s r).mp hf |>.2]
    exact (eval ((Native.Quarter.decode as.length r.2).zip as) s).isLt
  · rw [(mem_inverse bs 0 r).mp hb |>.2]
    exact (backward (((Native.Quarter.decode bs.length r.2).reverse).zip bs) 0).isLt

/-- Exhaustive miss from actual generated records; no dictionary or matching correctness
is assumed. -/
theorem solve_none_iff {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) :
    solve ((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)) = none ↔
      ¬ Solvable (as ++ bs) s 0 := by
  rw [solve, Option.map_eq_none_iff]
  dsimp only [matching]
  rw [SortedMatch.none_iff _ (generated_fit as bs s), meeting_iff]

/-- Every returned decoded witness is an original-order solution of exactly the original length. -/
theorem solve_sound {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (ops : List Bool)
    (hit : solve ((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)) = some ops) :
    ops.length = (as ++ bs).length ∧ eval (ops.zip (as ++ bs)) s = 0 := by
  unfold solve at hit
  cases h : matching ((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)) with
  | none => simp [h] at hit
  | some out =>
    simp only [h, Option.map_some, Option.some.injEq] at hit
    have hm := h
    dsimp only [matching] at hm
    obtain ⟨a, ha, b, hb, hk, ho⟩ := SortedMatch.sound _ out hm
    have hf := (mem_forward as s a).mp ha
    have hi := (mem_inverse bs 0 b).mp hb
    subst ops
    rw [ho]
    constructor
    · simp [decodeWitness]
    · simp only [decodeWitness, List.length_map]
      rw [List.zip_append (by simp : (Native.Quarter.decode as.length a.2).length = as.length)]
      apply (eval_append_eq_iff _ _ _ _).mpr
      apply BitVec.eq_of_toNat_eq
      exact hf.2.symm.trans (hk.trans hi.2)

private abbrev recEncoding : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

private theorem inverseInput_polyTime : ComputableInPolyTime inverseInput
    SortedQuarterMachine.encoding SortedQuarterMachine.encoding := by
  unfold inverseInput
  dsimp only [SortedQuarterMachine.encoding]
  apply ComputableInPolyTime.of_tidy
  fun_prop

private theorem reflect_polyTime : ComputableInPolyTime
    (fun q : ℕ × (ℕ × ℕ) => [reflect q.1 q.2])
    (encPair encUnary recEncoding) (encList recEncoding) := by
  have value : ComputableTidilyInPolyTime (fun q : ℕ × (ℕ × ℕ) => reflect q.1 q.2)
      (encPair encUnary recEncoding) recEncoding := by
    unfold reflect
    fun_prop
  have singleton : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
      recEncoding (encList recEncoding) := .of_linear (.of_frame (fun _ => by simp))
  exact ComputableInPolyTime.of_tidy (singleton.comp value)

private theorem reflect_computable :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun q : ℕ × List (ℕ × ℕ) => q.2.map (reflect q.1))
        (encPair encUnary (encList recEncoding)) (encList recEncoding)
        (fun q => (encPair encUnary (encList recEncoding) q).length +
          (q.2.length + 1) * P (streamFilterWidth encUnary recEncoding q))
        (fun q => (encPair encUnary (encList recEncoding) q).length +
          (q.2.length + 1) * P (streamFilterWidth encUnary recEncoding q)) := by
  obtain ⟨P, hp, hm, h⟩ := ComputableInO.flatMap_stream reflect_polyTime
  refine ⟨P, hp, hm, h.of_enc_eq ?_⟩
  intro q
  rw [List.map_eq_flatMap]

private noncomputable def quarterCertificate : NativeCertificate SortedQuarterMachine.run
    SortedQuarterMachine.encoding (encList recEncoding) :=
  let h := (Classical.choose_spec SortedQuarterMachine.run_computable).2.2
  ⟨_, _, h.of_enc_eq (encC := encList recEncoding) (fun _ => rfl)⟩

private noncomputable def reflectCertificate : NativeCertificate
    (fun q : ℕ × List (ℕ × ℕ) => q.2.map (reflect q.1))
    (encPair encUnary (encList recEncoding)) (encList recEncoding) :=
  let h := (Classical.choose_spec reflect_computable).2.2
  ⟨_, _, h⟩

/-- Input reversal, target complement, genuine forward generation and per-record output
complementation are all executed and charged. No backward-simulation oracle is supplied. -/
noncomputable def inverseCertificate : NativeCertificate inverse
    SortedQuarterMachine.encoding (encList (encPair encNat encNat)) := by
  let original : NativeCertificate (id : SortedQuarterMachine.Input → _)
      SortedQuarterMachine.encoding SortedQuarterMachine.encoding :=
    .linear (.of_eq (fun _ => rfl))
  let prepared := NativeCertificate.ofPolyTime inverseInput_polyTime
  let generated := quarterCertificate.comp prepared
  let c := reflectCertificate.comp (original.fst.fst.prod generated)
  exact NativeCertificate.congr c (fun _ => rfl)

/-- Both generated batches, tagging, sorting and one-record scan are present in this profile.
The two half lists are simultaneously retained and must not be charged as the smaller class. -/
noncomputable def matchingCertificate : NativeCertificate matching encoding
    (encOption (encPair encNat encNat)) := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let left := quarterCertificate.comp (original.fst.prod original.snd.fst)
  let right := inverseCertificate.comp
    ((original.fst.fst.prod (NativeCertificate.const (em := encNat) 0)).prod original.snd.snd)
  let c := SortedMatch.runCertificate.comp (original.fst.fst.prod (left.prod right))
  exact NativeCertificate.congr c (fun _ => rfl)

private theorem decodeWitness_polyTime : ComputableInPolyTime
    (fun q : Input × (ℕ × ℕ) => decodeWitness q.1 q.2)
    (encPair encoding recEncoding) encBits := by
  have left : ComputableInPolyTime (fun q : Input × (ℕ × ℕ) => q.1.2.1)
      (encPair encoding recEncoding) (encList encNat) := by dsimp only [encoding]; fun_prop
  have right : ComputableInPolyTime (fun q : Input × (ℕ × ℕ) => q.1.2.2)
      (encPair encoding recEncoding) (encList encNat) := by dsimp only [encoding]; fun_prop
  have u : ComputableInPolyTime (fun q : Input × (ℕ × ℕ) => q.2.1)
      (encPair encoding recEncoding) encNat := by fun_prop
  have v : ComputableInPolyTime (fun q : Input × (ℕ × ℕ) => q.2.2)
      (encPair encoding recEncoding) encNat := by fun_prop
  have kl := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.length_list encNat).comp left.tidy)
  have kr := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.length_list encNat).comp right.tidy)
  have dl := SortedQuarterMachine.decode_polyTime.comp (kl.prod u)
  have dr := SortedQuarterMachine.decode_polyTime.comp (kr.prod v)
  have rev := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.listReverse encBool).comp dr.tidy)
  have append := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.listAppend encBool).comp (dl.tidy.prod rev.tidy))
  have bits := (bits_encList_polyTime encBool).2.comp append
  simpa only [decodeWitness, Function.comp_def] using bits

private theorem readback_polyTime : ComputableInPolyTime
    (fun q : Input × Option (ℕ × ℕ) => q.2.map (decodeWitness q.1))
    (encPair encoding (encOption recEncoding)) (encOption encBits) := by
  have value := ComputableTidilyInPolyTime.snd encoding (encOption recEncoding)
  have body : ComputableTidilyInPolyTime
      (fun q : (Input × Option (ℕ × ℕ)) × (ℕ × ℕ) => some (decodeWitness q.1.1 q.2))
      (encPair (encPair encoding (encOption recEncoding)) recEncoding) (encOption encBits) := by
    have h := decodeWitness_polyTime.tidy.comp
      (((ComputableTidilyInPolyTime.fst encoding (encOption recEncoding)).comp
        (ComputableTidilyInPolyTime.fst
          (encPair encoding (encOption recEncoding)) recEncoding)).prod
        (ComputableTidilyInPolyTime.snd (encPair encoding (encOption recEncoding)) recEncoding))
    exact (ComputableTidilyInPolyTime.optionSome encBits).comp h
  have h := value.optionElimWithInput
    (body := fun q out => some (decodeWitness q.1 out))
    (ComputableTidilyInPolyTime.const none) body
  convert ComputableInPolyTime.of_tidy h using 1
  funext q
  cases q.2 <;> rfl

/-- The actual matcher result is decoded on tape, charging original input capture/readback. -/
noncomputable def solveCertificate : NativeCertificate solve encoding (encOption encBits) := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let decoded := (NativeCertificate.ofPolyTime readback_polyTime).comp
    (original.prod matchingCertificate)
  exact NativeCertificate.congr decoded (fun _ => rfl)

private theorem prepare_polyTime : ComputableInPolyTime prepare Source.encoding encoding := by
  have h : ComputableInPolyTime
      (fun x : ProgramGeneration.Source => ((x.1.1.1, x.1.2.1),
        (x.2.1.1 ++ x.2.1.2, x.2.2.1 ++ x.2.2.2))) ProgramGeneration.sourceEncoding encoding := by
    apply ComputableInPolyTime.of_tidy
    dsimp only [encoding, BitInput.encoding]
    fun_prop
  exact (h.comp Source.prepare_polyTime).of_enc_eq (fun _ => rfl)

/-- One uniform original-source machine, with complete preparation/matching/output profiles.
This bypasses the sparse interpreter rather than deleting its costs from an unchanged run. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding (encOption encBits) :=
  solveCertificate.comp (NativeCertificate.ofPolyTime prepare_polyTime)

private theorem prepare_ofWords {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    prepare (Source.ofWords p a tail) =
      ((m, a.toNat),
        (((Source.quarters tail).1.1 ++ (Source.quarters tail).1.2).map BitVec.toNat,
          ((Source.quarters tail).2.1 ++ (Source.quarters tail).2.2).map BitVec.toNat)) := by
  simp only [prepare, Source.prepare_ofWords, ProgramGeneration.originalSource,
    BitInput.words, List.map_append]

/-- Exhaustive original-input absence and sound original-order output, for every quarter residue. -/
theorem original_correct {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    (run (Source.ofWords p a tail) = none ↔ ¬ Solvable tail a 0) ∧
      ∀ ops, run (Source.ofWords p a tail) = some ops →
        ops.length = tail.length ∧ eval (ops.zip tail) a = 0 := by
  have cut := Source.quarters_append tail
  constructor
  · rw [run, prepare_ofWords, solve_none_iff, cut]
  · intro ops hit
    rw [run, prepare_ofWords] at hit
    simpa only [cut] using solve_sound _ _ a ops hit

/-- The actual same finite machine precedes all original widths, depths and operand lists.
Its profile includes both full half spaces; no sharp smaller-class space is concluded. -/
theorem original_machine : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q)
    (machine : Turing.MultiTapeTM k Bool Q), ∀ {m : ℕ} (p : ℕ) (a : BitVec m)
      (tail : List (BitVec m)),
      machine.ComputesInTimeAndSpace (Source.encoding (Source.ofWords p a tail))
        (encOption encBits (run (Source.ofWords p a tail)))
        (c * (sourceCertificate.time (Source.ofWords p a tail) + 1))
        (c * (sourceCertificate.space (Source.ofWords p a tail) + 1)) ∧
      (run (Source.ofWords p a tail) = none ↔ ¬ Solvable tail a 0) ∧
      ∀ ops, run (Source.ofWords p a tail) = some ops →
        ops.length = tail.length ∧ eval (ops.zip tail) a = 0 := by
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := sourceCertificate.computes
  exact ⟨c, k, Q, hQ, machine, fun p a tail =>
    ⟨computes _, original_correct p a tail⟩⟩

end Cslib.Cryptanalysis.AddXNOR.SortedMeet
