/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORRestartResources
import all CslibFrontier.Cryptanalysis.AddXNORRestartResources
import all CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Cryptanalysis.AddXNORProducerResources
import all CslibFrontier.Cryptanalysis.AddXNORBalanceResources
import all CslibFrontier.Cryptanalysis.AddXNORMatcherResources
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Resources of the installed restarted batch pipeline

Compose scalar controls, retained-context copies and actual quarter/window/full-state
construction with the two-orientation matcher. All resource fields refer to installed uniform
bit-machine certificates, including internal input/output and callback tapes at every prefix.

`source_label_bounds` sums the actual guarded callbacks over every computed class and generated
label. This closes the callback pipeline, not the enclosing label loop, retained setup or the
whole solver. The source reachable-state-DP all-count/faster-prepass clause remains open.

This is original resource accounting for [WangLvShenZhang2027], Lemma 8/Theorem 7,
PDF pp. 21–22, using the deterministic multitape bit convention on p. 6. The sharp whole-run
source asymptotics are not claimed.

## Main results

* `context_bounds`: derived physical dictionary/context and scalar-control widths.
* `batchCertificate_bounds`: installed producer, including repeated quarters, sort and windows.
* `matchLabelCertificate_bounds`: complete guarded callback, including count and matcher.
* `source_label_bounds`: source-cut summed callback clocks and simultaneous callback workspace.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.BatchResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev ec := JoinedProbe.encoding

private theorem quarter_polynomial : ClassBatches.quarterCertificate.IsPolynomial := by
  unfold ClassBatches.quarterCertificate
  exact NativeCertificate.ofPolyTime_isPolynomial _

private theorem context_wire_eq (input : ClassBalance.Input) (produced retained : Bool)
    (w : ℕ) (kept : List (ℕ × ℕ)) (allowance : ℕ) :
    (ec ((input, produced), ((w, (retained, kept)), allowance))).length =
      4*(ClassBalance.encoding input).length+4*w+2*(encNatPairList kept).length+
        (encNat allowance).length+14 := by
  simp only [ec, JoinedProbe.encoding, JoinedProbe.contextEncoding,
    BatchedAccess.parameterEncoding, encNatPairList, RadixPartition.recordEncoding,
    length_encPair, encBool_apply, List.length_singleton, encUnary_apply, List.length_replicate]
  ring

/-- The actual retained context and runtime labels have physical widths derived from original
source operands and computed capacity. No dictionary-size or runtime bound is a premise. -/
theorem context_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      i ∈ ClassBatches.labels context g.toNat →
      (JoinedProbe.encoding context).length ≤ ClassBatches.capacity context*P B ∧
        (encNat (ClassBatches.capacity context)).length+(encNat i).length+
          (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length
            ≤ P B := by
  obtain ⟨D, hD, mD, widths⟩ := RestartResources.original_window_width
  let P := fun B => 1000*(D B+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 1000 (by have := mD h; omega), ?_⟩
  intro m p hp as bs cs ds s g i
  dsimp only
  intro hi
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let context := JoinedDissection.probeContext input g.toNat
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  let C := ClassBatches.capacity context
  let kept := ClassBalance.retain input g.toNat
  have positive : 0 < C := ClassBatches.capacity_pos context
  have lower : kept.length+1 ≤ C := by
    have h := JoinedDissection.restart_capacity_eq input g.toNat
    change C = kept.length+1+_ at h
    omega
  have width := widths hp as bs cs ds s g i hi
  have pairWire : (encPair encNat encNat (i*C, C)).length ≤ D B := by
    have h : (encPair encNat encNat (i*C, C)).length ≤
        KeyJoinBatch.windowWidth (i*C, C) (JoinedProbe.groups context g.toNat) := by
      dsimp only [KeyJoinBatch.windowWidth]; omega
    exact h.trans width
  have cw : (encNat C).length ≤ D B :=
    (length_le_encPair_right encNat encNat (i*C, C)).trans pairWire
  have iw : (encNat i).length ≤ D B := by
    have mul : i ≤ i*C := Nat.le_mul_of_pos_right _ positive
    exact (length_encNat_mono mul).trans
      ((length_le_encPair_left encNat encNat (i*C, C)).trans pairWire)
  have countWire := BalanceResources.count_wire hp as bs cs ds s
    (!(ClassBalance.retainRight input g.toNat)) g
  change (encNat (ClassBatches.population context g.toNat)).length ≤ q+1 at countWire
  have label : (encNat g.toNat).length ≤ p := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
  have rawWidth : m ≤ (ClassBalance.encoding input).length :=
    SearchResources.original_width (p := p) as bs cs ds s
  have rows (row : ℕ × ℕ) (hr : row ∈ kept) : (er row).length ≤ 4*B+1 := by
    have h := ClassBalance.record_wire hp as bs cs ds s _ g row hr
    change (er row).length ≤ 2*m+1+q at h
    dsimp only [B]
    omega
  have dictWire := length_encList_le er kept rows
  have allowance : (encNat (ClassBalance.count input (ClassBalance.retainRight input g.toNat)
      g.toNat+1)).length ≤ D B := (length_encNat_mono
        (show ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat+1 ≤ C from
          Nat.le_add_right _ _)).trans cw
  have contextWire : (ec context).length ≤ C*P B := by
    have originalWire : (ClassBalance.encoding input).length ≤ B := by dsimp only [B]; omega
    have widthWire : m ≤ B := rawWidth.trans originalWire
    change (encNatPairList kept).length ≤ kept.length*(2*(4*B+1)+1) at dictWire
    have eq := context_wire_eq input (!(ClassBalance.retainRight input g.toNat))
      (ClassBalance.retainRight input g.toNat) m kept
      (ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat+1)
    change (ec context).length = _ at eq
    rw [eq]
    have dictScaled := Nat.mul_le_mul_right (2*(8*B+3)) lower
    have scalar := Nat.mul_le_mul_left (D B) (show 1 ≤ C by omega)
    have original := Nat.mul_le_mul_left B (show 1 ≤ C by omega)
    dsimp only [P]
    nlinarith only [dictWire, originalWire, widthWire, allowance, lower, positive,
      dictScaled, scalar, original]
  have bp : q+p+1 ≤ B := by dsimp only [B]; omega
  constructor
  · exact contextWire
  · change (encNat C).length+(encNat i).length+
      (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length ≤ P B
    dsimp only [P]
    omega

private theorem capacity_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let q := as.length+bs.length+cs.length+ds.length
      i ∈ ClassBatches.labels context g.toNat →
      ClassBatches.capacityCertificate.time context+ClassBatches.capacityCertificate.space context ≤
        ClassBatches.capacity context*P ((ClassBalance.encoding input).length+q+p+1) := by
  delta ClassBatches.capacityCertificate
  extract_lets original add
  obtain ⟨D, hD, mD, data⟩ := context_bounds
  obtain ⟨Q, hQ, mQ, quarter⟩ := exists_mono_poly (quarter_polynomial.1.add quarter_polynomial.2)
  obtain ⟨A, hA, mA, addition⟩ := exists_mono_poly_cert add
  let P := fun B => 100*(D B+Q (10*B)+A (3*D B+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hq := mQ (Nat.mul_le_mul_left 10 hab)
    have ha := mA (by omega : 3*D a+1 ≤ 3*D b+1)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i
    dsimp only
    intro hi
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let C := ClassBatches.capacity context
    let N := ClassBatches.quarterVolume context
    let allowance := ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat+1
    let right := !(ClassBalance.retainRight input g.toNat)
    have h := data hp as bs cs ds s g i hi
    change (ec context).length ≤ C*D B ∧ _ at h
    have scalars : (encNat C).length+(encNat i).length+
        (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length ≤
        D B := h.2
    have cw : (encNat C).length ≤ D B := by omega
    have aw : (encNat allowance).length ≤ D B :=
      (length_encNat_mono (show allowance ≤ C from Nat.le_add_right _ _)).trans cw
    have nw : (encNat N).length ≤ D B :=
      (length_encNat_mono (show N ≤ C from Nat.le_add_left _ _)).trans cw
    have pairWire : (encPair encNat encNat (allowance, N)).length ≤ 3*D B+1 := by
      rw [length_encPair]
      dsimp only
      omega
    have a := addition (allowance, N)
    have atime := a.1.trans (mA pairWire)
    have aspace := a.2.trans (mA pairWire)
    have task := ProducerResources.count_task_wire input g right
    have sourceWire :
        (encPair ClassBalance.encoding encBool (input, right)).length ≤ 10*B := by
      have left := length_le_encPair_left (encPair ClassBalance.encoding encBool) encNat
        ((input, right), g.toNat)
      have taskWire :
          (encPair (encPair ClassBalance.encoding encBool) encNat
            ((input, right), g.toNat)).length+1 ≤
            10*B := task.trans (Nat.mul_le_mul_left 10 (by dsimp only [B]; omega))
      exact (left.trans (Nat.le_succ _)).trans taskWire
    have qb := (quarter (input, right)).trans (mQ sourceWire)
    have profile :
        ((NativeCertificate.ofPolyTime add).comp
          (original.snd.snd.prod (ClassBatches.quarterCertificate.comp original.fst))).time context+
        ((NativeCertificate.ofPolyTime add).comp
          (original.snd.snd.prod
            (ClassBatches.quarterCertificate.comp original.fst))).space context =
          4*(ec context).length+
          ClassBatches.quarterCertificate.time (input, right)+
          ClassBatches.quarterCertificate.space (input, right)+
          (NativeCertificate.ofPolyTime add).time (allowance, N)+
          (NativeCertificate.ofPolyTime add).space (allowance, N) := by
      dsimp only [original, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
        NativeCertificate.linear, NativeCertificate.congr, Function.comp_def, id_eq,
        context, JoinedDissection.probeContext, JoinedDissection.probeTask, allowance, N, right,
        ClassBatches.quarterVolume]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    have pos : 1 ≤ C := ClassBatches.capacity_pos context
    have qscale := Nat.mul_le_mul_left (Q (10*B)) pos
    have ascale := Nat.mul_le_mul_left (A (3*D B+1)) pos
    change _ ≤ C*P B
    dsimp only [P]
    nlinarith only [h.1, qb, atime, aspace, qscale, ascale]

private theorem count_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let q := as.length+bs.length+cs.length+ds.length
      i ∈ ClassBatches.labels context g.toNat →
      ClassBatches.countCertificate.time (context, g.toNat)+
          ClassBatches.countCertificate.space (context, g.toNat) ≤
        ClassBatches.capacity context*P ((ClassBalance.encoding input).length+q+p+1) := by
  delta ClassBatches.countCertificate
  extract_lets original ceil
  obtain ⟨D, hD, mD, data⟩ := context_bounds
  obtain ⟨K, hK, mK, capacity⟩ := capacity_bounds
  obtain ⟨Q, hQ, mQ, count⟩ := ProducerResources.projectedCount_bounds
  obtain ⟨A, hA, mA, division⟩ := exists_mono_poly_cert ceil
  let P := fun B => 100*(D B+K B+Q (10*B)+A (3*D B+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hk := mK hab
    have hq := mQ (Nat.mul_le_mul_left 10 hab)
    have ha := mA (by omega : 3*D a+1 ≤ 3*D b+1)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i
    dsimp only
    intro hi
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let C := ClassBatches.capacity context
    let N := ClassBatches.quarterVolume context
    let right := !(ClassBalance.retainRight input g.toNat)
    let pop := ClassBatches.population context g.toNat
    let args := (context, g.toNat)
    have h := data hp as bs cs ds s g i hi
    change (ec context).length ≤ C*D B ∧ _ at h
    have scalars : (encNat C).length+(encNat i).length+(encNat pop).length+
        (encNat g.toNat).length ≤ D B := h.2
    have pos : 1 ≤ C := ClassBatches.capacity_pos context
    have inputWire : (encPair ec encNat args).length ≤ C*(3*D B+2) := by
      have eq := length_encPair (enc₁ := ec) (enc₂ := encNat) args
      dsimp only [args] at eq
      rw [eq]
      have scale := Nat.mul_le_mul_left (D B+1) pos
      nlinarith only [h.1, scalars, scale]
    have cb := capacity hp as bs cs ds s g i hi
    change _ ≤ C*K B at cb
    have wire := ProducerResources.count_task_wire input g right
    have wire' :
        (encPair (encPair ClassBalance.encoding encBool) encNat
          ((input, right), g.toNat)).length+1 ≤
          10*B := wire.trans (Nat.mul_le_mul_left 10 (by dsimp only [B]; omega))
    have counted := count input right g.toNat
    change _ ≤ (N+1)*Q _ at counted
    have nle : N ≤ C := Nat.le_add_left _ _
    have actualCount := counted.trans
      (Nat.mul_le_mul (show N+1 ≤ 2*C by omega) (mQ wire'))
    have pairWire : (encPair encNat encNat (pop, C)).length ≤ 3*D B+1 := by
      rw [length_encPair]
      dsimp only
      omega
    have a := division (pop, C)
    have atime := a.1.trans (mA pairWire)
    have aspace := a.2.trans (mA pairWire)
    have populationProfile : ClassBatches.populationCertificate.time args+
        ClassBatches.populationCertificate.space args = 4*(encPair ec encNat args).length+
        ClassBalance.countCertificate.time ((input, right), g.toNat)+
        ClassBalance.countCertificate.space ((input, right), g.toNat) := by
      dsimp only [ClassBatches.populationCertificate, NativeCertificate.congr,
        NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear,
        Function.comp_def, id_eq, args, context, JoinedDissection.probeContext,
        JoinedDissection.probeTask, right]
      ring
    have profile :
        ((NativeCertificate.ofPolyTime ceil).comp (ClassBatches.populationCertificate.prod
          (ClassBatches.capacityCertificate.comp original.fst))).time args+
        ((NativeCertificate.ofPolyTime ceil).comp (ClassBatches.populationCertificate.prod
          (ClassBatches.capacityCertificate.comp original.fst))).space args =
          6*(encPair ec encNat args).length+
          ClassBalance.countCertificate.time ((input, right), g.toNat)+
          ClassBalance.countCertificate.space ((input, right), g.toNat)+
          ClassBatches.capacityCertificate.time context+
            ClassBatches.capacityCertificate.space context+
          (NativeCertificate.ofPolyTime ceil).time (pop, C)+
          (NativeCertificate.ofPolyTime ceil).space (pop, C) := by
      have eq :
          ((NativeCertificate.ofPolyTime ceil).comp (ClassBatches.populationCertificate.prod
            (ClassBatches.capacityCertificate.comp original.fst))).time args+
          ((NativeCertificate.ofPolyTime ceil).comp (ClassBatches.populationCertificate.prod
            (ClassBatches.capacityCertificate.comp original.fst))).space args =
          2*(encPair ec encNat args).length+
          (ClassBatches.populationCertificate.time args+
            ClassBatches.populationCertificate.space args)+
          ClassBatches.capacityCertificate.time context+
            ClassBatches.capacityCertificate.space context+
          (NativeCertificate.ofPolyTime ceil).time (pop, C)+
          (NativeCertificate.ofPolyTime ceil).space (pop, C) := by
        dsimp only [original, NativeCertificate.comp, NativeCertificate.prod,
          NativeCertificate.fst, NativeCertificate.post, NativeCertificate.linear,
          Function.comp_def, id_eq, args, pop, C]
        ring
      rw [eq, populationProfile]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    change _ ≤ C*P B
    have scale := Nat.mul_le_mul_left (A (3*D B+1)) pos
    dsimp only [P]
    nlinarith only [inputWire, cb, actualCount, atime, aspace, scale]

/-- The installed batch constructor composes real capacity arithmetic, quarter grouping,
window generation and original-state reconstruction. Copies of the full retained context
are charged linearly; scalar polynomials depend only on original physical input widths. -/
theorem batchCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let q := as.length+bs.length+cs.length+ds.length
      i ∈ ClassBatches.labels context g.toNat →
      ClassBatches.batchCertificate.time ((context, g.toNat), i)+
          ClassBatches.batchCertificate.space ((context, g.toNat), i) ≤
        ClassBatches.capacity context*P ((ClassBalance.encoding input).length+q+p+1) := by
  delta ClassBatches.batchCertificate
  extract_lets e original context capacity mul start bounds query groups selected
  obtain ⟨D, hD, mD, data⟩ := context_bounds
  obtain ⟨K, hK, mK, capacities⟩ := capacity_bounds
  obtain ⟨W, hW, mW, windows⟩ := RestartResources.original_window_bounds
  obtain ⟨R, hR, mR, reconstruct⟩ := ProducerResources.original_reconstruction_bounds
  obtain ⟨G, hG, mG, grouped⟩ := SearchResources.groupsCertificate_bounds
  obtain ⟨A, hA, mA, multiplication⟩ := exists_mono_poly_cert mul
  obtain ⟨Q, hQ, mQ, preparation⟩ := exists_mono_poly_cert ClassBalance.queryInput_polyTime
  obtain ⟨O, hO, mO, queryWire⟩ :=
    exists_mono_poly ClassBalance.queryInput_polyTime.polyBounded_length
  let P := fun B =>
    1000*(D B+K B+W B+R B+A (3*D B+1)+Q (10*B)+G (O (10*B)+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hk := mK hab
    have hw := mW hab
    have hr := mR hab
    have ha := mA (by omega : 3*D a+1 ≤ 3*D b+1)
    have hq := mQ (Nat.mul_le_mul_left 10 hab)
    have hg := mG (Nat.add_le_add_right (mO (Nat.mul_le_mul_left 10 hab)) 1)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i
    dsimp only
    intro hi
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let ctx := JoinedDissection.probeContext input g.toNat
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let C := ClassBatches.capacity ctx
    let N := ClassBatches.quarterVolume ctx
    let right := !(ClassBalance.retainRight input g.toNat)
    let args := ((ctx, g.toNat), i)
    let task := ((input, right), g.toNat)
    let queryInput := ClassBalance.queryInput input right g.toNat
    let emitted := ProducerResources.restartPairs input g.toNat i
    have d := data hp as bs cs ds s g i hi
    change (ec ctx).length ≤ C*D B ∧ _ at d
    have scalar : (encNat C).length+(encNat i).length+
        (encNat (ClassBatches.population ctx g.toNat)).length+(encNat g.toNat).length ≤ D B := d.2
    have positive : 1 ≤ C := ClassBatches.capacity_pos ctx
    have inputWire : (encPair (encPair ec encNat) encNat args).length ≤ C*(10*D B+10) := by
      have outer := length_encPair (enc₁ := encPair ec encNat) (enc₂ := encNat) args
      have inner := length_encPair (enc₁ := ec) (enc₂ := encNat) (ctx, g.toNat)
      dsimp only [args] at outer
      dsimp only at inner
      have scale := Nat.mul_le_mul_left (D B+1) positive
      nlinarith only [d.1, scalar, outer, inner, scale]
    have cap := capacities hp as bs cs ds s g i hi
    change _ ≤ C*K B at cap
    have pairWire : (encPair encNat encNat (i, C)).length ≤ 3*D B+1 := by
      rw [length_encPair]
      dsimp only
      omega
    have a := multiplication (i, C)
    have atime := a.1.trans (mA pairWire)
    have aspace := a.2.trans (mA pairWire)
    have taskWire : (encPair (encPair ClassBalance.encoding encBool) encNat task).length+1 ≤ 10*B :=
      (ProducerResources.count_task_wire input g right).trans
        (Nat.mul_le_mul_left 10 (by dsimp only [B]; omega))
    have taskWire' : (encPair (encPair ClassBalance.encoding encBool) encNat task).length ≤ 10*B :=
      (Nat.le_succ _).trans taskWire
    have prepared := preparation task
    have qtime := prepared.1.trans (mQ taskWire')
    have qspace := prepared.2.trans (mQ taskWire')
    have output := (queryWire task).trans (mO taskWire')
    have nle : N ≤ C := Nat.le_add_left _ _
    have groupBound := (grouped queryInput).trans
      (Nat.mul_le_mul (show ProducerResources.quarterVolume queryInput+1 ≤ 2*C by
        rw [ProducerResources.countVolume_eq]
        change N+1 ≤ 2*C
        omega) (mG (Nat.add_le_add_right output 1)))
    have window := windows hp as bs cs ds s g i hi
    have windowBound : RestartResources.windowAllowance input g.toNat i ≤ C*W B := by
      change _+RestartResources.windowAllowance input g.toNat i ≤ C*W B at window
      omega
    have pairsBound : emitted.length+1 ≤ 3*C := by
      have h := KeyJoinBatch.window_length (i*C, C) (JoinedProbe.groups ctx g.toNat)
      rw [ClassBatches.groups_length] at h
      change emitted.length ≤ C+N at h
      omega
    have reconstruction := (reconstruct hp as bs cs ds s g i).trans
      (Nat.mul_le_mul_right (R B) pairsBound)
    have profile : (ClassBalance.emitCertificate.comp (context.fst.prod selected)).time args+
        (ClassBalance.emitCertificate.comp (context.fst.prod selected)).space args =
        12*(encPair (encPair ec encNat) encNat args).length+
        2*(ClassBatches.capacityCertificate.time ctx+ClassBatches.capacityCertificate.space ctx)+
        (NativeCertificate.ofPolyTime mul).time (i, C)+
        (NativeCertificate.ofPolyTime mul).space (i, C)+
        (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).time task+
        (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).space task+
        ClassJoin.groupsCertificate.time queryInput+ClassJoin.groupsCertificate.space queryInput+
        RestartResources.windowAllowance input g.toNat i+
        ProducerResources.reconstructionAllowance input g.toNat i := by
      dsimp only [selected, groups, query, bounds, start, capacity, context, original,
        NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear,
        Function.comp_def, id_eq, args, ctx, task, queryInput, right, C, e,
        ClassBatches.ei, ec, JoinedProbe.groups,
        RestartResources.windowAllowance, ProducerResources.reconstructionAllowance,
        ProducerResources.restartPairs, JoinedDissection.probeContext,
        JoinedDissection.probeTask]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    have asc := Nat.mul_le_mul_left (A (3*D B+1)) positive
    have qsc := Nat.mul_le_mul_left (Q (10*B)) positive
    change _ ≤ C*P B
    dsimp only [P]
    nlinarith only [inputWire, cap, atime, aspace, qtime, qspace, groupBound,
      windowBound, reconstruction, asc, qsc]

/-- Complete installed label callback, including recomputed count/division, both physical
orientations of matching, retained-context frames and full-state batch reconstruction.
The outer generated-label loop is accounted for separately. -/
theorem matchLabelCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let q := as.length+bs.length+cs.length+ds.length
      i ∈ ClassBatches.labels context g.toNat →
      ClassBatches.matchLabelCertificate.time ((context, g.toNat), i)+
          ClassBatches.matchLabelCertificate.space ((context, g.toNat), i) ≤
        ClassBatches.capacity context*P ((ClassBalance.encoding input).length+q+p+1) := by
  delta ClassBatches.matchLabelCertificate
  extract_lets e original lt selected matched missing
  obtain ⟨D, hD, mD, data⟩ := context_bounds
  obtain ⟨K, hK, mK, counts⟩ := count_bounds
  obtain ⟨A, hA, mA, batches⟩ := batchCertificate_bounds
  obtain ⟨M, hM, mM, matching⟩ := MatcherResources.matchCertificate_bounds
  obtain ⟨L, hL, mL, comparison⟩ := exists_mono_poly_cert lt
  let P := fun B => 100*(D B+K B+A B+M (4*B+1)+L (3*D B+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hk := mK hab
    have ha := mA hab
    have hm := mM (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hab) 1)
    have hl := mL (by omega : 3*D a+1 ≤ 3*D b+1)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i
    dsimp only
    intro hi
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let ctx := JoinedDissection.probeContext input g.toNat
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let C := ClassBatches.capacity ctx
    let args := ((ctx, g.toNat), i)
    have d := data hp as bs cs ds s g i hi
    change (ec ctx).length ≤ C*D B ∧ _ at d
    have scalar : (encNat C).length+(encNat i).length+
        (encNat (ClassBatches.population ctx g.toNat)).length+(encNat g.toNat).length ≤ D B := d.2
    have positive : 1 ≤ C := ClassBatches.capacity_pos ctx
    have wire : (e args).length ≤ C*(10*D B+10) := by
      have outer := length_encPair (enc₁ := encPair ec encNat) (enc₂ := encNat) args
      have inner := length_encPair (enc₁ := ec) (enc₂ := encNat) (ctx, g.toNat)
      dsimp only [args] at outer
      dsimp only at inner
      have scale := Nat.mul_le_mul_left (D B+1) positive
      change (encPair (encPair ec encNat) encNat args).length ≤ _
      nlinarith only [d.1, scalar, outer, inner, scale]
    have cb := counts hp as bs cs ds s g i hi
    change _ ≤ C*K B at cb
    have bb := batches hp as bs cs ds s g i hi
    change _ ≤ C*A B at bb
    have countBound : ClassBatches.batchCount ctx g.toNat ≤ C :=
      (ClassBatches.batchCount_le_quarter ctx g.toNat).trans (Nat.le_add_left _ _)
    have pairWire : (encPair encNat encNat (i, ClassBatches.batchCount ctx g.toNat)).length ≤
        3*D B+1 := by
      have monotone := length_encNat_mono countBound
      rw [length_encPair]
      dsimp only
      omega
    have compared := comparison (i, ClassBatches.batchCount ctx g.toNat)
    have ltime := compared.1.trans (mL pairWire)
    have lspace := compared.2.trans (mL pairWire)
    let kept := ClassBalance.retain input g.toNat
    let batch := ClassBatches.batch ctx g.toNat i
    have originalWidth : m ≤ (ClassBalance.encoding input).length :=
      SearchResources.original_width (p := p) as bs cs ds s
    have rows (r : ℕ × ℕ) (hr : r ∈ kept++batch) : (er r).length ≤ 4*B+1 := by
      have original : (er r).length ≤ 2*m+1+q := by
        rcases List.mem_append.mp hr with retained | produced
        · exact ClassBalance.record_wire hp as bs cs ds s _ g r retained
        · exact ClassBalance.record_wire hp as bs cs ds s _ g r
            (ClassBatches.batch_sound ctx _ i r produced)
      dsimp only [B]
      omega
    have installed := matching m (4*B+1) (ClassBalance.retainRight input g.toNat)
      kept batch (by dsimp only [B]; omega) rows
    have volume : kept.length+batch.length+1 ≤ 4*C := by
      have capacity := JoinedDissection.restart_capacity_eq input g.toNat
      have batchSize := ClassBatches.batch_length ctx g.toNat i
      change C = kept.length+1+_ at capacity
      change batch.length ≤ C+_ at batchSize
      have quarter : ClassBatches.quarterVolume ctx ≤ C := Nat.le_add_left _ _
      omega
    have matchBound := installed.trans (Nat.mul_le_mul_right (M (4*B+1)) volume)
    change BatchedAccess.matchCertificate.time
        (BatchedAccess.parameters (JoinedDissection.probeTask input g.toNat), batch)+
      BatchedAccess.matchCertificate.space
        (BatchedAccess.parameters (JoinedDissection.probeTask input g.toNat), batch) ≤
      4*C*M (4*B+1) at matchBound
    have profile :
        (NativeCertificate.branch selected matched missing).time args+
          (NativeCertificate.branch selected matched missing).space args ≤
        6*(e args).length+
          ClassBatches.countCertificate.time (ctx, g.toNat)+
          ClassBatches.countCertificate.space (ctx, g.toNat)+
          (NativeCertificate.ofPolyTime lt).time (i, ClassBatches.batchCount ctx g.toNat)+
          (NativeCertificate.ofPolyTime lt).space (i, ClassBatches.batchCount ctx g.toNat)+
          ClassBatches.batchCertificate.time args+ClassBatches.batchCertificate.space args+
          BatchedAccess.matchCertificate.time
            (BatchedAccess.parameters (JoinedDissection.probeTask input g.toNat), batch)+
          BatchedAccess.matchCertificate.space
            (BatchedAccess.parameters (JoinedDissection.probeTask input g.toNat), batch) := by
      dsimp only [NativeCertificate.branch]
      split <;>
        dsimp only [selected, matched, missing, original, NativeCertificate.comp,
          NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
          NativeCertificate.post, NativeCertificate.linear, NativeCertificate.const,
          Function.comp_def, id_eq, args, batch, ctx, JoinedDissection.probeContext,
          JoinedDissection.probeTask, e, ClassBatches.ei]
      · omega
      · omega
    dsimp only [NativeCertificate.congr]
    have scale := Nat.mul_le_mul_left (L (3*D B+1)) positive
    change _ ≤ C*P B
    have coefficient : C*(60*D B+K B+A B+4*M (4*B+1)+2*L (3*D B+1)+60) ≤ C*P B :=
      Nat.mul_le_mul_left C (by dsimp only [P]; omega)
    dsimp only [P] at coefficient ⊢
    dsimp only [args, ctx, input] at profile wire cb bb ltime lspace matchBound ⊢
    refine profile.trans ?_
    nlinarith only [wire, cb, bb, ltime, lspace, matchBound, scale, coefficient]

/-- Actual label callback time plus all-prefix workspace, including its guarded producer and
matcher. The outer loop, retained preparation and ambient solver frames remain separate. -/
noncomputable def labelAllowance (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  let context := JoinedDissection.probeContext input g
  ClassBatches.matchLabelCertificate.time ((context, g), i)+
    ClassBatches.matchLabelCertificate.space ((context, g), i)

/-- All actual restarted-label callbacks, across both computed source orientations, have
half-exponential summed clocks and quarter-plus-balance simultaneous callback workspace.
This includes the formerly separate count/window/reconstruction/matcher profiles and their
retained-context frames. It does not yet charge the enclosing label loop or retained setup. -/
theorem source_label_bounds :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
        let original := Source.ofWords p s tail
        let input := Source.prepare original
        let I := (Source.encoding original).length
        (∑ g : BitVec (ClassBalance.depth input),
          ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
            (labelAllowance input g.toNat)).sum) ≤ 2^(tail.length/2)*P I ∧
        ∀ (g : BitVec (ClassBalance.depth input)) (i : ℕ),
          i ∈ ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat →
          labelAllowance input g.toNat i ≤
            (2^(tail.length/4)+ClassBalance.balance input)*P I :=
  RestartResources.source_capacity_bounds labelAllowance matchLabelCertificate_bounds

end Cslib.Cryptanalysis.AddXNOR.BatchResources
