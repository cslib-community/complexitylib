/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORBatchLoopResources
import all CslibFrontier.Cryptanalysis.AddXNORBatchLoopResources
import all CslibFrontier.Cryptanalysis.AddXNORBatchResources
import all CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Cryptanalysis.AddXNORWholeRunResources
import all CslibFrontier.Cryptanalysis.AddXNORBalanceResources
import all CslibFrontier.Cryptanalysis.AddXNORProducerResources
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Sharp original-input dissection resources

Compose retained preparation and actual restarted loops with the approved direct, balance
and whole-run certificates. `sourceCertificate_bounds` proves the installed uniform machine's
half-exponential time and quarter-exponential-plus-computed-balance simultaneous workspace.
All factors are polynomial in the physical original input: unary word width/requested depth
and the binary original-order operand list. The first operand is the seed, the target is zero,
and the machine computes the consecutive source quarter cut and caps depth at width and `q / 4`.
No direct-case restriction, semantic witness conclusion or desired runtime bound is a premise.

The source reachable-state-DP all-count and faster quarter-time prepass clauses of
[WangLvShenZhang2027], Lemma 8/Theorem 7, pp. 21–22 remain separate obligations. Thus these are
the worst-case time/space bounds of the actual original-input solver, not the complete source
Theorem 7 or whole-paper objective. The computational convention is deterministic multitape
bit cost (p. 6); native live-support bounds are not used as a substitute for internal space.

## Main results

* `source_restart_bounds`: summed actual selected restart clocks and maximum prefix workspace.
* `sourceCertificate_bounds`: preparation-to-readback bounds for the existing uniform certificate.

`JoinedDissection.original_correct` supplies original witness soundness and exhaustive misses
for the same function, without redoing or assuming its proof.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SourceResources
open Turing.MultiTapeTM Cslib.GenericRAM

private theorem task_wire (input : ClassStreaming.Input) (right : Bool)
    (kept : List (ℕ × ℕ)) (capacity : ℕ) :
    (BatchedAccess.taskEncoding (((input, right), kept), capacity)).length =
      8*(ClassStreaming.encoding input).length+2*(encNatPairList kept).length+
        (encNat capacity).length+11 := by
  simp only [BatchedAccess.taskEncoding, encNatPairList, length_encPair,
    encBool_apply, List.length_singleton, RadixPartition.recordEncoding]
  ring

private theorem batchSearch_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
      let Q := JoinedDissection.quarterBudget input
      JoinedDissection.batchSearchCertificate.time (input, g.toNat) ≤
          (Q+(ClassBatches.labels context g.toNat).length*ClassBatches.capacity context+1)*P B ∧
        JoinedDissection.batchSearchCertificate.space (input, g.toNat) ≤
          (Q+ClassBatches.capacity context+1)*P B := by
  delta JoinedDissection.batchSearchCertificate
  extract_lets original orientation streamed kept selected counts increment capacity task packed
    pe raw negation opposite parameter context prepared
  obtain ⟨D, hD, mD, data⟩ := BatchResources.context_bounds
  obtain ⟨A, hA, mA, components⟩ := SearchResources.original_components
  obtain ⟨S, hS, mS, streamBound⟩ := exists_mono_poly_cert JoinedDissection.classInput_polyTime
  obtain ⟨O, hO, mO, streamWire⟩ :=
    exists_mono_poly JoinedDissection.classInput_polyTime.polyBounded_length
  obtain ⟨I, hI, mI, increase⟩ := exists_mono_poly_cert increment
  obtain ⟨N, hN, mN, negate⟩ := exists_mono_poly_cert negation
  obtain ⟨R, hR, mR, running⟩ := BatchLoopResources.runCertificate_bounds
  let H := fun B => 1000*(D B+A B+S (3*B)+O (3*B)+I B+N (B+1)+B+1)
  let P := fun B => H B+R B
  have hH : PolynomiallyBounded H := by dsimp only [H]; fun_prop
  have mH : Monotone H := by
    intro a b hab
    have hd := mD hab
    have ha := mA hab
    have hs := mS (Nat.mul_le_mul_left 3 hab)
    have ho := mO (Nat.mul_le_mul_left 3 hab)
    have hi := mI hab
    have hn := mN (Nat.add_le_add_right hab 1)
    dsimp only [H]; omega
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.add_le_add (mH h) (mR h), ?_⟩
  intro m p hp as bs cs ds s g
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let ctx := JoinedDissection.probeContext input g.toNat
  let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
  let Q := JoinedDissection.quarterBudget input
  let C := ClassBatches.capacity ctx
  let r := ClassBalance.retainRight input g.toNat
  let dictionary := ClassBalance.retain input g.toNat
  let count := ClassBalance.count input r g.toNat
  let allocation := JoinedDissection.probeTask input g.toNat
  let source := (input, g.toNat)
  have cPos : 1 ≤ C := ClassBatches.capacity_pos ctx
  have nPos : 1 ≤ (ClassBatches.labels ctx g.toNat).length :=
    List.length_pos_of_mem (BatchLoopResources.zero_label ctx g.toNat)
  have d := data hp as bs cs ds s g 0 (BatchLoopResources.zero_label ctx g.toNat)
  change (JoinedProbe.encoding ctx).length ≤ C*D B ∧ _ at d
  have scalars : (encNat C).length+(encNat 0).length+
      (encNat (ClassBatches.population ctx g.toNat)).length+(encNat g.toNat).length ≤ D B := d.2
  have originalWidth : (ClassBalance.encoding input).length ≤ B := by dsimp only [B]; omega
  have label : (encNat g.toNat).length ≤ p := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
  have sourceWire : (JoinedDissection.classEncoding source).length ≤ 3*B := by
    have h := length_encPair (enc₁ := ClassBalance.encoding) (enc₂ := encNat) source
    dsimp only [source] at h
    change (encPair ClassBalance.encoding encNat source).length ≤ _
    dsimp only [B, source] at originalWidth ⊢
    omega
  have dictWire : (encNatPairList dictionary).length ≤ C*D B := by
    have h := BatchResources.context_wire_eq input (!r) r m dictionary (count+1)
    change (JoinedProbe.encoding ctx).length = _ at h
    omega
  have countLe : count+1 ≤ C := Nat.le_add_right _ _
  have countWidth := BalanceResources.count_wire hp as bs cs ds s r g
  change (encNat count).length ≤ as.length+bs.length+cs.length+ds.length+1 at countWidth
  have countWidth' : (encNat count).length ≤ B := by dsimp only [B]; omega
  have allowanceWidth : (encNat (count+1)).length ≤ D B :=
    (length_encNat_mono countLe).trans (by omega)
  have output := (streamWire source).trans (mO sourceWire)
  have allocationWire : (BatchedAccess.taskEncoding allocation).length ≤
      C*(8*O (3*B)+3*D B+11) := by
    have h := task_wire (JoinedDissection.classInput input g.toNat) r dictionary (count+1)
    change (BatchedAccess.taskEncoding allocation).length = _ at h
    have scale := Nat.mul_le_mul_left (8*O (3*B)+D B+11) cPos
    nlinarith only [h, output, dictWire, allowanceWidth, scale]
  have packedWire : (pe (input, allocation)).length ≤ C*(8*O (3*B)+3*D B+2*B+12) := by
    have h := length_encPair (enc₁ := ClassBalance.encoding)
      (enc₂ := BatchedAccess.taskEncoding) (input, allocation)
    dsimp only at h
    have scale := Nat.mul_le_mul_left (2*B+1) cPos
    change (encPair ClassBalance.encoding BatchedAccess.taskEncoding
      (input, allocation)).length ≤ _
    nlinarith only [h, allocationWire, originalWidth, scale]
  with_reducible
    have component := components hp as bs cs ds s g
    change _ ≤ (Q+1)*A B ∧ _ at component
    have oriented := component.1
    have counted := (component.2 r).1
    change _ ≤ (Q+1)*A B at counted
    have retained := (component.2 r).2
    change _ ≤ (Q+count+1)*A B at retained
    have retainedBound : ClassBalance.recordsCertificate.time ((input, r), g.toNat)+
        ClassBalance.recordsCertificate.space ((input, r), g.toNat) ≤ (Q+C)*A B :=
      retained.trans (Nat.mul_le_mul_right (A B) (by omega))
  have stream := streamBound source
  have st := stream.1.trans (mS sourceWire)
  have ss := stream.2.trans (mS sourceWire)
  have inc := increase count
  have it := inc.1.trans (mI countWidth')
  have isp := inc.2.trans (mI countWidth')
  have neg := negate r
  have small : (encBool r).length ≤ B+1 := by
    simp only [encBool_apply, List.length_singleton]
    omega
  have nt := neg.1.trans (mN small)
  have ns := neg.2.trans (mN small)
  have setup : (prepared.prod original.snd).time source+
      (prepared.prod original.snd).space source ≤ (Q+C+1)*H B := by
    have profile : (prepared.prod original.snd).time source+
        (prepared.prod original.snd).space source =
        12*(JoinedDissection.classEncoding source).length+
        (NativeCertificate.ofPolyTime JoinedDissection.classInput_polyTime).time source+
        (NativeCertificate.ofPolyTime JoinedDissection.classInput_polyTime).space source+
        3*(ClassBalance.orientationCertificate.time source+
          ClassBalance.orientationCertificate.space source)+
        ClassBalance.recordsCertificate.time ((input, r), g.toNat)+
        ClassBalance.recordsCertificate.space ((input, r), g.toNat)+
        ClassBalance.countCertificate.time ((input, r), g.toNat)+
        ClassBalance.countCertificate.space ((input, r), g.toNat)+
        (NativeCertificate.ofPolyTime increment).time count+
        (NativeCertificate.ofPolyTime increment).space count+
        8*(pe (input, allocation)).length+
        (NativeCertificate.ofPolyTime negation).time r+
        (NativeCertificate.ofPolyTime negation).space r+
        6*(BatchedAccess.taskEncoding allocation).length := by
      dsimp only [prepared, context, parameter, opposite, raw, pe, packed, task, capacity,
        counts, selected, kept, streamed, orientation, original,
          BatchedAccess.parametersCertificate,
        ClassBalance.retainCertificate, NativeCertificate.congr, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
        NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq,
        source, allocation, r, count, JoinedDissection.probeTask, ClassBalance.retain]
      ring
    rw [profile]
    have large : 1 ≤ Q+C+1 := by omega
    have cb : C ≤ Q+C+1 := by omega
    have qb : Q+1 ≤ Q+C+1 := by omega
    have rb : Q+C ≤ Q+C+1 := by omega
    have a := Nat.mul_le_mul_right (A B) qb
    have b := Nat.mul_le_mul_right (A B) rb
    have frames := Nat.mul_le_mul_right (8*(8*O (3*B)+3*D B+2*B+12)+
      6*(8*O (3*B)+3*D B+11)) cb
    have scalar := Nat.mul_le_mul_left (36*B+2*S (3*B)+2*I B+2*N (B+1)) large
    have coefficient : (Q+C+1)*(36*B+2*S (3*B)+2*I B+2*N (B+1)+
        5*A B+8*(8*O (3*B)+3*D B+2*B+12)+6*(8*O (3*B)+3*D B+11)) ≤ (Q+C+1)*H B :=
      Nat.mul_le_mul_left _ (by dsimp only [H]; omega)
    dsimp only [source, input] at sourceWire oriented counted retainedBound st ss packedWire ⊢
    have clocks :
        12*(JoinedDissection.classEncoding (input, g.toNat)).length+
        (NativeCertificate.ofPolyTime JoinedDissection.classInput_polyTime).time (input, g.toNat)+
        (NativeCertificate.ofPolyTime JoinedDissection.classInput_polyTime).space (input, g.toNat)+
        3*(ClassBalance.orientationCertificate.time (input, g.toNat)+
          ClassBalance.orientationCertificate.space (input, g.toNat))+
        ClassBalance.recordsCertificate.time ((input, r), g.toNat)+
        ClassBalance.recordsCertificate.space ((input, r), g.toNat)+
        ClassBalance.countCertificate.time ((input, r), g.toNat)+
        ClassBalance.countCertificate.space ((input, r), g.toNat)+
        (NativeCertificate.ofPolyTime increment).time count+
        (NativeCertificate.ofPolyTime increment).space count+
        8*(pe (input, allocation)).length+(NativeCertificate.ofPolyTime negation).time r+
        (NativeCertificate.ofPolyTime negation).space r+
          6*(BatchedAccess.taskEncoding allocation).length ≤
      36*B+2*S (3*B)+3*((Q+1)*A B)+(Q+C)*A B+(Q+1)*A B+2*I B+
        8*(C*(8*O (3*B)+3*D B+2*B+12))+2*N (B+1)+6*(C*(8*O (3*B)+3*D B+11)) := by
      dsimp only [input]
      omega
    with_reducible refine clocks.trans ?_
    nlinarith only [a, b, frames, scalar, coefficient]
  have run := running hp as bs cs ds s g
  change _ ≤ (ClassBatches.labels ctx g.toNat).length*C*R B ∧ _ ≤ C*R B at run
  have timeEq : (ClassBatches.runCertificate.comp (prepared.prod original.snd)).time source =
      (prepared.prod original.snd).time source+ClassBatches.runCertificate.time (ctx, g.toNat) := by
    dsimp only [NativeCertificate.comp]
    congr 2
  have spaceEq : (ClassBatches.runCertificate.comp (prepared.prod original.snd)).space source =
      (prepared.prod original.snd).space source+ClassBatches.runCertificate.space (ctx,
        g.toNat) := by
    dsimp only [NativeCertificate.comp]
    congr 2
  dsimp only [NativeCertificate.congr]
  rw [timeEq, spaceEq]
  have capacityScale := Nat.mul_le_mul_left C nPos
  have timeScale := Nat.mul_le_mul_right (H B) (show Q+C+1 ≤
    Q+(ClassBatches.labels ctx g.toNat).length*C+1 by nlinarith only [capacityScale])
  have timeRun := Nat.mul_le_mul_right (R B) (show (ClassBatches.labels ctx g.toNat).length*C ≤
    Q+(ClassBatches.labels ctx g.toNat).length*C+1 by omega)
  have spaceRun := Nat.mul_le_mul_right (R B) (show C ≤ Q+C+1 by omega)
  dsimp only [P]
  constructor
  · nlinarith only [setup, run.1, timeScale, timeRun]
  · nlinarith only [setup, run.2, spaceRun]

private theorem selected_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
      let Q := JoinedDissection.quarterBudget input
      (if JoinedDissection.materialize input g.toNat then 0 else
        JoinedDissection.searchCertificate.time (input, g.toNat)) ≤
          (Q+JoinedDissection.restartCopyWork input g.toNat+1)*P B ∧
      (if JoinedDissection.materialize input g.toNat then 0 else
        JoinedDissection.searchCertificate.space (input, g.toNat)) ≤
          (Q+ClassBalance.balance input+1)*P B := by
  obtain ⟨A, hA, mA, batches⟩ := batchSearch_bounds
  obtain ⟨M, hM, mM, tests⟩ := SearchResources.materialize_bounds
  let P := fun B => 2*(A B+M B)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 2 (Nat.add_le_add (mA h) (mM h)), ?_⟩
  intro m p hp as bs cs ds s g
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let ctx := JoinedDissection.probeContext input g.toNat
  let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
  let Q := JoinedDissection.quarterBudget input
  let C := ClassBatches.capacity ctx
  have batch := batches hp as bs cs ds s g
  have test := tests hp as bs cs ds s g
  change _ ≤ (Q+1)*M B at test
  change _ ≤ (Q+(ClassBatches.labels ctx g.toNat).length*C+1)*A B ∧
    _ ≤ (Q+C+1)*A B at batch
  have capacity := JoinedDissection.restart_capacity_eq input g.toNat
  have kept := ClassBalance.class_le_balance input g.toNat g.isLt
  have quarter := JoinedDissection.restart_quarter_le input g.toNat
  have cap : C ≤ ClassBalance.balance input+Q+1 := by
    change C = _ at capacity
    omega
  with_reducible
    change (if JoinedDissection.materialize input g.toNat then 0 else
      JoinedDissection.searchCertificate.time (input, g.toNat)) ≤
        (Q+JoinedDissection.restartCopyWork input g.toNat+1)*P B ∧
      (if JoinedDissection.materialize input g.toNat then 0 else
        JoinedDissection.searchCertificate.space (input, g.toNat)) ≤
        (Q+ClassBalance.balance input+1)*P B
  cases h : JoinedDissection.materialize input g.toNat with
  | true => simp only [ite_true]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [JoinedDissection.searchCertificate, NativeCertificate.congr,
      NativeCertificate.branch]
    simp only [h, Bool.false_eq_true, ite_false]
    have timeScale := Nat.mul_le_mul_right (M B)
      (show Q+1 ≤ Q+(ClassBatches.labels ctx g.toNat).length*C+1 by omega)
    have spaceScale := Nat.mul_le_mul_right (A B)
      (show Q+C+1 ≤ 2*(Q+ClassBalance.balance input+1) by omega)
    have testScale := Nat.mul_le_mul_right (M B)
      (show Q+1 ≤ 2*(Q+ClassBalance.balance input+1) by omega)
    dsimp only [JoinedDissection.restartCopyWork, P]
    constructor
    · nlinarith only [test, batch.1, timeScale,
        Nat.zero_le ((Q+(ClassBatches.labels ctx g.toNat).length*C+1)*A B),
        Nat.zero_le ((Q+(ClassBatches.labels ctx g.toNat).length*C+1)*M B)]
    · nlinarith only [test, batch.2, spaceScale, testScale]

/-- Actual selected restarted searches, including retained preparation, generated labels,
parking, every internal callback/frame and output, normalized in original source bits.
The maximum is simultaneous workspace; early exits only omit calls from the time sum. -/
theorem source_restart_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let input := Source.prepare original
      let I := (Source.encoding original).length
      SearchResources.restartTime input ≤ 2^(tail.length/2)*P I ∧
        SearchResources.restartSpace input ≤
          (2^(tail.length/4)+ClassBalance.balance input)*P I := by
  obtain ⟨A, hA, mA, selected⟩ := selected_bounds
  obtain ⟨L, hL, mL, layout⟩ := WholeRunResources.sourceScalarWidth
  have capacityLinear : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
        (g : BitVec p) (i : ℕ),
        let input := ProgramGeneration.originalSource p as bs cs ds s 0
        let context := JoinedDissection.probeContext input g.toNat
        let q := as.length+bs.length+cs.length+ds.length
        i ∈ ClassBatches.labels context g.toNat →
        ClassBatches.capacity context ≤ ClassBatches.capacity context*
          P ((ClassBalance.encoding input).length+q+p+1) := by
    refine ⟨fun _ => 1, by fun_prop, fun _ _ _ => le_rfl, ?_⟩
    intro m p hp as bs cs ds s g i
    dsimp only
    intro _
    exact Nat.le_mul_of_pos_right _ (by decide)
  obtain ⟨D, hD, mD, copies⟩ := RestartResources.source_capacity_bounds
    (fun input g _ => ClassBatches.capacity (JoinedDissection.probeContext input g)) capacityLinear
  let P := fun I => 100*(D I+1)*(A (L I)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 100 (Nat.add_le_add_right (mD hab) 1))
      (Nat.add_le_add_right (mA (mL hab)) 1)
  · intro m p s tail
    let original := Source.ofWords p s tail
    let input := Source.prepare original
    let I := (Source.encoding original).length
    let d := min p (min m (tail.length/4))
    let Q := JoinedDissection.quarterBudget input
    let G := 2^d
    let quarter := 2^(tail.length/4)
    let half := 2^(tail.length/2)
    have hp : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    have hk : d ≤ tail.length/4 := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
    have preparedEq : input = ProgramGeneration.originalSource d
        (Source.quarters tail).1.1 (Source.quarters tail).1.2
        (Source.quarters tail).2.1 (Source.quarters tail).2.2 s 0 := Source.prepare_ofWords p s tail
    have depthEq : ClassBalance.depth input = d := by rw [preparedEq]; rfl
    have total := congrArg List.length (Source.quarters_append tail)
    simp only [List.length_append] at total
    have total' : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
        (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length = tail.length :=
          by omega
    have scalar : (ClassBalance.encoding input).length+tail.length+d+1 ≤ L I := by
      have h := layout m p s tail
      change (ClassBalance.encoding input).length+tail.length+
        ClassBalance.depth input+1 ≤ L I at h
      rw [depthEq] at h
      exact h
    have each (g : BitVec d) :
        (if JoinedDissection.materialize input g.toNat then 0 else
          JoinedDissection.searchCertificate.time (input, g.toNat)) ≤
            (Q+JoinedDissection.restartCopyWork input g.toNat+1)*A (L I) ∧
        (if JoinedDissection.materialize input g.toNat then 0 else
          JoinedDissection.searchCertificate.space (input, g.toNat)) ≤
            (Q+ClassBalance.balance input+1)*A (L I) := by
      have actual := selected hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
        (Source.quarters tail).2.1 (Source.quarters tail).2.2 s g
      dsimp only at actual
      rw [← preparedEq, total'] at actual
      exact ⟨actual.1.trans (Nat.mul_le_mul_left _ (mA scalar)),
        actual.2.trans (Nat.mul_le_mul_left _ (mA scalar))⟩
    have quarterBound : Q ≤ 11*quarter := JoinedDissection.quarterBudget_source p s tail
    have labelBound : G ≤ quarter := Nat.pow_le_pow_right (by decide) hk
    have positive : 1 ≤ quarter := Nat.two_pow_pos _
    have square : quarter*quarter ≤ half := by
      dsimp only [quarter, half]
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have baseWork : G*(Q+1) ≤ 12*half := by
      have h := Nat.mul_le_mul labelBound (show Q+1 ≤ 12*quarter by omega)
      nlinarith only [h, square]
    have copyWork : (∑ g : BitVec d, JoinedDissection.restartCopyWork input g.toNat) ≤
      half*D I := by
      have h := (copies m p s tail).1
      change (∑ g : BitVec (ClassBalance.depth input),
        ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
          (fun _ => ClassBatches.capacity
            (JoinedDissection.probeContext input g.toNat))).sum) ≤ _ at h
      simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
      rw [depthEq] at h
      exact h
    have sums (f : ℕ → ℕ) : (∑ g : BitVec d, f g.toNat) =
        ∑ g ∈ Finset.range (2^d), f g :=
      (Fintype.sum_equiv BitVec.equivFin.toEquiv _ (fun g => f g.val) (fun _ => rfl)).trans
        (Fin.sum_univ_eq_sum_range f _)
    constructor
    · have h := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => (each g).1)
      rw [← Finset.sum_mul, sums (fun n => if JoinedDissection.materialize input n then 0 else
        JoinedDissection.searchCertificate.time (input, n))] at h
      have volume : (∑ g : BitVec d, (Q+JoinedDissection.restartCopyWork input g.toNat+1)) =
          G*(Q+1)+(∑ g : BitVec d, JoinedDissection.restartCopyWork input g.toNat) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin, Nat.cast_id]
        dsimp only [G]
        ring
      rw [volume] at h
      change SearchResources.restartTime input ≤ half*P I
      dsimp only [SearchResources.restartTime]
      rw [depthEq]
      dsimp only [P]
      nlinarith only [h, baseWork, copyWork, Nat.zero_le (half*A (L I)),
        Nat.zero_le (half*D I*A (L I))]
    · change SearchResources.restartSpace input ≤ (quarter+ClassBalance.balance input)*P I
      dsimp only [SearchResources.restartSpace]
      rw [depthEq]
      apply Finset.sup_le
      intro n hn
      have hn' : n < 2^d := Finset.mem_range.mp hn
      let g := BitVec.ofNat d n
      have natEq : g.toNat = n := Nat.mod_eq_of_lt hn'
      have h := (each g).2
      rw [natEq] at h
      have workspace : Q+ClassBalance.balance input+1 ≤ 12*(quarter+
        ClassBalance.balance input) := by
        omega
      have upper := h.trans (Nat.mul_le_mul_right (A (L I)) workspace)
      dsimp only [P]
      nlinarith only [upper, Nat.zero_le ((quarter+ClassBalance.balance input)*D I),
        Nat.zero_le ((quarter+ClassBalance.balance input)*D I*A (L I))]

/-- The actual uniform original-input dissection certificate has half-exponential bit time
and quarter-exponential-plus-computed-balance simultaneous space, including preparation,
retention, both search directions, early-hit parking, release and witness readback. Polynomial
factors depend only on the physical original input. This proves the worst-case resource bounds
of the source dissection, not its faster balance-prepass or reachable-state-DP clauses. -/
theorem sourceCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let input := Source.prepare original
      let I := (Source.encoding original).length
      JoinedDissection.sourceCertificate.time original ≤ 2^(tail.length/2)*P I ∧
        JoinedDissection.sourceCertificate.space original ≤
          (2^(tail.length/4)+ClassBalance.balance input)*P I := by
  obtain ⟨A, hA, mA, restarts⟩ := source_restart_bounds
  obtain ⟨W, hW, mW, whole⟩ := SearchResources.sourceCertificate_restart_bounds
  let P := fun I => (A I+1)*(W I+1)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul (Nat.add_le_add_right (mA h) 1)
      (Nat.add_le_add_right (mW h) 1), ?_⟩
  intro m p s tail
  let I := (Source.encoding (Source.ofWords p s tail)).length
  have r := restarts m p s tail
  have w := whole m p s tail
  dsimp only at r w ⊢
  constructor
  · have h := w.1.trans (Nat.mul_le_mul_right (W I) (Nat.add_le_add_right r.1 _))
    dsimp only [P]
    nlinarith only [h, Nat.zero_le (2^(tail.length/2)*(A I+1))]
  · have h := w.2.trans (Nat.mul_le_mul_right (W I)
      (Nat.add_le_add_right (Nat.add_le_add_right r.2 _) _))
    dsimp only [P]
    nlinarith only [h, Nat.zero_le ((2^(tail.length/4)+ClassBalance.balance (Source.prepare
      (Source.ofWords p s tail)))*(A I+1))]

end Cslib.Cryptanalysis.AddXNOR.SourceResources
