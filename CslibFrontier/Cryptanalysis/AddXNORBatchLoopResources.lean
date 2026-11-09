/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORBatchResources
public import CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Cryptanalysis.AddXNORBatchResources
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Generated-label loop resources for source dissection

Charge actual index generation, option parking and retained-context frames around the
installed restarted callbacks. Prefix states are derived from actual matching soundness.
This is original resource accounting towards [WangLvShenZhang2027], Lemma 8/Theorem 7,
pp. 21–22, in the deterministic multitape bit model on p. 6.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.BatchLoopResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev ei := encPair JoinedProbe.encoding encNat
private abbrev eo := encNatPairOption

private theorem zero_label (context : JoinedProbe.Context) (g : ℕ) :
    0 ∈ ClassBatches.labels context g := by
  simp only [ClassBatches.labels, SortedQuarterMachine.indices_eq_range, List.mem_range]
  exact Nat.two_pow_pos _

private abbrev labelStep (context : JoinedProbe.Context) (g : ℕ)
    (found : Option (ℕ × ℕ)) (i : ℕ) : Option (ℕ × ℕ) :=
  found.orElse (fun _ => ClassBatches.matchLabel context g i)

/-- Every parked prefix contains at most one actual packed witness. Its physical width is
proved from generated full-state records, not supplied as a loop invariant. -/
theorem prefix_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (xs : List ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
    (encNatPairOption (xs.foldl (fun found i =>
      found.orElse (fun _ => ClassBatches.matchLabel context g.toNat i)) none)).length ≤ 12*B+
        5 := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let context := JoinedDissection.probeContext input g.toNat
  let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
  have originalWidth : m ≤ (ClassBalance.encoding input).length :=
    SearchResources.original_width (p := p) as bs cs ds s
  have calls (i : ℕ) : (eo (ClassBatches.matchLabel context g.toNat i)).length ≤ 12*B+5 := by
    cases h : ClassBatches.matchLabel context g.toNat i with
    | none => simp [eo]
    | some out =>
      have hit := h
      dsimp only [ClassBatches.matchLabel] at hit
      split at hit
      · obtain ⟨a, ha, b, hb, _, ho⟩ := BatchedAccess.match_sound _ _ out hit
        have aw := ClassBalance.record_wire hp as bs cs ds s
          (ClassBalance.retainRight input g.toNat) g a ha
        have bw := ClassBalance.record_wire hp as bs cs ds s
          (!(ClassBalance.retainRight input g.toNat)) g b
          (ClassBatches.batch_sound context _ i b hb)
        have ap := (length_le_encPair_right encNat encNat a).trans aw
        have bp := (length_le_encPair_right encNat encNat b).trans bw
        have scale : 2*m+1+(as.length+bs.length+cs.length+ds.length) ≤ 4*B+1 := by
          dsimp only [B]
          omega
        have ap' := ap.trans scale
        have bp' := bp.trans scale
        simp only [eo, encNatPairOption, encOption_some, List.length_cons, ho]
        split <;> simp only [length_encPair] <;> omega
      · simp at hit
  exact List.foldlRecOn (motive := fun found => (eo found).length ≤ 12*B+5)
    xs (labelStep context g.toNat) (by simp [eo])
    (fun found hf i _ => by
      cases found with
      | none => exact calls i
      | some out => exact hf)

private theorem round_profile (parameter : JoinedProbe.Context × ℕ)
    (state : Option (ℕ × ℕ)) (i : ℕ) :
    ClassBatches.roundCertificate.time ((parameter, state), i)+
      ClassBatches.roundCertificate.space ((parameter, state), i) ≤
    10*(NativeCertificate.encFoldStep ei eo encNat ((parameter, state), i)).length+
      2*(eo state).length+
      ClassBatches.matchLabelCertificate.time (parameter, i)+
      ClassBatches.matchLabelCertificate.space (parameter, i) := by
  delta ClassBatches.roundCertificate
  extract_lets e arg fresh found parked
  let argument := ((parameter, state), i)
  cases hs : state with
  | none =>
    dsimp only [NativeCertificate.congr, found, fresh, arg, NativeCertificate.option,
      NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
      NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear,
      Function.comp_def, id_eq]
    simp only [Option.elim_none]
    dsimp only [e, NativeCertificate.encFoldStep, ei, eo, encNatPairOption, ClassBatches.ei,
      ClassBatches.er, ClassBatches.ec]
    omega
  | some out =>
    have pairWire := length_encPair (enc₁ := e) (enc₂ := ClassBatches.er)
      (((parameter, some out), i), out)
    have foundWire : (eo (some out)).length = (ClassBatches.er out).length+1 := by
      simp only [eo, encNatPairOption, encOption_some, List.length_cons]
    dsimp only [NativeCertificate.congr, found, fresh, parked, arg, NativeCertificate.option,
      NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
      NativeCertificate.snd, NativeCertificate.some, NativeCertificate.post,
      NativeCertificate.linear, Function.comp_def, id_eq]
    simp only [Option.elim_some]
    dsimp only [e, NativeCertificate.encFoldStep, ei, eo, encNatPairOption, ClassBatches.ei,
      ClassBatches.er, ClassBatches.ec]
      at pairWire foundWire ⊢
    omega

private theorem round_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ) (state : Option (ℕ × ℕ)),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
      i ∈ ClassBatches.labels context g.toNat → (eo state).length ≤ 12*B+5 →
      ClassBatches.roundCertificate.time (((context, g.toNat), state), i)+
        ClassBatches.roundCertificate.space (((context, g.toNat), state), i) ≤
          ClassBatches.capacity context*P B := by
  obtain ⟨D, hD, mD, data⟩ := BatchResources.context_bounds
  obtain ⟨A, hA, mA, callbacks⟩ := BatchResources.matchLabelCertificate_bounds
  let P := fun B => 1000*(D B+A B+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mD hab; have := mA hab; dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i state
    dsimp only
    intro hi sw
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
    let C := ClassBatches.capacity context
    let parameter : JoinedProbe.Context × ℕ := (context, g.toNat)
    let argument := ((parameter, state), i)
    change (eo state).length ≤ 12*B+5 at sw
    have cPos : 1 ≤ C := ClassBatches.capacity_pos context
    have d := data hp as bs cs ds s g i hi
    change (JoinedProbe.encoding context).length ≤ C*D B ∧ _ at d
    have scalars : (encNat C).length+(encNat i).length+
        (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length ≤
          D B := d.2
    have controlWire : (ei parameter).length ≤ C*(3*D B+2) := by
      have h := length_encPair (enc₁ := JoinedProbe.encoding) (enc₂ := encNat) parameter
      dsimp only [parameter] at h
      have scale := Nat.mul_le_mul_left (D B+1) cPos
      change (encPair JoinedProbe.encoding encNat parameter).length ≤ _
      nlinarith only [h, d.1, scalars, scale]
    have iw : (encNat i).length ≤ D B := by omega
    have body := callbacks hp as bs cs ds s g i hi
    change _ ≤ C*A B at body
    have wire : (NativeCertificate.encFoldStep ei eo encNat argument).length ≤ C*(20*D B+40*B+
      40) := by
      have h := length_encPair (enc₁ := encPair ei eo) (enc₂ := encNat) argument
      have h' := length_encPair (enc₁ := ei) (enc₂ := eo) (parameter, state)
      dsimp only [argument] at h
      dsimp only at h'
      change (encPair (encPair ei eo) encNat argument).length ≤ _
      have scale := Nat.mul_le_mul_left (D B+B+1) cPos
      dsimp only [argument]
      nlinarith only [h, h', controlWire, sw, iw, scale]
    have profile := round_profile parameter state i
    have extra : C*(10*(20*D B+40*B+40)+24*B+10+A B) ≤ C*P B :=
      Nat.mul_le_mul_left C (by dsimp only [P]; omega)
    have scale := Nat.mul_le_mul_left (12*B+5) cPos
    change _ ≤ C*P B
    dsimp only [argument, parameter, context, input] at profile wire body sw ⊢
    with_reducible refine profile.trans ?_
    nlinarith only [wire, sw, body, extra, scale]

private theorem setup_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
      ClassBatches.setupCertificate.time (context, g.toNat)+
        ClassBatches.setupCertificate.space (context, g.toNat) ≤
          ClassBatches.capacity context*P B := by
  delta ClassBatches.setupCertificate
  extract_lets original power generation generated indices initial
  obtain ⟨D, hD, mD, data⟩ := BatchResources.context_bounds
  obtain ⟨H, hH, mH, counts⟩ := BatchResources.count_bounds
  obtain ⟨V, hV, mV, sizeBound⟩ := exists_mono_poly_cert ComputableInPolyTime.binary_size
  let J := Classical.choose SortedQuarterMachine.indices_computable
  have hJ : PolynomiallyBounded J :=
    (Classical.choose_spec SortedQuarterMachine.indices_computable).1
  have mJ : Monotone J := (Classical.choose_spec SortedQuarterMachine.indices_computable).2.1
  let P := fun B => 100*(D B+H B+V (D B)+(D B+1)*J (D B+1)+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hh := mH hab
    have hv := mV hd
    have hj := Nat.mul_le_mul (Nat.add_le_add_right hd 1) (mJ (Nat.add_le_add_right hd 1))
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
    let C := ClassBatches.capacity context
    let parameter : JoinedProbe.Context × ℕ := (context, g.toNat)
    let rows := ClassBatches.labels context g.toNat
    let n := rows.length
    let w := (ClassBatches.batchCount context g.toNat).size
    have cPos : 1 ≤ C := ClassBatches.capacity_pos context
    have nPos : 1 ≤ n := List.length_pos_of_mem (zero_label context g.toNat)
    have d := data hp as bs cs ds s g 0 (zero_label context g.toNat)
    change (JoinedProbe.encoding context).length ≤ C*D B ∧ _ at d
    have scalars : (encNat C).length+(encNat 0).length+
        (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length ≤
          D B := d.2
    have controlWire : (ei parameter).length ≤ C*(3*D B+2) := by
      have h := length_encPair (enc₁ := JoinedProbe.encoding) (enc₂ := encNat) parameter
      dsimp only [parameter] at h
      have scale := Nat.mul_le_mul_left (D B+1) cPos
      change (encPair JoinedProbe.encoding encNat parameter).length ≤ _
      nlinarith only [h, d.1, scalars, scale]
    have countLe : ClassBatches.batchCount context g.toNat ≤ C :=
      (ClassBatches.batchCount_le_quarter context g.toNat).trans (Nat.le_add_left _ _)
    have width : w ≤ D B := by
      have h := Nat.size_le_size countLe
      have cw : (encNat C).length ≤ D B := by omega
      rw [encNat_apply, Nat.size_eq_bits_len] at cw
      exact h.trans cw
    have rowLen : n = 2^w := (SortedQuarterMachine.indices_wire w).1
    have rowCount : n ≤ 4*C := by
      have bound := (ClassBatches.pow_size (ClassBatches.batchCount context g.toNat)).trans
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_right countLe 1))
      rw [← rowLen] at bound
      omega
    have count := counts hp as bs cs ds s g 0 (zero_label context g.toNat)
    change _ ≤ C*H B at count
    have sizeWire : (encNat (ClassBatches.batchCount context g.toNat)).length ≤ D B := by
      exact (length_encNat_mono countLe).trans (show (encNat C).length ≤ D B by omega)
    have size := sizeBound (ClassBatches.batchCount context g.toNat)
    have sizeT := size.1.trans (mV sizeWire)
    have sizeS := size.2.trans (mV sizeWire)
    have generationBound := mJ (Nat.add_le_add_right width 1)
    have timeGen := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right width 1) rowCount) generationBound
    have spaceGen := Nat.mul_le_mul rowCount generationBound
    have setupEq :
        (original.prod (initial.prod indices)).time parameter+
          (original.prod (initial.prod indices)).space parameter =
        4*(ei parameter).length+
        ClassBatches.countCertificate.time parameter+ClassBatches.countCertificate.space parameter+
        (NativeCertificate.ofPolyTime ComputableInPolyTime.binary_size).time
          (ClassBatches.batchCount context g.toNat)+
        (NativeCertificate.ofPolyTime ComputableInPolyTime.binary_size).space
          (ClassBatches.batchCount context g.toNat)+
        (w+1)*n*J (w+1)+n*J (w+1) := by
      dsimp only [original, initial, indices, power, generated, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.const, NativeCertificate.linear,
        Function.comp_def, id_eq, parameter, n, rows, w, J, ClassBatches.labels]
      simp only [SortedQuarterMachine.indices_eq_range, List.length_range]
      ring
    dsimp only [NativeCertificate.congr]
    rw [setupEq]
    have scale := Nat.mul_le_mul_left (V (D B)) cPos
    have jscale : 4*C*J (D B+1) ≤ 4*C*((D B+1)*J (D B+1)) := by
      apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_left _ (by omega)
    have coefficient : C*(4*(3*D B+2)+H B+2*V (D B)+8*((D B+1)*J (D B+1))) ≤ C*P B :=
      Nat.mul_le_mul_left C (by dsimp only [P]; omega)
    nlinarith only [controlWire, count, sizeT, sizeS, scale, timeGen, spaceGen,
      jscale, coefficient]

/-- Actual generated-label setup, parked states and the installed streaming loop. Clocks sum
retained-context copies over generated labels; simultaneous workspace uses capacity once. -/
theorem runCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let context := JoinedDissection.probeContext input g.toNat
      let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
      ClassBatches.runCertificate.time (context, g.toNat) ≤
          (ClassBatches.labels context g.toNat).length*ClassBatches.capacity context*P B ∧
        ClassBatches.runCertificate.space (context, g.toNat) ≤
          ClassBatches.capacity context*P B := by
  delta ClassBatches.runCertificate
  extract_lets original loop searched _ empty missing
  let step := ClassBatches.roundCertificate
  obtain ⟨D, hD, mD, data⟩ := BatchResources.context_bounds
  obtain ⟨F, hF, mF, rounds⟩ := round_bounds
  obtain ⟨R, hR, mR, setupBound⟩ := setup_bounds
  obtain ⟨K, loopBounds⟩ := NativeCertificate.foldlStream_bounds ei eo encNat
    (fun q found i => found.orElse (fun _ => ClassBatches.matchLabel q.1 q.2 i)) step
  let P := fun B => 100*(K+1)*(F B+R B+100*(D B+B+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hf := mF hab
    have hr := mR hab
    exact Nat.mul_le_mul_left _ (by omega)
  · intro m p hp as bs cs ds s g
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let B := (ClassBalance.encoding input).length+(as.length+bs.length+cs.length+ds.length)+p+1
    let C := ClassBatches.capacity context
    let parameter : JoinedProbe.Context × ℕ := (context, g.toNat)
    let rows := ClassBatches.labels context g.toNat
    let n := rows.length
    let w := (ClassBatches.batchCount context g.toNat).size
    let args : (JoinedProbe.Context × ℕ) × (Option (ℕ × ℕ) × List ℕ) :=
      (parameter, (none, rows))
    have cPos : 1 ≤ C := ClassBatches.capacity_pos context
    have nPos : 1 ≤ n := List.length_pos_of_mem (zero_label context g.toNat)
    have d := data hp as bs cs ds s g 0 (zero_label context g.toNat)
    change (JoinedProbe.encoding context).length ≤ C*D B ∧ _ at d
    have scalars : (encNat C).length+(encNat 0).length+
        (encNat (ClassBatches.population context g.toNat)).length+(encNat g.toNat).length ≤
          D B := d.2
    have controlWire : (ei parameter).length ≤ C*(3*D B+2) := by
      have h := length_encPair (enc₁ := JoinedProbe.encoding) (enc₂ := encNat) parameter
      dsimp only [parameter] at h
      have scale := Nat.mul_le_mul_left (D B+1) cPos
      change (encPair JoinedProbe.encoding encNat parameter).length ≤ _
      nlinarith only [h, d.1, scalars, scale]
    have countLe : ClassBatches.batchCount context g.toNat ≤ C :=
      (ClassBatches.batchCount_le_quarter context g.toNat).trans (Nat.le_add_left _ _)
    have width : w ≤ D B := by
      have h := Nat.size_le_size countLe
      have cw : (encNat C).length ≤ D B := by omega
      rw [encNat_apply, Nat.size_eq_bits_len] at cw
      exact h.trans cw
    have rowLen : n = 2^w := (SortedQuarterMachine.indices_wire w).1
    have rowCount : n ≤ 4*C := by
      have bound := (ClassBatches.pow_size (ClassBatches.batchCount context g.toNat)).trans
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_right countLe 1))
      rw [← rowLen] at bound
      omega
    have labelWire (i : ℕ) (hi : i ∈ rows) : (encNat i).length ≤ D B := by
      have h := data hp as bs cs ds s g i hi
      change _ ≤ C*D B ∧ _ at h
      have scalar : (encNat C).length+(encNat i).length+
          (encNat (ClassBatches.population context g.toNat)).length+
          (encNat g.toNat).length ≤ D B := h.2
      omega
    have rowsWire : (encList encNat rows).length ≤ C*(10*D B+10) := by
      have h := (SortedQuarterMachine.indices_wire w).2.2
      change (encList encNat rows).length ≤ 2^w*(2*w+1) at h
      rw [← rowLen] at h
      have scale := Nat.mul_le_mul rowCount (show 2*w+1 ≤ 2*D B+1 by omega)
      nlinarith only [h, scale, Nat.zero_le (C*(D B+1))]
    have states (j : ℕ) :
        (eo ((rows.take j).foldl (labelStep context g.toNat) none)).length ≤ 12*B+5 :=
      prefix_wire hp as bs cs ds s g (rows.take j)
    have stateWidth : NativeCertificate.foldStateWidth eo
        (fun q found i => found.orElse (fun _ => ClassBatches.matchLabel q.1 q.2 i)) args ≤
          12*B+5 := by
      apply Finset.sup_le
      intro j _
      exact states j
    have recordWidth : streamRecordLength encNat rows ≤ D B := listMax_le labelWire
    have inputWire : (encPair ei (encPair eo (encList encNat)) args).length ≤
        C*(20*D B+20) := by
      have out := length_encPair (enc₁ := ei) (enc₂ := encPair eo (encList encNat)) args
      have inn := length_encPair (enc₁ := eo) (enc₂ := encList encNat)
        ((none : Option (ℕ × ℕ)), rows)
      dsimp only [args] at out
      simp only [eo, encNatPairOption, encOption_none, List.length_nil] at inn
      have scale := Nat.mul_le_mul_left (D B+1) cPos
      nlinarith only [out, inn, rowsWire, controlWire, scale]
    have each (j : ℕ) (hj : j < rows.length) :
        let state := (rows.take j).foldl (labelStep context g.toNat) none
        step.time ((parameter, state), rows[j])+step.space ((parameter, state), rows[j]) ≤ C*F B :=
      rounds hp as bs cs ds s g rows[j] _ (List.getElem_mem hj) (states j)
    have sumCallbacks : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
        step.time ((parameter, (rows.take j).foldl (labelStep context g.toNat) none), rows[j])
        else 0) ≤ n*C*F B := by
      have h := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range rows.length) =>
        show (if h : j < rows.length then step.time
            ((parameter, (rows.take j).foldl (labelStep context g.toNat) none), rows[j]) else 0) ≤
            C*F B from by
          rw [dite_eq_left (Finset.mem_range.mp hj)]
          exact (Nat.le_add_right _ _).trans (each j (Finset.mem_range.mp hj)))
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, n,
        Nat.mul_assoc] using h
    have maxCallbacks : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
        step.space ((parameter, (rows.take j).foldl (labelStep context g.toNat) none), rows[j])
        else 0) ≤ C*F B := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      exact (Nat.le_add_left _ _).trans (each j (Finset.mem_range.mp hj))
    have control : (ei parameter).length+NativeCertificate.foldStateWidth eo
        (fun q found i => found.orElse (fun _ => ClassBatches.matchLabel q.1 q.2 i)) args+
          streamRecordLength encNat rows+1 ≤ C*(10*D B+20*B+20) := by
      have scale := Nat.mul_le_mul_left (D B+B+1) cPos
      nlinarith only [controlWire, stateWidth, recordWidth, scale]
    have budgets : NativeCertificate.foldTimeBudget ei eo encNat
          (fun q found i => found.orElse (fun _ => ClassBatches.matchLabel q.1 q.2 i)) step args ≤
          n*C*(F B+100*(D B+B+1)) ∧
        NativeCertificate.foldSpaceBudget ei eo encNat
          (fun q found i => found.orElse (fun _ => ClassBatches.matchLabel q.1 q.2 i)) step args ≤
          C*(F B+100*(D B+B+1)) := by
      have frameScale := Nat.mul_le_mul_left (C*(20*D B+20)) nPos
      have timeControl := Nat.mul_le_mul (show rows.length+1 ≤ 2*n by dsimp only [n]; omega) control
      constructor
      · dsimp only [NativeCertificate.foldTimeBudget, args]
        nlinarith only [inputWire, sumCallbacks, timeControl, frameScale,
          Nat.zero_le (n*C*(D B+B+1))]
      · dsimp only [NativeCertificate.foldSpaceBudget, args]
        nlinarith only [inputWire, maxCallbacks, control, Nat.zero_le (C*(D B+B+1))]
    have running := loopBounds args
    have runTime := running.1.trans (Nat.mul_le_mul_left K budgets.1)
    have runSpace := running.2.trans (Nat.mul_le_mul_left K budgets.2)
    have produced : (parameter, ((none : Option (ℕ × ℕ)),
        ClassBatches.labels parameter.1 parameter.2)) = args := rfl
    have coefficient : R B+K*(F B+100*(D B+B+1))+2*(3*D B+2) ≤ P B := by
      dsimp only [P]
      nlinarith only [Nat.zero_le (K*F B), Nat.zero_le (K*R B), Nat.zero_le (K*D B),
        Nat.zero_le (K*B)]
    have setup := setupBound hp as bs cs ds s g
    change _ ≤ C*R B at setup
    have setupTime := (Nat.le_add_right _ _).trans setup
    have setupSpace := (Nat.le_add_left _ _).trans setup
    have searchedTime : searched.time parameter =
        ClassBatches.setupCertificate.time parameter+loop.time args := by
      dsimp only [searched]
      rw [NativeCertificate.comp_time, produced]
    have searchedSpace : searched.space parameter =
        ClassBatches.setupCertificate.space parameter+loop.space args := by
      dsimp only [searched]
      rw [NativeCertificate.comp_space, produced]
    have emptyTime : empty.time parameter = (ei parameter).length := by
      dsimp only [empty, original, NativeCertificate.post, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.linear]
    have emptySpace : empty.space parameter = (ei parameter).length := by
      dsimp only [empty, original, NativeCertificate.post, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.linear]
    have missingTime : missing.time parameter = (ei parameter).length := by
      dsimp only [missing, NativeCertificate.const, NativeCertificate.linear]
    have missingSpace : missing.space parameter = (ei parameter).length := by
      dsimp only [missing, NativeCertificate.const, NativeCertificate.linear]
    have profile :
        (NativeCertificate.branch empty missing searched).time parameter ≤
          2*(ei parameter).length+ClassBatches.setupCertificate.time parameter+loop.time args ∧
        (NativeCertificate.branch empty missing searched).space parameter ≤
          2*(ei parameter).length+ClassBatches.setupCertificate.space parameter+
            loop.space args := by
      constructor
      · rw [NativeCertificate.branch_time, emptyTime]
        split
        · rw [missingTime]; omega
        · rw [searchedTime]; omega
      · rw [NativeCertificate.branch_space, emptySpace]
        split
        · rw [missingSpace]; omega
        · rw [searchedSpace]; omega
    dsimp only [NativeCertificate.congr]
    change _ ≤ n*C*P B ∧ _ ≤ C*P B
    have spaceCoefficient := Nat.mul_le_mul_left C coefficient
    have timeCoefficient := Nat.mul_le_mul_left (n*C) coefficient
    have setupScale := Nat.mul_le_mul_left (C*(R B+2*(3*D B+2))) nPos
    constructor
    · with_reducible refine profile.1.trans ?_
      nlinarith only [setupTime, runTime, controlWire, timeCoefficient, setupScale]
    · with_reducible refine profile.2.trans ?_
      nlinarith only [setupSpace, runSpace, controlWire, spaceCoefficient]

end Cslib.Cryptanalysis.AddXNOR.BatchLoopResources
