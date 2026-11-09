/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSearchResources
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatchCallbackBounds
import all CslibFrontier.Cryptanalysis.AddXNORWholeRunResources
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Cryptanalysis.AddXNORBalanceResources
import all CslibFrontier.Cryptanalysis.AddXNORProducerResources
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# Original-width resources of actual restarted class windows

Normalize the installed window callbacks and machine at the actual computed orientation,
retained capacity and generated labels. Scalar polynomials use original physical input
widths; count/filter/division/cut/cross work is charged, not replaced by record volume.
This is a component toward [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22,
not a complete solver bound or the faster reachable-state-DP count prepass.
The conventions are the deterministic multitape bit costs on PDF p. 6. Time sums
all generated class/label window allowances, including guarded padding and classes
skipped after hits; workspace bounds each actual window independently. Polynomial factors
are in original encoded input length, with no unit-record or supplied runtime premise.
Ambient retained/consumer frames and remaining class-control composition are still separate.

## Main definitions

* `callbackAllowance`, `windowAllowance`: actual installed window component profiles.

## Main results

* `original_window_bounds`, `original_window_sum`: original-width capacity amortization.
* `source_window_bounds`: source-cut window-phase clocks and all-prefix workspace.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.RestartResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding

private theorem original_window_width :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
        (g : BitVec p) (i : ℕ),
        let input := ProgramGeneration.originalSource p as bs cs ds s 0
        let context := JoinedDissection.probeContext input g.toNat
        let q := as.length+bs.length+cs.length+ds.length
        i ∈ ClassBatches.labels context g.toNat →
        KeyJoinBatch.windowWidth (i*ClassBatches.capacity context, ClassBatches.capacity context)
          (JoinedProbe.groups context g.toNat) ≤
            P ((ClassBalance.encoding input).length+q+p+1) := by
  obtain ⟨A, hA, mA, sorted⟩ := SearchResources.sorted_wire
  obtain ⟨D, hD, mD, queryWire⟩ :=
    exists_mono_poly ClassBalance.queryInput_polyTime.polyBounded_length
  let P := fun B => A (D (10*B)+1)+100*B+100
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD (Nat.mul_le_mul_left 10 hab)
    have ha := mA (Nat.add_le_add_right hd 1)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g i
    dsimp only
    intro hi
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let context := JoinedDissection.probeContext input g.toNat
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let N := ClassBatches.quarterVolume context
    let C := ClassBatches.capacity context
    let groups := JoinedProbe.groups context g.toNat
    let r := !(ClassBalance.retainRight input g.toNat)
    have label : (encNat g.toNat).length ≤ p := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
    have queryInputWire :
        (encPair (encPair ClassBalance.encoding encBool) encNat ((input, r), g.toNat)).length ≤
          10*B := by
      have outer := length_encPair (enc₁ := encPair ClassBalance.encoding encBool)
        (enc₂ := encNat) ((input, r), g.toNat)
      have inner := length_encPair (enc₁ := ClassBalance.encoding) (enc₂ := encBool) (input, r)
      have boolWire : (encBool r).length = 1 := rfl
      dsimp only at outer inner
      dsimp only [B]
      omega
    have preparedWire : (ClassJoin.encoding (ClassBalance.queryInput input r g.toNat)).length ≤
        D (10*B) := (queryWire ((input, r), g.toNat)).trans (mD queryInputWire)
    have recordsWire := (sorted (ClassBalance.queryInput input r g.toNat)).2.trans
      (mA (Nat.add_le_add_right preparedWire 1))
    have rowWire : streamRecordLength er groups.flatten ≤ A (D (10*B)+1) := by
      change streamRecordLength er
        (KeyGrouping.run
          (ClassJoin.sortedRecords (ClassBalance.queryInput input r g.toNat))).flatten ≤ _
      rw [KeyGrouping.flatten_run]
      exact recordsWire
    have nle : N ≤ JoinedDissection.quarterBudget input :=
      JoinedDissection.restart_quarter_le input g.toNat
    have nw : (encNat N).length ≤ q+3 := (length_encNat_mono nle).trans
      (SearchResources.quarter_counter_wire (p := p) as bs cs ds s)
    have squared : (encNat (N^2+1)).length ≤ 2*q+7 := by
      have mul := length_encNat_mul_le N N
      rw [← pow_two] at mul
      have plus := ComputableTidilyInO.length_encNat_add_le (N^2) 1
      omega
    have countWire := BalanceResources.count_wire hp as bs cs ds s
      (ClassBalance.retainRight input g.toNat) g
    change (encNat (ClassBalance.count input (ClassBalance.retainRight input g.toNat)
      g.toNat)).length ≤ q+1 at countWire
    have cw : (encNat C).length ≤ 2*q+6 := by
      have plus := ComputableTidilyInO.length_encNat_add_le
        (ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat) 1
      have sum := length_encNat_add_le_add
        (ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat+1) N
      change (encNat
        (ClassBalance.count input (ClassBalance.retainRight input g.toNat) g.toNat+1+N)).length ≤ _
      omega
    have iw : (encNat i).length ≤ q+3 := by
      have bit := (le_listMax (f := fun j => (encNat j).length) hi).trans
        (SortedQuarterMachine.indices_wire (ClassBatches.batchCount context g.toNat).size).2.1
      have size := Nat.size_le_size (ClassBatches.batchCount_le_quarter context g.toNat)
      have bits : (ClassBatches.batchCount context g.toNat).size ≤ (encNat N).length := by
        simpa only [encNat_apply, ← Nat.size_eq_bits_len, N] using size
      omega
    have skip := length_encNat_mul_le i C
    have stateWire : (encPair encNat encNat (i*C, C)).length ≤ 8*q+25 := by
      rw [length_encPair]
      dsimp only
      omega
    have nEq : groups.flatten.length = N := ClassBatches.groups_length context g.toNat
    change KeyJoinBatch.windowWidth (i*C, C) groups ≤ P B
    dsimp only [KeyJoinBatch.windowWidth]
    rw [nEq]
    change (encPair encNat encNat (i*C, C)).length+streamRecordLength er groups.flatten+
      (encNat (N^2+1)).length+1 ≤ P B
    have qBound : q ≤ B := by dsimp only [B]; omega
    dsimp only [P]
    omega

/-- Actual window callback time/workspace at the computed opposite orientation and capacity. -/
noncomputable def callbackAllowance (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  let context := JoinedDissection.probeContext input g
  let capacity := ClassBatches.capacity context
  let groups := JoinedProbe.groups context g
  KeyJoinBatch.windowCallbackTime (i*capacity, capacity) groups+
    KeyJoinBatch.windowCallbackSpace (i*capacity, capacity) groups

/-- Time plus all-prefix workspace of the actual installed window machine at a restart label.
The two fields share an upper bound; running time is not used to define workspace. -/
noncomputable def windowAllowance (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  let context := JoinedDissection.probeContext input g
  let capacity := ClassBatches.capacity context
  let groups := JoinedProbe.groups context g
  KeyJoinBatch.windowCertificate.time ((i*capacity, capacity), groups)+
    KeyJoinBatch.windowCertificate.space ((i*capacity, capacity), groups)

/-- Normalize actual callback and installed-window allowances in original physical widths,
for both computed orientations and every generated label, including guarded padding labels.
Capacity includes the real retained population and quarter input, not a supplied memory bound. -/
theorem original_window_bounds :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
        (g : BitVec p) (i : ℕ),
        let input := ProgramGeneration.originalSource p as bs cs ds s 0
        let context := JoinedDissection.probeContext input g.toNat
        let q := as.length+bs.length+cs.length+ds.length
        i ∈ ClassBatches.labels context g.toNat →
        callbackAllowance input g.toNat i+windowAllowance input g.toNat i ≤
          ClassBatches.capacity context*P ((ClassBalance.encoding input).length+q+p+1) := by
  obtain ⟨D, hD, mD, widths⟩ := original_window_width
  obtain ⟨A, hA, mA, callbacks⟩ := KeyJoinBatch.windowCallback_bounds
  obtain ⟨C, hC, mC, windows⟩ := KeyJoinBatch.windowCertificate_scalar_bounds
  let P := fun B => 4*(A (D B)+C (D B))
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 4 (Nat.add_le_add (mA (mD h)) (mC (mD h))), ?_⟩
  intro m p hp as bs cs ds s g i
  dsimp only
  intro hi
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let context := JoinedDissection.probeContext input g.toNat
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  let N := ClassBatches.quarterVolume context
  let capacity := ClassBatches.capacity context
  let groups := JoinedProbe.groups context g.toNat
  let initial := (i*capacity, capacity)
  let right := !(ClassBalance.retainRight input g.toNat)
  have groupCount : groups.length ≤ N := by
    have h := SearchResources.groups_count_le
      (ClassJoin.sortedRecords (ClassBalance.queryInput input right g.toNat))
    have len :
        (ClassJoin.sortedRecords (ClassBalance.queryInput input right g.toNat)).length = N := by
      change _ = ClassBatches.quarterVolume context
      rw [← ClassBatches.groups_length context g.toNat]
      change _ = (KeyGrouping.run
        (ClassJoin.sortedRecords (ClassBalance.queryInput input right g.toNat))).flatten.length
      rw [KeyGrouping.flatten_run]
    exact h.trans_eq len
  have nEq : groups.flatten.length = N := ClassBatches.groups_length context g.toNat
  have nCapacity : N ≤ capacity := Nat.le_add_left _ _
  have positive : 0 < capacity := ClassBatches.capacity_pos context
  have volume : initial.2+groups.flatten.length+groups.length+1 ≤ 4*capacity := by
    rw [nEq]
    change capacity+N+groups.length+1 ≤ _
    omega
  have width := widths hp as bs cs ds s g i hi
  change KeyJoinBatch.windowWidth initial groups ≤ D B at width
  have cb := callbacks initial groups
  have win := windows initial groups
  have combined := Nat.add_le_add cb win
  have scaled := Nat.mul_le_mul volume (Nat.add_le_add (mA width) (mC width))
  change callbackAllowance input g.toNat i+windowAllowance input g.toNat i ≤ capacity*P B
  dsimp only [callbackAllowance, windowAllowance]
  change _ ≤ capacity*(4*(A (D B)+C (D B)))
  nlinarith only [combined, scaled]

/-- Sum of actual installed window allowances over all computed classes and generated labels,
with a simultaneous per-window bound using computed balance. These are window-phase bounds,
not whole-run clocks or a replacement for preprocessing, retained joins, matching and control. -/
theorem original_window_sum :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
        let input := ProgramGeneration.originalSource p as bs cs ds s 0
        let q := as.length+bs.length+cs.length+ds.length
        let B := (ClassBalance.encoding input).length+q+p+1
        (∑ g : BitVec p,
          ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
            (windowAllowance input g.toNat)).sum) ≤
          (6*(2^(as.length+bs.length)+2^(cs.length+ds.length))+
            4*2^p*(JoinedDissection.quarterBudget input+1))*P B ∧
        ∀ (g : BitVec p) (i : ℕ),
          i ∈ ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat →
          windowAllowance input g.toNat i ≤
            (ClassBalance.balance input+JoinedDissection.quarterBudget input+1)*P B := by
  obtain ⟨P, hP, mP, bounds⟩ := original_window_bounds
  refine ⟨P, hP, mP, ?_⟩
  intro m p hp as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  have each (g : BitVec p) (i : ℕ)
      (hi : i ∈ ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat) :
      windowAllowance input g.toNat i ≤
        ClassBatches.capacity (JoinedDissection.probeContext input g.toNat)*P B := by
    have h := bounds hp as bs cs ds s g i hi
    change callbackAllowance input g.toNat i+windowAllowance input g.toNat i ≤
      ClassBatches.capacity (JoinedDissection.probeContext input g.toNat)*P B at h
    omega
  constructor
  · have classBound (g : BitVec p) :
        ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
          (windowAllowance input g.toNat)).sum ≤
            JoinedDissection.restartCopyWork input g.toNat*P B := by
      have h := List.sum_le_sum (fun i hi => each g i hi)
      simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
      exact h.trans_eq (Nat.mul_assoc _ _ _).symm
    have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => classBound g)
    rw [← Finset.sum_mul] at total
    exact total.trans (Nat.mul_le_mul_right (P B)
      (JoinedDissection.sum_restartCopyWork hp as bs cs ds s))
  · intro g i hi
    have h := each g i hi
    have kept := ClassBalance.class_le_balance input g.toNat g.isLt
    have quarter := JoinedDissection.restart_quarter_le input g.toNat
    have capacity := JoinedDissection.restart_capacity_eq input g.toNat
    have capBound : ClassBatches.capacity (JoinedDissection.probeContext input g.toNat) ≤
        ClassBalance.balance input+JoinedDissection.quarterBudget input+1 := by omega
    exact h.trans (Nat.mul_le_mul_right (P B) capBound)

/-- The actual window phase, summed over every generated source class/label, fits half-exponential
bit time and quarter-exponential-plus-computed-balance simultaneous window workspace. Polynomial
factors use original input bits. Ambient solver frames, retained preparation, matching, loop
control and readback still require whole-run composition; this is not the source Theorem 7. -/
theorem source_window_bounds :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
        let original := Source.ofWords p s tail
        let input := Source.prepare original
        let I := (Source.encoding original).length
        (∑ g : BitVec (ClassBalance.depth input),
          ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
            (windowAllowance input g.toNat)).sum) ≤ 2^(tail.length/2)*P I ∧
        ∀ (g : BitVec (ClassBalance.depth input)) (i : ℕ),
          i ∈ ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat →
          windowAllowance input g.toNat i ≤
            (2^(tail.length/4)+ClassBalance.balance input)*P I := by
  obtain ⟨A, hA, mA, windows⟩ := original_window_sum
  obtain ⟨D, hD, mD, layout⟩ := WholeRunResources.sourceScalarWidth
  let P := fun I => 100*(A (D I)+1)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 100 (Nat.add_le_add_right (mA (mD h)) 1), ?_⟩
  intro m p s tail
  let original := Source.ofWords p s tail
  let input := Source.prepare original
  let I := (Source.encoding original).length
  let d := min p (min m (tail.length/4))
  let quarter := 2^(tail.length/4)
  let half := 2^(tail.length/2)
  let Q := JoinedDissection.quarterBudget input
  let G := 2^d
  let H := 2^((Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length)+
    2^((Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length)
  have hm : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have hk : d ≤ tail.length/4 := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  have preparedEq : input = ProgramGeneration.originalSource d
      (Source.quarters tail).1.1 (Source.quarters tail).1.2
      (Source.quarters tail).2.1 (Source.quarters tail).2.2 s 0 := Source.prepare_ofWords p s tail
  have depthEq : ClassBalance.depth input = d := by rw [preparedEq]; rfl
  have lengths := Source.quarters_lengths tail
  have total : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
      (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length = tail.length := by
    dsimp only at lengths
    omega
  have typed := windows hm (Source.quarters tail).1.1 (Source.quarters tail).1.2
    (Source.quarters tail).2.1 (Source.quarters tail).2.2 s
  dsimp only at typed
  rw [← preparedEq, total] at typed
  have wire : (ClassBalance.encoding input).length+tail.length+ClassBalance.depth input+1 ≤
      D I := layout m p s tail
  rw [depthEq] at wire
  have scaled := mA wire
  have quarters : Q ≤ 11*quarter := JoinedDissection.quarterBudget_source p s tail
  have labels : G ≤ quarter := Nat.pow_le_pow_right (by decide) hk
  have positive : 1 ≤ quarter := Nat.two_pow_pos _
  have square : quarter*quarter ≤ half := by
    dsimp only [quarter, half]
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  dsimp only at lengths
  have leftExp : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length ≤
      tail.length/2 := by omega
  have rightExp : (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length ≤
      tail.length/2+2 := by omega
  have leftSize := Nat.pow_le_pow_right (by decide : 1 ≤ 2) leftExp
  have rightSize := Nat.pow_le_pow_right (by decide : 1 ≤ 2) rightExp
  have rightCeiling : (2 : ℕ)^(tail.length/2+2) = 4*half := by
    dsimp only [half]
    rw [pow_add]
    norm_num
    ring
  rw [rightCeiling] at rightSize
  have halves : H ≤ 5*half := by dsimp only [H, half]; omega
  have work : 6*H+4*G*(Q+1) ≤ 100*half := by
    have charge := Nat.mul_le_mul labels (show Q+1 ≤ 12*quarter by omega)
    nlinarith only [halves, charge, square]
  have workspace : ClassBalance.balance input+Q+1 ≤
      12*(quarter+ClassBalance.balance input) := by omega
  change (∑ g : BitVec (ClassBalance.depth input),
    ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
      (windowAllowance input g.toNat)).sum) ≤ half*P I ∧ _
  rw [depthEq]
  constructor
  · have upper := typed.1.trans (Nat.mul_le_mul work scaled)
    change _ ≤ half*(100*(A (D I)+1))
    nlinarith only [upper]
  · intro g i hi
    have upper := (typed.2 g i hi).trans (Nat.mul_le_mul workspace scaled)
    change _ ≤ (quarter+ClassBalance.balance input)*(100*(A (D I)+1))
    nlinarith only [upper, Nat.zero_le ((quarter+ClassBalance.balance input)*A (D I))]

end Cslib.Cryptanalysis.AddXNOR.RestartResources
