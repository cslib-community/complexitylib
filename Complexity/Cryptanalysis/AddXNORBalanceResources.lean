/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORWholeRunResources
import all Complexity.Cryptanalysis.AddXNORWholeRunResources
import all Complexity.Cryptanalysis.AddXNORProducerResources
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Computability.GenericRAM.Native.Combinators

/-!
# Original-width normalization of the installed balance prepass

Bound the actual count-regenerating scalar prepass, including every fold prefix,
labels and internal count/scalar/copy workspace. Compose it into the installed
original-input source run. Regenerating quarters per class fits a half-exponential
budget under the source cap; it does not implement the faster reachable-state-DP
prepass of [WangLvShenZhang2027], Lemma 8/Theorem 7, pp.21–22.

## Main results

* `balanceCertificate_bounds`: complete scalar prepass time/workspace in original quarter widths.
* `source_balance_bounds`: source-cut half-time/quarter-space prepass, including all prefixes.
* `sourceCertificate_search_bounds`: whole source run with only search sum/max left explicit.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.BalanceResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := encPair encNat encNat
private abbrev roundEncoding := encPair (encPair ClassBalance.encoding encNat) encNat

private abbrev step (input : ClassBalance.Input) (current g : ℕ) : ℕ :=
  max current (min (ClassBalance.count input false g) (ClassBalance.count input true g))

private noncomputable def roundCertificate : NativeCertificate
    (fun q : (ClassBalance.Input × ℕ) × ℕ => step q.1.1 q.1.2 q.2) roundEncoding encNat := by
  let original : NativeCertificate (id : (ClassBalance.Input × ℕ) × ℕ → _)
      roundEncoding roundEncoding := .linear (.of_eq (fun _ => rfl))
  let selected := original.fst.fst.prod original.snd
  let both := ((ClassBalance.countOn false).comp selected).prod
    ((ClassBalance.countOn true).comp selected)
  let smaller := (NativeCertificate.ofPolyTime ClassBalance.minimum_polyTime).comp both
  exact (NativeCertificate.ofPolyTime ClassBalance.maximum_polyTime).comp
    (original.fst.snd.prod smaller)

private theorem round_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (current g B : ℕ),
      (ClassBalance.encoding input).length+(encNat current).length+(encNat g).length+
        (encNat (ClassBalance.count input false g)).length+
        (encNat (ClassBalance.count input true g)).length+1 ≤ B →
      roundCertificate.time ((input, current), g)+roundCertificate.space ((input, current), g) ≤
        ProducerResources.countAllowance input g+P B := by
  obtain ⟨A, hA, mA, minimum⟩ := exists_mono_poly_cert ClassBalance.minimum_polyTime
  obtain ⟨D, hD, mD, minWire⟩ :=
    exists_mono_poly ClassBalance.minimum_polyTime.polyBounded_length
  obtain ⟨C, hC, mC, maximum⟩ := exists_mono_poly_cert ClassBalance.maximum_polyTime
  let P := fun B => 2*A (4*B)+2*C (4*B+D (4*B))+100*B
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA (by omega : 4*a ≤ 4*b)
    have hd := mD (by omega : 4*a ≤ 4*b)
    have hc := mC (by omega : 4*a+D (4*a) ≤ 4*b+D (4*b))
    dsimp only [P]; omega
  · intro input current g B wire
    let counts := (ClassBalance.count input false g, ClassBalance.count input true g)
    have countsWire : (er counts).length ≤ 4*B := by
      dsimp only [er, counts]
      simp only [length_encPair]
      omega
    have minBound := minimum counts
    have minScale := mA countsWire
    have output := (minWire counts).trans (mD countsWire)
    have maxWire : (er (current, min counts.1 counts.2)).length ≤ 4*B+D (4*B) := by
      dsimp only [er]
      simp only [length_encPair]
      change (encNat (min counts.1 counts.2)).length ≤ D (4*B) at output
      omega
    have maxBound := maximum (current, min counts.1 counts.2)
    have maxScale := mC maxWire
    have inputWire : (roundEncoding ((input, current), g)).length ≤ 4*B := by
      dsimp only [roundEncoding]
      rw [length_encPair, length_encPair (enc₁ := ClassBalance.encoding)]
      dsimp only
      omega
    have taskWire : (encPair ClassBalance.encoding encNat (input, g)).length ≤ 2*B := by
      rw [length_encPair]
      dsimp only
      omega
    have profile : roundCertificate.time ((input, current), g)+
        roundCertificate.space ((input, current), g) =
        10*(roundEncoding ((input, current), g)).length+
        12*(encPair ClassBalance.encoding encNat (input, g)).length+
        ProducerResources.countAllowance input g+
        (NativeCertificate.ofPolyTime ClassBalance.minimum_polyTime).time counts+
        (NativeCertificate.ofPolyTime ClassBalance.minimum_polyTime).space counts+
        (NativeCertificate.ofPolyTime ClassBalance.maximum_polyTime).time
          (current, min counts.1 counts.2)+
        (NativeCertificate.ofPolyTime ClassBalance.maximum_polyTime).space
          (current, min counts.1 counts.2) := by
      dsimp only [roundCertificate, ClassBalance.countOn, NativeCertificate.comp,
        NativeCertificate.congr, NativeCertificate.prod, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.post, NativeCertificate.const,
        NativeCertificate.linear, Function.comp_def, id_eq, counts,
        ProducerResources.countAllowance]
      ring
    rw [profile]
    dsimp only [P]
    nlinarith only [minBound.1, minBound.2, maxBound.1, maxBound.2,
      minScale, maxScale, inputWire, taskWire]

private theorem count_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (right : Bool) (g : BitVec p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (encNat (ClassBalance.count input right g.toNat)).length ≤
      as.length+bs.length+cs.length+ds.length+1 := by
  have bounded := ClassBalance.count_le_half hp as bs cs ds s right g
  have exponents : (if right then cs.length+ds.length else as.length+bs.length) ≤
      as.length+bs.length+cs.length+ds.length := by split <;> omega
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) exponents
  have strict : 2^(as.length+bs.length+cs.length+ds.length) <
      2^(as.length+bs.length+cs.length+ds.length+1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos (as.length+bs.length+cs.length+ds.length)
    omega
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.size_le.mpr ((bounded.trans power).trans_lt strict)

private theorem loop_budgets : ∃ A : ℕ → ℕ, PolynomiallyBounded A ∧ Monotone A ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      let G := 2^p
      let Q := JoinedDissection.quarterBudget input
      let args : ClassBalance.Input × (ℕ × List ℕ) :=
        (input, (0, SortedQuarterMachine.indices p))
      NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat
        step roundCertificate args ≤
          G*((Q+2)*A B+40*(B+1)) ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat
        step roundCertificate args ≤
          (Q+2)*A B+G*(20*(B+1)) := by
  obtain ⟨H, hH, mH, rounds⟩ := round_bounds
  obtain ⟨C, hC, mC, counted⟩ := ProducerResources.projectedCount_bounds
  let A := fun B => C (10*B)+H (10*B)
  refine ⟨A, by dsimp only [A]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.add_le_add (mC (by omega)) (mH (by omega))
  · intro m p hp as bs cs ds s
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let G := 2^p
    let Q := JoinedDissection.quarterBudget input
    let rows := SortedQuarterMachine.indices p
    let args : ClassBalance.Input × (ℕ × List ℕ) := (input, (0, rows))
    have gPos : 1 ≤ G := Nat.two_pow_pos p
    have bPos : 1 ≤ B := by dsimp only [B]; omega
    have rowLen : rows.length = G := (SortedQuarterMachine.indices_wire p).1
    have labels (g : ℕ) (hg : g ∈ rows) : (encNat g).length ≤ p := by
      have hlt : g < 2^p := by
        simpa only [rows, SortedQuarterMachine.indices_eq_range, List.mem_range] using hg
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hlt
    have labelWidth : streamRecordLength encNat rows ≤ p := listMax_le labels
    have states (j : ℕ) (hj : j ≤ rows.length) :
        (encNat ((rows.take j).foldl (step input) 0)).length ≤ q+1 := by
      have stored :=  ClassBalance.balancePrefix_wire hp as bs cs ds s j
        (by rw [rowLen] at hj; exact hj)
      have takeEq : rows.take j = List.range j := by
        simp only [rows, SortedQuarterMachine.indices_eq_range, List.take_range,
          List.length_range] at hj ⊢
        rw [Nat.min_eq_left hj]
      rw [takeEq]
      exact stored.trans (by dsimp only [q]; omega)
    have stateWidth : NativeCertificate.foldStateWidth encNat step args ≤ q+1 := by
      apply Finset.sup_le
      intro j hj
      exact states j (by have := Finset.mem_range.mp hj; omega)
    have inputWire :
        (encPair ClassBalance.encoding (encPair encNat (encList encNat)) args).length ≤
        G*(10*(B+1)) := by
      have wire := length_encList_le encNat rows labels
      rw [rowLen] at wire
      dsimp only [args]
      rw [length_encPair, length_encPair (enc₁ := encNat)]
      dsimp only
      rw [show (encNat 0).length = 0 from rfl]
      have scale := Nat.mul_le_mul_left G (by dsimp only [B]; omega : 2*p+1 ≤ 3*(B+1))
      have originalScale := Nat.mul_le_mul_left (B+1) gPos
      dsimp only [B] at *
      nlinarith only [wire, scale, originalScale]
    have each (j : ℕ) (hj : j < rows.length) :
        let current := (rows.take j).foldl (step input) 0
        roundCertificate.time ((input, current), rows[j])+
          roundCertificate.space ((input, current), rows[j]) ≤
          (Q+2)*A B := by
      have gj : rows[j] < 2^p := by
        have member := List.getElem_mem hj
        simpa only [rows, SortedQuarterMachine.indices_eq_range, List.mem_range] using member
      let g := BitVec.ofNat p rows[j]
      have natEq : g.toNat = rows[j] := Nat.mod_eq_of_lt gj
      have left := count_wire hp as bs cs ds s false g
      have right := count_wire hp as bs cs ds s true g
      rw [natEq] at left right
      with_reducible
        change (encNat (ClassBalance.count input false rows[j])).length ≤ q+1 at left
        change (encNat (ClassBalance.count input true rows[j])).length ≤ q+1 at right
      have state := states j (by omega)
      have label := labels rows[j] (List.getElem_mem hj)
      have raw := rounds input ((rows.take j).foldl (step input) 0) rows[j] (10*B)
        (by dsimp only [B]; omega)
      have countEach (right : Bool) :
          ClassBalance.countCertificate.time ((input, right), rows[j])+
            ClassBalance.countCertificate.space ((input, right), rows[j]) ≤
              (ProducerResources.countVolume input right+1)*C (10*B) := by
        have wire := ProducerResources.count_task_wire input g right
        rw [natEq] at wire
        have scalar := wire.trans (Nat.mul_le_mul_left 10
          (show (ClassBalance.encoding input).length+p+1 ≤ B by dsimp only [B]; omega))
        have scaled := Nat.mul_le_mul_left (ProducerResources.countVolume input right+1) (mC scalar)
        with_reducible exact (counted input right rows[j]).trans scaled
      have f := countEach false
      have b := countEach true
      have volumes : ProducerResources.countVolume input false+
          ProducerResources.countVolume input true = Q := by
        simp only [ProducerResources.countVolume, ClassBalance.halfInput, Bool.false_eq_true,
          ite_false, ite_true, JoinedDissection.quarterBudget, input,
          ProgramGeneration.originalSource, BitInput.words, List.length_map, List.length_reverse, Q]
        ring
      dsimp only [ProducerResources.countAllowance] at raw
      dsimp only [A]
      nlinarith only [raw, f, b, volumes, Nat.zero_le (H (10*B))]
    let times := fun j => if h : j < rows.length then
      roundCertificate.time ((input, (rows.take j).foldl (step input) 0), rows[j]) else 0
    let spaces := fun j => if h : j < rows.length then
      roundCertificate.space ((input, (rows.take j).foldl (step input) 0), rows[j]) else 0
    have sumRounds : (∑ j ∈ Finset.range rows.length, times j) ≤ G*((Q+2)*A B) := by
      have h : (∑ j ∈ Finset.range rows.length, times j) ≤
          ∑ _j ∈ Finset.range rows.length, (Q+2)*A B := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simp only [times, dite_eq_left hj']
        exact (Nat.le_add_right _ _).trans (each j hj')
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, rowLen] using h
    have maxRounds : (Finset.range rows.length).sup spaces ≤ (Q+2)*A B := by
      apply Finset.sup_le
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [spaces, dite_eq_left hj']
      exact (Nat.le_add_left _ _).trans (each j hj')
    have control : (ClassBalance.encoding input).length+
        NativeCertificate.foldStateWidth encNat step args+streamRecordLength encNat rows+1 ≤
          10*(B+1) := by dsimp only [B]; omega
    have budgets :
        NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat
        step roundCertificate args ≤
          G*((Q+2)*A B+40*(B+1)) ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat
        step roundCertificate args ≤
          (Q+2)*A B+G*(20*(B+1)) := by
      constructor
      · dsimp only [NativeCertificate.foldTimeBudget, args]
        have frames := Nat.mul_le_mul (by omega : rows.length+1 ≤ 2*G) control
        have positive : 1 ≤ G*(B+1) := Nat.mul_pos (by omega) (by omega)
        dsimp only [times] at sumRounds
        nlinarith only [inputWire, sumRounds, frames, positive]
      · dsimp only [NativeCertificate.foldSpaceBudget, args]
        have scaledFrames := Nat.mul_le_mul_left (10*(B+1)) gPos
        dsimp only [spaces] at maxRounds
        nlinarith only [inputWire, maxRounds, control, scaledFrames]
    exact budgets

/-- Actual scalar count-regenerating prepass, with every callback and prefix charged.
Time pays quarter generation for every class; space pays the maximum count callback
plus the generated class labels. Neither is a supplied runtime invariant. -/
theorem balanceCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      ClassBalance.balanceCertificate.time input ≤
          2^p*(JoinedDissection.quarterBudget input+2)*P B ∧
        ClassBalance.balanceCertificate.space input ≤
          (2^p+JoinedDissection.quarterBudget input+2)*P B := by
  delta ClassBalance.balanceCertificate
  extract_lets e original selected both smaller round loop generation generated indices
    inputCert initial
  have roundTime : round.time = roundCertificate.time := by funext x; rfl
  have roundSpace : round.space = roundCertificate.space := by funext x; rfl
  have setupTime : (inputCert.prod (initial.prod indices)).time =
      WholeRunResources.allSetupCertificate.time := by funext x; rfl
  have setupSpace : (inputCert.prod (initial.prod indices)).space =
      WholeRunResources.allSetupCertificate.space := by funext x; rfl
  obtain ⟨K, foldBound⟩ := NativeCertificate.foldlStream_bounds
    ClassBalance.encoding encNat encNat step round
  obtain ⟨A, hA, mA, budgets⟩ := loop_budgets
  obtain ⟨R, hR, mR, setup⟩ := WholeRunResources.allSetup_bounds
  let P := fun B => (K+1)*(A B+R B+100*(B+1))
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    apply Nat.mul_le_mul_left
    have := mA hab
    have := mR hab
    omega
  · intro m p hp as bs cs ds s
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let G := 2^p
    let Q := JoinedDissection.quarterBudget input
    let args : ClassBalance.Input × (ℕ × List ℕ) :=
      (input, (0, SortedQuarterMachine.indices p))
    have budget := budgets hp as bs cs ds s
    change NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat step
        roundCertificate args ≤ G*((Q+2)*A B+40*(B+1)) ∧
      NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat step
        roundCertificate args ≤ (Q+2)*A B+G*(20*(B+1)) at budget
    have actualBudgets :
        NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat step round args ≤
          G*((Q+2)*A B+40*(B+1)) ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat step round args ≤
          (Q+2)*A B+G*(20*(B+1)) := by
      constructor
      · have eq : NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat
            step round args = NativeCertificate.foldTimeBudget ClassBalance.encoding encNat encNat
              step roundCertificate args := by
          dsimp only [NativeCertificate.foldTimeBudget]
          rw [roundTime]
        exact eq.le.trans budget.1
      · have eq : NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat
            step round args = NativeCertificate.foldSpaceBudget ClassBalance.encoding encNat encNat
              step roundCertificate args := by
          dsimp only [NativeCertificate.foldSpaceBudget]
          rw [roundSpace]
        exact eq.le.trans budget.2
    have actual := foldBound args
    have prepared := (setup input).trans (Nat.mul_le_mul_left G
      (mR (show (ClassBalance.encoding input).length+ClassBalance.depth input+1 ≤ B by
        change (ClassBalance.encoding input).length+p+1 ≤ B
        dsimp only [B]; omega)))
    have produced : (id input, ((0 : ℕ),
        (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) = args := rfl
    constructor
    · rw [NativeCertificate.congr_time, NativeCertificate.comp_time]
      with_reducible
        change (inputCert.prod (initial.prod indices)).time input+
          loop.time (id input, (0, (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) ≤ _
      rw [produced, setupTime]
      have upper := Nat.mul_le_mul_left K actualBudgets.1
      have lower := actual.1.trans upper
      have scale := Nat.mul_le_mul_left (G*(Q+2))
        (show R B+K*A B+40*K*(B+1) ≤ P B by dsimp only [P]; nlinarith)
      change _ ≤ G*(Q+2)*P B
      nlinarith only [prepared, lower, scale, Nat.zero_le (G*Q*R B),
        Nat.zero_le (G*(Q+1)*40*K*(B+1))]
    · rw [NativeCertificate.congr_space, NativeCertificate.comp_space]
      with_reducible
        change (inputCert.prod (initial.prod indices)).space input+
          loop.space (id input, (0, (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) ≤ _
      rw [produced, setupSpace]
      have upper := Nat.mul_le_mul_left K actualBudgets.2
      have lower := actual.2.trans upper
      have scale := Nat.mul_le_mul_left (G+Q+2)
        (show R B+K*A B+20*K*(B+1) ≤ P B by dsimp only [P]; nlinarith)
      change _ ≤ (G+Q+2)*P B
      nlinarith only [prepared, lower, scale, Nat.zero_le ((Q+2)*R B),
        Nat.zero_le (G*K*A B), Nat.zero_le ((Q+2)*20*K*(B+1))]

/-- The installed regenerated-count prepass fits half-exponential time and quarter-exponential
workspace on the actual source cut, with polynomial factors in original physical input bits.
This is slower than the source's quarter-time reachable-state-DP prepass. -/
theorem source_balance_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      let I := (Source.encoding original).length
      ClassBalance.balanceCertificate.time prepared ≤ 2^(tail.length/2)*P I ∧
        ClassBalance.balanceCertificate.space prepared ≤ 2^(tail.length/4)*P I := by
  obtain ⟨A, hA, mA, bound⟩ := balanceCertificate_bounds
  obtain ⟨D, hD, mD, layout⟩ := WholeRunResources.sourceScalarWidth
  let P := fun I => 14*A (D I)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 14 (mA (mD h)), ?_⟩
  intro m p s tail
  let original := Source.ofWords p s tail
  let prepared := Source.prepare original
  let I := (Source.encoding original).length
  let k := tail.length/4
  let d := min p (min m k)
  have hp : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have hk : d ≤ k := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  have preparedEq : prepared = ProgramGeneration.originalSource d
      (Source.quarters tail).1.1 (Source.quarters tail).1.2
      (Source.quarters tail).2.1 (Source.quarters tail).2.2 s 0 := Source.prepare_ofWords p s tail
  have total := congrArg List.length (Source.quarters_append tail)
  simp only [List.length_append] at total
  have actual := bound hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
    (Source.quarters tail).2.1 (Source.quarters tail).2.2 s
  have typed : ClassBalance.balanceCertificate.time prepared ≤
        2^d*(JoinedDissection.quarterBudget prepared+2)*
          A ((ClassBalance.encoding prepared).length+tail.length+d+1) ∧
      ClassBalance.balanceCertificate.space prepared ≤
        (2^d+JoinedDissection.quarterBudget prepared+2)*
          A ((ClassBalance.encoding prepared).length+tail.length+d+1) := by
    rw [preparedEq]
    have total' : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
        (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length = tail.length := by
      omega
    simpa only [total'] using actual
  have depthEq : ClassBalance.depth prepared = d := by rw [preparedEq]; rfl
  have scalar : (ClassBalance.encoding prepared).length+tail.length+d+1 ≤ D I := by
    have h := layout m p s tail
    change (ClassBalance.encoding prepared).length+tail.length+
      ClassBalance.depth prepared+1 ≤ D I at h
    rw [depthEq] at h
    exact h
  have normalized := mA scalar
  have quarters : JoinedDissection.quarterBudget prepared ≤ 11*2^k :=
    JoinedDissection.quarterBudget_source p s tail
  have labels : 2^d ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have positive : 1 ≤ 2^k := Nat.two_pow_pos _
  have halves : 2^k*2^k ≤ 2^(tail.length/2) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [k]; omega)
  have timeVolume : 2^d*(JoinedDissection.quarterBudget prepared+2) ≤
      14*2^(tail.length/2) := by
    have upper := Nat.mul_le_mul labels
      (show JoinedDissection.quarterBudget prepared+2 ≤ 13*2^k by omega)
    nlinarith only [upper, halves]
  have spaceVolume : 2^d+JoinedDissection.quarterBudget prepared+2 ≤ 14*2^k := by omega
  constructor
  · have upper := typed.1.trans (Nat.mul_le_mul timeVolume normalized)
    change _ ≤ 2^(tail.length/2)*P I
    dsimp only [P]
    nlinarith only [upper]
  · have upper := typed.2.trans (Nat.mul_le_mul spaceVolume normalized)
    change _ ≤ 2^k*P I
    dsimp only [P]
    nlinarith only [upper]

/-- The actual original-input whole run with its balance prepass completely normalized.
Only the installed class-search sum and maximum remain explicit cost expressions. This is
not the source sharp theorem until those search costs have independent closed bounds. -/
theorem sourceCertificate_search_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      let I := (Source.encoding original).length
      JoinedDissection.sourceCertificate.time original ≤
          (WholeRunResources.classTime prepared+2^(tail.length/2))*P I ∧
        JoinedDissection.sourceCertificate.space original ≤
          (WholeRunResources.classSpace prepared+2^(tail.length/4))*P I := by
  obtain ⟨A, hA, mA, balance⟩ := source_balance_bounds
  obtain ⟨W, hW, mW, whole⟩ := WholeRunResources.sourceCertificate_bounds
  let P := fun I => A I+2*W I
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA hab
    have hw := mW hab
    dsimp only [P]; omega
  · intro m p s tail
    let original := Source.ofWords p s tail
    let prepared := Source.prepare original
    let I := (Source.encoding original).length
    let G := 2^ClassBalance.depth prepared
    let quarter := 2^(tail.length/4)
    let half := 2^(tail.length/2)
    have h := whole m p s tail
    have b := balance m p s tail
    have labels : G ≤ quarter := by
      have capped : ClassBalance.depth prepared ≤ tail.length/4 := by
        dsimp only [prepared, original]
        rw [Source.prepare_ofWords]
        change min p (min m (tail.length/4)) ≤ tail.length/4
        exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
      exact Nat.pow_le_pow_right (by decide) capped
    have quarterLe : quarter ≤ half := Nat.pow_le_pow_right (by decide) (by omega)
    have positive : 1 ≤ quarter := Nat.two_pow_pos _
    constructor
    · have control := Nat.mul_le_mul_right (W I) (show G+1 ≤ 2*half by omega)
      have total : JoinedDissection.sourceCertificate.time original ≤
          half*A I+(WholeRunResources.classTime prepared+G+1)*W I := by
        have upper := Nat.add_le_add_right b.1
          ((WholeRunResources.classTime prepared+G+1)*W I)
        with_reducible exact h.1.trans upper
      change _ ≤ (WholeRunResources.classTime prepared+half)*P I
      dsimp only [P]
      nlinarith only [total, control,
        Nat.zero_le (WholeRunResources.classTime prepared*A I),
        Nat.zero_le (WholeRunResources.classTime prepared*W I)]
    · have control := Nat.mul_le_mul_right (W I) (show G+1 ≤ 2*quarter by omega)
      have total : JoinedDissection.sourceCertificate.space original ≤
          quarter*A I+(WholeRunResources.classSpace prepared+G+1)*W I := by
        have upper := Nat.add_le_add_right b.2
          ((WholeRunResources.classSpace prepared+G+1)*W I)
        with_reducible exact h.2.trans upper
      change _ ≤ (WholeRunResources.classSpace prepared+quarter)*P I
      dsimp only [P]
      nlinarith only [total, control,
        Nat.zero_le (WholeRunResources.classSpace prepared*A I),
        Nat.zero_le (WholeRunResources.classSpace prepared*W I)]

end Cslib.Cryptanalysis.AddXNOR.BalanceResources
