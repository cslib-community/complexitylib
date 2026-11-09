/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORProducerResources
public import Complexity.Computability.GenericRAM.Native.StreamingFoldBounds
import all Complexity.Computability.GenericRAM.Native.StreamingFoldBounds
import all Complexity.Computability.GenericRAM.Native.Combinators
import all Complexity.Cryptanalysis.AddXNORJoinedDissection
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine

/-!
# Whole-run resource envelopes for the installed dissection machine

Account for class-loop state copies and control by actual callback sums and
prefix maxima, then connect original-input preparation and readback to the
installed source certificate. Explicit search/balance allowances remain real
subprogram costs, not supplied runtime contracts. An envelope in those costs
is not the sharp resource theorem of [WangLvShenZhang2027], Theorem 7, pp.21–22.

## Main definitions

* `classTime`: sum of installed class-search allowances, conservatively including skipped classes.
* `classSpace`: maximum installed class-search workspace, rather than its sum or a class mean.

## Main results

* `allCertificate_bounds`: actual outer-loop resources with original-width control overhead.
* `sourceCertificate_bounds`: whole original-input preparation-to-readback envelope.

The remaining sharp inequalities must bound the actual balance prepass and
these search sum/max functions. They still include window scan/cut/division,
retained/group emission and internal control. No runtime bound on them is a
premise of the envelope, and the source fast reachable-state count prepass and
whole-paper endpoints remain open.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.WholeRunResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := encPair encNat encNat
private abbrev eo := encOption er

private theorem allStep_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (g : ℕ) (result : Option (ℕ × ℕ)),
      let wire := (encPair ClassBalance.encoding JoinedDissection.stateEncoding
        (input, (g, result))).length
      JoinedDissection.allStepCertificate.time (input, (g, result)) ≤
          JoinedDissection.searchCertificate.time (input, g)+P wire ∧
        JoinedDissection.allStepCertificate.space (input, (g, result)) ≤
          JoinedDissection.searchCertificate.space (input, g)+P wire := by
  delta JoinedDissection.allStepCertificate
  extract_lets e original foundCert fresh yes chosen increment next
  obtain ⟨A, hA, mA, bound⟩ := exists_mono_poly_cert increment
  let P := fun n => A n+100*(n+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mA hab; dsimp only [P]; omega
  · intro input g result
    let q := (input, (g, result))
    let E := (e q).length
    have wireEq : E = 2*(ClassBalance.encoding input).length+
        2*(encNat g).length+(eo result).length+2 := by
      change (encPair ClassBalance.encoding (encPair encNat eo) (input, (g, result))).length = _
      simp only [length_encPair]
      ring
    have fields : (encNat g).length+(eo result).length ≤ E := by rw [wireEq]; omega
    have inc := bound g
    have scaled := mA (show (encNat g).length ≤ E by omega)
    change _ ≤ JoinedDissection.searchCertificate.time (input, g)+P E ∧
      _ ≤ JoinedDissection.searchCertificate.space (input, g)+P E
    cases result <;> constructor <;>
      dsimp only [NativeCertificate.congr, NativeCertificate.prod, NativeCertificate.comp,
        NativeCertificate.option, NativeCertificate.fst, NativeCertificate.snd,
        NativeCertificate.some, NativeCertificate.post, NativeCertificate.linear,
        original, chosen, foundCert, fresh, yes, next, Function.comp_def, id_eq,
        Option.elim, P]
    all_goals
      dsimp only [E, q] at fields scaled ⊢
      simp only [length_encPair, JoinedDissection.recEncoding, eo, er,
        encOption_some, encOption_none, List.length_cons] at fields scaled ⊢
      omega

/-- Conservative sum of real class-search allowances, including classes skipped after a hit. -/
noncomputable def classTime (input : ClassBalance.Input) : ℕ :=
  (Finset.range (2^ClassBalance.depth input)).sum
    (fun g => JoinedDissection.searchCertificate.time (input, g))

/-- Maximum real class-search workspace allowance; no class mean or summed allocation. -/
noncomputable def classSpace (input : ClassBalance.Input) : ℕ :=
  (Finset.range (2^ClassBalance.depth input)).sup
    (fun g => JoinedDissection.searchCertificate.space (input, g))

private theorem prefix_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (j : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let step := fun (found : Option (ℕ × ℕ)) (g : ℕ) =>
      found.orElse (fun _ => JoinedDissection.search input g)
    let q := as.length+bs.length+cs.length+ds.length
    (eo (((List.range (2^p)).take j).foldl step none)).length ≤ 3*q+2 := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let step := fun (found : Option (ℕ × ℕ)) (g : ℕ) =>
      found.orElse (fun _ => JoinedDissection.search input g)
  let rows := List.range (2^p)
  let q := as.length+bs.length+cs.length+ds.length
  have park (out : ℕ × ℕ) (xs : List ℕ) : xs.foldl step (some out) = some out := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.foldl_cons, step, Option.orElse_some] using ih
  have full : rows.foldl step none = JoinedDissection.allSearch input :=
    (JoinedDissection.allSearch_eq_fold input).symm
  have wire := JoinedDissection.allSearch_wire hp as bs cs ds s
  change (eo ((rows.take j).foldl step none)).length ≤ 3*q+2
  cases hit : (rows.take j).foldl step none with
  | none => simp [eo]
  | some out =>
    have final : rows.foldl step none = some out := by
      rw [← List.take_append_drop j rows, List.foldl_append, hit]
      exact park out (rows.drop j)
    rw [full] at final
    change (eo (JoinedDissection.allSearch input)).length ≤ 3*q+2 at wire
    rw [final] at wire
    exact wire


private abbrev roundEncoding := encPair (encPair ClassBalance.encoding eo) encNat

private noncomputable def classRoundCertificate : NativeCertificate
    (fun q : (ClassBalance.Input × Option (ℕ × ℕ)) × ℕ =>
      q.1.2.orElse (fun _ => JoinedDissection.search q.1.1 q.2)) roundEncoding eo := by
  let original : NativeCertificate (id : (ClassBalance.Input × Option (ℕ × ℕ)) × ℕ → _)
      roundEncoding roundEncoding := .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr ((JoinedDissection.allStepCertificate.comp
    (original.fst.fst.prod (original.snd.prod original.fst.snd))).snd) (fun _ => rfl)

private theorem classRound_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (g : ℕ) (found : Option (ℕ × ℕ)) (B : ℕ),
      (ClassBalance.encoding input).length+(encNat g).length+(eo found).length+1 ≤ B →
      classRoundCertificate.time ((input, found), g) ≤
          JoinedDissection.searchCertificate.time (input, g)+P B ∧
        classRoundCertificate.space ((input, found), g) ≤
          JoinedDissection.searchCertificate.space (input, g)+P B := by
  obtain ⟨A, hA, mA, bound⟩ := allStep_bounds
  let P := fun B => A (4*B)+100*(B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mA (by omega : 4*a ≤ 4*b); dsimp only [P]; omega
  · intro input g found B wire
    have stepWire : (encPair ClassBalance.encoding JoinedDissection.stateEncoding
        (input, (g, found))).length ≤ 4*B := by
      change (encPair ClassBalance.encoding (encPair encNat eo) (input, (g, found))).length ≤ _
      rw [length_encPair, length_encPair (enc₁ := encNat) (enc₂ := eo)]
      dsimp only
      omega
    have actual := bound input g found
    dsimp only at actual
    have overhead := mA stepWire
    have rawWire : (roundEncoding ((input, found), g)).length ≤ 4*B := by
      dsimp only [roundEncoding]
      rw [length_encPair, length_encPair (enc₁ := ClassBalance.encoding) (enc₂ := eo)]
      dsimp only
      omega
    constructor <;>
      dsimp only [classRoundCertificate, NativeCertificate.congr, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.snd, NativeCertificate.fst,
        NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq]
    all_goals
      change (roundEncoding ((input, found), g)).length+
        ((roundEncoding ((input, found), g)).length+(roundEncoding ((input, found), g)).length)+
        _ ≤ _+P B
      dsimp only [P]
      omega

private abbrev classStep (input : ClassBalance.Input) (found : Option (ℕ × ℕ)) (g : ℕ) :
    Option (ℕ × ℕ) := found.orElse (fun _ => JoinedDissection.search input g)

private theorem classLoop_budgets : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      let args := (input, (none, SortedQuarterMachine.indices p))
      NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep
          classRoundCertificate args ≤ classTime input+2^p*P B ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep
          classRoundCertificate args ≤ classSpace input+2^p*P B := by
  obtain ⟨H, hH, mH, rounds⟩ := classRound_bounds
  let P := fun B => H (10*B)+100*(B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mH (by omega : 10*a ≤ 10*b); dsimp only [P]; omega
  · intro m p hp as bs cs ds s
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let G := 2^p
    let rows := SortedQuarterMachine.indices p
    let args : ClassBalance.Input × (Option (ℕ × ℕ) × List ℕ) := (input, (none, rows))
    have gPos : 1 ≤ G := Nat.two_pow_pos p
    have bPos : 1 ≤ B := by dsimp only [B]; omega
    have rowLen : rows.length = G := (SortedQuarterMachine.indices_wire p).1
    have states (j : ℕ) : (eo ((rows.take j).foldl (classStep input) none)).length ≤ 3*q+2 := by
      change (eo ((rows.take j).foldl
        (fun found g => found.orElse (fun _ => JoinedDissection.search input g)) none)).length ≤ _
      simpa only [rows, SortedQuarterMachine.indices_eq_range] using prefix_wire hp as bs cs ds s j
    have labels (g : ℕ) (hg : g ∈ rows) : (encNat g).length ≤ p := by
      have hlt : g < 2^p := by
        simpa only [rows, SortedQuarterMachine.indices_eq_range, List.mem_range] using hg
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hlt
    have labelWidth : streamRecordLength encNat rows ≤ p := listMax_le labels
    have stateWidth : NativeCertificate.foldStateWidth eo classStep args ≤ 3*q+2 := by
      apply Finset.sup_le
      intro j _
      exact states j
    have inputWire : (encPair ClassBalance.encoding (encPair eo (encList encNat)) args).length ≤
        G*(10*(B+1)) := by
      have wire := length_encList_le encNat rows labels
      rw [rowLen] at wire
      rw [length_encPair, length_encPair (enc₁ := eo) (enc₂ := encList encNat)]
      dsimp only [args]
      simp only [eo, encOption_none, List.length_nil]
      have originalWire : (ClassBalance.encoding input).length ≤ B := by dsimp only [B]; omega
      have depth : p ≤ B := by dsimp only [B]; omega
      have scale := Nat.mul_le_mul_left G (by omega : 2*p+1 ≤ 3*(B+1))
      have originalScale := Nat.mul_le_mul_left (B+1) gPos
      nlinarith only [wire, scale, originalScale, originalWire]
    have each (j : ℕ) (hj : j < rows.length) :
        let found := (rows.take j).foldl (classStep input) none
        classRoundCertificate.time ((input, found), rows[j]) ≤
            JoinedDissection.searchCertificate.time (input, rows[j])+H (10*B) ∧
          classRoundCertificate.space ((input, found), rows[j]) ≤
            JoinedDissection.searchCertificate.space (input, rows[j])+H (10*B) := by
      have fs := states j
      have gs := labels rows[j] (List.getElem_mem hj)
      exact rounds input rows[j] _ (10*B) (by dsimp only [B]; omega)
    let timeRows := fun j => if h : j < rows.length then
      classRoundCertificate.time
        ((input, (rows.take j).foldl (classStep input) none), rows[j]) else 0
    let spaceRows := fun j => if h : j < rows.length then
      classRoundCertificate.space
        ((input, (rows.take j).foldl (classStep input) none), rows[j]) else 0
    let searchRows := fun j => if h : j < rows.length then
      JoinedDissection.searchCertificate.time (input, rows[j]) else 0
    have sumRound : (∑ j ∈ Finset.range rows.length, timeRows j) ≤
        classTime input+G*H (10*B) := by
      have h : (∑ j ∈ Finset.range rows.length, timeRows j) ≤
          ∑ j ∈ Finset.range rows.length, (searchRows j+H (10*B)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < rows.length := Finset.mem_range.mp hj
        simp only [timeRows, searchRows, dite_eq_left hj']
        exact (each j hj').1
      have sums : (∑ j ∈ Finset.range rows.length, searchRows j) = classTime input := by
        simp only [searchRows, rows, SortedQuarterMachine.indices_eq_range, List.length_range]
        change _ = ∑ j ∈ Finset.range (2^p),
          JoinedDissection.searchCertificate.time (input, j)
        apply Finset.sum_congr rfl
        intro j hj
        rw [dite_eq_left (Finset.mem_range.mp hj)]
        simp only [List.getElem_range]
      rw [Finset.sum_add_distrib, sums] at h
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, rowLen] using h
    have maxRound : (Finset.range rows.length).sup spaceRows ≤ classSpace input+H (10*B) := by
      apply Finset.sup_le
      intro j hj
      have hj' : j < rows.length := Finset.mem_range.mp hj
      have h := (each j hj').2
      have member : rows[j] ∈ Finset.range (2^p) := by
        have hm := List.getElem_mem hj'
        simpa only [rows, SortedQuarterMachine.indices_eq_range, List.mem_range,
          Finset.mem_range] using hm
      have max := Finset.le_sup (f := fun g =>
        JoinedDissection.searchCertificate.space (input, g)) member
      change _ ≤ classSpace input at max
      dsimp only [spaceRows]
      rw [dite_eq_left hj']
      omega
    have control : (ClassBalance.encoding input).length+
        NativeCertificate.foldStateWidth eo classStep args+streamRecordLength encNat rows+1 ≤
          10*(B+1) := by dsimp only [B]; omega
    constructor
    · change NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep
        classRoundCertificate args ≤ classTime input+G*P B
      dsimp only [NativeCertificate.foldTimeBudget, args]
      have frames := Nat.mul_le_mul (by omega : rows.length+1 ≤ 2*G) control
      have positive : 1 ≤ G*(B+1) := Nat.mul_pos (by omega) (by omega)
      dsimp only [timeRows] at sumRound
      dsimp only [P]
      nlinarith only [inputWire, sumRound, frames, positive]
    · change NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep
        classRoundCertificate args ≤ classSpace input+G*P B
      dsimp only [NativeCertificate.foldSpaceBudget, args]
      have scaledCallback := Nat.mul_le_mul_left (H (10*B)) gPos
      have scaledFrames := Nat.mul_le_mul_left (10*(B+1)) gPos
      dsimp only [spaceRows] at maxRound
      dsimp only [P]
      nlinarith only [inputWire, maxRound, control, scaledCallback, scaledFrames]

private noncomputable def allSetupCertificate : NativeCertificate
    (fun input : ClassBalance.Input =>
      (input, ((none : Option (ℕ × ℕ)), SortedQuarterMachine.indices (ClassBalance.depth input))))
    ClassBalance.encoding (encPair ClassBalance.encoding (encPair eo (encList encNat))) := by
  let generation := (Classical.choose_spec SortedQuarterMachine.indices_computable).2.2
  let generated : NativeCertificate SortedQuarterMachine.indices encUnary (encList encNat) :=
    ⟨_, _, generation⟩
  let indices := generated.comp (NativeCertificate.ofPolyTime ClassBalance.depth_polyTime)
  let original : NativeCertificate (id : ClassBalance.Input → _)
      ClassBalance.encoding ClassBalance.encoding := .linear (.of_eq (fun _ => rfl))
  let initial : NativeCertificate (fun _ : ClassBalance.Input => (none : Option (ℕ × ℕ)))
      ClassBalance.encoding eo := .const _
  exact original.prod (initial.prod indices)

private theorem allSetup_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : ClassBalance.Input,
      allSetupCertificate.time input+allSetupCertificate.space input ≤
        2^ClassBalance.depth input*
          P ((ClassBalance.encoding input).length+ClassBalance.depth input+1) := by
  obtain ⟨D, hD, mD, depthBound⟩ := exists_mono_poly_cert ClassBalance.depth_polyTime
  let J := Classical.choose SortedQuarterMachine.indices_computable
  have hJ := (Classical.choose_spec SortedQuarterMachine.indices_computable).1
  have mJ : Monotone J := (Classical.choose_spec SortedQuarterMachine.indices_computable).2.1
  let P := fun n => 10*(D n+n*J n+n+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    apply Nat.mul_le_mul_left
    have hd := mD hab
    have hj := Nat.mul_le_mul hab (mJ hab)
    omega
  · intro input
    let B := (ClassBalance.encoding input).length+ClassBalance.depth input+1
    let G := 2^ClassBalance.depth input
    have gPos : 1 ≤ G := Nat.two_pow_pos _
    have bPos : 1 ≤ B := by dsimp only [B]; omega
    have sourceWire : (ClassBalance.encoding input).length ≤ B := by dsimp only [B]; omega
    have depthWidth : ClassBalance.depth input+1 ≤ B := by dsimp only [B]; omega
    have actual := depthBound input
    have scaled := mD sourceWire
    have labels := Nat.mul_le_mul depthWidth (mJ depthWidth)
    have generation := Nat.mul_le_mul_left G labels
    have output := Nat.mul_le_mul_left G (mJ depthWidth)
    have outputScale := Nat.mul_le_mul_left (G*J B) bPos
    have scalarScale := Nat.mul_le_mul_left (D B) gPos
    have frameScale := Nat.mul_le_mul_left B gPos
    dsimp only [allSetupCertificate, NativeCertificate.prod, NativeCertificate.comp,
      NativeCertificate.const, NativeCertificate.linear, Function.comp_def, id_eq]
    change ((ClassBalance.encoding input).length+((ClassBalance.encoding input).length+
        ((NativeCertificate.ofPolyTime ClassBalance.depth_polyTime).time input+
          (ClassBalance.depth input+1)*G*J (ClassBalance.depth input+1))))+
      ((ClassBalance.encoding input).length+((ClassBalance.encoding input).length+
        ((NativeCertificate.ofPolyTime ClassBalance.depth_polyTime).space input+
          G*J (ClassBalance.depth input+1)))) ≤ G*P B
    dsimp only [P]
    nlinarith only [actual.1, actual.2, scaled, generation, output, outputScale,
      scalarScale, frameScale, sourceWire]

/-- The installed all-class certificate pays polynomial original-width overhead beyond
the real class-search sum/max and generated class-label volume. Every callback prefix and
parked result is charged. No class-search runtime bound is a hypothesis. -/
theorem allCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      JoinedDissection.allCertificate.time input ≤ (classTime input+2^p)*P B ∧
        JoinedDissection.allCertificate.space input ≤ (classSpace input+2^p)*P B := by
  delta JoinedDissection.allCertificate
  extract_lets e original round loop generation generated indices inputCert initial
  have roundTime : round.time = classRoundCertificate.time := by funext q; rfl
  have roundSpace : round.space = classRoundCertificate.space := by funext q; rfl
  have setupEq : inputCert.prod (initial.prod indices) = allSetupCertificate := rfl
  have loopResources : ∃ K : ℕ, ∀ args,
      loop.time args ≤ K*NativeCertificate.foldTimeBudget ClassBalance.encoding
        (encOption JoinedDissection.recEncoding) encNat
        (fun input found g => found.orElse (fun _ => JoinedDissection.search input g)) round args ∧
      loop.space args ≤ K*NativeCertificate.foldSpaceBudget ClassBalance.encoding
        (encOption JoinedDissection.recEncoding) encNat
        (fun input found g => found.orElse (fun _ => JoinedDissection.search input g))
          round args := by
    exact NativeCertificate.foldlStream_bounds ClassBalance.encoding
      (encOption JoinedDissection.recEncoding) encNat
      (fun input found g => found.orElse (fun _ => JoinedDissection.search input g)) round
  obtain ⟨K, foldBound⟩ := loopResources
  obtain ⟨Q, hQ, mQ, budgets⟩ := classLoop_budgets
  obtain ⟨R, hR, mR, setup⟩ := allSetup_bounds
  let P := fun B => (K+1)*(Q B+R B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul_left (K+1)
      (Nat.add_le_add_right (Nat.add_le_add (mQ hab) (mR hab)) 1)
  · intro m p hp as bs cs ds s
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let G := 2^p
    let args : ClassBalance.Input × (Option (ℕ × ℕ) × List ℕ) :=
      (input, (none, SortedQuarterMachine.indices p))
    have bounds :
        NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep
          classRoundCertificate args ≤ classTime input+G*Q B ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep
          classRoundCertificate args ≤ classSpace input+G*Q B := budgets hp as bs cs ds s
    have actualBounds :
        NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep round args ≤
          classTime input+G*Q B ∧
        NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep round args ≤
          classSpace input+G*Q B := by
      constructor
      · have eq : NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep
            round args = NativeCertificate.foldTimeBudget ClassBalance.encoding eo encNat classStep
              classRoundCertificate args := by
          dsimp only [NativeCertificate.foldTimeBudget]
          rw [roundTime]
        exact eq.le.trans bounds.1
      · have eq : NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep
            round args = NativeCertificate.foldSpaceBudget ClassBalance.encoding eo encNat classStep
              classRoundCertificate args := by
          dsimp only [NativeCertificate.foldSpaceBudget]
          rw [roundSpace]
        exact eq.le.trans bounds.2
    have executed := foldBound args
    have loopTime : loop.time args ≤ K*(classTime input+G*Q B) :=
      executed.1.trans (Nat.mul_le_mul_left K actualBounds.1)
    have loopSpace : loop.space args ≤ K*(classSpace input+G*Q B) :=
      executed.2.trans (Nat.mul_le_mul_left K actualBounds.2)
    have prepared := (setup input).trans (Nat.mul_le_mul_left G
      (mR (show (ClassBalance.encoding input).length+p+1 ≤ B by dsimp only [B]; omega)))
    have coefficient : K+R B+K*Q B ≤ P B := by
      have difference : P B = (K+R B+K*Q B)+(K*R B+Q B+1) := by dsimp only [P]; ring
      rw [difference]
      exact Nat.le_add_right _ _
    have produced : (id input, ((none : Option (ℕ × ℕ)),
        (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) = args := by
      dsimp only [Function.comp_def, id_eq]
      rw [show ClassBalance.depth input = p from rfl]
    -- Keep the class-search implementation opaque when transporting scalar loop inputs.
    constructor
    · rw [NativeCertificate.congr_time, NativeCertificate.comp_time]
      with_reducible
        change (inputCert.prod (initial.prod indices)).time input+
          loop.time (id input, (none, (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) ≤
            (classTime input+G)*P B
      rw [produced, setupEq]
      have h : allSetupCertificate.time input+loop.time args ≤
          G*R B+K*(classTime input+G*Q B) := by omega
      have scaled := Nat.mul_le_mul_left (classTime input+G) coefficient
      nlinarith only [h, scaled, Nat.zero_le (classTime input*(R B+K*Q B))]
    · rw [NativeCertificate.congr_space, NativeCertificate.comp_space]
      with_reducible
        change (inputCert.prod (initial.prod indices)).space input+
          loop.space (id input, (none, (SortedQuarterMachine.indices ∘ ClassBalance.depth) input)) ≤
            (classSpace input+G)*P B
      rw [produced, setupEq]
      have h : allSetupCertificate.space input+loop.space args ≤
          G*R B+K*(classSpace input+G*Q B) := by omega
      have scaled := Nat.mul_le_mul_left (classSpace input+G) coefficient
      nlinarith only [h, scaled, Nat.zero_le (classSpace input*(R B+K*Q B))]

private theorem source_profile (original : Source.Input) :
    let prepared := Source.prepare original
    JoinedDissection.sourceCertificate.time original =
      ClassBalance.balanceCertificate.time prepared+
      (Source.prepareCertificate.time original+JoinedDissection.halvesCertificate.time prepared+
        JoinedDissection.readbackCertificate.time
          (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared))+
      JoinedDissection.allCertificate.time prepared ∧
    JoinedDissection.sourceCertificate.space original =
      ClassBalance.balanceCertificate.space prepared+
      (Source.prepareCertificate.space original+JoinedDissection.halvesCertificate.space prepared+
        JoinedDissection.readbackCertificate.space
          (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared))+
      JoinedDissection.allCertificate.space prepared := by
  constructor <;>
    dsimp only [JoinedDissection.sourceCertificate, JoinedDissection.solveCertificate,
      NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
      Function.comp_def] <;> ring

private theorem sourceScalarWidth : ∃ D : ℕ → ℕ, PolynomiallyBounded D ∧ Monotone D ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      (ClassBalance.encoding prepared).length+tail.length+ClassBalance.depth prepared+1 ≤
        D ((Source.encoding original).length) := by
  obtain ⟨A, hA, mA, output⟩ := exists_mono_poly Source.prepare_polyTime.polyBounded_length
  let D := fun n => A n+3*n+3
  refine ⟨D, by dsimp only [D]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mA hab; dsimp only [D]; omega
  · intro m p s tail
    let original := Source.ofWords p s tail
    let prepared := Source.prepare original
    let width := (Source.encoding original).length
    have tailWire : tail.length ≤ width := by
      have hl := length_le_length_encList encNat ((s :: tail).map BitVec.toNat)
      simp only [List.length_map, List.length_cons] at hl
      dsimp only [width, original, Source.ofWords, Source.encoding]
      simp only [length_encPair]
      omega
    have depthEq : ClassBalance.depth prepared = min p (min m (tail.length/4)) := by
      dsimp only [prepared, original]
      rw [Source.prepare_ofWords]
      rfl
    have depthWire : ClassBalance.depth prepared ≤ width := by
      rw [depthEq]
      have h : min p (min m (tail.length/4)) ≤ tail.length/4 :=
        (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
      exact h.trans ((Nat.div_le_self _ _).trans tailWire)
    have prepWire : (ClassBalance.encoding prepared).length ≤ A width := output original
    change (ClassBalance.encoding prepared).length+tail.length+
      ClassBalance.depth prepared+1 ≤ D width
    dsimp only [D]
    omega

/-- Whole original-input source-certificate envelope, from preparation through decoded output.
Only the actual computed-balance prepass and class-search sum/max remain unnormalized here.
They are explicit installed subprogram fields, not runtime contracts in the hypotheses.
The polynomial depends only on original physical input length; all class-loop/frame/index/
parked-state/readback costs are paid. This does not assert the sharp source asymptotics. -/
theorem sourceCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      let classes := 2^ClassBalance.depth prepared
      let width := (Source.encoding original).length
      JoinedDissection.sourceCertificate.time original ≤
          ClassBalance.balanceCertificate.time prepared+(classTime prepared+classes+1)*P width ∧
        JoinedDissection.sourceCertificate.space original ≤
          ClassBalance.balanceCertificate.space prepared+
            (classSpace prepared+classes+1)*P width := by
  obtain ⟨A, hA, mA, allBounds⟩ := allCertificate_bounds
  obtain ⟨B, hB, mB, boundary⟩ := JoinedDissection.preparation_readback_bounds
  obtain ⟨D, hD, mD, layout⟩ := sourceScalarWidth
  let P := fun n => B n+A (D n)+1
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab; have := mB hab; have := mA (mD hab); dsimp only [P]; omega
  · intro m p s tail
    let original := Source.ofWords p s tail
    let prepared := Source.prepare original
    let width := (Source.encoding original).length
    let depth := min p (min m (tail.length/4))
    let classes := 2^ClassBalance.depth prepared
    have hp : depth ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    have preparedEq : prepared = ProgramGeneration.originalSource depth
        (Source.quarters tail).1.1 (Source.quarters tail).1.2
        (Source.quarters tail).2.1 (Source.quarters tail).2.2 s 0 := Source.prepare_ofWords p s tail
    have depthEq : ClassBalance.depth prepared = depth := by rw [preparedEq]; rfl
    have searched : JoinedDissection.allCertificate.time prepared ≤
        (classTime prepared+classes)*A ((ClassBalance.encoding prepared).length+
          ((Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
            (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length)+depth+1) ∧
        JoinedDissection.allCertificate.space prepared ≤
          (classSpace prepared+classes)*A ((ClassBalance.encoding prepared).length+
            ((Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
              (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length)+depth+1) := by
      dsimp only [classes]
      rw [depthEq, preparedEq]
      exact allBounds hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
        (Source.quarters tail).2.1 (Source.quarters tail).2.2 s
    have cut := congrArg List.length (Source.quarters_append tail)
    simp only [List.length_append] at cut
    have size : (ClassBalance.encoding prepared).length+tail.length+depth+1 ≤ D width := by
      have h := layout m p s tail
      change (ClassBalance.encoding prepared).length+tail.length+ClassBalance.depth prepared+1 ≤
        D width at h
      rw [depthEq] at h
      exact h
    have scalar : (ClassBalance.encoding prepared).length+
        ((Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
          (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length)+depth+1 ≤
            D width := by omega
    have normalized := mA scalar
    have allTime : JoinedDissection.allCertificate.time prepared ≤
        (classTime prepared+classes)*A (D width) :=
      searched.1.trans (Nat.mul_le_mul_left _ normalized)
    have allSpace : JoinedDissection.allCertificate.space prepared ≤
        (classSpace prepared+classes)*A (D width) :=
      searched.2.trans (Nat.mul_le_mul_left _ normalized)
    have edges := boundary m p s tail
    have timeEq := (source_profile original).1
    have spaceEq := (source_profile original).2
    have arithmetic (c : ℕ) : B width+c*A (D width) ≤ (c+1)*P width := by
      calc
        B width+c*A (D width) ≤ B width+(c+1)*A (D width) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right c 1)) _
        _ ≤ (c+1)*B width+(c+1)*A (D width) :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos c)) _
        _ = (c+1)*(B width+A (D width)) := by ring
        _ ≤ (c+1)*P width := Nat.mul_le_mul_left _ (by dsimp only [P]; omega)
    constructor
    · rw [timeEq]
      have edge : Source.prepareCertificate.time original+
          JoinedDissection.halvesCertificate.time prepared+JoinedDissection.readbackCertificate.time
            (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared) ≤
              B width := edges.1
      have combined := (Nat.add_le_add edge allTime).trans
        (arithmetic (classTime prepared+classes))
      have regroup := Nat.add_assoc (ClassBalance.balanceCertificate.time prepared)
        (Source.prepareCertificate.time original+JoinedDissection.halvesCertificate.time prepared+
          JoinedDissection.readbackCertificate.time
            (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared))
        (JoinedDissection.allCertificate.time prepared)
      with_reducible
        exact regroup.le.trans (Nat.add_le_add_left combined
          (ClassBalance.balanceCertificate.time prepared))
    · rw [spaceEq]
      have edge : Source.prepareCertificate.space original+
          JoinedDissection.halvesCertificate.space prepared+
            JoinedDissection.readbackCertificate.space
            (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared) ≤
              B width := edges.2
      have combined := (Nat.add_le_add edge allSpace).trans
        (arithmetic (classSpace prepared+classes))
      have regroup := Nat.add_assoc (ClassBalance.balanceCertificate.space prepared)
        (Source.prepareCertificate.space original+JoinedDissection.halvesCertificate.space prepared+
          JoinedDissection.readbackCertificate.space
            (JoinedDissection.halves prepared, JoinedDissection.allSearch prepared))
        (JoinedDissection.allCertificate.space prepared)
      with_reducible
        exact regroup.le.trans (Nat.add_le_add_left combined
          (ClassBalance.balanceCertificate.space prepared))

end Cslib.Cryptanalysis.AddXNOR.WholeRunResources
