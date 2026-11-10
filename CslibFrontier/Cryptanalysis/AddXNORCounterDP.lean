/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounterInitialization
public import CslibFrontier.Cryptanalysis.AddXNORCounterPairing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.IndexNat
public import CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Cryptanalysis.AddXNORCounterInitialization
import all CslibFrontier.Cryptanalysis.AddXNORCounterPairing
import all CslibFrontier.Cryptanalysis.AddXNORCounterPull
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.IndexNat
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds

/-!
# Uniform reachable-state counting on original operands

Initialize the dense keyed counter table from the original seed/target, execute
the actual pull/pair/add machine for each operand, and restore numeric keys with
the small-state index writer. Inverse execution consumes operands in reverse.
The table returned on the output tape contains every state count, including zeros.

This realizes the reachable-state counter recurrence used in
[WangLvShenZhang2027], Lemma 8 (PDF pp. 21–22). The faster balance prepass and its
composition with the dissection solver remain separate objectives.

## Main definitions

* `run`, `ofWords`: counting from original data, in either direction.
* `runCertificate`: one native machine for initialization, iteration, indexing and output.

## Main results

* `run_words`: exact complete counter tables, without an assumed execution conclusion.
* `prefix_wire`: original-width physical storage at every operand prefix.
* `runCertificate_bounds`: actual summed-clock/maximum-workspace composition.
* `CounterDP.source_certificate` in `AddXNORCounterDPResources` normalizes the whole DP.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterDP
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Direction and original unary-width/binary-seed/binary-operand instance. -/
abbrev Input := Bool × SortedQuarterMachine.Input

/-- Frame the direction bit before the existing original-operand encoding. -/
abbrev encoding : Input ↪ List Bool := encPair encBool SortedQuarterMachine.encoding

/-- The fold captures only unary width and direction; its evolving state is the counter table. -/
abbrev Parameters := ℕ × Bool

/-- Frame the unary width before the direction bit. -/
abbrev parameterEncoding : Parameters ↪ List Bool := encPair encUnary encBool

/-- Execute one genuine counter update, then restore keys for the next iteration. -/
def step (parameters : Parameters) (rows : List (ℕ × ℕ)) (operand : ℕ) : List (ℕ × ℕ) :=
  let (width, inverse) := parameters
  IndexNat.run (CounterPairing.layer (((width, operand), inverse), rows))

/-- All counts, obtained without enumerating operator words or supplying an initial table. -/
def run (input : Input) : List (ℕ × ℕ) :=
  let (inverse, ((width, seed), operands)) := input
  let ordered := if inverse then operands.reverse else operands
  ordered.foldl (step (width, inverse)) (CounterInitialization.run (width, seed))

/-- The actual encoding of original typed words, with unrestricted target for inverse execution. -/
def ofWords {m : ℕ} (inverse : Bool) (seed : BitVec m) (operands : List (BitVec m)) : Input :=
  (inverse, ((m, seed.toNat), operands.map BitVec.toNat))

/-- The native forward or inverse counter recurrence, selected by the original direction. -/
def advance {m : ℕ} (inverse : Bool) (a : BitVec m) (table : WordTable ℕ m) :
    WordTable ℕ m :=
  if inverse then (WordTable.countBackAdvance (stateKey a) table).ret
  else (WordTable.countAdvance (stateKey a) table).ret

/-- The index writer reconstructs exactly the graph consumed by the next real machine call. -/
theorem step_table {m : ℕ} (table : WordTable ℕ m) (a : BitVec m) (inverse : Bool) :
    step (m, inverse) (CounterPull.graph table.read) a.toNat =
      CounterPull.graph (advance inverse a table).read := by
  rw [step, CounterPairing.layer_table]
  simp only [CounterPull.graph, List.map_ofFn, IndexNat.run_ofFn, advance, Function.comp_def]

private theorem fold_table {m : ℕ} (as : List (BitVec m)) (table : WordTable ℕ m)
    (inverse : Bool) :
    (as.map BitVec.toNat).foldl (step (m, inverse)) (CounterPull.graph table.read) =
      CounterPull.graph (as.foldl (fun table a => advance inverse a table) table).read := by
  induction as generalizing table with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.map_cons, List.foldl_cons, step_table] using
      ih (advance inverse a table)

private theorem forward_fold {m : ℕ} (as : List (BitVec m)) (table : WordTable ℕ m) :
    as.foldl (fun table a => advance false a table) table =
      (WordTable.countRun (as.map stateKey) table).ret := by
  induction as generalizing table with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    simp only [advance, Bool.false_eq_true, ite_false, List.map_cons,
      WordTable.countRun, Cslib.Algorithms.Lean.TimeM.ret_bind,
      Cslib.Algorithms.Lean.TimeM.ret_pure]

private theorem backward_fold {m : ℕ} (as : List (BitVec m)) (table : WordTable ℕ m) :
    as.reverse.foldl (fun table a => advance true a table) table =
      (WordTable.countBackRun (as.map stateKey) table).ret := by
  induction as generalizing table with
  | nil => rfl
  | cons a as ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [advance, ite_true, List.map_cons, WordTable.countBackRun,
      Cslib.Algorithms.Lean.TimeM.ret_bind, Cslib.Algorithms.Lean.TimeM.ret_pure]

/-- Complete original-input correctness, retaining every indexed operator multiplicity.
No completed table, traversal, execution or counting conclusion is supplied as a premise. -/
theorem run_words {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool) :
    run (ofWords inverse seed as) = CounterPull.graph
      (if inverse then WordTable.backwardCounters as seed
        else WordTable.classCounters as seed).read := by
  cases inverse <;>
    simp only [run, ofWords, Bool.false_eq_true, ite_false, ite_true,
      CounterInitialization.run_words, ← List.map_reverse, fold_table,
      forward_fold, backward_fold, WordTable.classCounters, WordTable.backwardCounters,
      List.map_nil,
      WordTable.countRun]

private noncomputable def layerCertificate : NativeCertificate
    CounterPairing.layer CounterPairing.encoding (encList encNat) :=
  let P := Classical.choose CounterPairing.layer_computable
  ⟨fun input => (input.2.length+1)*P (CounterPairing.width input),
    fun input => (input.2.length+1)*P (CounterPairing.width input),
    (Classical.choose_spec CounterPairing.layer_computable).2.2⟩

private noncomputable def indexCertificate : NativeCertificate
    IndexNat.run (encList encNat) encNatPairList :=
  let P := Classical.choose IndexNat.run_computable
  ⟨fun rows => (rows.length+1)*P (IndexNat.width rows),
    fun rows => (rows.length+1)*P (IndexNat.width rows),
    (Classical.choose_spec IndexNat.run_computable).2.2⟩

/-- The installed callback runs the pull/pair/add machine and index writer in sequence.
Its allowance includes the input rearrangement and the materialized intermediate counts. -/
noncomputable def stepCertificate : NativeCertificate
    (fun ((parameters, rows), operand) => step parameters rows operand)
    (NativeCertificate.encFoldStep parameterEncoding encNatPairList encNat) encNatPairList := by
  let e := NativeCertificate.encFoldStep parameterEncoding encNatPairList encNat
  let original : NativeCertificate (id : (Parameters × List (ℕ × ℕ)) × ℕ → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let argument := ((original.fst.fst.fst.prod original.snd).prod
    original.fst.fst.snd).prod original.fst.snd
  exact (indexCertificate.comp (layerCertificate.comp argument)).congr (fun _ => rfl)

private noncomputable def initializationCertificate : NativeCertificate
    CounterInitialization.run CounterInitialization.encoding encNatPairList :=
  let P := Classical.choose CounterInitialization.run_computable
  ⟨fun input => 2^input.1*P ((CounterInitialization.encoding input).length+1),
    fun input => 2^input.1*P ((CounterInitialization.encoding input).length+1),
    (Classical.choose_spec CounterInitialization.run_computable).2.2⟩

/-- Reversing the original operand tape is scalar preprocessing, before table allocation. -/
def orderedOperands (input : Input) : List ℕ :=
  let (inverse, (_, operands)) := input
  if inverse then operands.reverse else operands

private theorem ordered_polyTime : ComputableInPolyTime orderedOperands encoding
    (encList encNat) := by
  unfold orderedOperands
  fun_prop

/-- Original scalar preprocessing and dense initialization, before the operand fold. -/
noncomputable def setupCertificate : NativeCertificate
    (fun input : Input =>
      let (inverse, ((width, seed), _)) := input
      ((width, inverse), (CounterInitialization.run (width, seed), orderedOperands input)))
    encoding (encPair parameterEncoding (encPair encNatPairList (encList encNat))) := by
  let original : NativeCertificate (id : Input → Input) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let parameters := original.snd.fst.fst.prod original.fst
  let initialized := initializationCertificate.comp original.snd.fst
  exact parameters.prod (initialized.prod (NativeCertificate.ofPolyTime ordered_polyTime))

/-- One native machine initializes from original data, iterates in the chosen direction,
reindexes each genuine update, and returns the complete encoded table. No executable,
initial table or execution conclusion is an endpoint premise. Resource profiles retain
all copied table wires, callbacks, control and output; sharp DP normalization is separate. -/
noncomputable def runCertificate : NativeCertificate run encoding encNatPairList :=
  ((NativeCertificate.foldlStream parameterEncoding encNatPairList encNat step
    stepCertificate).comp setupCertificate).congr (fun _ => rfl)

/-- Original operands represented by the state after exactly `j` actual machine updates.
Inverse processing consumes a suffix from right to left. -/
def prefixWords {m : ℕ} (inverse : Bool) (as : List (BitVec m)) (j : ℕ) : List (BitVec m) :=
  if inverse then (as.reverse.take j).reverse else as.take j

/-- Every actual intermediate table is itself a complete original-input counter table. -/
theorem prefix_run {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool) (j : ℕ) :
    ((orderedOperands (ofWords inverse seed as)).take j).foldl (step (m, inverse))
      (CounterInitialization.run (m, seed.toNat)) =
        run (ofWords inverse seed (prefixWords inverse as j)) := by
  cases inverse <;> simp [orderedOperands, ofWords, prefixWords, run, List.map_reverse,
    List.map_take]

private theorem counter_size {m : ℕ} (as : List (BitVec m)) (seed : BitVec m)
    (inverse : Bool) (s : BitVec m) :
    Nat.size ((if inverse then WordTable.backwardCounters as seed
      else WordTable.classCounters as seed).read s) ≤ as.length+1 := by
  have hf := WordTable.classCounters_size_le (fun i : Fin as.length => as[i.val]) seed s
  have hb := WordTable.backwardCounters_size_le (fun i : Fin as.length => as[i.val]) seed s
  simp only [List.ofFn_getElem] at hf hb
  split <;> assumption

/-- Physical prefix wires are linear in the number of states and original scalar widths.
This includes the initial/final tables, physical zero counters and numeric keys. -/
theorem prefix_wire {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool) (j : ℕ) :
    (encNatPairList
      (((orderedOperands (ofWords inverse seed as)).take j).foldl (step (m, inverse))
        (CounterInitialization.run (m, seed.toNat)))).length ≤
      2^m*(4*m+2*as.length+5) := by
  rw [prefix_run, run_words]
  let bs := prefixWords inverse as j
  have len : bs.length ≤ as.length := by
    cases inverse <;> simp [bs, prefixWords, List.length_take]
  let table := if inverse then WordTable.backwardCounters bs seed
    else WordTable.classCounters bs seed
  have counts (s : BitVec m) : Nat.size (table.read s) ≤ as.length+1 :=
    (counter_size bs seed inverse s).trans (by omega)
  have rows := CounterPull.graph_record_width table.read counts
  have wire := length_encList_le (encPair encNat encNat) (CounterPull.graph table.read) rows
  rw [CounterPull.graph_length] at wire
  convert wire using 1; ring

/-- The whole installed DP charges setup and the actual fold's callback sum/maximum.
The fixed multiplier is selected before any original width, operand list or direction.
No desired clock or workspace conclusion is a hypothesis. -/
theorem runCertificate_bounds : ∃ K : ℕ, ∀ input,
    runCertificate.time input ≤ setupCertificate.time input +
      K*NativeCertificate.foldTimeBudget parameterEncoding encNatPairList encNat step
        stepCertificate
        (let (inverse, ((width, seed), _)) := input
         ((width, inverse), (CounterInitialization.run (width, seed), orderedOperands input))) ∧
    runCertificate.space input ≤ setupCertificate.space input +
      K*NativeCertificate.foldSpaceBudget parameterEncoding encNatPairList encNat step
        stepCertificate
        (let (inverse, ((width, seed), _)) := input
         ((width, inverse), (CounterInitialization.run (width, seed), orderedOperands input))) := by
  obtain ⟨K, hk⟩ := NativeCertificate.foldlStream_bounds parameterEncoding encNatPairList encNat
    step stepCertificate
  refine ⟨K, fun input => ?_⟩
  exact ⟨Nat.add_le_add_left (hk _).1 _, Nat.add_le_add_left (hk _).2 _⟩

private theorem step_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m B : ℕ} (table : WordTable ℕ m) (_bound : ∀ s, Nat.size (table.read s) ≤ B)
      (a : BitVec m) (inverse : Bool),
      stepCertificate.time (((m, inverse), CounterPull.graph table.read), a.toNat) ≤
        2^m*P (m+B+1) ∧
      stepCertificate.space (((m, inverse), CounterPull.graph table.read), a.toNat) ≤
        2^m*P (m+B+1) := by
  let P := Classical.choose CounterPairing.layer_computable
  let Q := Classical.choose IndexNat.run_computable
  have hp : Cslib.PolynomiallyBounded P :=
    (Classical.choose_spec CounterPairing.layer_computable).1
  have mp : Monotone P := (Classical.choose_spec CounterPairing.layer_computable).2.1
  have hq : Cslib.PolynomiallyBounded Q := (Classical.choose_spec IndexNat.run_computable).1
  have mq : Monotone Q := (Classical.choose_spec IndexNat.run_computable).2.1
  let R := fun b => 100*b+100+2*P (10*(b+1))+2*Q (3*(b+1))
  have hr : Cslib.PolynomiallyBounded R := by dsimp only [R]; fun_prop
  have mr : Monotone R := by
    intro a b h
    have := mp (by omega : 10*(a+1) ≤ 10*(b+1))
    have := mq (by omega : 3*(a+1) ≤ 3*(b+1))
    dsimp only [R]
    omega
  refine ⟨R, hr, mr, ?_⟩
  intro m B table bound a inverse
  let input := (((m, a.toNat), inverse), CounterPull.graph table.read)
  let b := m+B+1
  have w : CounterPairing.width input ≤ 10*(b+1) := by
    have hw := CounterPull.graph_width table.read bound a inverse false
    have larger : CounterPairing.width input ≤ CounterPull.width
        (((m, a.toNat), (inverse, false)), CounterPull.graph table.read) := by
      dsimp only [CounterPairing.width, CounterPairing.parameterEncoding,
        CounterPull.width, CounterPull.parameterEncoding, input]
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega
    dsimp only [b]
    omega
  let result := advance inverse a table
  have countBound (s : BitVec m) : Nat.size (result.read s) ≤ B+1 := by
    have sumBound (x y : BitVec m) : Nat.size (table.read x+table.read y) ≤ B+1 := by
      have hx := Nat.size_le.mp (bound x)
      have hy := Nat.size_le.mp (bound y)
      apply Nat.size_le.mpr
      rw [pow_succ]
      omega
    cases inverse <;> simpa only [result, advance, Bool.false_eq_true, ite_false, ite_true,
      WordTable.countAdvance_read, WordTable.countBackAdvance_read] using sumBound _ _
  have resultEq : CounterPairing.layer input = List.ofFn (fun i : Fin (2^m) =>
      result.read (BitVec.ofFin i)) := by
    simpa only [input, CounterPull.graph, List.map_ofFn, advance, result,
      Function.comp_def] using CounterPairing.layer_table table a inverse
  have resultLength : (CounterPairing.layer input).length = 2^m := by
    rw [resultEq, List.length_ofFn]
  have resultMax : streamRecordLength encNat (CounterPairing.layer input) ≤ B+1 := by
    apply listMax_le
    intro n hn
    rw [resultEq] at hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    simpa only [encNat_apply, Nat.size_eq_bits_len] using countBound (BitVec.ofFin i)
  have indexBits : (encNat (2^m)).length ≤ m+1 := by
    apply length_encNat_le_of_lt_two_pow
    rw [pow_succ]
    have := Nat.two_pow_pos m
    omega
  have v : IndexNat.width (CounterPairing.layer input) ≤ 3*(b+1) := by
    dsimp only [IndexNat.width]
    rw [resultLength]
    dsimp only [b]
    omega
  have recordBound := CounterPull.graph_record_width table.read bound
  have wire := length_encList_le (encPair encNat encNat) (CounterPull.graph table.read)
    recordBound
  rw [CounterPull.graph_length] at wire
  have operand := length_encNat_le_of_lt_two_pow a.isLt
  have positive := Nat.two_pow_pos m
  have wireBudget : (NativeCertificate.encFoldStep parameterEncoding encNatPairList encNat
      (((m, inverse), CounterPull.graph table.read), a.toNat)).length ≤ 2^m*(20*b+20) := by
    simp only [NativeCertificate.encFoldStep, parameterEncoding, length_encPair,
      encUnary_apply, List.length_replicate, encBool_apply, List.length_singleton]
    dsimp only [b]
    nlinarith [Nat.mul_le_mul_left m (show 1 ≤ 2^m by omega)]
  have layerCost := Nat.mul_le_mul (by omega : 2^m+1 ≤ 2*2^m) (mp w)
  have indexCost := Nat.mul_le_mul (by omega : 2^m+1 ≤ 2*2^m) (mq v)
  have estimate : 4*(NativeCertificate.encFoldStep parameterEncoding encNatPairList encNat
      (((m, inverse), CounterPull.graph table.read), a.toNat)).length+
      (2^m+1)*P (CounterPairing.width input)+
      (2^m+1)*Q (IndexNat.width (CounterPairing.layer input)) ≤ 2^m*R b := by
    dsimp only [R]
    nlinarith only [wireBudget, layerCost, indexCost]
  constructor <;>
    simp only [stepCertificate, layerCertificate, indexCertificate, NativeCertificate.congr,
      NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
      NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq,
      CounterPull.graph_length, resultLength, input]
  all_goals
    convert estimate using 1; ring

end Cslib.Cryptanalysis.AddXNOR.CounterDP
