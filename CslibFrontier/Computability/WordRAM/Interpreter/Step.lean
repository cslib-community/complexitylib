/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ProgramLiterals.Encoding
public import CslibFrontier.Computability.WordRAM.Turing.ListOutput
public import CslibFrontier.Computability.GenericRAM.SparseMemory.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Turing
import all CslibFrontier.Computability.WordRAM.Native
import all CslibFrontier.Computability.WordRAM.Defs
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.GenericRAM.Simulation.Finite
import all CslibFrontier.Computability.GenericRAM.Simulation.Turing
import all CslibFrontier.Computability.WordRAM.ProgramLiterals.Encoding

/-!
# A program-input word-RAM instruction interpreter on binary tapes

Instructions are runtime rows in the explicit native program encoding. The
interpreter reads their opcode, register indices, literals and labels; one fixed
finite opcode dispatcher handles every program. Checked binary operations reuse
the actual standard-basis bit implementations, including overflow-safe shifts.
Sparse reads/updates use the charged association-list machines.

The register count is fixed; programs, word width, instruction fields and states
are runtime inputs. Malformed rows have total default-field semantics, with
unknown opcodes faulting. Correctness is proved on every encoded native program;
malformed bitstream recognition is not asserted.
-/

public section

namespace Cslib.WordRAM.Interpreter

open Turing.MultiTapeTM Cslib.GenericRAM

local notation "PolyTime" => Turing.MultiTapeTM.ComputableInPolyTime

/-- Program counter, registers, memory default and the actual finite sparse store. -/
abbrev Tuple (r : ℕ) := ℕ × (Fin r → ℕ) × ℕ × SparseMemory ℕ ℕ
/-- Complete encoded finite state; zero bindings remain represented. -/
noncomputable abbrev tupleEncoding (r : ℕ) : Tuple r ↪ List Bool :=
  encPair encNat (encPair (encPi encNat) (encPair encNat (SparseMemory.encoding encNat encNat)))
/-- Fault, continuation and returned word have separate tags. -/
abbrev Result (r : ℕ) := Option (Sum (Tuple r) ℕ)
/-- The complete result wire. -/
noncomputable abbrev resultEncoding (r : ℕ) : Result r ↪ List Bool :=
  encOption (encSum (tupleEncoding r) encNat)
/-- Runtime width, current instruction row and current state. -/
abbrev Context (r : ℕ) := (ℕ × List ℕ) × Tuple r
/-- Width is unary; opcode fields and the full state use binary natural encodings. -/
noncomputable abbrev contextEncoding (r : ℕ) : Context r ↪ List Bool :=
  encPair (encPair encUnary (encList encNat)) (tupleEncoding r)

/-- Read a runtime register index; out-of-range indices yield zero. -/
def readReg {r : ℕ} (s : Tuple r) (i : ℕ) : ℕ := (List.ofFn s.2.1).getD i 0
/-- Update a runtime register index, preserving every other field. -/
def setReg {r : ℕ} (s : Tuple r) (i v : ℕ) : Tuple r :=
  (s.1, (fun j => if j.val = i then v else s.2.1 j), s.2.2)
/-- Continue at a runtime label without changing data. -/
def next {r : ℕ} (pc : ℕ) (s : Tuple r) : Result r := some (.inl (pc, s.2))

/-- Register selection is a charged bit computation, uniform in the supplied index. -/
theorem readReg_polyTime {r : ℕ} : PolyTime
    (fun q : Tuple r × ℕ => readReg q.1 q.2)
    (encPair (tupleEncoding r) encNat) encNat := by
  have table : PolyTime (fun q : Tuple r × ℕ => List.ofFn q.1.2.1)
      (encPair (tupleEncoding r) encNat) (encList encNat) := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0 table.tidy
    (Turing.MultiTapeTM.ComputableInPolyTime.snd (tupleEncoding r) encNat).tidy)

/-- Register updates materialize the fixed finite tuple and preserve the sparse memory. -/
theorem setReg_polyTime {r : ℕ} : PolyTime
    (fun q : Tuple r × (ℕ × ℕ) => setReg q.1 q.2.1 q.2.2)
    (encPair (tupleEncoding r) (encPair encNat encNat)) (tupleEncoding r) := by
  have index (i : Fin r) : PolyTime (fun _ : Tuple r × (ℕ × ℕ) => i.val)
      (encPair (tupleEncoding r) (encPair encNat encNat)) encNat := .const i.val
  unfold setReg
  fun_prop

private theorem next_polyTime {r : ℕ} : PolyTime
    (fun q : ℕ × Tuple r => next q.1 q.2)
    (encPair encNat (tupleEncoding r)) (resultEncoding r) := by
  unfold next
  fun_prop

/-- Select a computed runtime register from a computed full state. -/
@[fun_prop] theorem readReg_withInput {r : ℕ} {α : Type} {enc : α ↪ List Bool}
    {s : α → Tuple r} {i : α → ℕ}
    (hs : PolyTime s enc (tupleEncoding r)) (hi : PolyTime i enc encNat) :
    PolyTime (fun x => readReg (s x) (i x)) enc encNat :=
  readReg_polyTime.comp (hs.prod hi)

/-- Update a computed runtime register while charging the full tuple. -/
@[fun_prop] theorem setReg_withInput {r : ℕ} {α : Type} {enc : α ↪ List Bool}
    {s : α → Tuple r} {i v : α → ℕ}
    (hs : PolyTime s enc (tupleEncoding r)) (hi : PolyTime i enc encNat)
    (hv : PolyTime v enc encNat) :
    PolyTime (fun x => setReg (s x) (i x) (v x)) enc (tupleEncoding r) :=
  setReg_polyTime.comp (hs.prod (hi.prod hv))

@[fun_prop] private theorem next_withInput {r : ℕ} {α : Type} {enc : α ↪ List Bool}
    {s : α → Tuple r} {pc : α → ℕ}
    (hp : PolyTime pc enc encNat) (hs : PolyTime s enc (tupleEncoding r)) :
    PolyTime (fun x => next (pc x) (s x)) enc (resultEncoding r) :=
  next_polyTime.comp (hp.prod hs)

@[fun_prop] private theorem memoryRead_withInput {α : Type} {enc : α ↪ List Bool}
    {mem : α → SparseMemory ℕ ℕ} {addr fill : α → ℕ}
    (hm : PolyTime mem enc (SparseMemory.encoding encNat encNat))
    (ha : PolyTime addr enc encNat) (hf : PolyTime fill enc encNat) :
    PolyTime (fun x => SparseMemory.read (fill x) (addr x) (mem x)) enc encNat :=
  (SparseMemory.read_polytime encNat encNat).comp ((ha.prod hm).prod hf)

private theorem memoryWrite_withInput {α : Type} {enc : α ↪ List Bool}
    {mem : α → SparseMemory ℕ ℕ} {addr value : α → ℕ}
    (hm : PolyTime mem enc (SparseMemory.encoding encNat encNat))
    (ha : PolyTime addr enc encNat) (hv : PolyTime value enc encNat) :
    PolyTime (fun x => AList.insert (β := fun _ : ℕ => ℕ) (addr x) (value x) (mem x)) enc
      (SparseMemory.encoding encNat encNat) := by
  have h := (SparseMemory.insert_polytime encNat encNat).comp ((ha.prod hv).prod hm)
  exact h.of_enc_eq (fun _ => rfl)

attribute [fun_prop] memoryWrite_withInput

private theorem binaryArgs_polyTime : PolyTime
    (fun q : ℕ × ℕ => ![q.1, q.2]) (encPair encNat encNat) (encPi encNat) := by
  apply Turing.MultiTapeTM.ComputableInPolyTime.pi
  intro i
  fin_cases i
  · change PolyTime (fun q : ℕ × ℕ => q.1) _ _
    fun_prop
  · change PolyTime (fun q : ℕ × ℕ => q.2) _ _
    fun_prop

/-- Finite operation-symbol dispatch, with every operation's width check executed. -/
def binaryDispatch : List BinOp → ℕ → ℕ × (ℕ × ℕ) → Option ℕ
  | [], _, _ => none
  | f :: fs, tag, x => if tag = 0 then
      Basis.standard.genericModel.checkedOp (.bin f) (x.1, ![x.2.1, x.2.2])
    else binaryDispatch fs (tag - 1) x

/-- All ten standard operation symbols, in the actual instruction wire order. -/
def binaryOps : List BinOp := [.add, .sub, .mul, .div, .mod, .and, .or, .xor,
  .shiftLeft, .shiftRight]

/-- Dispatch is uniform in the operation tag, width and arbitrary binary operands. -/
theorem binaryDispatch_polyTime (fs : List BinOp) : PolyTime
    (fun q : ℕ × (ℕ × (ℕ × ℕ)) => binaryDispatch fs q.1 q.2)
    (encPair encNat (encPair encUnary (encPair encNat encNat))) (encOption encNat) := by
  induction fs with
  | nil => exact .const none
  | cons f fs ih =>
    have op := checkedOp_polyTime (.bin f)
    have args := binaryArgs_polyTime
    have head : PolyTime
        (fun q : ℕ × (ℕ × (ℕ × ℕ)) =>
          Basis.standard.genericModel.checkedOp (.bin f) (q.2.1, ![q.2.2.1, q.2.2.2]))
        (encPair encNat (encPair encUnary (encPair encNat encNat))) (encOption encNat) := by
      have hw : PolyTime (fun q : ℕ × (ℕ × (ℕ × ℕ)) => q.2.1)
          (encPair encNat (encPair encUnary (encPair encNat encNat))) encUnary := by fun_prop
      have ha : PolyTime (fun q : ℕ × (ℕ × (ℕ × ℕ)) => (q.2.2.1, q.2.2.2))
          (encPair encNat (encPair encUnary (encPair encNat encNat)))
          (encPair encNat encNat) := by fun_prop
      exact op.comp (hw.prod (args.comp ha))
    have tail : PolyTime
        (fun q : ℕ × (ℕ × (ℕ × ℕ)) => binaryDispatch fs (q.1 - 1) q.2)
        (encPair encNat (encPair encUnary (encPair encNat encNat))) (encOption encNat) := by
      exact ih.comp (show PolyTime
        (fun q : ℕ × (ℕ × (ℕ × ℕ)) => (q.1 - 1, q.2))
        (encPair encNat (encPair encUnary (encPair encNat encNat)))
        (encPair encNat (encPair encUnary (encPair encNat encNat))) by fun_prop)
    change PolyTime (fun q : ℕ × (ℕ × (ℕ × ℕ)) => if q.1 = 0 then _ else _) _ _
    fun_prop

/-- A handler reads its own literal/register/label fields from the runtime row. -/
def constant {r : ℕ} (x : Context r) : Result r :=
  let v := x.1.2.getD 2 0
  if v < 2 ^ x.1.1 then next (x.2.1 + 1) (setReg x.2 (x.1.2.getD 1 0) v) else none
/-- Runtime copy, with the standard basis's unmodified move convention. -/
def copy {r : ℕ} (x : Context r) : Result r :=
  next (x.2.1 + 1) (setReg x.2 (x.1.2.getD 1 0) (readReg x.2 (x.1.2.getD 2 0)))
/-- Runtime binary ALU selection, retaining operation faults and overflow. -/
def binary {r : ℕ} (x : Context r) : Result r :=
  (binaryDispatch binaryOps (x.1.2.getD 1 0)
    (x.1.1, readReg x.2 (x.1.2.getD 3 0), readReg x.2 (x.1.2.getD 4 0))).elim none
    (fun v => next (x.2.1 + 1) (setReg x.2 (x.1.2.getD 2 0) v))
/-- Reading the actual runtime physical word width. -/
def width {r : ℕ} (x : Context r) : Result r :=
  next (x.2.1 + 1) (setReg x.2 (x.1.2.getD 1 0) x.1.1)
/-- A charged sparse lookup at the runtime source register's address. -/
def load {r : ℕ} (x : Context r) : Result r :=
  next (x.2.1 + 1) (setReg x.2 (x.1.2.getD 1 0)
    (SparseMemory.read x.2.2.2.1 (readReg x.2 (x.1.2.getD 2 0)) x.2.2.2.2))
/-- A charged sparse update, including bindings whose new value is zero. -/
def store {r : ℕ} (x : Context r) : Result r :=
  let a := readReg x.2 (x.1.2.getD 1 0)
  let v := readReg x.2 (x.1.2.getD 2 0)
  some (.inl (x.2.1 + 1, x.2.2.1,
    x.2.2.2.1, AList.insert (β := fun _ : ℕ => ℕ) a v x.2.2.2.2))
/-- A runtime jump label. -/
def jump {r : ℕ} (x : Context r) : Result r := next (x.1.2.getD 1 0) x.2
/-- Runtime equality and branch labels. -/
def branchEq {r : ℕ} (x : Context r) : Result r :=
  next (if readReg x.2 (x.1.2.getD 1 0) = readReg x.2 (x.1.2.getD 2 0)
    then x.1.2.getD 3 0 else x.2.1 + 1) x.2
/-- Runtime unsigned comparison and branch labels. -/
def branchLt {r : ℕ} (x : Context r) : Result r :=
  next (if readReg x.2 (x.1.2.getD 1 0) < readReg x.2 (x.1.2.getD 2 0)
    then x.1.2.getD 3 0 else x.2.1 + 1) x.2
/-- Return the actual runtime output register; deterministic random instructions fault. -/
def halt {r : ℕ} (x : Context r) : Result r := some (.inr (readReg x.2 (x.1.2.getD 1 0)))

/-- The fixed instruction-set dispatcher, independent of program length and literals. -/
def handlers (r : ℕ) : List (Context r → Result r) :=
  [constant, copy, binary, width, load, store, jump, branchEq, branchLt, halt]

/-- Dispatch a finite set of semantic operations, using a runtime numeric opcode. -/
def dispatch {r : ℕ} : List (Context r → Result r) → ℕ × Context r → Result r
  | [], _ => none
  | f :: fs, x => if x.1 = 0 then f x.2 else dispatch fs (x.1 - 1, x.2)

private theorem constant_polyTime {r : ℕ} : PolyTime (constant (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold constant
  fun_prop

private theorem copy_polyTime {r : ℕ} : PolyTime (copy (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold copy
  fun_prop

private theorem binary_polyTime {r : ℕ} : PolyTime (binary (r := r))
    (contextEncoding r) (resultEncoding r) := by
  have alu := binaryDispatch_polyTime binaryOps
  unfold binary
  fun_prop

private theorem width_polyTime {r : ℕ} : PolyTime (width (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold width
  fun_prop

private theorem load_polyTime {r : ℕ} : PolyTime (load (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold load
  fun_prop

private theorem store_polyTime {r : ℕ} : PolyTime (store (r := r))
    (contextEncoding r) (resultEncoding r) := by
  have hm : PolyTime (fun x : Context r =>
      AList.insert (β := fun _ : ℕ => ℕ)
        (readReg x.2 (x.1.2.getD 1 0)) (readReg x.2 (x.1.2.getD 2 0)) x.2.2.2.2)
      (contextEncoding r) (SparseMemory.encoding encNat encNat) :=
    memoryWrite_withInput (by fun_prop) (by fun_prop) (by fun_prop)
  have hp : PolyTime (fun x : Context r => x.2.1 + 1) (contextEncoding r) encNat := by
    fun_prop
  have hr : PolyTime (fun x : Context r => x.2.2.1)
      (contextEncoding r) (encPi encNat) := by fun_prop
  have hd : PolyTime (fun x : Context r => x.2.2.2.1)
      (contextEncoding r) encNat := by fun_prop
  have h := (hp.prod (hr.prod (hd.prod hm)))
  have hi := (Turing.MultiTapeTM.ComputableInPolyTime.sumInl (tupleEncoding r) encNat).comp h
  have ho := (Turing.MultiTapeTM.ComputableInPolyTime.optionSome
    (encSum (tupleEncoding r) encNat)).comp hi
  exact ho.of_enc_eq (fun _ => rfl)

private theorem jump_polyTime {r : ℕ} : PolyTime (jump (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold jump
  fun_prop

private theorem branchEq_polyTime {r : ℕ} : PolyTime (branchEq (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold branchEq
  fun_prop

private theorem branchLt_polyTime {r : ℕ} : PolyTime (branchLt (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold branchLt
  fun_prop

private theorem halt_polyTime {r : ℕ} : PolyTime (halt (r := r))
    (contextEncoding r) (resultEncoding r) := by
  unfold halt
  fun_prop

/-- Every concrete instruction handler has a uniform polynomial bit implementation. -/
theorem handlers_polyTime {r : ℕ} : ∀ f ∈ handlers r,
    PolyTime f (contextEncoding r) (resultEncoding r) := by
  intro f hf
  simp only [handlers, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact constant_polyTime
  · exact copy_polyTime
  · exact binary_polyTime
  · exact width_polyTime
  · exact load_polyTime
  · exact store_polyTime
  · exact jump_polyTime
  · exact branchEq_polyTime
  · exact branchLt_polyTime
  · exact halt_polyTime

/-- The one opcode selector has no constants depending on the runtime program. -/
theorem dispatch_polyTime {r : ℕ} (fs : List (Context r → Result r))
    (hf : ∀ f ∈ fs, PolyTime f (contextEncoding r) (resultEncoding r)) :
    PolyTime (dispatch fs) (encPair encNat (contextEncoding r)) (resultEncoding r) := by
  induction fs with
  | nil => exact .const none
  | cons f fs ih =>
    have hfin := hf f (by simp)
    have head := hfin.comp
      (Turing.MultiTapeTM.ComputableInPolyTime.snd encNat (contextEncoding r))
    have tail := (ih (fun f h => hf f (by simp [h]))).comp (show PolyTime
      (fun x : ℕ × Context r => (x.1 - 1, x.2))
      (encPair encNat (contextEncoding r)) (encPair encNat (contextEncoding r)) by fun_prop)
    change PolyTime (fun x : ℕ × Context r => if x.1 = 0 then _ else _) _ _
    fun_prop

/-- Interpret the supplied instruction row, rather than selecting a fixed program. -/
def evalRow {r : ℕ} (x : Context r) : Result r := dispatch (handlers r) (x.1.2.headD 0, x)

/-- A single finite bit machine implements every encoded instruction row. -/
theorem evalRow_polyTime {r : ℕ} : PolyTime (evalRow (r := r))
    (contextEncoding r) (resultEncoding r) := by
  apply (dispatch_polyTime (handlers r) handlers_polyTime).comp
  fun_prop

/-- Runtime physical width, complete program rows and finite state. -/
abbrev Input (r : ℕ) := (ℕ × List (List ℕ)) × Tuple r
/-- The runtime program is present on the tape, not in the machine's control. -/
noncomputable abbrev inputEncoding (r : ℕ) : Input r ↪ List Bool :=
  encPair (encPair encUnary (encList (encList encNat))) (tupleEncoding r)

/-- Fetch the actual row at the binary program counter and execute it. -/
def step {r : ℕ} (x : Input r) : Result r :=
  if x.2.1 < x.1.2.length then evalRow ((x.1.1, x.1.2.getD x.2.1 []), x.2) else none

/-- Program lookup uses capped binary indexing, so enormous labels do not require unary scans. -/
theorem step_polyTime {r : ℕ} : PolyTime (step (r := r))
    (inputEncoding r) (resultEncoding r) := by
  have rows : PolyTime (fun x : Input r => x.1.2) (inputEncoding r)
      (encList (encList encNat)) := by fun_prop
  have pc : PolyTime (fun x : Input r => x.2.1) (inputEncoding r) encNat := by fun_prop
  have fetch : PolyTime (fun x : Input r => x.1.2.getD x.2.1 [])
      (inputEncoding r) (encList encNat) :=
    (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.listGetD_binary [] rows.tidy pc.tidy)).of_enc_eq
        (fun _ => rfl)
  have arg : PolyTime
      (fun x : Input r => ((x.1.1, x.1.2.getD x.2.1 []), x.2))
      (inputEncoding r) (contextEncoding r) := by fun_prop
  have heval := evalRow_polyTime.comp arg
  have len := (ComputableTidilyInPolyTime.length_list (encList encNat)).comp rows.tidy
  have lenBinary := ComputableTidilyInPolyTime.unary_to_binary.comp len
  have guard := ComputableTidilyInPolyTime.binary_lt.comp (pc.tidy.prod lenBinary)
  apply (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy
    (guard.cond heval.tidy (.const none))).of_enc_eq
  intro x
  simp only [step, Function.comp_apply, decide_eq_true_eq]

end Cslib.WordRAM.Interpreter
