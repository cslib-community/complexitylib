/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ProgramLiterals
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.WordRAM.ProgramLiterals

/-!
# A concrete binary encoding and literal-driven native program generator

Standard instructions are lists of at most five natural fields. Opcode and
operation tags, register indices, labels and scalar literals are all represented
explicitly; framed binary instruction lists give the program wire format. A
concrete decoder proves injectivity and reconstructs every executable, including
zero literals. Filling a fixed graph from computed literals has a charged
polynomial-time multitape implementation emitting that actual program encoding.
-/

public section

namespace Cslib.WordRAM.ProgramLiterals

open Turing.MultiTapeTM

/-- Binary-operation tags in the standard instruction wire format. -/
def binTag : BinOp → ℕ
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .and => 5 | .or => 6 | .xor => 7 | .shiftLeft => 8 | .shiftRight => 9

/-- Decode the ten standard binary operation tags, rejecting other values. -/
def decodeBin : ℕ → Option BinOp
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div | 4 => some .mod
  | 5 => some .and | 6 => some .or | 7 => some .xor
  | 8 => some .shiftLeft | 9 => some .shiftRight | _ => none

/-- Actual instruction fields; no scalar parameter or address is omitted from the wire. -/
def record {r : ℕ} : Instr .standard r → List ℕ
  | .op (.const d n) => [0, d, n]
  | .op (.copy d s) => [1, d, s]
  | .op (.alu (.bin f) d args) => [2, binTag f, d, args (0 : Fin 2), args (1 : Fin 2)]
  | .op (.alu .width d _) => [3, d]
  | .op (.load d a) => [4, d, a]
  | .op (.store a s) => [5, a, s]
  | .jump t => [6, t]
  | .branch (.eq i j) t => [7, i, j, t]
  | .branch (.lt i j) t => [8, i, j, t]
  | .halt i => [9, i]
  | .rand d s => [10, d, s]

/-- Decode a register number only when it fits the fixed register file. -/
def register (r n : ℕ) : Option (Fin r) := if h : n < r then some ⟨n, h⟩ else none

/-- A concrete parser for the program's instruction rows; invalid tags/registers are rejected. -/
def decodeRecord (r : ℕ) : List ℕ → Option (Instr .standard r)
  | [0, d, n] => do return .op (.const (← register r d) n)
  | [1, d, s] => do return .op (.copy (← register r d) (← register r s))
  | [2, f, d, a, b] => do
      return .op (.alu (.bin (← decodeBin f)) (← register r d)
        ![← register r a, ← register r b])
  | [3, d] => do return .op (.alu .width (← register r d) Fin.elim0)
  | [4, d, a] => do return .op (.load (← register r d) (← register r a))
  | [5, a, s] => do return .op (.store (← register r a) (← register r s))
  | [6, t] => some (.jump t)
  | [7, i, j, t] => do return .branch (.eq (← register r i) (← register r j)) t
  | [8, i, j, t] => do return .branch (.lt (← register r i) (← register r j)) t
  | [9, i] => do return .halt (← register r i)
  | [10, d, s] => do return .rand (← register r d) (← register r s)
  | _ => none

private theorem register_val {r : ℕ} (i : Fin r) : register r i = some i := by
  simp [register, i.isLt]

/-- Every encoded instruction reconstructs the identical operation, indices and immediates. -/
theorem decodeRecord_record {r : ℕ} (i : Instr .standard r) :
    decodeRecord r (record i) = some i := by
  cases i with
  | op o =>
    cases o with
    | alu f d args =>
      cases f with
      | bin f =>
        have hargs : ![args (0 : Fin 2), args (1 : Fin 2)] = args := by ext i; fin_cases i <;> rfl
        cases f <;> simp [record, decodeRecord, binTag, decodeBin, register_val, hargs]
      | width =>
        have hargs : Fin.elim0 = args := by ext i; exact Fin.elim0 i
        simp [record, decodeRecord, register_val, hargs]
    | _ => simp [record, decodeRecord, register_val]
  | branch c t => cases c <;> simp [record, decodeRecord, register_val]
  | _ => simp [record, decodeRecord, register_val]

/-- The explicit scalar-field rows of a complete native program. -/
def serialize {r : ℕ} (p : Program .standard r) : List (List ℕ) := p.map record

/-- Parse all instruction rows in order; a malformed row rejects the program. -/
def deserialize (r : ℕ) (rows : List (List ℕ)) : Option (Program .standard r) :=
  rows.mapM (decodeRecord r)

/-- Complete program roundtrip, not just agreement of an instruction count or graph shape. -/
theorem deserialize_serialize {r : ℕ} (p : Program .standard r) :
    deserialize r (serialize p) = some p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    dsimp only [deserialize, serialize] at ih
    simp only [deserialize, serialize, List.map_cons, List.mapM_cons, decodeRecord_record,
      bind, Option.bind_some]
    rw [ih]
    rfl

/-- Framed binary natural fields and instruction boundaries give an injective program encoding. -/
def programEncoding (r : ℕ) : Program .standard r ↪ List Bool where
  toFun p := encList (encList encNat) (serialize p)
  inj' := by
    intro p q h
    have rows := (encList (encList encNat)).injective h
    have parsed := congrArg (deserialize r) rows
    simpa only [deserialize_serialize, Option.some.injEq] using parsed

/-- A row has at most five scalar fields, independently of literal/address magnitude. -/
theorem record_length {r : ℕ} (i : Instr .standard r) : (record i).length ≤ 5 := by
  cases i with
  | op o => cases o with
    | alu f _ _ => cases f <;> simp [record]
    | _ => simp [record]
  | branch c _ => cases c <;> simp [record]
  | _ => simp [record]

/-- Program generation preserves its instruction count. -/
theorem serialize_fill_length {r : ℕ} (p : Program .standard r) (vs : List ℕ) :
    (serialize (Program.fillLiterals p vs)).length = p.length := by
  simp [serialize, Program.length_fillLiterals]

/-- A fixed graph is materialized in the actual binary program format by a polynomial-time
multitape computation on the framed binary literal list. No executable is a premise. -/
theorem serialize_fill_polyTime {r : ℕ} (p : Program .standard r) :
    ComputableInPolyTime (fun vs => serialize (Program.fillLiterals p vs))
      (encList encNat) (encList (encList encNat)) := by
  induction p with
  | nil => exact .const []
  | cons i p ih =>
    cases i with
    | op o =>
      cases o with
      | const d n =>
        have tail : ComputableInPolyTime
            (fun vs => serialize (Program.fillLiterals p vs.tail)) (encList encNat)
            (encList (encList encNat)) :=
          ih.comp
            (ComputableInPolyTime.tail (encA := encNat) (encL := encList encNat))
        change ComputableInPolyTime
          (fun vs : List ℕ => [0, d.val, vs.headD 0] ::
            serialize (Program.fillLiterals p vs.tail)) _ _
        fun_prop
      | _ =>
        change ComputableInPolyTime (fun vs => _ :: serialize (Program.fillLiterals p vs)) _ _
        fun_prop
    | _ =>
      change ComputableInPolyTime (fun vs => _ :: serialize (Program.fillLiterals p vs)) _ _
      fun_prop

end Cslib.WordRAM.ProgramLiterals
