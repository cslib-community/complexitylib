/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Interpreter.Run
public import Complexity.Computability.WordRAM.Turing.ListOutput
import all Complexity.Computability.WordRAM.Interpreter.Step
import all Complexity.Computability.WordRAM.Interpreter.Refinement
import all Complexity.Computability.WordRAM.ProgramLiterals.Encoding
import all Complexity.Computability.WordRAM.ListOutput
import all Complexity.Computability.WordRAM.Turing.ListOutput
import all Complexity.Computability.GenericRAM.Simulation.Turing

/-!
# Runtime program parking and charged output extraction

Halts are replaced by runtime-label jumps and register parking loops are
materialized on tape. The output reader uses the runtime program length, selects
the recorded register and scans every returned cell, including unwritten zeros.
Neither program-dependent interpreter constants nor free output decoding occur.
-/

public section

namespace Cslib.WordRAM.Interpreter

open Turing.MultiTapeTM Cslib.GenericRAM
open NativeCertificate
local notation "PolyTime" => Turing.MultiTapeTM.ComputableInPolyTime

/-- Replace a runtime halt row by a jump to its parking label. -/
def parkRow (x : ℕ × List ℕ) : List ℕ :=
  if x.2.headD 0 = 9 then [6, x.1 + x.2.getD 1 0] else x.2

/-- Materialize the parking transformation on arbitrary runtime rows. -/
def parkRows (r : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map (fun row => parkRow (rows.length, row)) ++
    List.ofFn (fun i : Fin r => [6, rows.length + i.val])

/-- Runtime halt transformation is polynomial in the full field encoding. -/
theorem parkRow_polyTime : PolyTime parkRow (encPair encNat (encList encNat))
    (encList encNat) := by unfold parkRow; fun_prop

/-- Parking generation charges every row, label and appended self-loop. -/
theorem parkRows_polyTime (r : ℕ) : PolyTime (parkRows r)
    (encList (encList encNat)) (encList (encList encNat)) := by
  have len := ComputableTidilyInPolyTime.unary_to_binary.comp
    (ComputableTidilyInPolyTime.length_list (encList encNat))
  have hm := ComputableTidilyInPolyTime.mapWith parkRow_polyTime.tidy len
    (ComputableTidilyInPolyTime.id' (encIn := encList (encList encNat)))
  have hi (i : Fin r) : ComputableTidilyInPolyTime (fun _ : List (List ℕ) => i.val)
      (encList (encList encNat)) encNat := .const i.val
  have tail : ComputableTidilyInPolyTime
      (fun rows : List (List ℕ) => List.ofFn (fun i : Fin r => [6, rows.length + i.val]))
      (encList (encList encNat)) (encList (encList encNat)) := by fun_prop
  exact .of_tidy ((ComputableTidilyInPolyTime.listAppend (encList encNat)).comp
    (hm.prod tail))

/-- Every instruction's transformed row is the row of its native parking instruction. -/
theorem parkRow_record {r : ℕ} (L : ℕ) (i : Instr .standard r) :
    parkRow (L, ProgramLiterals.record i) = ProgramLiterals.record (i.parkHalt L) := by
  cases i with
  | op o => cases o with
    | alu f d a => cases f <;> simp [parkRow, ProgramLiterals.record, Instr.parkHalt]
    | _ => simp [parkRow, ProgramLiterals.record, Instr.parkHalt]
  | branch c t => cases c <;> simp [parkRow, ProgramLiterals.record, Instr.parkHalt]
  | _ => simp [parkRow, ProgramLiterals.record, Instr.parkHalt]

/-- Parking operates on the actual program representation, preserving every non-halt field. -/
theorem parkRows_serialize {r : ℕ} (p : Program .standard r) :
    parkRows r (ProgramLiterals.serialize p) = ProgramLiterals.serialize p.parkHalts := by
  simp only [parkRows, ProgramLiterals.serialize, List.length_map, Program.parkHalts,
    List.map_append, List.map_map, List.map_ofFn]
  congr 1
  exact List.map_congr_left (fun i _ => parkRow_record p.length i)

/-- One bit machine parks every runtime program; the complete transformed program is charged. -/
noncomputable def parkingCertificate {r : ℕ} : NativeCertificate
    (Program.parkHalts (B := Basis.standard) (r := r))
    (ProgramLiterals.programEncoding r) (ProgramLiterals.programEncoding r) := by
  let serial : NativeCertificate (ProgramLiterals.serialize (r := r))
      (ProgramLiterals.programEncoding r) (encList (encList encNat)) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  let c := (NativeCertificate.ofPolyTime (parkRows_polyTime r)).comp serial
  exact ⟨c.time, c.space, c.computes.of_enc_eq (fun p => by
    rw [Function.comp_apply, parkRows_serialize]
    rfl)⟩

/-- Select among a fixed register set using a runtime program length and runtime label. -/
def select {r : ℕ} (x : ℕ × Tuple r) : List (Fin r) → ℕ
  | [] => 0
  | i :: rest => if x.2.1 = x.1 + i.val then x.2.2.1 i else select x rest

/-- Runtime output-register selection has constants independent of program length. -/
theorem select_polyTime {r : ℕ} (is : List (Fin r)) : PolyTime
    (fun x : ℕ × Tuple r => select x is) (encPair encNat (tupleEncoding r)) encNat := by
  induction is with
  | nil => exact .const 0
  | cons i is ih =>
    have hi : PolyTime (fun _ : ℕ × Tuple r => i.val)
        (encPair encNat (tupleEncoding r)) encNat := .const i.val
    change PolyTime (fun x : ℕ × Tuple r => if x.2.1 = x.1 + i.val then _ else _) _ _
    fun_prop

/-- The dynamic selector is exactly the original parked-state register observation. -/
theorem select_toTuple {r : ℕ} (L : ℕ) (s : FiniteState Basis.standard.genericModel r)
    (is : List (Fin r)) : select (L, toTuple s) is = parkedRegister L s is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [select, parkedRegister]
    split <;> split <;> first | rfl | exact ih | (simp_all [toTuple])

/-- Runtime length and complete parked finite state. -/
abbrev OutputInput (r : ℕ) := ℕ × FiniteState Basis.standard.genericModel r
/-- Output extraction never omits retained zero bindings from its input charge. -/
noncomputable abbrev outputInputEncoding (r : ℕ) : OutputInput r ↪ List Bool :=
  encPair encNat (FiniteState.encoding Basis.standard.encoding)

/-- The actual native output address is selected by a uniform bit computation. -/
noncomputable def addressCertificate {r : ℕ} : NativeCertificate
    (fun x : OutputInput r => parkedRegister x.1 x.2 (List.finRange r))
    (outputInputEncoding r) encNat := by
  let serial : NativeCertificate (fun x : OutputInput r => (x.1, toTuple x.2))
      (outputInputEncoding r) (encPair encNat (tupleEncoding r)) :=
    linear (ComputableInO.of_eq fun _ => rfl)
  exact congr ((NativeCertificate.ofPolyTime (select_polyTime (List.finRange r))).comp serial)
    (fun x => select_toTuple x.1 x.2 _)

/-- Read the real length-prefixed output using an actual binary-counted sparse-memory loop. -/
noncomputable def outputCertificate {r : ℕ} : NativeCertificate
    (fun x : OutputInput r => parkedOutput x.1 x.2) (outputInputEncoding r)
    (encList encNat) := by
  let hid : NativeCertificate (id : OutputInput r → OutputInput r)
      (outputInputEncoding r) (outputInputEncoding r) := linear (ComputableInO.of_eq fun _ => rfl)
  let state := snd hid
  let fields := FiniteState.Native.fields Basis.standard.encoding state
  let addr := addressCertificate (r := r)
  let length := FiniteState.Native.readCertificate Basis.standard.encoding state addr
  let initial := prod (prod (fst (snd (snd fields))) (snd (snd (snd fields))))
    (prod (post addr ComputableInDegree.natSucc.inO_one)
      (const (em := encList encNat) ([] : List ℕ)))
  exact congr (snd (snd (iterate length initial readRoundCertificate))) (fun x => by
    rw [iterate_readRound]
    simp [parkedOutput, outputList])

end Cslib.WordRAM.Interpreter
