/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeOutput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import all CslibFrontier.Cryptanalysis.AddXNORNativeOutput

/-!
# Concrete multitape bit decoding of native dissection outputs

A miss is the native word list `[0]`; a hit is `1 :: operators.map Bool.toNat`.
The ordinary framed binary word encoding is converted by one finite-state
transducer to `encOption encBits`: the empty word for a miss, and `true :: ops`
for a hit. The actual zero-work-tape machine takes at most six steps per output
operator plus nine, including status handling and halt.

This is an output-codec realization for the p. 6 bit conventions of
[WangLvShenZhang2027], not a simulation of sparse random-access memory or the
source sorted-list algorithm in Lemma 8/Theorem 7 (PDF pp. 21–22). Its input is
already the encoded represented output array. Extracting that array from a
bit-machine simulation of the RAM remains a separate obligation.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.OutputCodec

open Turing.MultiTapeTM
open Native.Driver

/-- Status word plus zero/one operator words, retaining successful empty witnesses. -/
def encode : Option (List Bool) → List ℕ
  | none => [0]
  | some ops => 1 :: ops.map Bool.toNat

/-- The actual framed binary word-list encoding consumed by the output machine. -/
def wire (out : Option (List Bool)) : List Bool := encList encNat (encode out)

/-- Six parser states distinguish the status frame from subsequent operator frames.
No word-sized registers, advice, memory access or simulation oracle are used. -/
@[expose] def decoder : Transducer Bool (Fin 6) where
  q₀ := 0
  step q b := match q.val, b with
    | 0, false => (3, [])
    | 0, true => (1, [])
    | 1, b => (2, [b])
    | 2, _ => (3, [])
    | 3, false => (3, [false])
    | 3, true => (4, [])
    | 4, b => (5, [b])
    | _, _ => (3, [])
  final _ := []
  length_step_le q b := by
    fin_cases q <;> cases b <;> simp
  length_final_le _ := by simp

private theorem run_operators (ops : List Bool) :
    decoder.run 3 (encList encNat (ops.map Bool.toNat)) = ops := by
  induction ops with
  | nil => rfl
  | cons b ops ih =>
    cases b
    · simpa [encNat_apply, Transducer.run, decoder, frame] using
        congrArg (List.cons false) ih
    · simpa [encNat_apply, Transducer.run, decoder, frame] using
        congrArg (List.cons true) ih

/-- The fixed finite parser reads every valid native output word, including zero bits. -/
theorem decoder_run (out : Option (List Bool)) :
    decoder.run decoder.q₀ (wire out) = encOption encBits out := by
  cases out with
  | none => rfl
  | some ops =>
    simpa [wire, encode, encNat_apply, Transducer.run, decoder, frame,
      encOption_some, encBits] using congrArg (List.cons true) (run_operators ops)

/-- The output wire convention is injective, derived from its concrete decoder. -/
theorem wire_injective : Function.Injective wire := by
  intro a b h
  apply (encOption encBits).injective
  rw [← decoder_run a, ← decoder_run b, h]

/-- A hit's encoded native array has at most three symbols per represented word. -/
theorem wire_length_some (ops : List Bool) : (wire (some ops)).length ≤ 3 * (ops.length + 1) := by
  have bound : (encList encNat (ops.map Bool.toNat)).length ≤ 3 * ops.length := by
    induction ops with
    | nil => simp
    | cons b ops ih =>
      cases b <;> simp [encNat_apply, frame] at * <;> omega
  simp [wire, encode, encNat_apply, frame]
  omega

/-- The actual finite multitape machine implements the output codec, including halt,
with no work tapes. This charges bit-format conversion, not random-access simulation. -/
theorem decoder_computes (out : Option (List Bool)) :
    decoder.toTM.ComputesInTimeAndSpace (wire out) (encOption encBits out)
      (2 * (wire out).length + 3) 0 := by
  simpa only [decoder_run] using decoder.computesInTimeAndSpace_toTM (wire out)

/-- The output machine's concrete linear bit bound, including misses and empty hits. -/
theorem decoder_computes_linear (out : Option (List Bool)) :
    decoder.toTM.ComputesInTimeAndSpace (wire out) (encOption encBits out)
      (6 * out.elim 0 List.length + 9) 0 := by
  have bound : (wire out).length ≤ 3 * (out.elim 0 List.length + 1) := by
    cases out with
    | none => decide
    | some ops => exact wire_length_some ops
  exact ⟨(decoder_computes out).1,
    (decoder_computes out).2.1.mono (by omega), (decoder_computes out).2.2⟩

/-- Native output words and the compact source output encode the same outcome. -/
theorem native_output {a b c d : ℕ} (x : Cslib.WordRAM.Data 40) :
    Output.outputWords a b c d x = encode (if x.regs tag = 0 then none
      else some (Output.operators a b c d x)) := by
  unfold Output.outputWords
  split <;> rfl

end Cslib.Cryptanalysis.AddXNOR.OutputCodec
