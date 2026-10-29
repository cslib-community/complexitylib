/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Combining circuit codes on shared inputs

`appendCode n c d` runs both codes on the same `n` inputs, keeping the outputs of `c` before
those of `d`. It shifts the gate references of `d` past the gates of `c`, while preserving its
input references. On codes of circuits, the result is the code of `Circuit.append`.
`appendCodes` combines any list of blocks by repeated append; each block is relocated by the
number of preceding gates. `bundleCode` uses a fixed block size and agrees with `appendCodes`
when its blocks have that size. All three constructors are computable in polynomial time
with binary layout parameters.

`compCode n d c` instead feeds `c`'s output wires to `d`'s inputs. Its polynomial-time constructor
performs binary-indexed lookup and gate relocation, and agrees exactly with `Circuit.comp`.

## Main definitions

* `Cslib.Circuits.Program.appendWireCode`: wire numbers under program continuation.
* `Cslib.Circuits.Boolean.shiftCodeWire`, `Cslib.Circuits.Boolean.shiftCode`: relocate gate and
  output wire references of a raw circuit code past preceding gates.
* `Cslib.Circuits.Boolean.appendCode`: combine raw codes on shared inputs.
* `Cslib.Circuits.Boolean.appendCodes`: combine raw blocks of varying sizes on shared inputs.
* `Cslib.Circuits.Boolean.bundleCode`: combine equal-sized raw blocks on shared inputs.
* `Cslib.Circuits.Boolean.compCodeWire`, `Cslib.Circuits.Boolean.compCode`: compose raw circuit
  codes through their output wires.

## Main results

* `Cslib.Circuits.Program.code_append`: code of program continuation.
* `Cslib.Circuits.Boolean.appendCode_code`: agreement with typed circuit append.
* `Cslib.Circuits.Boolean.length_appendCode`: additive gate count.
* `Cslib.Circuits.Boolean.computableInPolyTime_appendCode`: constructor efficiency.
* `Cslib.Circuits.Boolean.appendCodes_code`: agreement with arbitrary typed output families.
* `Cslib.Circuits.Boolean.computableInPolyTime_appendCodes`: varying-size constructor
  efficiency, including arbitrary binary wire indices.
* `Cslib.Circuits.Boolean.bundleCode_eq_foldl_appendCode`: bundling agrees with repeated append.
* `Cslib.Circuits.Boolean.computableInPolyTime_bundleCode`: bundling efficiency.
* `Cslib.Circuits.Boolean.exists_circuit_bundleCode`: raw bundles realize typed output families.
* `Cslib.Circuits.Boolean.compCode_code`: agreement with typed sequential composition.
* `Cslib.Circuits.Boolean.computableInPolyTime_compCode`: sequential constructor efficiency.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Program

universe v

variable {σ : Signature.{v}} {n m s t : ℕ}

private theorem code_mapWires (line : Line σ m t) (f : Wire m t → Wire n s)
    (ren : ℕ → ℕ) (h : ∀ w, (f w).toNat = ren w.toNat) :
    (line.mapWires f).code = (line.code.1, line.code.2.map ren) := by
  simp only [Line.code, Line.mapWires, List.map_ofFn]
  congr 2
  funext i
  exact h (line.wires i)

/-- The wire-number map when continuing a program with another program. -/
def appendWireCode (n m s : ℕ) (feed : Fin m → Wire n s) (i : ℕ) : ℕ :=
  if h : i < m then (feed ⟨i, h⟩).toNat else n + s + (i - m)

/-- Numbering a continued wire agrees with the raw wire-number map. -/
theorem appendedWire_toNat (feed : Fin m → Wire n s) (w : Wire m t) :
    (appendedWire feed w).toNat = appendWireCode n m s feed w.toNat := by
  cases w with
  | input i =>
      cases h : feed i <;> simp [appendWireCode, h, Wire.toNat]
  | gate j => simp [appendWireCode, Wire.toNat, Nat.add_assoc]

/-- Program continuation acts on codes by appending the rewired gate list. -/
theorem code_append (p : Program σ n s) (feed : Fin m → Wire n s) (q : Program σ m t) :
    (p.append feed q).code = p.code ++
      q.code.map (fun g => (g.1, g.2.map (appendWireCode n m s feed))) := by
  induction q with
  | empty => simp [append]
  | gate q line ih =>
    simp only [append, code_gate, ih, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, code_mapWires line (appendedWire feed) _ (appendedWire_toNat feed)]

end Program

namespace Boolean

/-- Retain an input wire, or shift a gate wire past `offset` preceding gates. -/
def shiftCodeWire (n offset i : ℕ) : ℕ := if i < n then i else i + offset

/-- Run two raw codes on shared inputs, listing the first code's outputs before the second's.
Malformed codes are transformed as data; semantic correctness is asserted on typed circuits. -/
def appendCode (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (c.1 ++ d.1.map (fun g => (g.1, g.2.map (shiftCodeWire n c.1.length))),
    c.2 ++ d.2.map (shiftCodeWire n c.1.length))

/-- Appending two raw codes sums their gate counts. -/
@[simp]
theorem length_appendCode (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).1.length = c.1.length + d.1.length := by
  simp [appendCode]

/-- Appending two raw codes sums their output counts. -/
@[simp]
theorem length_appendCode_outputs (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).2.length = c.2.length + d.2.length := by
  simp [appendCode]

private theorem appendWireCode_input (n offset : ℕ) :
    Program.appendWireCode n n offset Wire.input = shiftCodeWire n offset := by
  funext i
  by_cases hi : i < n
  · simp [Program.appendWireCode, shiftCodeWire, hi]
  · simp only [Program.appendWireCode, shiftCodeWire, dite_eq_right hi, ite_eq_right hi]
    omega

private theorem toNat_castAdd {n k : ℕ} (w : Wire n k) (extra : ℕ) :
    (w.castAdd extra).toNat = w.toNat := by
  cases w <;> rfl

/-- Raw shared-input composition agrees with ordinary typed circuit append. -/
theorem appendCode_code {n m p : ℕ} (c : Circuit signature n m) (d : Circuit signature n p) :
    appendCode n c.code d.code = (c.append d).code := by
  simp only [appendCode, Circuit.code, Circuit.append, Program.code_append,
    appendWireCode_input]
  apply Prod.ext
  · rw [Program.length_code]
  rw [show (fun j => (Fin.append (Wire.castAdd d.size ∘ c.outputs)
    (Program.appendedWire Wire.input ∘ d.outputs) j).toNat) =
      Fin.append (fun j => (c.outputs j).toNat)
        (fun j => shiftCodeWire n c.size (d.outputs j).toNat) from ?_]
  · simp only [List.ofFn_fin_append, List.map_ofFn]
    rw [Program.length_code]
    rfl
  · funext j
    induction j using Fin.addCases with
    | left i => simp [toNat_castAdd]
    | right i =>
      simp only [Fin.append_right, Function.comp_apply, Program.appendedWire_toNat,
        appendWireCode_input]

/-- The outputs of combined codes are the two output lists in order, on every input. -/
theorem evalOutput_appendCode_code {n m p : ℕ} (c : Circuit signature n m)
    (d : Circuit signature n p) (x : Fin n → Bool) :
    (appendCode n c.code d.code).2.map
      (evalOutput (List.ofFn x) (appendCode n c.code d.code).1) =
        List.ofFn (c.eval interpretation x) ++ List.ofFn (d.eval interpretation x) := by
  rw [appendCode_code]
  simp only [Circuit.code, List.map_ofFn]
  calc
    _ = List.ofFn ((c.append d).eval interpretation x) := by
      apply congrArg List.ofFn
      funext j
      exact ((c.append d).eval_eq_evalOutput x j).symm
    _ = _ := by rw [Circuit.eval_append, List.ofFn_fin_append]

open Turing.MultiTapeTM ComputableInPolyTime

/-- Shifting wire numbers is polynomial-time with all quantities encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_shiftCodeWire {α : Type} {enc : α ↪ List Bool}
    {n offset i : α → ℕ} (hn : ComputableInPolyTime n enc encNat)
    (hoffset : ComputableInPolyTime offset enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => shiftCodeWire (n a) (offset a) (i a)) enc encNat := by
  unfold shiftCodeWire
  fun_prop

/-- Shift the gate references and output references of a raw code. Input wires are preserved. -/
def shiftCode (n offset : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (code.1.map (fun g => (g.1, g.2.map (shiftCodeWire n offset))),
    code.2.map (shiftCodeWire n offset))

/-- Relocating a circuit-code block is polynomial-time with binary offsets. -/
@[fun_prop]
theorem computableInPolyTime_shiftCode {α : Type} {enc : α ↪ List Bool}
    {n offset : α → ℕ} {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hoffset : ComputableInPolyTime offset enc encNat)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun a => shiftCode (n a) (offset a) (code a)) enc encCode := by
  have hgate : ComputableInPolyTime
      (fun q : α × (Op × List ℕ) =>
        (q.2.1, q.2.2.map (shiftCodeWire (n q.1) (offset q.1))))
      (encPair enc encGate) encGate := by
    refine ((snd enc encGate).fst').prod ?_
    apply mapWithInput (snd enc encGate).snd'
    exact computableInPolyTime_shiftCodeWire
      (hn.comp ((fst _ _).comp (fst _ _)))
      (hoffset.comp ((fst _ _).comp (fst _ _))) (snd _ _)
  have hgates := mapWithInput (encB := encGate)
    (f := fun a g => (g.1, g.2.map (shiftCodeWire (n a) (offset a)))) hcode.fst' hgate
  have houtputs := mapWithInput (encB := encNat)
    (f := fun a i => shiftCodeWire (n a) (offset a) i) hcode.snd'
    (computableInPolyTime_shiftCodeWire (hn.comp (fst _ _))
      (hoffset.comp (fst _ _)) (snd _ _))
  exact hgates.prod houtputs

/-- Combining circuit codes is polynomial-time, including binary input and wire counts. -/
@[fun_prop]
theorem computableInPolyTime_appendCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {c d : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime c enc encCode)
    (hd : ComputableInPolyTime d enc encCode) :
    ComputableInPolyTime (fun a => appendCode (n a) (c a) (d a)) enc encCode := by
  have hlen : ComputableInPolyTime (fun a => (c a).1.length) enc encNat :=
    (length_list_binary encGate).comp hc.fst'
  have hshift := computableInPolyTime_shiftCode hn hlen hd
  exact (listAppend' hc.fst' hshift.fst').prod (listAppend' hc.snd' hshift.snd')

/-- Combine a list of raw codes on shared inputs, preserving block and output order.
Blocks may have different gate counts and any number of outputs. -/
def appendCodes (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  codes.foldl (appendCode n) ([], [])

/-- Combining an empty list of raw codes yields the empty code. -/
@[simp] theorem appendCodes_nil (n : ℕ) : appendCodes n [] = ([], []) := rfl

/-- Adding a final block is ordinary shared-input append. -/
theorem appendCodes_append_singleton (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    appendCodes n (codes ++ [code]) = appendCode n (appendCodes n codes) code := by
  simp [appendCodes]

/-- The combined code retains every gate, without padding the individual blocks. -/
@[simp] theorem length_appendCodes (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).1.length = (codes.flatMap Prod.fst).length := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    simp [appendCodes_append_singleton, ih]

/-- The combined code retains all outputs, including repeated outputs and zero-gate blocks. -/
@[simp] theorem length_appendCodes_outputs (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).2.length = (codes.flatMap Prod.snd).length := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    simp [appendCodes_append_singleton, ih]

private def appendCodesDirect (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  (codes.zipIdx.flatMap fun q =>
      (shiftCode n ((codes.take q.2).flatMap Prod.fst).length q.1).1,
    codes.zipIdx.flatMap fun q =>
      (shiftCode n ((codes.take q.2).flatMap Prod.fst).length q.1).2)

private theorem appendCodesDirect_snoc (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    appendCodesDirect n (codes ++ [code]) =
      ((appendCodesDirect n codes).1 ++
          (shiftCode n (codes.flatMap Prod.fst).length code).1,
        (appendCodesDirect n codes).2 ++
          (shiftCode n (codes.flatMap Prod.fst).length code).2) := by
  have hprefix (q : (List (Op × List ℕ) × List ℕ) × ℕ) (hq : q ∈ codes.zipIdx) :
      (codes ++ [code]).take q.2 = codes.take q.2 :=
    List.take_append_of_le_length (by have := List.snd_lt_of_mem_zipIdx hq; omega)
  simp only [appendCodesDirect, List.zipIdx_append, List.flatMap_append, List.zipIdx_cons,
    List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, Nat.zero_add,
    List.take_left, List.append_nil]
  apply Prod.ext <;> dsimp only <;> congr 1 <;>
    apply List.flatMap_congr <;> intro q hq <;> rw [hprefix q hq]

private theorem appendCodesDirect_eq_appendCodes (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    appendCodesDirect n codes = appendCodes n codes := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    rw [appendCodesDirect_snoc, appendCodes_append_singleton, ih]
    simp only [appendCode, length_appendCodes, shiftCode]

/-- Combining arbitrary raw blocks is polynomial-time in their complete encodings.
Input and wire numbers are binary; no uniform block-size or well-formedness premise is needed. -/
@[fun_prop]
theorem computableInPolyTime_appendCodes {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList encCode)) :
    ComputableInPolyTime (fun a => appendCodes (n a) (codes a)) enc encCode := by
  let encBlock := encPair encCode encUnary
  have hblocks : ComputableInPolyTime (fun a => (codes a).zipIdx) enc (encList encBlock) := by
    fun_prop
  have hpar := fst enc encBlock
  have hentry := snd enc encBlock
  have hprefix : ComputableInPolyTime
      (fun q : α × ((List (Op × List ℕ) × List ℕ) × ℕ) => (codes q.1).take q.2.2)
      (encPair enc encBlock) (encList encCode) := by
    fun_prop
  have hprefixGates := flatMapWithInput (encB := encGate)
    (f := fun (_ : α × ((List (Op × List ℕ) × List ℕ) × ℕ)) c => c.1)
    hprefix ((snd _ encCode).fst')
  have hoffset := (length_list_binary encGate).comp hprefixGates
  have hshift := computableInPolyTime_shiftCode (hn.comp hpar) hoffset hentry.fst'
  have hgates := flatMapWithInput (encB := encGate)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (((codes a).take q.2).flatMap Prod.fst).length q.1).1)
    hblocks hshift.fst'
  have houtputs := flatMapWithInput (encB := encNat)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (((codes a).take q.2).flatMap Prod.fst).length q.1).2)
    hblocks hshift.snd'
  have h := hgates.prod houtputs
  change ComputableInPolyTime (fun a => appendCodesDirect (n a) (codes a)) enc encCode at h
  simpa only [appendCodesDirect_eq_appendCodes] using h

/-- Combining single-output circuit codes agrees exactly with `Circuit.pi`, with no restriction
on the gate counts of its components. -/
theorem appendCodes_code {k n : ℕ} (cs : Fin k → Circuit signature n 1) :
    appendCodes n (List.ofFn (fun j => (cs j).code)) = (Circuit.pi cs).code := by
  induction k with
  | zero => simp [Circuit.pi, Circuit.code, Circuit.wiring]
  | succ k ih =>
    rw [List.ofFn_succ_last, appendCodes_append_singleton,
      ih (fun j => cs j.castSucc), appendCode_code]
    rfl

/-- Combine equal-sized gate blocks on shared inputs. Block `j` is relocated by `j * blockSize`.
The construction is total on raw data; its append semantics requires the stated block sizes. -/
def bundleCode (n blockSize : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  (codes.zipIdx.flatMap fun q => (shiftCode n (q.2 * blockSize) q.1).1,
    codes.zipIdx.flatMap fun q => (shiftCode n (q.2 * blockSize) q.1).2)

/-- Bundling raw blocks is polynomial-time in their encodings and binary layout parameters. -/
@[fun_prop]
theorem computableInPolyTime_bundleCode {α : Type} {enc : α ↪ List Bool}
    {n blockSize : α → ℕ} {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hblock : ComputableInPolyTime blockSize enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList encCode)) :
    ComputableInPolyTime (fun a => bundleCode (n a) (blockSize a) (codes a)) enc encCode := by
  let encBlock := encPair encCode encUnary
  have hblocks : ComputableInPolyTime (fun a => (codes a).zipIdx) enc (encList encBlock) := by
    fun_prop
  have hpar := fst enc encBlock
  have hentry := snd enc encBlock
  have hindex := unary_to_binary.comp hentry.snd'
  have hoffset := binary_mul' hindex (hblock.comp hpar)
  have hshift := computableInPolyTime_shiftCode (hn.comp hpar) hoffset hentry.fst'
  have hgates := flatMapWithInput (encB := encGate)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (q.2 * blockSize a) q.1).1)
    hblocks hshift.fst'
  have houtputs := flatMapWithInput (encB := encNat)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (q.2 * blockSize a) q.1).2)
    hblocks hshift.snd'
  exact hgates.prod houtputs

private theorem bundleCode_snoc (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    bundleCode n blockSize (codes ++ [code]) =
      ((bundleCode n blockSize codes).1 ++ (shiftCode n (codes.length * blockSize) code).1,
        (bundleCode n blockSize codes).2 ++ (shiftCode n (codes.length * blockSize) code).2) := by
  simp [bundleCode, List.zipIdx_append]

/-- Equal-sized blocks occupy exactly their number times their common gate count. -/
theorem length_bundleCode (n blockSize : ℕ) (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    (bundleCode n blockSize codes).1.length = codes.length * blockSize := by
  induction codes using List.reverseRecOn with
  | nil => simp [bundleCode]
  | append_singleton codes code ih =>
    rw [bundleCode_snoc]
    simp only [List.length_append, shiftCode, List.length_map, List.length_singleton,
      Nat.add_mul, Nat.one_mul]
    rw [ih (fun c hc => hlen c (List.mem_append_left _ hc)),
      hlen code (by simp)]

/-- Adding the next equal-sized block is shared-input append. -/
theorem bundleCode_append_singleton (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ)
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize (codes ++ [code]) =
      appendCode n (bundleCode n blockSize codes) code := by
  rw [bundleCode_snoc]
  simp only [appendCode, length_bundleCode n blockSize codes hlen, shiftCode]

/-- For equal-sized blocks, direct relocation agrees with repeated shared-input append. -/
theorem bundleCode_eq_foldl_appendCode (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = codes.foldl (appendCode n) ([], []) := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    have hprefix : ∀ c ∈ codes, c.1.length = blockSize :=
      fun c hc => hlen c (List.mem_append_left _ hc)
    rw [bundleCode_snoc, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih hprefix]
    simp only [appendCode, length_bundleCode n blockSize codes hprefix, shiftCode]

/-- Fixed-size bundling is a specialization of the varying-size constructor. -/
theorem bundleCode_eq_appendCodes (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = appendCodes n codes :=
  bundleCode_eq_foldl_appendCode n blockSize codes hlen

/-- The typed and raw bundles have exactly the same code when component sizes agree. -/
theorem bundleCode_code {k n : ℕ} (cs : Fin k → Circuit signature n 1) (blockSize : ℕ)
    (hs : ∀ j, (cs j).size = blockSize) :
    bundleCode n blockSize (List.ofFn (fun j => (cs j).code)) = (Circuit.pi cs).code := by
  induction k with
  | zero => simp [Circuit.pi, bundleCode, Circuit.code, Circuit.wiring]
  | succ k ih =>
    have hprefix : ∀ c ∈ List.ofFn (fun j : Fin k => (cs j.castSucc).code),
        c.1.length = blockSize := by
      intro c hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
      exact (Circuit.length_code_fst _).trans (hs j.castSucc)
    rw [List.ofFn_succ_last, bundleCode_append_singleton n blockSize _ _ hprefix,
      ih (fun j => cs j.castSucc) (fun j => hs j.castSucc), appendCode_code]
    rfl

/-- Equal-sized single-output codes form one typed circuit with the corresponding output order. -/
theorem exists_circuit_bundleCode {k n : ℕ} (cs : Fin k → Circuit signature n 1)
    (blockSize : ℕ) (hs : ∀ j, (cs j).size = blockSize) :
    ∃ c : Circuit signature n k,
      bundleCode n blockSize (List.ofFn (fun j => (cs j).code)) = c.code ∧
        ∀ x j, c.eval interpretation x j = (cs j).eval interpretation x 0 :=
  ⟨Circuit.pi cs, bundleCode_code cs blockSize hs, fun x j => congrFun (Circuit.eval_pi cs x) j⟩

/-- Route a later circuit's inputs through `c`'s outputs and shift its gates past `c`'s gates. -/
def compCodeWire (n : ℕ) (c : List (Op × List ℕ) × List ℕ) (i : ℕ) : ℕ :=
  if i < c.2.length then c.2.getD i 0 else n + c.1.length + (i - c.2.length)

/-- Feed the outputs of `c` to the inputs of `d`, matching the argument order of `Circuit.comp`.
The constructor is total on raw data, including malformed circuit codes. -/
def compCode (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (c.1 ++ d.1.map (fun g => (g.1, g.2.map (compCodeWire n c))),
    d.2.map (compCodeWire n c))

private theorem compCodeWire_code {n m : ℕ} (c : Circuit signature n m) (i : ℕ) :
    compCodeWire n c.code i = Program.appendWireCode n m c.size c.outputs i := by
  have hlength := Program.length_code c.program
  by_cases hi : i < m <;>
    simp [compCodeWire, Circuit.code, Program.appendWireCode, hi,
      List.getD_eq_getElem?_getD, hlength]

/-- Raw sequential composition is exactly the code of typed circuit composition. -/
theorem compCode_code {n m p : ℕ} (d : Circuit signature m p)
    (c : Circuit signature n m) : compCode n d.code c.code = (d.comp c).code := by
  have hwire : compCodeWire n c.code =
      Program.appendWireCode n m c.size c.outputs := funext (compCodeWire_code c)
  apply Prod.ext
  · simp only [compCode, Circuit.code, Circuit.comp, Program.code_append]
    change c.program.code ++ d.program.code.map (fun g => (g.1, g.2.map
      (compCodeWire n c.code))) = _
    rw [hwire]
  · simp only [compCode, Circuit.code, Circuit.comp, List.map_ofFn, Function.comp_apply]
    congr 1
    funext i
    rw [Program.appendedWire_toNat]
    exact compCodeWire_code c _

/-- Sequential composition retains both gate lists. -/
@[simp] theorem length_compCode (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).1.length = c.1.length + d.1.length := by
  simp [compCode]

/-- Sequential composition retains the later circuit's number of outputs. -/
@[simp] theorem length_compCode_outputs (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).2.length = d.2.length := by
  simp [compCode]

/-- Resolve a composed wire in polynomial time, including binary output lookup and offsets. -/
@[fun_prop] theorem computableInPolyTime_compCodeWire {α : Type}
    {enc : α ↪ List Bool} {n i : α → ℕ}
    {c : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime c enc encCode)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => compCodeWire (n a) (c a) (i a)) enc encNat := by
  have houtputs : ComputableInPolyTime (fun a => (c a).2.length) enc encNat :=
    (length_list_binary encNat).comp hc.snd'
  have hgates : ComputableInPolyTime (fun a => (c a).1.length) enc encNat :=
    (length_list_binary encGate).comp hc.fst'
  have hlookup : ComputableInPolyTime (fun a => (c a).2.getD (i a) 0) enc encNat :=
    listGetD_binary 0 hc.snd' hi
  unfold compCodeWire
  fun_prop

/-- Construct sequential circuit codes in polynomial time. All wire indices and input counts
are binary; list lengths, input lookup, gate relocation and the whole output code are charged. -/
@[fun_prop] theorem computableInPolyTime_compCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {d c : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hd : ComputableInPolyTime d enc encCode)
    (hc : ComputableInPolyTime c enc encCode) :
    ComputableInPolyTime (fun a => compCode (n a) (d a) (c a)) enc encCode := by
  have hwire : ComputableInPolyTime
      (fun p : α × ℕ => compCodeWire (n p.1) (c p.1) p.2)
      (encPair enc encNat) encNat := by fun_prop
  have hgate : ComputableInPolyTime
      (fun p : α × (Op × List ℕ) => (p.2.1, p.2.2.map (compCodeWire (n p.1) (c p.1))))
      (encPair enc encGate) encGate := by
    refine ((snd enc encGate).fst').prod ?_
    apply mapWithInput (snd enc encGate).snd'
    exact hwire.comp ((fst _ _).fst'.prod (snd _ _))
  exact (listAppend' hc.fst' (mapWithInput hd.fst' hgate)).prod
    (mapWithInput hd.snd' hwire)

end Boolean

end Cslib.Circuits
