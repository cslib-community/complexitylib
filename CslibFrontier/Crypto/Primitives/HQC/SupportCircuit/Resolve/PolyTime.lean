/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Scan.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of the descending support resolver

The raw generator builds the corrected suffix first and then installs the next head scan. Its
bounded fold retains the complete encoded circuit accumulator, including every output reference.

## Main definitions

* `Cslib.Crypto.HQC.supportScanCode`: the complete descending collision pass as raw code.

## Main results

* `Cslib.Crypto.HQC.supportScanCode_eq_code`: exact agreement with the typed resolver.
* `Cslib.Crypto.HQC.computableInPolyTime_supportScanCircuit`: native uniform construction.

The generator is offline: its execution and static description are separate from the generated
sampler circuit's online resources.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Add the next head scan to a previously generated corrected suffix. -/
@[expose] def supportScanStepCode (bits offset count : ℕ) (suffix : Code) : Code :=
  let inputCount := (count + 1) * bits
  let splitCount := bits + count * bits
  let parallelCode := appendCode splitCount
    (compCode splitCount ([], List.range bits) ([], List.range bits))
    (compCode splitCount suffix
      ([], (List.range (count * bits)).map (bits + ·)))
  compCode inputCount ([], List.range inputCount)
    (compCode inputCount (collisionScanCode bits offset count)
      (compCode inputCount parallelCode ([], List.range splitCount)))

/-- One raw descending step agrees with the typed resolver constructor. -/
theorem supportScanStepCode_eq_code (bits offset count : ℕ) :
    supportScanStepCode bits offset count
      (supportScanCircuit bits (offset + 1) count).code =
        (supportScanCircuit bits offset (count + 1)).code := by
  have hn : (count + 1) * bits = bits + count * bits := by
    rw [Nat.add_mul, one_mul, Nat.add_comm]
  have hout : (Circuit.wiring signature (Fin.cast hn)).code =
      ([], List.range ((count + 1) * bits)) := by
    simpa using Circuit.code_wiring_eq_map (σ := signature) (f := Fin.cast hn)
      (g := id) fun _ => rfl
  have hin : (Circuit.wiring signature (Fin.cast hn.symm)).code =
      ([], List.range (bits + count * bits)) := by
    simpa using Circuit.code_wiring_eq_map (σ := signature) (f := Fin.cast hn.symm)
      (g := id) fun _ => rfl
  have hfirst : (Circuit.wiring signature
      (Fin.castAdd (count * bits) : Fin bits → Fin (bits + count * bits))).code =
      ([], List.range bits) := by
    simpa using Circuit.code_wiring_eq_map (σ := signature)
      (f := (Fin.castAdd (count * bits) : Fin bits → Fin (bits + count * bits)))
      (g := id) fun _ => rfl
  have hsecond : (Circuit.wiring signature
      (Fin.natAdd bits : Fin (count * bits) → Fin (bits + count * bits))).code =
      ([], (List.range (count * bits)).map (bits + ·)) :=
    Circuit.code_wiring_eq_map fun _ => rfl
  have hid : (Circuit.id signature bits).code = ([], List.range bits) :=
    Circuit.code_wiring_id
  have hleft :
      compCode (bits + count * bits) ([], List.range bits) ([], List.range bits) =
        ((Circuit.id signature bits).comp
          (Circuit.wiring signature (Fin.castAdd (count * bits)))).code := by
    calc
      _ = compCode (bits + count * bits) (Circuit.id signature bits).code
          (Circuit.wiring signature (Fin.castAdd (count * bits))).code := by
            rw [hid, hfirst]
      _ = _ := compCode_code _ _
  have hright :
      compCode (bits + count * bits) (supportScanCircuit bits (offset + 1) count).code
        ([], (List.range (count * bits)).map (bits + ·)) =
      ((supportScanCircuit bits (offset + 1) count).comp
        (Circuit.wiring signature (Fin.natAdd bits))).code := by
    calc
      _ = compCode (bits + count * bits)
          (supportScanCircuit bits (offset + 1) count).code
          (Circuit.wiring signature (Fin.natAdd bits)).code := by rw [hsecond]
      _ = _ := compCode_code _ _
  have hparallel :
      appendCode (bits + count * bits)
        (compCode (bits + count * bits) ([], List.range bits) ([], List.range bits))
        (compCode (bits + count * bits) (supportScanCircuit bits (offset + 1) count).code
          ([], (List.range (count * bits)).map (bits + ·))) =
      ((Circuit.id signature bits).parallel
        (supportScanCircuit bits (offset + 1) count)).code := by
    rw [hleft, hright, appendCode_code]
    rfl
  simp only [supportScanStepCode]
  rw [← hout, ← hin, hparallel, collisionScanCode_eq_code,
    compCode_code, compCode_code, compCode_code]
  rfl

/-- The raw descending step is uniformly generated from unary dimensions and a binary circuit
encoding. -/
@[fun_prop] theorem computableInPolyTime_supportScanStepCode {α : Type}
    {enc : α ↪ List Bool} {bits offset count : α → ℕ} {suffix : α → Code}
    (hb : ComputableInPolyTime bits enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary)
    (hsuffix : ComputableInPolyTime suffix enc encCode) :
    ComputableInPolyTime
      (fun a => supportScanStepCode (bits a) (offset a) (count a) (suffix a))
      enc encCode := by
  have hinputCount : ComputableInPolyTime
      (fun a => (count a + 1) * bits a) enc encUnary := by fun_prop
  have hsplitCount : ComputableInPolyTime
      (fun a => bits a + count a * bits a) enc encUnary := by fun_prop
  have hinputRange : ComputableInPolyTime
      (fun a => List.range ((count a + 1) * bits a)) enc (encList encNat) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      unary_to_binary.map.comp (range.comp hinputCount)
  have hsplitRange : ComputableInPolyTime
      (fun a => List.range (bits a + count a * bits a)) enc (encList encNat) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      unary_to_binary.map.comp (range.comp hsplitCount)
  have hbitsRange : ComputableInPolyTime
      (fun a => List.range (bits a)) enc (encList encNat) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      unary_to_binary.map.comp (range.comp hb)
  have hsuffixRange : ComputableInPolyTime
      (fun a => (List.range (count a * bits a)).map (bits a + ·))
      enc (encList encNat) := by
    apply mapWithInput (encA := encUnary) (range.comp (by fun_prop))
    have hb' := unary_to_binary.comp (hb.comp (fst enc encUnary))
    have hi := unary_to_binary.comp (snd enc encUnary)
    fun_prop
  have hscan := computableInPolyTime_collisionScanCircuit hb ho hc
  simp only [← collisionScanCode_eq_code] at hscan
  have hleft := computableInPolyTime_compCode (unary_to_binary.comp hsplitCount)
    ((const (encOut := encList encGate) []).prod hbitsRange)
    ((const (encOut := encList encGate) []).prod hbitsRange)
  have hright := computableInPolyTime_compCode (unary_to_binary.comp hsplitCount) hsuffix
    ((const (encOut := encList encGate) []).prod hsuffixRange)
  have hparallel := computableInPolyTime_appendCode (unary_to_binary.comp hsplitCount)
    hleft hright
  exact computableInPolyTime_compCode (unary_to_binary.comp hinputCount)
    ((const (encOut := encList encGate) []).prod hinputRange)
    (computableInPolyTime_compCode (unary_to_binary.comp hinputCount) hscan
      (computableInPolyTime_compCode (unary_to_binary.comp hinputCount) hparallel
        ((const (encOut := encList encGate) []).prod hsplitRange)))

/-- Emit the complete descending pass. The bounded index is total on malformed raw fold inputs. -/
@[expose] def supportScanCode (bits offset count : ℕ) : Code :=
  (List.range count).foldl (fun suffix index =>
    let tailCount := min count index
    supportScanStepCode bits (offset + count - (tailCount + 1)) tailCount suffix) ([], [])

private theorem supportScanCode_prefix (bits offset count i : ℕ) (hi : i ≤ count) :
    ((List.range count).take i).foldl (fun suffix index =>
      let tailCount := min count index
      supportScanStepCode bits (offset + count - (tailCount + 1)) tailCount suffix) ([], []) =
        (supportScanCircuit bits (offset + count - i) i).code := by
  induction i with
  | zero => simp [supportScanCircuit, Circuit.id]
  | succ i ih =>
    have hi' : i ≤ count := (Nat.le_succ i).trans hi
    have ihcode := ih hi'
    rw [List.take_range, Nat.min_eq_left hi'] at ihcode
    rw [List.take_range, Nat.min_eq_left hi, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ihcode]
    simp only [Nat.min_eq_right (by omega : i ≤ count)]
    have hoff : offset + count - i = offset + count - (i + 1) + 1 := by omega
    rw [hoff]
    exact supportScanStepCode_eq_code bits (offset + count - (i + 1)) i

/-- Raw generation agrees with every gate and output wire of the descending resolver. -/
theorem supportScanCode_eq_code (bits offset count : ℕ) :
    supportScanCode bits offset count = (supportScanCircuit bits offset count).code := by
  have h := supportScanCode_prefix bits offset count count (Nat.le_refl count)
  rw [List.take_range, Nat.min_self] at h
  have hoff : offset + count - count = offset := by omega
  rw [hoff] at h
  exact h

private abbrev ResolveParameters := ℕ × (ℕ × ℕ)

private def supportScanFoldStep (par : ResolveParameters) (suffix : Code) (index : ℕ) : Code :=
  let tailCount := min par.2.2 index
  supportScanStepCode par.1 (par.2.1 + par.2.2 - (tailCount + 1)) tailCount suffix

private theorem computableInPolyTime_supportScanFoldStep :
    ComputableInPolyTime
      (fun p : (ResolveParameters × Code) × ℕ => supportScanFoldStep p.1.1 p.1.2 p.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat) encCode := by
  have hb : ComputableInPolyTime
      (fun p : (ResolveParameters × Code) × ℕ => p.1.1.1)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encUnary := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : (ResolveParameters × Code) × ℕ => p.1.1.2.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encUnary := by fun_prop
  have hindex : ComputableInPolyTime
      (fun p : (ResolveParameters × Code) × ℕ => p.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encNat := by fun_prop
  have htail : ComputableInPolyTime
      (fun p : (ResolveParameters × Code) × ℕ => min p.1.1.2.2 p.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encUnary := binary_min_unary' hc hindex
  unfold supportScanFoldStep
  exact computableInPolyTime_supportScanStepCode hb (by fun_prop) htail (by fun_prop)

private def supportScanCodeBound (bits count : ℕ) : ℕ :=
  let N := count * bits
  let G := count * count * (13 * bits + 6)
  2 * G * (23 + 8 * (N + G)) + 1 + N * (2 * (N + G) + 1)

private theorem polyBounded_supportScanCodeBound {α : Type} {enc : α ↪ List Bool}
    {bits count : α → ℕ} (hb : ComputableInPolyTime bits enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary) :
    PolyBounded (fun a => (enc a).length)
      (fun a => supportScanCodeBound (bits a) (count a)) := by
  have hb' := hb.tidy.polyBounded
  have hc' := hc.tidy.polyBounded
  have hN := hc'.mul hb'
  have hG := (hc'.mul hc').mul (((PolyBounded.const 13).mul hb').add (.const 6))
  have hNG := hN.add hG
  have hleft := (((PolyBounded.const 2).mul hG).mul
    ((PolyBounded.const 23).add ((PolyBounded.const 8).mul hNG))).add (.const 1)
  have hright := hN.mul (((PolyBounded.const 2).mul hNG).add (.const 1))
  simpa [supportScanCodeBound] using hleft.add hright

private theorem length_supportScanFold_le (bits offset count i : ℕ)
    (hi : i ≤ (List.range count).length) :
    (encCode (((List.range count).take i).foldl
      (supportScanFoldStep (bits, offset, count)) ([], []))).length ≤
        supportScanCodeBound bits count := by
  have hi' : i ≤ count := by simpa only [List.length_range] using hi
  have hstep : supportScanFoldStep (bits, offset, count) = fun suffix index =>
      let tailCount := min count index
      supportScanStepCode bits (offset + count - (tailCount + 1)) tailCount suffix := rfl
  rw [hstep]
  rw [supportScanCode_prefix bits offset count i hi']
  have hchoose : i.choose 2 ≤ count * count := by
    exact (Nat.choose_le_pow i 2).trans (by
      simpa only [pow_two] using Nat.pow_le_pow_left hi' 2)
  have hsize : (supportScanCircuit bits (offset + count - i) i).size ≤
      count * count * (13 * bits + 6) := by
    rw [size_supportScanCircuit]
    exact Nat.mul_le_mul_right _ hchoose
  exact (length_encCode_le (supportScanCircuit bits (offset + count - i) i)).trans (by
    dsimp only [supportScanCodeBound]
    gcongr)

/-- The whole descending resolver has a native polynomial-time generator in its unary
parameters, with every intermediate circuit encoding charged by the loop bound. -/
@[fun_prop] theorem computableInPolyTime_supportScanCircuit {α : Type}
    {enc : α ↪ List Bool} {bits offset count : α → ℕ}
    (hb : ComputableInPolyTime bits enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime
      (fun a => (supportScanCircuit (bits a) (offset a) (count a)).code) enc encCode := by
  let parEnc := encPair encUnary (encPair encUnary encUnary)
  have hpar := hb.prod (ho.prod hc)
  have hlist : ComputableInPolyTime (fun a => List.range (count a))
      enc (encList encNat) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      unary_to_binary.map.comp (range.comp hc)
  have h := foldlWith (step := supportScanFoldStep) hpar hlist
    (const (encOut := encCode) (([], []) : Code))
    (by simpa only [parEnc] using computableInPolyTime_supportScanFoldStep)
    (polyBounded_supportScanCodeBound hb hc) fun a i hi =>
      length_supportScanFold_le (bits a) (offset a) (count a) i hi
  have hcode : ComputableInPolyTime
      (fun a => supportScanCode (bits a) (offset a) (count a)) enc encCode := by
    have hstep (a : α) : supportScanFoldStep (bits a, offset a, count a) =
        fun suffix index =>
          let tailCount := min (count a) index
          supportScanStepCode (bits a) (offset a + count a - (tailCount + 1)) tailCount suffix :=
      rfl
    simpa only [supportScanCode, hstep] using h
  simpa only [supportScanCode_eq_code] using hcode

end Cslib.Crypto.HQC
