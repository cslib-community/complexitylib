/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Scan
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Collision.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of a corrected-suffix scan

The emitted code preserves the complete suffix and includes every intermediate comparison.
The generator is a bounded fold over the suffix positions, with a typed-circuit invariant
bounding its complete encoded accumulator, including all output references.

## Main definitions

* `Cslib.Crypto.HQC.headCollisionCode`: one comparison with a retained suffix.
* `Cslib.Crypto.HQC.collisionScanCode`: the complete increasing suffix scan.

## Main results

* `Cslib.Crypto.HQC.collisionScanCode_eq_code`: exact agreement with the typed scan.
* `Cslib.Crypto.HQC.computableInPolyTime_collisionScanCircuit`: native uniform construction.

These are original compiler certificates; static generator descriptions and offline compiler
execution costs are separate from the sampler's circuit execution.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Compare the head with suffix position `j`, then retain all suffix output wires. The raw
constructor is total; typed agreement requires `j < count`. -/
@[expose] def headCollisionCode (bits offset count j : ℕ) : Code :=
  appendCode (bits + count * bits)
    (compCode (bits + count * bits) (collisionStepCode bits offset)
      ([], (List.range (bits + bits)).map fun i =>
        if i < bits then i else bits + (i - bits + bits * j)))
    ([], (List.range (count * bits)).map (bits + ·))

/-- Every head-correction instruction and retained wire agrees with the typed circuit. -/
theorem headCollisionCode_eq_code (bits offset count : ℕ) (j : Fin count) :
    headCollisionCode bits offset count j.val =
      (headCollisionCircuit bits offset count j).code := by
  have hp : (Circuit.wiring signature
      (Fin.append (Fin.castAdd (count * bits))
        (fun i : Fin bits => Fin.natAdd bits (finProdFinEquiv (j, i))))).code =
      ([], (List.range (bits + bits)).map fun i =>
        if i < bits then i else bits + (i - bits + bits * j.val)) := by
    apply Circuit.code_wiring_eq_map
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [Fin.append_left, Fin.val_castAdd, ite_eq_left k.isLt]
    · simp only [Fin.append_right, Fin.val_natAdd, finProdFinEquiv_apply_val]
      rw [ite_eq_right (by omega)]
      omega
  have ht : (Circuit.wiring signature
      (Fin.natAdd bits : Fin (count * bits) → Fin (bits + count * bits))).code =
      ([], (List.range (count * bits)).map (bits + ·)) :=
    Circuit.code_wiring_eq_map fun _ => rfl
  rw [headCollisionCode, ← hp, ← ht, collisionStepCode_eq_code, compCode_code, appendCode_code]
  rfl

/-- The retained-suffix head step is generated uniformly, with a binary suffix index. -/
@[fun_prop] theorem computableInPolyTime_headCollisionCode {α : Type}
    {enc : α ↪ List Bool} {bits offset count j : α → ℕ}
    (hb : ComputableInPolyTime bits enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun a => headCollisionCode (bits a) (offset a) (count a) (j a))
      enc encCode := by
  have hn : ComputableInPolyTime (fun a => bits a + count a * bits a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hs : ComputableInPolyTime
      (fun a => (List.range (bits a + bits a)).map fun i =>
        if i < bits a then i else bits a + (i - bits a + bits a * j a))
      enc (encList encNat) := by
    have hi : ComputableInPolyTime
        (fun p : α × ℕ => if p.2 < bits p.1 then p.2
          else bits p.1 + (p.2 - bits p.1 + bits p.1 * j p.1))
        (encPair enc encUnary) encNat := by
      have hb' := unary_to_binary.comp (hb.comp (fst enc encUnary))
      have hj' := hj.comp (fst enc encUnary)
      have hi' := unary_to_binary.comp (snd enc encUnary)
      exact ((binary_lt' hi' hb').ite' hi'
        (binary_add' hb' (binary_add' (binary_sub' hi' hb') (binary_mul' hb' hj')))).of_enc_eq
          fun p => by simp only [Function.comp_apply, decide_eq_true_eq]
    exact mapWithInput (by fun_prop) hi
  have ht : ComputableInPolyTime
      (fun a => (List.range (count a * bits a)).map (bits a + ·)) enc (encList encNat) := by
    apply mapWithInput (encA := encUnary) (range.comp (by fun_prop))
    have hb' := unary_to_binary.comp (hb.comp (fst enc encUnary))
    have hi := unary_to_binary.comp (snd enc encUnary)
    fun_prop
  have hstep := computableInPolyTime_collisionStepCircuit hb ho
  simp only [← collisionStepCode_eq_code] at hstep
  exact computableInPolyTime_appendCode hn
    (computableInPolyTime_compCode hn hstep ((const []).prod hs))
    ((const []).prod ht)

/-- Emit the full increasing suffix scan; every composition keeps all suffix outputs. -/
@[expose] def collisionScanCode (bits offset count : ℕ) : Code :=
  (List.range count).foldr
    (fun j acc => compCode (bits + count * bits) acc (headCollisionCode bits offset count j))
    ([], List.range (bits + count * bits))

private theorem collisionScanCode_list (bits offset count : ℕ) (js : List (Fin count)) :
    (js.map Fin.val).foldr
      (fun j acc => compCode (bits + count * bits) acc (headCollisionCode bits offset count j))
      ([], List.range (bits + count * bits)) =
        (collisionScanCircuit bits offset count js).code := by
  induction js with
  | nil =>
      simp only [List.map_nil, List.foldr_nil, collisionScanCircuit]
      simpa only [Circuit.id] using
        (Circuit.code_wiring_id (n := bits + count * bits) (σ := signature)).symm
  | cons j js ih =>
    simp only [List.map_cons, List.foldr_cons, ih, headCollisionCode_eq_code, compCode_code]
    rfl

/-- Raw generation agrees with every instruction and wire of the typed ordered scan. -/
theorem collisionScanCode_eq_code (bits offset count : ℕ) :
    collisionScanCode bits offset count =
      (collisionScanCircuit bits offset count (List.finRange count)).code := by
  have h := collisionScanCode_list bits offset count (List.finRange count)
  simpa only [collisionScanCode, List.map_coe_finRange_eq_range] using h

private theorem exists_circuit_fold_head (bits offset count : ℕ) (js : List ℕ)
    (hjs : ∀ j ∈ js, j < count) :
    ∃ c : Circuit signature (bits + count * bits) (bits + count * bits),
      js.foldl (fun acc j => compCode (bits + count * bits) acc
        (headCollisionCode bits offset count j)) ([], List.range (bits + count * bits)) = c.code ∧
      c.size = js.length * (13 * bits + 6) := by
  induction js using List.reverseRecOn with
  | nil =>
      refine ⟨Circuit.id signature _, ?_, by simp [Circuit.id]⟩
      simpa only [List.foldl_nil] using
        (Circuit.code_wiring_id (n := bits + count * bits) (σ := signature)).symm
  | append_singleton js j ih =>
    obtain ⟨c, he, hs⟩ := ih (fun k hk => hjs k (by simp [hk]))
    have hj := hjs j (by simp)
    refine ⟨c.comp (headCollisionCircuit bits offset count ⟨j, hj⟩), ?_, ?_⟩
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, he,
        show headCollisionCode bits offset count j =
          (headCollisionCircuit bits offset count ⟨j, hj⟩).code from
            headCollisionCode_eq_code bits offset count ⟨j, hj⟩, compCode_code]
    · rw [Circuit.size_comp, hs, size_headCollisionCircuit]
      simp only [List.length_append, List.length_singleton]
      ring

private abbrev ScanParameters := ℕ × (ℕ × ℕ)

private def collisionScanFoldStep (par : ScanParameters) (acc : Code) (j : ℕ) : Code :=
  compCode (par.1 + par.2.2 * par.1) acc
    (headCollisionCode par.1 par.2.1 par.2.2 j)

private theorem computableInPolyTime_collisionScanFoldStep :
    ComputableInPolyTime
      (fun p : (ScanParameters × Code) × ℕ => collisionScanFoldStep p.1.1 p.1.2 p.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat) encCode := by
  have hb : ComputableInPolyTime
      (fun p : (ScanParameters × Code) × ℕ => p.1.1.1)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encUnary := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : (ScanParameters × Code) × ℕ => p.1.1.2.2)
      (encFoldStep (encPair encUnary (encPair encUnary encUnary)) encCode encNat)
      encUnary := by fun_prop
  unfold collisionScanFoldStep
  exact computableInPolyTime_compCode (unary_to_binary.comp (by fun_prop)) (by fun_prop)
    (computableInPolyTime_headCollisionCode hb (by fun_prop) hc (by fun_prop))

private def collisionScanCodeBound (bits count : ℕ) : ℕ :=
  let N := bits + count * bits
  let G := count * (13 * bits + 6)
  2 * G * (23 + 8 * (N + G)) + 1 + N * (2 * (N + G) + 1)

private theorem polyBounded_collisionScanCodeBound {α : Type} {enc : α ↪ List Bool}
    {bits count : α → ℕ} (hb : ComputableInPolyTime bits enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary) :
    PolyBounded (fun a => (enc a).length)
      (fun a => collisionScanCodeBound (bits a) (count a)) := by
  have hb' := hb.tidy.polyBounded
  have hc' := hc.tidy.polyBounded
  have hN := hb'.add (hc'.mul hb')
  have hG := hc'.mul (((PolyBounded.const 13).mul hb').add (.const 6))
  have hNG := hN.add hG
  have hleft := (((PolyBounded.const 2).mul hG).mul
    ((PolyBounded.const 23).add ((PolyBounded.const 8).mul hNG))).add (.const 1)
  have hright := hN.mul (((PolyBounded.const 2).mul hNG).add (.const 1))
  simpa [collisionScanCodeBound] using hleft.add hright

private theorem length_collisionScanFold_le (bits offset count i : ℕ)
    (hi : i ≤ (List.range count).reverse.length) :
    (encCode (((List.range count).reverse.take i).foldl
      (collisionScanFoldStep (bits, offset, count))
      ([], List.range (bits + count * bits)))).length ≤
        collisionScanCodeBound bits count := by
  obtain ⟨c, he, hs⟩ := exists_circuit_fold_head bits offset count
    (((List.range count).reverse).take i) (fun j hj => by
      exact List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take hj)))
  change (encCode (((List.range count).reverse.take i).foldl
    (fun acc j => compCode (bits + count * bits) acc
      (headCollisionCode bits offset count j))
    ([], List.range (bits + count * bits)))).length ≤ collisionScanCodeBound bits count
  rw [he]
  have hsize : c.size ≤ count * (13 * bits + 6) := by
    rw [hs]
    exact Nat.mul_le_mul_right _ ((List.length_take_le _ _).trans (by
      simpa only [List.length_reverse, List.length_range] using hi))
  exact (length_encCode_le c).trans (by
    dsimp only [collisionScanCodeBound]
    gcongr)

/-- The whole increasing suffix scan has a native polynomial-time generator in its unary
parameters, with its complete encoded intermediate circuits charged by the loop bound. -/
@[fun_prop] theorem computableInPolyTime_collisionScanCircuit {α : Type}
    {enc : α ↪ List Bool} {bits offset count : α → ℕ}
    (hb : ComputableInPolyTime bits enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary)
    (hc : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime
      (fun a => (collisionScanCircuit (bits a) (offset a) (count a)
        (List.finRange (count a))).code) enc encCode := by
  let parEnc := encPair encUnary (encPair encUnary encUnary)
  have hpar := hb.prod (ho.prod hc)
  have hlist : ComputableInPolyTime (fun a => (List.range (count a)).reverse)
      enc (encList encNat) := by
    have hr : ComputableInPolyTime (fun a => List.range (count a)) enc (encList encNat) := by
      simpa only [Function.comp_def, List.map_id_fun', id_eq] using
        unary_to_binary.map.comp (range.comp hc)
    exact .of_tidy (ComputableTidilyInPolyTime.listReverseWithInput hr.tidy)
  have hinit : ComputableInPolyTime
      (fun a => (([] : List (Op × List ℕ)), List.range (bits a + count a * bits a)))
      enc encCode := by
    have hN : ComputableInPolyTime (fun a => bits a + count a * bits a) enc encUnary := by
      fun_prop
    have hr := unary_to_binary.map.comp (range.comp hN)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using (const []).prod hr
  have h := foldlWith (step := collisionScanFoldStep) hpar hlist hinit
    (by simpa only [parEnc] using computableInPolyTime_collisionScanFoldStep)
    (polyBounded_collisionScanCodeBound hb hc) fun a i hi =>
      length_collisionScanFold_le (bits a) (offset a) (count a) i hi
  have hcode : ComputableInPolyTime
      (fun a => collisionScanCode (bits a) (offset a) (count a)) enc encCode := by
    simpa only [collisionScanFoldStep, List.foldl_reverse, collisionScanCode] using h
  simpa only [collisionScanCode_eq_code] using hcode

end Cslib.Crypto.HQC
