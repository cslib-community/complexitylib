/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Collision
public import CslibFrontier.Computability.Circuit.Boolean.Comparison.OrderPolyTime
public import CslibFrontier.Computability.Circuit.Boolean.Comparison.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of collision correction

The generator composes the existing comparator, mux and constant-word constructors. Its raw
code agrees with the complete typed circuit, including zero-width words and truncated offsets.

## Main definitions

* `Cslib.Crypto.HQC.collisionStepCode`: complete emitted collision-correction code.

## Main results

* `Cslib.Crypto.HQC.collisionStepCode_eq_code`: exact typed/raw code agreement.
* `Cslib.Crypto.HQC.computableInPolyTime_collisionStepCircuit`: native uniform construction.

These are original compiler certificates. Offline generator time and static generator program
size are separate from the construction-derived circuit execution costs.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

/-- Emit both comparisons, their conjunction, the offset word and the selecting multiplexer. -/
@[expose] def collisionStepCode (bits offset : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode (bits + bits) (muxCode bits)
    (appendCode (bits + bits)
      (compCode (bits + bits) ([(.and, [0, 1])], [2])
        (appendCode (bits + bits) (leCircuit bits).code
          (compCode (bits + bits) (leCircuit bits).code
            ([], (List.range (bits + bits)).map
              (fun i => if i < bits then bits + i else i - bits)))))
      (appendCode (bits + bits) (wordConstCode (bits + bits) bits offset)
        ([], List.range bits)))

/-- Every emitted instruction and output reference agrees with the typed construction. -/
theorem collisionStepCode_eq_code (bits offset : ℕ) :
    collisionStepCode bits offset = (collisionStepCircuit bits offset).code := by
  have hs : (Circuit.wiring signature
      (Fin.append (Fin.natAdd bits) (Fin.castAdd bits))).code =
      ([], (List.range (bits + bits)).map
        (fun i => if i < bits then bits + i else i - bits)) := by
    apply Circuit.code_wiring_eq_map
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, ite_eq_left j.isLt]
    · simp only [Fin.append_right, Fin.val_natAdd, Fin.val_castAdd]
      rw [ite_eq_right (by omega)]
      omega
  have hp : (Circuit.wiring signature (Fin.castAdd bits : Fin bits → Fin (bits + bits))).code =
      ([], List.range bits) := by
    simpa using Circuit.code_wiring_eq_map (σ := signature)
      (f := (Fin.castAdd bits : Fin bits → Fin (bits + bits))) (g := id) (fun _ => rfl)
  rw [collisionStepCode, ← hs, ← hp, muxCode_code, wordConstCode_eq_bits]
  change compCode (bits + bits) (muxCircuit bits).code
    (appendCode (bits + bits)
      (compCode (bits + bits) (Circuit.oneGate (σ := signature) Op.and (id : Fin 2 → Fin 2)).code
        (appendCode (bits + bits) (leCircuit bits).code
          (compCode (bits + bits) (leCircuit bits).code _))) _) = _
  simp only [compCode_code, appendCode_code]
  rfl

/-- The whole collision step is generated natively in polynomial time from unary parameters. -/
@[fun_prop] theorem computableInPolyTime_collisionStepCircuit {α : Type}
    {enc : α ↪ List Bool} {bits offset : α → ℕ}
    (hb : ComputableInPolyTime bits enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary) :
    ComputableInPolyTime (fun a => (collisionStepCircuit (bits a) (offset a)).code)
      enc encCode := by
  have hn : ComputableInPolyTime (fun a => bits a + bits a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hp : ComputableInPolyTime (fun a => ([], List.range (bits a))) enc encCode := by
    have h := unary_to_binary.map.comp (range.comp hb)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const (encOut := encList encGate) []).prod h
  have hs : ComputableInPolyTime
      (fun a => ([], (List.range (bits a + bits a)).map
        (fun i => if i < bits a then bits a + i else i - bits a))) enc encCode := by
    have hi : ComputableInPolyTime
        (fun p : α × ℕ => if p.2 < bits p.1 then bits p.1 + p.2 else p.2 - bits p.1)
        (encPair enc encUnary) encNat := by
      have hb' := unary_to_binary.comp (hb.comp (fst enc encUnary))
      have hi' := unary_to_binary.comp (snd enc encUnary)
      fun_prop
    have hr : ComputableInPolyTime (fun a => List.range (bits a + bits a))
        enc (encList encUnary) := by fun_prop
    exact (const (encOut := encList encGate) []).prod (mapWithInput hr hi)
  have hle := computableInPolyTime_leCircuit.comp hb
  have h := computableInPolyTime_compCode hn (computableInPolyTime_muxCode.comp hb)
    (computableInPolyTime_appendCode hn
      (computableInPolyTime_compCode hn (const ([(Op.and, [0, 1])], [2]))
        (computableInPolyTime_appendCode hn hle (computableInPolyTime_compCode hn hle hs)))
      (computableInPolyTime_appendCode hn
        (computableInPolyTime_wordConstCode hn hb (unary_to_binary.comp ho)) hp))
  change ComputableInPolyTime (fun a => collisionStepCode (bits a) (offset a)) enc encCode at h
  simpa only [collisionStepCode_eq_code] using h

end Cslib.Crypto.HQC
