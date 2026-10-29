/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.BalancedCode
import Complexity.Computability.Circuit.Boolean.CarrySave.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Exact balanced-code topology, dead programs and a varying-width carry-save consumer. -/

namespace ComplexityTests.BalancedCode

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

private def opCode : Code := ([(Op.and, [0, 1])], [2])
private def unitCode : Code := ([(Op.const false, []), (Op.const true, [])], [1])
private def a : Code := ([(Op.const true, [])], [1])
private def b : Code := ([(Op.const false, []), (Op.not, [1])], [2])
private def c : Code := ([], [0])
private def combine := fun x y => compCode 1 opCode (appendCode 1 x y)

example : balancedCode 1 opCode unitCode [] = unitCode := by decide
-- Neither the expensive unused operator nor the fallback is copied for a singleton.
example : balancedCode 1 (appendCode 2 opCode opCode) unitCode [b] = b := by decide
example : balancedCode 1 opCode unitCode [a, b, c] = combine a (combine b c) := by decide
-- Five leaves have the existing (ab)(c(de)) tree, including unequal and repeated blocks.
example : balancedCode 1 opCode unitCode [a, b, c, b, a] =
    combine (combine a b) (combine c (combine b a)) := by decide
example : balancedCode 1 opCode unitCode [a, b, c, b, a] ≠
    combine (combine (combine a b) (combine c b)) a := by decide

-- Zero-output programs retain dead gates, including the nonempty empty-list fallback.
example : balancedCode 0 ([(Op.const true, [])], [])
    ([(Op.const false, [])], []) [] = ([(Op.const false, [])], []) := by decide
example : (balancedCode 0 ([(Op.const true, [])], [])
    ([(Op.const false, [])], []) (List.replicate 5 ([(Op.const false, [])], []))).1.length = 9 :=
  by decide
-- A huge unused binary arity does not become a loop count.
example : balancedCode (2 ^ 128) opCode unitCode [] = unitCode := by decide

/-- Binary arity stays binary even when it is far larger than all supplied programs. -/
theorem binary_arity_generator : ComputableInPolyTime
    (fun n : ℕ => balancedCode n opCode unitCode [a, b, c]) encNat encCode := by
  fun_prop

private def largerLeaf (w : ℕ) :=
  (csa4to2 w).comp ((csa3to2 w).append (csa3to2 w))

private theorem largerLeaf_native : ComputableInPolyTime
    (fun w => (largerLeaf w).code) encUnary encCode := by
  have hn : ComputableInPolyTime (fun w : ℕ => w + (w + w)) encUnary encNat := by
    have hw := unary_to_binary
    fun_prop
  simpa only [largerLeaf, appendCode_code, compCode_code] using
    computableInPolyTime_compCode hn computableInPolyTime_csa4to2
      (computableInPolyTime_appendCode hn computableInPolyTime_csa3to2
        computableInPolyTime_csa3to2)

private def growingLeaves (p : ℕ × ℕ) :=
  List.replicate p.1 (csa3to2 p.2) ++ [largerLeaf p.2]

example : (growingLeaves (4, 2)).length = 5 ∧
    (largerLeaf 2).size > (csa3to2 2).size := by decide

/-- Both the width and the complete leaf count grow; leaf programs have unequal sizes.
The result is the existing typed carry-save tree, not a separately chosen balanced layout. -/
theorem growing_generator : ComputableInPolyTime
    (fun p : ℕ × ℕ => (Circuit.balanced (csa4to2 p.2) (csa3to2 p.2) (growingLeaves p)).code)
      (encPair encUnary encUnary) encCode := by
  have hn : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 + (p.2 + p.2))
      (encPair encUnary encUnary) encNat := by
    have hw := unary_to_binary.comp (snd encUnary encUnary)
    fun_prop
  have hl : ComputableInPolyTime
      (fun p : ℕ × ℕ => (growingLeaves p).map Circuit.code)
      (encPair encUnary encUnary) (encList encCode) := by
    simp only [growingLeaves, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
    have hlarge : ComputableInPolyTime (fun p : ℕ × ℕ => (largerLeaf p.2).code)
        (encPair encUnary encUnary) encCode :=
      largerLeaf_native.comp (snd encUnary encUnary)
    have hrep : ComputableInPolyTime
        (fun p : ℕ × ℕ => List.replicate p.1 (csa3to2 p.2).code)
        (encPair encUnary encUnary) (encList encCode) := by
      simpa only [Function.comp_def, List.map_const', List.length_range] using
        mapWithInput (f := fun (p : ℕ × ℕ) (_ : ℕ) => (csa3to2 p.2).code)
          (range.comp (fst _ _))
          (computableInPolyTime_csa3to2.comp ((snd _ _).comp (fst _ _)))
    exact listAppend' hrep (cons' hlarge (const []))
  simpa only [Function.comp_def, balancedCode_eq_code] using
    computableInPolyTime_balancedCode hn
      (computableInPolyTime_csa4to2.comp (snd _ _))
      (computableInPolyTime_csa3to2.comp (snd _ _)) hl

example (w count : ℕ) :
    Circuit.ofCode (σ := signature) (w + (w + w)) (w + w)
      (balancedCode (w + (w + w)) (csa4to2 w).code (csa3to2 w).code
        ((growingLeaves (count, w)).map Circuit.code)) =
      some (Circuit.balanced (csa4to2 w) (csa3to2 w) (growingLeaves (count, w))) := by
  rw [balancedCode_eq_code, Circuit.ofCode_code]

example : balancedCode 0 (csa4to2 0).code (zeroPairCircuit 0 0).code [] =
    (zeroPairCircuit 0 0).code := by decide
example : (balancedCode 0 (csa4to2 0).code (zeroPairCircuit 0 0).code []).1.length = 1 := by decide

end ComplexityTests.BalancedCode
