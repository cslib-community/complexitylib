/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.TreeEval.CookMertz

/-!
# Tree Evaluation with fan-in `d`

A ternary instance evaluated directly, and the Cook–Mertz procedure over `ZMod 11` on two-bit
values: the field-size hypothesis `d * ℓ < |K| - 1` holds, as `3 * 2 < 10`, so the correctness
theorem is not vacuous. A binary instance embedded with fan-in `2` keeps its value, the
fan-in-`2` procedure over `ZMod 7` computes it, and on it the fan-in-`2` procedure is the binary
procedure.
-/

namespace ComplexityTests.TreeEvalAry

open Cslib.TreeEval Cslib.TreeEval.Ary

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Bitwise majority of three two-bit values. -/
def majGate : Ary.Gate 3 2 := fun v i => (v 0 i && v 1 i) || (v 0 i && v 2 i) || (v 1 i && v 2 i)

/-- Bitwise exclusive or of three two-bit values. -/
def xorGate : Ary.Gate 3 2 := fun v i => v 0 i ^^ v 1 i ^^ v 2 i

/-- A height-two ternary instance:
`maj (10 ⊕ 11 ⊕ 01, 01 ⊕ 00 ⊕ 00, 11 ⊕ 11 ⊕ 11) = maj (00, 01, 11) = 01`. -/
def sample : Ary.Tree 3 2 2 :=
  .node majGate ![
    .node xorGate ![.leaf ![true, false], .leaf ![true, true], .leaf ![false, true]],
    .node xorGate ![.leaf ![false, true], .leaf ![false, false], .leaf ![false, false]],
    .node xorGate ![.leaf ![true, true], .leaf ![true, true], .leaf ![true, true]]]

example : sample.eval = ![false, true] := by decide

example : sample.nodeAt [2, 0] = .leaf ![true, true] := rfl

/-- The ternary Cook–Mertz procedure over `ZMod 11` computes the value of the sample instance. -/
example : Ary.proc (Finset.univ : Finset (ZMod 11)ˣ).toList sample 1 3 0 3 =
    embed ![false, true] := by
  rw [← Ary.embed_eval_eq_proc (by simp) sample 3]
  congr 1
  decide

/-- Any ternary two-bit instance over `ZMod 11` is computed, for every target register. -/
example {h : ℕ} (T : Ary.Tree 3 2 h) (t : Fin 4) :
    embed T.eval = Ary.proc (Finset.univ : Finset (ZMod 11)ˣ).toList T 1 t 0 t :=
  Ary.embed_eval_eq_proc (by simp) T t

/-- A binary instance: `(10 ⊕ 11) ∧ (01 ⊕ 00) = 01`. -/
def binarySample : Cslib.TreeEval.Tree 2 2 :=
  .node (fun x y i => x i && y i)
    (.node (fun x y i => x i ^^ y i) (.leaf ![true, false]) (.leaf ![true, true]))
    (.node (fun x y i => x i ^^ y i) (.leaf ![false, true]) (.leaf ![false, false]))

example : (Ary.Tree.ofBinary binarySample).eval = binarySample.eval := Ary.Tree.eval_ofBinary _

/-- With fan-in `2`, the procedure over `ZMod 7` computes the embedded binary instance. -/
example : Ary.proc (Finset.univ : Finset (ZMod 7)ˣ).toList (Ary.Tree.ofBinary binarySample)
    1 2 0 2 = embed ![false, true] := by
  rw [← Ary.embed_eval_eq_proc (by simp) _ 2, Ary.Tree.eval_ofBinary]
  congr 1
  decide

/-- On the embedded binary instance, the fan-in-`2` procedure over `ZMod 7` is the binary
procedure, for every coefficient, target register and contents of the registers. -/
example (c : ZMod 7) (t : Fin 3) (S : Cslib.TreeEval.State (ZMod 7) 2) :
    Ary.proc (Finset.univ : Finset (ZMod 7)ˣ).toList (Ary.Tree.ofBinary binarySample) c t S =
      Cslib.TreeEval.proc (Finset.univ : Finset (ZMod 7)ˣ).toList binarySample c t S := by
  rw [Ary.proc_ofBinary]

end ComplexityTests.TreeEvalAry
