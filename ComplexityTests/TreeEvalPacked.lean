/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Complexity.Computability.TreeEval.Ary.Packed
public import Mathlib.Data.ZMod.Basic

/-! # Packed Cook–Mertz regressions

A three-bit value uses two two-bit chunks, including a partially filled last chunk. The
nonbinary alphabet embeds in `ZMod 17`. Correctness holds from nonzero, unequal register contents.
The degree-two example over `ZMod 3` checks failure at the strict unit-sum threshold.
-/

@[expose] public section

open Cslib.TreeEval Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed

namespace TreeEvalPackedTests

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def alphabet : Fin 4 ↪ ZMod 17 where
  toFun i := i.val
  inj' := by
    intro a b h
    have h' := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (a.isLt.trans (by decide : 4 < 17)),
      Nat.mod_eq_of_lt (b.isLt.trans (by decide : 4 < 17)), Fin.val_inj] using h'

def encode : (Fin 3 → Bool) → Fin 2 → Fin 4 := packBits (r := 2) (m := 2) (by decide)
def decode : (Fin 2 → Fin 4) → Fin 3 → Bool := unpackBits (r := 2) (m := 2) (by decide)

example : encode ![true, false, true] = ![1, 1] := by decide
example : decode ![1, 3] = ![true, false, true] := by decide

example (v : Fin 3 → Bool) : decode (encode v) = v :=
  unpackBits_packBits (r := 2) (m := 2) (by decide) v

def gate : Gate 2 3 := fun v i => v 0 i ^^ v 1 i
def tree : Ary.Tree 2 3 1 :=
  .node gate ![.leaf ![true, false, true], .leaf ![true, true, false]]

example : tree.eval = ![false, true, true] := by decide
example : encode tree.eval = ![2, 1] := by decide

/-- Two packed coordinates replace three separate field coordinates; all other registers are
restored, even with arbitrary masks and a nontrivial scalar. -/
theorem packed_procedure_spec (c : ZMod 17) (S : Ary.State (ZMod 17) 2 2) :
    procWith (fun v i => alphabet (encode v i)) (gateExtension alphabet encode decode)
      (Finset.univ : Finset (ZMod 17)ˣ).toList tree c 2 S =
        Function.update S 2 (S 2 + c • fun i => alphabet (encode tree.eval i)) := by
  apply procWith_gateExtension_eq alphabet encode decode
    (fun v => unpackBits_packBits (r := 2) (m := 2) (by decide) v)
    (by decide) (Finset.nodup_toList _) (fun u => Finset.mem_toList.mpr (Finset.mem_univ u))

/-- The packed low-degree extension really returns a non-Boolean field coordinate. -/
example : gateExtension alphabet encode decode gate
    (fun j k => alphabet (encode (![![true, false, true], ![true, true, false]] j) k)) 0 = 2 := by
  rw [gateExtension_embed alphabet encode decode
    (fun v => unpackBits_packBits (r := 2) (m := 2) (by decide) v)]
  decide

/-- At degree `|F|-1`, the cancellation identity can fail: `P(X,Y)=XY` on the line `(u,u)`.
Its value at the origin is zero, but its unit sum over `F₃` is two. -/
example : (∑ u : (ZMod 3)ˣ, (u : ZMod 3) * (u : ZMod 3)) = 2 := by decide

example : (∑ u : (ZMod 3)ˣ, (u : ZMod 3) * (u : ZMod 3)) ≠ -(0 : ZMod 3) := by decide

end TreeEvalPackedTests
