/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Complexity.Computability.TreeEval.Ary.IterativePacked
public import Complexity.Computability.TreeEval.Ary.IterativeBounds
public import Complexity.Computability.TreeEval.Ary.Packed
public import Complexity.Computability.TreeEval.Iterative

/-!
# Iterative fan-in-d Cook–Mertz regressions

Positive arities one, two and three exercise all forward and undo child transitions. Pure
correspondence is checked from arbitrary registers and a nontrivial coefficient. A packed
three-bit value in two coordinates exercises the same controller with a different register width.
-/

@[expose] public section

namespace ComplexityTests.TreeEvalIterative

open Cslib.TreeEval Cslib.TreeEval.Ary

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- One bit as one field coordinate. -/
def value (v : Fin 1 → Bool) : Fin 1 → ZMod 7 := fun i => if v i then 1 else 0

/-- A gate reading its first child, for any positive arity. -/
def wire (d : ℕ) (hd : 0 < d) : Ary.Gate d 1 := fun v => v ⟨0, hd⟩

/-- The wire gate's field extension. -/
def extension (d : ℕ) (hd : 0 < d) :
    Ary.Gate d 1 → (Fin d → Fin 1 → ZMod 7) → Fin 1 → ZMod 7 := fun _ v => v ⟨0, hd⟩

/-- A one-level wire tree with true at the first leaf. -/
def sample (d : ℕ) (hd : 0 < d) : Ary.Tree d 1 1 :=
  .node (wire d hd) fun j => .leaf fun _ => j.val == 0

/-- A single unit round on this tree takes four transitions per child plus its initial step. -/
example : (Ary.Iter.runFrom (by decide) value (extension 1 (by decide)) [1]
    (sample 1 (by decide)).nodeAt (Ary.Iter.initialCfg 0 1 1) 5).regs 1 0 = 6 := by decide

example : (Ary.Iter.runFrom (by decide) value (extension 2 (by decide)) [1]
    (sample 2 (by decide)).nodeAt (Ary.Iter.initialCfg 0 1 2) 9).regs 2 0 = 6 := by decide

example : (Ary.Iter.runFrom (by decide) value (extension 3 (by decide)) [1]
    (sample 3 (by decide)).nodeAt (Ary.Iter.initialCfg 0 1 3) 13).regs 3 0 = 6 := by decide

example : (Ary.Iter.runFrom (by decide) value (extension 3 (by decide)) [1]
    (sample 3 (by decide)).nodeAt (Ary.Iter.initialCfg 0 1 3) 13).stack = [] := by decide

/-- A second round restores dirty masks as well as traversing the round-advance branch. -/
example : (Ary.Iter.runFrom (by decide) value (extension 2 (by decide)) [1, -1]
    (sample 2 (by decide)).nodeAt (Ary.Iter.initialCfg (fun _ _ => 4) 1 2) 17).regs =
      (fun r _ => if r.val = 2 then 2 else 4) := by decide

/-- A height-two tree makes the controller resume a genuine suspended caller. -/
def nested : Ary.Tree 2 1 2 := .node (wire 2 (by decide)) fun _ => sample 2 (by decide)

/-- The caller frame is control data, without a saved bank of registers. -/
def caller : Ary.Iter.Frame (ZMod 7) 2 := ⟨0, 0, false, 2, 2⟩

example : (Ary.Iter.runFrom (by decide) value (extension 2 (by decide)) [1] nested.nodeAt
    ⟨(fun _ _ => 4), [caller], .call 1 0⟩ 9).stack = [caller] := by decide

example : (Ary.Iter.runFrom (by decide) value (extension 2 (by decide)) [1] nested.nodeAt
    (Ary.Iter.initialCfg (fun _ _ => 4) 1 2) 41).regs =
      Ary.procWith value (extension 2 (by decide)) [1] nested 1 2 (fun _ _ => 4) := by decide

example (n : ℕ) : Ary.Iter.ControlBounds 2 1
    (Ary.Iter.runFrom (by decide) value (extension 2 (by decide)) [1] nested.nodeAt
      (Ary.Iter.initialCfg (fun _ _ => 4) 1 2) n) :=
  Ary.Iter.runFrom_initial_bounds nested (by decide) value (extension 2 (by decide)) [1]
    (fun _ _ => 4) 1 2 n

/-- Empty rounds immediately return a gate call, preserving a nonzero register bank. -/
example : (Ary.Iter.runFrom (by decide) value (extension 3 (by decide)) []
    (sample 3 (by decide)).nodeAt (Ary.Iter.initialCfg (fun _ _ => 4) 2 3) 1).regs =
      (fun _ _ => 4) := by decide

/-- The root theorem applies to arbitrary initial masks, coefficients and nested trees. -/
theorem arbitrary_masks {h : ℕ} (T : Ary.Tree 3 1 h) (S : Ary.State (ZMod 7) 3 1)
    (c : ZMod 7) (t : Fin 4) : ∃ N,
    Ary.Iter.runFrom (by decide) value (extension 3 (by decide)) [1, -1] T.nodeAt
      (Ary.Iter.initialCfg S c t) N =
        ⟨Ary.procWith value (extension 3 (by decide)) [1, -1] T c t S, [], .ret⟩ :=
  Ary.Iter.exists_runFrom_root (by decide) value (extension 3 (by decide)) [1, -1] T S c t

/-- The existing binary recursive specification is recovered through its established bridge. -/
theorem binary_recursive_compatibility {h : ℕ} (T : Cslib.TreeEval.Tree 1 h)
    (S : Cslib.TreeEval.State (ZMod 7) 1) (c : ZMod 7) (t : Fin 3) : ∃ N,
    Ary.Iter.runFrom (by decide) Cslib.TreeEval.embed
      (fun f x i => MvPolynomial.eval (fun q => x q.1 q.2) (Ary.gatePoly f i))
      [1, -1] (Ary.Tree.ofBinary T).nodeAt (Ary.Iter.initialCfg S c t) N =
        ⟨Cslib.TreeEval.proc [1, -1] T c t S, [], .ret⟩ := by
  obtain ⟨N, hN⟩ := Ary.Iter.exists_runFrom_root (by decide) Cslib.TreeEval.embed
    (fun f x i => MvPolynomial.eval (fun q => x q.1 q.2) (Ary.gatePoly f i))
    [1, -1] (Ary.Tree.ofBinary T) S c t
  refine ⟨N, ?_⟩
  rw [hN, Ary.procWith_embed, Ary.proc_ofBinary]

/-- Pack three bits into two symbols, with a partially filled last chunk. -/
def encode : (Fin 3 → Bool) → Fin 2 → Fin 4 :=
  Ary.Packed.packBits (r := 2) (m := 2) (by decide)

/-- Decode the original three-bit prefix. -/
def decode : (Fin 2 → Fin 4) → Fin 3 → Bool :=
  Ary.Packed.unpackBits (r := 2) (m := 2) (by decide)

/-- Four chunk symbols in the field. -/
def alphabet : Fin 4 ↪ ZMod 17 where
  toFun a := a.val
  inj' := by
    intro a b heq
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (a.isLt.trans (by decide : 4 < 17)),
      Nat.mod_eq_of_lt (b.isLt.trans (by decide : 4 < 17)), Fin.val_inj] using hv

/-- The iterative loop computes the encoded value with a counter-based inner gate loop. -/
theorem packed_root {h : ℕ} (T : Ary.Tree 2 3 h) (S : Ary.State (ZMod 17) 2 2)
    (c : ZMod 17) (t : Fin 3) : ∃ N,
    Ary.Iter.runFrom (by decide) (fun v i => alphabet (encode v i))
      (Ary.Packed.counterGateExtension (by decide : 0 < 4) encode decode)
      (Finset.univ : Finset (ZMod 17)ˣ).toList T.nodeAt (Ary.Iter.initialCfg S c t) N =
        ⟨Function.update S t (S t + c • fun i => alphabet (encode T.eval i)), [], .ret⟩ := by
  apply Ary.Iter.exists_runFrom_counter_root (by decide) (by decide) (by decide)
    alphabet (fun _ => rfl) encode decode
    (fun v => Ary.Packed.unpackBits_packBits (r := 2) (m := 2) (by decide) v)
    (by decide) (Finset.nodup_toList _) (fun u => Finset.mem_toList.mpr (Finset.mem_univ u))

end ComplexityTests.TreeEvalIterative
