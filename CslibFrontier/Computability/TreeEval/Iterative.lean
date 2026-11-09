/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.CookMertz

/-!
# Frames of the iterative Cook–Mertz procedure

`Cslib.TreeEval.proc` is recursive. Unravelled into a loop, its state is the three registers, a
stack with one frame per level, and a mode. A frame records only the round, the phase within the
round, the sign and the target register of its level, which is what makes the procedure
space-efficient: the path to the current node is read off the phases of the frames.

In mode `call neg t`, the procedure is about to add `±` the value of the node at the current path
to register `t`. In mode `ret`, it continues the round of the top frame, which calls the children
in the order left, right, left, right, with signs `+, +, -, -`, as in `Cslib.TreeEval.gateRound`,
and moves on to the next round or returns. The read machine `Cslib.TreeEval.Reader.machine` runs
this loop over `ZMod p` with the units `1, …, p - 1`.

## Main definitions

* `Cslib.TreeEval.Iter.Frame`, `Cslib.TreeEval.Iter.Mode`: frames and modes.
* `Cslib.TreeEval.Iter.path`: the path to the current node.
* `Cslib.TreeEval.Iter.zmodUnit`: the units `1, …, p - 1` of `ZMod p`.

## References

* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Iter

variable {K : Type*} [Field K] {ℓ : ℕ}

/-- A frame of the recursion: the round, the phase within the round, whether the level subtracts
its value, and its target register. In phase `n` the frame has called its left child (`n` even)
or its right child (`n` odd), adding for `n < 2` and subtracting otherwise. -/
structure Frame where
  /-- The round, indexing the unit that masks the children. -/
  round : ℕ
  /-- The phase within the round. -/
  phase : Fin 4
  /-- Whether the value of this level is subtracted. -/
  neg : Bool
  /-- The target register. -/
  target : Fin 3
  deriving DecidableEq

/-- The child a frame has called: the right one in the odd phases. -/
def Frame.dir (fr : Frame) : Bool := fr.phase.val % 2 == 1

/-- The path to the node called by the top frame, from the root. -/
def path : List Frame → List Bool
  | [] => []
  | fr :: st => path st ++ [fr.dir]

/-- The mode of the machine: about to evaluate the current node into a register, or returning to
the top frame. -/
inductive Mode where
  /-- About to add `±` the value of the node at the current path to register `t`. -/
  | call (neg : Bool) (t : Fin 3)
  /-- Returning to the top frame. -/
  | ret
  deriving DecidableEq

/-- The coefficient of a sign. -/
def sgn (neg : Bool) : K := if neg then -1 else 1

@[simp] theorem path_cons (fr : Frame) (st : List Frame) :
    path (fr :: st) = path st ++ [fr.dir] := rfl

@[simp] theorem length_path (st : List Frame) : (path st).length = st.length := by
  induction st with
  | nil => rfl
  | cons fr st ih => simp [path, ih]

@[simp] theorem sgn_false : (sgn false : K) = 1 := rfl
@[simp] theorem sgn_true : (sgn true : K) = -1 := rfl

section ZMod

variable {p : ℕ} [Fact p.Prime]

/-- The units `1, …, p - 1` of `ZMod p`, in order: `zmodUnit j` is `j + 1` for `j < p - 1`. -/
def zmodUnit (p : ℕ) [Fact p.Prime] (j : ℕ) : (ZMod p)ˣ :=
  if h : ((j + 1 : ℕ) : ZMod p) = 0 then 1 else Units.mk0 _ h

theorem zmodUnit_val {j : ℕ} (hj : j < p - 1) :
    (zmodUnit p j : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by
  have hp := (Fact.out : p.Prime).two_le
  have h : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  rw [zmodUnit, dite_eq_right h, Units.val_mk0]

theorem nodup_zmodUnits : ((List.range (p - 1)).map (zmodUnit p)).Nodup := by
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
  have hp := (Fact.out : p.Prime).two_le
  have h := congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p)).val) hij
  simp only [zmodUnit_val (List.mem_range.mp hi), zmodUnit_val (List.mem_range.mp hj),
    ZMod.val_natCast, Nat.mod_eq_of_lt (show i + 1 < p by have := List.mem_range.mp hi; omega),
    Nat.mod_eq_of_lt (show j + 1 < p by have := List.mem_range.mp hj; omega)] at h
  omega

theorem mem_zmodUnits (u : (ZMod p)ˣ) : u ∈ (List.range (p - 1)).map (zmodUnit p) := by
  have hp := (Fact.out : p.Prime).two_le
  have hu : (u : ZMod p).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]; exact u.ne_zero
  have hlt := ZMod.val_lt (u : ZMod p)
  refine List.mem_map.mpr ⟨(u : ZMod p).val - 1, List.mem_range.mpr (by omega), ?_⟩
  refine Units.ext ?_
  rw [zmodUnit_val (by omega), Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]

end ZMod

end Iter

end Cslib.TreeEval
