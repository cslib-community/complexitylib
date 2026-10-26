/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Encoding the states of the read machine for undirected connectivity

The states of `Cslib.USTCON.Reader.machine` are encoded through tuples of the control, numbers in
binary, and lists of labels and frames, every label and frame by its rank among the finitely many
(`Turing.MultiTapeTM.encFinEnum`). The machines simulating the read machine keep the encoded state
on their work tapes, so its length bounds their work space, up to a constant factor and the
position of the input head.

## Main definitions

* `Cslib.USTCON.Reader.Tuple`, `Cslib.USTCON.Reader.State.toTuple`: the states as tuples.
* `Cslib.USTCON.Reader.encTuple`, `Cslib.USTCON.Reader.encState`: their encodings.

## Main results

* `Cslib.USTCON.Reader.length_encState_le`: the length of an encoded state.
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Turing MultiTapeTM Cslib.RotationMap Cslib.Reachability.Reingold

instance : Fintype Ctl where
  elems := {.hdrN, .hdrS, .hdrT, .size, .start, .fill, .next, .eval, .check, .done}
  complete x := by cases x <;> simp

instance : FinEnum Ctl :=
  FinEnum.ofList [.hdrN, .hdrS, .hdrT, .size, .start, .fill, .next, .eval, .check, .done]
    fun x => by cases x <;> decide

instance : FinEnum ReingoldPc :=
  FinEnum.ofList [.zig₀, .call₀, .zag₀, .zig₁, .call₁, .zag₁, .finish]
    fun x => by cases x <;> decide

/-- Concrete enumeration of a positive modular ring. -/
instance instFinEnumZMod (n : ℕ) [NeZero n] : FinEnum (ZMod n) :=
  FinEnum.ofEquiv (Fin n) (ZMod.finEquiv n).toEquiv.symm

/-- The states as tuples: the control and the header counter, the parameters of the instance and of
Reingold's graph, and the counters of the walks with the state of the evaluation. -/
abbrev Tuple : Type :=
  (Ctl × ℕ) × ((ℕ × ℕ × ℕ) × (ℕ × ℕ)) ×
    ((ℕ × ℕ × ℕ) × ((ℕ × ℕ) × List Label × List (ReingoldPc × Label)))

/-- A state as a tuple. -/
def State.toTuple (q : State) : Tuple :=
  ((q.ctl, q.cnt), ((q.n, q.s, q.t), (q.depth, q.len)),
    ((q.c, q.w, q.j), (q.ev.vertex, q.ev.lower, q.ev.frames)))

/-- The state of a tuple. -/
def State.ofTuple (x : Tuple) : State :=
  ⟨x.1.1, x.1.2, x.2.1.1.1, x.2.1.1.2.1, x.2.1.1.2.2, x.2.1.2.1, x.2.1.2.2, x.2.2.1.1, x.2.2.1.2.1,
    x.2.2.1.2.2, ⟨x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩⟩

@[simp]
theorem State.ofTuple_toTuple (q : State) : State.ofTuple q.toTuple = q :=
  rfl

@[simp]
theorem State.toTuple_ofTuple (x : Tuple) : (State.ofTuple x).toTuple = x :=
  rfl

/-- Labels, by their ranks. -/
def encLab : Label ↪ List Bool :=
  encFinEnum Label

/-- Frames, by their ranks. -/
def encFrame : ReingoldPc × Label ↪ List Bool :=
  encFinEnum (ReingoldPc × Label)

/-- The state of the evaluation: the slot, the labels and the frames. -/
abbrev encEval : (ℕ × ℕ) × List Label × List (ReingoldPc × Label) ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair (encList encLab) (encList encFrame))

/-- The control, by its rank. -/
def encCtl : Ctl ↪ List Bool :=
  encFinEnum Ctl

/-- The encoding of tuples. -/
abbrev encTuple : Tuple ↪ List Bool :=
  encPair (encPair encCtl encNat)
    (encPair (encPair encNat3 (encPair encNat encNat)) (encPair encNat3 encEval))

/-- The encoding of the states, through their tuples. -/
def encState : State ↪ List Bool :=
  ⟨fun q ↦ encTuple q.toTuple, fun q q' h ↦ by
    rw [← State.ofTuple_toTuple q, ← State.ofTuple_toTuple q', encTuple.injective h]⟩

@[simp]
theorem encState_apply (q : State) : encState q = encTuple q.toTuple :=
  rfl

/-- The arithmetic of the framing of a state. -/
private theorem framing_le (a b c d e f g h i j k l m o : ℕ) :
    2 * (2 * a + 1 + b) + 1 + (2 * (2 * (2 * c + 1 + (2 * d + 1 + e)) + 1 + (2 * f + 1 + g)) + 1 +
      (2 * (2 * h + 1 + (2 * i + 1 + j)) + 1 + (2 * (2 * k + 1 + l) + 1 +
        (2 * m + 1 + o)))) ≤
      64 * (a + b + c + d + e + f + g + h + i + j + k + l + m + o + 1) := by
  linarith

/-- **The length of an encoded state**: the framing doubles the encodings of the components, a
bounded number of times. -/
theorem length_encState_le (q : State) :
    (encState q).length ≤ 64 * ((encCtl q.ctl).length + (encNat q.cnt).length +
      (encNat q.n).length + (encNat q.s).length + (encNat q.t).length + (encNat q.depth).length +
      (encNat q.len).length + (encNat q.c).length + (encNat q.w).length + (encNat q.j).length +
      (encNat q.ev.vertex.1).length + (encNat q.ev.vertex.2).length +
      (encList encLab q.ev.lower).length + (encList encFrame q.ev.frames).length + 1) := by
  simp only [encState_apply, State.toTuple, length_encPair]
  exact framing_le _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Cslib.USTCON.Reader
