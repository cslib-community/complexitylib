/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Reader.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Basic

/-!
# Encodings of the states of the Tree Evaluation read machine

The states of `Cslib.TreeEval.Reader.machine` are encoded as tuples: the value length, the height
and the prime in binary, the registers as lists of binary naturals, the stack as a list of frames,
each a binary round with finitely many other fields, the mode as a finite tag, and the control state
as a tag with two binary naturals and a list of them.

## Main definitions

* `Cslib.TreeEval.Reader.State.toTuple`: a state as a tuple.
* `Cslib.TreeEval.Reader.encState`: the encoding of states.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM Iter

/-- A frame as a tuple. -/
def Frame.equiv : Frame ≃ ℕ × Fin 4 × Bool × Fin 3 where
  toFun fr := (fr.round, fr.phase, fr.neg, fr.target)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The encoding of frames. -/
def encFrame : Frame ↪ List Bool :=
  encOfEquiv Frame.equiv (encPair encNat (encFinEnum (Fin 4 × Bool × Fin 3)))

/-- A mode as an option. -/
def Mode.equiv : Mode ≃ Option (Bool × Fin 3) where
  toFun
    | .call neg t => some (neg, t)
    | .ret => none
  invFun
    | some (neg, t) => .call neg t
    | none => .ret
  left_inv m := by cases m <;> rfl
  right_inv o := by rcases o with _ | ⟨_, _⟩ <;> rfl

instance : FinEnum Mode := FinEnum.ofEquiv _ Mode.equiv

/-- The encoding of modes. -/
def encMode : Mode ↪ List Bool := encFinEnum Mode

/-- The control state as a tuple: a tag, two naturals and a list. -/
def Ctl.toTuple : Ctl → Fin 7 × ℕ × ℕ × List ℕ
  | .hdrLength n => (0, n, 0, [])
  | .hdrHeight n => (1, n, 0, [])
  | .prime q d => (2, q, d, [])
  | .run => (3, 0, 0, [])
  | .leaf i => (4, i, 0, [])
  | .scan k acc => (5, k, 0, acc)
  | .done => (6, 0, 0, [])

theorem Ctl.toTuple_injective : Function.Injective Ctl.toTuple := by
  intro c c' h
  cases c <;> cases c' <;> simp_all [Ctl.toTuple]

/-- The encoding of tuples of control states. -/
abbrev encCtlTuple : Fin 7 × ℕ × ℕ × List ℕ ↪ List Bool :=
  encPair (encFinEnum (Fin 7)) (encPair encNat (encPair encNat (encList encNat)))

/-- The encoding of control states. -/
def encCtl : Ctl ↪ List Bool :=
  ⟨fun c => encCtlTuple c.toTuple, encCtlTuple.injective.comp Ctl.toTuple_injective⟩

/-- The encoding of registers. -/
abbrev encRegs : Regs ↪ List Bool :=
  encPair (encList encNat) (encPair (encList encNat) (encList encNat))

/-- The tuples of states. -/
abbrev Tuple := ((ℕ × ℕ × ℕ) × Regs) × (List Frame × Mode) × (Fin 7 × ℕ × ℕ × List ℕ)

/-- A state as a tuple. -/
def State.toTuple (s : State) : Tuple :=
  (((s.ell, s.height, s.p), s.regs), (s.stack, s.mode), s.ctl.toTuple)

theorem State.toTuple_injective : Function.Injective State.toTuple := by
  rintro ⟨e, h, p, R, st, m, c⟩ ⟨e', h', p', R', st', m', c'⟩ hs
  simp only [State.toTuple, Prod.mk.injEq] at hs
  obtain ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, ⟨rfl, rfl⟩, hc⟩ := hs
  rw [Ctl.toTuple_injective hc]

/-- The encoding of tuples of states. -/
abbrev encTuple : Tuple ↪ List Bool :=
  encPair (encPair (encPair encNat (encPair encNat encNat)) encRegs)
    (encPair (encPair (encList encFrame) encMode) encCtlTuple)

/-- **The encoding of states.** -/
def encState : State ↪ List Bool :=
  ⟨fun s => encTuple s.toTuple, encTuple.injective.comp State.toTuple_injective⟩

@[simp] theorem encState_apply (s : State) : encState s = encTuple s.toTuple := rfl

@[simp] theorem encCtl_apply (c : Ctl) : encCtl c = encCtlTuple c.toTuple := rfl

end Reader

end Cslib.TreeEval
