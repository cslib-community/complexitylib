/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.CookMertz

/-!
# Iterative control for fan-in-`d` Cook–Mertz

The controller unravels `Ary.procWith` into calls and returns over one shared register bank.
A frame retains a round number, child index, forward/undo phase, coefficient and target register;
it stores neither a tree nor a saved register bank. Reading a node is parameterized by the
existing `Tree.Node` lookup at a path. The path is recovered from the stack's child indices.

A forward phase scales a child's register and calls that child with coefficient one. After the
last forward call, it performs the supplied gate update. Undo phases call each child with
coefficient minus one and undo its scaling upon return. Children in both phases are processed
in increasing order, exactly as in `Ary.gateRoundWith`.

## Main definitions

* `Cslib.TreeEval.Ary.Iter.Frame`, `Mode`, `Cfg`: frames, call/return modes and global state.
* `Cslib.TreeEval.Ary.Iter.path`: recover the current node path without storing it per frame.
* `Cslib.TreeEval.Ary.Iter.step`, `runFrom`: the controller and its clocked iteration.

## References

* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, with signed calls.
* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], Appendix A.

This is pure control semantics for positive fan-in. Node lookup and the supplied gate extension
are parameters; their native implementation and space costs are separate obligations.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Iter

/-- A suspended call, retaining control data only. -/
structure Frame (K : Type*) (d : ℕ) where
  /-- The unit-round index. -/
  round : ℕ
  /-- The child currently being evaluated or just returned. -/
  child : Fin d
  /-- False during forward calls and true during undo calls. -/
  undo : Bool
  /-- The coefficient of the suspended call. -/
  coeff : K
  /-- The register targeted by the suspended call. -/
  target : Fin (d + 1)
  deriving DecidableEq

/-- Calling a node with a coefficient and target, or returning from one. -/
inductive Mode (K : Type*) (d : ℕ) where
  /-- Evaluate the current node into the target with the supplied coefficient. -/
  | call (coeff : K) (target : Fin (d + 1))
  /-- Continue the innermost suspended call, or halt if there is none. -/
  | ret
  deriving DecidableEq

/-- One shared register bank, the suspended calls and the current mode. -/
structure Cfg (K : Type*) (d r : ℕ) where
  /-- Registers shared by all levels. -/
  regs : Ary.State K d r
  /-- Suspended calls, innermost first. -/
  stack : List (Frame K d)
  /-- The current call or return. -/
  mode : Mode K d
  deriving DecidableEq

variable {K : Type*} {d b r : ℕ}

/-- The root-to-current-node path, read from the suspended calls. -/
def path (st : List (Frame K d)) : List (Fin d) := st.reverse.map Frame.child

@[simp] theorem path_nil : path ([] : List (Frame K d)) = [] := rfl

@[simp] theorem path_cons (fr : Frame K d) (st : List (Frame K d)) :
    path (fr :: st) = path st ++ [fr.child] := by
  simp [path]

@[simp] theorem length_path (st : List (Frame K d)) : (path st).length = st.length := by
  simp [path]

/-- Start a root call from arbitrary global registers. -/
def initialCfg (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) : Cfg K d r :=
  ⟨S, [], .call c t⟩

/-- A returned value with no suspended caller is final. -/
def halted (q : Cfg K d r) : Bool :=
  match q.mode with
  | .call _ _ => false
  | .ret => q.stack.isEmpty

@[simp] theorem halted_ret_nil (S : Ary.State K d r) :
    halted (⟨S, [], .ret⟩ : Cfg K d r) = true := rfl

variable [Field K]

/-- Read a unit round by index; the fallback makes malformed control states total. -/
def unitAt (us : List Kˣ) (i : ℕ) : Kˣ := us.getD i 1

/-- Update at a gate, leaving the registers unchanged if the requested path is invalid. -/
def updateAt (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (read : List (Fin d) → Tree.Node d b) (P : List (Fin d)) (c : K)
    (t : Fin (d + 1)) (S : Ary.State K d r) : Ary.State K d r :=
  match read P with
  | .gate f => gateUpdateWith E f c t S
  | _ => S

/-- Begin the first forward child of a round, scaling before the recursive call. -/
def beginRound (hd : 0 < d) (us : List Kˣ) (i : ℕ) (c : K) (t : Fin (d + 1))
    (S : Ary.State K d r) (st : List (Frame K d)) : Cfg K d r :=
  ⟨scale (reg t ⟨0, hd⟩) (unitAt us i : K) S,
    ⟨i, ⟨0, hd⟩, false, c, t⟩ :: st, .call 1 (reg t ⟨0, hd⟩)⟩

/-- One control step of the fan-in-`d` procedure. -/
def step (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) : Cfg K d r :=
  match q.mode with
  | .call c t =>
    match read (path q.stack) with
    | .leaf v => ⟨Function.update q.regs t (q.regs t + c • e v), q.stack, .ret⟩
    | .gate _ =>
      match us with
      | [] => ⟨q.regs, q.stack, .ret⟩
      | _ :: _ => beginRound hd us 0 c t q.regs q.stack
    | .none => ⟨q.regs, q.stack, .ret⟩
  | .ret =>
    match q.stack with
    | [] => q
    | fr :: st =>
      if fr.undo then
        let S := scale (reg fr.target fr.child) (((unitAt us fr.round)⁻¹ : Kˣ) : K) q.regs
        if h : fr.child.val + 1 < d then
          ⟨S, { fr with child := ⟨fr.child.val + 1, h⟩ } :: st,
            .call (-1) (reg fr.target ⟨fr.child.val + 1, h⟩)⟩
        else if fr.round + 1 < us.length then
          beginRound hd us (fr.round + 1) fr.coeff fr.target S st
        else ⟨S, st, .ret⟩
      else
        if h : fr.child.val + 1 < d then
          ⟨scale (reg fr.target ⟨fr.child.val + 1, h⟩) (unitAt us fr.round : K) q.regs,
            { fr with child := ⟨fr.child.val + 1, h⟩ } :: st,
            .call 1 (reg fr.target ⟨fr.child.val + 1, h⟩)⟩
        else
          ⟨updateAt E read (path st) fr.coeff fr.target q.regs,
            { fr with child := ⟨0, hd⟩, undo := true } :: st,
            .call (-1) (reg fr.target ⟨0, hd⟩)⟩

/-- Iterate control steps from any supplied configuration. -/
def runFrom (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) (n : ℕ) : Cfg K d r :=
  (step hd e E us read)^[n] q

@[simp] theorem runFrom_zero (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) :
    runFrom hd e E us read q 0 = q := rfl

@[simp] theorem runFrom_one (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) :
    runFrom hd e E us read q 1 = step hd e E us read q := rfl

/-- A successor clock performs one more control step. -/
theorem runFrom_succ (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) (n : ℕ) :
    runFrom hd e E us read q (n + 1) = step hd e E us read (runFrom hd e E us read q n) :=
  Function.iterate_succ_apply' _ _ _

/-- Consecutive runs compose without resetting registers or continuation frames. -/
theorem runFrom_add (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (q : Cfg K d r) (m n : ℕ) :
    runFrom hd e E us read q (m + n) =
      runFrom hd e E us read (runFrom hd e E us read q m) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, runFrom_succ, ih, runFrom_succ]

/-- A final return is stationary. -/
@[simp] theorem step_ret_nil (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) :
    step hd e E us read ⟨S, [], .ret⟩ = ⟨S, [], .ret⟩ := rfl

/-- A leaf call uses one control step and leaves its continuation stack intact. -/
theorem step_call_leaf (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (st : List (Frame K d))
    (c : K) (t : Fin (d + 1)) (v : Fin b → Bool) (hv : read (path st) = .leaf v) :
    step hd e E us read ⟨S, st, .call c t⟩ =
      ⟨Function.update S t (S t + c • e v), st, .ret⟩ := by
  simp [step, hv]

/-- A gate starts the first round when the unit enumeration is nonempty. -/
theorem step_call_gate_cons (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (u : Kˣ) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (st : List (Frame K d))
    (c : K) (t : Fin (d + 1)) (f : Gate d b) (hf : read (path st) = .gate f) :
    step hd e E (u :: us) read ⟨S, st, .call c t⟩ = beginRound hd (u :: us) 0 c t S st := by
  simp [step, hf]

/-- With no unit rounds a gate call immediately returns unchanged registers. -/
theorem step_call_gate_nil (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (st : List (Frame K d))
    (c : K) (t : Fin (d + 1)) (f : Gate d b) (hf : read (path st) = .gate f) :
    step hd e E [] read ⟨S, st, .call c t⟩ = ⟨S, st, .ret⟩ := by
  simp [step, hf]

/-- Reading a valid gate performs exactly the supplied algebraic gate update. -/
theorem updateAt_gate (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (read : List (Fin d) → Tree.Node d b) (P : List (Fin d)) (c : K)
    (t : Fin (d + 1)) (S : Ary.State K d r) (f : Gate d b) (hf : read P = .gate f) :
    updateAt E read P c t S = gateUpdateWith E f c t S := by
  simp [updateAt, hf]

/-- After a forward child returns, scale and call the next child if one remains. -/
theorem step_ret_forward_next (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (hu : fr.undo = false) (hj : fr.child.val + 1 < d) :
    step hd e E us read ⟨S, fr :: st, .ret⟩ =
      ⟨scale (reg fr.target ⟨fr.child.val + 1, hj⟩) (unitAt us fr.round : K) S,
        { fr with child := ⟨fr.child.val + 1, hj⟩ } :: st,
        .call 1 (reg fr.target ⟨fr.child.val + 1, hj⟩)⟩ := by
  simp [step, hu, hj]

/-- The last forward return performs the gate update and calls the first undo child. -/
theorem step_ret_forward_last (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (hu : fr.undo = false) (hj : ¬fr.child.val + 1 < d) :
    step hd e E us read ⟨S, fr :: st, .ret⟩ =
      ⟨updateAt E read (path st) fr.coeff fr.target S,
        { fr with child := ⟨0, hd⟩, undo := true } :: st,
        .call (-1) (reg fr.target ⟨0, hd⟩)⟩ := by
  simp [step, hu, hj]

/-- An undo return first cancels the scaling, then calls the next child without scaling it. -/
theorem step_ret_undo_next (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (hu : fr.undo = true) (hj : fr.child.val + 1 < d) :
    step hd e E us read ⟨S, fr :: st, .ret⟩ =
      ⟨scale (reg fr.target fr.child) (((unitAt us fr.round)⁻¹ : Kˣ) : K) S,
        { fr with child := ⟨fr.child.val + 1, hj⟩ } :: st,
        .call (-1) (reg fr.target ⟨fr.child.val + 1, hj⟩)⟩ := by
  simp [step, hu, hj]

/-- The last undo return begins the next round if one remains. -/
theorem step_ret_undo_round (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (hu : fr.undo = true) (hj : ¬fr.child.val + 1 < d)
    (hi : fr.round + 1 < us.length) :
    step hd e E us read ⟨S, fr :: st, .ret⟩ =
      beginRound hd us (fr.round + 1) fr.coeff fr.target
        (scale (reg fr.target fr.child) (((unitAt us fr.round)⁻¹ : Kˣ) : K) S) st := by
  simp [step, hu, hj, hi]

/-- The final undo return pops exactly the current call's frame. -/
theorem step_ret_undo_last (hd : 0 < d) (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (read : List (Fin d) → Tree.Node d b) (S : Ary.State K d r) (fr : Frame K d)
    (st : List (Frame K d)) (hu : fr.undo = true) (hj : ¬fr.child.val + 1 < d)
    (hi : ¬fr.round + 1 < us.length) :
    step hd e E us read ⟨S, fr :: st, .ret⟩ =
      ⟨scale (reg fr.target fr.child) (((unitAt us fr.round)⁻¹ : Kˣ) : K) S, st, .ret⟩ := by
  simp [step, hu, hj, hi]

end Cslib.TreeEval.Ary.Iter
