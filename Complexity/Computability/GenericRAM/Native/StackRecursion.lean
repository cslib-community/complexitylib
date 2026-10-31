/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Combinators
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Depth-first recursion with an explicit stack

A *recursion scheme* (`StackRecursion.Scheme`) evaluates node descriptions `x : X` to values
`y : Y`. A node is either a leaf, evaluated by `leaf`, or a call, which keeps an accumulator
`a : A`: starting from `start x`, it asks `next x a` for its next child, folds the child's value
into the accumulator with `absorb`, and when `next` returns `none` produces its value with
`finish`. Children may depend on the values of earlier children through the accumulator.

**The machine** (`Scheme.step`). Its state is the stack of open calls, innermost first, each
with its accumulator, and a register holding a pending call or a returned value. Each step
performs one call or one return. A derivation `Scheme.Eval I x y n h`, with `n` nodes and `h`
stack levels, makes the machine reach `y` in `2 * n - 1` steps (`Scheme.Eval.run`), through
states with at most `h` open calls whose nodes, frames and values satisfy the invariant `I`
(`Scheme.Eval.good_iterate`).

**The native certificate** (`Scheme.certificate`). The leaf step is an arbitrary native
certificate; the other components are polynomial-time. One fixed machine runs the stack machine
for a natively computed number `fuel a` of steps (`NativeCertificate.iterate`) and returns the
register. When `2 * n - 1 ≤ fuel a` the result is `y` (`Scheme.run_eq_some`). If every node,
frame and value on the derivation has encoded length at most `F` and every leaf is evaluated
within time `TL` and space `SL`, the time is at most `fuel a + 1` times
`K ((h + 1) (F + 1)) ^ K + TL` and the workspace at most `K ((h + 1) (F + 1)) ^ K + SL`, up to
the cost of computing the fuel and the root and of the binary clock, for one constant `K` of the
scheme (`Scheme.certificate_le`). Only the stack is kept, so the workspace grows with the depth,
not with the number of nodes. The number of nodes of a recursion tree is bounded in
`Complexity/Foundations/Data/Nat/RecursionTree.lean`.

This is the depth-first evaluation of the recursion in the proof of Theorem D.1 of
[OpenAI2026ETH] (Appendix D.4.7, p. 64), which keeps one sum over mode tuples and one product
over groups per stack level. The scheme is generic: the recursion of Appendix D.4 is one
instance, with its leaves evaluated by direct summation.

## Main definitions

* `Cslib.GenericRAM.StackRecursion.Scheme`: a recursion scheme.
* `Cslib.GenericRAM.StackRecursion.Invariant`: predicates on the nodes, frames and values met.
* `Cslib.GenericRAM.StackRecursion.Scheme.Loop`, `Cslib.GenericRAM.StackRecursion.Scheme.Eval`:
  derivations of the loop of a call and of the value of a node, with their node counts and
  stack depths.
* `Cslib.GenericRAM.StackRecursion.Scheme.step`, `Cslib.GenericRAM.StackRecursion.Scheme.run`:
  the stack machine and its clocked run.
* `Cslib.GenericRAM.StackRecursion.Scheme.PolyTime`: the polynomial-time components.
* `Cslib.GenericRAM.StackRecursion.Scheme.certificate`: one native machine for the clocked run.

## Main results

* `Cslib.GenericRAM.StackRecursion.Scheme.Eval.run`: a derivation with `n` nodes is evaluated in
  `2 * n - 1` steps.
* `Cslib.GenericRAM.StackRecursion.Scheme.run_eq_some`: enough fuel gives the value.
* `Cslib.GenericRAM.StackRecursion.Scheme.certificate_le`: time `fuel + 1` times a polynomial in
  `(h + 1) * (F + 1)` plus the leaf time, and workspace a polynomial plus the leaf space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

@[expose] public section

namespace Cslib.GenericRAM.StackRecursion

open Turing.MultiTapeTM

/-- A *recursion scheme*. A node `x` is a leaf when `isLeaf x`, with value `leaf x`. Otherwise
it is a call: its accumulator starts at `start x`; while `next x a` returns a child, the child is
evaluated and its value folded into the accumulator by `absorb`; when `next x a` is `none` the
call returns `finish x a`. -/
structure Scheme (X A Y : Type) where
  /-- Whether a node is a leaf. -/
  isLeaf : X → Bool
  /-- The value of a leaf. -/
  leaf : X → Y
  /-- The initial accumulator of a call. -/
  start : X → A
  /-- The next child of a call with the given accumulator, or `none` when it is done. -/
  next : X → A → Option X
  /-- Fold the value of the current child into the accumulator. -/
  absorb : X → A → Y → A
  /-- The value of a call from its final accumulator. -/
  finish : X → A → Y

/-- Predicates on what a derivation meets: the nodes evaluated, the frames pushed (a call with
its accumulator while one of its children is evaluated) and the values returned. -/
structure Invariant (X A Y : Type) where
  /-- Every node evaluated satisfies `node`. -/
  node : X → Prop
  /-- Every pushed frame satisfies `frame`. -/
  frame : X → A → Prop
  /-- Every returned value satisfies `value`. -/
  value : Y → Prop

/-- A state of the stack machine: the open calls with their accumulators, innermost first, a
pending call and a returned value. -/
abbrev State (X A Y : Type) := List (X × A) × Option X × Option Y

namespace Scheme

variable {X A Y : Type} (R : Scheme X A Y)

/-- Continue the call `x` with accumulator `a` above the stack `st`: push its frame and call its
next child, or return its value when it has none. -/
def resume (x : X) (a : A) (st : List (X × A)) : State X A Y :=
  match R.next x a with
  | none => (st, none, some (R.finish x a))
  | some c => ((x, a) :: st, some c, none)

/-- **One step of the stack machine.** A pending leaf is evaluated; a pending call is started; a
returned value is absorbed by the innermost open call, which then continues. A value returned
with no open call is final. -/
def step : State X A Y → State X A Y
  | (st, some x, _) => if R.isLeaf x then (st, none, some (R.leaf x)) else R.resume x (R.start x) st
  | ((x, a) :: st, none, some y) => R.resume x (R.absorb x a y) st
  | σ => σ

theorem resume_of_next_none {x : X} {a : A} (st : List (X × A)) (h : R.next x a = none) :
    R.resume x a st = (st, none, some (R.finish x a)) := by
  simp [resume, h]

theorem resume_of_next_some {x c : X} {a : A} (st : List (X × A)) (h : R.next x a = some c) :
    R.resume x a st = ((x, a) :: st, some c, none) := by
  simp [resume, h]

theorem step_leaf {x : X} (st : List (X × A)) (r : Option Y) (h : R.isLeaf x = true) :
    R.step (st, some x, r) = (st, none, some (R.leaf x)) := by
  simp [step, h]

theorem step_call {x : X} (st : List (X × A)) (r : Option Y) (h : R.isLeaf x = false) :
    R.step (st, some x, r) = R.resume x (R.start x) st := by
  simp [step, h]

theorem step_return (x : X) (a : A) (st : List (X × A)) (y : Y) :
    R.step ((x, a) :: st, none, some y) = R.resume x (R.absorb x a y) st := rfl

/-- A value returned with no open call is final. -/
@[simp] theorem step_final (y : Y) : R.step ([], none, some y) = ([], none, some y) := rfl

/-- **The loop of a call.** `R.Loop I x a a' n h`: the call `x`, from accumulator `a`, evaluates
its remaining children with `n` nodes in total and ends with accumulator `a'`, using at most `h`
stack levels above its own frame. Every frame pushed, child evaluated and value returned
satisfies `I`. -/
inductive Loop (I : Invariant X A Y) : X → A → A → ℕ → ℕ → Prop
  /-- The call has no further child. -/
  | done {x : X} {a : A} : R.next x a = none → Loop I x a a 0 0
  /-- The next child is a leaf. -/
  | leaf {x c : X} {a a' : A} {n h : ℕ} : I.frame x a → R.next x a = some c → I.node c →
      R.isLeaf c = true → I.value (R.leaf c) → Loop I x (R.absorb x a (R.leaf c)) a' n h →
      Loop I x a a' (n + 1) h
  /-- The next child is a call, whose own loop ends with accumulator `b`. -/
  | call {x c : X} {a b a' : A} {n₁ h₁ n₂ h₂ : ℕ} : I.frame x a → R.next x a = some c →
      I.node c → R.isLeaf c = false → Loop I c (R.start c) b n₁ h₁ → I.value (R.finish c b) →
      Loop I x (R.absorb x a (R.finish c b)) a' n₂ h₂ →
      Loop I x a a' (n₁ + 1 + n₂) (max (h₁ + 1) h₂)

/-- **A derivation of the value of a node.** `R.Eval I x y n h`: the node `x` has value `y`,
computed with `n` nodes and at most `h` open calls, and every node, frame and value met satisfies
`I`. A leaf has one node and no open call; a call has one more node and one more level than its
loop. -/
def Eval (I : Invariant X A Y) (x : X) (y : Y) (n h : ℕ) : Prop :=
  I.node x ∧ I.value y ∧
    ((R.isLeaf x = true ∧ y = R.leaf x ∧ n = 1 ∧ h = 0) ∨
      (R.isLeaf x = false ∧ ∃ b n' h', R.Loop I x (R.start x) b n' h' ∧ y = R.finish x b ∧
        n = n' + 1 ∧ h = h' + 1))

variable {R} {I : Invariant X A Y}

/-- A leaf is evaluated by `leaf`. -/
theorem Eval.leaf {x : X} (hx : I.node x) (hl : R.isLeaf x = true) (hv : I.value (R.leaf x)) :
    R.Eval I x (R.leaf x) 1 0 :=
  ⟨hx, hv, .inl ⟨hl, rfl, rfl, rfl⟩⟩

/-- A call is evaluated by its loop, from `start`, and `finish`. -/
theorem Eval.call {x : X} {b : A} {n h : ℕ} (hx : I.node x) (hl : R.isLeaf x = false)
    (hloop : R.Loop I x (R.start x) b n h) (hv : I.value (R.finish x b)) :
    R.Eval I x (R.finish x b) (n + 1) (h + 1) :=
  ⟨hx, hv, .inr ⟨hl, b, n, h, hloop, rfl, rfl, rfl⟩⟩

/-- **The loop absorbs an evaluated child.** -/
theorem Loop.child {x c : X} {a a' : A} {y : Y} {n₁ h₁ n₂ h₂ : ℕ} (hf : I.frame x a)
    (hn : R.next x a = some c) (hc : R.Eval I c y n₁ h₁)
    (hrest : R.Loop I x (R.absorb x a y) a' n₂ h₂) :
    R.Loop I x a a' (n₁ + n₂) (max h₁ h₂) := by
  obtain ⟨hnode, hval, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := hc
  · simpa [Nat.add_comm] using Loop.leaf hf hn hnode hl hval hrest
  · exact Loop.call hf hn hnode hl hloop hval hrest

/-- Every derivation has at least one node. -/
theorem Eval.one_le {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) : 1 ≤ n := by
  obtain ⟨-, -, ⟨-, -, rfl, -⟩ | ⟨-, -, -, -, -, -, rfl, -⟩⟩ := he <;> omega

/-! ### The machine follows the derivation -/

/-- **A loop is run in two steps per node**, ending with the value of the call returned to the
stack below it. -/
theorem Loop.run {x : X} {a a' : A} {n h : ℕ} (hl : R.Loop I x a a' n h) (st : List (X × A)) :
    R.step^[2 * n] (R.resume x a st) = (st, none, some (R.finish x a')) := by
  induction hl generalizing st with
  | done hn => exact R.resume_of_next_none st hn
  | @leaf x c a a' n h _ hn _ hl _ _ ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    rw [R.resume_of_next_some st hn, R.step_leaf _ _ hl, R.step_return, ih]
  | @call x c a b a' n₁ h₁ n₂ h₂ _ hn _ hl _ _ _ ih₁ ih₂ =>
    rw [show 2 * (n₁ + 1 + n₂) = 2 * n₂ + 1 + 2 * n₁ + 1 by ring]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    rw [R.resume_of_next_some st hn, R.step_call _ _ hl, ih₁, R.step_return, ih₂]

/-- **A node with `n` nodes is evaluated in `2 * n - 1` steps**, above any stack. -/
theorem Eval.run {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) (st : List (X × A)) :
    R.step^[2 * n - 1] (st, some x, none) = (st, none, some y) := by
  obtain ⟨-, -, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := he
  · exact R.step_leaf st none hl
  · rw [show 2 * (n' + 1) - 1 = 2 * n' + 1 by omega, Function.iterate_add_apply,
      Function.iterate_one, R.step_call _ _ hl, hloop.run]

/-! ### The states met -/

/-- A state is *good* for `I` and a depth `H` when at most `H` calls are open, every open frame
satisfies `I`, and the register holds either a pending node or a returned value satisfying
`I`. -/
def Good (I : Invariant X A Y) (H : ℕ) (σ : State X A Y) : Prop :=
  σ.1.length ≤ H ∧ (∀ f ∈ σ.1, I.frame f.1 f.2) ∧
    ((∃ x, σ.2 = (some x, none) ∧ I.node x) ∨ (∃ y, σ.2 = (none, some y) ∧ I.value y))

theorem Good.mono {H H' : ℕ} {σ : State X A Y} (hσ : Good I H σ) (h : H ≤ H') : Good I H' σ :=
  ⟨hσ.1.trans h, hσ.2⟩

private theorem good_push {x : X} {a : A} {st : List (X × A)} {H : ℕ} {r : Option X × Option Y}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) (hf : I.frame x a) (hH : st.length + 1 ≤ H)
    (hr : (∃ x, r = (some x, none) ∧ I.node x) ∨ (∃ y, r = (none, some y) ∧ I.value y)) :
    Good I H ((x, a) :: st, r) := by
  refine ⟨by simpa using hH, ?_, hr⟩
  intro f hf'
  rcases List.mem_cons.mp hf' with rfl | hf'
  · exact hf
  · exact hst f hf'

/-- **The states of a loop are good**, strictly before it returns. -/
theorem Loop.good {x : X} {a a' : A} {n h : ℕ} (hl : R.Loop I x a a' n h) {st : List (X × A)}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) :
    ∀ j < 2 * n, Good I (st.length + h + 1) (R.step^[j] (R.resume x a st)) := by
  induction hl generalizing st with
  | done _ => intro j hj; omega
  | @leaf x c a a' n h hf hn hc hl hv _ ih =>
    intro j hj
    rw [R.resume_of_next_some st hn]
    rcases j with _ | _ | j
    · exact good_push hst hf (by omega) (.inl ⟨c, rfl, hc⟩)
    · rw [Function.iterate_one, R.step_leaf _ _ hl]
      exact good_push hst hf (by omega) (.inr ⟨_, rfl, hv⟩)
    · rw [show j + 1 + 1 = j + 2 by ring, Function.iterate_add_apply,
        show R.step^[2] ((x, a) :: st, some c, none) = R.resume x (R.absorb x a (R.leaf c)) st by
          simp only [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply,
            Function.iterate_one]
          rw [R.step_leaf _ _ hl, R.step_return]]
      exact ih hst j (by omega)
  | @call x c a b a' n₁ h₁ n₂ h₂ hf hn hc hl hloop₁ hv _ ih₁ ih₂ =>
    intro j hj
    rw [R.resume_of_next_some st hn]
    have hst' : ∀ f ∈ (x, a) :: st, I.frame f.1 f.2 := fun f hf' => by
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hf
      · exact hst f hf'
    have hbegin : R.step^[1] ((x, a) :: st, some c, none) = R.resume c (R.start c) ((x, a) :: st) :=
      by rw [Function.iterate_one, R.step_call _ _ hl]
    rcases j with _ | j
    · exact good_push hst hf (by omega) (.inl ⟨c, rfl, hc⟩)
    rcases Nat.lt_or_ge j (2 * n₁) with hj₁ | hj₁
    · rw [show j + 1 = j + 1 from rfl, Function.iterate_add_apply, hbegin]
      exact (ih₁ hst' j hj₁).mono (by simp only [List.length_cons]; omega)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj₁
    rw [show 2 * n₁ + k + 1 = k + 2 * n₁ + 1 by ring, Function.iterate_add_apply,
      Function.iterate_add_apply, hbegin, hloop₁.run]
    rcases k with _ | k
    · exact good_push hst hf (by omega) (.inr ⟨_, rfl, hv⟩)
    · rw [show k + 1 = k + 1 from rfl, Function.iterate_add_apply, Function.iterate_one,
        R.step_return]
      exact (ih₂ hst k (by omega)).mono (by omega)

/-- **The states of an evaluation are good**, up to and including its returned value. -/
theorem Eval.good {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) {st : List (X × A)}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) :
    ∀ j ≤ 2 * n - 1, Good I (st.length + h) (R.step^[j] (st, some x, none)) := by
  obtain ⟨hx, hy, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := he
  · intro j hj
    rcases j with _ | j
    · exact ⟨by simp, hst, .inl ⟨x, rfl, hx⟩⟩
    · rw [show j = 0 by omega, Function.iterate_one, R.step_leaf _ _ hl]
      exact ⟨by simp, hst, .inr ⟨_, rfl, hy⟩⟩
  · intro j hj
    rcases j with _ | j
    · exact ⟨by simp, hst, .inl ⟨x, rfl, hx⟩⟩
    rw [Function.iterate_add_apply, Function.iterate_one, R.step_call _ _ hl]
    rcases Nat.lt_or_ge j (2 * n') with hj' | hj'
    · exact (hloop.good hst j hj').mono (by omega)
    · rw [show j = 2 * n' by omega, hloop.run]
      exact ⟨by simp, hst, .inr ⟨_, rfl, hy⟩⟩

/-- **Every state of a run from an empty stack is good**, including the final state, which no
step changes. -/
theorem Eval.good_iterate {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) (j : ℕ) :
    Good I h (R.step^[j] ([], some x, none)) := by
  rcases le_or_gt j (2 * n - 1) with hj | hj
  · simpa using he.good (st := []) (by simp) j hj
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
    rw [show 2 * n - 1 + k + 1 = (k + 1) + (2 * n - 1) by omega, Function.iterate_add_apply,
      he.run, Function.iterate_fixed (R.step_final y)]
    exact ⟨by simp, by simp, .inr ⟨y, rfl, he.2.1⟩⟩

/-! ### The native machine -/

section Native

variable (R) {encX : X ↪ List Bool} {encA : A ↪ List Bool} {encY : Y ↪ List Bool}

/-- The encoding of a machine state: the list of open frames, each a pair, then the optional
pending node and the optional returned value. -/
abbrev encState (encX : X ↪ List Bool) (encA : A ↪ List Bool) (encY : Y ↪ List Bool) :
    State X A Y ↪ List Bool :=
  encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY))

/-- **The polynomial-time components** of a scheme: everything but the leaf step. -/
structure PolyTime (encX : X ↪ List Bool) (encA : A ↪ List Bool) (encY : Y ↪ List Bool) :
    Prop where
  /-- The leaf test. -/
  isLeaf : ComputableInPolyTime R.isLeaf encX encBool
  /-- The initial accumulator. -/
  start : ComputableInPolyTime R.start encX encA
  /-- Child generation. -/
  next : ComputableInPolyTime (fun p : X × A => R.next p.1 p.2) (encPair encX encA)
    (encOption encX)
  /-- Absorbing a child's value. -/
  absorb : ComputableInPolyTime (fun p : (X × A) × Y => R.absorb p.1.1 p.1.2 p.2)
    (encPair (encPair encX encA) encY) encA
  /-- The value of a call. -/
  finish : ComputableInPolyTime (fun p : X × A => R.finish p.1 p.2) (encPair encX encA) encY

/-- Whether the register holds a pending leaf. -/
def isLeafCall (σ : State X A Y) : Bool := σ.2.1.elim false R.isLeaf

/-- Evaluate a pending node as a leaf, keeping the stack. -/
def leafStep (σ : State X A Y) : State X A Y :=
  (σ.1, none, σ.2.1.elim none fun x => some (R.leaf x))

/-- Every step but the evaluation of a leaf. -/
def polyStep (σ : State X A Y) : State X A Y :=
  σ.2.1.elim
    (σ.2.2.elim σ fun y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
    (fun x => R.resume x (R.start x) σ.1)

/-- A step evaluates a leaf, or takes a polynomial-time step. -/
theorem step_eq_ite (σ : State X A Y) :
    R.step σ = if R.isLeafCall σ then R.leafStep σ else R.polyStep σ := by
  rcases σ with ⟨_ | ⟨⟨x, a⟩, st⟩, _ | c, _ | y⟩ <;>
    simp only [step, isLeafCall, leafStep, polyStep, Option.elim, List.head?, List.tail,
      Bool.false_eq_true, ite_false] <;> rfl

variable {R}

/-- Continuing a call is polynomial-time. -/
theorem resume_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime (fun q : (X × A) × List (X × A) => R.resume q.1.1 q.1.2 q.2)
      (encPair (encPair encX encA) (encList (encPair encX encA))) (encState encX encA encY) := by
  have hfr := ComputableInPolyTime.fst (encPair encX encA) (encList (encPair encX encA))
  have hst := ComputableInPolyTime.snd (encPair encX encA) (encList (encPair encX encA))
  have hfallback : ComputableInPolyTime
      (fun q : (X × A) × List (X × A) => (q.2, (none : Option X), some (R.finish q.1.1 q.1.2)))
      (encPair (encPair encX encA) (encList (encPair encX encA))) (encState encX encA encY) :=
    hst.prod ((ComputableInPolyTime.const none).prod
      ((ComputableInPolyTime.optionSome encY).comp (h.finish.comp hfr)))
  have hbody : ComputableInPolyTime
      (fun p : ((X × A) × List (X × A)) × X => (p.1.1 :: p.1.2, some p.2, (none : Option Y)))
      (encPair (encPair (encPair encX encA) (encList (encPair encX encA))) encX)
      (encState encX encA encY) := by
    have hq := ComputableInPolyTime.fst
      (encPair (encPair encX encA) (encList (encPair encX encA))) encX
    have hc := ComputableInPolyTime.snd
      (encPair (encPair encX encA) (encList (encPair encX encA))) encX
    exact (ComputableInPolyTime.cons' (hfr.comp hq) (hst.comp hq)).prod
      (((ComputableInPolyTime.optionSome encX).comp hc).prod (ComputableInPolyTime.const none))
  have helim := ComputableInPolyTime.optionElimWithInput
    (value := fun q : (X × A) × List (X × A) => R.next q.1.1 q.1.2)
    (fallback := fun q => (q.2, (none : Option X), some (R.finish q.1.1 q.1.2)))
    (body := fun q c => (q.1 :: q.2, some c, (none : Option Y))) (h.next.comp hfr) hfallback hbody
  refine helim.of_enc_eq fun q => ?_
  rcases q with ⟨⟨x, a⟩, st⟩
  change encState encX encA encY (R.resume x a st) =
    encState encX encA encY ((R.next x a).elim (st, none, some (R.finish x a))
      fun c => ((x, a) :: st, some c, none))
  rw [resume]
  cases R.next x a <;> rfl

/-- The leaf test on the register is polynomial-time. -/
theorem isLeafCall_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime R.isLeafCall (encState encX encA encY) encBool := by
  have hreg := (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp
    (ComputableInPolyTime.snd (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY)))
  exact ComputableInPolyTime.optionElimWithInput (body := fun _ x => R.isLeaf x) hreg
    (ComputableInPolyTime.const false)
    (h.isLeaf.comp (ComputableInPolyTime.snd (encState encX encA encY) encX))

/-- Every step but the evaluation of a leaf is polynomial-time. -/
theorem polyStep_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime R.polyStep (encState encX encA encY) (encState encX encA encY) := by
  have hstack : ComputableInPolyTime (fun σ : State X A Y => σ.1) (encState encX encA encY)
      (encList (encPair encX encA)) :=
    ComputableInPolyTime.fst (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY))
  have hreg : ComputableInPolyTime (fun σ : State X A Y => σ.2) (encState encX encA encY)
      (encPair (encOption encX) (encOption encY)) :=
    ComputableInPolyTime.snd (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY))
  have hpend : ComputableInPolyTime (fun σ : State X A Y => σ.2.1) (encState encX encA encY)
      (encOption encX) := (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp hreg
  have hret : ComputableInPolyTime (fun σ : State X A Y => σ.2.2) (encState encX encA encY)
      (encOption encY) := (ComputableInPolyTime.snd (encOption encX) (encOption encY)).comp hreg
  -- A returned value is absorbed by the innermost open frame.
  have hframe : ComputableInPolyTime
      (fun q : (State X A Y × Y) × (X × A) =>
        R.resume q.2.1 (R.absorb q.2.1 q.2.2 q.1.2) q.1.1.1.tail)
      (encPair (encPair (encState encX encA encY) encY) (encPair encX encA))
      (encState encX encA encY) := by
    have hq := ComputableInPolyTime.fst (encPair (encState encX encA encY) encY)
      (encPair encX encA)
    have hf := ComputableInPolyTime.snd (encPair (encState encX encA encY) encY)
      (encPair encX encA)
    have hy := (ComputableInPolyTime.snd (encState encX encA encY) encY).comp hq
    have hσ := (ComputableInPolyTime.fst (encState encX encA encY) encY).comp hq
    have habs := h.absorb.comp (hf.prod hy)
    exact (resume_polyTime h).comp
      ((((ComputableInPolyTime.fst encX encA).comp hf).prod habs).prod
        ((ComputableInPolyTime.tail (encA := encPair encX encA)).comp (hstack.comp hσ)))
  have hreturn : ComputableInPolyTime
      (fun p : State X A Y × Y =>
        p.1.1.head?.elim p.1 fun f => R.resume f.1 (R.absorb f.1 f.2 p.2) p.1.1.tail)
      (encPair (encState encX encA encY) encY) (encState encX encA encY) := by
    have hσ := ComputableInPolyTime.fst (encState encX encA encY) encY
    have hhead : ComputableInPolyTime (fun p : State X A Y × Y => p.1.1.head?)
        (encPair (encState encX encA encY) encY) (encOption (encPair encX encA)) :=
      (ComputableInPolyTime.head? (encPair encX encA) (encL := encList (encPair encX encA))).comp
        (hstack.comp hσ)
    exact ComputableInPolyTime.optionElimWithInput
      (value := fun p : State X A Y × Y => p.1.1.head?) (fallback := fun p => p.1)
      (body := fun p f => R.resume f.1 (R.absorb f.1 f.2 p.2) p.1.1.tail) hhead hσ hframe
  have hnoCall : ComputableInPolyTime
      (fun σ : State X A Y =>
        σ.2.2.elim σ fun y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
      (encState encX encA encY) (encState encX encA encY) :=
    ComputableInPolyTime.optionElimWithInput (value := fun σ : State X A Y => σ.2.2)
      (fallback := fun σ => σ)
      (body := fun σ y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
      hret ComputableInPolyTime.id' hreturn
  have hcall : ComputableInPolyTime
      (fun p : State X A Y × X => R.resume p.2 (R.start p.2) p.1.1)
      (encPair (encState encX encA encY) encX) (encState encX encA encY) := by
    have hx : ComputableInPolyTime (fun p : State X A Y × X => p.2)
        (encPair (encState encX encA encY) encX) encX :=
      ComputableInPolyTime.snd (encState encX encA encY) encX
    have hst : ComputableInPolyTime (fun p : State X A Y × X => p.1.1)
        (encPair (encState encX encA encY) encX) (encList (encPair encX encA)) :=
      hstack.comp (ComputableInPolyTime.fst (encState encX encA encY) encX)
    exact (resume_polyTime h).comp ((hx.prod (h.start.comp hx)).prod hst)
  exact ComputableInPolyTime.optionElimWithInput (value := fun σ : State X A Y => σ.2.1)
    (fallback := fun σ => σ.2.2.elim σ fun y =>
      σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
    (body := fun σ x => R.resume x (R.start x) σ.1) hpend hnoCall hcall

end Native

section Certificate

variable {encX : X ↪ List Bool} {encA : A ↪ List Bool} {encY : Y ↪ List Bool}

theorem stack_polyTime :
    ComputableInPolyTime (fun σ : State X A Y => σ.1) (encState encX encA encY)
      (encList (encPair encX encA)) :=
  ComputableInPolyTime.fst _ _

theorem pending_polyTime :
    ComputableInPolyTime (fun σ : State X A Y => σ.2.1) (encState encX encA encY)
      (encOption encX) :=
  (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp (ComputableInPolyTime.snd _ _)

variable (R) in
/-- **The leaf step**: the leaf certificate on the pending node, keeping the stack. -/
noncomputable def leafStepCertificate (leaf : NativeCertificate R.leaf encX encY) :
    NativeCertificate R.leafStep (encState encX encA encY) (encState encX encA encY) :=
  (NativeCertificate.ofPolyTime stack_polyTime).prod ((NativeCertificate.const none).prod
    (NativeCertificate.option (value := fun σ : State X A Y => σ.2.1) (fallback := fun _ => none)
      (body := fun p : State X A Y × X => some (R.leaf p.2))
      (NativeCertificate.ofPolyTime pending_polyTime) (NativeCertificate.const none)
      (NativeCertificate.some (leaf.comp (NativeCertificate.payload _ encX)))))

/-- **One step of the machine**: the leaf certificate on a pending leaf, and a polynomial-time
step otherwise. -/
noncomputable def stepCertificate (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    NativeCertificate R.step (encState encX encA encY) (encState encX encA encY) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (isLeafCall_polyTime h))
    (leafStepCertificate R leaf) (NativeCertificate.ofPolyTime (polyStep_polyTime h))).congr
    fun σ => (R.step_eq_ite σ).symm

theorem stepCertificate_time (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) (σ : State X A Y) :
    (stepCertificate h leaf).time σ =
      (NativeCertificate.ofPolyTime (isLeafCall_polyTime h)).time σ +
      if R.isLeafCall σ then (leafStepCertificate R (encA := encA) leaf).time σ
      else (NativeCertificate.ofPolyTime (polyStep_polyTime h)).time σ := rfl

theorem stepCertificate_space (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) (σ : State X A Y) :
    (stepCertificate h leaf).space σ =
      (NativeCertificate.ofPolyTime (isLeafCall_polyTime h)).space σ +
      if R.isLeafCall σ then (leafStepCertificate R (encA := encA) leaf).space σ
      else (NativeCertificate.ofPolyTime (polyStep_polyTime h)).space σ := rfl

theorem leafStepCertificate_time (leaf : NativeCertificate R.leaf encX encY) (st : List (X × A))
    (x : X) (v : Option Y) :
    (leafStepCertificate R (encA := encA) leaf).time (st, some x, v) =
      (NativeCertificate.ofPolyTime (stack_polyTime (encX := encX) (encA := encA)
        (encY := encY))).time (st, some x, v) +
        ((encState encX encA encY (st, some x, v)).length +
          (2 * (NativeCertificate.ofPolyTime (pending_polyTime (encX := encX) (encA := encA)
            (encY := encY))).time (st, some x, v) +
            (encState encX encA encY (st, some x, v)).length +
            ((encPair (encState encX encA encY) encX ((st, some x, v), x)).length +
              leaf.time x))) := rfl

theorem leafStepCertificate_space (leaf : NativeCertificate R.leaf encX encY)
    (st : List (X × A)) (x : X) (v : Option Y) :
    (leafStepCertificate R (encA := encA) leaf).space (st, some x, v) =
      (NativeCertificate.ofPolyTime (stack_polyTime (encX := encX) (encA := encA)
        (encY := encY))).space (st, some x, v) +
        ((encState encX encA encY (st, some x, v)).length +
          (2 * (NativeCertificate.ofPolyTime (pending_polyTime (encX := encX) (encA := encA)
            (encY := encY))).space (st, some x, v) +
            (encState encX encA encY (st, some x, v)).length +
            ((encPair (encState encX encA encY) encX ((st, some x, v), x)).length +
              leaf.space x))) := rfl

variable (R) in
/-- The leaf cost of a state: the leaf certificate's bound at a pending leaf, and zero
otherwise. -/
def leafCost (cost : X → ℕ) (σ : State X A Y) : ℕ :=
  σ.2.1.elim 0 fun x => if R.isLeaf x then cost x else 0

private theorem length_pending_le {σ : State X A Y} {x : X} (hx : σ.2.1 = some x) :
    (encX x).length ≤ (encState encX encA encY σ).length := by
  rcases σ with ⟨st, r, v⟩
  simp only at hx
  subst hx
  simp only [length_encPair, encOption_some, List.length_cons]
  omega

/-- **The cost of one step**: a polynomial in the state length, plus the leaf certificate at a
pending leaf. -/
theorem exists_stepCertificate_le (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    ∃ K : ℕ, ∀ σ : State X A Y,
      (stepCertificate h leaf).time σ ≤
          K * ((encState encX encA encY σ).length + 1) ^ K + R.leafCost leaf.time σ ∧
        (stepCertificate h leaf).space σ ≤
          K * ((encState encX encA encY σ).length + 1) ^ K + R.leafCost leaf.space σ := by
  have ht := NativeCertificate.ofPolyTime_isPolynomial (isLeafCall_polyTime h)
  have hp := NativeCertificate.ofPolyTime_isPolynomial (polyStep_polyTime h)
  have hs := NativeCertificate.ofPolyTime_isPolynomial (stack_polyTime (encX := encX)
    (encA := encA) (encY := encY))
  have hc := NativeCertificate.ofPolyTime_isPolynomial (pending_polyTime (encX := encX)
    (encA := encA) (encY := encY))
  -- Everything but the leaf certificate is polynomial in the state length.
  have hT := ((((ht.1.add hp.1).add hs.1).add ((PolyBounded.const 2).mul hc.1)).add
    ((PolyBounded.const 6).mul PolyBounded.self)).add (PolyBounded.const 1)
  have hS := ((((ht.2.add hp.2).add hs.2).add ((PolyBounded.const 2).mul hc.2)).add
    ((PolyBounded.const 6).mul PolyBounded.self)).add (PolyBounded.const 1)
  obtain ⟨cT, dT, hcT⟩ := hT.exists_le
  obtain ⟨cS, dS, hcS⟩ := hS.exists_le
  refine ⟨cT + cS + dT + dS, fun σ => ?_⟩
  have hmono {c d : ℕ} (hc : c ≤ cT + cS + dT + dS) (hd : d ≤ cT + cS + dT + dS) :
      c * ((encState encX encA encY σ).length + 1) ^ d ≤
        (cT + cS + dT + dS) * ((encState encX encA encY σ).length + 1) ^ (cT + cS + dT + dS) :=
    Nat.mul_le_mul hc (Nat.pow_le_pow_right (Nat.succ_pos _) hd)
  have hT' := (hcT σ).trans (hmono (by omega) (by omega))
  have hS' := (hcS σ).trans (hmono (by omega) (by omega))
  rcases σ with ⟨st, _ | x, v⟩
  · rw [stepCertificate_time, stepCertificate_space]
    simp only [leafCost, isLeafCall, Option.elim, Bool.false_eq_true, ite_false, Nat.add_zero]
    constructor <;> omega
  · have hx := length_pending_le (encX := encX) (encA := encA) (encY := encY)
      (σ := (st, some x, v)) rfl
    rw [stepCertificate_time, stepCertificate_space]
    by_cases hl : R.isLeaf x = true
    · simp only [leafCost, isLeafCall, Option.elim, hl, ite_true]
      have hpair := length_encPair (enc₁ := encState encX encA encY) (enc₂ := encX)
        ((st, some x, v), x)
      dsimp only at hpair
      rw [leafStepCertificate_time, leafStepCertificate_space]
      constructor <;> omega
    · simp only [Bool.not_eq_true] at hl
      simp only [leafCost, isLeafCall, Option.elim, hl, Bool.false_eq_true, ite_false,
        Nat.add_zero]
      constructor <;> omega

variable (R) in
/-- **The clocked run**: the register after `fuel a` steps from the root `root a` on an empty
stack. -/
def run {I : Type} (fuel : I → ℕ) (root : I → X) (a : I) : Option Y :=
  (R.step^[fuel a] ([], some (root a), none)).2.2

/-- **Enough fuel gives the value.** -/
theorem run_eq_some {I : Type} {fuel : I → ℕ} {root : I → X} {Inv : Invariant X A Y} {a : I}
    {y : Y} {N H : ℕ} (he : R.Eval Inv (root a) y N H) (hfuel : 2 * N - 1 ≤ fuel a) :
    R.run fuel root a = some y := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
  rw [run, hk, Nat.add_comm, Function.iterate_add_apply, he.run,
    Function.iterate_fixed (R.step_final y)]

/-- **The native machine** for the clocked run: one fixed machine, from native certificates for
the fuel and the root. -/
noncomputable def certificate (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) {I : Type} {encIn : I ↪ List Bool}
    {fuel : I → ℕ} {root : I → X} (cn : NativeCertificate fuel encIn encNat)
    (croot : NativeCertificate root encIn encX) :
    NativeCertificate (R.run fuel root) encIn (encOption encY) :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.iterate cn
    ((NativeCertificate.const ([] : List (X × A))).prod
      ((NativeCertificate.some croot).prod (NativeCertificate.const (none : Option Y))))
    (stepCertificate h leaf)))

/-- A good state is at most `5 (H + 1) (F + 1)` long when the nodes, frames and values it holds
are at most `F` long. -/
theorem length_encState_le {Inv : Invariant X A Y} {H F : ℕ} {σ : State X A Y}
    (hσ : Good Inv H σ) (hnode : ∀ x, Inv.node x → (encX x).length ≤ F)
    (hframe : ∀ x a, Inv.frame x a → (encPair encX encA (x, a)).length ≤ F)
    (hvalue : ∀ y, Inv.value y → (encY y).length ≤ F) :
    (encState encX encA encY σ).length ≤ 5 * (H + 1) * (F + 1) := by
  obtain ⟨hlen, hfr, hreg⟩ := hσ
  have hstack : (encList (encPair encX encA) σ.1).length ≤ H * (2 * F + 1) := by
    rw [length_encList]
    calc (σ.1.map fun f => 2 * (encPair encX encA f).length + 1).sum
        ≤ (σ.1.map fun f => 2 * (encPair encX encA f).length + 1).length • (2 * F + 1) :=
          List.sum_le_length_nsmul _ _ fun n hn => by
            obtain ⟨⟨x, a⟩, hf, rfl⟩ := List.mem_map.mp hn
            have := hframe x a (hfr _ hf)
            omega
      _ ≤ H * (2 * F + 1) := by
          rw [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hlen
  have hHF : H * (2 * F + 1) ≤ 2 * H * F + H := by rw [Nat.mul_add, Nat.mul_one]; ring_nf; omega
  rcases σ with ⟨st, r, v⟩
  rcases hreg with ⟨x, hr, hx⟩ | ⟨y, hr, hy⟩ <;> simp only [Prod.mk.injEq] at hr <;>
    obtain ⟨rfl, rfl⟩ := hr
  · have := hnode x hx
    simp only [length_encPair, encOption_some, encOption_none, List.length_cons,
      List.length_nil] at hstack ⊢
    nlinarith
  · have := hvalue y hy
    simp only [length_encPair, encOption_some, encOption_none, List.length_cons,
      List.length_nil] at hstack ⊢
    nlinarith

private theorem pow_absorb (K₀ z : ℕ) (hz : 1 ≤ z) :
    K₀ * (5 * z + 1) ^ K₀ + 5 * z ≤ (K₀ * 6 ^ K₀ + K₀ + 6) * z ^ (K₀ * 6 ^ K₀ + K₀ + 6) := by
  set K := K₀ * 6 ^ K₀ + K₀ + 6
  have h6 : (5 * z + 1) ^ K₀ ≤ 6 ^ K₀ * z ^ K := by
    calc (5 * z + 1) ^ K₀ ≤ (6 * z) ^ K₀ := Nat.pow_le_pow_left (by omega) _
      _ = 6 ^ K₀ * z ^ K₀ := Nat.mul_pow _ _ _
      _ ≤ 6 ^ K₀ * z ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (by omega))
  have hz' : z ≤ z ^ K := by
    calc z = z ^ 1 := (pow_one z).symm
      _ ≤ z ^ K := Nat.pow_le_pow_right hz (by omega)
  calc K₀ * (5 * z + 1) ^ K₀ + 5 * z ≤ K₀ * (6 ^ K₀ * z ^ K) + 5 * z ^ K :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h6) (Nat.mul_le_mul_left _ hz')
    _ = (K₀ * 6 ^ K₀ + 5) * z ^ K := by ring
    _ ≤ K * z ^ K := Nat.mul_le_mul_right _ (by omega)

/-- **The resources of the native machine.** There is one constant `K` such that, for any fuel
and root certificates, if the root has a derivation with `N` nodes and at most `H` open calls
whose nodes, frames and values are at most `F` long, and whose leaves are evaluated by the leaf
certificate within time `TL` and space `SL`, then the time is at most the cost of the fuel and the
root plus `fuel + 1` times `K ((H + 1) (F + 1)) ^ K + TL` (and the cost of the binary clock), and
the workspace is at most the cost of the fuel and the root plus `K ((H + 1) (F + 1)) ^ K + SL`.
The bounds hold for any fuel; with `2 * N - 1 ≤ fuel` the result is the value
(`run_eq_some`). -/
theorem certificate_le (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    ∃ K : ℕ, ∀ {I : Type} {encIn : I ↪ List Bool} {fuel : I → ℕ} {root : I → X}
      (cn : NativeCertificate fuel encIn encNat) (croot : NativeCertificate root encIn encX)
      (Inv : Invariant X A Y) (F TL SL : ℕ),
      (∀ x, Inv.node x → (encX x).length ≤ F ∧
        (R.isLeaf x = true → leaf.time x ≤ TL ∧ leaf.space x ≤ SL)) →
      (∀ x a, Inv.frame x a → (encPair encX encA (x, a)).length ≤ F) →
      (∀ y, Inv.value y → (encY y).length ≤ F) →
      ∀ (a : I) (y : Y) (N H : ℕ), R.Eval Inv (root a) y N H →
        (certificate h leaf cn croot).time a ≤ cn.time a + croot.time a + 2 * (encIn a).length +
            (fuel a + 1) * (K * ((H + 1) * (F + 1)) ^ K + TL +
              ((encNat (fuel a)).length + 1) ^ 2) ∧
          (certificate h leaf cn croot).space a ≤ cn.space a + croot.space a +
            2 * (encIn a).length + K * ((H + 1) * (F + 1)) ^ K + SL +
              (encNat (fuel a)).length := by
  obtain ⟨K₀, hK₀⟩ := exists_stepCertificate_le h leaf
  refine ⟨K₀ * 6 ^ K₀ + K₀ + 6, ?_⟩
  intro I encIn fuel root cn croot Inv F TL SL hnode hframe hvalue a y N H he
  set z := (H + 1) * (F + 1)
  have hz : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have habsorb := pow_absorb K₀ z hz
  -- Every state of the run is good, hence short, and pays the leaf bound only at a leaf.
  have hgood := he.good_iterate (R := R)
  have hlen (j : ℕ) : (encState encX encA encY (R.step^[j] ([], some (root a), none))).length ≤
      5 * z := by
    have := length_encState_le (hgood j) (fun x hx => (hnode x hx).1) hframe hvalue
    rwa [Nat.mul_assoc] at this
  clear_value z
  have hcost (cost : X → ℕ) (B : ℕ)
      (hB : ∀ x, Inv.node x → R.isLeaf x = true → cost x ≤ B) (j : ℕ) :
      R.leafCost cost (R.step^[j] ([], some (root a), none)) ≤ B := by
    obtain ⟨-, -, ⟨x, hr, hx⟩ | ⟨y', hr, -⟩⟩ := hgood j <;> simp only [leafCost, hr, Option.elim]
    · split_ifs with hl
      · exact hB x hx hl
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hround (j : ℕ) :
      (stepCertificate h leaf).time (R.step^[j] ([], some (root a), none)) ≤
          K₀ * (5 * z + 1) ^ K₀ + TL ∧
        (stepCertificate h leaf).space (R.step^[j] ([], some (root a), none)) ≤
          K₀ * (5 * z + 1) ^ K₀ + SL := by
    obtain ⟨ht, hs⟩ := hK₀ (R.step^[j] ([], some (root a), none))
    have hp : K₀ * ((encState encX encA encY (R.step^[j] ([], some (root a), none))).length + 1) ^
        K₀ ≤ K₀ * (5 * z + 1) ^ K₀ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hlen j; omega) _)
    have hct := hcost leaf.time TL (fun x hx hl => ((hnode x hx).2 hl).1) j
    have hcs := hcost leaf.space SL (fun x hx hl => ((hnode x hx).2 hl).2) j
    constructor <;> omega
  have hmaxT := NativeCertificate.maxRoundTime_le (stepCertificate h leaf) (fuel a)
    ([], some (root a), none) (R := K₀ * (5 * z + 1) ^ K₀ + TL) fun j _ => (hround j).1
  have hmaxS := NativeCertificate.maxRoundSpace_le (stepCertificate h leaf) (fuel a)
    ([], some (root a), none) (Q := K₀ * (5 * z + 1) ^ K₀ + SL) fun j _ => (hround j).2
  have hmaxL := NativeCertificate.maxStateLength_le
    (encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY))) R.step
    (fuel a) ([], some (root a), none) (B := 5 * z) fun j _ => hlen j
  simp only [certificate, NativeCertificate.snd_time, NativeCertificate.snd_space,
    NativeCertificate.iterate_time, NativeCertificate.iterate_space,
    NativeCertificate.prod_time, NativeCertificate.prod_space, NativeCertificate.const_time,
    NativeCertificate.const_space, NativeCertificate.some_time, NativeCertificate.some_space]
  constructor
  · have hstep : NativeCertificate.maxRoundTime (stepCertificate h leaf) (fuel a)
        ([], some (root a), none) +
        NativeCertificate.maxStateLength
          (encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY)))
          R.step (fuel a) ([], some (root a), none) + ((encNat (fuel a)).length + 1) ^ 2 ≤
        (K₀ * 6 ^ K₀ + K₀ + 6) * z ^ (K₀ * 6 ^ K₀ + K₀ + 6) + TL +
          ((encNat (fuel a)).length + 1) ^ 2 := by omega
    have := Nat.mul_le_mul_left (fuel a + 1) hstep
    omega
  · omega

end Certificate

end Scheme

end Cslib.GenericRAM.StackRecursion
