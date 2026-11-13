/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Local
public import CslibFrontier.Computability.Circuit.Topology
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Circuit.Program

/-!
# Garbled circuits

A point-and-permute garbling of Boolean circuits over an arbitrary signature, in the style of Yao
[Yao1986] with the point-and-permute technique of Beaver, Micali and Rogaway
[BeaverMicaliRogaway1990], following the garbling-scheme syntax of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012]: garble, encode, evaluate, decode.

Each wire `w` has two labels `(key (w, c), c)`, one for each *colour* `c : Bool`. The colour of
the label carrying bit `b` is `b + perm w`, for a secret permutation bit `perm w`. Labels live in
`K × Bool` for a finite additive group `K` of keys, and a keyed function
`F : K → T → K × Bool` (a PRF in the security analysis) masks the table. Each gate `g` has one
table row for each colour vector `ρ` of its arguments; the row holds the label of the gate's
output for the bits those colours encode, masked by `∑ k, F (key (w_k, ρ k)) (tw (ρ, k))`, where
`w_k` is the `k`-th argument wire and `tw` assigns a tweak to each argument slot of each row. For
binary gates this is a double encryption under the two argument keys. The evaluator holding one
label per argument wire selects the row named by their colours and removes the mask with their
keys; the decoding information is the permutation bit of each output wire.

Correctness (`Garbled.run_garbleWith`) holds for every keyed function `F`, tweak assignment `tw`,
choice of keys and permutation bits, and input. Evaluation follows every wire labelling that is a
fixed point of one evaluation round (`evaluate_eq_of_evalStep`), for every topology whose gates
read only earlier wires, since such a round is local (`isLocal_evalStep`); this also gives
correctness of the simulator. Garbling uses the circuit's
operations only through its truth tables; the table shape depends only on the topology.

## Main definitions

* `Cslib.Crypto.Garbling.Row`, `Cslib.Crypto.Garbling.Slot`: table rows and their argument slots.
* `Cslib.Crypto.Garbling.garbleTable`: the garbled table.
* `Cslib.Crypto.Garbling.Garbled`: table, input encoding and output decoding.
* `Cslib.Crypto.Garbling.garbleWith`, `Cslib.Crypto.Garbling.garble`: garbling with given keys
  and permutation bits, and with uniform ones.
* `Cslib.Crypto.Garbling.evaluate`: the evaluator.

## Main results

* `Cslib.Crypto.Garbling.evaluate_eq_of_evalStep`: evaluation follows any consistent labelling.
* `Cslib.Crypto.Garbling.Garbled.run_garbleWith`,
  `Cslib.Crypto.Garbling.Garbled.run_of_mem_support`: correctness.

## References

* [A. C. Yao, *How to Generate and Exchange Secrets*][Yao1986]
* [D. Beaver, S. Micali, P. Rogaway, *The Round Complexity of Secure
  Protocols*][BeaverMicaliRogaway1990]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Cslib.Circuits

universe v

variable {σ : Signature.{v}} {n m s : ℕ}

/-- A row of a garbled table: a gate together with a colour for each of its arguments. -/
abbrev Row (τ : Circuit.Topology n m s) : Type := Σ g : Fin s, Fin (τ.arity g) → Bool

/-- An argument slot of a table row; each slot has its own tweak. -/
abbrev Slot (τ : Circuit.Topology n m s) : Type := Σ r : Row τ, Fin (τ.arity r.1)

variable {K T : Type}

/-- The input encoding: bit `b` of input `i` is the label of colour `b + perm (input i)`. -/
def inputEncoding {g : ℕ} (key : Wire n g × Bool → K) (perm : Wire n g → Bool) :
    Fin n → Bool → K × Bool :=
  fun i b => (key (.input i, b + perm (.input i)), b + perm (.input i))

/-- The output decoding information: the permutation bit of each output wire. -/
def outputDecoding (C : Circuit σ n m) (perm : Wire n C.size → Bool) : Fin m → Bool :=
  fun o => perm (C.outputs o)

/-- Encode an input with an input encoding. -/
def encode {L : Type} (e : Fin n → Bool → L) (x : Fin n → Bool) : Fin n → L := fun i => e i (x i)

/-- Decode output labels: the output bit is the colour plus the permutation bit. -/
def decode (d : Fin m → Bool) (Y : Fin m → K × Bool) : Fin m → Bool := fun o => (Y o).2 + d o

/-- The plaintext of a row: the label of the gate's output for the input bits that the row's
colours encode. -/
def plainRow (C : Circuit σ n m) (I : Interpretation σ Bool) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (r : Row C.topology) : K × Bool :=
  let b := I (C.program.lines r.1).op fun k => r.2 k + perm ((C.program.lines r.1).wires k)
  (key (.gate r.1, b + perm (.gate r.1)), b + perm (.gate r.1))

/-- A garbled circuit: its table, input encoding and output decoding. -/
structure Garbled (τ : Circuit.Topology n m s) (K : Type) where
  /-- The garbled table. -/
  table : Row τ → K × Bool
  /-- The label of each bit of each input. -/
  encoding : Fin n → Bool → K × Bool
  /-- The permutation bit of each output wire. -/
  decoding : Fin m → Bool

/-- The label of each wire that the evaluator holds on input `x`: the label of colour
`trace w + perm w`. -/
def activeLabel (C : Circuit σ n m) (I : Interpretation σ Bool) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (x : Fin n → Bool) (w : Wire n C.size) : K × Bool :=
  (key (w, C.program.trace I x w + perm w), C.program.trace I x w + perm w)

/-- The row named by the active colours of a gate's arguments holds the gate's active label. -/
theorem plainRow_trace (C : Circuit σ n m) (I : Interpretation σ Bool)
    (key : Wire n C.size × Bool → K) (perm : Wire n C.size → Bool) (x : Fin n → Bool)
    (g : Fin C.size) :
    plainRow C I key perm ⟨g, fun k => (activeLabel C I key perm x (C.topology.wires g k)).2⟩ =
      activeLabel C I key perm x (.gate g) := by
  have hv : (I (C.program.lines g).op fun k =>
      C.program.trace I x ((C.program.lines g).wires k) + perm ((C.program.lines g).wires k) +
        perm ((C.program.lines g).wires k)) = C.program.trace I x (.gate g) := by
    rw [C.program.trace_gate]
    congr 1 with k : 1
    rw [add_assoc, BooleanRing.add_self, add_zero]
  exact congrArg (fun b => (key (.gate g, b + perm (.gate g)), b + perm (.gate g))) hv

variable [AddCommGroup K]

/-- The mask of a row: the sum, over its arguments, of the keyed function at the argument's key
of the row's colour and the slot's tweak. -/
def rowMask (τ : Circuit.Topology n m s) (F : K → T → K × Bool) (tw : Slot τ → T)
    (key : Wire n s × Bool → K) (r : Row τ) : K × Bool :=
  ∑ k, F (key (τ.wires r.1 k, r.2 k)) (tw ⟨r, k⟩)

/-- The garbled table: each row's plaintext plus its mask. -/
def garbleTable (C : Circuit σ n m) (I : Interpretation σ Bool) (F : K → T → K × Bool)
    (tw : Slot C.topology → T) (key : Wire n C.size × Bool → K) (perm : Wire n C.size → Bool) :
    Row C.topology → K × Bool :=
  fun r => plainRow C I key perm r + rowMask C.topology F tw key r

/-- Garble a circuit with the given keys and permutation bits. -/
def garbleWith (C : Circuit σ n m) (I : Interpretation σ Bool) (F : K → T → K × Bool)
    (tw : Slot C.topology → T) (key : Wire n C.size × Bool → K) (perm : Wire n C.size → Bool) :
    Garbled C.topology K where
  table := garbleTable C I F tw key perm
  encoding := inputEncoding key perm
  decoding := outputDecoding C perm

/-- Garble a circuit with uniform keys and permutation bits. -/
noncomputable def garble [Fintype K] [Nonempty K] (C : Circuit σ n m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T) :
    ProbComp (Garbled C.topology K) := do
  let key ← ProbComp.uniform (Wire n C.size × Bool → K)
  let perm ← ProbComp.uniform (Wire n C.size → Bool)
  return garbleWith C I F tw key perm

/-- One round of evaluation: an input reads its label, and a gate reads the row named by the
colours of its arguments' labels and removes the mask with their keys. -/
def evalStep (τ : Circuit.Topology n m s) (F : K → T → K × Bool) (tw : Slot τ → T)
    (table : Row τ → K × Bool) (X : Fin n → K × Bool) (labels : Wire n s → K × Bool) :
    Wire n s → K × Bool
  | .input i => X i
  | .gate g =>
    table ⟨g, fun k => (labels (τ.wires g k)).2⟩ -
      ∑ k, F (labels (τ.wires g k)).1 (tw ⟨⟨g, fun k => (labels (τ.wires g k)).2⟩, k⟩)

/-- Evaluate a garbled table on input labels: `n + s` rounds from the zero labelling, which reach
every wire of an ordered topology, then read the output wires. -/
def evaluate (τ : Circuit.Topology n m s) (F : K → T → K × Bool) (tw : Slot τ → T)
    (table : Row τ → K × Bool) (X : Fin n → K × Bool) : Fin m → K × Bool :=
  fun o => (evalStep τ F tw table X)^[n + s] 0 (τ.outputs o)

/-- Evaluate a garbled circuit on an input and decode the result. -/
def Garbled.run {τ : Circuit.Topology n m s} (G : Garbled τ K) (F : K → T → K × Bool)
    (tw : Slot τ → T) (x : Fin n → Bool) : Fin m → Bool :=
  decode G.decoding (evaluate τ F tw G.table (encode G.encoding x))

/-- On an ordered topology, an evaluation round is local: a gate reads only the labels of its
arguments, which have lower wire numbers. -/
theorem isLocal_evalStep {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered) (F : K → T → K × Bool)
    (tw : Slot τ → T) (table : Row τ → K × Bool) (X : Fin n → K × Bool) :
    IsLocal (evalStep τ F tw table X) := by
  intro A B w h
  cases w with
  | input i => rfl
  | gate g =>
    exact congrArg (fun a : Fin (τ.arity g) → K × Bool =>
      table ⟨g, fun k => (a k).2⟩ - ∑ k, F (a k).1 (tw ⟨⟨g, fun k => (a k).2⟩, k⟩))
      (funext fun k => h _ (hτ g k))

/-- On an ordered topology, evaluation follows every wire labelling `A` that one evaluation
round leaves unchanged: the evaluated output labels are those of `A`. -/
theorem evaluate_eq_of_evalStep {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (F : K → T → K × Bool) (tw : Slot τ → T) (table : Row τ → K × Bool) (X : Fin n → K × Bool)
    (A : Wire n s → K × Bool) (hA : ∀ w, evalStep τ F tw table X A w = A w) :
    evaluate τ F tw table X = A ∘ τ.outputs :=
  funext fun o =>
    congrFun ((isLocal_evalStep hτ F tw table X).iterate_eq_of_isFixed 0 (funext hA)) (τ.outputs o)

/-- Removing the mask with the active labels of the arguments gives the gate's active label. -/
theorem evalStep_activeLabel (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (x : Fin n → Bool) (w : Wire n C.size) :
    evalStep C.topology F tw (garbleTable C I F tw key perm) (encode (inputEncoding key perm) x)
        (activeLabel C I key perm x) w = activeLabel C I key perm x w := by
  cases w with
  | input i => rfl
  | gate g =>
    simp only [evalStep, garbleTable, rowMask]
    rw [← plainRow_trace C I key perm x g]
    exact add_sub_cancel_right _ _

/-- **Correctness**: evaluating a garbled circuit on an encoded input and decoding gives the
circuit's output, for every keyed function, tweak assignment, keys and permutation bits. -/
theorem Garbled.run_garbleWith (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (x : Fin n → Bool) :
    (garbleWith C I F tw key perm).run F tw x = C.eval I x := by
  have h := evaluate_eq_of_evalStep C.isOrdered_topology F tw (garbleTable C I F tw key perm)
    (encode (inputEncoding key perm) x) (activeLabel C I key perm x)
    (evalStep_activeLabel C I F tw key perm x)
  funext o
  simp only [Garbled.run, garbleWith, h, decode, outputDecoding, Function.comp_apply, activeLabel,
    Circuit.eval]
  change C.program.trace I x (C.outputs o) + perm (C.outputs o) + perm (C.outputs o) =
    C.program.trace I x (C.outputs o)
  rw [add_assoc, BooleanRing.add_self, add_zero]

/-- **Correctness** of the randomized garbling: every garbled circuit it can output evaluates
correctly on every input. -/
theorem Garbled.run_of_mem_support [Fintype K] [Nonempty K] (C : Circuit σ n m)
    (I : Interpretation σ Bool) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    {G : Garbled C.topology K} (hG : G ∈ (ProbComp.eval (garble C I F tw)).support)
    (x : Fin n → Bool) : G.run F tw x = C.eval I x := by
  simp only [garble, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hG
  obtain ⟨key, -, perm, -, rfl⟩ := hG
  exact run_garbleWith C I F tw key perm x

end Cslib.Crypto.Garbling
