/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Configurations
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Radix
public import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Compact configuration graph: local arithmetic

The graph stores no input word. A vertex is a fixed tuple of natural registers packed in a radix
`B`: the input position, control, output summary, and three registers per work tape. Logarithmic
space uses the radix `(n+2)^D` (`Turing.MultiTapeNTM.ConfigurationGraph.radix`); larger space
bounds use larger radices.
An edge consults at most the input bit at `queryIndex`; the supplied symbol is ignored at the
blank boundaries. The transition table is fixed independently of `n`.

Every edge checks both vertex bounds, the semantic tag ranges and successor-register overflow.
The three output tags mean empty, exactly true, and permanently rejecting. In particular, an
emission after either nonempty output tag gives the rejecting tag.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.vertexID`: pack the input-free view.
* `Turing.MultiTapeNTM.ConfigurationGraph.vertexWidth`: the number of bits of a vertex ID.
* `Turing.MultiTapeNTM.ConfigurationGraph.queryIndex`: the only requested input-bit position.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol`: guarded local edge query.
* `Turing.MultiTapeNTM.ConfigurationGraph.bad`: accepting halted vertices.
* `Turing.MultiTapeNTM.ConfigurationGraph.overflow`: vertices whose source step leaves the radix.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

/-- The fixed register names for a machine with `k` tapes. -/
inductive Register (k : ℕ)
  | inputPos | control | output
  | head (i : Fin k) | left (i : Fin k) | right (i : Fin k)
  deriving DecidableEq, Fintype

variable {k : ℕ} {State : Type} [Fintype State]

/-- A fixed finite control tag, including a distinct halting tag. -/
noncomputable def stateCode (q : Option State) : ℕ :=
  (Fintype.equivFin (Option State) q).val

/-- Empty output is zero; the singleton true is one; everything else is rejecting. -/
def outputCode (w : List Bool) : ℕ :=
  if w = [] then 0 else if w = [true] then 1 else 2

/-- Update the acceptance summary on an optional emission. -/
def outputStep (o : ℕ) : Option Bool → ℕ
  | none => o
  | some b => if o = 0 then (if b then 1 else 2) else 2

/-- The fixed tuple of input-free registers of a view. -/
noncomputable def registers (v : FiniteCfg k Bool State) : Register k → ℕ
  | .inputPos => v.inputPos.val
  | .control => stateCode v.state
  | .output => outputCode v.output
  | .head i => symbolCode (v.workTapes i).head
  | .left i => stackCode (v.workTapes i).left
  | .right i => stackCode (v.workTapes i).right

/-- The radix `(n+2)^D` used in logarithmic space, with an exponent fixed with the source machine
and its space constant. -/
def radix (D n : ℕ) : ℕ := (n + 2) ^ D

/-- Number of vertices in the ambient graph of radix `B`, including invalid IDs. -/
def vertexBound (B : ℕ) : ℕ := B ^ Fintype.card (Register k)

variable (k) in
/-- The number of bits of a vertex of the graph of radix `B`: every vertex ID is below
`2 ^ vertexWidth k B`. -/
def vertexWidth (B : ℕ) : ℕ := (vertexBound (k := k) B).size

variable (k) in
/-- Every vertex ID of the graph of radix `B` fits in `vertexWidth k B` bits. -/
theorem vertexBound_lt_two_pow_vertexWidth (B : ℕ) :
    vertexBound (k := k) B < 2 ^ vertexWidth k B :=
  Nat.lt_size_self _

/-- All components fit below the radix. -/
def Fits (B : ℕ) (r : Register k → ℕ) : Prop := ∀ i, r i < B

/-- Packed input-free configuration ID. -/
noncomputable def vertexID (B : ℕ) (v : FiniteCfg k Bool State) : ℕ :=
  Cslib.Radix.pack B (registers v)

/-- Read the registers of an arbitrary ID. -/
noncomputable def readRegisters (B u : ℕ) : Register k → ℕ :=
  Cslib.Radix.component B u

/-- The input bit to request, in the native zero-based word indexing. Boundary requests are
ignored by `inputSymbol`; the right boundary may request the absent bit at `n`. -/
noncomputable def queryIndex (B u : ℕ) : ℕ :=
  readRegisters (k := k) B u .inputPos - 1

/-- Force blank at both boundaries; otherwise use the one externally supplied input symbol. -/
def inputSymbol (n p : ℕ) (symbol : Option Bool) : Option Bool :=
  if p = 0 ∨ p = n + 1 then none else symbol

/-- Clamped movement of the input head, computed on its binary position. -/
def inputMove (n p : ℕ) : SignType → ℕ
  | .neg => p - 1
  | .zero => p
  | .pos => min (p + 1) (n + 1)

/-- Update the fixed register tuple by a fixed native action. -/
noncomputable def nextRegisters (n : ℕ) (r : Register k → ℕ) (a : Action k Bool State) :
    Register k → ℕ
  | .inputPos => inputMove n (r .inputPos) a.inputTape
  | .control => stateCode a.state
  | .output => outputStep (r .output) a.output
  | .head i => (tapeStep (a.workTapes i) (r (.head i), r (.left i), r (.right i))).1
  | .left i => (tapeStep (a.workTapes i) (r (.head i), r (.left i), r (.right i))).2.1
  | .right i => (tapeStep (a.workTapes i) (r (.head i), r (.left i), r (.right i))).2.2

/-- The finite tuple of fields of a native action. -/
def actionEquiv : Action k Bool State ≃
    SignType × (Fin k → Option (Option Bool) × SignType) × Option Bool × Option State where
  toFun a := (a.inputTape, a.workTapes, a.output, a.state)
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨_, _, _, _⟩; rfl

/-- Native actions form a finite type over finite control and a fixed tape count. -/
noncomputable local instance instFintypeActionBool : Fintype (Action k Bool State) :=
  Fintype.ofEquiv _ actionEquiv.symm

/-- One entry in the machine's fixed finite transition table. -/
abbrev Instruction (k : ℕ) (State : Type) :=
  State × Option Bool × (Fin k → Option Bool) × Action k Bool State

/-- The finite table is selected once from the source transition relation. Its selection need
not be uniform in the machine; no runtime input influences this table. -/
noncomputable def instructions (ntm : MultiTapeNTM k Bool State) : List (Instruction k State) := by
  classical
  exact (Finset.univ.filter fun t => ntm.Tr t.1 t.2.1 t.2.2.1 t.2.2.2).toList

theorem mem_instructions (ntm : MultiTapeNTM k Bool State) (t : Instruction k State) :
    t ∈ instructions ntm ↔ ntm.Tr t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  classical
  simp [instructions]

/-- Syntactic validity of an ID. All ternary stack naturals are canonical; only finite tags,
input geometry, and the overall bound require guards. -/
noncomputable def valid (B n u : ℕ) : Bool :=
  let r := readRegisters (k := k) B u
  decide (u < vertexBound (k := k) B) && decide (r .inputPos < n + 2) &&
    decide (r .control < Fintype.card (Option State)) && decide (r .output < 3) &&
    (List.ofFn fun i : Fin k => decide (r (.head i) < 3)).all id

/-- Check that a decoded source has the observations of a fixed table entry. -/
noncomputable def matchesEntry (n : ℕ) (r : Register k → ℕ) (symbol : Option Bool)
    (t : Instruction k State) : Bool :=
  decide (r .control = stateCode (some t.1)) &&
    decide (inputSymbol n (r .inputPos) symbol = t.2.1) &&
    (List.ofFn fun i : Fin k => decide (r (.head i) = symbolCode (t.2.2.1 i))).all id

/-- Guard every successor component against radix overflow. -/
noncomputable def fitsB (B : ℕ) (r : Register k → ℕ) : Bool :=
  (Finset.univ.toList : List (Register k)).all fun i => decide (r i < B)

/-- One actual input read suffices for this edge predicate. The work is arithmetic on the short
stored arguments and a fixed finite transition table. -/
noncomputable def edgeWithSymbol (ntm : MultiTapeNTM k Bool State) (B n u v : ℕ)
    (symbol : Option Bool) : Bool :=
  let r := readRegisters (k := k) B u
  valid (k := k) (State := State) B n u && valid (k := k) (State := State) B n v &&
    ((decide (r .control = stateCode (none : Option State)) && decide (v = u)) ||
      (instructions ntm).any fun t =>
        matchesEntry n r symbol t && fitsB B (nextRegisters n r t.2.2.2) &&
          decide (v = Cslib.Radix.pack B (nextRegisters n r t.2.2.2)))

/-- Accepting halted vertices, the bad set for complement reachability. -/
noncomputable def bad (B n u : ℕ) : Bool :=
  let r := readRegisters (k := k) B u
  valid (k := k) (State := State) B n u && decide (r .control = stateCode (none : Option State)) &&
    decide (r .output = 1)

/-- Vertices with a matching transition whose successor overflows the radix. These are the
represented views from which the source leaves the graph of radix `B`. -/
noncomputable def overflow (ntm : MultiTapeNTM k Bool State) (B n u : ℕ)
    (symbol : Option Bool) : Bool :=
  let r := readRegisters (k := k) B u
  valid (k := k) (State := State) B n u &&
    (instructions ntm).any fun t =>
      matchesEntry n r symbol t && !fitsB B (nextRegisters n r t.2.2.2)

/-- The start vertex depends only on the radix, since initial storage is blank. -/
noncomputable def startID (ntm : MultiTapeNTM k Bool State) (B : ℕ) : ℕ :=
  Cslib.Radix.pack B fun i : Register k => match i with
    | .inputPos => 1
    | .control => stateCode (some ntm.q₀)
    | _ => 0

/-- The graph on an actual input; it reads no other bit than `queryIndex`. -/
def Edge (ntm : MultiTapeNTM k Bool State) (B : ℕ) (w : List Bool)
    (u v : ℕ) : Prop :=
  edgeWithSymbol ntm B w.length u v w[queryIndex (k := k) B u]? = true

/-- The overflow test on an actual input, reading the bit at `queryIndex`. -/
def Overflow (ntm : MultiTapeNTM k Bool State) (B : ℕ) (w : List Bool) (u : ℕ) : Prop :=
  overflow ntm B w.length u w[queryIndex (k := k) B u]? = true

end Turing.MultiTapeNTM.ConfigurationGraph
