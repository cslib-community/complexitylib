/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.Reingold
public import Complexity.Algorithms.Reachability.ReingoldEval
public import Complexity.Computability.Complexity.Problems.USTCON
public import Complexity.Computability.Machines.ReadMachine.Basic
public import Complexity.Foundations.Combinatorics.Expander.AffineFamily

/-!
# A read machine for undirected connectivity

`Cslib.USTCON.Reader.machine` decides undirected `s`–`t` connectivity (`Cslib.Complexity.USTCON`)
on the encodings `Cslib.Complexity.encUSTCON`, reading its input by address
(`Turing.ReadMachine`), following Reingold's algorithm [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09]:

1. it counts the unary header `1^n 0 1^s 0 1^t 0` (`hdrN`, `hdrS`, `hdrT`) and halves `n` until it
   vanishes, adding `16` to the depth and `4168` to the walk length at each halving (`size`), so
   that the depth and the walk length are `Cslib.Reachability.Reingold.depth a` and
   `Cslib.Reachability.Reingold.walkLength a` for `a = Nat.size n`, with `n ≤ 2 ^ a`;
2. for each counter `c = 0, 1, …` it walks in Reingold's graph from the vertex
   `(⋯ ((s, s), 0) ⋯, 0)` (`start`, `fill`) along the labels given by the digits of `c` in base
   `|B| = 257 ^ 8` (`next`), each step evaluating the rotation map in place (`eval`, by
   `Cslib.RotationMap.reingoldEvalStep`) and reading the adjacency matrix at a step of the slot
   graph;
3. it accepts when a walk ends over a slot of `t`, and rejects when the counter has more digits
   than the walk length, all counters having been tried (`check`).

Its memory is a constant number of numbers bounded by a polynomial in `n` or by `|B|` to the power
of the walk length, and two lists of `O(log n)` labels and program counters, so `O(log n)` bits.

## Main definitions

* `Cslib.USTCON.Reader.labelOfNat`: the label of a digit.
* `Cslib.USTCON.Reader.slotRotN`: the rotation map of the regular rotation map of the input graph,
  on the slots as pairs of numbers, given the entry of the adjacency matrix.
* `Cslib.USTCON.Reader.Ctl`, `Cslib.USTCON.Reader.State`: the control and the memory.
* `Cslib.USTCON.Reader.step`, `Cslib.USTCON.Reader.addr`: the step and the address read.
* `Cslib.USTCON.Reader.machine`: the read machine.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Cslib.RotationMap Cslib.Reachability.Reingold

/-- The number of labels, `257 ^ 8`. -/
def numLabels : ℕ := 257 ^ 8

/-- There are labels. -/
theorem numLabels_pos : 0 < numLabels := by
  simp [numLabels]

/-- The number of labels is the cardinality of the label type. -/
theorem card_label_eq_numLabels : Fintype.card Label = numLabels :=
  card_label

/-- The labels numbered by the residues modulo their number. -/
def labelEquiv : Fin numLabels ≃ Label :=
  (affinePlaneTowerBaseNumbering (ZMod.finEquiv 257).toEquiv.symm).symm

/-- The label of the digit `x % numLabels`. -/
def labelOfNat (x : ℕ) : Label :=
  labelEquiv ⟨x % numLabels, Nat.mod_lt _ numLabels_pos⟩

/-- **The rotation map of the regular rotation map of the input graph**, on slots written as pairs
of numbers below `n`, given the entry `bit` of the adjacency matrix at the slot: the edge of the
graph exchanges the ends of an edge if `bit` is set, the edges of the cycle of the slots move to the
next or the previous slot, and every other label is a self-loop. -/
def slotRotN (n : ℕ) (v : ℕ × ℕ) (b : Label) (bit : Bool) : (ℕ × ℕ) × Label :=
  if b = slotLabel (.inl ()) then (if bit then (v.2, v.1) else v, b)
  else if b = slotLabel (.inr ((), (), false)) then
    ((v.1, if v.2 + 1 = n then 0 else v.2 + 1), slotLabel (.inr ((), (), true)))
  else if b = slotLabel (.inr ((), (), true)) then
    ((v.1, if v.2 = 0 then n - 1 else v.2 - 1), slotLabel (.inr ((), (), false)))
  else (v, b)

/-- The control state of the machine. -/
inductive Ctl where
  /-- Counting the ones of the number of vertices. -/
  | hdrN
  /-- Counting the ones of the source. -/
  | hdrS
  /-- Counting the ones of the target. -/
  | hdrT
  /-- Halving the number of vertices, to compute the depth and the walk length. -/
  | size
  /-- Starting the walk of the counter. -/
  | start
  /-- Filling the labels of the start vertex with zeros. -/
  | fill
  /-- Taking the next step of the walk, or ending it. -/
  | next
  /-- Evaluating the rotation map of Reingold's graph. -/
  | eval
  /-- Checking the end of the walk. -/
  | check
  /-- Halted. -/
  | done
  deriving DecidableEq

/-- The memory of the machine. -/
structure State where
  /-- The control state. -/
  ctl : Ctl
  /-- The ones counted in the header, or the number of vertices being halved. -/
  cnt : ℕ
  /-- The number of vertices. -/
  n : ℕ
  /-- The source. -/
  s : ℕ
  /-- The target. -/
  t : ℕ
  /-- The depth of Reingold's graph. -/
  depth : ℕ
  /-- The length of the walks. -/
  len : ℕ
  /-- The counter of the walks. -/
  c : ℕ
  /-- The digits of the counter not yet used. -/
  w : ℕ
  /-- The steps of the walk not yet taken. -/
  j : ℕ
  /-- The state of the evaluation of the rotation map: the slot, the labels and the frames. -/
  ev : ReingoldEvalState (ℕ × ℕ) Label

/-- The step of the evaluation with the entry `bit` of the adjacency matrix. -/
def slotRot (n : ℕ) (bit : Bool) (p : (ℕ × ℕ) × Label) : (ℕ × ℕ) × Label :=
  slotRotN n p.1 p.2 bit

/-- **A step**, given the bit read. -/
def step (q : State) (b : Bool) : State × List Bool :=
  match q.ctl with
  | .hdrN =>
    if b then ({ q with cnt := q.cnt + 1 }, [])
    else ({ q with n := q.cnt, cnt := 0, ctl := .hdrS }, [])
  | .hdrS =>
    if b then ({ q with cnt := q.cnt + 1 }, [])
    else ({ q with s := q.cnt, cnt := 0, ctl := .hdrT }, [])
  | .hdrT =>
    if b then ({ q with cnt := q.cnt + 1 }, [])
    else ({ q with t := q.cnt, cnt := q.n, depth := 524, len := 136240, ctl := .size }, [])
  | .size =>
    if q.cnt = 0 then ({ q with c := 0, ctl := .start }, [])
    else ({ q with cnt := q.cnt / 2, depth := q.depth + 16, len := q.len + 4168 }, [])
  | .start => ({ q with ev := ⟨(q.s, q.s), [], []⟩, w := q.c, j := q.len, ctl := .fill }, [])
  | .fill =>
    if q.ev.lower.length = q.depth then ({ q with ctl := .next }, [])
    else ({ q with ev := { q.ev with lower := 0 :: q.ev.lower } }, [])
  | .next =>
    if q.j = 0 then ({ q with ctl := .check }, [])
    else
      ({ q with
          ev := { q.ev with frames := [(.zig₀, labelOfNat q.w)] }
          w := q.w / numLabels
          j := q.j - 1
          ctl := .eval }, [])
  | .eval =>
    if q.ev.frames = [] then
      ({ q with ev := { q.ev with lower := q.ev.lower.tail }, ctl := .next }, [])
    else ({ q with ev := reingoldEvalStep base baseEquiv (slotRot q.n b) q.ev }, [])
  | .check =>
    if q.w ≠ 0 then ({ q with ctl := .done }, [false])
    else if q.ev.vertex.1 = q.t then ({ q with ctl := .done }, [true])
    else ({ q with c := q.c + 1, ctl := .start }, [])
  | .done => (q, [])

/-- **The address read by a step**: the next bit of the header while counting it, and the entry of
the adjacency matrix at the slot at a step of the slot graph. -/
def addr (q : State) : Option ℕ :=
  match q.ctl with
  | .hdrN => some q.cnt
  | .hdrS => some (q.n + 1 + q.cnt)
  | .hdrT => some (q.n + 1 + q.s + 1 + q.cnt)
  | .eval =>
    if q.ev.atRoot then some (q.n + q.s + q.t + 3 + (q.ev.vertex.1 * q.n + q.ev.vertex.2))
    else none
  | _ => none

/-- The initial state: counting the header. -/
def init : State :=
  ⟨.hdrN, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨(0, 0), [], []⟩⟩

/-- **The read machine for undirected connectivity.** -/
def machine : Turing.ReadMachine State where
  init := init
  halt q := decide (q.ctl = .done)
  addr := addr
  step := step

end Cslib.USTCON.Reader
