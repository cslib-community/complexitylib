/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.Basic
public import CslibFrontier.Computability.TreeEval.Encoding
public import CslibFrontier.Computability.TreeEval.Iterative

/-!
# A read machine for Tree Evaluation

The Cook–Mertz procedure as a `Turing.ReadMachine` on the encoding of an instance. Its state holds
natural numbers only, so that one state type serves all instances: the value length, the height
and the prime `p` found at the start, three registers of residues modulo `p`, the stack of frames of
`Cslib.TreeEval.Iter` and a control state.

The machine reads the header, finds the least prime `p ≥ 2ℓ + 2`, and then follows the iterative
procedure over `ZMod p` with the units `1, …, p - 1`, reading the input only at a leaf, bit by bit,
and for the update of a round, in one pass over the table of the gate. That pass accumulates, for
every output bit `i`, the sum of the weights `∏ⱼ χ` of the table entries for `i` that are set,
which is the multilinear extension of output bit `i` at the masked registers. At the end it emits
register `2`.

## Main definitions

* `Cslib.TreeEval.Reader.State`: the states of the machine.
* `Cslib.TreeEval.Reader.machine`: the machine.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Iter

/-! ### Residues -/

/-- The sum modulo `p`. -/
def addMod (p a b : ℕ) : ℕ := (a + b) % p

/-- The product modulo `p`. -/
def mulMod (p a b : ℕ) : ℕ := a * b % p

/-- The negation modulo `p`. -/
def negMod (p a : ℕ) : ℕ := (p - a % p) % p

/-- The `n`-th power modulo `p`, by repeated multiplication. -/
def powMod (p a : ℕ) : ℕ → ℕ
  | 0 => 1 % p
  | n + 1 => mulMod p (powMod p a n) a

/-- The residue of the unit of round `j`. -/
def unitVal (j : ℕ) : ℕ := j + 1

/-- The inverse of the unit of round `j` modulo a prime `p`, by Fermat's little theorem. -/
def unitInv (p j : ℕ) : ℕ := powMod p (j + 1) (p - 2)

/-- The residue of a sign. -/
def sgnVal (p : ℕ) (neg : Bool) : ℕ := if neg then p - 1 else 1

/-- The residue of `x` if `b`, and of `1 - x` otherwise. -/
def chi (p : ℕ) (b : Bool) (x : ℕ) : ℕ := if b then x % p else addMod p 1 (negMod p x)

/-- The weight of the table entries for the inputs indexed by `k` at the masked registers `x` and
`y`: the product of `chi` over the low and the high `ℓ` bits of `k`. -/
def weight (p ℓ k : ℕ) (x y : List ℕ) : ℕ :=
  mulMod p ((List.range ℓ).foldl (fun a j => mulMod p a (chi p (k.testBit j) (x.getD j 0))) (1 % p))
    ((List.range ℓ).foldl (fun a j => mulMod p a (chi p (k.testBit (ℓ + j)) (y.getD j 0))) (1 % p))

/-- Change the element at `i` of a list by `g`. -/
def modifyAt (l : List ℕ) (i : ℕ) (g : ℕ → ℕ) : List ℕ := l.set i (g (l.getD i 0))

/-! ### Registers -/

/-- Three registers of residues. -/
abbrev Regs := List ℕ × List ℕ × List ℕ

/-- Register `r`. -/
def Regs.get (R : Regs) : Fin 3 → List ℕ
  | 0 => R.1
  | 1 => R.2.1
  | 2 => R.2.2

/-- Replace register `r`. -/
def Regs.set (R : Regs) : Fin 3 → List ℕ → Regs
  | 0, l => (l, R.2)
  | 1, l => (R.1, l, R.2.2)
  | 2, l => (R.1, R.2.1, l)

/-- Multiply register `r` by `a` modulo `p`. -/
def Regs.scale (p : ℕ) (r : Fin 3) (a : ℕ) (R : Regs) : Regs :=
  R.set r ((R.get r).map (mulMod p a))

/-! ### The machine -/

/-- The control state. -/
inductive Ctl where
  /-- Reading the value length from the header, `n` ones read so far. -/
  | hdrLength (n : ℕ)
  /-- Reading the height from the header, `n` ones read so far. -/
  | hdrHeight (n : ℕ)
  /-- Searching the prime: testing the candidate `q` against the divisor `d`. -/
  | prime (q d : ℕ)
  /-- A step of the iterative procedure. -/
  | run
  /-- Reading bit `i` of the leaf at the current path. -/
  | leaf (i : ℕ)
  /-- Reading bit `k` of the table of the gate of the top frame, with the sums so far. -/
  | scan (k : ℕ) (acc : List ℕ)
  /-- Halted, after emitting the value. -/
  | done

/-- A state of the machine. -/
structure State where
  /-- The value length `ℓ`. -/
  ell : ℕ
  /-- The height. -/
  height : ℕ
  /-- The prime. -/
  p : ℕ
  /-- The registers. -/
  regs : Regs
  /-- The stack of frames, innermost first. -/
  stack : List Frame
  /-- The mode of the iterative procedure. -/
  mode : Mode
  /-- The control state. -/
  ctl : Ctl

/-- The offset in the encoding of the node at the path of a stack. -/
def offset (s : State) (st : List Frame) : ℕ :=
  s.ell + s.height + 2 + pathOffset s.ell s.height (path st)

/-- The steps of the iterative procedure, without input. -/
def runStep (s : State) : State × List Bool :=
  match s.mode, s.stack with
  | .call neg t, st =>
    if st.length = s.height then ({ s with ctl := .leaf 0 }, [])
    else
      ({ s with
          regs := s.regs.scale s.p (t + 1) (unitVal 0)
          stack := ⟨0, 0, neg, t⟩ :: st
          mode := .call false (t + 1) }, [])
  | .ret, [] => ({ s with ctl := .done }, (s.regs.get 2).map (· == 1))
  | .ret, fr :: st =>
    match fr.phase with
    | 0 =>
      ({ s with
          regs := s.regs.scale s.p (fr.target + 2) (unitVal fr.round)
          stack := { fr with phase := 1 } :: st
          mode := .call false (fr.target + 2) }, [])
    | 1 => ({ s with ctl := .scan 0 (List.replicate s.ell 0) }, [])
    | 2 =>
      ({ s with
          regs := s.regs.scale s.p (fr.target + 1) (unitInv s.p fr.round)
          stack := { fr with phase := 3 } :: st
          mode := .call true (fr.target + 2) }, [])
    | 3 =>
      let R := s.regs.scale s.p (fr.target + 2) (unitInv s.p fr.round)
      if fr.round + 1 < s.p - 1 then
        ({ s with
            regs := R.scale s.p (fr.target + 1) (unitVal (fr.round + 1))
            stack := ⟨fr.round + 1, 0, fr.neg, fr.target⟩ :: st
            mode := .call false (fr.target + 1) }, [])
      else ({ s with regs := R, stack := st }, [])

/-- Subtract `c` times the sums `acc` from register `t`, modulo `p`. -/
def subtractSums (p c : ℕ) (t : Fin 3) (acc : List ℕ) (R : Regs) : Regs :=
  R.set t ((List.range (R.get t).length).map fun i =>
    addMod p ((R.get t).getD i 0) (negMod p (mulMod p c (acc.getD i 0))))

/-- A step, given the bit read. -/
def step (s : State) (b : Bool) : State × List Bool :=
  match s.ctl with
  | .hdrLength n =>
    if b then ({ s with ctl := .hdrLength (n + 1) }, [])
    else ({ s with ell := n, ctl := .hdrHeight 0 }, [])
  | .hdrHeight n =>
    if b then ({ s with ctl := .hdrHeight (n + 1) }, [])
    else ({ s with height := n, ctl := .prime (2 * s.ell + 2) 2 }, [])
  | .prime q d =>
    if d < q then
      if q % d = 0 then ({ s with ctl := .prime (q + 1) 2 }, [])
      else ({ s with ctl := .prime q (d + 1) }, [])
    else
      ({ s with
          p := q
          regs := (List.replicate s.ell 0, List.replicate s.ell 0, List.replicate s.ell 0)
          stack := []
          mode := .call false 2
          ctl := .run }, [])
  | .run => runStep s
  | .leaf i =>
    match s.mode with
    | .call neg t =>
      if i < s.ell then
        ({ s with
            regs := s.regs.set t (modifyAt (s.regs.get t) i
              (addMod s.p (if b then sgnVal s.p neg else 0)))
            ctl := .leaf (i + 1) }, [])
      else ({ s with mode := .ret, ctl := .run }, [])
    | .ret => (s, [])
  | .scan k acc =>
    match s.stack with
    | fr :: st =>
      if k < tableLength s.ell then
        if b then
          ({ s with ctl := .scan (k + 1) (modifyAt acc (k % s.ell) (addMod s.p
            (weight s.p s.ell (k / s.ell) (s.regs.get (fr.target + 1))
              (s.regs.get (fr.target + 2))))) }, [])
        else ({ s with ctl := .scan (k + 1) acc }, [])
      else
        ({ s with
            regs := subtractSums s.p (sgnVal s.p fr.neg) fr.target acc s.regs
            stack := { fr with phase := 2 } :: st
            mode := .call true (fr.target + 1)
            ctl := .run }, [])
    | [] => (s, [])
  | .done => (s, [])

/-- The address read by a step. -/
def addr (s : State) : Option ℕ :=
  match s.ctl with
  | .hdrLength n => some n
  | .hdrHeight n => some (s.ell + 1 + n)
  | .leaf i => some (offset s s.stack + i)
  | .scan k _ => some (offset s s.stack.tail + k)
  | _ => none

/-- The initial state: reading the header. -/
def init : State := ⟨0, 0, 0, ([], [], []), [], .ret, .hdrLength 0⟩

/-- **The Tree Evaluation read machine.** -/
def machine : Turing.ReadMachine State where
  init := init
  halt s := match s.ctl with
    | .done => true
    | _ => false
  addr := addr
  step := step

end Reader

end Cslib.TreeEval
