/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.ParityFactorEval
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native negacyclic multiplication of coefficient lists

The existing truncated integer polynomial product supplies the coefficients below `2*n`.
Subtracting its upper half from its lower half reduces modulo `X^n + 1`. Inputs are
truncated to `n` coefficients and missing entries are zero. The output always has length `n`.
At modulus zero, signed remainder followed by `toNat` truncates each integer result at zero;
canonical modular semantics require positive modulus.

## Main definitions

* `negacyclicMulResidues`: total multiplication of binary-natural coefficient lists.

## Main results

* `computableInPolyTime_negacyclicMulResidues`: one plain certificate for all unary
  dimensions, binary moduli, and framed binary coefficient lists.
-/

@[expose] public section

namespace Cslib

open Turing.MultiTapeTM

/-- Multiply the first `n` coefficients modulo `X^n + 1` and then reduce modulo `q`.
Short lists are zero-padded; excess coefficients are ignored. -/
def negacyclicMulResidues (n q : ℕ) (a b : List ℕ) : List ℕ :=
  let c := mulZJet (2 * n) ((a.take n).map Int.ofNat) ((b.take n).map Int.ofNat)
  (List.range n).map fun i => ((c.getD i 0 - c.getD (n + i) 0) % (q : ℤ)).toNat

/-- Output length is the requested dimension, including the empty dimension. -/
@[simp] theorem length_negacyclicMulResidues (n q : ℕ) (a b : List ℕ) :
    (negacyclicMulResidues n q a b).length = n := by
  simp [negacyclicMulResidues]

private theorem takeCast_polytime :
    ComputableInPolyTime (fun x : ℕ × List ℕ => (x.2.take x.1).map Int.ofNat)
      (encPair encUnary (encList encNat)) (encList encIntBin) := by
  apply ComputableInPolyTime.mapWithInput
    (show ComputableInPolyTime (fun x : ℕ × List ℕ => x.2.take x.1)
      (encPair encUnary (encList encNat)) (encList encNat) by fun_prop)
  exact ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.snd _ _)

private theorem reduce_polytime :
    ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List ℤ => (List.range x.1.1).map fun i =>
        ((x.2.getD i 0 - x.2.getD (x.1.1 + i) 0) % (x.1.2 : ℤ)).toNat)
      (encPair (encPair encUnary encNat) (encList encIntBin)) (encList encNat) := by
  apply ComputableInPolyTime.mapWithInput
    (show ComputableInPolyTime (fun x : (ℕ × ℕ) × List ℤ => List.range x.1.1)
      (encPair (encPair encUnary encNat) (encList encIntBin))
      (encList encUnary) by fun_prop)
  have hpar := ComputableInPolyTime.fst
    (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary
  have hi := ComputableInPolyTime.snd
    (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary
  have hlo := (ComputableInPolyTime.listGetD (encA := encIntBin) 0).comp
    (hpar.snd'.prod hi)
  have hhi := (ComputableInPolyTime.listGetD (encA := encIntBin) 0).comp
    (hpar.snd'.prod (ComputableInPolyTime.unary_add.comp (hpar.fst'.fst'.prod hi)))
  exact ComputableInPolyTime.intBin_emodNat'
    (ComputableInPolyTime.intBin_sub.comp (hlo.prod hhi)) hpar.fst'.snd'

private theorem product_polytime :
    ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List ℕ × List ℕ =>
        mulZJet (2 * x.1.1) ((x.2.1.take x.1.1).map Int.ofNat)
          ((x.2.2.take x.1.1).map Int.ofNat))
      (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat)))
      (encList encIntBin) := by
  have hpar := ComputableInPolyTime.fst (encPair encUnary encNat)
    (encPair (encList encNat) (encList encNat))
  have hlists := ComputableInPolyTime.snd (encPair encUnary encNat)
    (encPair (encList encNat) (encList encNat))
  have ha := takeCast_polytime.comp (hpar.fst'.prod hlists.fst')
  have hb := takeCast_polytime.comp (hpar.fst'.prod hlists.snd')
  have hc := computableInPolyTime_mulZJet
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hpar.fst')) ha hb
  exact hc

/-- The dimension is unary, while the modulus and all coefficients are binary. The bound
charges the complete input lists, including coefficients beyond the requested dimension. -/
@[fun_prop] theorem computableInPolyTime_negacyclicMulResidues :
    ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List ℕ × List ℕ => negacyclicMulResidues x.1.1 x.1.2 x.2.1 x.2.2)
      (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat)))
      (encList encNat) := by
  have h := reduce_polytime.comp
    ((ComputableInPolyTime.fst (encPair encUnary encNat)
      (encPair (encList encNat) (encList encNat))).prod product_polytime)
  simpa only [Function.comp_def, negacyclicMulResidues] using h

end Cslib
