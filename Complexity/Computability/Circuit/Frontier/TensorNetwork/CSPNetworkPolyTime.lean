/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ClauseNetworkPolyTime
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CSPNetwork
public import Complexity.Computability.PolyTime.CSP.ToCNF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The constraint network in polynomial time

The constraint network of a weighted Boolean CSP instance
(`Cslib.Circuits.Frontier.ClauseNetwork.cspNetwork`) is computable in polynomial time from the
encoded instance, in the encoding of the contraction algorithm, whenever the weight of a relation
symbol at each fixed pattern of length at most `k` is polynomial-time in the symbol (for instance,
when the relation alphabet is finite). Its tables are maps over the constant list of the first
`k + 1` widths, read at the arity of each constraint.

## Main results

* `Cslib.Circuits.Frontier.ClauseNetwork.computableInPolyTime_cspNetwork`: the constraint network
  is polynomial-time.
-/

public section

namespace Cslib.Circuits.Frontier.ClauseNetwork

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Logic.PL
open Cslib.Complexity (encCSP encConstraint)

variable {Rel : Type}

/-- The occurrences of a CSP instance, those of its positive formula, are polynomial-time. -/
theorem computableInPolyTime_occurrences_varCNF (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun F : CSP Rel ℕ => occurrences F.varCNF) (encCSP encRel encNat)
      (encList (encOccurrence encNat)) := by
  have h : ComputableInPolyTime (CSP.varCNF (Rel := Rel) (V := ℕ)) (encCSP encRel encNat)
      (encList (encList (encPair encNat encBool))) := by
    unfold CSP.varCNF
    fun_prop
  exact (computableInPolyTime_occurrences encNat).comp h

variable (encRel : Rel ↪ List Bool) (k : ℕ) (wt : Rel → List Bool → ℕ)
  (hwt : ∀ w : List Bool, w.length ≤ k →
    ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat)
include hwt

/-- The entry of a constraint table at a fixed word value is polynomial-time. -/
theorem computableInPolyTime_cspEntry (idx : ℕ) :
    ComputableInPolyTime (fun c : Constraint Rel ℕ => cspEntry k wt c idx)
      (encConstraint encRel encNat) encNat := by
  have hlist := mapFilterConst (List.range (k + 1)) (test := fun _ _ => true)
    (f := fun (c : Constraint Rel ℕ) r => wt c.1 (BitString.lowBits r idx))
    (encIn := encConstraint encRel encNat) (fun _ _ => const true)
    (fun r hr => (hwt _ (by rw [BitString.length_lowBits]; simpa [Nat.lt_succ_iff] using hr)).comp
      (fst _ _))
  simp only [List.filter_true] at hlist
  unfold cspEntry
  exact listGetDWithInput hlist ((length_list _).comp (snd _ _)) 0

/-- The entry of a row table at a fixed word value is polynomial-time in the instance and the
unary row number. -/
theorem computableInPolyTime_cspRow (idx : ℕ) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × ℕ => cspRow k wt p.1 p.2 idx)
      (encPair (encCSP encRel encNat) encUnary) encNat := by
  unfold cspRow
  exact listGetDWithInput ((map (computableInPolyTime_cspEntry encRel k wt hwt idx)).comp
    (fst _ _)) (snd _ _) 0

/-- **The constraint network is polynomial-time** from the encoded instance, with its number of
rows in binary. -/
theorem computableInPolyTime_cspNetwork :
    ComputableInPolyTime (cspNetwork k wt) (encCSP encRel encNat)
      (encPair encNat ExplicitTensorNetwork.encExplicitNetwork) :=
  computableInPolyTime_network (max k 4) (computableInPolyTime_occurrences_varCNF encRel)
    ((length_list _).comp id') (computableInPolyTime_cspRow encRel k wt hwt)

end Cslib.Circuits.Frontier.ClauseNetwork
