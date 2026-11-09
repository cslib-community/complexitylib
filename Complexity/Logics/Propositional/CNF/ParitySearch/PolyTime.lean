/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ParitySearch
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Foundations.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Searching the three-wise independent sample space runs in polynomial time

Exhaustive search of the three-wise independent sample space (`Cslib.Logic.PL.paritySearch`) is
polynomial-time for any encoding of the variables, with literals encoded by `encPair` and clauses
and formulas by `encList` (`Cslib.Logic.PL.computableInPolyTime_paritySearch`). A sample bit is a
Boolean fold over the seed and the low binary digits of a position, computed in unary by `idxOf`
and converted to binary. The seeds of `⌈log₂ n⌉ + 1` bits are enumerated by `bitsEnumList`; there
are at most `4 n + 4` of them (`Nat.two_pow_clog_two_le`), so the enumeration has polynomial size.
Counting falsified clauses is polynomial-time, and the search is a fold over the candidates whose
step reads the input formula. Every candidate is a sublist of the distinct variables
(`Cslib.Logic.PL.sublist_of_mem_parityCandidates`), which bounds the state.

## Main results

* `Cslib.Logic.PL.computableInPolyTime_paritySample`: a sample bit.
* `Cslib.Logic.PL.computableInPolyTime_countUnsat_mem`: counting the clauses falsified by the
  assignment setting the listed variables to `true`.
* `Cslib.Logic.PL.computableInPolyTime_parityCandidates`: the points of the sample space.
* `Cslib.Logic.PL.computableInPolyTime_paritySearch`: the search.

## References

* [N. Alon, L. Babai, A. Itai, *A fast and simple randomized parallel algorithm for the maximal
  independent set problem*][AlonBabaiItai1986]
-/

public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

variable {V : Type} [DecidableEq V] (enc : V ↪ List Bool)

/-- Computing the value a seed gives a variable is polynomial-time. -/
theorem computableInPolyTime_paritySample :
    ComputableInPolyTime (fun p : (List V × List Bool) × V => paritySample p.1.1 p.1.2 p.2)
      (encPair (encPair (encList enc) encBits) enc) encBool := by
  unfold paritySample
  fun_prop

/-- Counting the clauses falsified by the assignment setting the listed variables to `true` is
polynomial-time. -/
theorem computableInPolyTime_countUnsat_mem :
    ComputableInPolyTime (fun p : CNF V × List V => p.1.countUnsat fun v => decide (v ∈ p.2))
      (encPair (encCNFOver enc) (encList enc)) encUnary := by
  unfold CNF.countUnsat Clause.eval Literal.eval
  fun_prop

/-- One step of the search, reading the formula, is polynomial-time. -/
theorem computableInPolyTime_betterCandidate :
    ComputableInPolyTime (fun p : (CNF V × List V) × List V => betterCandidate p.1.1 p.1.2 p.2)
      (encPair (encPair (encCNFOver enc) (encList enc)) (encList enc)) (encList enc) := by
  have h := computableInPolyTime_countUnsat_mem enc
  have hp := fst (encPair (encList (encList (encPair enc encBool))) (encList enc)) (encList enc)
  have hlt := unary_lt' (h.comp (hp.fst'.prod (snd _ _))) (h.comp (hp.fst'.prod hp.snd'))
  have h' := ite hlt (snd _ _) hp.snd'
  simp only [Function.comp_apply, decide_eq_true_eq] at h'
  exact h'

/-- Listing the points of the sample space is polynomial-time. -/
theorem computableInPolyTime_parityCandidates :
    ComputableInPolyTime (parityCandidates (V := V)) (encList enc) (encList (encList enc)) := by
  have hsample := computableInPolyTime_paritySample enc
  have hcount : ComputableInPolyTime (fun vs : List V => Nat.clog 2 vs.length + 1)
      (encList enc) encUnary := by
    have := unary_clog_const 2
    fun_prop
  have henum := bitsEnumList hcount (size := fun n => (4 * n + 4) * (8 * n + 9)) (by fun_prop)
    fun vs => by
      have h1 := Nat.two_pow_clog_two_le vs.length
      have h2 := SizedListEncoding.length_le (encA := enc) (encL := encList enc) vs
      have h3 := Nat.lt_two_pow_self (n := Nat.clog 2 vs.length + 1)
      rw [pow_succ] at h3 ⊢
      exact Nat.mul_le_mul (by omega) (by omega)
  unfold parityCandidates
  fun_prop

/-- Every point of the sample space lists some of the variables, in order. -/
theorem sublist_of_mem_parityCandidates {vs T : List V} (hT : T ∈ parityCandidates vs) :
    T.Sublist vs := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hT
  exact List.filter_sublist

/-- **Searching the three-wise independent sample space is polynomial-time**, for any encoding of
the variables. -/
theorem computableInPolyTime_paritySearch :
    ComputableInPolyTime (paritySearch (V := V))
      (encCNFOver enc) (encList enc) := by
  have hcands := (computableInPolyTime_parityCandidates enc).comp
    (CNF.computableInPolyTime_distinctVars enc)
  have hfold := foldlWithInput_of_bounded_growth
    (encA := encList enc) (encB := encList enc)
    (list := fun φ : CNF V => parityCandidates φ.distinctVars)
    (step := betterCandidate)
    (const (encIn := encList (encList (encPair enc encBool))) (encOut := encList enc) [])
    ⟨hcands, computableInPolyTime_betterCandidate enc, inferInstance, inferInstance⟩
    (growth := fun φ => (encList enc φ.distinctVars).length)
    ⟨(CNF.computableInPolyTime_distinctVars enc).polyBounded_length, fun φ best T hT => by
      have := length_encList_sublist enc (sublist_of_mem_parityCandidates hT)
      unfold betterCandidate
      split <;> omega⟩
  exact hfold

end Cslib.Logic.PL
