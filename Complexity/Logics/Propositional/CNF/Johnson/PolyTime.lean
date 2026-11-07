/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Johnson
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# Johnson's algorithm runs in polynomial time

Johnson's algorithm (`Cslib.Logic.PL.johnson`) is polynomial-time for any encoding of the
variables, with literals encoded by `encPair` and clauses and formulas by `encList`
(`Cslib.Logic.PL.computableInPolyTime_johnson`). Removing repeated literals, setting a variable
and computing the weight are polynomial-time, the weight in binary from the bound `L` in unary.
The algorithm is a fold over the distinct variables whose step reads the input formula; setting a
variable does not lengthen the encoded formula (`Cslib.Logic.PL.CNF.length_encList_assign_le`)
and each round adds one variable to the output, so the state stays polynomially bounded. The
weights have `O(L)` bits, and comparing them is polynomial-time.

## Main results

* `Cslib.Logic.PL.Clause.computableInPolyTime_eraseDupLits`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_eraseDupLits`: removing repeated literals.
* `Cslib.Logic.PL.CNF.computableInPolyTime_assign`: setting a variable.
* `Cslib.Logic.PL.CNF.computableInPolyTime_johnsonWeight`: Johnson's weight.
* `Cslib.Logic.PL.computableInPolyTime_johnson`: Johnson's algorithm.

## References

* [D. S. Johnson, *Approximation algorithms for combinatorial problems*][Johnson1974]
-/

public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

variable {V : Type} [DecidableEq V] (enc : V ↪ List Bool)

/-- Removing repeated literals from a clause is polynomial-time. -/
theorem Clause.computableInPolyTime_eraseDupLits :
    ComputableInPolyTime (Clause.eraseDupLits (V := V))
      (encList (encPair enc encBool)) (encList (encPair enc encBool)) := by
  unfold Clause.eraseDupLits
  fun_prop

/-- Removing repeated literals from every clause is polynomial-time. -/
theorem CNF.computableInPolyTime_eraseDupLits :
    ComputableInPolyTime (CNF.eraseDupLits (V := V))
      (encList (encList (encPair enc encBool))) (encList (encList (encPair enc encBool))) := by
  have := Clause.computableInPolyTime_eraseDupLits enc
  unfold CNF.eraseDupLits
  fun_prop

/-- Setting a variable is polynomial-time. -/
theorem CNF.computableInPolyTime_assign :
    ComputableInPolyTime (fun p : (V × Bool) × CNF V => p.2.assign p.1.1 p.1.2)
      (encPair (encPair enc encBool) (encList (encList (encPair enc encBool))))
      (encList (encList (encPair enc encBool))) := by
  unfold CNF.assign
  fun_prop

omit [DecidableEq V] in
/-- Johnson's weight, in binary, is polynomial-time in a unary bound `L` and the formula. -/
theorem CNF.computableInPolyTime_johnsonWeight :
    ComputableInPolyTime (fun p : ℕ × CNF V => p.2.johnsonWeight p.1)
      (encPair encUnary (encList (encList (encPair enc encBool)))) encNat := by
  unfold CNF.johnsonWeight
  fun_prop

/-- Setting a variable does not lengthen the encoding of a formula. -/
theorem CNF.length_encList_assign_le (v : V) (b : Bool) (ψ : CNF V) :
    (encList (encList (encPair enc encBool)) (ψ.assign v b)).length ≤
      (encList (encList (encPair enc encBool)) ψ).length :=
  (length_encList_map_le _ _ fun _ _ =>
    length_encList_sublist _ List.filter_sublist).trans
    (length_encList_sublist _ List.filter_sublist)

/-- Setting a computed variable to a computed value in a computed formula is polynomial-time. -/
theorem CNF.computableInPolyTime_assign' {α : Type} {input : α ↪ List Bool} {v : α → V}
    {b : α → Bool} {ψ : α → CNF V} (hv : ComputableInPolyTime v input enc)
    (hb : ComputableInPolyTime b input encBool)
    (hψ : ComputableInPolyTime ψ input (encList (encList (encPair enc encBool)))) :
    ComputableInPolyTime (fun a => (ψ a).assign (v a) (b a)) input
      (encList (encList (encPair enc encBool))) := by
  have h := (CNF.computableInPolyTime_assign enc).comp ((hv.prod hb).prod hψ)
  exact h

omit [DecidableEq V] in
/-- Johnson's weight of a computed formula with a computed unary bound is polynomial-time. -/
theorem CNF.computableInPolyTime_johnsonWeight' {α : Type} {input : α ↪ List Bool}
    {L : α → ℕ} {ψ : α → CNF V} (hL : ComputableInPolyTime L input encUnary)
    (hψ : ComputableInPolyTime ψ input (encList (encList (encPair enc encBool)))) :
    ComputableInPolyTime (fun a => (ψ a).johnsonWeight (L a)) input encNat := by
  have h := (CNF.computableInPolyTime_johnsonWeight enc).comp (hL.prod hψ)
  exact h

/-- One round of Johnson's algorithm, reading the input formula, the state and the next variable,
is polynomial-time. -/
private theorem computableInPolyTime_johnsonRound :
    ComputableInPolyTime
      (fun p : (CNF V × (CNF V × List V)) × V =>
        if (p.1.2.1.assign p.2 true).johnsonWeight p.1.1.vars.length ≤
            (p.1.2.1.assign p.2 false).johnsonWeight p.1.1.vars.length then
          (p.1.2.1.assign p.2 true, p.2 :: p.1.2.2) else (p.1.2.1.assign p.2 false, p.1.2.2))
      (encPair (encPair (encList (encList (encPair enc encBool)))
        (encPair (encList (encList (encPair enc encBool))) (encList enc))) enc)
      (encPair (encList (encList (encPair enc encBool))) (encList enc)) := by
  have hassign (b : Bool) := CNF.computableInPolyTime_assign' enc (snd _ _) (const b)
    ((fst (encPair (encList (encList (encPair enc encBool)))
      (encPair (encList (encList (encPair enc encBool))) (encList enc))) enc).snd'.fst')
  have hweight (b : Bool) := CNF.computableInPolyTime_johnsonWeight' enc
    (CNF.computableInPolyTime_vars_length (fst _ _).fst') (hassign b)
  have hle := ComputableTidilyInPolyTime.binary_le.computableInPolyTime.comp
    ((hweight true).prod (hweight false))
  have hT := (fst (encPair (encList (encList (encPair enc encBool)))
    (encPair (encList (encList (encPair enc encBool))) (encList enc))) enc).snd'.snd'
  have h := ite hle ((hassign true).prod (cons' (snd _ _) hT)) ((hassign false).prod hT)
  simpa only [Function.comp_apply, decide_eq_true_eq] using h

/-- Johnson's algorithm as a fold whose step reads the input formula. -/
private theorem johnson_eq_foldl (φ : CNF V) :
    johnson φ = (φ.distinctVars.foldl (fun s v =>
      if (s.1.assign v true).johnsonWeight φ.vars.length ≤
          (s.1.assign v false).johnsonWeight φ.vars.length then
        (s.1.assign v true, v :: s.2) else (s.1.assign v false, s.2))
      (φ.eraseDupLits, [])).2 :=
  rfl

/-- **Johnson's algorithm is polynomial-time**, for any encoding of the variables. -/
theorem computableInPolyTime_johnson :
    ComputableInPolyTime (johnson (V := V))
      (encList (encList (encPair enc encBool))) (encList enc) := by
  have hlist := CNF.computableInPolyTime_distinctVars enc
  have hinit := (CNF.computableInPolyTime_eraseDupLits enc).prod
    (const (encIn := encList (encList (encPair enc encBool))) (encOut := encList enc) [])
  have hfold := foldlWithInput_of_bounded_growth
    (encA := enc) (encB := encPair (encList (encList (encPair enc encBool))) (encList enc))
    (list := fun φ : CNF V => φ.distinctVars)
    (step := fun (φ : CNF V) (s : CNF V × List V) (v : V) =>
      if (s.1.assign v true).johnsonWeight φ.vars.length ≤
          (s.1.assign v false).johnsonWeight φ.vars.length then
        (s.1.assign v true, v :: s.2) else (s.1.assign v false, s.2))
    hinit ⟨hlist, computableInPolyTime_johnsonRound enc, inferInstance, inferInstance⟩
    (growth := fun φ => 2 * (encList enc φ.distinctVars).length + 1)
    ⟨((PolyBounded.const 2).mul hlist.polyBounded_length).add (.const 1),
      fun φ s v hv => by
        have := SizedListEncoding.length_elem_le (encA := enc) (encL := encList enc) _ v hv
        have h1 := CNF.length_encList_assign_le enc v true s.1
        have h2 := CNF.length_encList_assign_le enc v false s.1
        split
        · simp only [length_encPair, encList_cons, List.length_append, length_frame]
          omega
        · simp only [length_encPair]
          omega⟩
  have h := (snd _ _).comp hfold
  exact h

end Cslib.Logic.PL
