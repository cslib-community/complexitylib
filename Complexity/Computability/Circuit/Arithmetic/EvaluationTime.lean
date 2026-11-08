/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Encoding
public import Complexity.Computability.Circuit.Encoding.Evaluation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time evaluation over a fixed finite semiring

One machine evaluates every runtime arithmetic gate list and input list over a fixed finite
semiring. Indices use binary encoding and bounded list lookup, including on malformed gate lists.
Each gate appends one value whose encoded size is bounded by a constant depending only on the
fixed carrier and its encoding. The result includes the full input and gate trace, not just a
single output. This does not certify arithmetic uniformly over growing fields.

## Main results

* `Arithmetic.computableInPolyTime_evalCode`: the existing total evaluator is polynomial-time.
* `Arithmetic.computableInPolyTime_evalOutput`: a binary-indexed output lookup is polynomial-time.

The semantic bridges are the existing `Program.evalCode_code` and `Circuit.eval_eq_getD`.
These runtime certificates are original.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Turing.MultiTapeTM ComputableInPolyTime

variable {F α : Type} [Semiring F] [Finite F] {eF : F ↪ List Bool}
  {eIn : α ↪ List Bool}

private theorem polyTime_step :
    ComputableInPolyTime (fun p : List F × (ArithOp F × List ℕ) =>
      p.1 ++ [arithInterpretation F p.2.1 fun a =>
        p.2.2[a.val]?.elim 0 (p.1.getD · 0)])
      (encPair (encList eF) (Circuit.encGate (ArithOp.encoding eF))) (encList eF) := by
  let value : ArithOp F × F × F → F := fun p => match p.1 with
    | .add => p.2.1 + p.2.2
    | .mul => p.2.1 * p.2.2
    | .const c => c
  have heq : (fun p : List F × (ArithOp F × List ℕ) =>
      p.1 ++ [arithInterpretation F p.2.1 fun a =>
        p.2.2[a.val]?.elim 0 (p.1.getD · 0)]) =
      fun p => p.1 ++ [value (p.2.1, p.2.2[0]?.elim 0 (p.1.getD · 0),
        p.2.2[1]?.elim 0 (p.1.getD · 0))] := by
    funext p
    rcases p with ⟨xs, op, args⟩
    cases op <;> rfl
  rw [heq]
  have hargs (i : ℕ) : ComputableInPolyTime (fun p : List F × (ArithOp F × List ℕ) =>
      p.2.2[i]?.elim 0 (p.1.getD · 0))
      (encPair (encList eF) (Circuit.encGate (ArithOp.encoding eF))) eF :=
    optionElimWithInput (getElem? (snd _ _).snd' (const i)) (const 0)
      (listGetD_binary 0 (fst _ _).fst' (snd _ _))
  have hvalue := (of_finite (encIn := encPair (ArithOp.encoding eF) (encPair eF eF))
    (encOut := eF) value).comp
    ((snd _ _).fst'.prod ((hargs 0).prod (hargs 1)))
  exact listAppend' (.fst _ _) (cons' hvalue (.const []))

/-- The input and the entire arithmetic gate list are charged runtime data. The carrier and
scalar encoding are fixed; missing arguments and invalid binary indices use the total default
semantics of `evalCode`. -/
@[fun_prop]
theorem computableInPolyTime_evalCode {x : α → List F}
    {gates : α → List (ArithOp F × List ℕ)}
    (hx : ComputableInPolyTime x eIn (encList eF))
    (hgates : ComputableInPolyTime gates eIn
      (encList (Circuit.encGate (ArithOp.encoding eF)))) :
    ComputableInPolyTime (fun a => evalCode (arithInterpretation F) 0 (x a) (gates a))
      eIn (encList eF) := by
  let _ := Fintype.ofFinite F
  let bound := Finset.univ.sup (fun x : F => (eF x).length)
  apply ComputableInPolyTime.foldl_of_bounded_growth hgates hx polyTime_step
    (growth := 2 * bound + 1)
  intro state gate
  simp only [encList_append, encList_cons, encList_nil, List.append_nil,
    List.length_append, length_frame]
  have hbound (x : F) : (eF x).length ≤ bound :=
    Finset.le_sup (f := fun x : F => (eF x).length) (Finset.mem_univ x)
  exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hbound _)) 1) _

/-- Read an output from the computed trace without iterating to the numeric value of an
unchecked binary index. -/
@[fun_prop]
theorem computableInPolyTime_evalOutput {x : α → List F}
    {gates : α → List (ArithOp F × List ℕ)} {output : α → ℕ}
    (hx : ComputableInPolyTime x eIn (encList eF))
    (hgates : ComputableInPolyTime gates eIn
      (encList (Circuit.encGate (ArithOp.encoding eF))))
    (houtput : ComputableInPolyTime output eIn encNat) :
    ComputableInPolyTime (fun a =>
      (evalCode (arithInterpretation F) 0 (x a) (gates a)).getD (output a) 0) eIn eF :=
  listGetD_binary 0 (computableInPolyTime_evalCode hx hgates) houtput

end Cslib.Circuits.Arithmetic
