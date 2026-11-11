/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Evaluation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.OpValue
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Evaluating De Morgan circuits in polynomial time

`CslibFrontier.Computability.Circuit.Encoding.Evaluation` defines signature-polymorphic gate-list
evaluation (`Cslib.Circuits.evalCode`) and proves its agreement with typed circuit evaluation
(`Cslib.Circuits.Program.evalCode_code`, `Cslib.Circuits.Circuit.eval_eq_getD`). This module
specializes that evaluator to De Morgan circuits (`Cslib.Circuits.Boolean.evalOutput`) and proves
polynomial-time computability certificates for it.

For De Morgan circuits, `evalCode` is computable in polynomial time on the binary encoding of
gate lists (`Cslib.Circuits.Boolean.computableInPolyTime_evalCode`), and so is reading an output
wire given by its binary number (`Cslib.Circuits.Boolean.computableInPolyTime_evalOutput`).
These are certificates for the `fun_prop` calculus of polynomial-time computations; the
evaluators of `CslibFrontier.Computability.Circuit.Evaluation` carry no runtime bound. Each gate is
evaluated by two lookups at wire numbers, which are capped at the number of values computed so far
before they are converted to unary, so wire numbers far beyond the circuit cost only their binary
length.

The typed evaluation certificate accepts any bit list. It pads short lists with `false` and
truncates long lists to the declared input arity before invoking the raw evaluator. Circuit
generation, input preparation, binary wire lookup and evaluation are all included in its cost.

## Main definitions

* `Cslib.Circuits.Boolean.evalOutput`: the value of a wire after evaluating a list of De Morgan
  gates.

## Main results

* `Cslib.Circuits.Circuit.eval_eq_evalOutput`: De Morgan circuit evaluation through
  `Cslib.Circuits.Boolean.evalOutput`.
* `Cslib.Circuits.Circuit.eval_ofList_eq_evalOutput`: typed evaluation on an arbitrary input list
  uses the padded or truncated input word.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalCode`,
  `Cslib.Circuits.Boolean.computableInPolyTime_evalOutput`: evaluation of De Morgan gate lists
  is polynomial-time.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalCircuit`: evaluating an efficiently
  generated typed circuit on an efficiently generated input list is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

universe u v

variable {σ : Signature.{v}} {U : Type u} {n k m : ℕ}

namespace Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Polynomial time -/

/-- One evaluation step: append the value of a gate. -/
private theorem computableInPolyTime_step :
    ComputableInPolyTime (fun p : List Bool × (Op × List ℕ) =>
      p.1 ++ [interpretation p.2.1 fun a => p.2.2[a.val]?.elim false (p.1.getD · false)])
      (encPair encBits encGate) encBits := by
  have heq : (fun p : List Bool × (Op × List ℕ) =>
      p.1 ++ [interpretation p.2.1 fun a => p.2.2[a.val]?.elim false (p.1.getD · false)]) =
      fun p => p.1 ++ [p.2.1.value (p.2.2[0]?.elim false (p.1.getD · false))
        (p.2.2[1]?.elim false (p.1.getD · false))] :=
    funext fun p => by
      rw [Op.interpretation_eq_value p.2.1 fun i => p.2.2[i]?.elim false (p.1.getD · false)]
  rw [heq]
  have hargs (i : ℕ) : ComputableInPolyTime (fun p : List Bool × (Op × List ℕ) =>
      p.2.2[i]?.elim false (p.1.getD · false)) (encPair encBits encGate) encBool :=
    optionElimWithInput (getElem? (snd _ _).snd' (const i)) (const false)
      (listGetD_binary false (fst _ _).fst' (snd _ _))
  have hvalue : ComputableInPolyTime (fun p : List Bool × (Op × List ℕ) =>
      p.2.1.value (p.2.2[0]?.elim false (p.1.getD · false))
        (p.2.2[1]?.elim false (p.1.getD · false)))
      (encPair encBits encGate) encBool :=
    (of_finite (encIn := encPair encOp (encPair encBool encBool))
      fun p : Op × Bool × Bool => p.1.value p.2.1 p.2.2).comp
      ((snd _ _).fst'.prod ((hargs 0).prod (hargs 1)))
  exact bitsAppend (fst _ _) (bitsCons hvalue (const []))

/-- **Polynomial-time evaluation** of De Morgan gate lists, for input bits and a gate list in the
binary encoding `encGate`, both computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_evalCode {γ : Type} {encIn : γ ↪ List Bool}
    {x : γ → List Bool} {gates : γ → List (Op × List ℕ)}
    (hx : ComputableInPolyTime x encIn encBits)
    (hgates : ComputableInPolyTime gates encIn (encList encGate)) :
    ComputableInPolyTime (fun a => evalCode interpretation false (x a) (gates a))
      encIn encBits :=
  foldl_of_bounded_growth hgates hx computableInPolyTime_step (growth := 1) fun _ _ => by simp

/-- The value of wire `o` after evaluating the De Morgan gate list `gates` on the input bits `x`:
on the code of a circuit and the number of an output wire, the value of that output
(`Circuit.eval_eq_getD`). -/
def evalOutput (x : List Bool) (gates : List (Op × List ℕ)) (o : ℕ) : Bool :=
  (evalCode interpretation false x gates).getD o false

/-- Output `j` of a De Morgan circuit is `evalOutput` at the number of its output wire. -/
theorem _root_.Cslib.Circuits.Circuit.eval_eq_evalOutput (c : Circuit signature n m)
    (x : Fin n → Bool) (j : Fin m) :
    c.eval interpretation x j = evalOutput (List.ofFn x) c.code.1 (c.outputs j).toNat :=
  c.eval_eq_getD interpretation false x j

/-- **Polynomial-time evaluation** of an output of a De Morgan gate list, for input bits, a gate
list in the binary encoding `encGate` and a binary wire number, all computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_evalOutput {γ : Type} {encIn : γ ↪ List Bool}
    {x : γ → List Bool} {gates : γ → List (Op × List ℕ)} {o : γ → ℕ}
    (hx : ComputableInPolyTime x encIn encBits)
    (hgates : ComputableInPolyTime gates encIn (encList encGate))
    (ho : ComputableInPolyTime o encIn encNat) :
    ComputableInPolyTime (fun a => evalOutput (x a) (gates a) (o a)) encIn encBool :=
  listGetD_binary false (computableInPolyTime_evalCode hx hgates) ho

/-- Evaluate a typed circuit on an arbitrary bit list by padding or truncating to its input
arity. The output wire is read from the circuit's code at the specified output position. -/
theorem _root_.Cslib.Circuits.Circuit.eval_ofList_eq_evalOutput
    (c : Circuit signature n m) (x : List Bool) (j : Fin m) :
    c.eval interpretation (BitString.ofList n x) j =
      evalOutput ((x ++ List.replicate n false).take n) c.code.1 (c.code.2.getD j.val 0) := by
  rw [Circuit.eval_eq_evalOutput, BitString.ofFn_ofList_eq_take]
  congr 1
  simp [Circuit.code, List.getD_eq_getElem?_getD]

/-- Evaluate an efficiently computed typed circuit on any efficiently computed bit list.
No length premise is needed: missing inputs are `false`, and inputs past the circuit's arity
are ignored. The certificate charges circuit generation, input padding and all evaluation. -/
@[fun_prop] theorem computableInPolyTime_evalCircuit {γ : Type}
    {encIn : γ ↪ List Bool} {c : γ → Σ n, Circuit signature n 1} {x : γ → List Bool}
    (hc : ComputableInPolyTime c encIn (encCircuit 1))
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => (c a).2.eval interpretation (BitString.ofList (c a).1 (x a)) 0)
      encIn encBool := by
  have hview : ComputableInPolyTime
      (fun C : Σ n, Circuit signature n 1 => (C.1, C.2.code))
      (encCircuit 1) (encPair encUnary encCode) := .of_eq fun _ => rfl
  have hparts := hview.comp hc
  have hn := hparts.fst'
  have hpad := bitsTakeWithInput (hx.bitsAppend ((bitsReplicate false).comp hn)) hn
  have houtput := listGetD_binary (encA := encNat) 0 hparts.snd'.snd' (const 0)
  simpa only [Circuit.eval_ofList_eq_evalOutput, Fin.val_zero, Function.comp_def] using
    computableInPolyTime_evalOutput hpad hparts.snd'.fst' houtput

end Boolean

end Cslib.Circuits
