/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Circuit.Boolean.OpValue
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Evaluating circuits in polynomial time

`evalCode` evaluates a list of gates (`Cslib.Circuits.Program.code`) on a list of input values:
starting from the inputs, it appends the value of each gate in turn, reading wire `i` at
position `i` of the values computed so far. On the code of a program it returns the inputs
followed by the values of the gates (`Cslib.Circuits.Program.evalCode_code`), so it evaluates
circuits exactly as `Cslib.Circuits.Circuit.eval` does (`Cslib.Circuits.Circuit.eval_eq_getD`).
It is total: an argument or a wire missing from a malformed list reads a default value.

For De Morgan circuits, `evalCode` is computable in polynomial time on the binary encoding of
gate lists (`Cslib.Circuits.Boolean.computableInPolyTime_evalCode`), so is reading an output
wire given by its binary number (`Cslib.Circuits.Boolean.computableInPolyTime_evalOutput`).
These are certificates for the `fun_prop` calculus of polynomial-time computations; the
evaluators of `Complexity.Computability.Circuit.Evaluation` carry no runtime bound. Each gate is
evaluated by two lookups at wire numbers, which are capped at the number of values computed so far
before they are converted to unary, so wire numbers far beyond the circuit cost only their binary
length.

The typed evaluation certificate accepts any bit list. It pads short lists with `false` and
truncates long lists to the declared input arity before invoking the raw evaluator. Circuit
generation, input preparation, binary wire lookup and evaluation are all included in its cost.

## Main definitions

* `Cslib.Circuits.evalCode`: evaluation of a list of gates.
* `Cslib.Circuits.Boolean.evalOutput`: the value of a wire after evaluating a list of De Morgan
  gates.

## Main results

* `Cslib.Circuits.prefix_evalCode`: evaluating a gate list preserves its input prefix.
* `Cslib.Circuits.getD_evalCode`: the value of a well-formed gate from its arguments.

* `Cslib.Circuits.Program.evalCode_code`: on the code of a program, `evalCode` lists the inputs and
  the gate values.
* `Cslib.Circuits.Circuit.eval_eq_getD`: circuit evaluation through the code.
* `Cslib.Circuits.Circuit.eval_eq_evalOutput`: the same for De Morgan circuits, through
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

/-- Evaluate the list of gates `gates` on the input values `x`: start from `x` and append the value
of each gate in turn, reading wire `i` at position `i` of the values computed so far. An argument
missing from a gate, or a wire not yet computed, reads `d`; on the code of a program neither
happens (`Program.evalCode_code`). -/
def evalCode (I : Interpretation σ U) (d : U) (x : List U) (gates : List (σ.Op × List ℕ)) :
    List U :=
  gates.foldl (fun values g => values ++ [I g.1 fun a => g.2[a.val]?.elim d (values.getD · d)]) x

/-- Evaluating an empty gate list returns the initial wire values unchanged. -/
@[simp] theorem evalCode_nil (I : Interpretation σ U) (d : U) (x : List U) :
    evalCode I d x [] = x := rfl

/-- Evaluating a gate list followed by one gate `g` appends `g`'s evaluated output to the wire
values computed by `gates`. -/
theorem evalCode_append_singleton (I : Interpretation σ U) (d : U) (x : List U)
    (gates : List (σ.Op × List ℕ)) (g : σ.Op × List ℕ) :
    evalCode I d x (gates ++ [g]) =
      evalCode I d x gates ++
        [I g.1 fun a => g.2[a.val]?.elim d ((evalCode I d x gates).getD · d)] := by
  simp [evalCode, List.foldl_append]

/-- Evaluating a concatenation of gate lists evaluates the second list starting from the wire
values produced by the first. -/
theorem evalCode_append (I : Interpretation σ U) (d : U) (x : List U)
    (gates gates' : List (σ.Op × List ℕ)) :
    evalCode I d x (gates ++ gates') = evalCode I d (evalCode I d x gates) gates' := by
  simp [evalCode, List.foldl_append]

/-- Each gate adds one value. -/
@[simp] theorem length_evalCode (I : Interpretation σ U) (d : U) (x : List U)
    (gates : List (σ.Op × List ℕ)) : (evalCode I d x gates).length = x.length + gates.length := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih => simp [evalCode_append_singleton, ih, Nat.add_assoc]

/-- Evaluating a gate list only appends values. -/
theorem prefix_evalCode (I : Interpretation σ U) (d : U) (x : List U)
    (gates : List (σ.Op × List ℕ)) : x <+: evalCode I d x gates := by
  induction gates using List.reverseRecOn with
  | nil => exact List.prefix_refl _
  | append_singleton gates g ih =>
    rw [evalCode_append_singleton]
    exact ih.trans (List.prefix_append _ _)

/-- **The value of a gate** of a well-formed gate list is its operation applied to the values of
its arguments. -/
theorem getD_evalCode (I : Interpretation σ U) (d : U) (x : List U)
    {gates : List (σ.Op × List ℕ)} (h : Program.IsCodeFrom σ x.length 0 gates) {j : ℕ}
    {gate : σ.Op × List ℕ} (hg : gates[j]? = some gate) :
    (evalCode I d x gates).getD (x.length + j) d =
      I gate.1 fun a => gate.2[a.val]?.elim d ((evalCode I d x gates).getD · d) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have hsplit : gates = gates.take j ++ [gates[j]] ++ gates.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  have hlen : (evalCode I d x (gates.take j)).length = x.length + j := by
    rw [length_evalCode, List.length_take, Nat.min_eq_left hj.le]
  have hpre := prefix_evalCode I d (evalCode I d x (gates.take j ++ [gates[j]]))
    (gates.drop (j + 1))
  rw [← evalCode_append, ← hsplit, evalCode_append_singleton] at hpre
  obtain ⟨rest, hrest⟩ := hpre
  -- the arguments read wires computed before gate `j`
  have hargs : ∀ i ∈ gates[j].2, i < x.length + j := by
    intro i hi
    have := (h.getElem j hj).2 i hi
    omega
  have hread (i : ℕ) (hi : i < x.length + j) :
      (evalCode I d x gates).getD i d = (evalCode I d x (gates.take j)).getD i d := by
    rw [← hrest, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  have hv : (evalCode I d x gates).getD (x.length + j) d = I gates[j].1 fun a =>
      gates[j].2[a.val]?.elim d ((evalCode I d x (gates.take j)).getD · d) := by
    rw [← hrest, List.getD_append _ _ _ _ (by simp [hlen]), List.getD_append_right _ _ _ _
      (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  rw [hv]
  congr 1
  funext a
  rcases ha : gates[j].2[a.val]? with _ | i
  · rfl
  · exact (hread i (hargs i (List.mem_of_getElem? ha))).symm

/-- Wire `w` is at position `w.toNat` of the inputs followed by the gates. -/
theorem Wire.getD_append_toNat (x : Fin n → U) (y : Fin k → U) (d : U) (w : Wire n k) :
    (List.ofFn x ++ List.ofFn y).getD w.toNat d = Wire.elim x y w := by
  cases w with
  | input i =>
    rw [Wire.toNat_input, List.getD_append _ _ _ _ (by simp)]
    simp
  | gate j =>
    rw [Wire.toNat_gate, List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- **Evaluation through the code.** On the code of a program, `evalCode` lists the inputs and then
the values of the gates. -/
theorem Program.evalCode_code (p : Program σ n k) (I : Interpretation σ U) (d : U)
    (x : Fin n → U) :
    evalCode I d (List.ofFn x) p.code = List.ofFn x ++ List.ofFn (p.eval I x) := by
  induction p with
  | empty => simp
  | gate p line ih =>
    rw [Program.code_gate, evalCode_append_singleton, ih, List.ofFn_succ' ((p.gate line).eval I x)]
    simp only [Program.eval_gate_castSucc, Program.eval_gate_last, List.concat_eq_append,
      List.append_assoc, Line.code, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt]
    congr 3
    rw [Line.eval]
    congr 1
    funext a
    simp [← List.getD_eq_getElem?_getD, Wire.getD_append_toNat]

/-- **Evaluation through the code.** Output `j` of a circuit is the value at the number of its
output wire after evaluating the gate list. -/
theorem Circuit.eval_eq_getD (c : Circuit σ n m) (I : Interpretation σ U) (d : U)
    (x : Fin n → U) (j : Fin m) :
    c.eval I x j = (evalCode I d (List.ofFn x) c.code.1).getD (c.outputs j).toNat d := by
  rw [Circuit.code, Program.evalCode_code, Wire.getD_append_toNat]
  rfl

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
