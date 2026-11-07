/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
import Mathlib.Data.List.GetD

/-!
# Evaluation of circuit codes

The signature and interpretation are arbitrary. Gate lists are evaluated in program order,
appending one value per gate. Missing arguments and out-of-range wire indices read a supplied
default. This total semantics agrees with typed circuit evaluation on actual circuit codes.
Runtime certificates belong to the interpretation-specific modules.

## Main definitions

* `evalCode`: total evaluation of a gate list.

## Main results

* `length_evalCode`, `prefix_evalCode`: the evaluator appends one value per gate.
* `getD_evalCode`: gate equations on well-formed codes.
* `Program.evalCode_code`: the input values followed by the complete program trace.
* `Circuit.eval_eq_getD`: typed circuit outputs are lookups in that trace.

These are original implementation lemmas for the existing circuit semantics.
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

end Cslib.Circuits
