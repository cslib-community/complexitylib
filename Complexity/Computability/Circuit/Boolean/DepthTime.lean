/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Depth

import Complexity.Foundations.Data.List.Lookup

/-!
# Computing the depths of a Boolean circuit

The ordinary code evaluator, interpreted over depths with unit gate cost, computes one depth
for every input and gate. Missing arguments and unavailable wires read zero, so the computation
is total even on malformed code. Each gate increases the largest available depth by at most
one; the bounds below therefore require no well-formedness premise.

The circuit depth takes the maximum only over the designated outputs. Unused gates, including
ones deeper than every output, do not change it. Native polynomial-time certificates, with
binary wire indices and unary computed depths, are in `Boolean.DepthTime.PolyTime`.

## Main definitions

* `Cslib.Circuits.Boolean.wireDepthsCode`: the input and gate depths, in wire-number order.
* `Cslib.Circuits.Boolean.depthCode`: the maximum designated-output depth.

## Main results

* `Cslib.Circuits.Boolean.wireDepthsCode_getD_toNat`: agreement with typed program depths.
* `Cslib.Circuits.Boolean.depthCode_code`: agreement with typed circuit depth.
* `Cslib.Circuits.Boolean.wireDepthsCode_le`, `Cslib.Circuits.Boolean.depthCode_le`:
  depths are bounded by the number of gates, even for malformed code.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n g m : ℕ}

/-- Compute every wire depth, with inputs first and gates in program order. A missing argument
or unavailable wire has depth zero. Every gate, including a constant, has unit cost. -/
def wireDepthsCode (inputCount : ℕ) (gates : List (Op × List ℕ)) : List ℕ :=
  evalCode (depthInterpretation (σ := signature) 1) 0 (List.replicate inputCount 0) gates

/-- The maximum depth of a designated output, with maximum zero for no outputs. -/
def depthCode (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) : ℕ :=
  code.2.foldl (fun depth i => max depth ((wireDepthsCode inputCount code.1).getD i 0)) 0

/-- The table has one entry for each input and gate. -/
@[simp] theorem length_wireDepthsCode (inputCount : ℕ) (gates : List (Op × List ℕ)) :
    (wireDepthsCode inputCount gates).length = inputCount + gates.length := by
  simp [wireDepthsCode]

/-- The raw table of a typed program lists its zero input depths and then its gate depths. -/
private theorem wireDepthsCode_code (p : Program signature n g) :
    wireDepthsCode n p.code = List.replicate n 0 ++ List.ofFn p.depths := by
  have h := p.evalCode_code (depthInterpretation 1) 0 (fun _ => 0)
  rw [← p.depthsWith_one]
  simpa only [wireDepthsCode, List.ofFn_const, Program.depthsWith] using h

/-- Looking up a typed wire in the raw table gives its program depth. -/
theorem wireDepthsCode_getD_toNat (p : Program signature n g) (w : Wire n g) :
    (wireDepthsCode n p.code).getD w.toNat 0 = p.wireDepths w := by
  rw [wireDepthsCode_code, ← List.ofFn_const]
  exact Wire.getD_append_toNat (fun _ => 0) p.depths 0 w

/-- Taking the maximum over exactly the designated outputs computes `Circuit.depth`. -/
theorem depthCode_code (c : Circuit signature n m) : depthCode n c.code = c.depth := by
  simp only [depthCode, Circuit.code, ← List.foldl_map, List.map_ofFn,
    Function.comp_def, wireDepthsCode_getD_toNat]
  rw [Circuit.depth, Fin.foldl_eq_finRange_foldl]
  rw [show List.ofFn (fun i => c.program.wireDepths (c.outputs i)) =
      (List.finRange m).map c.outputDepths from by
        simp [List.finRange, Circuit.outputDepths, Function.comp_def]]
  simp only [List.foldl_map]

private theorem depthInterpretation_le {op : Op} {values : Fin (signature.Arity op) → ℕ}
    {bound : ℕ} (h : ∀ i, values i ≤ bound) :
    depthInterpretation (σ := signature) 1 op values ≤ bound + 1 := by
  simp only [depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max, Pi.one_apply]
  exact Nat.add_le_add_right (Finset.sup_le fun i _ => h i) 1

/-- Every computed depth is at most the number of gates. No well-formedness is required. -/
theorem wireDepthsCode_le (inputCount : ℕ) (gates : List (Op × List ℕ)) :
    ∀ value ∈ wireDepthsCode inputCount gates, value ≤ gates.length := by
  induction gates using List.reverseRecOn with
  | nil => simp [wireDepthsCode, evalCode_nil (σ := signature)]
  | append_singleton gates gate ih =>
    intro value hvalue
    rw [wireDepthsCode, evalCode_append_singleton (σ := signature)] at hvalue
    simp only [List.mem_append, List.mem_singleton] at hvalue
    rcases hvalue with hvalue | rfl
    · exact (ih _ hvalue).trans (by simp)
    · simp only [List.length_append, List.length_singleton]
      apply depthInterpretation_le
      intro i
      cases gate.2[i.val]? with
      | none => exact Nat.zero_le _
      | some j => exact List.getD_le_of_forall_le ih j

/-- The depth returned by any raw table lookup is bounded, including an unavailable wire. -/
theorem getD_wireDepthsCode_le (inputCount : ℕ) (gates : List (Op × List ℕ)) (i : ℕ) :
    (wireDepthsCode inputCount gates).getD i 0 ≤ gates.length :=
  List.getD_le_of_forall_le (wireDepthsCode_le inputCount gates) i

/-- Even malformed output references cannot make the selected depth exceed the gate count. -/
theorem depthCode_le (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    depthCode inputCount code ≤ code.1.length := by
  unfold depthCode
  have hfold (outputs : List ℕ) (initial : ℕ) (h : initial ≤ code.1.length) :
      outputs.foldl (fun depth i => max depth ((wireDepthsCode inputCount code.1).getD i 0))
        initial ≤ code.1.length := by
    induction outputs generalizing initial with
    | nil => exact h
    | cons i outputs ih =>
      exact ih _ (max_le h (getD_wireDepthsCode_le inputCount code.1 i))
  exact hfold _ 0 (Nat.zero_le _)

end Cslib.Circuits.Boolean
