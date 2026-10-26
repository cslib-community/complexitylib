/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.DepthTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time circuit depths

The raw depth computation uses binary wire indices, unary input count, and unary computed
depths. A prefix of `k` gates has `n + k` depth entries, all at most `k`, so its full framed
encoding has length at most `(n + k) * (2 * k + 1)`. This bound also holds on malformed code:
missing arguments and unavailable wires read zero. Binary lookups cap the index before
converting it to unary, so a large invalid index is charged only its binary encoded length.

## Main results

* `Cslib.Circuits.Boolean.computableInPolyTime_wireDepthsCode`: compute the entire table.
* `Cslib.Circuits.Boolean.computableInPolyTime_depthCode`: compute the maximum depth of
  the designated outputs, including their binary lookups.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableTidilyInPolyTime

private def gateDepth : Op × ℕ × ℕ → ℕ
  | (.const _, _, _) => 1
  | (.not, a, _) => a + 1
  | (.and, a, b) | (.or, a, b) => max a b + 1

private theorem depthInterpretation_eq_gateDepth (op : Op) (f : ℕ → ℕ) :
    (depthInterpretation (σ := signature) 1 op fun a => f a) = gateDepth (op, f 0, f 1) := by
  cases op <;> simp [depthInterpretation, gateDepth, Fin.foldl_succ]

private theorem computableTidilyInPolyTime_gateDepth :
    ComputableTidilyInPolyTime gateDepth (encPair encOp (encPair encUnary encUnary))
      encUnary := by
  let isConst : Op → Bool := fun op => match op with | .const _ => true | _ => false
  let isNot : Op → Bool := fun op => match op with | .not => true | _ => false
  have hc := (of_finite (encA := encOp) (encB := encBool) isConst).comp
    (fst encOp (encPair encUnary encUnary))
  have hn := (of_finite (encA := encOp) (encB := encBool) isNot).comp
    (fst encOp (encPair encUnary encUnary))
  have ha : ComputableTidilyInPolyTime (fun p : Op × ℕ × ℕ => p.2.1 + 1)
      (encPair encOp (encPair encUnary encUnary)) encUnary := by fun_prop
  have hab : ComputableTidilyInPolyTime (fun p : Op × ℕ × ℕ => max p.2.1 p.2.2 + 1)
      (encPair encOp (encPair encUnary encUnary)) encUnary := by fun_prop
  convert hc.cond (const 1) (hn.cond ha hab) using 1
  funext p
  rcases p with ⟨op, a, b⟩
  cases op <;> rfl

private theorem computableTidilyInPolyTime_depthStep :
    ComputableTidilyInPolyTime (fun p : List ℕ × (Op × List ℕ) =>
      p.1 ++ [depthInterpretation (σ := signature) 1 p.2.1 fun a =>
        p.2.2[a.val]?.elim 0 (p.1.getD · 0)])
      (encPair (encList encUnary) encGate) (encList encUnary) := by
  have hargs (i : ℕ) : ComputableTidilyInPolyTime (fun p : List ℕ × (Op × List ℕ) =>
      p.2.2[i]?.elim 0 (p.1.getD · 0)) (encPair (encList encUnary) encGate) encUnary :=
    optionElimWithInput (getElem? (snd _ _).snd' (const i)) (const 0)
      (listGetD_binary 0 (fst _ _).fst' (snd _ _))
  have hvalue := computableTidilyInPolyTime_gateDepth.comp
    ((snd (encList encUnary) encGate).fst'.prod ((hargs 0).prod (hargs 1)))
  have h := listAppend' (fst (encList encUnary) encGate) (cons' hvalue (const []))
  convert h using 1
  funext p
  rw [depthInterpretation_eq_gateDepth p.2.1 (fun i => p.2.2[i]?.elim 0 (p.1.getD · 0))]
  rfl

/-- Compute all wire depths, charging every unary depth and list delimiter. The gate code may
be malformed, and its wire indices retain their binary encoding. -/
@[fun_prop]
theorem computableInPolyTime_wireDepthsCode {α : Type} {input : α ↪ List Bool}
    {inputCount : α → ℕ} {gates : α → List (Op × List ℕ)}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hgates : ComputableInPolyTime gates input (encList encGate)) :
    ComputableInPolyTime (fun a => wireDepthsCode (inputCount a) (gates a))
      input (encList encUnary) := by
  have hn := hn.tidy
  have hgates := hgates.tidy
  refine .of_tidy ?_
  have hcount := (length_list encGate).comp hgates
  have hnPoly : PolyBounded (fun a => (input a).length) inputCount := by
    simpa only [encUnary_apply, List.length_replicate] using hn.polyBounded_length
  have hgPoly : PolyBounded (fun a => (input a).length) (fun a => (gates a).length) := by
    simpa only [encUnary_apply, List.length_replicate, Function.comp_def] using
      hcount.polyBounded_length
  apply foldl' hgates (replicate hn (const 0)) computableTidilyInPolyTime_depthStep
    ((hnPoly.add hgPoly).mul (((PolyBounded.const 2).mul hgPoly).add (.const 1)))
  intro a i hi
  change (encList encUnary (wireDepthsCode (inputCount a) ((gates a).take i))).length ≤
    (inputCount a + (gates a).length) * (2 * (gates a).length + 1)
  refine (length_encList_le encUnary _ (b := (gates a).length) fun value hvalue => ?_).trans ?_
  · simpa only [encUnary_apply, List.length_replicate] using
      (wireDepthsCode_le _ _ value hvalue).trans ((List.length_take_le _ _).trans hi)
  · rw [length_wireDepthsCode]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_left ((List.length_take_le _ _).trans hi) _)

/-- Compute the designated-output maximum. Both construction of the table and every binary
output lookup are charged; no validity or promised-depth hypothesis is needed. -/
@[fun_prop]
theorem computableInPolyTime_depthCode {α : Type} {input : α ↪ List Bool}
    {inputCount : α → ℕ} {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hcode : ComputableInPolyTime code input encCode) :
    ComputableInPolyTime (fun a => depthCode (inputCount a) (code a)) input encUnary := by
  have hn := hn.tidy
  have hcode := hcode.tidy
  refine .of_tidy ?_
  have htable := (computableInPolyTime_wireDepthsCode (.of_tidy hn) (.of_tidy hcode.fst')).tidy
  have hcount := (length_list encGate).comp hcode.fst'
  have hbound : PolyBounded (fun a => (input a).length) (fun a => (code a).1.length) := by
    simpa only [encUnary_apply, List.length_replicate, Function.comp_def] using
      hcount.polyBounded_length
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List ℕ × ℕ) × ℕ => max p.1.2 (p.1.1.getD p.2 0))
      (encPair (encPair (encList encUnary) encUnary) encNat) encUnary :=
    unary_max.comp ((fst _ _).snd'.prod (listGetD_binary 0 (fst _ _).fst' (snd _ _)))
  exact foldlWith_of_bounded_growth (encA := encNat) (encB := encUnary)
    (step := fun table depth i => max depth (table.getD i 0))
    htable hcode.snd' (const 0) hstep hbound
    (fun a state value _ => by
      simp only [encUnary_apply, List.length_replicate]
      have h := getD_wireDepthsCode_le (inputCount a) (code a).1 value
      omega)

end Cslib.Circuits.Boolean
