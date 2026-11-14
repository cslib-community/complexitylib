/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of word comparison

A unary-width loop emits the existing linear-size word comparator, including all gates and
output references. This construction is shared by threshold circuits and support sampling.

## Main results

* `Cslib.Circuits.Boolean.computableInPolyTime_leCircuit`: native generation of `leCircuit`.

This certificate was extracted unchanged from the threshold compiler; it concerns uniform
construction, not the static description size or execution time of an offline compiler.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

private def comparisonStepCode (w : ℕ) (c : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (w + 1 + (w + 1)) leStep.code
    (appendCode (w + 1 + (w + 1))
      (compCode (w + 1 + (w + 1)) c
        ([], (List.range (w + w)).map (fun i => if i < w then i else i + 1)))
      ([], [w, w + 1 + w]))

private theorem comparisonStepCode_eq (w : ℕ) :
    comparisonStepCode w (leCircuit w).code = (leCircuit (w + 1)).code := by
  have hl (i : Fin (w + w)) :
      (lowBits w i).val = if i.val < w then i.val else i.val + 1 := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [lowBits, Fin.append_left, Fin.val_castAdd, Fin.val_castSucc]
      simp [i.isLt]
    · simp only [lowBits, Fin.append_right, Fin.val_natAdd, Fin.val_castSucc]
      rw [ite_eq_right (by omega)]
      omega
  have hcode := Circuit.code_wiring_eq_map (σ := signature) (f := lowBits w)
    (g := fun i => if i < w then i else i + 1) hl
  rw [leCircuit, ← compCode_code, ← appendCode_code, ← compCode_code, hcode]
  have ht : (Circuit.wiring signature (topBits w)).code = ([], [w, w + 1 + w]) := by
    simp [Circuit.code_wiring, topBits]
  rw [ht]
  rfl

private theorem comparisonStepCode_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => comparisonStepCode p.1 p.2)
      (encPair encUnary encCode) encCode := by
  have hw := fst encUnary encCode
  have hw' := unary_to_binary.comp hw
  have hn : ComputableInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => p.1 + 1 + (p.1 + 1))
      (encPair encUnary encCode) encNat := by fun_prop
  have hl : ComputableInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) =>
        ([], (List.range (p.1 + p.1)).map (fun i => if i < p.1 then i else i + 1)))
      (encPair encUnary encCode) encCode := by
    have hi : ComputableInPolyTime
        (fun p : (ℕ × (List (Op × List ℕ) × List ℕ)) × ℕ =>
          if p.2 < p.1.1 then p.2 else p.2 + 1)
        (encPair (encPair encUnary encCode) encUnary) encNat := by
      have hw'' := hw'.comp (fst (encPair encUnary encCode) encUnary)
      have hi' := unary_to_binary.comp (snd (encPair encUnary encCode) encUnary)
      fun_prop
    have hr : ComputableInPolyTime
        (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => List.range (p.1 + p.1))
        (encPair encUnary encCode) (encList encUnary) := by fun_prop
    exact (const (encOut := encList encGate) []).prod
      (mapWithInput (f := fun p i => if i < p.1 then i else i + 1) hr hi)
  have ht : ComputableInPolyTime
      (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => ([], [p.1, p.1 + 1 + p.1]))
      (encPair encUnary encCode) encCode := by fun_prop
  exact computableInPolyTime_compCode hn (const leStep.code)
    (computableInPolyTime_appendCode hn
      (computableInPolyTime_compCode hn (snd encUnary encCode) hl) ht)

/-- Generate the existing comparator's complete circuit code from unary word width. -/
theorem computableInPolyTime_leCircuit :
    ComputableInPolyTime (fun w => (leCircuit w).code) encUnary encCode := by
  let stateEnc := encPair encUnary encCode
  let init : ℕ × (List (Op × List ℕ) × List ℕ) := (0, ([(.const true, [])], [0]))
  let next (state : ℕ × (List (Op × List ℕ) × List ℕ)) :=
    (state.1 + 1, comparisonStepCode state.1 state.2)
  have hn : ComputableInPolyTime next stateEnc stateEnc := by
    have hh : ComputableInPolyTime
        (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => p.1 + 1)
        stateEnc encUnary := by fun_prop
    exact hh.prod comparisonStepCode_polyTime
  have heq (i : ℕ) : next^[i] init = (i, (leCircuit i).code) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [next, comparisonStepCode_eq]
  let bound (w : ℕ) := 1000 * (w + 1) ^ 2
  have hb : PolyBounded (fun w => (encUnary w).length) bound :=
    polyBounded (by unfold bound; fun_prop)
  have h := iterateWith (encPar := encUnary) (par := fun _ : ℕ => 0)
    (count := fun w => w) (init := fun _ => init) (step := fun _ => next)
    (const 0) id' (const init) (hn.comp (snd encUnary stateEnc)) hb (fun w i hi => by
      rw [heq]
      have hc := length_encCode_le (leCircuit i)
      rw [size_leCircuit] at hc
      change (encPair encUnary encCode (i, (leCircuit i).code)).length ≤ _
      rw [length_encPair]
      simp only [encUnary_apply, List.length_replicate]
      dsimp only [bound]
      nlinarith [Nat.pow_le_pow_left hi 2])
  simpa only [Function.comp_def, heq] using h.snd'

end Cslib.Circuits.Boolean
