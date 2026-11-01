/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PopulationCount.PolyTime
import Complexity.Computability.Circuit.Boolean.EncodingSize
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of the threshold comparison

A unary-width loop generates the existing linear-size comparator, and binary digit selection
generates its constant threshold word. Together with the population-count generator these give
a native polynomial-time certificate for the full linear-size threshold circuit.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

namespace PopulationCount

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

end PopulationCount

/-- Generate the existing comparator's complete circuit code from unary word width. -/
theorem computableInPolyTime_leCircuit :
    ComputableInPolyTime (fun w => (leCircuit w).code) encUnary encCode := by
  let stateEnc := encPair encUnary encCode
  let init : ℕ × (List (Op × List ℕ) × List ℕ) := (0, ([(.const true, [])], [0]))
  let next (state : ℕ × (List (Op × List ℕ) × List ℕ)) :=
    (state.1 + 1, PopulationCount.comparisonStepCode state.1 state.2)
  have hn : ComputableInPolyTime next stateEnc stateEnc := by
    have hh : ComputableInPolyTime
        (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => p.1 + 1)
        stateEnc encUnary := by fun_prop
    exact hh.prod PopulationCount.comparisonStepCode_polyTime
  have heq (i : ℕ) : next^[i] init = (i, (leCircuit i).code) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [next, PopulationCount.comparisonStepCode_eq]
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

namespace PopulationCount

/-- The two constant gates and their selected output wires for a binary numeral. -/
def numeralCode (n w q : ℕ) : List (Op × List ℕ) × List ℕ :=
  ([(.const false, []), (.const true, [])],
    (List.range w).map (fun i => if q.testBit i then n + 1 else n))

private theorem numeralCode_eq (n w : ℕ) (q : Fin (2 ^ w)) :
    numeralCode n w q.val = (wordConstCircuit n ((BitString.equivFin w).symm q)).code := by
  have hw (i : Fin w) :
      ((wordConstCircuit n ((BitString.equivFin w).symm q)).outputs i).toNat =
        if q.val.testBit i.val then n + 1 else n := by
    dsimp only [wordConstCircuit, Circuit.comp, Circuit.wiring, Function.comp_apply,
      Program.appendedWire]
    rw [BitString.equivFin_symm_apply]
    cases q.val.testBit i.val <;> rfl
  apply Prod.ext
  · rfl
  · apply List.ext_getElem (by simp [numeralCode, Circuit.code])
    intro i hi hj
    simp only [numeralCode, List.getElem_map, List.getElem_range, Circuit.code,
      List.getElem_ofFn, hw]

private theorem numeralCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {n w q : α → ℕ} (hn : ComputableInPolyTime n enc encNat)
    (hw : ComputableInPolyTime w enc encUnary) (hq : ComputableInPolyTime q enc encNat) :
    ComputableInPolyTime (fun a => numeralCode (n a) (w a) (q a)) enc encCode := by
  have hi : ComputableInPolyTime
      (fun p : α × ℕ => if (q p.1).testBit p.2 then n p.1 + 1 else n p.1)
      (encPair enc encUnary) encNat := by
    have hn' := (hn.comp (fst enc encUnary)).tidy
    have hq' := (hq.comp (fst enc encUnary)).tidy
    have hi' := (snd enc encUnary).tidy
    have ht := ComputableTidilyInPolyTime.binary_testBit hq' hi'
    exact .of_tidy (ht.cond
      (ComputableTidilyInPolyTime.binary_add.comp
        (hn'.prod (ComputableTidilyInPolyTime.const 1))) hn')
  exact (const (encOut := encList encGate) [(Op.const false, []), (Op.const true, [])]).prod
    (mapWithInput (range.comp hw) hi)

end PopulationCount

/-- A native polynomial-time compiler for the whole linear-size threshold circuit. The number
of inputs and the cutoff are supplied in unary; all output circuit references are binary. -/
theorem computableInPolyTime_linearThresholdCircuit :
    ComputableInPolyTime (fun p : ℕ × ℕ => (linearThresholdCircuit p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  have hn := fst encUnary encUnary
  have hq := snd encUnary encUnary
  have hn' := unary_to_binary.comp hn
  have hq' := unary_to_binary.comp hq
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.clog 2 (p.1 + 1) + 1)
      (encPair encUnary encUnary) encUnary := by
    have hc := (unary_clog_const 2).comp
      (show ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + 1)
        (encPair encUnary encUnary) encUnary from by fun_prop)
    fun_prop
  have hp := computableInPolyTime_compCode hn' (computableInPolyTime_leCircuit.comp hw)
    (computableInPolyTime_appendCode hn'
      (PopulationCount.numeralCode_polyTime hn' hw hq')
      (computableInPolyTime_populationCountCircuit.comp hn))
  have hz : ComputableInPolyTime (fun p : ℕ × ℕ => ([(Op.const false, [])], [p.1]))
      (encPair encUnary encUnary) encCode := by fun_prop
  have ht : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.2 ≤ p.1))
      (encPair encUnary encUnary) encBool := by fun_prop
  have h := ite_decide ht hp hz
  apply h.of_enc_eq
  intro p
  dsimp only [linearThresholdCircuit, Function.comp_apply]
  split_ifs with hq
  · rw [← compCode_code, ← appendCode_code, ← PopulationCount.numeralCode_eq]
  · rfl

end Cslib.Circuits.Boolean
