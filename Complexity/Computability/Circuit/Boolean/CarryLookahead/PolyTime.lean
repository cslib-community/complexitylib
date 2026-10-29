/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarryLookahead
public import Complexity.Computability.Circuit.Boolean.CodeTemplate
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Circuit.Boolean.EncodingSize
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of carry-lookahead circuit codes

All constructors return the actual binary gate-and-output encoding. Widths and loop counts are
unary; distances and wire references are binary. The prefix loop carries its already generated
code and appends one fixed-width round at a time. Bounds on the complete intermediate encoding
justify the loop, including tags, delimiters and output references.

## Main definitions

* `Cslib.Circuits.Boolean.CarryLookahead.neighbourIndex`,
  `Cslib.Circuits.Boolean.CarryLookahead.generateCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.propagateCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.stepCode`: one round on raw parameters.
* `Cslib.Circuits.Boolean.CarryLookahead.initialGenerateCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.initialPropagateCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.initialCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.sumCode`,
  `Cslib.Circuits.Boolean.CarryLookahead.finishCode`: initial generate/propagate, sum, and
  finishing codes.

## Main results

* `Cslib.Circuits.Boolean.CarryLookahead.stepCode_eq`: agreement with the typed round.
* `Cslib.Circuits.Boolean.computableInPolyTime_carryLookahead`: native generation of
  the complete adder code from unary width.
* `Cslib.Circuits.Boolean.computableInPolyTime_carryLookaheadAdd`,
  `computableInPolyTime_carryLookaheadFinish`: the modular and carry-save finishing codes.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace CarryLookahead

open Turing.MultiTapeTM ComputableInPolyTime

/-- The total raw neighbour rule used by the doubling layer. -/
def neighbourIndex (k distance i : ℕ) : ℕ := if i + distance < k then i + distance else i

private def generateTemplate : Formula signature 3 :=
  (Formula.input 0).or ((Formula.input 1).and (.input 2))

private def propagateTemplate : Formula signature 2 :=
  (Formula.input 0).and (.input 1)

/-- The generate cell's full code, also defined on out-of-range raw coordinates. -/
def generateCode (k distance i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode (k + k) ((Formula.input (n := 3) 0).or ((Formula.input 1).and (.input 2)))
    ![i, k + i, neighbourIndex k distance i]

/-- The propagate cell's full code. -/
def propagateCode (k distance i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode (k + k) ((Formula.input (n := 2) 0).and (.input 1))
    ![k + i, k + neighbourIndex k distance i]

private theorem generateCode_eq (k distance : ℕ) (i : Fin k) :
    generateCode k distance i.val = (generateFormula k distance i).toCircuit.code := by
  let wires : Fin 3 → Fin (k + k) :=
    ![Fin.castAdd k i, Fin.natAdd k i, Fin.castAdd k (neighbour k distance i)]
  have hw : (fun j => (wires j).val) = ![i.val, k + i.val, neighbourIndex k distance i.val] := by
    funext j
    by_cases h : distance + i.val < k <;>
      fin_cases j <;> simp [wires, neighbour, neighbourIndex, h, Nat.add_comm]
  have h := formulaCode_eq_code generateTemplate wires
  rw [hw] at h
  exact h

private theorem propagateCode_eq (k distance : ℕ) (i : Fin k) :
    propagateCode k distance i.val = (propagateFormula k distance i).toCircuit.code := by
  let wires : Fin 2 → Fin (k + k) := ![Fin.natAdd k i, Fin.natAdd k (neighbour k distance i)]
  have hw : (fun j => (wires j).val) = ![k + i.val, k + neighbourIndex k distance i.val] := by
    funext j
    by_cases h : distance + i.val < k <;>
      fin_cases j <;> simp [wires, neighbour, neighbourIndex, h, Nat.add_comm]
  have h := formulaCode_eq_code propagateTemplate wires
  rw [hw] at h
  exact h

private theorem generateCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {k distance i : α → ℕ} (hk : ComputableInPolyTime k enc encNat)
    (hd : ComputableInPolyTime distance enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => generateCode (k a) (distance a) (i a)) enc encCode := by
  apply computableInPolyTime_formulaCode _ (by fun_prop)
  intro j
  fin_cases j
  · exact hi
  · change ComputableInPolyTime (fun a => k a + i a) enc encNat
    fun_prop
  · change ComputableInPolyTime (fun a => neighbourIndex (k a) (distance a) (i a)) enc encNat
    unfold neighbourIndex
    fun_prop

private theorem propagateCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {k distance i : α → ℕ} (hk : ComputableInPolyTime k enc encNat)
    (hd : ComputableInPolyTime distance enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => propagateCode (k a) (distance a) (i a)) enc encCode := by
  apply computableInPolyTime_formulaCode _ (by fun_prop)
  intro j
  fin_cases j
  · change ComputableInPolyTime (fun a => k a + i a) enc encNat
    fun_prop
  · change ComputableInPolyTime
      (fun a => k a + neighbourIndex (k a) (distance a) (i a)) enc encNat
    unfold neighbourIndex
    fun_prop

/-- Bundle the fixed-size generate and propagate blocks of one doubling round. -/
def stepCode (k distance : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode (k + k)
    (bundleCode (k + k) 2 ((List.range k).map (generateCode k distance)))
    (bundleCode (k + k) 1 ((List.range k).map (propagateCode k distance)))

/-- The raw round is exactly the typed circuit's code, with no malformed-input assumption. -/
theorem stepCode_eq (k distance : ℕ) : stepCode k distance = (step k distance).code := by
  have hg : (List.range k).map (generateCode k distance) =
      List.ofFn (fun i : Fin k => (generateFormula k distance i).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simpa using generateCode_eq k distance ⟨i, by simpa using hi⟩
  have hp : (List.range k).map (propagateCode k distance) =
      List.ofFn (fun i : Fin k => (propagateFormula k distance i).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simpa using propagateCode_eq k distance ⟨i, by simpa using hi⟩
  rw [stepCode, hg, hp, bundleCode_code _ _ (by intro i; simp [generateFormula]),
    bundleCode_code _ _ (by intro i; simp [propagateFormula]), appendCode_code]
  rfl

/-- A doubling round is generated uniformly from a unary width and a binary distance. -/
theorem computableInPolyTime_stepCode {α : Type} {enc : α ↪ List Bool}
    {k distance : α → ℕ} (hk : ComputableInPolyTime k enc encUnary)
    (hd : ComputableInPolyTime distance enc encNat) :
    ComputableInPolyTime (fun a => stepCode (k a) (distance a)) enc encCode := by
  have hk' := unary_to_binary.comp hk
  have hn : ComputableInPolyTime (fun a => k a + k a) enc encNat := by fun_prop
  have hg : ComputableInPolyTime
      (fun p : α × ℕ => generateCode (k p.1) (distance p.1) p.2)
      (encPair enc encUnary) encCode :=
    generateCode_polyTime (hk'.comp (fst _ _)) (hd.comp (fst _ _))
      (unary_to_binary.comp (snd _ _))
  have hp : ComputableInPolyTime
      (fun p : α × ℕ => propagateCode (k p.1) (distance p.1) p.2)
      (encPair enc encUnary) encCode :=
    propagateCode_polyTime (hk'.comp (fst _ _)) (hd.comp (fst _ _))
      (unary_to_binary.comp (snd _ _))
  exact computableInPolyTime_appendCode hn
    (computableInPolyTime_bundleCode hn (const 2) (mapWithInput (range.comp hk) hg))
    (computableInPolyTime_bundleCode hn (const 1) (mapWithInput (range.comp hk) hp))

/-- Generate any number of doubling rounds from unary width and round count. The native loop
keeps the accumulated code and unary round counter, with polynomial intermediate encoded length. -/
theorem computableInPolyTime_scan :
    ComputableInPolyTime (fun p : ℕ × ℕ => (scan p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  let stateEnc := encPair encUnary encCode
  let init (k : ℕ) : ℕ × (List (Op × List ℕ) × List ℕ) := (0, ([], List.range (k + k)))
  let next (k : ℕ) (state : ℕ × (List (Op × List ℕ) × List ℕ)) :=
    (state.1 + 1, compCode (k + k) (stepCode k (2 ^ state.1)) state.2)
  have hn : ComputableInPolyTime
      (fun p : ℕ × (ℕ × (List (Op × List ℕ) × List ℕ)) => next p.1 p.2)
      (encPair encUnary stateEnc) stateEnc := by
    have hk := fst encUnary stateEnc
    have ht := (snd encUnary stateEnc).fst'
    have hc := (snd encUnary stateEnc).snd'
    have hd := binary_two_pow.comp ht
    have hk' := unary_to_binary.comp hk
    have ht' : ComputableInPolyTime
        (fun p : ℕ × (ℕ × (List (Op × List ℕ) × List ℕ)) => p.2.1 + 1)
        (encPair encUnary stateEnc) encUnary := by fun_prop
    exact ht'.prod (computableInPolyTime_compCode
      (by fun_prop) (computableInPolyTime_stepCode hk hd) hc)
  have hi : ComputableInPolyTime (fun p : ℕ × ℕ => init p.1)
      (encPair encUnary encUnary) stateEnc := by
    have hr := unary_to_binary.map.comp
      (range.comp (show ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.1)
        (encPair encUnary encUnary) encUnary from by fun_prop))
    simpa only [Function.comp_def, List.map_id_fun', id_eq, init] using
      (const (encOut := encUnary) 0).prod ((const (encOut := encList encGate) []).prod hr)
  have heq (k t : ℕ) : (next k)^[t] (init k) = (t, (scan k t).code) := by
    induction t with
    | zero => simp [init, scan]
    | succ t ih =>
      rw [Function.iterate_succ_apply' (f := next k), ih]
      simp only [next, stepCode_eq, compCode_code, scan]
  let bound (p : ℕ × ℕ) := 2 * p.2 + 1 +
    (2 * (3 * p.1 * p.2) * (23 + 8 * ((p.1 + p.1) + 3 * p.1 * p.2)) + 1 +
      (p.1 + p.1) * (2 * ((p.1 + p.1) + 3 * p.1 * p.2) + 1))
  have hb : PolyBounded (fun p : ℕ × ℕ => (encPair encUnary encUnary p).length) bound :=
    polyBounded (by unfold bound; fun_prop)
  have h := iterateWith (par := Prod.fst) (count := Prod.snd) (init := fun p => init p.1)
    (step := next) (fst _ _) (snd _ _) hi hn hb (fun p i hit => by
      rw [heq]
      have hsize : (scan p.1 i).size ≤ 3 * p.1 * p.2 := by
        rw [size_scan]
        exact Nat.mul_le_mul_left _ hit
      have hcode := length_encCode_le (scan p.1 i)
      have hbound : (encCode (scan p.1 i).code).length ≤
          2 * (3 * p.1 * p.2) * (23 + 8 * ((p.1 + p.1) + 3 * p.1 * p.2)) + 1 +
            (p.1 + p.1) * (2 * ((p.1 + p.1) + 3 * p.1 * p.2) + 1) :=
        hcode.trans (by gcongr)
      change (encPair encUnary encCode (i, (scan p.1 i).code)).length ≤ _
      rw [length_encPair]
      simp only [encUnary_apply, List.length_replicate]
      dsimp only [bound]
      omega)
  simpa only [Function.comp_def, heq] using h.snd'

/-- The generate gate of an initial cell, expressed as raw circuit data. -/
def initialGenerateCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  if i < w then ([(.and, [w - 1 - i, w + (w - 1 - i)])], [w + w + 1])
  else ([(.or, [w + w, w + w])], [w + w + 1])

/-- The propagate gate of an initial cell, expressed as raw circuit data. -/
def initialPropagateCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  if i < w then ([(.or, [w - 1 - i, w + (w - 1 - i)])], [w + w + 1])
  else ([(.const false, [])], [w + w + 1])

private theorem initialGenerateCode_eq (w : ℕ) (i : Fin (w + 1)) :
    initialGenerateCode w i.val = (initialGenerate w i).code := by
  unfold initialGenerateCode initialGenerate
  split <;> rfl

private theorem initialPropagateCode_eq (w : ℕ) (i : Fin (w + 1)) :
    initialPropagateCode w i.val = (initialPropagate w i).code := by
  unfold initialPropagateCode initialPropagate
  split <;> rfl

/-- The whole initial row, with one gate per generate or propagate cell. -/
def initialCode (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode (w + w + 1)
    (bundleCode (w + w + 1) 1 ((List.range (w + 1)).map (initialGenerateCode w)))
    (bundleCode (w + w + 1) 1 ((List.range (w + 1)).map (initialPropagateCode w)))

private theorem initialCode_eq (w : ℕ) : initialCode w = (initial w).code := by
  have hg : (List.range (w + 1)).map (initialGenerateCode w) =
      List.ofFn (fun i : Fin (w + 1) => (initialGenerate w i).code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      initialGenerateCode_eq w ⟨i, by simpa using hi⟩
  have hp : (List.range (w + 1)).map (initialPropagateCode w) =
      List.ofFn (fun i : Fin (w + 1) => (initialPropagate w i).code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      initialPropagateCode_eq w ⟨i, by simpa using hi⟩
  rw [initialCode, hg, hp, bundleCode_code _ _ (size_initialGenerate w),
    bundleCode_code _ _ (size_initialPropagate w), appendCode_code]
  rfl

/-- Native generation of the complete initial carry row from unary width. -/
theorem computableInPolyTime_initial :
    ComputableInPolyTime (fun w => (initial w).code) encUnary encCode := by
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => p.1)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : ℕ × ℕ => p.2)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (snd _ _)
  have hg : ComputableInPolyTime (fun p : ℕ × ℕ => initialGenerateCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by unfold initialGenerateCode; fun_prop
  have hp : ComputableInPolyTime (fun p : ℕ × ℕ => initialPropagateCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by unfold initialPropagateCode; fun_prop
  have hn : ComputableInPolyTime (fun w : ℕ => w + w + 1) encUnary encNat := by
    have h := unary_to_binary
    fun_prop
  have hr : ComputableInPolyTime (fun w : ℕ => List.range (w + 1))
      encUnary (encList encUnary) := by fun_prop
  have h := computableInPolyTime_appendCode hn
    (computableInPolyTime_bundleCode hn (const 1) (mapWithInput hr hg))
    (computableInPolyTime_bundleCode hn (const 1) (mapWithInput hr hp))
  simpa only [← initialCode_eq, initialCode] using h

/-- Native generation of all the input carries from unary word width. -/
theorem computableInPolyTime_carries :
    ComputableInPolyTime (fun w => (carries w).code) encUnary encCode := by
  have hw : ComputableInPolyTime (fun w : ℕ => w + 1) encUnary encUnary := by fun_prop
  have ht : ComputableInPolyTime (fun w : ℕ => Nat.clog 2 (w + 1)) encUnary encUnary := by
    fun_prop
  have hs := computableInPolyTime_scan.comp (hw.prod ht)
  have hn : ComputableInPolyTime (fun w : ℕ => w + w + 1) encUnary encNat := by
    have h := unary_to_binary
    fun_prop
  simpa only [Function.comp_def, compCode_code, carries] using
    computableInPolyTime_compCode hn hs computableInPolyTime_initial

private def sumTemplate : Formula signature 3 :=
  ((Formula.input 0).xor (.input 1)).xor (.input 2)

/-- The sum cell's raw code, using the original inputs and the reversed carry row. -/
def sumCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode ((w + w + 1) + ((w + 1) + (w + 1)))
    (((Formula.input (n := 3) 0).xor (.input 1)).xor (.input 2))
    ![i, w + i, (w + w + 1) + (w - i)]

private theorem sumCode_eq (w : ℕ) (i : Fin w) :
    sumCode w i.val = (sumFormula w i).toCircuit.code := by
  let wires : Fin 3 → Fin ((w + w + 1) + ((w + 1) + (w + 1))) :=
    ![Fin.castAdd ((w + 1) + (w + 1)) (leftInput w i),
      Fin.castAdd ((w + 1) + (w + 1)) (rightInput w i),
      Fin.natAdd (w + w + 1) ⟨w - i.val, by omega⟩]
  have hw : (fun j => (wires j).val) = ![i.val, w + i.val, (w + w + 1) + (w - i.val)] := by
    funext j
    fin_cases j <;> simp [wires, leftInput, rightInput, Nat.add_comm]
  have h := formulaCode_eq_code sumTemplate wires
  rw [hw] at h
  exact h

/-- The full final-output code, including the carry-out reference. -/
def finishCode (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode ((w + w + 1) + ((w + 1) + (w + 1)))
    (bundleCode ((w + w + 1) + ((w + 1) + (w + 1))) 15 ((List.range w).map (sumCode w)))
    ([], [w + w + 1])

private theorem finishCode_eq (w : ℕ) : finishCode w = (finish w).code := by
  have hs : (List.range w).map (sumCode w) =
      List.ofFn (fun i : Fin w => (sumFormula w i).toCircuit.code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
      sumCode_eq w ⟨i, by simpa using hi⟩
  rw [finishCode, hs, bundleCode_code _ _ (by intro i; simp)]
  have hc : ([], [w + w + 1]) =
      (Circuit.wiring signature (fun _ : Fin 1 =>
        (Fin.natAdd (w + w + 1) ⟨0, by omega⟩ :
          Fin ((w + w + 1) + ((w + 1) + (w + 1)))))).code := rfl
  rw [hc, appendCode_code]
  rfl

/-- Native generation of sum-bit and carry-out wiring from unary width. -/
theorem computableInPolyTime_finish :
    ComputableInPolyTime (fun w => (finish w).code) encUnary encCode := by
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => p.1)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : ℕ × ℕ => p.2)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (snd _ _)
  have hs : ComputableInPolyTime (fun p : ℕ × ℕ => sumCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    apply computableInPolyTime_formulaCode _ (by fun_prop)
    intro j
    fin_cases j
    · exact hi
    · change ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2) _ encNat
      fun_prop
    · change ComputableInPolyTime
        (fun p : ℕ × ℕ => (p.1 + p.1 + 1) + (p.1 - p.2)) _ encNat
      fun_prop
  have hw' := unary_to_binary
  have hn : ComputableInPolyTime
      (fun w : ℕ => (w + w + 1) + ((w + 1) + (w + 1))) encUnary encNat := by fun_prop
  have hc : ComputableInPolyTime (fun w : ℕ => ([], [w + w + 1]))
      encUnary encCode := by fun_prop
  have h := computableInPolyTime_appendCode hn
    (computableInPolyTime_bundleCode hn (const 15) (mapWithInput range hs)) hc
  simpa only [← finishCode_eq, finishCode] using h

/-- Identity-wire codes are generated from a unary input count, with binary output references. -/
private theorem computableInPolyTime_identityCode :
    ComputableInPolyTime
      (fun k => (Circuit.wiring signature (id : Fin k → Fin k)).code) encUnary encCode := by
  have h := (const (encOut := encList encGate) []).prod (unary_to_binary.map.comp range)
  simpa only [Circuit.code_wiring_id, Function.comp_def, List.map_id_fun', id_eq] using h

end CarryLookahead

open Turing.MultiTapeTM ComputableInPolyTime

/-- One native polynomial-time algorithm generates the entire logarithmic-depth adder code
from unary width. Every binary gate reference, output reference and framing bit is charged. -/
theorem computableInPolyTime_carryLookahead :
    ComputableInPolyTime (fun w => (carryLookahead w).code) encUnary encCode := by
  have hn : ComputableInPolyTime (fun w : ℕ => w + w + 1) encUnary encUnary := by fun_prop
  have hn' := unary_to_binary.comp hn
  have hi := CarryLookahead.computableInPolyTime_identityCode.comp hn
  have h := computableInPolyTime_compCode hn'
    CarryLookahead.computableInPolyTime_finish
    (computableInPolyTime_appendCode hn' hi CarryLookahead.computableInPolyTime_carries)
  simpa only [Function.comp_def, appendCode_code, compCode_code, carryLookahead] using h

/-- The modular adder is generated by the same uniform native algorithm plus free output wiring
and one hardwired carry gate. -/
theorem computableInPolyTime_carryLookaheadAdd :
    ComputableInPolyTime (fun w => (carryLookaheadAdd w).code) encUnary encCode := by
  have hn : ComputableInPolyTime (fun w : ℕ => w + w) encUnary encUnary := by fun_prop
  have hn' := unary_to_binary.comp hn
  have hi := CarryLookahead.computableInPolyTime_identityCode.comp hn
  have hz : ComputableInPolyTime
      (fun w => (Circuit.oneGate (σ := signature) (n := w + w) (.const false) Fin.elim0).code)
      encUnary encCode := by
    have h : ComputableInPolyTime (fun w : ℕ => ([(Op.const false, [])], [w + w]))
        encUnary encCode := (const [(Op.const false, [])]).prod (hn'.cons' (const []))
    exact h
  have ho : ComputableInPolyTime
      (fun w => (Circuit.wiring signature (fun i : Fin w => i.castSucc)).code)
      encUnary encCode := by
    have he (w : ℕ) : (Circuit.wiring signature (fun i : Fin w => i.castSucc)).code =
        ([], List.range w) := by
      simpa using Circuit.code_wiring_eq_map (σ := signature)
        (f := fun i : Fin w => i.castSucc) (g := id) fun _ => rfl
    have h := (const (encOut := encList encGate) []).prod (unary_to_binary.map.comp range)
    simpa only [he, Function.comp_def, List.map_id_fun', id_eq] using h
  have h := computableInPolyTime_compCode hn' ho
    (computableInPolyTime_compCode hn' computableInPolyTime_carryLookahead
      (computableInPolyTime_appendCode hn' hi hz))
  simpa only [Function.comp_def, appendCode_code, compCode_code, carryLookaheadAdd] using h

/-- Generate the complete carry-save finishing code, including its repeated zero output wires. -/
theorem computableInPolyTime_carryLookaheadFinish :
    ComputableInPolyTime (fun w => (carryLookaheadFinish w).code) encUnary encCode := by
  have hn : ComputableInPolyTime (fun w : ℕ => w + w) encUnary encNat := by fun_prop
  have hrep : ComputableInPolyTime (fun w : ℕ => List.replicate w (w + w))
      encUnary (encList encNat) := by fun_prop
  have hz : ComputableInPolyTime
      (fun w => ((Circuit.wiring signature (fun _ : Fin w => (0 : Fin 1))).comp
        (Circuit.oneGate (σ := signature) (n := w + w) (.const false) Fin.elim0)).code)
      encUnary encCode := by
    have he (w : ℕ) : ((Circuit.wiring signature (fun _ : Fin w => (0 : Fin 1))).comp
        (Circuit.oneGate (σ := signature) (n := w + w) (.const false) Fin.elim0)).code =
        ([(Op.const false, [])], List.replicate w (w + w)) := by
      apply Prod.ext
      · rfl
      change List.ofFn (fun _ : Fin w => w + w) = _
      simp
    simpa only [he] using (const [(Op.const false, [])]).prod hrep
  have h := computableInPolyTime_appendCode hn computableInPolyTime_carryLookaheadAdd hz
  simpa only [appendCode_code, carryLookaheadFinish] using h

end Cslib.Circuits.Boolean
