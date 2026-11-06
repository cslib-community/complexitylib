/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PopulationCount
public import Complexity.Computability.Circuit.Boolean.CarryLookahead.PolyTime
import Complexity.Computability.Circuit.Boolean.EncodingSize
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of linear-size threshold circuits

The population tree is generated one height at a time. Its state includes the current number
of leaves in unary as well as the complete circuit code. Only logarithmically many heights are
visited, and each intermediate tree has at most twice the requested number of leaves. Thus all
wire numbers, framing bits, and intermediate circuit descriptions have polynomial total length.

The resulting polynomial-time certificate concerns the actual gate-and-output encoding used
by the native circuit counter.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

namespace PopulationCount

/-- Combine two copies of a counter on `p` inputs, using an exact `w`-bit adder. -/
def treeStepCode (p w : ℕ) (c : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (p + p) (carryLookahead w).code
    (appendCode (p + p)
      (appendCode (p + p)
        (compCode (p + p) c ([], List.range p))
        (compCode (p + p) c ([], (List.range p).map (fun i => p + i))))
      ([(.const false, [])], [p + p]))

private theorem treeStepCode_eq (h : ℕ) :
    treeStepCode (2 ^ h) (h + 1) (tree h).code = (tree (h + 1)).code := by
  have hl : (Circuit.wiring signature (leftWire h)).code = ([], List.range (2 ^ h)) := by
    simpa using Circuit.code_wiring_eq_map (σ := signature) (f := leftWire h)
      (g := id) (fun _ => rfl)
  have hr : (Circuit.wiring signature (rightWire h)).code =
      ([], (List.range (2 ^ h)).map (fun i => 2 ^ h + i)) :=
    Circuit.code_wiring_eq_map (σ := signature) (f := rightWire h)
      (g := fun i => 2 ^ h + i) (fun _ => rfl)
  rw [tree, ← compCode_code, ← appendCode_code, ← appendCode_code,
    ← compCode_code, ← compCode_code, hl, hr]
  have hz : (Circuit.oneGate (σ := signature) (n := 2 ^ (h + 1))
      (.const false) Fin.elim0).code = ([(.const false, [])], [2 ^ (h + 1)]) := rfl
  rw [hz]
  simp only [treeStepCode, pow_succ, Nat.mul_two]

private theorem treeStepCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {p w : α → ℕ} {c : α → List (Op × List ℕ) × List ℕ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hw : ComputableInPolyTime w enc encUnary)
    (hc : ComputableInPolyTime c enc encCode) :
    ComputableInPolyTime (fun a => treeStepCode (p a) (w a) (c a)) enc encCode := by
  have hp' := unary_to_binary.comp hp
  have hn : ComputableInPolyTime (fun a => p a + p a) enc encNat := by fun_prop
  have hl : ComputableInPolyTime (fun a => ([], List.range (p a))) enc encCode := by
    have h := unary_to_binary.map.comp (range.comp hp)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const (encOut := encList encGate) []).prod h
  have hr : ComputableInPolyTime
      (fun a => ([], (List.range (p a)).map (fun i => p a + i))) enc encCode := by
    have hi : ComputableInPolyTime (fun a : α × ℕ => p a.1 + a.2)
        (encPair enc encUnary) encNat := by
      have hleft := hp'.comp (fst enc encUnary)
      have hright := unary_to_binary.comp (snd enc encUnary)
      fun_prop
    exact (const (encOut := encList encGate) []).prod (mapWithInput (range.comp hp) hi)
  have hz : ComputableInPolyTime
      (fun a => ([(Op.const false, [])], [p a + p a])) enc encCode := by fun_prop
  exact computableInPolyTime_compCode hn (computableInPolyTime_carryLookahead.comp hw)
    (computableInPolyTime_appendCode hn
      (computableInPolyTime_appendCode hn
        (computableInPolyTime_compCode hn hc hl)
        (computableInPolyTime_compCode hn hc hr)) hz)

/-- Generate the power-of-two tree selected by an arbitrary unary input count. -/
theorem computableInPolyTime_tree :
    ComputableInPolyTime (fun n => (tree (Nat.clog 2 (n + 1))).code) encUnary encCode := by
  let stateEnc := encPair (encPair encUnary encUnary) encCode
  let init : (ℕ × ℕ) × (List (Op × List ℕ) × List ℕ) := ((0, 1), ([], [0]))
  let next (state : (ℕ × ℕ) × (List (Op × List ℕ) × List ℕ)) :=
    ((state.1.1 + 1, state.1.2 + state.1.2),
      treeStepCode state.1.2 (state.1.1 + 1) state.2)
  have hn : ComputableInPolyTime next stateEnc stateEnc := by
    have hh := (fst (encPair encUnary encUnary) encCode).fst'
    have hp := (fst (encPair encUnary encUnary) encCode).snd'
    have hc := snd (encPair encUnary encUnary) encCode
    have hw : ComputableInPolyTime
        (fun a : (ℕ × ℕ) × (List (Op × List ℕ) × List ℕ) => a.1.1 + 1)
        stateEnc encUnary := by fun_prop
    have hp2 : ComputableInPolyTime
        (fun a : (ℕ × ℕ) × (List (Op × List ℕ) × List ℕ) => a.1.2 + a.1.2)
        stateEnc encUnary := by fun_prop
    exact (hw.prod hp2).prod (treeStepCode_polyTime hp hw hc)
  have heq (i : ℕ) : next^[i] init = ((i, 2 ^ i), (tree i).code) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [next, treeStepCode_eq, pow_succ, Nat.mul_two]
  have hcount : ComputableInPolyTime (fun n : ℕ => Nat.clog 2 (n + 1))
      encUnary encUnary := by
    exact (unary_clog_const 2).comp (by fun_prop)
  let bound (n : ℕ) := 5000000 * (n + 2) ^ 2
  have hb : PolyBounded (fun n => (encUnary n).length) bound :=
    polyBounded (by unfold bound; fun_prop)
  have h := iterateWith (encPar := encUnary) (par := fun _ : ℕ => 0)
    (count := fun n => Nat.clog 2 (n + 1)) (init := fun _ => init)
    (step := fun _ => next) (const 0) hcount (const init)
    (hn.comp (snd encUnary stateEnc)) hb (fun n i hi => by
      rw [heq]
      have hi' : i ≤ n + 1 := hi.trans (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le))
      have hp : 2 ^ i ≤ 2 * (n + 1) :=
        (Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hi).trans
          (Nat.pow_clog_le_mul Nat.one_lt_two (Nat.succ_ne_zero n))
      have hs : (tree i).size ≤ 462 * (n + 1) :=
        (size_tree_le i).trans (by nlinarith)
      have hiout : i + 1 ≤ n + 2 := by omega
      have hcode := length_encCode_le (tree i)
      have hbound : (encCode (tree i).code).length ≤
          2 * (462 * (n + 1)) * (23 + 8 * (2 * (n + 1) + 462 * (n + 1))) + 1 +
            (n + 2) * (2 * (2 * (n + 1) + 462 * (n + 1)) + 1) :=
        hcode.trans (by gcongr)
      change (encPair (encPair encUnary encUnary) encCode
        ((i, 2 ^ i), (tree i).code)).length ≤ _
      rw [length_encPair, length_encPair]
      simp only [encUnary_apply, List.length_replicate]
      dsimp only [bound]
      nlinarith)
  simpa only [Function.comp_def, heq] using h.snd'

private theorem pad_code (n m : ℕ) :
    (pad n m).code = ([(.const false, [])],
      (List.range m).map (fun i => if i < n then i else n)) := by
  have hw (i : Fin m) : ((pad n m).outputs i).toNat =
      if i.val < n then i.val else n := by
    dsimp only [pad, Circuit.comp, Circuit.wiring, Function.comp_apply,
      Program.appendedWire]
    split_ifs with hi
    · rw [Circuit.outputs_append_castAdd]
      rfl
    · rw [Circuit.outputs_append_natAdd]
      rfl
  apply Prod.ext
  · rfl
  · apply List.ext_getElem (by simp [pad, Circuit.code])
    intro i hi hj
    simp only [Circuit.code, List.getElem_ofFn, hw, List.getElem_map, List.getElem_range]

/-- Generate padding from unary input and output counts. -/
theorem computableInPolyTime_pad :
    ComputableInPolyTime (fun p : ℕ × ℕ => (pad p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  have hwire : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => if p.2 < p.1.1 then p.2 else p.1.1)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by
    have hn := unary_to_binary.comp ((fst (encPair encUnary encUnary) encUnary).fst')
    have hi := unary_to_binary.comp (snd (encPair encUnary encUnary) encUnary)
    fun_prop
  have h := (const (encOut := encList encGate) [(Op.const false, [])]).prod
    (mapWithInput (f := fun p i => if i < p.1 then i else p.1)
      (range.comp (snd encUnary encUnary)) hwire)
  simpa only [pad_code, Function.comp_def] using h

end PopulationCount

/-- The complete linear-size population-count circuit is generated in polynomial time from
its unary number of inputs. -/
theorem computableInPolyTime_populationCountCircuit :
    ComputableInPolyTime (fun n => (populationCountCircuit n).code) encUnary encCode := by
  have hn := unary_to_binary
  have hp : ComputableInPolyTime (fun n : ℕ => 2 ^ Nat.clog 2 (n + 1))
      encUnary encUnary := by
    apply unary_pow_clog_const
    fun_prop
  have hpad := PopulationCount.computableInPolyTime_pad.comp
    ((ComputableInPolyTime.id' (encIn := encUnary)).prod hp)
  have h := computableInPolyTime_compCode hn PopulationCount.computableInPolyTime_tree hpad
  simpa only [Function.comp_def, compCode_code, populationCountCircuit] using h

end Cslib.Circuits.Boolean
