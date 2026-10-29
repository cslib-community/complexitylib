/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CodeComposition
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Hardwiring a prefix of a Boolean circuit code

`prefixCode r n code` replaces the first `r.length` inputs by `r` and leaves `n` live inputs.
Two shared constant gates precede the original gates. The transformation is the raw code of
ordinary circuit composition, with exactly two additional gates. Its constructor runs in
polynomial time, with `n` in binary and all wire numbers in binary.

## Main definitions

* `Cslib.Circuits.Boolean.prefixWire`, `Cslib.Circuits.Boolean.prefixCode`: hardwiring a prefix of
  inputs on raw circuit codes.
* `Cslib.Circuits.Boolean.prefixInputs`, `Cslib.Circuits.Boolean.prefixCircuit`: the corresponding
  input substitution and typed circuit.

## Main results

* `Cslib.Circuits.Boolean.code_prefixCircuit`: the raw and typed constructions agree.
* `Cslib.Circuits.Boolean.eval_prefixCircuit`: hardwiring preserves evaluation.
* `Cslib.Circuits.Boolean.computableInPolyTime_prefixCode`: constructor efficiency.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean

/-- Map an old wire to a live suffix input, a shared constant, or a shifted gate. -/
def prefixWire (r : List Bool) (n i : ℕ) : ℕ :=
  if i < r.length then n + if r.getD i false then 1 else 0
  else if i < r.length + n then i - r.length else n + 2 + (i - (r.length + n))

/-- Hardwire a prefix, sharing two constant gates and retaining all original gates and outputs.
Malformed codes are transformed as data; correctness is asserted on codes of typed circuits. -/
def prefixCode (r : List Bool) (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  ([(.const false, []), (.const true, [])] ++
    code.1.map (fun g => (g.1, g.2.map (prefixWire r n))), code.2.map (prefixWire r n))

/-- Feed the fixed prefix bits followed by the live suffix inputs. -/
def prefixInputs (r : List Bool) (n : ℕ) : Fin (r.length + n) → Fin n ⊕ Bool :=
  Fin.append (fun i => .inr r[i.val]) Sum.inl

/-- Hardwire a prefix using the existing shared-constant substitution circuit. -/
def prefixCircuit {n m : ℕ} (r : List Bool) (c : Circuit signature (r.length + n) m) :
    Circuit signature n m := c.comp (substituteCircuit (prefixInputs r n))

private theorem toNat_outputs_substituteCircuit {n N : ℕ}
    (ρ : Fin N → Fin n ⊕ Bool) (i : Fin N) :
    ((substituteCircuit ρ).outputs i).toNat =
      (ρ i).elim Fin.val (fun b => n + if b then 1 else 0) := by
  cases h : ρ i with
  | inl j =>
    simp only [substituteCircuit, Circuit.comp, Circuit.wiring, Function.comp_apply, h,
      Sum.elim_inl, Program.appendedWire_input, Circuit.append]
    rw [Fin.append_left]
    rfl
  | inr b =>
    cases b <;> simp only [substituteCircuit, Circuit.comp, Circuit.wiring, Function.comp_apply, h,
      Sum.elim_inr, Program.appendedWire_input, Circuit.append]
    · rw [Fin.append_right]
      rfl
    · rw [Fin.append_right]
      rfl

private theorem prefixFeed_toNat (r : List Bool) (n : ℕ) (i : Fin (r.length + n)) :
    ((substituteCircuit (prefixInputs r n)).outputs i).toNat = prefixWire r n i.val := by
  rw [toNat_outputs_substituteCircuit]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [prefixInputs, Fin.append_left, Sum.elim_inr, prefixWire, Fin.val_castAdd,
      j.isLt, ↓reduceIte]
    simp only [List.getD_eq_getElem _ _ j.isLt]
  · simp [prefixInputs, prefixWire]

private theorem appendWireCode_prefixFeed (r : List Bool) (n i : ℕ) :
    Program.appendWireCode n (r.length + n) 2
      (substituteCircuit (prefixInputs r n)).outputs i = prefixWire r n i := by
  unfold Program.appendWireCode
  split_ifs with hi
  · exact prefixFeed_toNat r n ⟨i, hi⟩
  · simp only [prefixWire, show ¬i < r.length by omega, hi, ↓reduceIte]

/-- The raw hardwiring transformation is exactly the code of typed circuit composition. -/
theorem code_prefixCircuit {n m : ℕ} (r : List Bool)
    (c : Circuit signature (r.length + n) m) :
    (prefixCircuit r c).code = prefixCode r n c.code := by
  have hp : (substituteCircuit (prefixInputs r n)).program.code =
      [(Op.const false, []), (Op.const true, [])] := rfl
  apply Prod.ext
  · change ((substituteCircuit (prefixInputs r n)).program.append
      (substituteCircuit (prefixInputs r n)).outputs c.program).code = _
    rw [Program.code_append, hp]
    change [(Op.const false, []), (Op.const true, [])] ++
      c.program.code.map (fun g => (g.1, g.2.map
        (Program.appendWireCode n (r.length + n) 2
          (substituteCircuit (prefixInputs r n)).outputs))) = _
    have hren := funext (appendWireCode_prefixFeed r n)
    rw [hren]
    rfl
  · simp only [prefixCircuit, Circuit.comp, Circuit.code,
      prefixCode, List.map_ofFn, Function.comp_apply]
    congr 1
    funext i
    rw [Program.appendedWire_toNat]
    change Program.appendWireCode n (r.length + n) 2
      (substituteCircuit (prefixInputs r n)).outputs (c.outputs i).toNat = _
    exact appendWireCode_prefixFeed r n _

/-- Decoding the hardwired code produces the corresponding typed circuit. -/
@[simp] theorem ofCode_prefixCode {n m : ℕ} (r : List Bool)
    (c : Circuit signature (r.length + n) m) :
    Circuit.ofCode n m (prefixCode r n c.code) = some (prefixCircuit r c) := by
  rw [← code_prefixCircuit, Circuit.ofCode_code]

/-- A valid circuit code remains valid after hardwiring its input prefix. -/
theorem isSome_ofCode_prefixCode {n m : ℕ} (r : List Bool)
    (code : List (Op × List ℕ) × List ℕ)
    (h : (Circuit.ofCode (r.length + n) m code : Option (Circuit signature _ _)).isSome) :
    (Circuit.ofCode n m (prefixCode r n code) : Option (Circuit signature n m)).isSome := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  rw [← Circuit.code_of_ofCode_eq_some hc, ofCode_prefixCode]
  rfl

/-- Hardwiring a prefix supplies its bits before the live inputs. -/
@[simp] theorem eval_prefixCircuit {n m : ℕ} (r : List Bool)
    (c : Circuit signature (r.length + n) m) (x : Fin n → Bool) :
    (prefixCircuit r c).eval interpretation x =
      c.eval interpretation (Fin.append (fun i => r[i.val]) x) := by
  rw [prefixCircuit, Circuit.eval_comp, eval_substituteCircuit]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [substitute, prefixInputs]

/-- Reading the hardwired raw code's output wires gives the original circuit's outputs. -/
theorem evalOutputs_prefixCode {n m : ℕ} (r : List Bool)
    (c : Circuit signature (r.length + n) m) (x : Fin n → Bool) :
    (prefixCode r n c.code).2.map
        (evalOutput (List.ofFn x) (prefixCode r n c.code).1) =
      List.ofFn (c.eval interpretation (Fin.append (fun i => r[i.val]) x)) := by
  rw [← code_prefixCircuit, ← eval_prefixCircuit r c x]
  simp only [Circuit.code, List.map_ofFn]
  congr 1
  funext j
  exact ((prefixCircuit r c).eval_eq_evalOutput x j).symm

/-- Exactly two gates are added, even if the constants or all outputs are unused. -/
@[simp] theorem size_prefixCircuit {n m : ℕ} (r : List Bool)
    (c : Circuit signature (r.length + n) m) : (prefixCircuit r c).size = 2 + c.size := by
  simp [prefixCircuit]

/-- Hardwiring adds two gates and retains every designated output. -/
@[simp] theorem length_prefixCode (r : List Bool) (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) :
    (prefixCode r n code).1.length = 2 + code.1.length ∧
      (prefixCode r n code).2.length = code.2.length := by
  simp only [prefixCode, List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  exact ⟨trivial, trivial⟩

open Turing.MultiTapeTM ComputableInPolyTime

/-- Rewriting one wire is polynomial-time even when wire numbers and `n` are binary. -/
@[fun_prop] theorem computableInPolyTime_prefixWire {α : Type}
    {encIn : α ↪ List Bool} {r : α → List Bool} {n i : α → ℕ}
    (hr : ComputableInPolyTime r encIn encBits)
    (hn : ComputableInPolyTime n encIn encNat)
    (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun a => prefixWire (r a) (n a) (i a)) encIn encNat := by
  have hlen : ComputableInPolyTime (fun a => (r a).length) encIn encNat :=
    unary_to_binary.comp (length_bits.comp hr)
  have hbit : ComputableInPolyTime (fun a => (r a).getD (i a) false) encIn encBool :=
    listGetD_binary false hr hi
  unfold prefixWire
  fun_prop

/-- Construct hardwired raw codes in polynomial time, with binary live-input and wire counts. -/
@[fun_prop] theorem computableInPolyTime_prefixCode {α : Type}
    {encIn : α ↪ List Bool} {r : α → List Bool} {n : α → ℕ}
    {code : α → List (Op × List ℕ) × List ℕ}
    (hr : ComputableInPolyTime r encIn encBits)
    (hn : ComputableInPolyTime n encIn encNat)
    (hcode : ComputableInPolyTime code encIn encCode) :
    ComputableInPolyTime (fun a => prefixCode (r a) (n a) (code a)) encIn encCode := by
  have hwire : ComputableInPolyTime
      (fun p : α × ℕ => prefixWire (r p.1) (n p.1) p.2)
      (encPair encIn encNat) encNat := by fun_prop
  have hgate : ComputableInPolyTime
      (fun p : α × (Op × List ℕ) =>
        (p.2.1, p.2.2.map (prefixWire (r p.1) (n p.1))))
      (encPair encIn encGate) encGate :=
    ((snd encIn encGate).fst').prod
      (mapWithInput (snd encIn encGate).snd' (hwire.comp ((fst _ _).fst'.prod (snd _ _))))
  exact (listAppend' (const [(Op.const false, []), (Op.const true, [])])
    (mapWithInput hcode.fst' hgate)).prod (mapWithInput hcode.snd' hwire)

end Boolean
end Cslib.Circuits
