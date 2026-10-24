/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Basic
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Mathlib.Data.List.GetD

/-!
# The dual-rail translation of De Morgan circuits

A De Morgan circuit becomes a monotone circuit by computing, for every wire, both its value and
its negation [Goldschlager1977]. The monotone circuit (`Cslib.Circuits.Monotone.dualRail`) has
`2 n + 1` inputs: input `0` is the constant `true`, and the input `i` of the De Morgan circuit is
carried positively by input `2 i + 1` and negatively by input `2 i + 2` (`railBits`). Each gate is
replaced by two gates, carrying it positively and negatively: an AND gate by the AND of the
positive rails and the OR of the negative rails, an OR gate dually, a negation by copies of the
crossed rails (conjunctions with the constant `true` wire), and a constant by the constant and its
negation (`dualGates`). Every wire `w` of the De Morgan circuit is then carried by the wires
`2 w + 1` and `2 w + 2` (`railWire`), uniformly for inputs and gates, so the translation of a gate
depends on the gate alone, not on its position.

The translation works on gate lists (`dualCode`): it keeps well-formedness
(`isCodeFrom_dualCode`), and evaluating the translated list on the dual-rail inputs gives the
dual-rail values (`evalCode_dualCode`). The translated circuit computes the same function on the
dual-rail inputs (`eval_dualRail`) and has twice the size (`size_dualRail`).

## Main definitions

* `Cslib.Circuits.Monotone.railWire`, `Cslib.Circuits.Monotone.railBits`: the dual-rail wires and
  inputs.
* `Cslib.Circuits.Monotone.dualGates`, `Cslib.Circuits.Monotone.dualCode`: the translation of
  gates and gate lists.
* `Cslib.Circuits.Monotone.dualRail`: the dual-rail translation of a De Morgan circuit.

## Main results

* `Cslib.Circuits.Monotone.evalCode_dualCode`: the translated gate list computes the dual-rail
  values.
* `Cslib.Circuits.Monotone.eval_dualRail`: the translated circuit computes the same function.
* `Cslib.Circuits.Monotone.size_dualRail`: the translated circuit has twice the size.

## References

* [L. M. Goldschlager, *The monotone and planar circuit value problems are log space complete
  for P*][Goldschlager1977]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

/-! ### Dual-rail wires and inputs -/

/-- The wire carrying wire `w` positively (`b = true`), `2 w + 1`, or negatively, `2 w + 2`.
Wire `0` is the constant `true`. -/
def railWire (b : Bool) (w : ℕ) : ℕ := 2 * w + if b then 1 else 2

/-- The dual-rail values: the constant `true`, then each value followed by its negation. -/
def railBits (x : List Bool) : List Bool := true :: x.flatMap fun b => [b, !b]

@[simp] theorem length_railBits (x : List Bool) : (railBits x).length = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [railBits, List.length_cons, List.flatMap_cons] at ih ⊢
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem railBits_append (x : List Bool) (v : Bool) :
    railBits (x ++ [v]) = railBits x ++ [v, !v] := by
  simp [railBits]

@[simp] theorem getD_railBits_zero (x : List Bool) : (railBits x).getD 0 false = true := rfl

@[simp] theorem getElem_railBits_zero (x : List Bool) (h : 0 < (railBits x).length) :
    (railBits x)[0] = true := rfl

private theorem getD_flatMap_pair (x : List Bool) {w : ℕ} (hw : w < x.length) :
    (x.flatMap fun b => [b, !b]).getD (2 * w) false = x.getD w false ∧
      (x.flatMap fun b => [b, !b]).getD (2 * w + 1) false = !x.getD w false := by
  induction x generalizing w with
  | nil => simp at hw
  | cons b x ih =>
    rcases w with _ | w
    · simp
    · have := ih (w := w) (by simpa using hw)
      rw [List.flatMap_cons, show 2 * (w + 1) = 2 * w + 1 + 1 by omega,
        show 2 * w + 1 + 1 + 1 = 2 * w + 1 + 1 + 1 from rfl]
      simpa [List.getD_cons_succ] using this

/-- The positive rail of a value. -/
theorem getD_railBits_true (x : List Bool) {w : ℕ} (hw : w < x.length) :
    (railBits x).getD (railWire true w) false = x.getD w false := by
  simp only [railBits, railWire, ↓reduceIte, List.getD_cons_succ]
  exact (getD_flatMap_pair x hw).1

/-- The negative rail of a value. -/
theorem getD_railBits_false (x : List Bool) {w : ℕ} (hw : w < x.length) :
    (railBits x).getD (railWire false w) false = !x.getD w false := by
  simp only [railBits, railWire, Bool.false_eq_true, ↓reduceIte,
    show 2 * w + 2 = 2 * w + 1 + 1 from rfl, List.getD_cons_succ]
  exact (getD_flatMap_pair x hw).2

/-! ### Gates -/

/-- **The two monotone gates computing a De Morgan gate positively and negatively**, from its
operation and its wires `g.2`: an AND gate by the AND of the positive rails and the OR of the
negative rails, an OR gate dually, a negation by the crossed rails (each in a conjunction with the
constant `true` wire `0`), a constant by the constant and its negation. -/
def dualGates (g : Boolean.Op × List ℕ) : List (Op × List ℕ) :=
  match g.1 with
  | .const b => [(.const b, []), (.const (!b), [])]
  | .not => [(.and, [railWire false (g.2.getD 0 0), 0]), (.and, [railWire true (g.2.getD 0 0), 0])]
  | .and => [(.and, [railWire true (g.2.getD 0 0), railWire true (g.2.getD 1 0)]),
      (.or, [railWire false (g.2.getD 0 0), railWire false (g.2.getD 1 0)])]
  | .or => [(.or, [railWire true (g.2.getD 0 0), railWire true (g.2.getD 1 0)]),
      (.and, [railWire false (g.2.getD 0 0), railWire false (g.2.getD 1 0)])]

@[simp] theorem length_dualGates (g : Boolean.Op × List ℕ) : (dualGates g).length = 2 := by
  rcases g with ⟨_ | _ | _ | _, _⟩ <;> rfl

/-- **The dual-rail translation of a gate list**: each gate by its two monotone gates. -/
def dualCode (gates : List (Boolean.Op × List ℕ)) : List (Op × List ℕ) := gates.flatMap dualGates

@[simp] theorem length_dualCode (gates : List (Boolean.Op × List ℕ)) :
    (dualCode gates).length = 2 * gates.length := by
  induction gates with
  | nil => rfl
  | cons g gates ih => simp only [dualCode, List.flatMap_cons, List.length_append,
      length_dualGates, List.length_cons] at ih ⊢; omega

private theorem dualCode_append (gates gates' : List (Boolean.Op × List ℕ)) :
    dualCode (gates ++ gates') = dualCode gates ++ dualCode gates' :=
  List.flatMap_append

private theorem getD_lt_of_isCode {l : List ℕ} {B j : ℕ} (hj : j < l.length) (h : ∀ i ∈ l, i < B) :
    l.getD j 0 < B := by
  rw [List.getD_eq_getElem _ _ hj]
  exact h _ (List.getElem_mem hj)

private theorem isCodeFrom_pair {N K : ℕ} {o₁ o₂ : Op} {l₁ l₂ : List ℕ}
    (h₁ : l₁.length = signature.Arity o₁) (h₂ : l₂.length = signature.Arity o₂)
    (hl₁ : ∀ i ∈ l₁, i < N + K) (hl₂ : ∀ i ∈ l₂, i < N + K) :
    Program.IsCodeFrom signature N K [(o₁, l₁), (o₂, l₂)] :=
  ⟨⟨h₁, hl₁⟩, ⟨h₂, fun i hi => (hl₂ i hi).trans_le (by omega)⟩, trivial⟩

/-- **The translation keeps well-formedness**: the gates of a De Morgan gate list reading the
first `n + k` wires become gates reading the first `2 n + 1 + 2 k` wires. -/
theorem isCodeFrom_dualCode {n : ℕ} :
    ∀ {k : ℕ} {gates : List (Boolean.Op × List ℕ)},
      Program.IsCodeFrom Boolean.signature n k gates →
        Program.IsCodeFrom signature (2 * n + 1) (2 * k) (dualCode gates)
  | _, [], _ => trivial
  | k, g :: gates, h => by
    obtain ⟨⟨hlen, hlt⟩, hrest⟩ := h
    rw [show dualCode (g :: gates) = dualGates g ++ dualCode gates from rfl,
      Program.isCodeFrom_append, length_dualGates]
    refine ⟨?_, by simpa [Nat.mul_add] using isCodeFrom_dualCode hrest⟩
    have hw (j : ℕ) (hj : j < g.2.length) : g.2.getD j 0 < n + k := getD_lt_of_isCode hj hlt
    rcases g with ⟨_ | _ | _ | _, args⟩ <;> simp only at hlen hw
    · exact isCodeFrom_pair rfl rfl (by simp) (by simp)
    · have h₀ := hw 0 (by omega)
      exact isCodeFrom_pair rfl rfl (by
          simp only [railWire, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)
        (by
          simp only [railWire, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)
    · have h₀ := hw 0 (by omega)
      have h₁ := hw 1 (by omega)
      exact isCodeFrom_pair rfl rfl (by
          simp only [railWire, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)
        (by
          simp only [railWire, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)
    · have h₀ := hw 0 (by omega)
      have h₁ := hw 1 (by omega)
      exact isCodeFrom_pair rfl rfl (by
          simp only [railWire, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)
        (by
          simp only [railWire, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)

/-- Evaluating two gates, the second reading only wires computed before the first. -/
private theorem evalCode_pair {σ : Signature} {U : Type*} (I : Interpretation σ U)
    (d : U) (vs : List U)
    (g₁ g₂ : σ.Op × List ℕ) (h₂ : ∀ i ∈ g₂.2, i < vs.length) :
    evalCode I d vs [g₁, g₂] = vs ++ [I g₁.1 fun a => g₁.2[a.val]?.elim d (vs.getD · d),
      I g₂.1 fun a => g₂.2[a.val]?.elim d (vs.getD · d)] := by
  rw [show [g₁, g₂] = [g₁] ++ [g₂] from rfl, evalCode_append_singleton,
    show [g₁] = [] ++ [g₁] from rfl, evalCode_append_singleton, evalCode_nil]
  have hv : (fun a : Fin (σ.Arity g₂.1) => g₂.2[a.val]?.elim d
      ((vs ++ [I g₁.1 fun a => g₁.2[a.val]?.elim d (vs.getD · d)]).getD · d)) =
      fun a => g₂.2[a.val]?.elim d (vs.getD · d) := by
    funext a
    rcases ha : g₂.2[a.val]? with _ | i
    · rfl
    · simp only [Option.elim]
      rw [List.getD_append _ _ _ _ (h₂ i (List.mem_of_getElem? ha))]
  rw [hv]
  simp

/-- **The translated gate list computes the dual-rail values**: on the dual-rail inputs, the
gates translating gate `j` carry the value of gate `j` and its negation. -/
theorem evalCode_dualCode (x : List Bool) {gates : List (Boolean.Op × List ℕ)}
    (h : Program.IsCodeFrom Boolean.signature x.length 0 gates) :
    evalCode interpretation false (railBits x) (dualCode gates) =
      railBits (evalCode Boolean.interpretation false x gates) := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates g ih =>
    rw [Program.isCodeFrom_append] at h
    obtain ⟨hgates, ⟨⟨hlen, hlt⟩, -⟩⟩ := h
    rw [dualCode_append, evalCode_append, ih hgates, evalCode_append_singleton, railBits_append]
    set vs := evalCode Boolean.interpretation false x gates with hvs
    have hlv : vs.length = x.length + gates.length := length_evalCode _ _ _ _
    have hw (j : ℕ) (hj : j < g.2.length) : g.2.getD j 0 < vs.length := by
      have := getD_lt_of_isCode hj hlt
      omega
    have hlr : (railBits vs).length = 2 * vs.length + 1 := length_railBits vs
    rw [show dualCode [g] = dualGates g by simp [dualCode]]
    rcases g with ⟨_ | _ | _ | _, args⟩ <;> simp only at hlen hw
    · obtain rfl : args = [] := List.length_eq_zero_iff.1 hlen
      simp only [dualGates]
      rw [evalCode_pair _ _ _ _ _ (by simp)]
      simp [interpretation, Boolean.interpretation]
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
      have ha : a < vs.length := by simpa using hw 0 (by simp)
      have hTa := getD_railBits_true vs ha
      have hFa := getD_railBits_false vs ha
      simp only [dualGates, List.getD_cons_zero]
      rw [evalCode_pair _ _ _ _ _ (by
          simp only [railWire, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)]
      simp only [List.getD_eq_getElem?_getD] at hTa hFa
      simp [interpretation, Boolean.interpretation, hTa, hFa]
    · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
      have ha : a < vs.length := by simpa using hw 0 (by simp)
      have hb : b < vs.length := by simpa using hw 1 (by simp)
      have hTa := getD_railBits_true vs ha
      have hFa := getD_railBits_false vs ha
      have hTb := getD_railBits_true vs hb
      have hFb := getD_railBits_false vs hb
      simp only [dualGates, List.getD_cons_zero, List.getD_cons_succ]
      rw [evalCode_pair _ _ _ _ _ (by
          simp only [railWire, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)]
      simp only [List.getD_eq_getElem?_getD] at hTa hFa hTb hFb
      simp [interpretation, Boolean.interpretation, hTa, hFa, hTb, hFb]
    · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
      have ha : a < vs.length := by simpa using hw 0 (by simp)
      have hb : b < vs.length := by simpa using hw 1 (by simp)
      have hTa := getD_railBits_true vs ha
      have hFa := getD_railBits_false vs ha
      have hTb := getD_railBits_true vs hb
      have hFb := getD_railBits_false vs hb
      simp only [dualGates, List.getD_cons_zero, List.getD_cons_succ]
      rw [evalCode_pair _ _ _ _ _ (by
          simp only [railWire, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
            List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          omega)]
      simp only [List.getD_eq_getElem?_getD] at hTa hFa hTb hFb
      simp [interpretation, Boolean.interpretation, hTa, hFa, hTb, hFb]

/-! ### Circuits -/

section Circuit

variable {n m : ℕ}

/-- The dual-rail inputs of an input of a De Morgan circuit (`railBits`). -/
def railBitString (x : BitString n) : BitString (2 * n + 1) :=
  fun i => (railBits (List.ofFn x)).getD i false

theorem ofFn_railBitString (x : BitString n) :
    List.ofFn (railBitString x) = railBits (List.ofFn x) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ h₂

private theorem isCodeFrom_code_fst {σ : Signature} (c : Circuit σ n m) :
    Program.IsCodeFrom σ n 0 c.code.1 :=
  Program.isSome_ofCode_iff.1 (by rw [Circuit.code, Program.ofCode_code]; rfl)

theorem isSome_ofCode_dualRail (c : Circuit Boolean.signature n m) :
    (Circuit.ofCode (2 * n + 1) m (dualCode c.code.1, c.code.2.map (railWire true)) :
      Option (Circuit signature (2 * n + 1) m)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_dualCode (isCodeFrom_code_fst c), by simp [Circuit.code], fun i hi => ?_⟩
  simp only [Circuit.code, List.mem_map, List.mem_ofFn] at hi
  obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hi
  have := (c.outputs j).toNat_lt
  have hl := Circuit.length_code_fst c
  simp only [length_dualCode, railWire, ↓reduceIte]
  omega

/-- **The dual-rail translation of a De Morgan circuit**: a monotone circuit on the `2 n + 1`
dual-rail inputs with two gates for every gate. -/
def dualRail (c : Circuit Boolean.signature n m) : Circuit signature (2 * n + 1) m :=
  (Circuit.ofCode (2 * n + 1) m (dualCode c.code.1, c.code.2.map (railWire true))).get
    (isSome_ofCode_dualRail c)

theorem code_dualRail (c : Circuit Boolean.signature n m) :
    (dualRail c).code = (dualCode c.code.1, c.code.2.map (railWire true)) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- The dual-rail translation has twice the size. -/
theorem size_dualRail (c : Circuit Boolean.signature n m) : (dualRail c).size = 2 * c.size := by
  rw [← Circuit.length_code_fst, code_dualRail, length_dualCode, Circuit.length_code_fst]

private theorem toNat_outputs_dualRail (c : Circuit Boolean.signature n m) (j : Fin m) :
    ((dualRail c).outputs j).toNat = railWire true (c.outputs j).toNat := by
  have h := congrArg Prod.snd (code_dualRail c)
  simp only [Circuit.code] at h
  have := congrArg (fun l => l[j.val]?) h
  simpa using this

/-- **The dual-rail translation computes the same function** on the dual-rail inputs. -/
theorem eval_dualRail (c : Circuit Boolean.signature n m) (x : BitString n) (j : Fin m) :
    (dualRail c).eval interpretation (railBitString x) j = c.eval Boolean.interpretation x j := by
  rw [Circuit.eval_eq_getD _ _ false, Circuit.eval_eq_getD _ _ false, code_dualRail,
    toNat_outputs_dualRail, ofFn_railBitString]
  have hc : Program.IsCodeFrom Boolean.signature (List.ofFn x).length 0 c.code.1 := by
    simpa using isCodeFrom_code_fst c
  rw [evalCode_dualCode _ hc]
  apply getD_railBits_true
  have := (c.outputs j).toNat_lt
  have hl := Circuit.length_code_fst c
  simp only [length_evalCode, List.length_ofFn]
  omega

end Circuit

end Cslib.Circuits.Monotone
