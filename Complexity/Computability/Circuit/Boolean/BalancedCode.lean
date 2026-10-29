/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Balanced
public import Complexity.Computability.Circuit.Boolean.CodeComposition
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native codes for the existing half-split balanced circuit

The constructor keeps the exact `Circuit.balanced` topology, including the order of gate blocks.
Its private dynamic program fills contiguous-interval rows in increasing interval length.
The loop count is the length of the complete leaf-code list, never a binary arity parameter.

## Main definitions

* `Cslib.Circuits.Boolean.balancedCode`: the complete raw code of a balanced circuit.

## Main results

* `Cslib.Circuits.Boolean.balancedCode_eq_code`: exact agreement with `Circuit.balanced`.
* `Cslib.Circuits.Boolean.computableInPolyTime_balancedCode`: uniform construction from
  binary input arity and native generators of the complete operator, fallback and leaf codes.

The resource proof counts all gates, gate arguments and outputs, including dead gates, and
controls the binary lengths of wire references. Thus an arbitrarily large unused input arity
does not become a unary resource bound. Every stored interval, invalid-interval fallback, row
and table frame is charged; the captured input is charged by the native loop combinator.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

private def intervalRow (n : ℕ) (op unit : Code) (leaves : List Code)
    (rows : List (List Code)) : List Code :=
  (List.range (leaves.length + 1)).map fun start =>
    if rows.length = 1 then leaves.getD start unit
    else if start + rows.length ≤ leaves.length then
      compCode n op (appendCode n
        ((rows.getD (rows.length / 2) []).getD start unit)
        ((rows.getD (rows.length - rows.length / 2) []).getD
          (start + rows.length / 2) unit))
    else unit

private def intervalTables (n : ℕ) (op unit : Code) (leaves : List Code) (count : ℕ) :
    List (List Code) :=
  (fun rows => rows ++ [intervalRow n op unit leaves rows])^[count]
    [List.replicate (leaves.length + 1) unit]

/-- Generate the exact half-split code on shared inputs. The supplied fallback is returned only
for an empty leaf list. Malformed codes are transformed as data, without arity-sized loops. -/
@[expose] def balancedCode (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : List (Op × List ℕ) × List ℕ :=
  private_decl% ((intervalTables n op unit leaves leaves.length).getD leaves.length []).getD 0 unit

private theorem length_intervalTables (n : ℕ) (op unit : Code) (leaves : List Code) (count : ℕ) :
    (intervalTables n op unit leaves count).length = count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [intervalTables, Function.iterate_succ_apply', List.length_append,
      List.length_cons, List.length_nil]
    simpa only [intervalTables] using congrArg (· + 1) ih

private def referenceCode (n : ℕ) (op unit : Code) (leaves : List Code) : Code :=
  leaves.balancedFold (fun c d => compCode n op (appendCode n c d)) unit id

-- Count all gates, gate arguments and outputs, even for malformed codes and dead gates.
private def codeMass (c : Code) : ℕ :=
  (c.1.map fun gate => gate.2.length + 1).sum + c.2.length

private def WireBitsLe (c : Code) (bound : ℕ) : Prop :=
  (∀ gate ∈ c.1, ∀ wire ∈ gate.2, (encNat wire).length ≤ bound) ∧
    ∀ wire ∈ c.2, (encNat wire).length ≤ bound

private theorem length_encoding_member {α : Type} (enc : α ↪ List Bool)
    {values : List α} {value : α} (h : value ∈ values) :
    (enc value).length ≤ (encList enc values).length := by
  induction values with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · rw [length_encList]
      simp only [List.map_cons, List.sum_cons]
      omega
    · have := ih ht
      rw [length_encList] at this ⊢
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem codeMass_le_encoding (c : Code) : codeMass c ≤ (encCode c).length := by
  have hg : (c.1.map fun gate => gate.2.length + 1).sum ≤ (encList encGate c.1).length := by
    rw [length_encList]
    apply List.sum_le_sum
    intro gate _
    have := length_le_length_encList encNat gate.2
    simp only [encGate, Circuit.encGate, length_encPair]
    omega
  have ho := length_le_length_encList encNat c.2
  simp only [codeMass, encCode, Circuit.encCode, encGate, length_encPair] at hg ⊢
  omega

private theorem wireBitsLe_encoding (c : Code) : WireBitsLe c (encCode c).length := by
  constructor
  · intro gate hg wire hw
    have ha := length_encoding_member encNat hw
    have hb := length_encoding_member encGate hg
    rw [show (encGate gate).length =
      2 * (encOp gate.1).length + 1 + (encList encNat gate.2).length from length_encPair gate] at hb
    rw [show (encCode c).length =
      2 * (encList encGate c.1).length + 1 + (encList encNat c.2).length from length_encPair c]
    omega
  · intro wire hw
    have := length_encoding_member encNat hw
    simp only [encCode, length_encPair]
    omega

private theorem codeMass_append (n : ℕ) (c d : Code) :
    codeMass (appendCode n c d) = codeMass c + codeMass d := by
  simp [codeMass, appendCode, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

private theorem codeMass_comp_le (n : ℕ) (d c : Code) :
    codeMass (compCode n d c) ≤ codeMass c + codeMass d := by
  simp only [codeMass, compCode, List.map_append, List.map_map, Function.comp_def,
    List.length_map, List.sum_append]
  omega

private theorem gates_le_codeMass (c : Code) : c.1.length ≤ codeMass c := by
  have h : c.1.length ≤ (c.1.map fun gate => gate.2.length + 1).sum := by
    induction c.1 with
    | nil => simp
    | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  exact h.trans (Nat.le_add_right _ _)

private theorem wireBitsLe_mono {c : Code} {a b : ℕ} (h : WireBitsLe c a) (hab : a ≤ b) :
    WireBitsLe c b :=
  ⟨fun g hg i hi => (h.1 g hg i hi).trans hab, fun i hi => (h.2 i hi).trans hab⟩

private theorem shiftCodeWire_bits (n offset wire bound : ℕ)
    (h : (encNat wire).length ≤ bound) :
    (encNat (shiftCodeWire n offset wire)).length ≤ bound + offset := by
  unfold shiftCodeWire
  split
  · omega
  · induction offset with
    | zero => simpa using h
    | succ k ih =>
      have hsize : (wire + k + 1).size ≤ (wire + k).size + 1 := by
        refine Nat.size_le.mpr ?_
        rw [pow_succ]
        have := Nat.lt_size_self (wire + k)
        have := Nat.one_le_two_pow (n := (wire + k).size)
        omega
      rw [← Nat.add_assoc, length_encNat_eq_size]
      rw [length_encNat_eq_size] at ih
      omega

private theorem wireBitsLe_append (n : ℕ) {c d : Code} {a b : ℕ}
    (hc : WireBitsLe c a) (hd : WireBitsLe d b) :
    WireBitsLe (appendCode n c d) (a + b + codeMass c) := by
  constructor
  · intro gate hg wire hw
    rcases List.mem_append.mp hg with hg | hg
    · exact (hc.1 gate hg wire hw).trans (by omega)
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact (shiftCodeWire_bits n _ i b (hd.1 g hmem i hi)).trans
        (by have := gates_le_codeMass c; omega)
  · intro wire hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (hc.2 wire hw).trans (by omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact (shiftCodeWire_bits n _ i b (hd.2 i hi)).trans
        (by have := gates_le_codeMass c; omega)

private theorem compCodeWire_bits (n : ℕ) {c : Code} {wire a b : ℕ}
    (hc : WireBitsLe c a) (hi : (encNat wire).length ≤ b) :
    (encNat (compCodeWire n c wire)).length ≤
      a + b + (encNat n).length + codeMass c + 2 := by
  unfold compCodeWire
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ h]
    exact (hc.2 _ (List.getElem_mem h)).trans (by omega)
  · have hsub : (encNat (wire - c.2.length)).length ≤ b := by
      refine (?_ : (encNat (wire - c.2.length)).length ≤ (encNat wire).length).trans hi
      simpa only [length_encNat_eq_size] using Nat.size_le_size (Nat.sub_le wire c.2.length)
    have hgate := (length_encNat_le_self c.1.length).trans (gates_le_codeMass c)
    have hsum := length_encNat_add_le_add n c.1.length
    have htotal := length_encNat_add_le_add (n + c.1.length) (wire - c.2.length)
    omega

private theorem wireBitsLe_comp (n : ℕ) {d c : Code} {a b : ℕ}
    (hc : WireBitsLe c a) (hd : WireBitsLe d b) :
    WireBitsLe (compCode n d c) (a + b + (encNat n).length + codeMass c + 2) := by
  constructor
  · intro gate hg wire hw
    rcases List.mem_append.mp hg with hg | hg
    · exact (hc.1 gate hg wire hw).trans (by omega)
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact compCodeWire_bits n hc (hd.1 g hmem i hi)
  · intro wire hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact compCodeWire_bits n hc (hd.2 i hi)

private theorem referenceCode_bounds (n : ℕ) (op unit : Code) (leaves : List Code) (k B : ℕ)
    (hop : codeMass op ≤ B) (hopBits : WireBitsLe op B)
    (hk : leaves.length ≤ k)
    (hcodes : ∀ c ∈ leaves, codeMass c ≤ B ∧ WireBitsLe c B) (hne : leaves ≠ []) :
    codeMass (referenceCode n op unit leaves) ≤ (2 * leaves.length - 1) * B ∧
      WireBitsLe (referenceCode n op unit leaves)
        ((2 * leaves.length - 1) * (B + (encNat n).length + 3 * ((2 * k + 1) * B) + 2)) := by
  let M := (2 * k + 1) * B
  let D := B + (encNat n).length + 3 * M + 2
  change codeMass (leaves.balancedFold _ unit id) ≤ _ ∧
    WireBitsLe (leaves.balancedFold _ unit id) ((2 * leaves.length - 1) * D)
  refine List.balancedFold_induction
    (p := fun l c => l.length ≤ k →
      (∀ a ∈ l, codeMass a ≤ B ∧ WireBitsLe a B) → l ≠ [] →
      codeMass c ≤ (2 * l.length - 1) * B ∧ WireBitsLe c ((2 * l.length - 1) * D))
    (fun _ _ h => (h rfl).elim) ?_ ?_ leaves hk hcodes hne
  · intro c _ hc _
    have h := hc c (by simp)
    simpa only [List.length_singleton, Nat.reduceMul, Nat.reduceSub, one_mul] using
      ⟨h.1, wireBitsLe_mono h.2 (by dsimp [D]; omega)⟩
  · intro left right c d hleft hright ihleft ihright hlength hc _
    have hlpos := List.length_pos_iff.mpr hleft
    have hrpos := List.length_pos_iff.mpr hright
    have hll : left.length ≤ k := by simp only [List.length_append] at hlength; omega
    have hrl : right.length ≤ k := by simp only [List.length_append] at hlength; omega
    have hcl := ihleft hll (fun a ha => hc a (List.mem_append_left _ ha)) hleft
    have hcr := ihright hrl (fun a ha => hc a (List.mem_append_right _ ha)) hright
    have hcm : codeMass c ≤ M := hcl.1.trans (Nat.mul_le_mul_right B (by omega))
    have hdm : codeMass d ≤ M := hcr.1.trans (Nat.mul_le_mul_right B (by omega))
    have hcoeff : 2 * (left ++ right).length - 1 =
        (2 * left.length - 1) + (2 * right.length - 1) + 1 := by
      simp only [List.length_append]
      omega
    constructor
    · have h := codeMass_comp_le n op (appendCode n c d)
      rw [codeMass_append] at h
      rw [hcoeff]
      nlinarith [hcl.1, hcr.1]
    · apply wireBitsLe_mono (wireBitsLe_comp n (wireBitsLe_append n hcl.2 hcr.2) hopBits)
      rw [codeMass_append, hcoeff]
      dsimp only [D]
      nlinarith

private theorem le_sum_map_of_mem {α : Type} (f : α → ℕ) {a : α} {l : List α}
    (ha : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

private theorem length_encoding_of_bounds {c : Code} {M W : ℕ}
    (hm : codeMass c ≤ M) (hw : WireBitsLe c W) :
    (encCode c).length ≤
      2 * M * (19 + 2 * M * (2 * W + 1)) + 1 + M * (2 * W + 1) := by
  have hgate (g : Op × List ℕ) (hg : g ∈ c.1) :
      (encGate g).length ≤ 9 + M * (2 * W + 1) := by
    have htag : (encOp g.1).length ≤ 4 := by
      cases g.1 with
      | const b => cases b <;> decide
      | _ => decide
    have hargs : g.2.length ≤ M := by
      have h := le_sum_map_of_mem (fun g : Op × List ℕ => g.2.length + 1) hg
      dsimp only [codeMass] at hm
      omega
    have hwords := length_encList_le encNat g.2 (hw.1 g hg)
    have hb := hwords.trans (Nat.mul_le_mul_right (2 * W + 1) hargs)
    rw [show (encGate g).length =
      2 * (encOp g.1).length + 1 + (encList encNat g.2).length from length_encPair g]
    omega
  have hgates := length_encList_le encGate c.1 hgate
  have hgc := (gates_le_codeMass c).trans hm
  have hgates' := hgates.trans (Nat.mul_le_mul_right (2 * (9 + M * (2 * W + 1)) + 1) hgc)
  have hout := length_encList_le encNat c.2 hw.2
  have hoc : c.2.length ≤ M := by dsimp only [codeMass] at hm; omega
  have hout' := hout.trans (Nat.mul_le_mul_right (2 * W + 1) hoc)
  rw [show (encCode c).length =
    2 * (encList encGate c.1).length + 1 + (encList encNat c.2).length from length_encPair c]
  nlinarith

private theorem computedGetD {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {values : α → List β} {index : α → ℕ} {fallback : α → β}
    (hv : ComputableInPolyTime values encIn (encList enc))
    (hi : ComputableInPolyTime index encIn encUnary)
    (hf : ComputableInPolyTime fallback encIn enc) :
    ComputableInPolyTime (fun a => (values a).getD (index a) (fallback a)) encIn enc := by
  have hhead := (head? enc).comp ((dropUnary (encA := enc)).comp (hv.prod hi))
  simpa only [Function.comp_def, List.head?_drop, List.getD_eq_getElem?_getD] using
    optionGetDWithInput hhead hf

private theorem computable_intervalRow {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {op unit : α → Code} {leaves : α → List Code}
    {rows : α → List (List Code)}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime op enc encCode)
    (hu : ComputableInPolyTime unit enc encCode)
    (hl : ComputableInPolyTime leaves enc (encList encCode))
    (hr : ComputableInPolyTime rows enc (encList (encList encCode))) :
    ComputableInPolyTime (fun a => intervalRow (n a) (op a) (unit a) (leaves a) (rows a))
      enc (encList encCode) := by
  have hlen := (length_list (encList encCode)).comp hr
  have hhalf := (unary_div_const 2).comp hlen
  have hrest : ComputableInPolyTime (fun a => (rows a).length - (rows a).length / 2)
      enc encUnary := by fun_prop
  have hleft := (listGetD (encA := encList encCode) []).comp (hr.prod hhalf)
  have hright := (listGetD (encA := encList encCode) []).comp (hr.prod hrest)
  have hbody : ComputableInPolyTime
      (fun p : α × ℕ =>
        if (rows p.1).length = 1 then (leaves p.1).getD p.2 (unit p.1)
        else if p.2 + (rows p.1).length ≤ (leaves p.1).length then
          compCode (n p.1) (op p.1) (appendCode (n p.1)
            (((rows p.1).getD ((rows p.1).length / 2) []).getD p.2 (unit p.1))
            (((rows p.1).getD ((rows p.1).length - (rows p.1).length / 2) []).getD
              (p.2 + (rows p.1).length / 2) (unit p.1)))
        else unit p.1) (encPair enc encUnary) encCode := by
    have hfst := fst enc encUnary
    have hs := snd enc encUnary
    have hleaf := computedGetD (hl.comp hfst) hs (hu.comp hfst)
    have hlc := computedGetD (hleft.comp hfst) hs (hu.comp hfst)
    have hrc := computedGetD (hright.comp hfst)
      (show ComputableInPolyTime
        (fun p : α × ℕ => p.2 + (rows p.1).length / 2) (encPair enc encUnary) encUnary from
          by fun_prop) (hu.comp hfst)
    fun_prop
  have hrange : ComputableInPolyTime (fun a => List.range ((leaves a).length + 1))
      enc (encList encUnary) := by fun_prop
  exact mapWithInput hrange hbody

private theorem intervalRow_getD (n : ℕ) (op unit : Code) (leaves : List Code)
    (rows : List (List Code)) (start : ℕ) (hs : start ≤ leaves.length) :
    (intervalRow n op unit leaves rows).getD start unit =
      if rows.length = 1 then leaves.getD start unit
      else if start + rows.length ≤ leaves.length then
        compCode n op (appendCode n
          ((rows.getD (rows.length / 2) []).getD start unit)
          ((rows.getD (rows.length - rows.length / 2) []).getD
            (start + rows.length / 2) unit))
      else unit := by
  rw [List.getD_eq_getElem _ _ (by simp [intervalRow]; omega)]
  simp [intervalRow]

private theorem intervalTables_getD (n : ℕ) (op unit : Code) (leaves : List Code)
    (count len start : ℕ) (hl : len ≤ count) (hs : start + len ≤ leaves.length) :
    ((intervalTables n op unit leaves count).getD len []).getD start unit =
      referenceCode n op unit ((leaves.drop start).take len) := by
  induction count generalizing len start with
  | zero =>
    have : len = 0 := by omega
    subst len
    simp [intervalTables, referenceCode]
  | succ count ih =>
    rw [intervalTables, Function.iterate_succ_apply']
    change (((intervalTables n op unit leaves count) ++
      [intervalRow n op unit leaves (intervalTables n op unit leaves count)]).getD len []).getD
        start unit = _
    by_cases hlt : len ≤ count
    · rw [List.getD_append _ _ _ _ (by rw [length_intervalTables]; omega)]
      exact ih _ _ hlt hs
    · have heq : len = count + 1 := by omega
      subst len
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, length_intervalTables,
        lt_self_iff_false, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [← List.getD_eq_getElem?_getD, intervalRow_getD n op unit leaves _ start (by omega),
        length_intervalTables]
      by_cases hc : count = 0
      · subst count
        rw [ite_eq_left rfl]
        rw [List.take_one_drop_eq_of_lt_length (by omega)]
        rw [List.getD_eq_getElem _ _ (by omega : start < leaves.length)]
        simp [referenceCode]
      · rw [ite_eq_right (by omega), ite_eq_left hs]
        have hh : (count + 1) / 2 ≤ count := by omega
        have hr : count + 1 - (count + 1) / 2 ≤ count := by omega
        rw [ih _ _ hh (by omega), ih _ _ hr (by omega)]
        have hlength : ((leaves.drop start).take (count + 1)).length = count + 1 := by
          simp only [List.length_take, List.length_drop]
          omega
        conv_rhs =>
          unfold referenceCode
          rw [List.balancedFold_of_two_le (by rw [hlength]; omega), hlength]
        simp only [List.take_take, List.drop_take, List.drop_drop, referenceCode,
          Nat.min_eq_left (by omega : (count + 1) / 2 ≤ count + 1)]

private theorem intervalTables_getD_invalid (n : ℕ) (op unit : Code) (leaves : List Code)
    (count len start : ℕ) (hl : len ≤ count) (hs : start ≤ leaves.length)
    (hinvalid : leaves.length < start + len) :
    ((intervalTables n op unit leaves count).getD len []).getD start unit = unit := by
  induction count generalizing len start with
  | zero => omega
  | succ count ih =>
    rw [intervalTables, Function.iterate_succ_apply']
    change (((intervalTables n op unit leaves count) ++
      [intervalRow n op unit leaves (intervalTables n op unit leaves count)]).getD len []).getD
        start unit = _
    by_cases hlt : len ≤ count
    · rw [List.getD_append _ _ _ _ (by rw [length_intervalTables]; omega)]
      exact ih _ _ hlt hs hinvalid
    · have heq : len = count + 1 := by omega
      subst len
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, length_intervalTables,
        lt_self_iff_false, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [← List.getD_eq_getElem?_getD, intervalRow_getD n op unit leaves _ start hs,
        length_intervalTables]
      split
      · exact List.getD_eq_default _ _ (by omega)
      · rw [ite_eq_right (by omega)]

private theorem intervalTables_row_length (n : ℕ) (op unit : Code) (leaves : List Code)
    (count : ℕ) (row : List Code) (hr : row ∈ intervalTables n op unit leaves count) :
    row.length = leaves.length + 1 := by
  induction count with
  | zero =>
    have heq : row = List.replicate (leaves.length + 1) unit := by
      simpa [intervalTables] using hr
    simp [heq]
  | succ count ih =>
    change row ∈ (fun rows => rows ++ [intervalRow n op unit leaves rows])^[count + 1]
      [List.replicate (leaves.length + 1) unit] at hr
    rw [Function.iterate_succ_apply'] at hr
    rcases List.mem_append.mp hr with h | h
    · exact ih h
    · have heq : row = intervalRow n op unit leaves (intervalTables n op unit leaves count) :=
        List.mem_singleton.mp h
      rw [heq]
      simp [intervalRow]

private def inputBudget (op unit : Code) (leaves : List Code) : ℕ :=
  (encCode op).length + (encCode unit).length + (encList encCode leaves).length + 1

private def entryBound (n : ℕ) (op unit : Code) (leaves : List Code) : ℕ :=
  let B := inputBudget op unit leaves
  let M := (2 * leaves.length + 1) * B
  let W := (2 * leaves.length + 1) * (B + (encNat n).length + 3 * M + 2)
  2 * M * (19 + 2 * M * (2 * W + 1)) + 1 + M * (2 * W + 1)

private def tableBound (n : ℕ) (op unit : Code) (leaves : List Code) : ℕ :=
  (leaves.length + 1) *
    (2 * ((leaves.length + 1) * (2 * entryBound n op unit leaves + 1)) + 1)

private theorem intervalTables_entry_bound (n : ℕ) (op unit : Code) (leaves : List Code)
    (count : ℕ) {row : List Code} {code : Code}
    (hr : row ∈ intervalTables n op unit leaves count) (hc : code ∈ row) :
    (encCode code).length ≤ entryBound n op unit leaves := by
  let B := inputBudget op unit leaves
  let M := (2 * leaves.length + 1) * B
  let D := B + (encNat n).length + 3 * M + 2
  have hunit : codeMass unit ≤ B ∧ WireBitsLe unit B := by
    constructor
    · exact (codeMass_le_encoding unit).trans (by dsimp [B, inputBudget]; omega)
    · exact wireBitsLe_mono (wireBitsLe_encoding unit) (by dsimp [B, inputBudget]; omega)
  have hop : codeMass op ≤ B ∧ WireBitsLe op B := by
    constructor
    · exact (codeMass_le_encoding op).trans (by dsimp [B, inputBudget]; omega)
    · exact wireBitsLe_mono (wireBitsLe_encoding op) (by dsimp [B, inputBudget]; omega)
  have hleaves : ∀ c ∈ leaves, codeMass c ≤ B ∧ WireBitsLe c B := by
    intro c h
    have hc := length_encoding_member encCode h
    have hB : (encCode c).length ≤ B := by dsimp only [B, inputBudget]; omega
    exact ⟨(codeMass_le_encoding c).trans hB, wireBitsLe_mono (wireBitsLe_encoding c) hB⟩
  have hBM : B ≤ M := by dsimp [M]; nlinarith
  have hBW : B ≤ (2 * leaves.length + 1) * D := by dsimp [D]; nlinarith
  suffices codeMass code ≤ M ∧ WireBitsLe code ((2 * leaves.length + 1) * D) by
    exact length_encoding_of_bounds this.1 this.2
  obtain ⟨len, hlen, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨start, hstart, rfl⟩ := List.mem_iff_getElem.mp hc
  have hlen' : len ≤ count := by rw [length_intervalTables] at hlen; omega
  have hrowlen := intervalTables_row_length n op unit leaves count _
    (List.getElem_mem hlen)
  have hstart' : start ≤ leaves.length := by omega
  rw [← List.getD_eq_getElem _ unit hstart, ← List.getD_eq_getElem _ [] hlen]
  by_cases hvalid : start + len ≤ leaves.length
  · rw [intervalTables_getD _ _ _ _ _ _ _ hlen' hvalid]
    by_cases he : (leaves.drop start).take len = []
    · rw [he]
      simpa only [referenceCode, List.balancedFold_nil] using
        ⟨hunit.1.trans hBM, wireBitsLe_mono hunit.2 hBW⟩
    · have hlength : ((leaves.drop start).take len).length ≤ leaves.length := by
        simp only [List.length_take, List.length_drop]
        omega
      have hb := referenceCode_bounds n op unit _ leaves.length B hop.1 hop.2 hlength
        (fun c hc => hleaves c (List.mem_of_mem_drop (List.mem_of_mem_take hc))) he
      exact ⟨hb.1.trans (Nat.mul_le_mul_right B (by omega)),
        wireBitsLe_mono hb.2 (Nat.mul_le_mul_right D (by omega))⟩
  · rw [intervalTables_getD_invalid _ _ _ _ _ _ _ hlen' hstart' (by omega)]
    exact ⟨hunit.1.trans hBM, wireBitsLe_mono hunit.2 hBW⟩

private theorem intervalTables_bound (n : ℕ) (op unit : Code) (leaves : List Code)
    (count : ℕ) (hcount : count ≤ leaves.length) :
    (encList (encList encCode) (intervalTables n op unit leaves count)).length ≤
      tableBound n op unit leaves := by
  have hrows (row : List Code) (hr : row ∈ intervalTables n op unit leaves count) :
      (encList encCode row).length ≤
        (leaves.length + 1) * (2 * entryBound n op unit leaves + 1) := by
    have h := length_encList_le encCode row
      (fun c hc => intervalTables_entry_bound n op unit leaves count hr hc)
    rwa [intervalTables_row_length n op unit leaves count row hr] at h
  have h := length_encList_le (encList encCode) _ hrows
  rw [length_intervalTables] at h
  exact h.trans (Nat.mul_le_mul_right _ (by omega))

private theorem referenceCode_map {n r : ℕ} (op : Circuit signature (r + r) r)
    (unit : Circuit signature n r) (leaves : List (Circuit signature n r)) :
    referenceCode n op.code unit.code (leaves.map Circuit.code) =
      (Circuit.balanced op unit leaves).code := by
  induction leaves using List.balancedFold.induct with
  | case1 => simp [referenceCode, Circuit.balanced]
  | case2 c => simp [referenceCode, Circuit.balanced]
  | case3 a b leaves ih₁ ih₂ =>
    have hm : 2 ≤ ((a :: b :: leaves).map Circuit.code).length := by simp
    rw [referenceCode, List.balancedFold_of_two_le hm, List.length_map,
      ← List.map_take, ← List.map_drop]
    change compCode n op.code (appendCode n
      (referenceCode n op.code unit.code _)
      (referenceCode n op.code unit.code _)) = _
    rw [ih₁, ih₂, appendCode_code, compCode_code]
    congr 1
    simp only [Circuit.balanced]
    exact (List.balancedFold_of_two_le
      (op := fun C D : Circuit signature n r => op.comp (C.append D))
      (e := unit) (f := id) (by simp : 2 ≤ (a :: b :: leaves).length)).symm

/-- Exact raw-code agreement, including empty fallback programs, unused operators, dead gates
and the existing half-split order of all intermediate gate blocks. -/
theorem balancedCode_eq_code {n r : ℕ} (op : Circuit signature (r + r) r)
    (unit : Circuit signature n r) (leaves : List (Circuit signature n r)) :
    balancedCode n op.code unit.code (leaves.map Circuit.code) =
      (Circuit.balanced op unit leaves).code := by
  change ((intervalTables n op.code unit.code (leaves.map Circuit.code)
    (leaves.map Circuit.code).length).getD (leaves.map Circuit.code).length []).getD 0 unit.code = _
  rw [intervalTables_getD _ _ _ _ _ _ _ le_rfl (by omega)]
  simp only [List.drop_zero, List.take_length]
  exact referenceCode_map op unit leaves

/-- Uniform native generation from the binary shared-input count and the complete operator,
fallback and leaf codes. The derived bound charges every interval row and its list framing;
no well-formedness, fixed arity or assumed construction-runtime bound is required. -/
@[fun_prop] theorem computableInPolyTime_balancedCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {op unit : α → Code} {leaves : α → List Code}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime op enc encCode)
    (hu : ComputableInPolyTime unit enc encCode)
    (hl : ComputableInPolyTime leaves enc (encList encCode)) :
    ComputableInPolyTime (fun a => balancedCode (n a) (op a) (unit a) (leaves a))
      enc encCode := by
  let rowsEnc := encList (encList encCode)
  let init (a : α) := [List.replicate ((leaves a).length + 1) (unit a)]
  let step (a : α) (rows : List (List Code)) :=
    rows ++ [intervalRow (n a) (op a) (unit a) (leaves a) rows]
  have hcount := (length_list encCode).comp hl
  have hi : ComputableInPolyTime init enc rowsEnc := by
    dsimp only [init, rowsEnc]
    fun_prop
  have hs : ComputableInPolyTime (fun p : α × List (List Code) => step p.1 p.2)
      (encPair enc rowsEnc) rowsEnc := by
    have hf := fst enc rowsEnc
    have hr := snd enc rowsEnc
    have hrow := computable_intervalRow (hn.comp hf) (hop.comp hf) (hu.comp hf) (hl.comp hf) hr
    dsimp only [step, rowsEnc]
    fun_prop
  have hb : PolyBounded (fun a => (enc a).length)
      (fun a => tableBound (n a) (op a) (unit a) (leaves a)) := by
    have hnlen := (encoding_length encNat).comp hn
    have hoplen := (encoding_length encCode).comp hop
    have hulen := (encoding_length encCode).comp hu
    have hllen := (encoding_length (encList encCode)).comp hl
    have hB : ComputableInPolyTime (fun a => inputBudget (op a) (unit a) (leaves a))
        enc encUnary := by unfold inputBudget; fun_prop
    have hM : ComputableInPolyTime
        (fun a => (2 * (leaves a).length + 1) * inputBudget (op a) (unit a) (leaves a))
        enc encUnary := by fun_prop
    have hW : ComputableInPolyTime
        (fun a => (2 * (leaves a).length + 1) *
          (inputBudget (op a) (unit a) (leaves a) + (encNat (n a)).length +
            3 * ((2 * (leaves a).length + 1) * inputBudget (op a) (unit a) (leaves a)) + 2))
        enc encUnary := by fun_prop
    have hC : ComputableInPolyTime
        (fun a => entryBound (n a) (op a) (unit a) (leaves a)) enc encUnary := by
      have hp : ComputableInPolyTime
          (fun p : ℕ × ℕ => 2 * p.1 * (19 + 2 * p.1 * (2 * p.2 + 1)) + 1 +
            p.1 * (2 * p.2 + 1)) (encPair encUnary encUnary) encUnary := by fun_prop
      exact hp.comp (hM.prod hW)
    have hp : ComputableInPolyTime
        (fun p : ℕ × ℕ => (p.1 + 1) * (2 * ((p.1 + 1) * (2 * p.2 + 1)) + 1))
        (encPair encUnary encUnary) encUnary := by fun_prop
    exact polyBounded (hp.comp (hcount.prod hC))
  have ht := iterateWith (par := id) (count := fun a => (leaves a).length)
    (init := init) (step := step) id' hcount hi hs hb (fun a count hcount =>
      intervalTables_bound (n a) (op a) (unit a) (leaves a) count hcount)
  have hrow := (listGetD (encA := encList encCode) []).comp (ht.prod hcount)
  change ComputableInPolyTime (fun a =>
    ((intervalTables (n a) (op a) (unit a) (leaves a) (leaves a).length).getD
      (leaves a).length []).getD 0 (unit a)) enc encCode
  exact computedGetD hrow (const 0) hu

end Cslib.Circuits.Boolean
