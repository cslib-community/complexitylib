/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Decoder.Circuit
import Complexity.Foundations.Data.List.RowMajor
import Complexity.Foundations.Data.Nat.Doubling
import Mathlib.Data.Nat.Size

/-!
# The decoder circuit of the succinct tableau

The three stages of the decoder of the tableau formula on bit-field labels
(`Complexity/Computability/Circuit/Boolean/Tableau/Decoder/Circuit.lean`) composed into one
De Morgan circuit (`decoder`). From the bits of a clause number below `2 ^ clauseBits`, it computes
the bits of `Cslib.Circuits.Boolean.Tableau.clauseAt` (`ofFn_eval_decoder`). It has
`O(colBits T + timeBits T + x.length)` gates (`size_decoder_le`): the field stage has
`2 + N + 14 P + (2 ^ (Nat.size x.length + 1) - 1) + x.length` gates for `N = clauseBits` and
`P = N - 4`, the constant stage a number depending only on the machine, and the output stage `63`
gates per output bit. There is no carry-lookahead adder, whose size is not linear in the width.

Its code is `decoderCode`, written with the code combinators `compCode`, `appendCode`,
`appendCodes` and `formulaCode` on the explicit gate list of the field stage and the constant code
of the constant stage (`code_decoder`). This is the decoder of the sketch of
[Williams, Theorem 6.1, p. 20][Williams2010]: the variables of the clauses of a cell differ from
cell to cell only by the block and the column, which enter through comparisons, increments and
decrements of fields. The sketch first converts the machine to a single-tape machine; this decoder
is built for the multi-tape tableau directly.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Decoder.decoder`: the decoder circuit.
* `Cslib.Circuits.Boolean.Tableau.Decoder.decoderCode`: its code.
* `Cslib.Circuits.Boolean.Tableau.Decoder.sizeConst`: the constant of its size bound.

## Main results

* `Cslib.Circuits.Boolean.Tableau.Decoder.ofFn_eval_decoder`: the decoder computes the clause with
  a given number, bit by bit.
* `Cslib.Circuits.Boolean.Tableau.Decoder.size_decoder_le`: it has
  `O(colBits T + timeBits T + x.length)` gates.
* `Cslib.Circuits.Boolean.Tableau.Decoder.code_decoder`: its code is `decoderCode`.
* `Cslib.Circuits.Boolean.Tableau.Decoder.exists_decoder`: the three together.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau.Decoder

open Turing MultiTapeTM Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

omit [DecidableEq State] in
/-- There is at least one slot bit. -/
theorem one_le_slotBits : 1 ≤ slotBits k State :=
  Nat.size_pos.2 (Fintype.card_pos_iff.2 ⟨Loc.scan .nx⟩)

/-- The selection of the inputs of the constant stage among the wires of the field stage. -/
def keySel (s cb tb : ℕ) (x : List Bool) (n T : ℕ) :
    Fin (4 + s + 14) → Fin (aWidth s cb tb x n T) :=
  fun i => ⟨keyWire s cb tb i, keyWire_lt i.isLt⟩

/-- The constant stage on the wires of the field stage, beside those wires. -/
noncomputable def middleCircuit (x : List Bool) (n T : ℕ) :
    Circuit signature (aWidth (slotBits k State) (colBits T) (timeBits T) x n T)
      (aWidth (slotBits k State) (colBits T) (timeBits T) x n T + 3 * (13 + slotBits k State)) :=
  (Circuit.wiring signature id).append ((tableCircuit tm).comp
    (Circuit.wiring signature (keySel (slotBits k State) (colBits T) (timeBits T) x n T)))

/-- **The output stage**: one copy of `outTemplate` per output bit, on the wires `wireNat`. -/
def outputCircuit (s cb tb : ℕ) (x : List Bool) (n T : ℕ) :
    Circuit signature (aWidth s cb tb x n T + 3 * (13 + s)) (3 * (2 + (s + cb + tb) + 1)) :=
  Circuit.pi fun o => (outTemplate.rename fun j =>
    ⟨wireNat s cb tb x n T o j, wireNat_lt o.isLt j.isLt⟩).toCircuit

/-- **The decoder circuit** of the tableau formula of `tm` on bit-field labels, for the fixed
prefix `x`, `n` inputs and `T` steps. -/
noncomputable def decoder {x : List Bool} {n T : ℕ}
    (hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T) :
    Circuit signature (4 + (slotBits k State + colBits T + timeBits T))
      (3 * (2 + (slotBits k State + colBits T + timeBits T) + 1)) :=
  (outputCircuit (slotBits k State) (colBits T) (timeBits T) x n T).comp
    ((middleCircuit tm x n T).comp (fieldCircuit hm))

/-! ### The code -/

/-- **The code of the decoder**, written with the code combinators `compCode`, `appendCode`,
`appendCodes` and `formulaCode`: the field stage, the constant code of the constant stage, and one
instance of `outTemplate` per output bit (`code_decoder`). -/
noncomputable def decoderCode : List Bool × ℕ × ℕ → List (Op × List ℕ) × List ℕ
  | (x, n, T) =>
    compCode (4 + (slotBits k State + colBits T + timeBits T))
      (appendCodes (aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
          3 * (13 + slotBits k State))
        ((List.range (3 * (2 + (slotBits k State + colBits T + timeBits T) + 1))).map
          fun o => formulaCode (aWidth (slotBits k State) (colBits T) (timeBits T) x n
            T + 3 * (13 + slotBits k State)) outTemplate
            (fun j => wireNat (slotBits k State) (colBits T) (timeBits T) x n T o
              j)))
      (compCode (4 + (slotBits k State + colBits T + timeBits T))
        (appendCode (aWidth (slotBits k State) (colBits T) (timeBits T) x n T)
          ([], List.range
            (aWidth (slotBits k State) (colBits T) (timeBits T) x n T))
          (compCode (aWidth (slotBits k State) (colBits T) (timeBits T) x n T)
            (tableCircuit tm).code
            ([], (List.range (4 + slotBits k State + 14)).map
              (keyWire (slotBits k State) (colBits T) (timeBits T)))))
        (fieldGates (slotBits k State) (colBits T) (timeBits T) x n T,
          List.range (aWidth (slotBits k State) (colBits T) (timeBits T) x n T)))

/-- **The code of the decoder circuit is `decoderCode`.** -/
theorem code_decoder {x : List Bool} {n T : ℕ}
    (hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T) :
    (decoder (n := n) tm hm).code = decoderCode tm (x, n, T) := by
  rw [decoder, ← compCode_code, middleCircuit, ← compCode_code, ← appendCode_code,
    ← compCode_code, Circuit.code_wiring_id, code_fieldCircuit, outputCircuit, ← appendCodes_code,
    Circuit.code_wiring_eq_map (g := keyWire (slotBits k State) (colBits T) (timeBits T))
      (fun j => rfl)]
  simp only [decoderCode]
  congr 2
  apply List.ext_getElem (by simp; omega)
  intro o h₁ h₂
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact (formulaCode_eq_code outTemplate _).symm

/-! ### Size -/

theorem size_outputCircuit_le (s cb tb : ℕ) (x : List Bool) (n T : ℕ) :
    (outputCircuit s cb tb x n T).size ≤ 3 * (2 + (s + cb + tb) + 1) * 63 := by
  simp only [outputCircuit, Circuit.size_pi, Formula.size_toCircuit]
  calc ∑ o : Fin (3 * (2 + (s + cb + tb) + 1)), (outTemplate.rename _).size
      ≤ ∑ _o : Fin (3 * (2 + (s + cb + tb) + 1)), 63 := Finset.sum_le_sum fun o _ => by
        have := Formula.size_bind_le (c := 0) (s := fun j => Formula.input
          (⟨wireNat s cb tb x n T o j, wireNat_lt o.isLt j.isLt⟩ :
            Fin (aWidth s cb tb x n T + 3 * (13 + s)))) (fun _ => le_rfl) outTemplate
        simpa [Formula.rename, size_outTemplate] using this
    _ = 3 * (2 + (s + cb + tb) + 1) * 63 := by simp

/-- **The decoder has `O(colBits T + timeBits T + x.length)` gates**, with a constant depending
only on the machine. -/
theorem size_decoder_le {x : List Bool} {n T : ℕ}
    (hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T) :
    (decoder (n := n) tm hm).size ≤ (204 * slotBits k State + 600 + (tableCircuit tm).size) *
      (colBits T + timeBits T + x.length + 1) := by
  have hX := Nat.two_pow_size_le x.length
  have hpow : 2 ^ (Nat.size x.length + 1) = 2 * 2 ^ Nat.size x.length := Nat.pow_succ'
  have hout := size_outputCircuit_le (slotBits k State) (colBits T) (timeBits T) x n T
  rw [decoder, Circuit.size_comp, Circuit.size_comp, middleCircuit, Circuit.size_append,
    Circuit.size_comp, Circuit.size_wiring, Circuit.size_wiring, size_fieldCircuit,
    length_fieldGates]
  clear hm
  generalize (tableCircuit tm).size = S at *
  generalize (outputCircuit (slotBits k State) (colBits T) (timeBits T) x n T).size = O at *
  generalize slotBits k State = s at *
  generalize colBits T = cb at *
  generalize timeBits T = tb at *
  generalize x.length = X at *
  generalize 2 ^ Nat.size X = Y at *
  have h1 : 204 * s + 600 + S ≤ (204 * s + 600 + S) * (cb + tb + X + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h2 : 204 * (cb + tb + X) ≤ (204 * s + 600 + S) * (cb + tb + X) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_add (204 * s + 600 + S) (cb + tb + X) 1, Nat.mul_one] at h1 ⊢
  rw [hpow]
  omega

/-! ### Correctness -/

theorem outBit_congr {s cb tb : ℕ} {ts ts' sel sel' : ℕ → Bool}
    (hts : ∀ f < 2 + s, ts f = ts' f) (hsel : ∀ q < 11, sel q = sel' q) (p c t T : ℕ) (lk : Bool)
    (i : ℕ) : outBit s cb tb ts sel p c t T lk i = outBit s cb tb ts' sel' p c t T lk i := by
  unfold outBit payTerm colTerm timeTerm
  simp only [hsel 0 (by omega), hsel 1 (by omega), hsel 2 (by omega), hsel 3 (by omega),
    hsel 4 (by omega), hsel 5 (by omega), hsel 6 (by omega), hsel 7 (by omega), hsel 8 (by omega),
    hsel 9 (by omega), hsel 10 (by omega)]
  split_ifs with h1 h2
  · rw [hts i (by omega)]
  · by_cases hq : i - 2 < s
    · simp [hq, hts (2 + (i - 2)) (by omega)]
    · simp [hq]
  · rfl

/-- The values of the wires of the field and constant stages. -/
theorem eval_middle_field {x : List Bool} {n T : ℕ}
    (hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T) (idx : ℕ)
    (w : Fin (aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
      3 * (13 + slotBits k State))) :
    ((middleCircuit tm x n T).comp (fieldCircuit hm)).eval interpretation
        (fun i => idx.testBit i) w =
      if h : w.val < aWidth (slotBits k State) (colBits T) (timeBits T) x n T then
        fieldVal (slotBits k State) (colBits T) (timeBits T) x n T idx w
      else tableFn tm (fun i => fieldVal (slotBits k State) (colBits T) (timeBits T) x n T idx
          (keyWire (slotBits k State) (colBits T) (timeBits T) i))
        ⟨w.val - aWidth (slotBits k State) (colBits T) (timeBits T) x n T, by omega⟩ := by
  rw [Circuit.eval_comp, middleCircuit, Circuit.eval_append]
  split
  · rename_i h
    have hw : w = Fin.castAdd _ ⟨w.val, h⟩ := rfl
    conv_lhs => rw [hw]
    rw [Fin.append_left, Circuit.eval_wiring, Function.comp_apply, id, eval_fieldCircuit]
  · rename_i h
    have hw : w = Fin.natAdd _ (⟨w.val - aWidth (slotBits k State) (colBits T) (timeBits T) x n T,
        by omega⟩ : Fin (3 * (13 + slotBits k State))) := by ext; simp; omega
    conv_lhs => rw [hw]
    rw [Fin.append_right, Circuit.eval_comp, Circuit.eval_wiring, eval_tableCircuit]
    congr 1
    funext i
    simp [keySel, eval_fieldCircuit]

theorem getElem?_litBits (w : ℕ) (l : Literal ℕ) {i : ℕ} (hi : i < w + 1) :
    (litBits w l)[i]? = some (if i < w then l.1.testBit i else l.2) := by
  unfold litBits
  split
  · rename_i h
    rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rename_i h
    rw [List.getElem?_append_right (by simp; omega)]
    simp [show i - w = 0 by omega]

/-- **The decoder computes the clause with a given number**: its outputs are the bits of the
three literals of `clauseAt`, for `n < 2 T` and a fixed prefix of length at most `n`. -/
theorem ofFn_eval_decoder {x : List Bool} {n T : ℕ} (hn : n < 2 * T) (hx : x.length ≤ n)
    (hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T) {idx : ℕ}
    (hidx : idx < 2 ^ (4 + (slotBits k State + colBits T + timeBits T))) :
    List.ofFn ((decoder (n := n) tm hm).eval interpretation (fun i => idx.testBit i)) =
      (clauseAt tm x n T idx).flatMap
        (litBits (2 + (slotBits k State + colBits T + timeBits T))) := by
  have hs := one_le_slotBits (k := k) (State := State)
  have h2T : 2 * T < 2 ^ colBits T := Nat.lt_size_self _
  have hT : T < 2 ^ timeBits T := Nat.lt_size_self _
  have hkey := ofBits_keyWire (x := x) (n := n) (T := T) hidx hs h2T hT hn hx
  have hcl := clauseOf_eq_map_shapeOf tm x n T (idx % 4) (idx / 4 % 4) (idx / 16)
  rw [clauseAt, hcl]
  generalize hκ : Key.ofFields (slotBits k State) (colBits T) x.length n T (idx % 4) (idx / 4 % 4)
    (idx / 16) = κ at hkey
  have hlen := length_shapeOf tm κ
  apply List.ext_getElem?
  intro o
  rw [List.getElem?_ofFn]
  by_cases ho : o < 3 * (2 + (slotBits k State + colBits T + timeBits T) + 1)
  · have hr : o / (2 + (slotBits k State + colBits T + timeBits T) + 1) < 3 :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hi : o % (2 + (slotBits k State + colBits T + timeBits T) + 1) <
        2 + (slotBits k State + colBits T + timeBits T) + 1 := Nat.mod_lt _ (by omega)
    rw [dite_eq_left ho]
    conv_rhs => rw [← Nat.div_add_mod' o (2 + (slotBits k State + colBits T + timeBits T) + 1)]
    rw [List.getElem?_flatMap_mul_add _ _ _ (fun _ _ => by simp [litBits]) (by simpa [hlen]) hi]
    rw [List.getElem_map, getElem?_litBits _ _ hi]
    congr 1
    -- the left side
    rw [decoder, Circuit.eval_comp]
    simp only [outputCircuit, Circuit.eval_pi, Formula.eval_toCircuit, Formula.eval_rename]
    set z' := ((middleCircuit tm x n T).comp (fieldCircuit hm)).eval interpretation
      (fun i => idx.testBit i) with hz'
    let z : ℕ → Bool := fun w => if h : w < aWidth (slotBits k State) (colBits T) (timeBits T)
      x n T + 3 * (13 + slotBits k State) then z' ⟨w, h⟩ else false
    have hzz : (z' ∘ fun j : Fin 28 => (⟨wireNat (slotBits k State) (colBits T) (timeBits T) x n T
        o j, wireNat_lt ho j.isLt⟩ : Fin _)) =
        fun j : Fin 28 => z (wireNat (slotBits k State) (colBits T) (timeBits T) x n T o j) := by
      funext j
      simp [z, wireNat_lt ho j.isLt]
    have hF : ∀ w < aWidth (slotBits k State) (colBits T) (timeBits T) x n T,
        z w = fieldVal (slotBits k State) (colBits T) (timeBits T) x n T idx w := by
      intro w hw
      simp only [z, show w < aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
        3 * (13 + slotBits k State) by omega, ↓reduceDIte, hz', eval_middle_field, hw]
    rw [hzz, eval_outTemplate_wireNat hidx hF]
    set r := o / (2 + (slotBits k State + colBits T + timeBits T) + 1) with hrdef
    set i := o % (2 + (slotBits k State + colBits T + timeBits T) + 1) with hidef
    set sh := (shapeOf tm κ).getD r defaultShape with hsh
    have hsh' : sh = (shapeOf tm κ)[r]'(by omega) := by
      rw [hsh, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    have htab (f : ℕ) (hf : f < 13 + slotBits k State) :
        z (aWidth (slotBits k State) (colBits T) (timeBits T) x n T + r * (13 + slotBits k State) +
          f) = if f < 2 + slotBits k State then tagSlot sh f
            else selOf κ.c0 κ.t0 sh (f - (2 + slotBits k State)) := by
      have hlt : r * (13 + slotBits k State) + f < 3 * (13 + slotBits k State) := by
        have : r * (13 + slotBits k State) + (13 + slotBits k State) ≤
            3 * (13 + slotBits k State) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
        omega
      simp only [z, show aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
        r * (13 + slotBits k State) + f < aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
          3 * (13 + slotBits k State) by omega, ↓reduceDIte, hz', eval_middle_field,
        show ¬ aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
          r * (13 + slotBits k State) + f < aWidth (slotBits k State) (colBits T) (timeBits T) x n T
          by omega]
      simp only [tableFn, hkey]
      have h₁ : (aWidth (slotBits k State) (colBits T) (timeBits T) x n T +
          r * (13 + slotBits k State) + f - aWidth (slotBits k State) (colBits T) (timeBits T)
            x n T) = r * (13 + slotBits k State) + f := by omega
      have h₂ : (r * (13 + slotBits k State) + f) / (13 + slotBits k State) = r := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hf, Nat.add_zero]
      have h₃ : (r * (13 + slotBits k State) + f) % (13 + slotBits k State) = f := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
      simp only [h₁, h₂, h₃, hsh]
    rw [outBit_congr (ts' := tagSlot sh) (sel' := selOf κ.c0 κ.t0 sh)
      (fun f hf => by rw [htab f (by omega), ite_eq_left hf])
      (fun q hq => by rw [htab _ (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left])]
    have hmem : sh ∈ shapeOf tm κ := by rw [hsh']; exact List.getElem_mem _
    have hc0 : κ.c0 = decide (colOf (slotBits k State) (colBits T) (idx / 16) = 0) := by
      rw [← hκ]; rfl
    have ht0 : κ.t0 = decide (timeOf (slotBits k State) (colBits T) (idx / 16) = 0) := by
      rw [← hκ]; rfl
    rw [hc0, ht0]
    rw [← hκ] at hmem
    rw [outBit_shape (x := x) hs (inRange_of_mem_shapeOf tm hmem) ?_ (by omega), ← hsh']
    · rfl
    · intro hl
      have hp := lt_of_mem_shapeOf tm hmem hl
      have hX := Nat.lt_size_self x.length
      have hlk : lookW (slotBits k State) (colBits T) (timeBits T) x <
          aWidth (slotBits k State) (colBits T) (timeBits T) x n T := lookW_lt
      rw [hF _ hlk, lookW, ite_eq_right (by omega), fieldVal_or,
        Nat.mod_eq_of_lt (show idx / 16 < 2 ^ Nat.size x.length by omega)]
      simp [show idx / 16 ≤ x.length - 1 by omega]
  · rw [dite_eq_right ho, eq_comm, List.getElem?_eq_none]
    rw [List.length_flatMap, List.map_congr_left (fun a _ => show (litBits
      (2 + (slotBits k State + colBits T + timeBits T)) a).length =
        2 + (slotBits k State + colBits T + timeBits T) + 1 by simp [litBits])]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, hlen]
    omega

/-! ### The decoder of the succinct tableau -/

/-- The constant of the size bound of the decoder, which depends only on the machine. -/
noncomputable def sizeConst : ℕ := 204 * slotBits k State + 600 + (tableCircuit tm).size

/-- **The decoder of the succinct tableau formula**: for `n < 2 T` and a fixed prefix `x` of length
at most `n`, a De Morgan circuit with code `decoderCode tm (x, n, T)` and at most
`sizeConst tm * (colBits T + timeBits T + x.length + 1)` gates computes, from the bits of a clause
number below `2 ^ clauseBits`, the bits of the clause `clauseAt tm x n T idx` of
`Cslib.Circuits.Boolean.Tableau.succinctCNF`: the label of each of its three literals in
`labelBits` bits, least significant first, then its sign. -/
theorem exists_decoder (x : List Bool) {n T : ℕ} (hn : n < 2 * T) (hx : x.length ≤ n) :
    ∃ c : Circuit signature (clauseBits k State T) (3 * (labelBits k State T + 1)),
      c.code = decoderCode tm (x, n, T) ∧
      c.size ≤ sizeConst tm * (colBits T + timeBits T + x.length + 1) ∧
      ∀ idx < 2 ^ clauseBits k State T,
        List.ofFn (c.eval interpretation fun i => idx.testBit i) =
          (clauseAt tm x n T idx).flatMap (litBits (labelBits k State T)) := by
  have hm : Nat.size x.length ≤ slotBits k State + colBits T + timeBits T := by
    have : Nat.size x.length ≤ colBits T := Nat.size_le_size (by omega)
    omega
  exact ⟨decoder (n := n) tm hm, code_decoder tm hm, size_decoder_le tm hm,
    fun idx hidx => ofFn_eval_decoder tm hn hx hm hidx⟩

end Cslib.Circuits.Boolean.Tableau.Decoder
