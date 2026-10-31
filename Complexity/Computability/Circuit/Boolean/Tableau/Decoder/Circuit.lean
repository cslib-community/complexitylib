/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Decoder.Fields
public import Complexity.Computability.Circuit.Boolean.Tableau.Decoder.Shape
public import Complexity.Computability.Circuit.Boolean.CodeTemplate
public import Complexity.Computability.Circuit.Pi
import Mathlib.Data.Nat.Size

/-!
# The stages of the decoder circuit of the succinct tableau

The decoder computes, from the bits of a clause number, the bits of the clause of the tableau
formula on bit-field labels (`Cslib.Circuits.Boolean.Tableau.clauseAt`): for each of its three
literals, the label in `labelBits` bits, least significant first, then the sign (`litBits`). It
composes three stages:

* the field stage (`Complexity/Computability/Circuit/Boolean/Tableau/Decoder/Fields.lean`):
  comparison chains, borrows and carries, and the lookup of the fixed prefix `x`;
* a circuit of constant size (`tableCircuit`) that computes the shapes of the three literals
  (`Complexity/Computability/Circuit/Boolean/Tableau/Decoder/Shape.lean`) from the clause and tag
  bits, the slot bits and the comparisons (`ofBits_keyWire`);
* the output stage: one copy of a fixed formula of 63 gates (`outTemplate`) per output bit, reading
  the wires `wireNat`, which selects the bit of the label from the fields chosen by the shape
  (`eval_outTemplate_wireNat`).

The stages are assembled, with the correctness and the linear size of the whole circuit, in
`Complexity/Computability/Circuit/Boolean/Tableau/Decoder/Assembly.lean`.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Decoder.litBits`: the bits of a literal.
* `Cslib.Circuits.Boolean.Tableau.Decoder.outTemplate`: the formula of an output bit.
* `Cslib.Circuits.Boolean.Tableau.Decoder.tableFn`,
  `Cslib.Circuits.Boolean.Tableau.Decoder.tableCircuit`: the constant stage.
* `Cslib.Circuits.Boolean.Tableau.Decoder.wireNat`,
  `Cslib.Circuits.Boolean.Tableau.Decoder.keyWire`: the wires read by the output stage and by the
  constant stage.
* `Cslib.Circuits.Boolean.Tableau.Decoder.fieldCircuit`: the field stage as a circuit.

## Main results

* `Cslib.Circuits.Boolean.Tableau.Decoder.eval_fieldCircuit`: the field stage computes the intended
  values.
* `Cslib.Circuits.Boolean.Tableau.Decoder.ofBits_keyWire`: the constant stage reads the key of the
  fields of the clause number.
* `Cslib.Circuits.Boolean.Tableau.Decoder.eval_outTemplate_wireNat`: each output bit computes
  `outBit`.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau.Decoder

open Turing MultiTapeTM Cslib.Logic.PL

/-! ### The formula of an output bit -/

/-- Input `j` of the formula of an output bit. -/
def tIn (j : ℕ) (h : j < 28 := by omega) : Formula signature 28 := .input ⟨j, h⟩

/-- Term `k` of the formula of an output bit: a selector and the exclusive or of two bits. -/
def term (k : ℕ) (h : 3 * k + 3 < 28 := by omega) : Formula signature 28 :=
  (tIn (1 + 3 * k)).and ((tIn (2 + 3 * k)).xor (tIn (3 + 3 * k)))

/-- **The formula of an output bit**: the input `0`, or one of nine terms, each the conjunction
of a selector with the exclusive or of two bits. -/
def outTemplate : Formula signature 28 :=
  (tIn 0).or ((term 0).or ((term 1).or ((term 2).or ((term 3).or ((term 4).or ((term 5).or
    ((term 6).or ((term 7).or (term 8)))))))))

theorem eval_outTemplate (y : Fin 28 → Bool) :
    outTemplate.eval interpretation y =
      (y 0 || (y 1 && (y 2 ^^ y 3)) || (y 4 && (y 5 ^^ y 6)) || (y 7 && (y 8 ^^ y 9)) ||
        (y 10 && (y 11 ^^ y 12)) || (y 13 && (y 14 ^^ y 15)) || (y 16 && (y 17 ^^ y 18)) ||
        (y 19 && (y 20 ^^ y 21)) || (y 22 && (y 23 ^^ y 24)) || (y 25 && (y 26 ^^ y 27))) := by
  simp only [outTemplate, term, tIn, Formula.eval_or, Formula.eval_and, Formula.eval_xor,
    Formula.eval_input, Bool.or_assoc]
  rfl

/-- The formula of an output bit on the values of numbered wires. -/
theorem eval_outTemplate_nat (y : ℕ → Bool) :
    outTemplate.eval interpretation (fun j => y j) =
      (y 0 || (y 1 && (y 2 ^^ y 3)) || (y 4 && (y 5 ^^ y 6)) || (y 7 && (y 8 ^^ y 9)) ||
        (y 10 && (y 11 ^^ y 12)) || (y 13 && (y 14 ^^ y 15)) || (y 16 && (y 17 ^^ y 18)) ||
        (y 19 && (y 20 ^^ y 21)) || (y 22 && (y 23 ^^ y 24)) || (y 25 && (y 26 ^^ y 27))) :=
  eval_outTemplate _

theorem size_outTemplate : outTemplate.size = 63 := by
  simp [outTemplate, term, tIn]

/-! ### The bits of a literal -/

/-- **The bits of a literal**: its label in `w` bits, least significant first, then its sign. -/
def litBits (w : ℕ) (l : Literal ℕ) : List Bool :=
  List.ofFn (fun i : Fin w => l.1.testBit i) ++ [l.2]

/-! ### The constant stage -/

/-- The bit `i` of a bit string, or `false`. -/
def bitAt {m : ℕ} (b : BitString m) (i : ℕ) : Bool := if h : i < m then b ⟨i, h⟩ else false

/-- The number with the first `w` bits of `f`, least significant first. -/
def bitsVal (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | w + 1 => bitsVal f w + 2 ^ w * (f w).toNat

theorem bitsVal_testBit (v w : ℕ) : bitsVal (fun i => v.testBit i) w = v % 2 ^ w := by
  induction w with
  | zero => simp [bitsVal, Nat.mod_one]
  | succ w ih => rw [bitsVal, ih, mod_two_pow_succ]

theorem bitsVal_congr {f g : ℕ → Bool} {w : ℕ} (h : ∀ i < w, f i = g i) :
    bitsVal f w = bitsVal g w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [bitsVal, bitsVal, ih fun i hi => h i (by omega), h w (by omega)]

/-- The key of the input bits of the constant stage: the clause and tag bits, `s` slot bits,
and the fourteen comparison chains. -/
def Key.ofBits (s : ℕ) {m : ℕ} (b : BitString m) : Key where
  j := (bitAt b 0).toNat + 2 * (bitAt b 1).toNat
  tag := (bitAt b 2).toNat + 2 * (bitAt b 3).toNat
  slot := bitsVal (fun i => bitAt b (4 + i)) s
  c0 := bitAt b (4 + s)
  cGt1 := bitAt b (4 + s + 3)
  cGtN := bitAt b (4 + s + 4)
  cGtN1 := bitAt b (4 + s + 5)
  cLt2T := bitAt b (4 + s + 6)
  cGt2T := bitAt b (4 + s + 7)
  cLtT := bitAt b (4 + s + 8)
  cGtT := bitAt b (4 + s + 9)
  t0 := bitAt b (4 + s + 2)
  tGtT := bitAt b (4 + s + 10)
  pLtX := bitAt b (4 + s + 11)
  p0 := bitAt b (4 + s + 12)
  pGt1 := bitAt b (4 + s + 13)

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

/-- The default shape. -/
def defaultShape : Shape := (.const false, .const false)

/-- **The function of the constant stage**: bit `f` of literal `r` (`f < 13 + s`) is a tag or slot
bit or a selector of the shape of literal `r` of the key of the input bits. -/
noncomputable def tableFn (b : BitString (4 + slotBits k State + 14))
    (o : Fin (3 * (13 + slotBits k State))) : Bool :=
  let κ := Key.ofBits (slotBits k State) b
  let sh := (shapeOf tm κ).getD (o / (13 + slotBits k State)) defaultShape
  if o % (13 + slotBits k State) < 2 + slotBits k State then
    tagSlot sh (o % (13 + slotBits k State))
  else selOf κ.c0 κ.t0 sh (o % (13 + slotBits k State) - (2 + slotBits k State))

/-- **The constant stage**: a circuit computing `tableFn`, one disjunctive normal form per output.
Its size depends only on the machine. -/
noncomputable def tableCircuit :
    Circuit signature (4 + slotBits k State + 14) (3 * (13 + slotBits k State)) :=
  Circuit.pi fun o =>
    (Classical.choose (Formula.exists_computes (fun b => tableFn tm b o))).toCircuit

theorem eval_tableCircuit (b : BitString (4 + slotBits k State + 14)) :
    (tableCircuit tm).eval interpretation b = tableFn tm b := by
  funext o
  simp only [tableCircuit, Circuit.eval_pi, Formula.eval_toCircuit]
  exact Classical.choose_spec (Formula.exists_computes (fun b => tableFn tm b o)) b

/-! ### The wires of the output stage -/

/-- The wire of the constant `b`, after `N` inputs. -/
def constW (N : ℕ) (b : Bool) : ℕ := if b then N + 1 else N

/-- The wire of bit `q` of the field of width `w` at offset `off`, or of `false`. -/
def bitW (N off w q : ℕ) : ℕ := if q < w then off + q else N

/-- The wire of chain `k` after `q` bits, `true` for `q = 0`. -/
def chainW (N P k q : ℕ) : ℕ := if q = 0 then N + 1 else chainBase N + k * P + (q - 1)

/-- The first wire of the term `kk` of the payload bit `q`. -/
def uWire (s cb tb T q kk : ℕ) : ℕ :=
  if kk = 0 then 4 + q
  else if kk = 1 then bitW (4 + (s + cb + tb)) (4 + s) cb q
  else if kk ≤ 5 then
    (if s ≤ q ∧ q < s + cb then
      (if kk = 5 then constW (4 + (s + cb + tb)) ((2 * T).testBit (q - s))
        else bitW (4 + (s + cb + tb)) (4 + s) cb (q - s))
    else 4 + (s + cb + tb))
  else if kk ≤ 8 then
    (if s + cb ≤ q then
      (if kk = 8 then constW (4 + (s + cb + tb)) (T.testBit (q - s - cb))
        else bitW (4 + (s + cb + tb)) (4 + s + cb) tb (q - s - cb))
    else 4 + (s + cb + tb))
  else 4 + (s + cb + tb)

/-- The second wire of the term `kk` of the payload bit `q`: a borrow or a carry. -/
def vWire (s cb tb q kk : ℕ) : ℕ :=
  if kk = 1 then chainW (4 + (s + cb + tb)) (s + cb + tb) 0 q
  else if kk = 3 then
    (if s ≤ q ∧ q < s + cb then chainW (4 + (s + cb + tb)) (s + cb + tb) 0 (q - s)
      else 4 + (s + cb + tb))
  else if kk = 4 then
    (if s ≤ q ∧ q < s + cb then chainW (4 + (s + cb + tb)) (s + cb + tb) 1 (q - s)
      else 4 + (s + cb + tb))
  else if kk = 7 then
    (if s + cb ≤ q then chainW (4 + (s + cb + tb)) (s + cb + tb) 2 (q - s - cb)
      else 4 + (s + cb + tb))
  else 4 + (s + cb + tb)

/-- The number of wires of the field stage. -/
def aWidth (s cb tb : ℕ) (x : List Bool) (n T : ℕ) : ℕ :=
  4 + (s + cb + tb) + (fieldGates s cb tb x n T).length

/-- The wire of the lookup of `x`. -/
def lookW (s cb tb : ℕ) (x : List Bool) : ℕ :=
  if x.length = 0 then 4 + (s + cb + tb)
  else orBase (4 + (s + cb + tb)) (s + cb + tb) (Nat.size x.length) + (x.length - 1)

/-- **The wire read at input `j` of the formula of output bit `o`** of the output stage. Output
`o` is bit `o % (3 + P)` of literal `o / (3 + P)`, where `P = s + cb + tb`: two tag bits, `P`
payload bits and the sign. The output `r * (13 + s) + f` of the constant stage is wire
`aWidth + r * (13 + s) + f`. -/
def wireNat (s cb tb : ℕ) (x : List Bool) (n T o j : ℕ) : ℕ :=
  if o % (2 + (s + cb + tb) + 1) < 2 then
    (if j = 0 then aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) +
      o % (2 + (s + cb + tb) + 1) else 4 + (s + cb + tb))
  else if o % (2 + (s + cb + tb) + 1) < 2 + (s + cb + tb) then
    (if j = 0 then
      (if o % (2 + (s + cb + tb) + 1) - 2 < s then
        aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + o % (2 + (s + cb + tb) + 1)
      else 4 + (s + cb + tb))
    else if (j - 1) % 3 = 0 then
      aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + (2 + s + (j - 1) / 3)
    else if (j - 1) % 3 = 1 then uWire s cb tb T (o % (2 + (s + cb + tb) + 1) - 2) ((j - 1) / 3)
    else vWire s cb tb (o % (2 + (s + cb + tb) + 1) - 2) ((j - 1) / 3))
  else
    (if j = 0 then aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + (2 + s + 9)
    else if j = 1 then aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + (2 + s + 10)
    else if j = 2 then lookW s cb tb x
    else 4 + (s + cb + tb))

/-- The wire of input `i` of the constant stage: a clause, tag or slot bit, or the last gate of a
comparison chain. -/
def keyWire (s cb tb i : ℕ) : ℕ :=
  if i < 4 + s then i
  else chainBase (4 + (s + cb + tb)) + (i - (4 + s)) * (s + cb + tb) + (s + cb + tb - 1)

/-! ### Wire bounds -/

section Bounds

variable {s cb tb : ℕ} {x : List Bool} {n T : ℕ}

theorem chainBase_add_lt_aWidth {k q : ℕ} (hk : k < 14) (hq : q < s + cb + tb) :
    chainBase (4 + (s + cb + tb)) + k * (s + cb + tb) + q < aWidth s cb tb x n T := by
  have h₁ : k * (s + cb + tb) + (s + cb + tb) ≤ 14 * (s + cb + tb) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  simp only [aWidth, length_fieldGates, chainBase]
  omega

theorem lt_aWidth_of_lt {w : ℕ} (hw : w < 2 * (4 + (s + cb + tb)) + 2) :
    w < aWidth s cb tb x n T := by
  simp only [aWidth, length_fieldGates]
  omega

theorem constW_lt (b : Bool) : constW (4 + (s + cb + tb)) b < aWidth s cb tb x n T :=
  lt_aWidth_of_lt (by unfold constW; split <;> omega)

theorem bitW_lt {off w q : ℕ} (h : off + w ≤ 4 + (s + cb + tb)) :
    bitW (4 + (s + cb + tb)) off w q < aWidth s cb tb x n T :=
  lt_aWidth_of_lt (by unfold bitW; split <;> omega)

theorem chainW_lt {k q : ℕ} (hk : k < 14) (hq : q ≤ s + cb + tb) :
    chainW (4 + (s + cb + tb)) (s + cb + tb) k q < aWidth s cb tb x n T := by
  unfold chainW
  split
  · exact lt_aWidth_of_lt (by omega)
  · exact chainBase_add_lt_aWidth hk (by omega)

theorem uWire_lt (q kk : ℕ) (hq : q < s + cb + tb) :
    uWire s cb tb T q kk < aWidth s cb tb x n T := by
  unfold uWire
  split_ifs <;> first
    | exact lt_aWidth_of_lt (by omega)
    | exact constW_lt _
    | exact bitW_lt (by omega)

theorem vWire_lt (q kk : ℕ) (hq : q < s + cb + tb) :
    vWire s cb tb q kk < aWidth s cb tb x n T := by
  unfold vWire
  split_ifs <;> first
    | exact lt_aWidth_of_lt (by omega)
    | exact chainW_lt (by omega) (by omega)

theorem lookW_lt : lookW s cb tb x < aWidth s cb tb x n T := by
  unfold lookW
  split
  · exact lt_aWidth_of_lt (by omega)
  · simp only [aWidth, length_fieldGates, orBase, treeBase, chainBase]
    omega

/-- The wires of the output stage lie among the wires of the field and constant stages. -/
theorem wireNat_lt {o j : ℕ} (ho : o < 3 * (2 + (s + cb + tb) + 1)) (hj : j < 28) :
    wireNat s cb tb x n T o j < aWidth s cb tb x n T + 3 * (13 + s) := by
  have hj3 : (j - 1) / 3 ≤ 8 := by omega
  have hr : o / (2 + (s + cb + tb) + 1) < 3 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hr' : o / (2 + (s + cb + tb) + 1) * (13 + s) + (13 + s) ≤ 3 * (13 + s) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
  have hU := fun kk (hq : o % (2 + (s + cb + tb) + 1) - 2 < s + cb + tb) =>
    uWire_lt (x := x) (n := n) (T := T) (o % (2 + (s + cb + tb) + 1) - 2) kk hq
  have hV := fun kk (hq : o % (2 + (s + cb + tb) + 1) - 2 < s + cb + tb) =>
    vWire_lt (x := x) (n := n) (T := T) (o % (2 + (s + cb + tb) + 1) - 2) kk hq
  have hL := lookW_lt (s := s) (cb := cb) (tb := tb) (x := x) (n := n) (T := T)
  have hN : 4 + (s + cb + tb) < aWidth s cb tb x n T := lt_aWidth_of_lt (by omega)
  unfold wireNat
  split_ifs
  all_goals first
    | omega
    | (have := hU ((j - 1) / 3) (by omega); omega)
    | (have := hV ((j - 1) / 3) (by omega); omega)

theorem keyWire_lt {i : ℕ} (hi : i < 4 + s + 14) : keyWire s cb tb i < aWidth s cb tb x n T := by
  unfold keyWire
  split
  · exact lt_aWidth_of_lt (by omega)
  · have h₁ : (i - (4 + s)) * (s + cb + tb) + (s + cb + tb) ≤ 14 * (s + cb + tb) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have := Nat.one_le_two_pow (n := Nat.size x.length + 1)
    simp only [aWidth, length_fieldGates, chainBase]
    omega

end Bounds

/-! ### The circuit -/

section Assembly

variable {s cb tb : ℕ} {x : List Bool} {n T : ℕ}

theorem isSome_fieldCode (hm : Nat.size x.length ≤ s + cb + tb) :
    (Circuit.ofCode (σ := signature) (4 + (s + cb + tb)) (aWidth s cb tb x n T)
      (fieldGates s cb tb x n T, List.range (aWidth s cb tb x n T))).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_of_allGates (allGates_wellFormedAt_fieldGates hm), by simp, fun i hi => ?_⟩
  simpa [aWidth] using hi

/-- **The field stage** as a circuit whose outputs are all its wires. -/
noncomputable def fieldCircuit (hm : Nat.size x.length ≤ s + cb + tb) :
    Circuit signature (4 + (s + cb + tb)) (aWidth s cb tb x n T) :=
  (Circuit.ofCode _ _ (fieldGates s cb tb x n T, List.range (aWidth s cb tb x n T))).get
    (isSome_fieldCode hm)

theorem code_fieldCircuit (hm : Nat.size x.length ≤ s + cb + tb) :
    (fieldCircuit (n := n) (T := T) hm).code =
      (fieldGates s cb tb x n T, List.range (aWidth s cb tb x n T)) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

theorem size_fieldCircuit (hm : Nat.size x.length ≤ s + cb + tb) :
    (fieldCircuit (n := n) (T := T) hm).size = (fieldGates s cb tb x n T).length := by
  rw [← Circuit.length_code_fst, code_fieldCircuit]

theorem eval_fieldCircuit (hm : Nat.size x.length ≤ s + cb + tb) (idx : ℕ)
    (w : Fin (aWidth s cb tb x n T)) :
    (fieldCircuit hm).eval interpretation (fun i => idx.testBit i) w =
      fieldVal s cb tb x n T idx w := by
  have hout : ((fieldCircuit (n := n) (T := T) hm).outputs w).toNat = w := by
    have h := congrArg Prod.snd (code_fieldCircuit (n := n) (T := T) hm)
    simp only [Circuit.code] at h
    have := congrArg (fun l => l[w.val]?) h
    simpa using this
  rw [Circuit.eval_eq_evalOutput, code_fieldCircuit, hout, evalOutput]
  exact getD_evalCode_fieldGates hm idx (by simpa [aWidth] using w.isLt)

end Assembly

/-! ### Values of the wires read by the output stage -/

section Values

variable {s cb tb : ℕ} {x : List Bool} {n T : ℕ}

theorem fieldVal_constW (idx : ℕ) (b : Bool) :
    fieldVal s cb tb x n T idx (constW (4 + (s + cb + tb)) b) = b := by
  cases b
  · exact fieldVal_false idx
  · exact fieldVal_true idx

theorem fieldVal_bitW (idx : ℕ) {off w q : ℕ} (h : off + w ≤ 4 + (s + cb + tb)) :
    fieldVal s cb tb x n T idx (bitW (4 + (s + cb + tb)) off w q) =
      (idx / 2 ^ off % 2 ^ w).testBit q := by
  unfold bitW
  split
  · rw [fieldVal_input idx (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [*, Nat.add_comm]
  · rw [fieldVal_false, Nat.testBit_mod_two_pow]
    simp [*]

theorem fieldVal_payload (idx : ℕ) {q : ℕ} (hq : q < s + cb + tb) :
    fieldVal s cb tb x n T idx (4 + q) = (idx / 16).testBit q := by
  rw [fieldVal_input idx (by omega), show idx / 16 = idx / 2 ^ 4 from rfl,
    Nat.testBit_div_two_pow, Nat.add_comm]

/-- The value of chain `k` after `q` bits, through `chainW`. -/
theorem fieldVal_chainW (idx : ℕ) {k q : ℕ} (hk : k < 14) (hq : q ≤ s + cb + tb)
    (hinit : (chain s cb tb x.length n T k).init = true) :
    fieldVal s cb tb x n T idx (chainW (4 + (s + cb + tb)) (s + cb + tb) k q) =
      chainVal (chain s cb tb x.length n T k) idx q := by
  unfold chainW
  split
  · subst q
    rw [fieldVal_true]
    simp [chainVal, cmp, hinit, Nat.mod_one]
  · rw [fieldVal_chain idx hk (by omega), Nat.sub_add_cancel (by omega)]

/-- The column of the payload, from the clause number. -/
theorem div_mod_eq_colOf (idx : ℕ) :
    idx / 2 ^ (4 + s) % 2 ^ cb = colOf s cb (idx / 16) := by
  rw [colOf, Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- The block of the payload, from a clause number of `4 + (s + cb + tb)` bits. -/
theorem div_mod_eq_timeOf {idx : ℕ} (hidx : idx < 2 ^ (4 + (s + cb + tb))) :
    idx / 2 ^ (4 + s + cb) % 2 ^ tb = timeOf s cb (idx / 16) := by
  have h₁ : idx / 2 ^ (4 + s + cb) = timeOf s cb (idx / 16) := by
    rw [timeOf, Nat.pow_add, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  rw [h₁, Nat.mod_eq_of_lt]
  rw [← h₁]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add]
  calc idx < 2 ^ (4 + (s + cb + tb)) := hidx
    _ = 2 ^ (4 + s + cb + tb) := by congr 1; omega

theorem fieldVal_borrowC (idx : ℕ) {q : ℕ} (hq : q ≤ s + cb + tb) :
    fieldVal s cb tb x n T idx (chainW (4 + (s + cb + tb)) (s + cb + tb) 0 q) =
      decide (colOf s cb (idx / 16) % 2 ^ q = 0) := by
  rw [fieldVal_chainW idx (by omega) hq rfl]
  simp only [chainVal, chain, ↓reduceIte, cmp, Nat.zero_mod, div_mod_eq_colOf]
  simp

theorem fieldVal_carryC (idx : ℕ) {q : ℕ} (hq : q ≤ s + cb + tb) :
    fieldVal s cb tb x n T idx (chainW (4 + (s + cb + tb)) (s + cb + tb) 1 q) =
      decide (colOf s cb (idx / 16) % 2 ^ q = 2 ^ q - 1) := by
  rw [fieldVal_chainW idx (by omega) hq rfl]
  simp only [chainVal, chain, one_ne_zero, ↓reduceIte, cmp, div_mod_eq_colOf]
  have hK : (2 ^ (s + cb + tb) - 1) % 2 ^ q = 2 ^ q - 1 := by
    obtain ⟨d, hd⟩ : ∃ d, s + cb + tb = q + d := ⟨s + cb + tb - q, by omega⟩
    rw [hd, Nat.pow_add]
    have h1 := Nat.one_le_two_pow (n := q)
    have h2 := Nat.one_le_two_pow (n := d)
    have h3 : 2 ^ q ≤ 2 ^ q * 2 ^ d := Nat.le_mul_of_pos_right _ (by omega)
    rw [show 2 ^ q * 2 ^ d - 1 = 2 ^ q * (2 ^ d - 1) + (2 ^ q - 1) by
      rw [Nat.mul_sub_one]; omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hK]
  have := Nat.mod_lt (colOf s cb (idx / 16)) (Nat.two_pow_pos q)
  rw [Bool.eq_iff_iff]
  simp
  omega

theorem fieldVal_borrowT (idx : ℕ) (hidx : idx < 2 ^ (4 + (s + cb + tb))) {q : ℕ}
    (hq : q ≤ s + cb + tb) :
    fieldVal s cb tb x n T idx (chainW (4 + (s + cb + tb)) (s + cb + tb) 2 q) =
      decide (timeOf s cb (idx / 16) % 2 ^ q = 0) := by
  rw [fieldVal_chainW idx (by omega) hq rfl]
  simp only [chainVal, chain, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte, cmp,
    Nat.zero_mod, div_mod_eq_timeOf hidx]
  simp

/-- **The formula of an output bit computes `outBit`** on the values of its wires: the values of
the field stage, and the outputs `ts` of the constant stage for its literal. -/
theorem eval_outTemplate_wireNat {z : ℕ → Bool} {idx : ℕ} (hidx : idx < 2 ^ (4 + (s + cb + tb)))
    (hF : ∀ w < aWidth s cb tb x n T, z w = fieldVal s cb tb x n T idx w) (o : ℕ) :
    outTemplate.eval interpretation (fun j => z (wireNat s cb tb x n T o j)) =
      outBit s cb tb
        (fun f => z (aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + f))
        (fun q => z (aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) + (2 + s + q)))
        (idx / 16) (colOf s cb (idx / 16)) (timeOf s cb (idx / 16)) T (z (lookW s cb tb x))
        (o % (2 + (s + cb + tb) + 1)) := by
  have hN : z (4 + (s + cb + tb)) = false :=
    (hF _ (lt_aWidth_of_lt (by omega))).trans (fieldVal_false idx)
  have hC (b : Bool) : z (constW (4 + (s + cb + tb)) b) = b :=
    (hF _ (constW_lt b)).trans (fieldVal_constW idx b)
  have hcol (q : ℕ) :
      z (bitW (4 + (s + cb + tb)) (4 + s) cb q) = (colOf s cb (idx / 16)).testBit q := by
    rw [hF _ (bitW_lt (by omega)), fieldVal_bitW idx (by omega), div_mod_eq_colOf]
  have htime (q : ℕ) :
      z (bitW (4 + (s + cb + tb)) (4 + s + cb) tb q) = (timeOf s cb (idx / 16)).testBit q := by
    rw [hF _ (bitW_lt (by omega)), fieldVal_bitW idx (by omega), div_mod_eq_timeOf hidx]
  have hb0 {q : ℕ} (hq : q ≤ s + cb + tb) :
      z (chainW (4 + (s + cb + tb)) (s + cb + tb) 0 q) =
        decide (colOf s cb (idx / 16) % 2 ^ q = 0) := by
    rw [hF _ (chainW_lt (by omega) hq), fieldVal_borrowC idx hq]
  have hb1 {q : ℕ} (hq : q ≤ s + cb + tb) :
      z (chainW (4 + (s + cb + tb)) (s + cb + tb) 1 q) =
        decide (colOf s cb (idx / 16) % 2 ^ q = 2 ^ q - 1) := by
    rw [hF _ (chainW_lt (by omega) hq), fieldVal_carryC idx hq]
  have hb2 {q : ℕ} (hq : q ≤ s + cb + tb) :
      z (chainW (4 + (s + cb + tb)) (s + cb + tb) 2 q) =
        decide (timeOf s cb (idx / 16) % 2 ^ q = 0) := by
    rw [hF _ (chainW_lt (by omega) hq), fieldVal_borrowT idx hidx hq]
  rw [eval_outTemplate_nat (fun j => z (wireNat s cb tb x n T o j))]
  simp only [wireNat]
  unfold outBit
  have hi := Nat.mod_lt o (show 0 < 2 + (s + cb + tb) + 1 by omega)
  generalize o % (2 + (s + cb + tb) + 1) = i at hi ⊢
  generalize aWidth s cb tb x n T + o / (2 + (s + cb + tb) + 1) * (13 + s) = B
  by_cases h2 : i < 2
  · simp [h2, hN]
  · by_cases hP : i < 2 + (s + cb + tb)
    · have hq : i - 2 < s + cb + tb := by omega
      have hi2 : 2 + (i - 2) = i := by omega
      generalize i - 2 = q at hq hi2
      subst hi2
      have hp : z (4 + q) = (idx / 16).testBit q := by
        rw [hF _ (lt_aWidth_of_lt (by omega)), fieldVal_payload idx hq]
      have h0 : z (if q < s then B + (2 + q) else 4 + (s + cb + tb)) =
          (decide (q < s) && z (B + (2 + q))) := by
        split <;> simp [*]
      simp only [h2, hP, ↓reduceIte, h0, uWire, vWire, payTerm, colTerm,
        timeTerm, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, one_ne_zero, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, Nat.reduceEqDiff, Nat.reduceLeDiff, hp, hcol, hb0 hq.le, hN,
        Bool.xor_false, Nat.add_zero]
      by_cases hc : s ≤ q ∧ q < s + cb
      · have ht : ¬ s + cb ≤ q := by omega
        simp only [hc, ht, and_self, ↓reduceIte, hcol, hC, hb0 (show q - s ≤ s + cb + tb by omega),
          hb1 (show q - s ≤ s + cb + tb by omega), hN, Bool.xor_false, Bool.and_false,
          Bool.or_false, decide_true, decide_false, Bool.true_and, Bool.false_and]
        simp only [Bool.or_assoc]
      · simp only [hc, ↓reduceIte, hN, Bool.xor_false, Bool.and_false, Bool.or_false,
          decide_false, Bool.false_and]
        by_cases ht : s + cb ≤ q
        · simp only [ht, ↓reduceIte, htime, hC, hb2 (show q - s - cb ≤ s + cb + tb by omega),
            decide_true, Bool.true_and]
          simp only [Bool.or_assoc]
        · simp only [ht, ↓reduceIte, hN, Bool.xor_false, Bool.and_false, Bool.or_false,
            decide_false, Bool.false_and]
    · simp [h2, hP, hN]

private theorem bitsVal_two (f : ℕ → Bool) : bitsVal f 2 = (f 0).toNat + 2 * (f 1).toNat := by
  simp only [bitsVal]; omega

/-- The value of the last gate of chain `k`. -/
theorem fieldVal_keyWire_chain (idx : ℕ) {k : ℕ} (hk : k < 14) (hP : 1 ≤ s + cb + tb) :
    fieldVal s cb tb x n T idx (keyWire s cb tb (4 + s + k)) =
      chainVal (chain s cb tb x.length n T k) idx (s + cb + tb) := by
  have h := fieldVal_chain (x := x) (n := n) (T := T) idx hk
    (show s + cb + tb - 1 < s + cb + tb by omega)
  rw [Nat.sub_add_cancel hP] at h
  simp only [keyWire, show ¬ 4 + s + k < 4 + s by omega, ↓reduceIte,
    show 4 + s + k - (4 + s) = k by omega]
  exact h

/-- **The key read by the constant stage is the key of the fields** of the clause number. -/
theorem ofBits_keyWire {idx : ℕ} (hidx : idx < 2 ^ (4 + (s + cb + tb))) (hs : 1 ≤ s)
    (h2T : 2 * T < 2 ^ cb) (hT : T < 2 ^ tb) (hn : n < 2 * T) (hx : x.length ≤ n) :
    Key.ofBits s (fun i : Fin (4 + s + 14) => fieldVal s cb tb x n T idx (keyWire s cb tb i)) =
      Key.ofFields s cb x.length n T (idx % 4) (idx / 4 % 4) (idx / 16) := by
  have hP : 1 ≤ s + cb + tb := by omega
  have hbit (i : ℕ) (hi : i < 4 + s + 14) : bitAt (fun i : Fin (4 + s + 14) =>
      fieldVal s cb tb x n T idx (keyWire s cb tb i)) i =
      fieldVal s cb tb x n T idx (keyWire s cb tb i) := by simp [bitAt, hi]
  have hin (i : ℕ) (hi : i < 4 + s) : bitAt (fun i : Fin (4 + s + 14) =>
      fieldVal s cb tb x n T idx (keyWire s cb tb i)) i = idx.testBit i := by
    rw [hbit i (by omega), keyWire, ite_eq_left hi, fieldVal_input idx (by omega)]
  have hch (k : ℕ) (hk : k < 14) : bitAt (fun i : Fin (4 + s + 14) =>
      fieldVal s cb tb x n T idx (keyWire s cb tb i)) (4 + s + k) =
      chainVal (chain s cb tb x.length n T k) idx (s + cb + tb) := by
    rw [hbit _ (by omega), fieldVal_keyWire_chain idx hk hP]
  have hcb : 2 ^ cb ≤ 2 ^ (s + cb + tb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htb : 2 ^ tb ≤ 2 ^ (s + cb + tb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : colOf s cb (idx / 16) < 2 ^ cb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have ht : timeOf s cb (idx / 16) < 2 ^ tb := by
    rw [← div_mod_eq_timeOf hidx]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hp : idx / 16 < 2 ^ (s + cb + tb) := by
    apply Nat.div_lt_of_lt_mul
    calc idx < 2 ^ (4 + (s + cb + tb)) := hidx
      _ = 16 * 2 ^ (s + cb + tb) := by rw [Nat.pow_add]
  have hpmod : idx / 2 ^ 4 % 2 ^ (s + cb + tb) = idx / 16 := Nat.mod_eq_of_lt hp
  have h1 : 1 < 2 ^ (s + cb + tb) := Nat.one_lt_two_pow (by omega)
  have hcv (gt : Bool) (K : ℕ) (e : Bool) (hK : K < 2 ^ (s + cb + tb)) :
      cmp gt (idx / 2 ^ (4 + s) % 2 ^ cb % 2 ^ (s + cb + tb)) (K % 2 ^ (s + cb + tb)) e =
        cmp gt (colOf s cb (idx / 16)) K e := by
    rw [div_mod_eq_colOf, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hK]
  have htv (gt : Bool) (K : ℕ) (e : Bool) (hK : K < 2 ^ (s + cb + tb)) :
      cmp gt (idx / 2 ^ (4 + s + cb) % 2 ^ tb % 2 ^ (s + cb + tb)) (K % 2 ^ (s + cb + tb)) e =
        cmp gt (timeOf s cb (idx / 16)) K e := by
    rw [div_mod_eq_timeOf hidx, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hK]
  have hpv (gt : Bool) (K : ℕ) (e : Bool) (hK : K < 2 ^ (s + cb + tb)) :
      cmp gt (idx / 2 ^ 4 % 2 ^ (s + cb + tb) % 2 ^ (s + cb + tb)) (K % 2 ^ (s + cb + tb)) e =
        cmp gt (idx / 16) K e := by
    rw [Nat.mod_mod, hpmod, Nat.mod_eq_of_lt hK]
  have hc0 : bitAt (fun i : Fin (4 + s + 14) =>
      fieldVal s cb tb x n T idx (keyWire s cb tb i)) (4 + s) =
      chainVal (chain s cb tb x.length n T 0) idx (s + cb + tb) := by
    simpa using hch 0 (by omega)
  simp only [Key.ofBits, Key.ofFields, hc0,
    hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hin 3 (by omega)]
  rw [bitsVal_congr (g := fun i => (idx / 16).testBit i) (fun i hi => by
      rw [hin _ (by omega), show idx / 16 = idx / 2 ^ 4 from rfl, Nat.testBit_div_two_pow,
        Nat.add_comm]), bitsVal_testBit]
  have hj : (idx.testBit 0).toNat + 2 * (idx.testBit 1).toNat = idx % 4 := by
    have := bitsVal_testBit idx 2
    rw [bitsVal_two] at this
    exact this
  have htag : (idx.testBit 2).toNat + 2 * (idx.testBit 3).toNat = idx / 4 % 4 := by
    have := bitsVal_testBit (idx / 4) 2
    rw [bitsVal_two, show idx / 4 = idx / 2 ^ 2 from rfl, Nat.testBit_div_two_pow,
      Nat.testBit_div_two_pow] at this
    exact this
  rw [hj, htag]
  simp only [hch 3 (by omega), hch 4 (by omega), hch 5 (by omega), hch 6 (by omega),
    hch 7 (by omega), hch 8 (by omega), hch 9 (by omega), hch 2 (by omega), hch 10 (by omega),
    hch 11 (by omega), hch 12 (by omega), hch 13 (by omega), chainVal, chain]
  simp only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte, Nat.reduceEqDiff]
  simp (disch := omega) only [hcv, htv, hpv]
  simp [cmp]

end Values


end Cslib.Circuits.Boolean.Tableau.Decoder
