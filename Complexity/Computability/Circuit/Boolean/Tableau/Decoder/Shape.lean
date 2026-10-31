/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Succinct

/-!
# The clauses of the succinct tableau as symbolic shapes

A clause of the tableau formula on bit-field labels (`Cslib.Circuits.Boolean.Tableau.clauseOf`)
is determined by finitely many data: its clause and tag fields, its slot, and thirteen comparisons
of the column `c`, the block `t` and the payload `p` with `0`, `1`, `n`, `n + 1`, `2 T`, `T` and
the length of the fixed prefix `x` (`Key`). From these, the clause is a list of three symbolic
literals (`shapeOf`): the label of each literal is a constant, the input `p`, the input `c - 1`,
or a position whose column is `0`, `c`, `c - 1`, `c + 1` or `2 T` and whose block is `t`, `t - 1`
or `T` (`LabelSrc`); its sign is a constant or the bit of `x` at `p` (`SignSrc`). Evaluating the
shapes on the fields gives the clause (`clauseOf_eq_map_shapeOf`).

This is the case analysis behind the decoder circuit: a circuit of constant size computes the
shape from the key, and circuits linear in the field widths compute the fields `c - 1`, `c + 1`
and `t - 1` and the comparisons.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Decoder.LabelSrc`,
  `Cslib.Circuits.Boolean.Tableau.Decoder.SignSrc`: symbolic labels and signs.
* `Cslib.Circuits.Boolean.Tableau.Decoder.Key`,
  `Cslib.Circuits.Boolean.Tableau.Decoder.Key.ofFields`: the finite data determining a clause.
* `Cslib.Circuits.Boolean.Tableau.Decoder.shapeOf`: the symbolic clause of a key.

## Main results

* `Cslib.Circuits.Boolean.Tableau.Decoder.clauseOf_eq_map_shapeOf`: the clause with given fields
  is the evaluation of the shape of their key.
* `Cslib.Circuits.Boolean.Tableau.Decoder.inRange_of_mem_shapeOf`: the labels of the shapes stay
  within their fields.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau.Decoder

open Turing MultiTapeTM Cslib.Logic.PL

/-! ### Symbolic labels -/

/-- The column field of a symbolic position label. -/
inductive ColSrc where
  /-- The column `0`. -/
  | zero
  /-- The column `c`. -/
  | same
  /-- The column `c - 1`. -/
  | prev
  /-- The column `c + 1`. -/
  | next
  /-- The column `2 T`. -/
  | last
  deriving DecidableEq

/-- The block field of a symbolic position label. -/
inductive TimeSrc where
  /-- The block `t`. -/
  | same
  /-- The block `t - 1`. -/
  | prev
  /-- The block `T`. -/
  | top
  deriving DecidableEq

/-- A symbolic label. -/
inductive LabelSrc where
  /-- The constant gate `b`. -/
  | const (b : Bool)
  /-- The input `p` (`false`) or `c - 1` (`true`). -/
  | input (fromCol : Bool)
  /-- A position, with its slot and the sources of its column and block. -/
  | pos (slot : ℕ) (col : ColSrc) (time : TimeSrc)

/-- A symbolic sign. -/
inductive SignSrc where
  /-- A constant sign. -/
  | const (b : Bool)
  /-- The bit of `x` at the payload. -/
  | lookup

/-- A symbolic literal. -/
abbrev Shape := LabelSrc × SignSrc

/-- The column of a column source. -/
def ColSrc.eval (c T : ℕ) : ColSrc → ℕ
  | .zero => 0
  | .same => c
  | .prev => c - 1
  | .next => c + 1
  | .last => 2 * T

/-- The block of a block source. -/
def TimeSrc.eval (t T : ℕ) : TimeSrc → ℕ
  | .same => t
  | .prev => t - 1
  | .top => T

/-- The label of a symbolic label, for slot and column widths `s` and `cb`, payload `p`, column
`c` and block `t`. -/
def LabelSrc.eval (s cb p c t T : ℕ) : LabelSrc → ℕ
  | .const b => constLabel b
  | .input false => inputLabel p
  | .input true => inputLabel (c - 1)
  | .pos sl cs ts => 2 + 4 * (sl + 2 ^ s * (cs.eval c T + 2 ^ cb * ts.eval t T))

/-- The sign of a symbolic sign. -/
def SignSrc.eval (x : List Bool) (p : ℕ) : SignSrc → Bool
  | .const b => b
  | .lookup => x.getD p false

/-- The literal of a symbolic literal. -/
def Shape.eval (s cb p c t T : ℕ) (x : List Bool) (sh : Shape) : Literal ℕ :=
  (sh.1.eval s cb p c t T, sh.2.eval x p)

/-! ### Keys -/

/-- **The finite data that determine a clause**: the clause and tag fields, the slot, and
comparisons of the column `c`, the block `t` and the payload `p`. -/
structure Key where
  /-- The clause field. -/
  j : ℕ
  /-- The tag field. -/
  tag : ℕ
  /-- The slot. -/
  slot : ℕ
  /-- `c = 0`. -/
  c0 : Bool
  /-- `1 < c`. -/
  cGt1 : Bool
  /-- `n < c`. -/
  cGtN : Bool
  /-- `n + 1 < c`. -/
  cGtN1 : Bool
  /-- `c < 2 T`. -/
  cLt2T : Bool
  /-- `2 T < c`. -/
  cGt2T : Bool
  /-- `c < T`. -/
  cLtT : Bool
  /-- `T < c`. -/
  cGtT : Bool
  /-- `t = 0`. -/
  t0 : Bool
  /-- `T < t`. -/
  tGtT : Bool
  /-- `p < X`, for the length `X` of the fixed prefix. -/
  pLtX : Bool
  /-- `p = 0`. -/
  p0 : Bool
  /-- `1 < p`. -/
  pGt1 : Bool

/-- The column of a payload. -/
abbrev colOf (s cb p : ℕ) : ℕ := p / 2 ^ s % 2 ^ cb

/-- The block of a payload. -/
abbrev timeOf (s cb p : ℕ) : ℕ := p / 2 ^ s / 2 ^ cb

/-- **The key of the fields** `j`, `tag` and `p` of a clause number, for slot and column widths
`s` and `cb`, a prefix of length `X`, `n` inputs and `T` steps. -/
def Key.ofFields (s cb X n T j tag p : ℕ) : Key where
  j := j
  tag := tag
  slot := p % 2 ^ s
  c0 := decide (colOf s cb p = 0)
  cGt1 := decide (1 < colOf s cb p)
  cGtN := decide (n < colOf s cb p)
  cGtN1 := decide (n + 1 < colOf s cb p)
  cLt2T := decide (colOf s cb p < 2 * T)
  cGt2T := decide (2 * T < colOf s cb p)
  cLtT := decide (colOf s cb p < T)
  cGtT := decide (T < colOf s cb p)
  t0 := decide (timeOf s cb p = 0)
  tGtT := decide (T < timeOf s cb p)
  pLtX := decide (p < X)
  p0 := decide (p = 0)
  pGt1 := decide (1 < p)

/-- The guard of a reference, from a key. -/
def Key.guard (κ : Key) : Guard → Bool
  | .always => true
  | .pos => !κ.c0
  | .ltLast => κ.cLt2T
  | .inRange => !κ.c0 && !κ.cGtN
  | .outRange => !(!κ.c0 && !κ.cGtN)
  | .isZero => κ.c0
  | .isEnd => κ.cGtN && !κ.cGtN1
  | .leEnd => !κ.c0 && !κ.cGtN1

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]

/-- Whether a position is admissible in the column, from a key. -/
def Key.colOK (κ : Key) : Loc k State → Bool
  | .scan _ => !κ.cGt2T
  | .col .. => !κ.cGt2T
  | .glob _ => κ.c0
  | .gf .. => κ.c0

/-- The column source of a reference to a position: `0` for the global positions. -/
def colSrcOf : Loc k State → ColSel → ColSrc
  | .glob _, _ => .zero
  | .gf .., _ => .zero
  | _, .same => .same
  | _, .prev => .prev
  | _, .next => .next
  | _, .last => .last

/-- The symbolic label of a reference, from a key. -/
noncomputable def Key.refSrc (κ : Key) : Ref k State → LabelSrc
  | .fls => .const false
  | .tru => .const true
  | .inp => if !κ.c0 && !κ.cGtN then .input true else .const false
  | .node p l cs g => if κ.guard g then .pos l.slot (colSrcOf l cs) (if p then .prev else .same)
      else .const false

/-- The initial value of a column feature, from a key. -/
def Key.colInit (κ : Key) : ColFeat k → Bool
  | .inPos => !κ.c0 && !κ.cGt1
  | .head _ => !κ.cLtT && !κ.cGtT
  | .cell _ s => decide (s = none)

variable (tm : MultiTapeTM k Bool State)

/-- The initial value of a position, from a key. -/
def Key.initBit (κ : Key) : Loc k State → Bool
  | .gf f true j => decide (j = 7) && gfInit tm f
  | .col f true j => decide (j = 7) && κ.colInit f
  | _ => false

/-- Clauses on symbolic labels with constant signs. -/
def lift (cl : Clause LabelSrc) : List Shape := cl.map fun l => (l.1, .const l.2)

/-- The symbolic tautology. -/
def tautShape : List Shape :=
  [(.const false, .const true), (.const false, .const false), (.const false, .const true)]

/-- The symbolic clause `j` of a position. -/
noncomputable def posShape (κ : Key) (l : Loc k State) (j : Fin 3) : Clause LabelSrc :=
  if κ.t0 then tseitinClause (.const (κ.initBit tm l)) (.pos l.slot .same .same) (.const false)
    (.const false) j
  else tseitinClause (table tm l).1 (.pos l.slot .same .same) (κ.refSrc (table tm l).2.1)
    (κ.refSrc (table tm l).2.2) j

/-- The symbolic label of the output. -/
noncomputable def outSrc : LabelSrc :=
  .pos (Loc.gf (k := k) (State := State) (.out (.one true)) true 7).slot .zero .top

/-- **The symbolic clause of a key**, following `clauseOf`. -/
noncomputable def shapeOf (κ : Key) : List Shape :=
  if hj : κ.j < 3 then
    if κ.tag = 0 then
      if !κ.pGt1 then
        lift (tseitinClause (.const !κ.p0) (.const !κ.p0) (.const false) (.const false) ⟨κ.j, hj⟩)
      else tautShape
    else if κ.tag = 1 then
      if κ.j = 0 ∧ κ.pLtX then [(.input false, .lookup), (.input false, .lookup),
        (.input false, .lookup)]
      else tautShape
    else if κ.tag = 2 then
      match Loc.ofSlot (k := k) (State := State) κ.slot with
      | some l => if !κ.tGtT && κ.colOK l then lift (posShape tm κ l ⟨κ.j, hj⟩) else tautShape
      | none => tautShape
    else if κ.j = 0 ∧ κ.p0 then
      [(outSrc (k := k) (State := State), .const true),
        (outSrc (k := k) (State := State), .const true),
        (outSrc (k := k) (State := State), .const true)]
    else tautShape
  else tautShape

/-! ### Evaluation -/

section Eval

variable {s cb X n T : ℕ}

theorem Key.guard_ofFields (j tag p : ℕ) (g : Guard) :
    (Key.ofFields s cb X n T j tag p).guard g = g.test n T (colOf s cb p) := by
  cases g <;> simp only [Key.guard, Key.ofFields, Guard.test, numCols] <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

omit [DecidableEq State] in
theorem Key.colOK_ofFields (j tag p : ℕ) (l : Loc k State) :
    (Key.ofFields s cb X n T j tag p).colOK l = decide (l.ColOK T (colOf s cb p)) := by
  cases l <;> simp only [Key.colOK, Key.ofFields, Loc.ColOK, numCols] <;>
    rw [Bool.eq_iff_iff] <;> simp

theorem Key.initBit_ofFields (j tag p : ℕ) (l : Loc k State) :
    (Key.ofFields s cb X n T j tag p).initBit tm l = Tableau.initBit tm T (colOf s cb p) l := by
  rcases l with l | l | ⟨f, (_ | _), j⟩ | ⟨f, (_ | _), j⟩ <;> try rfl
  rcases f with _ | i | ⟨i, s⟩ <;>
    simp only [Key.initBit, Tableau.initBit, Key.colInit, Tableau.colInit, Key.ofFields] <;>
    congr 1 <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

omit [DecidableEq State] in
theorem colSrcOf_eval (l : Loc k State) (cs : ColSel) (c T : ℕ) :
    (colSrcOf l cs).eval c T = l.labelCol (cs.apply T c) := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> cases cs <;> rfl

omit [DecidableEq State] in
/-- **The symbolic label of a reference evaluates to its label.** -/
theorem refSrc_eval {t : ℕ} (j tag p : ℕ) (r : Ref k State) :
    ((Key.ofFields (slotBits k State) (colBits T) X n T j tag p).refSrc r).eval (slotBits k State)
        (colBits T) p (colOf (slotBits k State) (colBits T) p) t T =
      r.label n T t (colOf (slotBits k State) (colBits T) p) := by
  rcases r with _ | _ | _ | ⟨q, l, cs, g⟩
  · rfl
  · rfl
  · simp only [Key.refSrc, Ref.label, Key.ofFields]
    by_cases h : 1 ≤ colOf (slotBits k State) (colBits T) p ∧
        colOf (slotBits k State) (colBits T) p ≤ n
    · have h₁ : (!decide (colOf (slotBits k State) (colBits T) p = 0) &&
          !decide (n < colOf (slotBits k State) (colBits T) p)) = true := by simp; omega
      simp only [h₁, h, ↓reduceIte]
      rfl
    · have h₁ : ¬ (!decide (colOf (slotBits k State) (colBits T) p = 0) &&
          !decide (n < colOf (slotBits k State) (colBits T) p)) = true := by simp; omega
      simp only [h₁, h, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [Key.refSrc, Ref.label, Key.guard_ofFields]
    by_cases hg : g.test n T (colOf (slotBits k State) (colBits T) p) = true
    · simp only [hg, ↓reduceIte, LabelSrc.eval, posLabel, colSrcOf_eval]
      cases q <;> rfl
    · simp only [hg, ↓reduceIte, Bool.false_eq_true]
      rfl

theorem map_eval_lift (s cb p c t T : ℕ) (x : List Bool) (cl : Clause LabelSrc) :
    (lift cl).map (Shape.eval s cb p c t T x) = cl.relabel (LabelSrc.eval s cb p c t T) := by
  simp [lift, Clause.relabel, Shape.eval, SignSrc.eval, Function.comp_def, Prod.map]

/-- **The clause with given fields is the evaluation of the shape of their key.** -/
theorem clauseOf_eq_map_shapeOf (x : List Bool) (n T j tag p : ℕ) :
    clauseOf tm x n T j tag p =
      (shapeOf tm (Key.ofFields (slotBits k State) (colBits T) x.length n T j tag p)).map
        (Shape.eval (slotBits k State) (colBits T) p (colOf (slotBits k State) (colBits T) p)
          (timeOf (slotBits k State) (colBits T) p) T x) := by
  set κ := Key.ofFields (slotBits k State) (colBits T) x.length n T j tag p with hκ
  have hκj : κ.j = j := rfl
  have hκtag : κ.tag = tag := rfl
  have hκslot : κ.slot = p % 2 ^ slotBits k State := rfl
  rw [clauseOf, shapeOf, hκj, hκtag]
  by_cases hj : j < 3
  · simp only [hj, ↓reduceDIte]
    by_cases h0 : tag = 0
    · simp only [h0, ↓reduceIte]
      by_cases hp : p < 2
      · have h₁ : (!κ.pGt1) = true := by simp [hκ, Key.ofFields]; omega
        have h₂ : (!κ.p0) = decide (p = 1) := by
          rw [Bool.eq_iff_iff]; simp [hκ, Key.ofFields]; omega
        simp only [hp, h₁, ↓reduceIte, h₂, map_eval_lift, relabel_tseitinClause]
        rfl
      · have h₁ : ¬ (!κ.pGt1) = true := by simp [hκ, Key.ofFields]; omega
        simp only [hp, h₁, ↓reduceIte]
        rfl
    · by_cases h1 : tag = 1
      · simp only [h1, ↓reduceIte, one_ne_zero]
        by_cases hp : j = 0 ∧ p < x.length
        · have h₁ : (j = 0 ∧ κ.pLtX = true) := ⟨hp.1, by simp [hκ, Key.ofFields, hp.2]⟩
          rw [dite_eq_left hp, ite_eq_left h₁]
          simp [unitClause, Shape.eval, LabelSrc.eval, SignSrc.eval, List.getElem?_eq_getElem hp.2]
        · have h₁ : ¬ (j = 0 ∧ κ.pLtX = true) := by simp [hκ, Key.ofFields]; omega
          rw [dite_eq_right hp, ite_eq_right h₁]
          rfl
      · by_cases h2 : tag = 2
        · simp only [h2, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, hκslot]
          rcases hl : Loc.ofSlot (k := k) (State := State) (p % 2 ^ slotBits k State) with _ | l
          · rfl
          · have hc : κ.colOK l = decide (l.ColOK T (colOf (slotBits k State) (colBits T) p)) :=
              Key.colOK_ofFields _ _ _ l
            have hiff : (!κ.tGtT && κ.colOK l) = true ↔
                (p / 2 ^ slotBits k State / 2 ^ colBits T ≤ T ∧
                  l.ColOK T (p / 2 ^ slotBits k State % 2 ^ colBits T)) := by
              rw [hc]; simp [hκ, Key.ofFields]
            simp only
            by_cases hok : p / 2 ^ slotBits k State / 2 ^ colBits T ≤ T ∧
                l.ColOK T (p / 2 ^ slotBits k State % 2 ^ colBits T)
            · simp only [hok, hiff.2 hok, and_self, ↓reduceIte, map_eval_lift]
              unfold posClause posShape
              by_cases ht : p / 2 ^ slotBits k State / 2 ^ colBits T = 0
              · have hκt : κ.t0 = true := by simp [hκ, Key.ofFields, ht]
                simp only [ht, hκt, ↓reduceIte, relabel_tseitinClause]
                rw [hκ, Key.initBit_ofFields]
                rfl
              · have hκt : κ.t0 = false := by simp [hκ, Key.ofFields, ht]
                simp only [ht, hκt, ↓reduceIte, Bool.false_eq_true, relabel_tseitinClause]
                rw [hκ, refSrc_eval, refSrc_eval]
                rfl
            · have hnot : ¬ (!κ.tGtT && κ.colOK l) = true := fun h => hok (hiff.1 h)
              simp only [hok, hnot, ↓reduceIte]
              rfl
        · simp only [h0, h1, h2, ↓reduceIte]
          by_cases hp : j = 0 ∧ p = 0
          · have h₁ : (j = 0 ∧ κ.p0 = true) := ⟨hp.1, by simp [hκ, Key.ofFields, hp.2]⟩
            rw [ite_eq_left hp, ite_eq_left h₁]
            simp [unitClause, Shape.eval, LabelSrc.eval, SignSrc.eval, outLabel, outSrc, posLabel,
              ColSrc.eval, TimeSrc.eval]
          · have h₁ : ¬ (j = 0 ∧ κ.p0 = true) := by simp [hκ, Key.ofFields]; omega
            rw [ite_eq_right hp, ite_eq_right h₁]
            rfl
  · simp only [hj, ↓reduceDIte]
    rfl

end Eval

/-! ### Bits -/

section Bits

/-- The tag of a symbolic label. -/
def LabelSrc.tag : LabelSrc → ℕ
  | .const _ => 0
  | .input _ => 1
  | .pos .. => 2

/-- The constant part of the payload of a symbolic label, in its slot field. -/
def LabelSrc.slotVal : LabelSrc → ℕ
  | .const b => b.toNat
  | .input _ => 0
  | .pos sl _ _ => sl

/-- The selector `q` of a symbolic label: the payload is `p` (`0`) or `c - 1` (`1`), the column is
`c`, `c - 1`, `c + 1` or `2 T` (`2` to `5`), the block is `t`, `t - 1` or `T` (`6` to `8`).
Decrements of `c = 0` and `t = 0` select nothing, giving `0 = 0 - 1`. -/
def LabelSrc.sel (c0 t0 : Bool) : LabelSrc → ℕ → Bool
  | .const _, _ => false
  | .input b, q => (decide (q = 0) && !b) || (decide (q = 1) && b && !c0)
  | .pos _ cs ts, q =>
    (decide (q = 2) && decide (cs = .same)) || (decide (q = 3) && decide (cs = .prev) && !c0) ||
    (decide (q = 4) && decide (cs = .next)) || (decide (q = 5) && decide (cs = .last)) ||
    (decide (q = 6) && decide (ts = .same)) || (decide (q = 7) && decide (ts = .prev) && !t0) ||
    (decide (q = 8) && decide (ts = .top))

/-- The selector `q` of a symbolic sign: the constant `true` (`9`) or the lookup (`10`). -/
def SignSrc.sel : SignSrc → ℕ → Bool
  | .const b, q => decide (q = 9) && b
  | .lookup, q => decide (q = 10)

/-- **The tag and slot bits of a shape**: two tag bits, then the slot bits. -/
def tagSlot (sh : Shape) (f : ℕ) : Bool :=
  if f < 2 then sh.1.tag.testBit f else sh.1.slotVal.testBit (f - 2)

/-- **The selectors of a shape**, `0` to `10`. -/
def selOf (c0 t0 : Bool) (sh : Shape) (q : ℕ) : Bool := sh.1.sel c0 t0 q || sh.2.sel q

/-- The column field selected by `sel`, at bit `q`. -/
def colTerm (sel : ℕ → Bool) (c T q : ℕ) : Bool :=
  (sel 2 && c.testBit q) || (sel 3 && (c.testBit q ^^ decide (c % 2 ^ q = 0))) ||
    (sel 4 && (c.testBit q ^^ decide (c % 2 ^ q = 2 ^ q - 1))) || (sel 5 && (2 * T).testBit q)

/-- The block field selected by `sel`, at bit `q`. -/
def timeTerm (sel : ℕ → Bool) (t T q : ℕ) : Bool :=
  (sel 6 && t.testBit q) || (sel 7 && (t.testBit q ^^ decide (t % 2 ^ q = 0))) ||
    (sel 8 && T.testBit q)

/-- The payload bit `q` selected by the tag and slot bits `ts` and the selectors `sel`. -/
def payTerm (ts sel : ℕ → Bool) (s cb p c t T q : ℕ) : Bool :=
  (decide (q < s) && ts (2 + q)) || (sel 0 && p.testBit q) ||
    (sel 1 && (c.testBit q ^^ decide (c % 2 ^ q = 0))) ||
    (decide (s ≤ q ∧ q < s + cb) && colTerm sel c T (q - s)) ||
    (decide (s + cb ≤ q) && timeTerm sel t T (q - s - cb))

/-- **The output bit `i` of a literal** with tag and slot bits `ts` and selectors `sel`: the tag
bits, then the payload bits, then the sign. This is what the output stage of the decoder
computes. -/
def outBit (s cb tb : ℕ) (ts sel : ℕ → Bool) (p c t T : ℕ) (lk : Bool) (i : ℕ) : Bool :=
  if i < 2 then ts i
  else if i < 2 + (s + cb + tb) then payTerm ts sel s cb p c t T (i - 2)
  else sel 9 || (sel 10 && lk)

/-- Bit `q` of `c - 1`, for `1 ≤ c`: bit `q` of `c`, flipped when the lower bits of `c` are
zero. -/
theorem testBit_sub_one {c : ℕ} (hc : 1 ≤ c) (q : ℕ) :
    (c - 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 0)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]; simp; omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have hd : 1 ≤ d := by omega
      have h₁ : (d + d - 1) / 2 = d - 1 := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, ih hd, h₃]
      congr 2
      rw [Nat.zero_add, Nat.mul_eq_zero]
      simp
    · have h₁ : (2 * d + 1 - 1) / 2 = d := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃]
      simp

/-- Bit `q` of `c + 1`: bit `q` of `c`, flipped when the lower bits of `c` are all one. -/
theorem testBit_add_one (c q : ℕ) :
    (c + 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 2 ^ q - 1)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, Nat.sub_self, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]; simp; omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    have hq := Nat.one_le_two_pow (n := q)
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have h₁ : (d + d + 1) / 2 = d := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, h₃]
      have : ¬ (2 * (d % 2 ^ q) = 2 * 2 ^ q - 1) := by omega
      simp [this]
    · have h₁ : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃, ih d]
      congr 2
      exact propext ⟨fun h => by omega, fun h => by omega⟩

/-- The bits of a tag and a payload. -/
theorem testBit_tag_add {tag : ℕ} (htag : tag < 4) (pay i : ℕ) :
    (tag + 4 * pay).testBit i = if i < 2 then tag.testBit i else pay.testBit (i - 2) := by
  rw [Nat.add_comm, show 4 = 2 ^ 2 from rfl, Nat.testBit_two_pow_mul_add _ htag]

/-- The bits of three fields of widths `s` and `cb` and a high field. -/
theorem testBit_fields {s cb sl C Tm : ℕ} (hsl : sl < 2 ^ s) (hC : C < 2 ^ cb) (q : ℕ) :
    (sl + 2 ^ s * (C + 2 ^ cb * Tm)).testBit q =
      if q < s then sl.testBit q else if q < s + cb then C.testBit (q - s)
      else Tm.testBit (q - s - cb) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hsl, Nat.add_comm C,
    Nat.testBit_two_pow_mul_add _ hC]
  split_ifs <;> first | rfl | omega

/-- A symbolic label whose slot and column fit their fields. -/
def LabelSrc.InRange (s cb c T : ℕ) : LabelSrc → Prop
  | .pos sl cs _ => sl < 2 ^ s ∧ cs.eval c T < 2 ^ cb
  | _ => True

/-- The payload of a symbolic label. -/
def LabelSrc.payload (s cb p c t T : ℕ) : LabelSrc → ℕ
  | .const b => b.toNat
  | .input false => p
  | .input true => c - 1
  | .pos sl cs ts => sl + 2 ^ s * (cs.eval c T + 2 ^ cb * ts.eval t T)

theorem LabelSrc.eval_eq (s cb p c t T : ℕ) (l : LabelSrc) :
    l.eval s cb p c t T = l.tag + 4 * l.payload s cb p c t T := by
  rcases l with b | (_ | _) | ⟨sl, cs, ts⟩ <;> simp [LabelSrc.eval, LabelSrc.tag,
    LabelSrc.payload, constLabel, inputLabel]

theorem LabelSrc.tag_lt (l : LabelSrc) : l.tag < 4 := by
  rcases l with b | b | ⟨sl, cs, ts⟩ <;> simp [LabelSrc.tag]

private theorem colTerm_eq {c T q sl : ℕ} (cs : ColSrc) (ts : TimeSrc) (t0 : Bool)
    (sg : SignSrc) :
    colTerm (selOf (decide (c = 0)) t0 (.pos sl cs ts, sg)) c T q = (cs.eval c T).testBit q := by
  cases sg <;> cases cs <;> simp only [colTerm, selOf, LabelSrc.sel, SignSrc.sel, ColSrc.eval] <;>
    simp only [decide_true, reduceCtorEq, decide_false, Bool.and_false, Nat.reduceEqDiff,
      Bool.and_self, Bool.false_and, Bool.or_self, Nat.succ_ne_self, Nat.zero_testBit,
      Bool.or_false, Bool.true_and, Bool.and_true, Bool.false_or, Bool.or_true]
  all_goals first
    | rw [testBit_add_one]
    | (by_cases hc : c = 0
       · simp [hc]
       · rw [testBit_sub_one (by omega)]; simp [hc])

private theorem timeTerm_eq {t T q sl : ℕ} (cs : ColSrc) (ts : TimeSrc) (c0 : Bool)
    (sg : SignSrc) :
    timeTerm (selOf c0 (decide (t = 0)) (.pos sl cs ts, sg)) t T q = (ts.eval t T).testBit q := by
  cases sg <;> cases ts <;> simp only [timeTerm, selOf, LabelSrc.sel, SignSrc.sel, TimeSrc.eval] <;>
    simp only [Nat.reduceEqDiff, decide_false, Bool.false_and, Bool.or_self, Nat.succ_ne_self,
      decide_true, Bool.and_self, Bool.or_true, reduceCtorEq, Bool.or_false, Bool.true_and,
      Bool.and_true, Bool.and_false, Bool.false_or]
  all_goals
    by_cases ht : t = 0
    · simp [ht]
    · rw [testBit_sub_one (by omega)]; simp [ht]

/-- **The output bits of a shape are the bits of its literal**: its label below `2 + P` and its
sign at `2 + P`, for `P = s + cb + tb`, at least one slot bit, a looked-up bit that is the bit of
`x` at `p` whenever it is used, and a label whose slot and column fit their fields. -/
theorem outBit_shape {s cb tb p c t T : ℕ} {x : List Bool} {lk : Bool} (hs : 1 ≤ s)
    {sh : Shape} (hR : sh.1.InRange s cb c T) (hlk : sh.2 = .lookup → lk = x.getD p false)
    {i : ℕ} (hi : i ≤ 2 + (s + cb + tb)) :
    outBit s cb tb (tagSlot sh) (selOf (decide (c = 0)) (decide (t = 0)) sh) p c t T lk i =
      if i < 2 + (s + cb + tb) then (sh.1.eval s cb p c t T).testBit i else sh.2.eval x p := by
  obtain ⟨l, sg⟩ := sh
  rw [LabelSrc.eval_eq, testBit_tag_add l.tag_lt]
  unfold outBit
  by_cases h2 : i < 2
  · simp [h2, tagSlot, show i < 2 + (s + cb + tb) by omega]
  · by_cases hP : i < 2 + (s + cb + tb)
    · simp only [h2, hP, ↓reduceIte]
      have hq : i - 2 < s + cb + tb := by omega
      have hts : 2 + (i - 2) = i := by omega
      generalize i - 2 = q at hq hts ⊢
      subst hts
      have h21 : ¬ 2 + q ≤ 1 := by omega
      rcases l with b | (_ | _) | ⟨sl, cs, ts⟩
      · cases sg <;> simp only [payTerm, tagSlot, Order.lt_two_iff, h21, ↓reduceIte,
          LabelSrc.slotVal, add_tsub_cancel_left, selOf, LabelSrc.sel, SignSrc.sel,
          OfNat.zero_ne_ofNat, decide_false, Bool.false_and, Bool.or_self, Bool.or_false,
          OfNat.one_ne_ofNat, Bool.decide_and, colTerm, Nat.reduceEqDiff, Bool.and_false, timeTerm,
          LabelSrc.payload, Bool.and_eq_right_iff_imp, decide_eq_true_eq]
        all_goals
          intro hqs
          cases b <;> simp [Nat.testBit_one_eq_true_iff_self_eq_zero] at hqs
          omega
      · cases sg <;> simp [payTerm, tagSlot, selOf, LabelSrc.sel, SignSrc.sel, LabelSrc.payload,
          LabelSrc.slotVal, colTerm, timeTerm, h21]
      · cases sg <;> simp only [payTerm, tagSlot, Order.lt_two_iff, h21, ↓reduceIte,
          LabelSrc.slotVal, add_tsub_cancel_left, Nat.zero_testBit, Bool.and_false, selOf,
          LabelSrc.sel, decide_true, Bool.not_true, zero_ne_one, decide_false, Bool.and_true,
          Bool.false_and, Bool.or_self, SignSrc.sel, OfNat.zero_ne_ofNat, one_ne_zero,
          Bool.and_self, Bool.true_and, Bool.false_or, OfNat.one_ne_ofNat, Bool.or_false,
          Bool.decide_and, colTerm, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
          timeTerm, LabelSrc.payload]
        all_goals
          by_cases hc : c = 0
          · simp [hc]
          · rw [testBit_sub_one (by omega)]; simp [hc]
      · obtain ⟨hsl, hC⟩ := hR
        rw [LabelSrc.payload, testBit_fields hsl hC]
        have hcol := colTerm_eq (c := c) (T := T) (q := q - s) (sl := sl) cs ts (decide (t = 0)) sg
        have htime := timeTerm_eq (t := t) (T := T) (q := q - s - cb) (sl := sl) cs ts
          (decide (c = 0)) sg
        simp only [payTerm, hcol, htime]
        have h0 : selOf (decide (c = 0)) (decide (t = 0)) (.pos sl cs ts, sg) 0 = false := by
          cases sg <;> simp [selOf, LabelSrc.sel, SignSrc.sel]
        have h1 : selOf (decide (c = 0)) (decide (t = 0)) (.pos sl cs ts, sg) 1 = false := by
          cases sg <;> simp [selOf, LabelSrc.sel, SignSrc.sel]
        simp only [h0, h1, Bool.false_and, Bool.or_false, tagSlot,
          show ¬ 2 + q < 2 by omega, ↓reduceIte, LabelSrc.slotVal, Nat.add_sub_cancel_left]
        by_cases hqs : q < s
        · simp [hqs, show ¬ s ≤ q by omega, show ¬ s + cb ≤ q by omega]
        · by_cases hqc : q < s + cb
          · simp [hqs, hqc, show s ≤ q by omega, show ¬ s + cb ≤ q by omega]
          · simp [hqs, hqc, show s + cb ≤ q by omega]
    · simp only [h2, hP, ↓reduceIte]
      cases sg <;> rcases l with b | b | ⟨sl, cs, ts⟩ <;>
        simp only [selOf, LabelSrc.sel, SignSrc.sel, decide_true, Bool.true_and, Bool.false_or,
            Nat.succ_ne_self, decide_false, Bool.false_and, Bool.or_self, Bool.or_false,
            SignSrc.eval, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.reduceEqDiff, Bool.or_true,
            List.getD_eq_getElem?_getD]
      all_goals exact hlk rfl

end Bits

/-! ### The shapes stay within their fields -/

section Range

theorem fst_mem_tseitinClause {V : Type} {op : Op} {w a b : V} {j : Fin 3} {l : Literal V}
    (h : l ∈ tseitinClause op w a b j) : l.1 = w ∨ l.1 = a ∨ l.1 = b := by
  obtain ⟨v, s⟩ := l
  fin_cases j <;> cases op <;> simp [tseitinClause] at h <;> aesop

variable {X n T : ℕ}

omit [DecidableEq State] in
theorem refSrc_inRange {j tag p : ℕ} {r : Ref k State}
    (hr : r.InWindow n T (colOf (slotBits k State) (colBits T) p)) :
    ((Key.ofFields (slotBits k State) (colBits T) X n T j tag p).refSrc r).InRange
      (slotBits k State) (colBits T) (colOf (slotBits k State) (colBits T) p) T := by
  rcases r with _ | _ | _ | ⟨q, l, cs, g⟩
  · trivial
  · trivial
  · simp only [Key.refSrc]; split <;> trivial
  · simp only [Key.refSrc, Key.guard_ofFields]
    split
    · rename_i hg
      refine ⟨slot_lt_two_pow l, ?_⟩
      rw [colSrcOf_eval]
      exact lt_of_le_of_lt (Loc.labelCol_le l _) (lt_of_lt_of_le (hr hg) (numCols_le_two_pow T))
    · trivial

/-- A property of every literal of every branch of `shapeOf` holds of its literals. -/
theorem forall_mem_shapeOf {P : Shape → Prop} (κ : Key) (htaut : ∀ sh ∈ tautShape, P sh)
    (h0 : ∀ (hj : κ.j < 3), ∀ sh ∈ lift (tseitinClause (.const !κ.p0) (.const !κ.p0)
      (.const false) (.const false) ⟨κ.j, hj⟩), P sh)
    (h1 : κ.pLtX = true → P (.input false, .lookup))
    (h2 : ∀ (hj : κ.j < 3) (l : Loc k State), Loc.ofSlot κ.slot = some l →
      (!κ.tGtT && κ.colOK l) = true → ∀ sh ∈ lift (posShape tm κ l ⟨κ.j, hj⟩), P sh)
    (h3 : P (outSrc (k := k) (State := State), .const true)) :
    ∀ sh ∈ shapeOf tm κ, P sh := by
  intro sh hsh
  unfold shapeOf at hsh
  by_cases hj : κ.j < 3
  · rw [dite_eq_left hj] at hsh
    by_cases ht0 : κ.tag = 0
    · rw [ite_eq_left ht0] at hsh
      split at hsh
      · exact h0 hj sh hsh
      · exact htaut sh hsh
    · rw [ite_eq_right ht0] at hsh
      by_cases ht1 : κ.tag = 1
      · rw [ite_eq_left ht1] at hsh
        split at hsh
        · rename_i hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
          rcases hsh with rfl | rfl | rfl <;> exact h1 hc.2
        · exact htaut sh hsh
      · rw [ite_eq_right ht1] at hsh
        by_cases ht2 : κ.tag = 2
        · rw [ite_eq_left ht2] at hsh
          split at hsh
          · rename_i l hl
            split at hsh
            · rename_i hok
              exact h2 hj l hl hok sh hsh
            · exact htaut sh hsh
          · exact htaut sh hsh
        · rw [ite_eq_right ht2] at hsh
          split at hsh
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsh
            rcases hsh with rfl | rfl | rfl <;> exact h3
          · exact htaut sh hsh
  · rw [dite_eq_right hj] at hsh
    exact htaut sh hsh

/-- **The labels of the shapes fit their fields.** -/
theorem inRange_of_mem_shapeOf {j tag p : ℕ} {sh : Shape}
    (hsh : sh ∈ shapeOf tm (Key.ofFields (slotBits k State) (colBits T) X n T j tag p)) :
    sh.1.InRange (slotBits k State) (colBits T) (colOf (slotBits k State) (colBits T) p) T := by
  have hc : colOf (slotBits k State) (colBits T) p < 2 ^ colBits T :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  refine forall_mem_shapeOf (P := fun sh => sh.1.InRange (slotBits k State) (colBits T)
    (colOf (slotBits k State) (colBits T) p) T) tm _ ?_ ?_ ?_ ?_ ?_ sh hsh
  · intro sh hsh
    simp only [tautShape, List.mem_cons, List.not_mem_nil, or_false] at hsh
    rcases hsh with rfl | rfl | rfl <;> trivial
  · intro hj sh hsh
    simp only [lift, List.mem_map] at hsh
    obtain ⟨l, hl, rfl⟩ := hsh
    rcases fst_mem_tseitinClause hl with h | h | h <;> simp only [h] <;> trivial
  · intro _; trivial
  · intro hj l _ hok sh hsh
    simp only [lift, List.mem_map] at hsh
    obtain ⟨lit, hlit, rfl⟩ := hsh
    have hok' : l.ColOK T (colOf (slotBits k State) (colBits T) p) := by
      have := Key.colOK_ofFields (s := slotBits k State) (cb := colBits T) (X := X) (n := n)
        (T := T) j tag p l
      simp only [Bool.and_eq_true] at hok
      simpa [this] using hok.2
    obtain ⟨hra, hrb⟩ := table_inWindow (n := n) hok'.lt tm l
    unfold posShape at hlit
    split_ifs at hlit <;> rcases fst_mem_tseitinClause hlit with h | h | h <;> simp only [h]
    all_goals first
      | trivial
      | exact ⟨slot_lt_two_pow _, hc⟩
      | exact refSrc_inRange hra
      | exact refSrc_inRange hrb
  · exact ⟨slot_lt_two_pow _, Nat.two_pow_pos _⟩

/-- **A shape looks up `x` only at a payload within it.** -/
theorem lt_of_mem_shapeOf {j tag p : ℕ} {sh : Shape}
    (hsh : sh ∈ shapeOf tm (Key.ofFields (slotBits k State) (colBits T) X n T j tag p))
    (hlk : sh.2 = .lookup) : p < X := by
  revert hlk
  refine forall_mem_shapeOf (P := fun sh => sh.2 = .lookup → p < X) tm _ ?_ ?_ ?_ ?_ ?_ sh hsh
  · intro sh hsh
    simp only [tautShape, List.mem_cons, List.not_mem_nil, or_false] at hsh
    rcases hsh with rfl | rfl | rfl <;> simp
  · intro hj sh hsh
    simp only [lift, List.mem_map] at hsh
    obtain ⟨l, -, rfl⟩ := hsh
    simp
  · intro h _
    simpa [Key.ofFields] using h
  · intro hj l _ _ sh hsh
    simp only [lift, List.mem_map] at hsh
    obtain ⟨l, -, rfl⟩ := hsh
    simp
  · simp

/-- A shape has three literals. -/
theorem length_shapeOf (κ : Key) : (shapeOf tm κ).length = 3 := by
  unfold shapeOf
  split
  · split
    · split
      · simp [lift]
      · rfl
    · split
      · split <;> rfl
      · split
        · split
          · split
            · simp only [lift, List.length_map, posShape]
              split <;> simp
            · rfl
          · rfl
        · split <;> rfl
  · rfl

end Range

end Cslib.Circuits.Boolean.Tableau.Decoder
