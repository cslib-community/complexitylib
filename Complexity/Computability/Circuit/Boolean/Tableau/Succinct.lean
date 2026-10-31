/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Correct
public import Complexity.Computability.Circuit.Boolean.Tseitin
public import Mathlib.Data.Nat.Bits
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.Nat.Div
import Complexity.Foundations.Data.Nat.Fields
import Mathlib.Data.Nat.Size

/-!
# The tableau formula on bit-field labels

The Tseitin formula (`Complexity/Computability/Circuit/Boolean/Tseitin.lean`) of the uniform
tableau circuit of a multi-tape machine
(`Complexity/Computability/Circuit/Boolean/Tableau/Basic.lean`), written with variables that are
*labels* made of fixed-width binary fields rather than wire numbers. Each clause is computed from
its number by bit-field arithmetic (`Cslib.Circuits.Boolean.Tableau.clauseAt`), with no
multiplication by the block size, so that a circuit of size linear in the field widths can decode
it. This is the succinct tableau formula of the sketch of
[Williams, Theorem 6.1, p. 20][Williams2010]: the clauses of a cell are the same for every cell,
except that the block and the column enter the labels of their variables. The sketch first
converts the machine to a single-tape one; this formula uses the multi-tape tableau directly.

A label is a two-bit *tag* followed by a payload (`label = tag + 4 * payload`):

* tag `0`, the constant gate `b` (`constLabel`), payload `b`;
* tag `1`, the input `i` (`inputLabel`), payload `i`;
* tag `2`, the position `l` of block `t` in column `c` (`posLabel`), payload
  `slot + 2 ^ sb * (c + 2 ^ cb * t)`, where `slot` is the number of `l` among the positions of a
  block (`Loc.slot`), `sb = slotBits k State` depends only on the machine,
  `cb = colBits T = Nat.size (2 * T)` and `t` takes the remaining high bits.

A reference of the tableau (`Ref`), relative to the block and the column of its gate, becomes the
label `Ref.label`: the block `t` or `t - 1`, the column `c`, `c - 1`, `c + 1` or `2 T` (`0` for the
global positions, which are not repeated across the columns), and the slot of the position. A
clause number is `j + 4 * (tag + 4 * payload)`: clause `j < 3` of the gate of a constant or a
position, the unit clause fixing an input, or (tag `3`, payload `0`) the unit clause fixing the
output; every other number gives a tautology. The formula `succinctCNF tm x n T` lists the clauses
of all numbers below `2 ^ clauseBits k State T`.

The formula is satisfiable exactly when some input of length `n` extending `x` makes the machine
write exactly `[true]` within `T` steps (`satisfiable_succinctCNF_iff`). The proof compares it
with `tseitinSatCNF` of the tableau gate list, through the labelling of wires (`wireLabel`) and
the inverse decoding of labels (`wireOf`); the labels of references agree with their resolved wire
numbers (`wireLabel_resolve`, `wireOf_label`).

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Loc.slot`, `Cslib.Circuits.Boolean.Tableau.slotBits`,
  `Cslib.Circuits.Boolean.Tableau.colBits`, `Cslib.Circuits.Boolean.Tableau.timeBits`: the fields.
* `Cslib.Circuits.Boolean.Tableau.constLabel`, `Cslib.Circuits.Boolean.Tableau.inputLabel`,
  `Cslib.Circuits.Boolean.Tableau.posLabel`, `Cslib.Circuits.Boolean.Tableau.Ref.label`: labels.
* `Cslib.Circuits.Boolean.Tableau.posClause`, `Cslib.Circuits.Boolean.Tableau.clauseOf`,
  `Cslib.Circuits.Boolean.Tableau.clauseAt`: the clause with a number, from its fields.
* `Cslib.Circuits.Boolean.Tableau.clauseBits`, `Cslib.Circuits.Boolean.Tableau.labelBits`: the
  widths of clause numbers and labels.
* `Cslib.Circuits.Boolean.Tableau.succinctCNF`: the formula.

## Main results

* `Cslib.Circuits.Boolean.Tableau.wireLabel_resolve`, `Cslib.Circuits.Boolean.Tableau.wireOf_label`:
  the label of a reference is the label of the wire it resolves to, and decodes to that wire.
* `Cslib.Circuits.Boolean.Tableau.satisfiable_succinctCNF_iff_tseitin`: the formula is
  equisatisfiable with the Tseitin formula of the tableau.
* `Cslib.Circuits.Boolean.Tableau.satisfiable_succinctCNF_iff`: the formula is satisfiable exactly
  when some completion of `x` is accepted within `T` steps.
* `Cslib.Circuits.Boolean.Tableau.length_succinctCNF`,
  `Cslib.Circuits.Boolean.Tableau.length_of_mem_succinctCNF`,
  `Cslib.Circuits.Boolean.Tableau.lt_two_pow_labelBits_of_mem_vars`: there are
  `2 ^ clauseBits k State T` clauses of three literals, on variables below
  `2 ^ labelBits k State T`.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau

open Turing MultiTapeTM Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]

/-! ### Fields -/

/-- The slot of a position: its number among the positions of a block. -/
noncomputable def Loc.slot (l : Loc k State) : ℕ := Fintype.equivFin (Loc k State) l

/-- The position with a slot number, if any. -/
noncomputable def Loc.ofSlot (s : ℕ) : Option (Loc k State) :=
  if h : s < Fintype.card (Loc k State) then some ((Fintype.equivFin (Loc k State)).symm ⟨s, h⟩)
  else none

omit [DecidableEq State] in
/-- Slots are below the number of positions. -/
theorem Loc.slot_lt (l : Loc k State) : l.slot < Fintype.card (Loc k State) :=
  (Fintype.equivFin (Loc k State) l).isLt

omit [DecidableEq State] in
/-- Decoding a slot gives its position. -/
@[simp] theorem Loc.ofSlot_slot (l : Loc k State) : Loc.ofSlot l.slot = some l := by
  simp [Loc.ofSlot, Loc.slot]

variable (k State) in
/-- The width of the slot field. -/
noncomputable def slotBits : ℕ := Nat.size (Fintype.card (Loc k State))

/-- The width of the column field, for the columns `c ≤ 2 T`. -/
def colBits (T : ℕ) : ℕ := Nat.size (2 * T)

/-- The width of the time field, for the blocks `t ≤ T`. -/
def timeBits (T : ℕ) : ℕ := Nat.size T

omit [DecidableEq State] in
/-- The slots fit in their field. -/
theorem slot_lt_two_pow (l : Loc k State) : l.slot < 2 ^ slotBits k State :=
  l.slot_lt.trans (Nat.lt_size_self _)

/-- The columns fit in their field. -/
theorem numCols_le_two_pow (T : ℕ) : numCols T ≤ 2 ^ colBits T :=
  Nat.lt_size_self (2 * T)

/-- The blocks fit in their field. -/
theorem lt_two_pow_timeBits {t T : ℕ} (ht : t ≤ T) : t < 2 ^ timeBits T :=
  lt_of_le_of_lt ht (Nat.lt_size_self T)

/-- Three fields of widths `a` and `b` and a high field decode into their values. -/
private theorem fields {a b x y z : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    (x + 2 ^ a * (y + 2 ^ b * z)) % 2 ^ a = x ∧
      (x + 2 ^ a * (y + 2 ^ b * z)) / 2 ^ a % 2 ^ b = y ∧
      (x + 2 ^ a * (y + 2 ^ b * z)) / 2 ^ a / 2 ^ b = z := by
  rw [Nat.add_mul_div_left_of_lt _ hx]
  exact ⟨Nat.add_mul_mod_of_lt _ hx, Nat.add_mul_mod_of_lt _ hy, Nat.add_mul_div_left_of_lt _ hy⟩

/-- Three fields of widths `a`, `b` and `d` fit in `a + b + d` bits. -/
private theorem fields_lt {a b d x y z : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) (hz : z < 2 ^ d) :
    x + 2 ^ a * (y + 2 ^ b * z) < 2 ^ (a + b + d) := by
  rw [Nat.add_assoc]
  exact Nat.add_two_pow_mul_lt hx (Nat.add_two_pow_mul_lt hy hz)

/-- A tag below `4` and a payload decode into their values. -/
private theorem tag_fields {tag p : ℕ} (htag : tag < 4) :
    (tag + 4 * p) % 4 = tag ∧ (tag + 4 * p) / 4 = p := by
  omega

/-! ### Labels -/

/-- The label of the constant gate `b`: tag `0`. -/
def constLabel (b : Bool) : ℕ := 4 * b.toNat

/-- The label of the input `i`: tag `1`. -/
def inputLabel (i : ℕ) : ℕ := 1 + 4 * i

variable (k State) in
/-- **The label of the position `l` of block `t` in column `c`**: tag `2`, and the slot, the column
and the block in fields of widths `slotBits k State`, `colBits T` and the remaining high bits. -/
noncomputable def posLabel (T t c : ℕ) (l : Loc k State) : ℕ :=
  2 + 4 * (l.slot + 2 ^ slotBits k State * (c + 2 ^ colBits T * t))

/-- The column under which a position is labelled: `0` for the global positions, which do not
depend on the column. -/
def Loc.labelCol : Loc k State → ℕ → ℕ
  | .glob _, _ => 0
  | .gf _ _ _, _ => 0
  | _, c => c

omit [DecidableEq State] in
/-- Labelling a column does not change the offset of a position. -/
theorem Loc.offset_labelCol (l : Loc k State) (T c : ℕ) :
    l.offset T (l.labelCol c) = l.offset T c := by
  cases l <;> rfl

omit [DecidableEq State] in
/-- The labelled column of a column of the window is admissible. -/
theorem Loc.colOK_labelCol {l : Loc k State} {T c : ℕ} (hc : c < numCols T) :
    l.ColOK T (l.labelCol c) := by
  cases l <;> simp [Loc.labelCol, Loc.ColOK, hc]

omit [DecidableEq State] in
/-- The labelled column is at most the column. -/
theorem Loc.labelCol_le (l : Loc k State) (c : ℕ) : l.labelCol c ≤ c := by
  cases l <;> simp [Loc.labelCol]

/-- **The label of a reference** from block `t` and column `c`: `Ref.resolve` with labels in place
of wire numbers. -/
noncomputable def Ref.label (n T t c : ℕ) : Ref k State → ℕ
  | .fls => constLabel false
  | .tru => constLabel true
  | .inp => if 1 ≤ c ∧ c ≤ n then inputLabel (c - 1) else constLabel false
  | .node p l cs g =>
    if g.test n T c then posLabel k State T (if p then t - 1 else t) (l.labelCol (cs.apply T c)) l
    else constLabel false

/-! ### From labels to wires -/

/-- The wire with a label: inverts the labelling on the labels of wires. -/
noncomputable def wireOf (n T lab : ℕ) : ℕ :=
  if lab % 4 = 0 then n + lab / 4
  else if lab % 4 = 1 then lab / 4
  else
    match Loc.ofSlot (k := k) (State := State) (lab / 4 % 2 ^ slotBits k State) with
    | some l => wire n T (lab / 4 / 2 ^ slotBits k State / 2 ^ colBits T) l
        (lab / 4 / 2 ^ slotBits k State % 2 ^ colBits T)
    | none => n

omit [DecidableEq State] in
/-- Decoding the label of a constant gives its wire. -/
@[simp] theorem wireOf_constLabel (n T : ℕ) (b : Bool) :
    wireOf (k := k) (State := State) n T (constLabel b) = n + b.toNat := by
  simp [wireOf, constLabel]

omit [DecidableEq State] in
/-- Decoding the label of an input gives its wire. -/
@[simp] theorem wireOf_inputLabel (n T i : ℕ) :
    wireOf (k := k) (State := State) n T (inputLabel i) = i := by
  have h₁ : inputLabel i % 4 = 1 := by unfold inputLabel; omega
  have h₂ : inputLabel i / 4 = i := by unfold inputLabel; omega
  simp [wireOf, h₁, h₂]

omit [DecidableEq State] in
/-- Decoding the label of a position gives its wire. -/
theorem wireOf_posLabel {n T t c : ℕ} (l : Loc k State) (hc : c < 2 ^ colBits T) :
    wireOf (k := k) (State := State) n T (posLabel k State T t c l) = wire n T t l c := by
  obtain ⟨h₁, h₂, h₃⟩ := fields (z := t) (slot_lt_two_pow l) hc
  obtain ⟨h₄, h₅⟩ := tag_fields (tag := 2)
    (p := l.slot + 2 ^ slotBits k State * (c + 2 ^ colBits T * t)) (by omega)
  simp only [wireOf, posLabel, h₄, h₅, h₁, h₂, h₃, Loc.ofSlot_slot]
  rfl

/-! ### From wires to labels -/

variable (k State) in
/-- **The label of a wire** of the tableau on `n` inputs: an input, a constant, or the position of
a gate decoded from its number. -/
noncomputable def wireLabel (n T w : ℕ) : ℕ :=
  if w < n then inputLabel w
  else if w < n + 2 then constLabel (decide (w = n + 1))
  else
    let (c, l) := posOf (k := k) (State := State) T ((w - n - 2) % blockSize k State T)
    posLabel k State T ((w - n - 2) / blockSize k State T) c l

omit [DecidableEq State] in
/-- The label of an input wire. -/
theorem wireLabel_of_lt {n T w : ℕ} (hw : w < n) : wireLabel k State n T w = inputLabel w := by
  simp [wireLabel, hw]

omit [DecidableEq State] in
/-- The labels of the constant wires. -/
theorem wireLabel_const (n T : ℕ) (b : Bool) :
    wireLabel k State n T (n + b.toNat) = constLabel b := by
  cases b <;> simp [wireLabel]

omit [DecidableEq State] in
/-- **The label of the wire of a position** is the label of the position. -/
theorem wireLabel_wire {n T t c : ℕ} {l : Loc k State} (hl : l.ColOK T c) :
    wireLabel k State n T (wire n T t l c) = posLabel k State T t c l := by
  obtain ⟨hdiv, hmod⟩ := div_mod_wire (n := n) (t := t) hl
  have h₁ : ¬ wire n T t l c < n := by simp only [wire]; omega
  have h₂ : ¬ wire n T t l c < n + 2 := by simp only [wire]; omega
  simp only [wireLabel, h₁, h₂, ↓reduceIte, hdiv, hmod, posOf_offset hl]

/-! ### Labels of references -/

/-- A reference reads a column of the window whenever its guard holds. -/
def Ref.InWindow (n T c : ℕ) : Ref k State → Prop
  | .node _ _ cs g => g.test n T c = true → cs.apply T c < numCols T
  | _ => True

omit [DecidableEq State] in
/-- **The label of a reference is the label of its wire.** -/
theorem wireLabel_resolve {n T t c : ℕ} {r : Ref k State} (hr : r.InWindow n T c) :
    wireLabel k State n T (r.resolve n T t c) = r.label n T t c := by
  rcases r with _ | _ | _ | ⟨p, l, cs, g⟩
  · simpa [Ref.resolve, Ref.label] using wireLabel_const (k := k) (State := State) n T false
  · simpa [Ref.resolve, Ref.label] using wireLabel_const (k := k) (State := State) n T true
  · simp only [Ref.resolve, Ref.label]
    split_ifs with h
    · exact wireLabel_of_lt (by omega)
    · simpa using wireLabel_const (k := k) (State := State) n T false
  · simp only [Ref.InWindow] at hr
    by_cases hg : g.test n T c = true
    · simp only [Ref.resolve, Ref.label, hg, ↓reduceIte]
      rw [← wire_labelCol, wireLabel_wire (Loc.colOK_labelCol (hr hg))]
    · simp only [Ref.resolve, Ref.label, hg, Bool.false_eq_true, ↓reduceIte]
      simpa using wireLabel_const (k := k) (State := State) n T false
where
  wire_labelCol {n T t c : ℕ} {l : Loc k State} : wire n T t l (l.labelCol c) = wire n T t l c := by
    simp only [wire, Loc.offset_labelCol]

omit [DecidableEq State] in
/-- **Decoding the label of a reference gives its wire.** -/
theorem wireOf_label {n T t c : ℕ} {r : Ref k State} (hr : r.InWindow n T c) :
    wireOf (k := k) (State := State) n T (r.label n T t c) = r.resolve n T t c := by
  rcases r with _ | _ | _ | ⟨p, l, cs, g⟩
  · simp [Ref.label, Ref.resolve]
  · simp [Ref.label, Ref.resolve]
  · simp only [Ref.resolve, Ref.label]
    split_ifs <;> simp
  · simp only [Ref.InWindow] at hr
    by_cases hg : g.test n T c = true
    · simp only [Ref.resolve, Ref.label, hg, ↓reduceIte]
      rw [wireOf_posLabel _ (lt_of_le_of_lt (Loc.labelCol_le l _)
        (lt_of_lt_of_le (hr hg) (numCols_le_two_pow T)))]
      exact wireLabel_resolve.wire_labelCol
    · simp [Ref.resolve, Ref.label, hg]

omit [DecidableEq State] in
private theorem inWindow_of_cs {n T c : ℕ} (hc : c < numCols T) {p : Bool} {l : Loc k State}
    {cs : ColSel} {g : Guard} (h : cs = .next → g = .ltLast) :
    (Ref.node p l cs g).InWindow n T c := by
  intro hg
  cases cs with
  | same => exact hc
  | prev => simp only [ColSel.apply]; omega
  | next =>
    obtain rfl := h rfl
    simpa [Guard.test, ColSel.apply] using hg
  | last => simp [ColSel.apply, numCols]

/-- **The references of the gates of the tableau read the window.** -/
theorem table_inWindow {n T c : ℕ} (hc : c < numCols T) (tm : MultiTapeTM k Bool State)
    (l : Loc k State) :
    let (_, left, right) := table tm l
    left.InWindow n T c ∧ right.InWindow n T c := by
  change (table tm l).2.1.InWindow n T c ∧ (table tm l).2.2.InWindow n T c
  have hw {r : Ref k State} (h : ∀ p l g, r = .node p l .next g → g = .ltLast) :
      r.InWindow n T c := by
    rcases r with _ | _ | _ | ⟨p, l, cs, g⟩
    · trivial
    · trivial
    · trivial
    · exact inWindow_of_cs hc fun hcs => h p l g (by rw [hcs])
  have hterm {L : List (Ref k State × Ref k State)}
      (hL : ∀ q ∈ L, ∀ p l g, (q.1 = .node p l .next g → g = .ltLast) ∧
        (q.2 = .node p l .next g → g = .ltLast)) (j : ℕ) :
      (L.getD j (.fls, .fls)).1.InWindow n T c ∧ (L.getD j (.fls, .fls)).2.InWindow n T c := by
    rcases List.getD_mem_or L j (.fls, .fls) with hj | hj
    · exact ⟨hw fun p l g => (hL _ hj p l g).1, hw fun p l g => (hL _ hj p l g).2⟩
    · rw [hj]; exact ⟨trivial, trivial⟩
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩
  · rcases l with i | _ | q | q
    · exact ⟨hw (by simp [table, colF]), trivial⟩
    · exact ⟨trivial, trivial⟩
    · rcases q with s | ⟨i, s⟩
      · rcases s with _ | _ | _ <;>
          exact ⟨hw (by simp [table, scanTerm, colF, scanAt]),
            hw (by simp [table, scanTerm, colF, scanAt])⟩
      · exact ⟨hw (by simp [table, scanTerm, colF]), hw (by simp [table, scanTerm, colF])⟩
    · exact ⟨hw (by simp [table, scanAt]), hw (by simp [table, scanAt])⟩
  · rcases l with ⟨j, i⟩ | ⟨v, j⟩
    · cases i using Fin.cases <;>
        exact ⟨hw (by simp [table, gfF]), hw (by simp [table, scanAt])⟩
    · cases j using Fin.cases with
      | zero => exact ⟨trivial, trivial⟩
      | succ j =>
        refine ⟨hw (by simp [table]), hw ?_⟩
        simp only [table, Fin.cases_succ]
        split_ifs <;> simp
  · rcases b with _ | _
    · refine hterm (fun q hq p l g => ?_) j
      rcases f with (_ | q') | ((_ | _) | _) | _ <;>
        simp only [gfTerms, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [halted, gfF, act]
    · cases j using Fin.cases <;> exact ⟨hw (by simp [table]), hw (by simp [table])⟩
  · rcases b with _ | _
    · refine hterm (fun q hq p l g => ?_) j
      rcases f with _ | i | ⟨i, s⟩ <;>
        simp only [colTerms, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +contextual [halted, gfF, act, colF, scanAt]
    · cases j using Fin.cases <;> exact ⟨hw (by simp [table]), hw (by simp [table])⟩

/-! ### The clauses -/

/-- A clause that every assignment satisfies. -/
def tautology : Clause ℕ := [(0, true), (0, false), (0, true)]

/-- Every assignment satisfies `tautology`. -/
@[simp] theorem eval_tautology (σ : ℕ → Bool) : tautology.eval σ = true := by
  cases h : σ 0 <;> simp [tautology, h]

omit [DecidableEq State] in
/-- Admissibility of a column is decidable. -/
instance Loc.decidableColOK (T c : ℕ) (l : Loc k State) : Decidable (l.ColOK T c) := by
  cases l <;> unfold Loc.ColOK <;> infer_instance

variable (tm : MultiTapeTM k Bool State)

/-- Clause `j` of the gate at the position `l` of block `t` in column `c`, on labels: the initial
constant in block `0`, and otherwise the gate of `table` on the labels of its references. -/
noncomputable def posClause (n T t c : ℕ) (l : Loc k State) (j : Fin 3) : Clause ℕ :=
  if t = 0 then tseitinClause (.const (initBit tm T c l)) (posLabel k State T t c l) 0 0 j
  else
    let (op, left, right) := table tm l
    tseitinClause op (posLabel k State T t c l) (left.label n T t c) (right.label n T t c) j

variable (k State) in
/-- The label of the output wire: the output view `[true]` at time `T`. -/
noncomputable def outLabel (T : ℕ) : ℕ := posLabel k State T T 0 (.gf (.out (.one true)) true 7)

/-- **The clause with the fields `j`, `tag` and `p`** of its number `j + 4 * (tag + 4 * p)`:
clause `j` of the constant gate `p` (tag `0`), the unit clause fixing input `p` to `x[p]`
(tag `1`, `j = 0`), clause `j` of the gate at the position whose slot, column and block are the
fields of `p` (tag `2`), or the unit clause fixing the output (tag `3`, `j = p = 0`). Every other
number gives a tautology. -/
noncomputable def clauseOf (x : List Bool) (n T j tag p : ℕ) : Clause ℕ :=
  if hj : j < 3 then
    if tag = 0 then
      if p < 2 then
        tseitinClause (.const (decide (p = 1))) (constLabel (decide (p = 1))) 0 0 ⟨j, hj⟩
      else tautology
    else if tag = 1 then
      if hp : j = 0 ∧ p < x.length then unitClause (inputLabel p, x[p]) else tautology
    else if tag = 2 then
      match Loc.ofSlot (k := k) (State := State) (p % 2 ^ slotBits k State) with
      | some l =>
        if p / 2 ^ slotBits k State / 2 ^ colBits T ≤ T ∧
            l.ColOK T (p / 2 ^ slotBits k State % 2 ^ colBits T) then
          posClause tm n T (p / 2 ^ slotBits k State / 2 ^ colBits T)
            (p / 2 ^ slotBits k State % 2 ^ colBits T) l ⟨j, hj⟩
        else tautology
      | none => tautology
    else if j = 0 ∧ p = 0 then unitClause (outLabel k State T, true) else tautology
  else tautology

/-- **The clause with number `idx`**, from the fields of `idx`. -/
noncomputable def clauseAt (x : List Bool) (n T idx : ℕ) : Clause ℕ :=
  clauseOf tm x n T (idx % 4) (idx / 4 % 4) (idx / 16)

variable (k State) in
/-- The width of a clause number: the clause and the tag, then the slot, the column and the
block. -/
noncomputable def clauseBits (T : ℕ) : ℕ := 4 + (slotBits k State + colBits T + timeBits T)

/-- **The tableau formula on bit-field labels**: the clauses of all numbers below
`2 ^ clauseBits k State T`, for the tableau of `tm` for `T` steps on `n` inputs, with the inputs
`i < x.length` fixed to `x[i]` and the output fixed to `true`. -/
noncomputable def succinctCNF (x : List Bool) (n T : ℕ) : CNF ℕ :=
  (List.range (2 ^ clauseBits k State T)).map (clauseAt tm x n T)

/-! ### Clauses at their numbers -/

/-- The clause of a number with the fields `j`, `tag` and `p`. -/
theorem clauseAt_fields (x : List Bool) (n T : ℕ) {j tag : ℕ} (p : ℕ) (hj : j < 4)
    (htag : tag < 4) : clauseAt tm x n T (j + 4 * (tag + 4 * p)) = clauseOf tm x n T j tag p := by
  have h₁ : (j + 4 * (tag + 4 * p)) % 4 = j := by omega
  have h₂ : (j + 4 * (tag + 4 * p)) / 4 % 4 = tag := by omega
  have h₃ : (j + 4 * (tag + 4 * p)) / 16 = p := by omega
  rw [clauseAt, h₁, h₂, h₃]

omit [DecidableEq State] in
/-- The numbers of the clauses with a payload of `slotBits + colBits + timeBits` bits are below
`2 ^ clauseBits`. -/
theorem fields_lt_clauseBits {T j tag p : ℕ} (hj : j < 4) (htag : tag < 4)
    (hp : p < 2 ^ (slotBits k State + colBits T + timeBits T)) :
    j + 4 * (tag + 4 * p) < 2 ^ clauseBits k State T := by
  rw [clauseBits, Nat.pow_add]
  have : 2 ^ 4 * (p + 1) ≤ 2 ^ 4 * 2 ^ (slotBits k State + colBits T + timeBits T) :=
    Nat.mul_le_mul_left _ hp
  omega

/-- The clauses of a position. -/
theorem clauseOf_pos (x : List Bool) {n T t c : ℕ} {l : Loc k State} (j : Fin 3) (ht : t ≤ T)
    (hl : l.ColOK T c) :
    clauseOf tm x n T j 2 (l.slot + 2 ^ slotBits k State * (c + 2 ^ colBits T * t)) =
      posClause tm n T t c l j := by
  obtain ⟨h₁, h₂, h₃⟩ := fields (z := t) (slot_lt_two_pow l)
    (lt_of_lt_of_le hl.lt (numCols_le_two_pow T))
  simp only [clauseOf, j.isLt, ↓reduceDIte, OfNat.ofNat_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_one, h₁, h₂, h₃, Loc.ofSlot_slot, ht, hl, and_self]

/-- The clauses of a position hold exactly when its label carries the value of its gate. -/
theorem forall_eval_posClause_iff (σ : ℕ → Bool) (n T t c : ℕ) (l : Loc k State) :
    (∀ j, (posClause tm n T t c l j).eval σ = true) ↔
      σ (posLabel k State T t c l) = if t = 0 then initBit tm T c l
        else
          let (op, left, right) := table tm l
          op.value (σ (left.label n T t c)) (σ (right.label n T t c)) := by
  unfold posClause
  split_ifs
  · exact forall_eval_tseitinClause_iff _ _ _ _ _
  · generalize table tm l = e
    obtain ⟨op, left, right⟩ := e
    exact forall_eval_tseitinClause_iff _ _ _ _ _

/-- **Every clause holds** under an assignment of labels that gives the constants their values,
the fixed inputs the bits of `x` and the output `true`, and every position the value of its gate on
the labels of its references. -/
theorem eval_clauseOf {x : List Bool} {n T : ℕ} {σ : ℕ → Bool}
    (hconst : ∀ b, σ (constLabel b) = b) (hin : ∀ i (hi : i < x.length), σ (inputLabel i) = x[i])
    (hout : σ (outLabel k State T) = true)
    (hpos : ∀ t ≤ T, ∀ c (l : Loc k State), l.ColOK T c →
      σ (posLabel k State T t c l) = if t = 0 then initBit tm T c l
        else
          let (op, left, right) := table tm l
          op.value (σ (left.label n T t c)) (σ (right.label n T t c)))
    (j tag p : ℕ) : (clauseOf tm x n T j tag p).eval σ = true := by
  unfold clauseOf
  split_ifs with hj h₀ hp h₁ hp' h₂ h₃
  · exact (forall_eval_tseitinClause_iff _ _ _ _ σ).2 (hconst _) _
  · exact eval_tautology σ
  · simpa using hin p hp'.2
  · exact eval_tautology σ
  · split
    · split_ifs with h
      · exact (forall_eval_posClause_iff tm σ _ _ _ _ _).2 (hpos _ h.1 _ _ h.2) _
      · exact eval_tautology σ
    · exact eval_tautology σ
  · simpa using hout
  · exact eval_tautology σ
  · exact eval_tautology σ

/-! ### Comparison with the Tseitin formula of the tableau -/

omit [DecidableEq State] in
private theorem wire_sub_lt_numGates {n T t c : ℕ} {l : Loc k State} (hl : l.ColOK T c)
    (ht : t ≤ T) : wire n T t l c - n < numGates k State T := by
  rw [wire_sub]
  have := Loc.offset_lt hl
  have : t * blockSize k State T + blockSize k State T ≤ (T + 1) * blockSize k State T := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [numGates]
  omega

/-- The value of the gate at a position, on the values of its arguments. -/
private theorem value_gateAt (f : ℕ → Bool) (n T t c : ℕ) (l : Loc k State) :
    (gateAt tm n T t c l).1.value (f ((gateAt tm n T t c l).2.getD 0 0))
        (f ((gateAt tm n T t c l).2.getD 1 0)) =
      if t = 0 then initBit tm T c l
      else (table tm l).1.value (f ((table tm l).2.1.resolve n T t c))
        (f ((table tm l).2.2.resolve n T t c)) := by
  unfold gateAt
  split_ifs with ht
  · rfl
  · generalize table tm l = e
    obtain ⟨op, a, b⟩ := e
    cases op <;> rfl

private theorem getElem_gates {n T g : ℕ} (hg : g < (gates tm n T).length) :
    (gates tm n T)[g] = gateCode tm n T g := by
  simp [gates]

private theorem length_gates (n T : ℕ) : (gates tm n T).length = numGates k State T := by
  simp [gates]

/-- **The tableau formula on labels is equisatisfiable with the Tseitin formula of the tableau**
with the same fixed inputs and output. -/
theorem satisfiable_succinctCNF_iff_tseitin {n T : ℕ} (hn : n < 2 * T) {x : List Bool}
    (hx : x.length ≤ n) :
    (succinctCNF tm x n T).Satisfiable ↔
      (tseitinSatCNF x n (gates tm n T) (outWire k State n T)).Satisfiable := by
  have hcb : 2 * T < 2 ^ colBits T := Nat.lt_size_self _
  have hpay {p : ℕ} (hp : p < 2 ^ colBits T) :
      p < 2 ^ (slotBits k State + colBits T + timeBits T) := by
    have : 2 ^ colBits T ≤ 2 ^ (slotBits k State + colBits T + timeBits T) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hout_ok : (Loc.gf (k := k) (State := State) (.out (.one true)) true 7).ColOK T 0 := rfl
  constructor
  · rintro ⟨σ, hσ⟩
    rw [succinctCNF, CNF.eval_map_eq_true_iff] at hσ
    have hfield {j tag p : ℕ} (hj : j < 4) (htag : tag < 4)
        (hp : p < 2 ^ (slotBits k State + colBits T + timeBits T)) :
        (clauseOf tm x n T j tag p).eval σ = true := by
      rw [← clauseAt_fields tm x n T p hj htag]
      exact hσ _ (List.mem_range.2 (fields_lt_clauseBits hj htag hp))
    refine ⟨fun w => σ (wireLabel k State n T w),
      (eval_tseitinSatCNF_eq_true_iff _ _ _ _ _).2 ⟨?_, fun i hi => ?_, ?_⟩⟩
    · have := hfield (j := 0) (tag := 3) (p := 0) (by omega) (by omega) (Nat.two_pow_pos _)
      simpa [clauseOf, outWire, wireLabel_wire hout_ok, outLabel] using this
    · have := hfield (j := 0) (tag := 1) (p := i) (by omega) (by omega) (hpay (by omega))
      simpa [clauseOf, hi, wireLabel_of_lt (show i < n by omega)] using this
    · rw [eval_tseitinCNF_eq_true_iff]
      intro g hg
      rw [getElem_gates]
      rw [length_gates] at hg
      by_cases hg₂ : g < 2
      · have hcode : gateCode tm n T g = (.const (decide (g = 1)), []) := by
          simp [gateCode, hg₂]
        have hc := (forall_eval_tseitinClause_iff (.const (decide (g = 1)))
          (constLabel (decide (g = 1))) 0 0 σ).1 fun j => by
            have := hfield (j := j) (tag := 0) (p := g) (by omega) (by omega) (hpay (by omega))
            simpa [clauseOf, j.isLt, hg₂] using this
        have hw : n + g = n + (decide (g = 1)).toNat := by
          rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl <;> rfl
        rw [hcode, hw, wireLabel_const]
        exact hc
      · obtain ⟨t, ht, l, c, hl, hw⟩ := exists_wire_eq (k := k) (State := State) (n := n)
          (Nat.le_of_not_lt hg₂) hg
        have hwn : n + (wire n T t l c - n) = wire n T t l c := by simp only [wire]; omega
        have hp := fields_lt (d := timeBits T) (slot_lt_two_pow l)
          (lt_of_lt_of_le hl.lt (numCols_le_two_pow T)) (lt_two_pow_timeBits ht)
        have hpos := (forall_eval_posClause_iff tm σ n T t c l).1 fun j => by
          rw [← clauseOf_pos tm x j ht hl]
          exact hfield (by omega) (by omega) hp
        have hwin := table_inWindow (n := n) hl.lt tm l
        have hv := value_gateAt tm (fun w => σ (wireLabel k State n T w)) n T t c l
        rw [← hw, gateCode_wire tm hl, hv, hwn, wireLabel_wire hl, hpos]
        generalize table tm l = e at hwin ⊢
        obtain ⟨op, left, right⟩ := e
        obtain ⟨hra, hrb⟩ := hwin
        dsimp only
        rw [wireLabel_resolve hra, wireLabel_resolve hrb]
  · rintro ⟨τ, hτ⟩
    obtain ⟨hτo, hτx, hτφ⟩ := (eval_tseitinSatCNF_eq_true_iff _ _ _ _ _).1 hτ
    rw [eval_tseitinCNF_eq_true_iff] at hτφ
    have hgate {g : ℕ} (hg : g < numGates k State T) :
        τ (n + g) = (gateCode tm n T g).1.value (τ ((gateCode tm n T g).2.getD 0 0))
          (τ ((gateCode tm n T g).2.getD 1 0)) := by
      have := hτφ g (by rwa [length_gates])
      rwa [getElem_gates] at this
    have h2 : 2 ≤ numGates k State T := by simp only [numGates]; omega
    have hwire {t c : ℕ} {l : Loc k State} (hl : l.ColOK T c) (ht : t ≤ T) :
        τ (wire n T t l c) = if t = 0 then initBit tm T c l
          else (table tm l).1.value (τ ((table tm l).2.1.resolve n T t c))
            (τ ((table tm l).2.2.resolve n T t c)) := by
      have hwn : n + (wire n T t l c - n) = wire n T t l c := by simp only [wire]; omega
      rw [← hwn, hgate (wire_sub_lt_numGates hl ht), gateCode_wire tm hl, value_gateAt]
    refine ⟨fun lab => τ (wireOf (k := k) (State := State) n T lab), ?_⟩
    rw [succinctCNF, CNF.eval_map_eq_true_iff]
    intro idx _
    refine eval_clauseOf tm (fun b => ?_) (fun i hi => ?_) ?_ (fun t ht c l hl => ?_) _ _ _
    · rw [wireOf_constLabel]
      cases b
      · simpa [gateCode, Op.value] using hgate (g := 0) (by omega)
      · simpa [gateCode, Op.value] using hgate (g := 1) (by omega)
    · simpa using hτx i hi
    · simpa [outLabel, outWire, wireOf_posLabel _ (show 0 < 2 ^ colBits T from Nat.two_pow_pos _)]
        using hτo
    · have hwin := table_inWindow (n := n) hl.lt tm l
      rw [wireOf_posLabel _ (lt_of_lt_of_le hl.lt (numCols_le_two_pow T)), hwire hl ht]
      generalize table tm l = e at hwin ⊢
      obtain ⟨op, left, right⟩ := e
      obtain ⟨hra, hrb⟩ := hwin
      dsimp only
      rw [wireOf_label hra, wireOf_label hrb]

/-- **The tableau formula on labels is satisfiable** exactly when some input of length `n`
extending `x` makes `tm` write exactly `[true]` within `T` steps, for `n < 2 T`. -/
theorem satisfiable_succinctCNF_iff {n T : ℕ} (hn : n < 2 * T) {x : List Bool}
    (hx : x.length ≤ n) :
    (succinctCNF tm x n T).Satisfiable ↔ ∃ y : List Bool, y.length = n ∧ x <+: y ∧
      OutView.ofList (tm.runFrom (tm.initCfg y) T).output = .one true := by
  rw [satisfiable_succinctCNF_iff_tseitin tm hn hx,
    satisfiable_tseitinSatCNF_iff (isCodeFrom_gates tm n T) hx
      (by simpa [length_gates] using outWire_lt (k := k) (State := State) n T)]
  refine exists_congr fun y => and_congr_right fun hy => and_congr_right fun _ => ?_
  subst hy
  rw [evalOutput_gates tm (by omega), decide_eq_true_iff]

/-! ### Size -/

/-- **Every clause of the formula has three literals.** -/
theorem length_of_mem_succinctCNF {x : List Bool} {n T : ℕ} {C : Clause ℕ}
    (hC : C ∈ succinctCNF tm x n T) : C.length = 3 := by
  obtain ⟨idx, -, rfl⟩ := List.mem_map.1 hC
  unfold clauseAt clauseOf
  split_ifs
  · exact length_tseitinClause _ _ _ _ _
  · rfl
  · rfl
  · rfl
  · split
    · split_ifs
      · unfold posClause
        split_ifs
        · exact length_tseitinClause _ _ _ _ _
        · split
          exact length_tseitinClause _ _ _ _ _
      · rfl
    · rfl
  · rfl
  · rfl
  · rfl

/-- The formula has `2 ^ clauseBits k State T` clauses. -/
theorem length_succinctCNF (x : List Bool) (n T : ℕ) :
    (succinctCNF tm x n T).length = 2 ^ clauseBits k State T := by
  simp [succinctCNF]

variable (k State) in
/-- The width of a label: the tag, then the slot, the column and the block. -/
noncomputable def labelBits (T : ℕ) : ℕ := 2 + (slotBits k State + colBits T + timeBits T)

omit [DecidableEq State] in
/-- The labels of positions of blocks `t ≤ T` fit in `labelBits` bits. -/
theorem posLabel_lt {T t c : ℕ} (l : Loc k State) (hc : c < 2 ^ colBits T) (ht : t ≤ T) :
    posLabel k State T t c l < 2 ^ labelBits k State T := by
  have := fields_lt (slot_lt_two_pow l) hc (lt_two_pow_timeBits ht)
  rw [labelBits, Nat.pow_add]
  simp only [posLabel]
  omega

omit [DecidableEq State] in
/-- The labels of the inputs `i < 2 T` fit in `labelBits` bits. -/
theorem inputLabel_lt {T i : ℕ} (hi : i < 2 * T) : inputLabel i < 2 ^ labelBits k State T := by
  have hcb : 2 * T < 2 ^ colBits T := Nat.lt_size_self _
  have : 2 ^ colBits T ≤ 2 ^ (slotBits k State + colBits T + timeBits T) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [labelBits, Nat.pow_add]
  simp only [inputLabel]
  omega

omit [DecidableEq State] in
/-- The labels of the constants fit in `labelBits` bits, for `1 ≤ T`. -/
theorem constLabel_lt {T : ℕ} (hT : 1 ≤ T) (b : Bool) : constLabel b < 2 ^ labelBits k State T := by
  have h := inputLabel_lt (k := k) (State := State) (T := T) (i := 1) (by omega)
  cases b <;> simp only [constLabel, inputLabel, Bool.toNat_false, Bool.toNat_true] at h ⊢ <;> omega

omit [DecidableEq State] in
/-- The labels of the references of a gate in a column of the window fit in `labelBits` bits. -/
theorem Ref.label_lt {n T t c : ℕ} (hn : n < 2 * T) (ht : t ≤ T) {r : Ref k State}
    (hr : r.InWindow n T c) : r.label n T t c < 2 ^ labelBits k State T := by
  have hT : 1 ≤ T := by omega
  rcases r with _ | _ | _ | ⟨p, l, cs, g⟩
  · exact constLabel_lt hT _
  · exact constLabel_lt hT _
  · simp only [Ref.label]
    split_ifs
    · exact inputLabel_lt (by omega)
    · exact constLabel_lt hT _
  · simp only [Ref.InWindow] at hr
    by_cases hg : g.test n T c = true
    · simp only [Ref.label, hg, ↓reduceIte]
      exact posLabel_lt _ (lt_of_le_of_lt (Loc.labelCol_le l _)
        (lt_of_lt_of_le (hr hg) (numCols_le_two_pow T))) (by split <;> omega)
    · simp only [Ref.label, hg, Bool.false_eq_true, ↓reduceIte]
      exact constLabel_lt hT _

omit [DecidableEq State] in
private theorem mem_tseitinClause {op : Op} {w a b v : ℕ} {s : Bool} {j : Fin 3}
    (h : (v, s) ∈ tseitinClause op w a b j) : v = w ∨ v = a ∨ v = b := by
  fin_cases j <;> cases op <;> simp [tseitinClause] at h <;> omega

/-- **Every variable of the formula is below `2 ^ labelBits k State T`**, for `n < 2 T`: labels
have `labelBits k State T` bits. -/
theorem lt_two_pow_labelBits_of_mem_vars {n T : ℕ} (hn : n < 2 * T) {x : List Bool}
    (hx : x.length ≤ n) {v : ℕ} (hv : v ∈ (succinctCNF tm x n T).vars) :
    v < 2 ^ labelBits k State T := by
  have hT : 1 ≤ T := by omega
  have h0 : 0 < 2 ^ labelBits k State T := Nat.two_pow_pos _
  obtain ⟨C, hC, s, hvC⟩ := CNF.mem_vars.1 hv
  obtain ⟨idx, -, rfl⟩ := List.mem_map.1 hC
  unfold clauseAt clauseOf at hvC
  split_ifs at hvC with hj h₀ hp h₁ hp' h₂ h₃
  · rcases mem_tseitinClause hvC with rfl | rfl | rfl
    · exact constLabel_lt hT _
    · exact h0
    · exact h0
  · simp [tautology] at hvC; omega
  · simp only [unitClause, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
      or_self] at hvC
    rw [hvC.1]
    exact inputLabel_lt (by omega)
  · simp [tautology] at hvC; omega
  · split at hvC
    · rename_i l _
      split_ifs at hvC with h
      · have hc := lt_of_lt_of_le h.2.lt (numCols_le_two_pow T)
        have hwin := table_inWindow (n := n) h.2.lt tm l
        unfold posClause at hvC
        generalize table tm l = e at hwin hvC
        obtain ⟨op, left, right⟩ := e
        obtain ⟨hra, hrb⟩ := hwin
        split_ifs at hvC <;> rcases mem_tseitinClause hvC with rfl | rfl | rfl <;>
          first
          | exact posLabel_lt _ hc h.1
          | exact h0
          | exact Ref.label_lt hn h.1 hra
          | exact Ref.label_lt hn h.1 hrb
      · simp [tautology] at hvC; omega
    · simp [tautology] at hvC; omega
  · simp only [unitClause, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
      or_self] at hvC
    rw [hvC.1]
    exact posLabel_lt _ (Nat.two_pow_pos _) le_rfl
  · simp [tautology] at hvC; omega
  · simp [tautology] at hvC; omega

end Cslib.Circuits.Boolean.Tableau
