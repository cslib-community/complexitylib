/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Circuit.Boolean.Tableau.Layout
import Complexity.Foundations.Data.List.Lookup

/-!
# The uniform tableau circuit of a multi-tape machine

The run of a multi-tape machine over `Bool` for `T` steps on inputs of length `n` is simulated by
a De Morgan circuit written down gate by gate (`Cslib.Circuits.Boolean.Tableau.gates`), in the
format of `Cslib.Circuits.Circuit.code`. The circuit is *uniform*: the operation and the wires of
gate `g` are given by a table of constant size, indexed by `g` modulo the size of a block, and by
a few additions and multiplications of `g`, `n` and `T` (`Cslib.Circuits.Boolean.Tableau.gateCode`).
This is the circuit of Ladner's proof that the circuit value problem is `P`-complete under
logarithmic-space reductions [Ladner1975], [Arora and Barak, Section 6.7][AroraBarak09],
[Papadimitriou, Theorem 8.1][Papadimitriou94].

The circuit follows the configuration in the model of `Turing.MultiTapeTM`, without conversion to
a single-tape or oblivious machine. Work-tape cells `-T, …, T` and input positions `0, …, n + 1`
share the `2 T + 1` *columns* `c`: column `c` holds the input head at position `c`, and the work
heads and work cells at `c - T`. After two constant gates (`false` at wire `n`, `true` at wire
`n + 1`), the circuit has one block of gates for each time `t ≤ T`. Block `0` consists of
constants describing the initial configuration. Block `t + 1` reads block `t` and has four
regions (`Complexity/Computability/Circuit/Boolean/Tableau/Layout.lean`):

* the *scan*, column by column: the symbols under the heads, as disjunctions accumulated across
  the columns (`Cslib.Circuits.Boolean.Tableau.ScanLoc`), and the negated head positions;
* the *global* gates: each situation (`Turing.MultiTapeTM.Situation`) as a conjunction of the
  state and the symbols read, and each attribute of the action
  (`Cslib.Circuits.Boolean.Tableau.Attr`) as a disjunction over the situations with that
  attribute;
* the *global features*: the state and the view of the output (`Turing.OutView`);
* the *column features*: the input head, the work heads and the work cells of each column.

Every feature at time `t + 1` is a disjunction of at most eight conjunctions of two wires
(`Cslib.Circuits.Boolean.Tableau.gfTerms`, `Cslib.Circuits.Boolean.Tableau.colTerms`), computed
by sixteen gates. A gate refers to wires symbolically (`Cslib.Circuits.Boolean.Tableau.Ref`),
relative to its block and column, and a reference is resolved to a wire number by arithmetic
(`Cslib.Circuits.Boolean.Tableau.Ref.resolve`).

The circuit is well formed (`Cslib.Circuits.Boolean.Tableau.isCodeFrom_gates`): every gate reads
only inputs and earlier gates. Its correctness is proved in
`Complexity/Computability/Circuit/Boolean/Tableau/Correct.lean`.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Attr.test`, `Cslib.Circuits.Boolean.Tableau.sitOf`,
  `Cslib.Circuits.Boolean.Tableau.scanTerm`, `Cslib.Circuits.Boolean.Tableau.gfTerms`,
  `Cslib.Circuits.Boolean.Tableau.colTerms`, `Cslib.Circuits.Boolean.Tableau.gfInit`,
  `Cslib.Circuits.Boolean.Tableau.colInit`, `Cslib.Circuits.Boolean.Tableau.initBit`,
  `Cslib.Circuits.Boolean.Tableau.table`: the gate and initial-configuration tables for a block.
* `Cslib.Circuits.Boolean.Tableau.gateAt`, `Cslib.Circuits.Boolean.Tableau.gateCode`: the gate at
  a block position and the gate with a given number.
* `Cslib.Circuits.Boolean.Tableau.gates`, `Cslib.Circuits.Boolean.Tableau.outWire`: the gate list
  and the output wire.
* `Cslib.Circuits.Boolean.Tableau.circuit`: the tableau as a De Morgan circuit.

## Main results

* `Cslib.Circuits.Boolean.Tableau.gateCode_wire`: the gate at a position's wire is the gate of its
  position.
* `Cslib.Circuits.Boolean.Tableau.isCodeFrom_gates`: the gate list is the code of a program.
* `Cslib.Circuits.Boolean.Tableau.code_circuit`: the code of the circuit is the gate list with
  the output wire.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Sections 6.1 and 6.7][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Theorem 8.1][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau

open Turing MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]

/-! ### The gates -/

/-- Whether an action has an attribute. -/
def Attr.test (a : Action k Bool State) : Attr k State → Bool
  | .state q => decide (a.state = q)
  | .inMove m => decide (a.inputTape = m)
  | .write i w => decide ((a.workTapes i).1 = w)
  | .move i m => decide ((a.workTapes i).2 = m)
  | .out e => decide (a.output = e)

/-- The situation with number `j`. -/
noncomputable def sitOf (j : Fin (numSit k State)) : Situation k State :=
  (Fintype.equivFin (Situation k State)).symm j

/-- The two wires of the contribution of a column to a scanned quantity. -/
def scanTerm : ScanQ k → Ref k State × Ref k State
  | .inRead none => (colF .inPos .same .outRange, .tru)
  | .inRead (some true) => (colF .inPos .same .always, .inp)
  | .inRead (some false) => (colF .inPos .same .inRange, scanAt .nx .same .always)
  | .read i s => (colF (.head i) .same .always, colF (.cell i s) .same .always)

/-- The terms of a global feature at the next time: the feature holds after the step exactly when
both wires of one term are true. -/
def gfTerms : GFeat State → List (Ref k State × Ref k State)
  | .state none => [(halted, .tru), (act (.state none), .tru)]
  | .state (some q) => [(act (.state (some q)), .tru)]
  | .out .empty => [(halted, gfF (.out .empty)), (act (.out none), gfF (.out .empty))]
  | .out (.one b) => [(halted, gfF (.out (.one b))), (act (.out none), gfF (.out (.one b))),
      (act (.out (some b)), gfF (.out .empty))]
  | .out .many => [(halted, gfF (.out .many)), (act (.out none), gfF (.out .many)),
      (act (.out (some false)), gfF (.out (.one false))),
      (act (.out (some false)), gfF (.out (.one true))),
      (act (.out (some false)), gfF (.out .many)),
      (act (.out (some true)), gfF (.out (.one false))),
      (act (.out (some true)), gfF (.out (.one true))),
      (act (.out (some true)), gfF (.out .many))]

/-- The terms of a column feature at the next time. -/
def colTerms : ColFeat k → List (Ref k State × Ref k State)
  | .inPos => [(halted, colF .inPos .same .always),
      (act (.inMove 0), colF .inPos .same .always),
      (act (.inMove 1), colF .inPos .prev .leEnd),
      (act (.inMove (-1)), colF .inPos .next .ltLast),
      (act (.inMove (-1)), colF .inPos .same .isZero),
      (act (.inMove 1), colF .inPos .same .isEnd)]
  | .head i => [(halted, colF (.head i) .same .always),
      (act (.move i 0), colF (.head i) .same .always),
      (act (.move i 1), colF (.head i) .prev .pos),
      (act (.move i (-1)), colF (.head i) .next .ltLast)]
  | .cell i s => [(halted, colF (.cell i s) .same .always),
      (act (.write i none), colF (.cell i s) .same .always),
      (scanAt (.nh i) .same .always, colF (.cell i s) .same .always),
      (colF (.head i) .same .always, act (.write i (some s)))]

variable (tm : MultiTapeTM k Bool State)

/-- **The gate at each position of a block** after the first, with symbolic references to its
wires. -/
noncomputable def table : Loc k State → Op × Ref k State × Ref k State
  | .scan (.nh i) => (.not, colF (.head i) .same .always, .fls)
  | .scan .nx => (.not, .inp, .fls)
  | .scan (.term q) => (.and, scanTerm q)
  | .scan (.acc q) => (.or, scanAt (.acc q) .prev .pos, scanAt (.term q) .same .always)
  | .glob (.sit j i) =>
    (.and, Fin.cases (motive := fun _ => Ref k State) (gfF (.state (some (sitOf j).1)))
        (fun i' => .node false (.glob (.sit j i'.castSucc)) .same .always) i,
      Fin.cases (motive := fun _ => Ref k State)
        (scanAt (.acc (.inRead (sitOf j).2.1)) .last .always)
        (fun i' => scanAt (.acc (.read i' ((sitOf j).2.2 i'))) .last .always) i)
  | .glob (.attr v j) =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.glob (.attr v j'.castSucc)) .same .always) j,
      Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => if v.test (tm.actionOf (sitOf j')) then
          .node false (.glob (.sit j' (Fin.last k))) .same .always else .fls) j)
  | .gf f false j => (.and, (gfTerms f).getD j (.fls, .fls))
  | .gf f true j =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.gf f true j'.castSucc) .same .always) j,
      .node false (.gf f false j) .same .always)
  | .col f false j => (.and, (colTerms f).getD j (.fls, .fls))
  | .col f true j =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.col f true j'.castSucc) .same .always) j,
      .node false (.col f false j) .same .always)

/-- The value of a global feature in the initial configuration. -/
def gfInit : GFeat State → Bool
  | .state q => decide (q = some tm.q₀)
  | .out o => decide (o = .empty)

/-- The value of a column feature in the initial configuration, for the column `c` of `2 T + 1`:
the input head on the first input cell, the work heads on cell `0`, the work cells blank. -/
def colInit (T c : ℕ) : ColFeat k → Bool
  | .inPos => decide (c = 1)
  | .head _ => decide (c = T)
  | .cell _ s => decide (s = none)

/-- The constant at each position of the first block: the initial value of a feature at the last
gate of its gadget, `false` elsewhere. -/
def initBit (T c : ℕ) : Loc k State → Bool
  | .gf f true j => decide (j = 7) && gfInit tm f
  | .col f true j => decide (j = 7) && colInit T c f
  | _ => false

/-- The gate at the position `l` of block `t`, in column `c`. -/
noncomputable def gateAt (n T t c : ℕ) (l : Loc k State) : Op × List ℕ :=
  if t = 0 then (.const (initBit tm T c l), [])
  else ((table tm l).1, argsOf (table tm l).1 ((table tm l).2.1.resolve n T t c)
    ((table tm l).2.2.resolve n T t c))

/-- **The gate with number `g`** of the tableau of `tm` for `T` steps on inputs of length `n`:
gates `0` and `1` are the constants `false` and `true`, and gate `2 + t * B + r` is the gate at
offset `r` of block `t`, for blocks of `B` gates. -/
noncomputable def gateCode (n T g : ℕ) : Op × List ℕ :=
  if g < 2 then (.const (decide (g = 1)), [])
  else
    let t := (g - 2) / blockSize k State T
    let r := (g - 2) % blockSize k State T
    if r < globStart k T then
      gateAt tm n T t (r / scanWidth k) (.scan (ScanLoc.ofIdx (r % scanWidth k)))
    else if r < gfStart k State T then
      gateAt tm n T t 0 (.glob (GlobLoc.ofIdx (r - globStart k T)))
    else if r < colStart k State T then
      gateAt tm n T t 0 (.gf (GFeat.ofIdx ((r - gfStart k State T) / 16))
        (gadgetB (r - gfStart k State T)) (gadgetJ (r - gfStart k State T)))
    else
      gateAt tm n T t ((r - colStart k State T) / colWidth k)
        (.col (ColFeat.ofIdx ((r - colStart k State T) % colWidth k / 16))
          (gadgetB ((r - colStart k State T) % colWidth k))
          (gadgetJ ((r - colStart k State T) % colWidth k)))

/-- **The gate list of the tableau** of `tm` for `T` steps on inputs of length `n`. -/
noncomputable def gates (n T : ℕ) : List (Op × List ℕ) :=
  (List.range (numGates k State T)).map (gateCode tm n T)

/-- **The output wire of the tableau**: the output has the view `[true]` at time `T`. -/
noncomputable def outWire (k : ℕ) (State : Type) [Fintype State] (n T : ℕ) : ℕ :=
  wire (k := k) (State := State) n T T (.gf (.out (.one true)) true 7) 0

/-! ### Gates at their wires -/

variable {T : ℕ}

/-- **The gate at a wire** is the gate of its position. -/
theorem gateCode_wire {n T t : ℕ} {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    gateCode tm n T (wire n T t l c - n) = gateAt tm n T t c l := by
  obtain ⟨hdiv, hmod⟩ := div_mod_wire (n := n) (t := t) hl
  have h2 : ¬ wire n T t l c - n < 2 := by rw [wire_sub]; omega
  rw [gateCode, ite_eq_right h2]
  simp only [hdiv, hmod]
  have hgs : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _
  have hgc : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.ColOK] at hl <;>
    simp only [Loc.offset]
  · have hi := l.idx_lt
    have hw : 0 < scanWidth k := by simp only [scanWidth]; omega
    have h₁ : c * scanWidth k + l.idx < globStart k T := scan_offset_lt_globStart hl l
    have h₂ : (c * scanWidth k + l.idx) / scanWidth k = c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hi, Nat.zero_add]
    have h₃ : (c * scanWidth k + l.idx) % scanWidth k = l.idx := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [h₁, ↓reduceIte, h₂, h₃, ScanLoc.ofIdx_idx]
  · have hi := l.idx_lt
    subst hl
    have h₁ : ¬ globStart k T + l.idx < globStart k T := by omega
    have h₂ : globStart k T + l.idx < gfStart k State T := by simp only [gfStart]; omega
    simp only [h₁, h₂, ↓reduceIte, Nat.add_sub_cancel_left, GlobLoc.ofIdx_idx]
  · subst hl
    have := gfStart_add_gadgetIdx_lt (k := k) (T := T) f b j
    have h₁ : ¬ gfStart k State T + gadgetIdx f.idx b j < globStart k T := by omega
    have h₂ : ¬ gfStart k State T + gadgetIdx f.idx b j < gfStart k State T := by omega
    simp only [h₁, h₂, this, ↓reduceIte, Nat.add_sub_cancel_left, gadgetIdx_div,
      GFeat.ofIdx_idx, gadgetB_gadgetIdx, gadgetJ_gadgetIdx]
  · have h₁ := gadgetIdx_lt f.idx b j
    have h₂ := f.idx_lt
    have hw : gadgetIdx f.idx b j < colWidth k := by simp only [colWidth]; omega
    have hw0 : 0 < colWidth k := by simp only [colWidth]; omega
    have h₃ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j < globStart k T := by
      omega
    have h₄ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j < gfStart k State T := by
      omega
    have h₅ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j <
        colStart k State T := by omega
    have h₆ : colStart k State T + c * colWidth k + gadgetIdx f.idx b j - colStart k State T =
        gadgetIdx f.idx b j + c * colWidth k := by omega
    have h₇ : (gadgetIdx f.idx b j + c * colWidth k) / colWidth k = c := by
      rw [Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hw, Nat.zero_add]
    have h₈ : (gadgetIdx f.idx b j + c * colWidth k) % colWidth k = gadgetIdx f.idx b j := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
    simp only [h₃, h₄, h₅, ↓reduceIte, h₆, h₇, h₈, gadgetIdx_div, ColFeat.ofIdx_idx,
      gadgetB_gadgetIdx, gadgetJ_gadgetIdx]

/-! ### Well-formedness -/

section Earlier

variable {n T t c : ℕ} {l : Loc k State}

omit [DecidableEq State] in
private theorem resolve_fls_lt : (Ref.fls : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; omega

omit [DecidableEq State] in
private theorem resolve_tru_lt : (Ref.tru : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; omega

omit [DecidableEq State] in
private theorem resolve_inp_lt : (Ref.inp : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; split_ifs <;> omega

omit [DecidableEq State] in
/-- A reference to the previous block reads an earlier wire. -/
private theorem resolve_prev_lt (ht : 1 ≤ t) {l' : Loc k State} {cs : ColSel} {g : Guard}
    (h : g.test n T c = true → cs.apply T c < numCols T) :
    (Ref.node true l' cs g).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, ↓reduceIte]
  split_ifs with hg
  · have := Loc.offset_lt_of_lt (l := l') (h hg)
    simp only [wire]
    have : (t - 1) * blockSize k State T + blockSize k State T = t * blockSize k State T := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ht]
    omega
  · simp only [wire]; omega

omit [DecidableEq State] in
/-- A reference to an earlier position of the current block reads an earlier wire. -/
private theorem resolve_cur_lt {l' : Loc k State} {cs : ColSel} {g : Guard}
    (h : g.test n T c = true → l'.offset T (cs.apply T c) < l.offset T c) :
    (Ref.node false l' cs g).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hg
  · have := h hg
    simp only [wire]
    omega
  · simp only [wire]; omega

end Earlier

omit [DecidableEq State] in
private theorem globStart_le_gfStart : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _

omit [DecidableEq State] in
private theorem gfStart_le_colStart : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _

omit [DecidableEq State] in
private theorem attr_offset_lt (v : Attr k State) (j : Fin (numSit k State + 1)) :
    globStart k T + (GlobLoc.attr v j).idx < gfStart k State T := by
  have := (GlobLoc.attr v j).idx_lt
  simp only [gfStart]
  omega

omit [DecidableEq State] in
/-- The references of a term of a global feature read earlier wires than the gates of the
feature. -/
private theorem gfTerms_lt {n T t : ℕ} (ht : 1 ≤ t) {f : GFeat State} {b : Bool} {j : Fin 8}
    {f' : GFeat State} {p : Ref k State × Ref k State} (hp : p ∈ gfTerms f' ∨ p = (.fls, .fls)) :
    p.1.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 ∧
      p.2.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 := by
  have hok {r : Ref k State} (hr : r = .tru ∨ r = .fls ∨ (∃ g, gfF g = r) ∨ ∃ v, act v = r) :
      r.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 := by
    rcases hr with rfl | rfl | ⟨g, rfl⟩ | ⟨v, rfl⟩
    · exact resolve_tru_lt
    · exact resolve_fls_lt
    · exact resolve_prev_lt ht fun _ => by simp [ColSel.apply, numCols]
    · refine resolve_cur_lt fun _ => ?_
      have := attr_offset_lt (T := T) v (Fin.last _)
      simp only [Loc.offset]
      omega
  rcases hp with hp | rfl
  · rcases f' with (_ | q) | ((_ | _) | _) | _ <;> simp only [gfTerms, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hok (by simp), hok (by simp)⟩
  · exact ⟨resolve_fls_lt, resolve_fls_lt⟩

omit [DecidableEq State] in
/-- The references of a term of a column feature read earlier wires than the gates of the
feature. -/
private theorem colTerms_lt {n T t c : ℕ} (ht : 1 ≤ t) (hc : c < numCols T)
    {f : ColFeat k} {b : Bool} {j : Fin 8} {f' : ColFeat k} {p : Ref k State × Ref k State}
    (hp : p ∈ colTerms f' ∨ p = (.fls, .fls)) :
    p.1.resolve n T t c < wire (State := State) n T t (.col f b j) c ∧
      p.2.resolve n T t c < wire (State := State) n T t (.col f b j) c := by
  have hcol (g : ColFeat k) (cs : ColSel) (gd : Guard)
      (h : gd.test n T c = true → cs.apply T c < numCols T) :
      (colF g cs gd : Ref k State).resolve n T t c < wire (State := State) n T t (.col f b j) c :=
    resolve_prev_lt ht h
  have hok {r : Ref k State} (hr : r = .tru ∨ r = .fls ∨ (∃ g, gfF g = r) ∨ (∃ v, act v = r) ∨
      (∃ g, colF g .same .always = r) ∨ (∃ g, colF g .prev .pos = r) ∨
      (∃ g, colF g .prev .leEnd = r) ∨ (∃ g, colF g .next .ltLast = r) ∨
      (∃ g, colF g .same .isZero = r) ∨ (∃ g, colF g .same .isEnd = r) ∨
      (∃ i, scanAt (.nh i) .same .always = r)) :
      r.resolve n T t c < wire (State := State) n T t (.col f b j) c := by
    rcases hr with rfl | rfl | ⟨g, rfl⟩ | ⟨v, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ |
      ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨i, rfl⟩
    · exact resolve_tru_lt
    · exact resolve_fls_lt
    · exact resolve_prev_lt ht fun _ => hc
    · refine resolve_cur_lt fun _ => ?_
      have := attr_offset_lt (T := T) v (Fin.last _)
      have := gfStart_le_colStart (k := k) (State := State) (T := T)
      simp only [Loc.offset]
      omega
    · exact hcol g _ _ fun _ => hc
    · exact hcol g _ _ fun _ => by simp only [ColSel.apply]; omega
    · exact hcol g _ _ fun _ => by simp only [ColSel.apply]; omega
    · exact hcol g _ _ fun hg => by
        simpa only [ColSel.apply, Guard.test, decide_eq_true_eq] using hg
    · exact hcol g _ _ fun _ => hc
    · exact hcol g _ _ fun _ => hc
    · refine resolve_cur_lt fun _ => ?_
      have := scan_offset_lt_globStart hc (.nh i)
      have := globStart_le_gfStart (k := k) (State := State) (T := T)
      have := gfStart_le_colStart (k := k) (State := State) (T := T)
      simp only [Loc.offset, ColSel.apply]
      omega
  rcases hp with hp | rfl
  · rcases f' with _ | i | ⟨i, s⟩ <;> simp only [colTerms, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hok (by simp), hok (by simp)⟩
  · exact ⟨resolve_fls_lt, resolve_fls_lt⟩

/-- **The references of a gate read earlier wires.** -/
private theorem resolve_table_lt {n T t c : ℕ} (ht : 1 ≤ t) {l : Loc k State} (hl : l.ColOK T c) :
    (table tm l).2.1.resolve n T t c < wire n T t l c ∧
      (table tm l).2.2.resolve n T t c < wire n T t l c := by
  have hc := hl.lt
  have hprevS (g : ColFeat k) :
      (colF g .same .always : Ref k State).resolve n T t c < wire n T t l c :=
    resolve_prev_lt ht fun _ => hc
  have hgs := globStart_le_gfStart (k := k) (State := State) (T := T)
  have hgc := gfStart_le_colStart (k := k) (State := State) (T := T)
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩
  · rcases l with i | _ | q | q
    · exact ⟨hprevS _, resolve_fls_lt⟩
    · exact ⟨resolve_inp_lt, resolve_fls_lt⟩
    · rcases q with (_ | (_ | _)) | ⟨i, s⟩
      · exact ⟨resolve_prev_lt ht fun _ => hc, resolve_tru_lt⟩
      · refine ⟨resolve_prev_lt ht fun _ => hc, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, ColSel.apply, ScanLoc.idx, ScanQ.idx, symIdx]
        omega
      · exact ⟨resolve_prev_lt ht fun _ => hc, resolve_inp_lt⟩
      · exact ⟨hprevS _, hprevS _⟩
    · refine ⟨resolve_cur_lt fun hg => ?_, resolve_cur_lt fun _ => ?_⟩
      · simp only [Guard.test, decide_eq_true_eq] at hg
        simp only [Loc.offset, ColSel.apply]
        have : (c - 1) * scanWidth k + scanWidth k = c * scanWidth k := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hg]
        have := scanWidth_pos (k := k)
        omega
      · simp only [Loc.offset, ColSel.apply, ScanLoc.idx]
        omega
  · simp only [Loc.ColOK] at hl
    subst hl
    have hlast (l' : ScanLoc k) (g : GlobLoc k State) :
        (scanAt l' .last .always : Ref k State).resolve n T t 0 < wire n T t (.glob g) 0 :=
      resolve_cur_lt fun _ => by
        have := scan_offset_lt_globStart (k := k) (T := T) (c := 2 * T)
          (by simp [numCols]) l'
        simp only [Loc.offset, ColSel.apply]
        omega
    rcases l with ⟨j, i⟩ | ⟨v, j⟩
    · cases i using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        exact ⟨resolve_prev_lt ht fun _ => by simp [ColSel.apply, numCols], hlast _ _⟩
      | succ i =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, hlast _ _⟩
        simp only [Loc.offset, GlobLoc.idx, Fin.val_castSucc, Fin.val_succ]
        omega
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        exact ⟨resolve_fls_lt, resolve_fls_lt⟩
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, ?_⟩
        · simp only [Loc.offset, GlobLoc.idx, Fin.val_castSucc, Fin.val_succ]
          omega
        · split_ifs
          · refine resolve_cur_lt fun _ => ?_
            have := (GlobLoc.sit (State := State) j (Fin.last k)).idx_lt
            have h₁ : (GlobLoc.sit (State := State) j (Fin.last k)).idx <
                numSit k State * (k + 1) := by
              simp only [GlobLoc.idx, Fin.val_last]
              have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) :=
                Nat.mul_le_mul_right _ j.isLt
              rw [Nat.succ_mul] at this
              omega
            simp only [Loc.offset, GlobLoc.idx] at h₁ ⊢
            omega
          · exact resolve_fls_lt
  · simp only [Loc.ColOK] at hl
    subst hl
    rcases b with _ | _
    · exact gfTerms_lt ht (List.getD_mem_or _ _ _)
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        refine ⟨resolve_fls_lt, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true]
        omega
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, resolve_cur_lt fun _ => ?_⟩ <;>
          simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true,
            Fin.val_castSucc, Fin.val_succ] <;> omega
  · rcases b with _ | _
    · exact colTerms_lt ht hc (List.getD_mem_or _ _ _)
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        refine ⟨resolve_fls_lt, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true, ColSel.apply]
        omega
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, resolve_cur_lt fun _ => ?_⟩ <;>
          simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true,
            Fin.val_castSucc, Fin.val_succ, ColSel.apply] <;> omega

/-! ### The gate list is the code of a circuit -/

omit [DecidableEq State] in
private theorem length_argsOf (op : Op) (a b : ℕ) :
    (argsOf op a b).length = signature.Arity op := by
  cases op <;> rfl

omit [DecidableEq State] in
private theorem mem_argsOf {op : Op} {a b i : ℕ} (h : i ∈ argsOf op a b) : i = a ∨ i = b := by
  cases op <;> simp_all [argsOf]

private theorem length_gateAt (n T t c : ℕ) (l : Loc k State) :
    (gateAt tm n T t c l).2.length = signature.Arity (gateAt tm n T t c l).1 := by
  unfold gateAt
  split_ifs
  · rfl
  · exact length_argsOf _ _ _

/-- A gate at a position reads earlier wires. -/
private theorem lt_of_mem_gateAt {n T t c : ℕ} {l : Loc k State} (hl : l.ColOK T c) {i : ℕ}
    (hi : i ∈ (gateAt tm n T t c l).2) : i < wire n T t l c := by
  unfold gateAt at hi
  split_ifs at hi with ht
  · simp at hi
  · have h := resolve_table_lt tm (n := n) (Nat.one_le_iff_ne_zero.mpr ht) hl
    rcases mem_argsOf hi with rfl | rfl
    exacts [h.1, h.2]

/-- **The tableau is well formed**: its gate list is the code of a program on `n` inputs. -/
theorem isCodeFrom_gates (n T : ℕ) : Program.IsCodeFrom signature n 0 (gates tm n T) := by
  refine Program.isCodeFrom_of_getElem fun g hg => ?_
  simp only [gates, List.length_map, List.length_range] at hg
  simp only [gates, List.getElem_map, List.getElem_range, Nat.add_zero]
  by_cases h₂ : g < 2
  · simp only [gateCode, h₂, ↓reduceIte]
    exact ⟨rfl, by simp⟩
  · obtain ⟨t, -, l, c, hl, hw⟩ := exists_wire_eq (k := k) (State := State) (n := n)
      (Nat.le_of_not_lt h₂) hg
    rw [← hw, gateCode_wire tm hl]
    refine ⟨length_gateAt tm _ _ _ _ _, fun i hi => ?_⟩
    have := lt_of_mem_gateAt tm hl hi
    rw [wire_sub] at hw ⊢
    simp only [wire] at this
    omega

omit [DecidableEq State] in
/-- The output wire index is strictly less than the total number of wires
`n + numGates k State T`. -/
theorem outWire_lt (n T : ℕ) : outWire k State n T < n + numGates k State T := by
  have := Loc.offset_lt (k := k) (State := State) (T := T)
    (l := .gf (.out (.one true)) true 7) (c := 0) rfl
  simp only [outWire, wire, numGates]
  rw [Nat.succ_mul]
  omega

/-- The raw gate list `gates tm n T` and output wire `outWire k State n T` form a valid circuit
code. -/
theorem isSome_ofCode (n T : ℕ) :
    (Circuit.ofCode n 1 (gates tm n T, [outWire k State n T]) :
      Option (Circuit signature n 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_gates tm n T, rfl, fun i hi => ?_⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simpa [gates] using outWire_lt (k := k) (State := State) n T

/-- **The tableau circuit** of `tm` for `T` steps on inputs of length `n`. -/
noncomputable def circuit (n T : ℕ) : Circuit signature n 1 :=
  (Circuit.ofCode n 1 (gates tm n T, [outWire k State n T])).get (isSome_ofCode tm n T)

/-- The code of the tableau circuit is its gate list with the output wire. -/
theorem code_circuit (n T : ℕ) :
    (circuit tm n T).code = (gates tm n T, [outWire k State n T]) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

end Cslib.Circuits.Boolean.Tableau
