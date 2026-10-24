/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Basic
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Correctness of the uniform tableau circuit

The tableau circuit of a multi-tape machine
(`Complexity/Computability/Circuit/Boolean/Tableau/Basic.lean`) computes the run: on an input
`x` of length `n`, for `T` steps with `n < 2 T`, the wire of each feature at time `t ≤ T` carries
the value of that feature in the configuration after `t` steps
(`Cslib.Circuits.Boolean.Tableau.invariant_le`). In particular the output wire is true exactly when
the output written after `T` steps is `[true]` (`Cslib.Circuits.Boolean.Tableau.evalOutput_gates`),
and the tableau circuit outputs this value (`Cslib.Circuits.Boolean.Tableau.eval_circuit`).

The proof follows the blocks. In block `t + 1`, the scan accumulates the symbols under the heads
across the columns, the global gates compute the situation and the attributes of the action, and
the gadget of each feature computes the disjunction of its terms, which is the step equation of
the feature.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.val`: the value of a numbered tableau wire.
* `Cslib.Circuits.Boolean.Tableau.colSem`, `Cslib.Circuits.Boolean.Tableau.gfSem`: the column and
  global features of a machine configuration.
* `Cslib.Circuits.Boolean.Tableau.Invariant`: the agreement of feature wires with the run.

## Main results

* `Cslib.Circuits.Boolean.Tableau.invariant_le`: the features at every time `t ≤ T`.
* `Cslib.Circuits.Boolean.Tableau.evalOutput_gates`: the output wire carries the answer.
* `Cslib.Circuits.Boolean.Tableau.eval_circuit`: the tableau circuit outputs the answer.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean.Tableau

open Turing MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

/-! ### Values of wires -/

/-- The value of a De Morgan gate from its operation and its first two arguments. -/
private def opVal : Op → Bool → Bool → Bool
  | .const b, _, _ => b
  | .not, a, _ => !a
  | .and, a, b => a && b
  | .or, a, b => a || b

private theorem interpretation_argsOf (op : Op) (a b : ℕ) (f : ℕ → Bool) :
    (interpretation op fun i => (argsOf op a b)[i.val]?.elim false f) = opVal op (f a) (f b) := by
  cases op <;> rfl

/-- The value of wire `w` of the tableau of `tm` for `T` steps, on the input `x`. -/
noncomputable def val (T : ℕ) (x : List Bool) (w : ℕ) : Bool :=
  (evalCode interpretation false x (gates tm x.length T)).getD w false

variable {T : ℕ} {x : List Bool}

/-- The value of a numbered gate is its operation applied to the values of its arguments. -/
private theorem val_add {g : ℕ} (hg : g < numGates k State T) :
    val tm T x (x.length + g) = interpretation (gateCode tm x.length T g).1
      fun a => (gateCode tm x.length T g).2[a.val]?.elim false (val tm T x) := by
  exact getD_evalCode interpretation false x (isCodeFrom_gates tm x.length T)
    (by simp [gates, hg])

/-- The input wires carry the input. -/
private theorem val_input {i : ℕ} (hi : i < x.length) : val tm T x i = x[i] := by
  rw [val, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp only [length_evalCode]; omega)]
  have hpre := prefix_evalCode interpretation false x (gates tm x.length T)
  rw [Option.getD_some, hpre.getElem hi]

omit [DecidableEq State] in
private theorem two_le_numGates : 2 ≤ numGates k State T := by
  simp only [numGates]
  omega

/-- The constant `false` at wire `n`. -/
private theorem val_fls : val tm T x x.length = false := by
  have := val_add tm (T := T) (x := x) (g := 0)
    (by have := two_le_numGates (k := k) (State := State) (T := T); omega)
  simpa [gateCode, interpretation] using this

/-- The constant `true` at wire `n + 1`. -/
private theorem val_tru : val tm T x (x.length + 1) = true := by
  have := val_add tm (T := T) (x := x) (g := 1)
    (by have := two_le_numGates (k := k) (State := State) (T := T); omega)
  simpa [gateCode, interpretation] using this

/-- **The value of a position** of block `t ≤ T`: the initial constant in block `0`, and otherwise
the operation of the gate applied to the values of its references. -/
private theorem val_wire {t c : ℕ} {l : Loc k State} (hl : l.ColOK T c) (ht : t ≤ T) :
    val tm T x (wire x.length T t l c) =
      if t = 0 then initBit tm T c l
      else opVal (table tm l).1 (val tm T x ((table tm l).2.1.resolve x.length T t c))
        (val tm T x ((table tm l).2.2.resolve x.length T t c)) := by
  have hg : wire x.length T t l c - x.length < numGates k State T := by
    rw [wire_sub]
    have := Loc.offset_lt hl
    have : t * blockSize k State T + blockSize k State T ≤ (T + 1) * blockSize k State T := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    simp only [numGates]
    omega
  have hw : wire x.length T t l c = x.length + (wire x.length T t l c - x.length) := by
    simp only [wire]; omega
  rw [hw, val_add tm hg, gateCode_wire tm hl]
  by_cases ht0 : t = 0
  · have h : gateAt tm x.length T t c l = (.const (initBit tm T c l), []) := by
      simp [gateAt, ht0]
    rw [h]
    simp [ht0, interpretation]
  · have h : gateAt tm x.length T t c l = ((table tm l).1, argsOf (table tm l).1
        ((table tm l).2.1.resolve x.length T t c) ((table tm l).2.2.resolve x.length T t c)) := by
      simp [gateAt, ht0]
    rw [h, ite_eq_right ht0]
    exact interpretation_argsOf _ _ _ _

/-! ### The features of configurations -/

variable (T) in
/-- The value of a column feature in column `c` of a configuration: the input head at `c`, the
work heads and the work cells at `c - T`. -/
def colSem {input : List Bool} (cfg : Cfg k Bool State input) (c : ℕ) : ColFeat k → Bool
  | .inPos => decide (cfg.inputPos.val = c)
  | .head i => decide (cfg.workTapePos i = (c : ℤ) - T)
  | .cell i s => decide (cfg.workTapes i ((c : ℤ) - T) = s)

/-- The value of a global feature of a configuration. -/
def gfSem {input : List Bool} (cfg : Cfg k Bool State input) : GFeat State → Bool
  | .state q => decide (cfg.state = q)
  | .out o => decide (OutView.ofList cfg.output = o)

/-- Whether the action of the step from a configuration has the attribute `v`: never, once
halted. -/
private noncomputable def actSem {input : List Bool} (cfg : Cfg k Bool State input)
    (v : Attr k State) :
    Bool :=
  match cfg.state with
  | none => false
  | some q => v.test (tm.actionOf (cfg.situation q))

variable (T x) in
/-- **The invariant** at time `t`: the wire of every feature carries its value after `t` steps. -/
def Invariant (t : ℕ) : Prop :=
  (∀ f, val tm T x (wire (k := k) x.length T t (.gf f true 7) 0) =
    gfSem (tm.runFrom (tm.initCfg x) t) f) ∧
  ∀ c < numCols T, ∀ f, val tm T x (wire (State := State) x.length T t (.col f true 7) c) =
    colSem T (tm.runFrom (tm.initCfg x) t) c f

/-- The first block holds the initial configuration. -/
private theorem invariant_zero : Invariant tm T x 0 := by
  refine ⟨fun f => ?_, fun c hc f => ?_⟩
  · rw [val_wire tm (l := .gf f true 7) rfl (Nat.zero_le _)]
    rcases f with q | o <;> simp [initBit, gfInit, gfSem, runFrom, Cfg.init, eq_comm]
  · rw [val_wire tm (l := .col f true 7) hc (Nat.zero_le _)]
    rcases f with _ | i | ⟨i, s⟩ <;>
      simp only [↓reduceIte, initBit, Fin.isValue, decide_true, colInit, Bool.true_and, colSem,
        runFrom, MultiTapeNTM.initCfg, Cfg.init, Function.iterate_zero, id_eq,
        Fin.coe_ofNat_eq_mod, Nat.one_mod, eq_comm, decide_eq_decide]
    omega

/-! ### Values of references -/

private theorem val_resolve_fls {t c : ℕ} :
    val tm T x ((Ref.fls : Ref k State).resolve x.length T t c) = false := val_fls tm

private theorem val_resolve_tru {t c : ℕ} :
    val tm T x ((Ref.tru : Ref k State).resolve x.length T t c) = true := val_tru tm

/-- The input bit of column `c`, `false` at the columns holding no input bit. -/
private theorem val_resolve_inp {t c : ℕ} :
    val tm T x ((Ref.inp : Ref k State).resolve x.length T t c) =
      (inputAt x c).getD false := by
  simp only [Ref.resolve]
  split_ifs with h
  · rw [val_input tm (by omega)]
    simp [inputAt, show c ≠ 0 by omega, List.getElem?_eq_getElem (show c - 1 < x.length by omega)]
  · rw [val_fls]
    by_cases hc : c = 0
    · simp [inputAt, hc]
    · simp [inputAt, hc, List.getElem?_eq_none (show x.length ≤ c - 1 by omega)]

private theorem val_resolve_node {t c : ℕ} {p : Bool} {l : Loc k State} {cs : ColSel} {g : Guard} :
    val tm T x ((Ref.node p l cs g).resolve x.length T t c) =
      (g.test x.length T c && val tm T x (wire x.length T (if p then t - 1 else t) l
        (cs.apply T c))) := by
  by_cases h : g.test x.length T c = true
  · simp only [Ref.resolve, h, ↓reduceIte, Bool.true_and]
  · simp only [Bool.not_eq_true] at h
    simp only [Ref.resolve, h, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact val_fls tm

variable (T x) in
/-- The contribution of column `c` to a scanned quantity. -/
private def termSem (cfg : Cfg k Bool State x) (c : ℕ) : ScanQ k → Prop
  | .inRead s => cfg.inputPos.val = c ∧ inputAt x c = s
  | .read i s => cfg.workTapePos i = (c : ℤ) - T ∧ cfg.workTapes i ((c : ℤ) - T) = s

private theorem inputAt_eq_none {c : ℕ} (h : ¬(1 ≤ c ∧ c ≤ x.length)) : inputAt x c = none := by
  by_cases hc0 : c = 0
  · simp [inputAt, hc0]
  · simp [inputAt, hc0, List.getElem?_eq_none (show x.length ≤ c - 1 by omega)]

private theorem inputAt_eq_some {c : ℕ} (h : 1 ≤ c ∧ c ≤ x.length) :
    inputAt x c = some (x[c - 1]'(by omega)) := by
  simp [inputAt, show c ≠ 0 by omega, List.getElem?_eq_getElem (show c - 1 < x.length by omega)]

variable (x) in
/-- The symbol read by a head of a configuration. -/
private def readSem (cfg : Cfg k Bool State x) : ScanQ k → Prop
  | .inRead s => cfg.inputSymbol = s
  | .read i s => cfg.workTapeSymbols i = s

omit [DecidableEq State] in
private theorem wire_glob (n T t c : ℕ) (l : GlobLoc k State) :
    wire n T t (.glob l) c = wire n T t (.glob l) 0 := rfl

omit [DecidableEq State] in
private theorem sitOf_equivFin (y : Situation k State) :
    sitOf (Fintype.equivFin (Situation k State) y) = y :=
  (Fintype.equivFin (Situation k State)).symm_apply_apply y

variable (T x) in
/-- The value of a term of a feature, from block `t` and column `c`: both of its wires are true. -/
private noncomputable def termVal (t c : ℕ) (p : Ref k State × Ref k State) : Bool :=
  val tm T x (p.1.resolve x.length T t c) && val tm T x (p.2.resolve x.length T t c)

section Step

variable {t : ℕ} (hinv : Invariant tm T x t)
include hinv

/-- A column feature of the previous block. -/
private theorem val_colF {c : ℕ} {f : ColFeat k} {cs : ColSel} {g : Guard}
    (h : g.test x.length T c = true → cs.apply T c < numCols T) :
    val tm T x ((colF f cs g : Ref k State).resolve x.length T (t + 1) c) =
      (g.test x.length T c && colSem T (tm.runFrom (tm.initCfg x) t) (cs.apply T c) f) := by
  rw [colF, val_resolve_node]
  by_cases hg : g.test x.length T c = true
  · simp only [hg, Bool.true_and, ↓reduceIte, Nat.add_sub_cancel]
    exact hinv.2 _ (h hg) f
  · simp [hg]

/-- A global feature of the previous block. -/
private theorem val_gfF {c : ℕ} {f : GFeat State} :
    val tm T x ((gfF f : Ref k State).resolve x.length T (t + 1) c) =
      gfSem (tm.runFrom (tm.initCfg x) t) f := by
  rw [gfF, val_resolve_node]
  simp only [Guard.test, Bool.true_and, ↓reduceIte, Nat.add_sub_cancel]
  exact hinv.1 f

/-- A column feature of the previous block, in the same column. -/
private theorem val_colF_same {c : ℕ} (hc : c < numCols T) {f : ColFeat k} {g : Guard} :
    val tm T x ((colF f .same g : Ref k State).resolve x.length T (t + 1) c) =
      (g.test x.length T c && colSem T (tm.runFrom (tm.initCfg x) t) c f) :=
  val_colF tm hinv fun _ => hc

/-! ### The scan -/

/-- The negated work head of a column. -/
private theorem val_nh (htT : t + 1 ≤ T) {c : ℕ} (hc : c < numCols T) (i : Fin k) :
    val tm T x (wire (State := State) x.length T (t + 1) (.scan (.nh i)) c) =
      !colSem T (tm.runFrom (tm.initCfg x) t) c (.head i) := by
  rw [val_wire tm (l := .scan (.nh i)) hc htT]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal]
  rw [val_colF_same tm hinv hc]
  simp [Guard.test]

omit hinv in
/-- The negated input bit of a column. -/
private theorem val_nx (htT : t + 1 ≤ T) {c : ℕ} (hc : c < numCols T) :
    val tm T x (wire (State := State) x.length T (t + 1) (.scan (.nx : ScanLoc k)) c) =
      !(inputAt x c).getD false := by
  rw [val_wire tm (l := .scan .nx) hc htT]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal]
  rw [val_resolve_inp]

/-- The contribution of a column to a scanned quantity. -/
private theorem val_term (htT : t + 1 ≤ T) {c : ℕ} (hc : c < numCols T) (q : ScanQ k) :
    val tm T x (wire (State := State) x.length T (t + 1) (.scan (.term q)) c) = true ↔
      termSem T x (tm.runFrom (tm.initCfg x) t) c q := by
  rw [val_wire tm (l := .scan (.term q)) hc htT]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal]
  rcases q with (_ | (_ | _)) | ⟨i, s⟩
  · simp only [scanTerm]
    rw [val_colF_same tm hinv hc, val_resolve_tru]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    by_cases h : 1 ≤ c ∧ c ≤ x.length
    · simp [Guard.test, h, termSem, inputAt_eq_some h]
    · simp [Guard.test, h, termSem, inputAt_eq_none h, colSem]
  · simp only [scanTerm, scanAt]
    rw [val_colF_same tm hinv hc, val_resolve_node]
    simp only [Guard.test, Bool.false_eq_true, ↓reduceIte, Bool.true_and, ColSel.apply]
    rw [val_nx tm htT hc]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    by_cases h : 1 ≤ c ∧ c ≤ x.length
    · simp [h, termSem, inputAt_eq_some h, colSem]
    · simp [h, termSem, inputAt_eq_none h]
  · simp only [scanTerm]
    rw [val_colF_same tm hinv hc, val_resolve_inp]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    rcases hx : inputAt x c with _ | (_ | _) <;>
      simp [Guard.test, termSem, hx, colSem]
  · simp only [scanTerm]
    rw [val_colF_same tm hinv hc, val_colF_same tm hinv hc]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    simp [Guard.test, termSem, colSem]

/-- **The scan accumulates** the contributions of the columns so far. -/
private theorem val_acc (htT : t + 1 ≤ T) (q : ScanQ k) :
    ∀ c < numCols T, val tm T x (wire (State := State) x.length T (t + 1) (.scan (.acc q)) c) =
      true ↔ ∃ c' ≤ c, termSem T x (tm.runFrom (tm.initCfg x) t) c' q := by
  intro c hc
  induction c with
  | zero =>
    rw [val_wire tm (l := .scan (.acc q)) hc htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, scanAt]
    rw [val_resolve_node, val_resolve_node]
    simp only [Guard.test, Bool.true_and, ↓reduceIte, ColSel.apply, Bool.false_eq_true]
    simp only [show decide (1 ≤ 0) = false from rfl, Bool.false_and, Bool.false_or]
    rw [val_term tm hinv htT hc]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨c', hc', h⟩ => by
      obtain rfl : c' = 0 := by omega
      exact h⟩
  | succ c ih =>
    rw [val_wire tm (l := .scan (.acc q)) hc htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, scanAt]
    rw [val_resolve_node, val_resolve_node]
    simp only [Guard.test, Bool.false_eq_true, ↓reduceIte, Bool.true_and, ColSel.apply,
      Nat.add_sub_cancel, show 1 ≤ c + 1 by omega, decide_true, Bool.or_eq_true]
    rw [ih (by omega), val_term tm hinv htT hc]
    constructor
    · rintro (⟨c', hc', h⟩ | h)
      · exact ⟨c', by omega, h⟩
      · exact ⟨c + 1, le_rfl, h⟩
    · rintro ⟨c', hc', h⟩
      rcases Nat.lt_or_ge c' (c + 1) with h' | h'
      · exact Or.inl ⟨c', by omega, h⟩
      · obtain rfl : c' = c + 1 := by omega
        exact Or.inr h

/-- At the last column, the scan has found the symbols under the heads. -/
private theorem val_acc_last (hn : x.length < 2 * T) (htT : t + 1 ≤ T) (q : ScanQ k) :
    val tm T x (wire (State := State) x.length T (t + 1) (.scan (.acc q)) (2 * T)) = true ↔
      readSem x (tm.runFrom (tm.initCfg x) t) q := by
  rw [val_acc tm hinv htT q _ (by simp [numCols])]
  set cfg := tm.runFrom (tm.initCfg x) t
  rcases q with s | ⟨i, s⟩
  · simp only [termSem, readSem, Cfg.inputSymbol_eq_inputAt]
    have := cfg.inputPos.isLt
    constructor
    · rintro ⟨c', -, h, hs⟩
      rw [h, hs]
    · intro h
      exact ⟨cfg.inputPos.val, by omega, rfl, h⟩
  · simp only [termSem, readSem, Cfg.workTapeSymbols]
    have hb : |cfg.workTapePos i| ≤ t := abs_workTapePos_runFrom_le (tm := tm) x t i
    rw [abs_le] at hb
    constructor
    · rintro ⟨c', -, h, hs⟩
      rw [h, hs]
    · intro h
      refine ⟨(cfg.workTapePos i + T).toNat, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [show (((cfg.workTapePos i + T).toNat : ℕ) : ℤ) - T = cfg.workTapePos i by omega]
        exact h

/-! ### Situations and attributes -/

/-- The conjunction of the first conditions of a situation. -/
private theorem val_sit (hn : x.length < 2 * T) (htT : t + 1 ≤ T) (j : Fin (numSit k State))
    (i : Fin (k + 1)) :
    val tm T x (wire (k := k) x.length T (t + 1) (.glob (.sit j i)) 0) = true ↔
      (tm.runFrom (tm.initCfg x) t).state = some (sitOf j).1 ∧
        (tm.runFrom (tm.initCfg x) t).inputSymbol = (sitOf j).2.1 ∧
        ∀ i' : Fin k, i'.val < i.val →
          (tm.runFrom (tm.initCfg x) t).workTapeSymbols i' = (sitOf j).2.2 i' := by
  induction i using Fin.induction with
  | zero =>
    rw [val_wire tm (l := .glob (.sit j 0)) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_zero]
    rw [val_gfF tm hinv, scanAt, val_resolve_node, Bool.and_eq_true]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [val_acc_last tm hinv hn htT]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    simp [gfSem, readSem]
  | succ i ih =>
    rw [val_wire tm (l := .glob (.sit j i.succ)) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_succ]
    rw [val_resolve_node, scanAt, val_resolve_node]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply,
      Bool.and_eq_true]
    rw [ih, val_acc_last tm hinv hn htT]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    simp only [readSem, Fin.val_castSucc, Fin.val_succ, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun ⟨h₁, h₂⟩ i' hi' => ?_,
      fun h => ⟨fun i' hi' => h i' (by omega), h i (by omega)⟩⟩
    rcases Nat.lt_or_ge i'.val i.val with h | h
    · exact h₁ i' h
    · obtain rfl : i' = i := Fin.ext (by omega)
      exact h₂

/-- A situation holds exactly when its gate is true. -/
private theorem val_sit_last (hn : x.length < 2 * T) (htT : t + 1 ≤ T) (j : Fin (numSit k State)) :
    val tm T x (wire (k := k) x.length T (t + 1) (.glob (.sit j (Fin.last k))) 0) = true ↔
      (Feature.sit (sitOf j)).Holds (tm.runFrom (tm.initCfg x) t) := by
  rw [val_sit tm hinv hn htT, Feature.holds_sit_iff]
  simp only [Fin.val_last, Fin.is_lt, forall_const, Feature.holds_state, Feature.holds_inRead,
    Feature.holds_read]

/-- The disjunction of the first situations having an attribute. -/
private theorem val_attr (hn : x.length < 2 * T) (htT : t + 1 ≤ T) (v : Attr k State)
    (j : Fin (numSit k State + 1)) :
    val tm T x (wire (k := k) x.length T (t + 1) (.glob (.attr v j)) 0) = true ↔
      ∃ j' : Fin (numSit k State), j'.val < j.val ∧
        (Feature.sit (sitOf j')).Holds (tm.runFrom (tm.initCfg x) t) ∧
        v.test (tm.actionOf (sitOf j')) = true := by
  induction j using Fin.induction with
  | zero =>
    rw [val_wire tm (l := .glob (.attr v 0)) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_zero, val_resolve_fls,
      Bool.or_false, Bool.false_eq_true, Fin.val_zero, Nat.not_lt_zero, false_and, exists_false]
  | succ j ih =>
    rw [val_wire tm (l := .glob (.attr v j.succ)) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_succ]
    rw [val_resolve_node, Bool.or_eq_true]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [ih]
    split_ifs with hv
    · rw [val_resolve_node]
      simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
      rw [val_sit_last tm hinv hn htT]
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor
      · rintro (⟨j', hj', h⟩ | h)
        · exact ⟨j', by omega, h⟩
        · exact ⟨j, by omega, h, hv⟩
      · rintro ⟨j', hj', h⟩
        rcases Nat.lt_or_ge j'.val j.val with h' | h'
        · exact Or.inl ⟨j', h', h⟩
        · obtain rfl : j' = j := Fin.ext (by omega)
          exact Or.inr h.1
    · rw [val_resolve_fls]
      simp only [Bool.false_eq_true, or_false, Fin.val_castSucc, Fin.val_succ]
      constructor
      · rintro ⟨j', hj', h⟩
        exact ⟨j', by omega, h⟩
      · rintro ⟨j', hj', h⟩
        rcases Nat.lt_or_ge j'.val j.val with h' | h'
        · exact ⟨j', h', h⟩
        · obtain rfl : j' = j := Fin.ext (by omega)
          exact absurd h.2 hv

/-- **The attributes of the action** of the step. -/
private theorem val_act (hn : x.length < 2 * T) (htT : t + 1 ≤ T) {c : ℕ} (v : Attr k State) :
    val tm T x ((act v : Ref k State).resolve x.length T (t + 1) c) =
      actSem tm (tm.runFrom (tm.initCfg x) t) v := by
  rw [act, val_resolve_node]
  simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
  rw [wire_glob, Bool.eq_iff_iff, val_attr tm hinv hn htT]
  simp only [Fin.val_last, Fin.is_lt, true_and]
  generalize tm.runFrom (tm.initCfg x) t = cfg
  rcases hq : cfg.state with _ | q
  · simp [actSem, hq, Feature.not_holds_sit hq]
  · simp only [actSem, hq, Feature.holds_sit_iff_eq hq]
    constructor
    · rintro ⟨j', hj', h⟩
      rwa [hj'] at h
    · intro h
      exact ⟨Fintype.equivFin _ (cfg.situation q), sitOf_equivFin _, by
        rw [sitOf_equivFin]; exact h⟩

/-! ### The gadgets of the features -/

omit hinv in
private theorem val_gf_and (htT : t + 1 ≤ T) (f : GFeat State) (j : Fin 8) :
    val tm T x (wire (k := k) x.length T (t + 1) (.gf f false j) 0) =
      termVal tm T x (t + 1) 0 ((gfTerms f).getD j (.fls, .fls)) := by
  rw [val_wire tm (l := .gf f false j) rfl htT]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, termVal]

omit hinv in
private theorem val_gf_or (htT : t + 1 ≤ T) (f : GFeat State) (j : Fin 8) :
    val tm T x (wire (k := k) x.length T (t + 1) (.gf f true j) 0) = true ↔
      ∃ j' : Fin 8, j' ≤ j ∧
        termVal tm T x (t + 1) 0 ((gfTerms f).getD j' (.fls, .fls)) = true := by
  induction j using Fin.induction with
  | zero =>
    rw [val_wire tm (l := .gf f true 0) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_zero, val_resolve_fls,
      Bool.false_or]
    rw [val_resolve_node]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [val_gf_and tm htT]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨j', hj', h⟩ => by rwa [Fin.le_zero_iff.1 hj'] at h⟩
  | succ j ih =>
    rw [val_wire tm (l := .gf f true j.succ) rfl htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_succ]
    rw [val_resolve_node, val_resolve_node, Bool.or_eq_true]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [ih, val_gf_and tm htT]
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro (⟨j', hj', h⟩ | h)
      · exact ⟨j', by omega, h⟩
      · exact ⟨j.succ, by simp only [Fin.val_succ, le_refl], h⟩
    · rintro ⟨j', hj', h⟩
      rcases Nat.lt_or_ge j'.val (j.val + 1) with h' | h'
      · exact Or.inl ⟨j', by omega, h⟩
      · obtain rfl : j' = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
        exact Or.inr h

omit hinv in
private theorem val_col_and (htT : t + 1 ≤ T) {c : ℕ} (hc : c < numCols T)
    (f : ColFeat k) (j : Fin 8) :
    val tm T x (wire (State := State) x.length T (t + 1) (.col f false j) c) =
      termVal tm T x (t + 1) c ((colTerms f).getD j (.fls, .fls)) := by
  rw [val_wire tm (l := .col f false j) hc htT]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, termVal]

omit hinv in
private theorem val_col_or (htT : t + 1 ≤ T) {c : ℕ} (hc : c < numCols T)
    (f : ColFeat k) (j : Fin 8) :
    val tm T x (wire (State := State) x.length T (t + 1) (.col f true j) c) = true ↔
      ∃ j' : Fin 8, j' ≤ j ∧
        termVal tm T x (t + 1) c ((colTerms f).getD j' (.fls, .fls)) = true := by
  induction j using Fin.induction with
  | zero =>
    rw [val_wire tm (l := .col f true 0) hc htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_zero, val_resolve_fls,
      Bool.false_or]
    rw [val_resolve_node]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [val_col_and tm htT hc]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨j', hj', h⟩ => by rwa [Fin.le_zero_iff.1 hj'] at h⟩
  | succ j ih =>
    rw [val_wire tm (l := .col f true j.succ) hc htT]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, table, opVal, Fin.cases_succ]
    rw [val_resolve_node, val_resolve_node, Bool.or_eq_true]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    rw [ih, val_col_and tm htT hc]
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro (⟨j', hj', h⟩ | h)
      · exact ⟨j', by omega, h⟩
      · exact ⟨j.succ, by simp only [Fin.val_succ, le_refl], h⟩
    · rintro ⟨j', hj', h⟩
      rcases Nat.lt_or_ge j'.val (j.val + 1) with h' | h'
      · exact Or.inl ⟨j', by omega, h⟩
      · obtain rfl : j' = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
        exact Or.inr h

end Step

omit [DecidableEq State] in
private theorem length_gfTerms_le (f : GFeat State) :
    (gfTerms f : List (Ref k State × Ref k State)).length ≤ 8 := by
  rcases f with (_ | q) | (_ | b | _) <;> simp [gfTerms]

omit [DecidableEq State] in
private theorem length_colTerms_le (f : ColFeat k) :
    (colTerms f : List (Ref k State × Ref k State)).length ≤ 8 := by
  rcases f with _ | i | ⟨i, s⟩ <;> simp [colTerms]

omit [DecidableEq State] in
/-- A disjunction over the eight padded terms is a disjunction over the terms. -/
private theorem exists_getD_iff {L : List (Ref k State × Ref k State)} (hL : L.length ≤ 8)
    {P : Ref k State × Ref k State → Bool} (hd : P (.fls, .fls) = false) :
    (∃ j' : Fin 8, j' ≤ 7 ∧ P (L.getD j' (.fls, .fls)) = true) ↔ ∃ p ∈ L, P p = true := by
  constructor
  · rintro ⟨j', -, h⟩
    rcases List.getD_mem_or L j' (.fls, .fls) with hm | hm
    · exact ⟨_, hm, h⟩
    · rw [hm, hd] at h
      exact absurd h Bool.false_ne_true
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    exact ⟨⟨i, by omega⟩, by
      simp only [Fin.isValue, Fin.le_iff_val_le_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ]; omega,
      by rw [List.getD_eq_getElem _ _ hi]; exact h⟩

omit [Fintype State] in
/-- The two cases of a step: a halted configuration stays, and otherwise the action of the
situation is applied. -/
private theorem step_cases {input : List Bool} (cfg : Cfg k Bool State input) :
    (cfg.state = none ∧ tm.step cfg = cfg ∧ ∀ v, actSem tm cfg v = false) ∨
      ∃ q, cfg.state = some q ∧ tm.step cfg = (tm.actionOf (cfg.situation q)).apply cfg ∧
        ∀ v, actSem tm cfg v = v.test (tm.actionOf (cfg.situation q)) := by
  rcases hq : cfg.state with _ | q
  · exact Or.inl ⟨rfl, MultiTapeTM.step_of_halt hq, fun v => by simp [actSem, hq]⟩
  · exact Or.inr ⟨q, rfl, Feature.step_eq_apply tm hq, fun v => by simp [actSem, hq]⟩

/-! ### The step equations of the features -/

section Step

variable {t : ℕ} (hinv : Invariant tm T x t) (hn : x.length < 2 * T) (htT : t + 1 ≤ T)
include hinv hn htT

/-- **A global feature after the step.** -/
private theorem val_gf_step (f : GFeat State) :
    val tm T x (wire (k := k) x.length T (t + 1) (.gf f true 7) 0) =
      gfSem (tm.runFrom (tm.initCfg x) (t + 1)) f := by
  rw [Bool.eq_iff_iff, val_gf_or tm htT,
    exists_getD_iff (length_gfTerms_le f) (by simp [termVal, val_resolve_fls]), runFrom_succ]
  have hgf (g : GFeat State) := val_gfF (c := 0) tm hinv (f := g)
  have hact (v : Attr k State) := val_act (c := 0) tm hinv hn htT v
  rcases f with (_ | q) | (_ | b | _) <;>
  · simp only [gfTerms, List.exists_mem_cons_iff, List.not_mem_nil, false_and, exists_false,
      or_false, termVal, halted, hgf, hact, val_resolve_tru, Bool.and_eq_true]
    generalize tm.runFrom (tm.initCfg x) t = cfg
    rcases step_cases tm cfg with ⟨h0, -, ha⟩ | ⟨q', hq, hs, ha⟩
    · simp [ha, gfSem, h0]
    · rw [hs]
      simp only [ha, gfSem, hq, Attr.test, Action.apply_state, Action.apply_output,
        OutView.ofList_append_toList, decide_eq_true_eq]
      generalize (tm.actionOf (cfg.situation q')).output = e
      generalize OutView.ofList cfg.output = o
      generalize (tm.actionOf (cfg.situation q')).state = s
      rcases e with _ | (_ | _) <;> rcases o with _ | (_ | _) | _ <;>
        simp [OutView.push]

/-- **A column feature after the step.** -/
private theorem val_col_step {c : ℕ} (hc : c < numCols T) (f : ColFeat k) :
    val tm T x (wire (State := State) x.length T (t + 1) (.col f true 7) c) =
      colSem T (tm.runFrom (tm.initCfg x) (t + 1)) c f := by
  rw [Bool.eq_iff_iff, val_col_or tm htT hc,
    exists_getD_iff (length_colTerms_le f) (by simp [termVal, val_resolve_fls]), runFrom_succ]
  have hgf (g : GFeat State) := val_gfF (c := c) tm hinv (f := g)
  have hact (v : Attr k State) := val_act (c := c) tm hinv hn htT v
  have hS (g : ColFeat k) (gd : Guard) := val_colF_same tm hinv hc (f := g) (g := gd)
  have hP (g : ColFeat k) (gd : Guard) :
      val tm T x ((colF g .prev gd : Ref k State).resolve x.length T (t + 1) c) =
        (gd.test x.length T c && colSem T (tm.runFrom (tm.initCfg x) t) (c - 1) g) :=
    val_colF tm hinv (fun _ => by simp only [ColSel.apply]; omega)
  have hN (g : ColFeat k) :
      val tm T x ((colF g .next .ltLast : Ref k State).resolve x.length T (t + 1) c) =
        (Guard.ltLast.test x.length T c && colSem T (tm.runFrom (tm.initCfg x) t) (c + 1) g) :=
    val_colF tm hinv (fun h => by simpa [ColSel.apply, Guard.test] using h)
  have hnh (i : Fin k) : val tm T x ((scanAt (.nh i) .same .always : Ref k State).resolve
      x.length T (t + 1) c) = !colSem T (tm.runFrom (tm.initCfg x) t) c (.head i) := by
    rw [scanAt, val_resolve_node]
    simp only [Guard.test, Bool.true_and, Bool.false_eq_true, ↓reduceIte, ColSel.apply]
    exact val_nh tm hinv htT hc i
  have hpos := (tm.runFrom (tm.initCfg x) t).inputPos.isLt
  have hb (i : Fin k) := abs_workTapePos_runFrom_le (tm := tm) x t i
  simp only [numCols] at hc
  rcases f with _ | i | ⟨i, s⟩ <;>
    simp only [colTerms, List.exists_mem_cons_iff, List.not_mem_nil, false_and, exists_false,
      or_false, termVal, halted, hgf, hact, hS, hP, hN, hnh, Bool.and_eq_true] <;>
    generalize tm.runFrom (tm.initCfg x) t = cfg at hpos hb <;>
    rcases step_cases tm cfg with ⟨h0, hs, ha⟩ | ⟨q', hq, hs, ha⟩
  · simp [ha, h0, colSem, gfSem, Guard.test]
  · rw [hs]
    simp only [colSem, gfSem, decide_eq_true_iff]
    simp only [ha, hq, Attr.test, Action.apply_inputPos, Guard.test]
    have hmv := val_moveInputPos_eq cfg.inputPos (tm.actionOf (cfg.situation q')).inputTape
    generalize (tm.actionOf (cfg.situation q')).inputTape = m at hmv ⊢
    rcases m with _ | _ | _ <;> simp +decide only [SignType.zero_eq_zero, moveInputPos_zero,
      SignType.coe_zero, add_zero, Nat.cast_nonneg, sup_of_le_right, right_eq_inf, reduceCtorEq,
      true_and, false_and, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, numCols,
      Order.lt_add_one_iff, Order.add_one_le_iff, or_self, or_false, false_or,
      SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, Int.reduceNeg,
      SignType.pos_eq_one] at hmv ⊢ <;> omega
  · simp [ha, h0, colSem, gfSem, Guard.test]
  · rw [hs]
    simp only [colSem, gfSem, decide_eq_true_iff]
    simp only [ha, hq, Attr.test, Action.apply_workTapePos, Guard.test]
    have hbi := hb i
    rw [abs_le] at hbi
    generalize ((tm.actionOf (cfg.situation q')).workTapes i).2 = m
    rcases Nat.eq_zero_or_pos c with rfl | hc1
    · rcases m with _ | _ | _ <;> simp +decide only [reduceCtorEq, Nat.cast_zero,
        zero_sub, true_and, false_and, zero_tsub, and_self, zero_add, numCols, lt_add_iff_pos_left,
        Order.lt_two_iff, mul_pos_iff_of_pos_left, decide_eq_true_eq, Nat.cast_one, or_self,
        or_false, false_or, SignType.zero_eq_zero, SignType.coe_zero, add_zero,
        SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, Int.reduceNeg, and_false,
        SignType.pos_eq_one, false_iff, ne_eq] <;> omega
    · have hcast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by rw [Nat.cast_sub hc1, Nat.cast_one]
      rcases m with _ | _ | _ <;> simp +decide only [reduceCtorEq, true_and,
        false_and, decide_eq_true_eq, hcast, numCols, Order.lt_add_one_iff, Order.add_one_le_iff,
        Nat.cast_add, Nat.cast_one, or_self, or_false, false_or, SignType.zero_eq_zero,
        SignType.coe_zero, add_zero, SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one,
        Int.reduceNeg, SignType.pos_eq_one] <;> omega
  · simp [ha, h0, colSem, gfSem, Guard.test]
  · rw [hs]
    simp only [colSem, gfSem, decide_eq_true_iff]
    simp only [ha, hq, Attr.test, Action.apply_workTapes_eq_ite, Guard.test]
    generalize ((tm.actionOf (cfg.situation q')).workTapes i).1 = w
    by_cases hz : (c : ℤ) - T = cfg.workTapePos i
    · rcases w with _ | w <;> simp [hz]
    · simp [hz, Ne.symm hz]

/-- One step of the simulation: the invariant passes from block `t` to block `t + 1`. -/
private theorem invariant_succ : Invariant tm T x (t + 1) :=
  ⟨fun f => val_gf_step tm hinv hn htT f, fun _ hc f => val_col_step tm hinv hn htT hc f⟩

end Step

/-- **The tableau computes the run**: on an input of length `n < 2 T`, the wire of each feature at
time `t ≤ T` carries the value of that feature after `t` steps. -/
theorem invariant_le (hn : x.length < 2 * T) : ∀ t ≤ T, Invariant tm T x t := by
  intro t ht
  induction t with
  | zero => exact invariant_zero tm
  | succ t ih => exact invariant_succ tm (ih (by omega)) hn ht

/-- **The output wire of the tableau carries the answer**: on an input of length `n < 2 T`, it is
true exactly when the output written after `T` steps is `[true]`. -/
theorem evalOutput_gates (hn : x.length < 2 * T) :
    evalOutput x (gates tm x.length T) (outWire k State x.length T) =
      decide (OutView.ofList (tm.runFrom (tm.initCfg x) T).output = .one true) :=
  (invariant_le tm hn T le_rfl).1 (.out (.one true))

/-- The output wire of the tableau circuit. -/
private theorem toNat_outputs_circuit (n T : ℕ) :
    ((circuit tm n T).outputs 0).toNat = outWire k State n T := by
  have h := congrArg Prod.snd (code_circuit tm n T)
  simp only [Circuit.code] at h
  simpa using congrArg (fun l => l.headD 0) h

/-- **The tableau circuit outputs the answer**: on inputs `y` of length `n < 2 T`, it outputs
whether `tm`, started on `y`, has written exactly `[true]` after `T` steps. -/
theorem eval_circuit {n T : ℕ} (hn : n < 2 * T) (y : BitString n) :
    (circuit tm n T).eval interpretation y 0 =
      decide (OutView.ofList (tm.runFrom (tm.initCfg (List.ofFn y)) T).output = .one true) := by
  rw [Circuit.eval_eq_evalOutput, code_circuit, toNat_outputs_circuit]
  have h := evalOutput_gates tm (T := T) (x := List.ofFn y) (by simpa using hn)
  simp only [List.length_ofFn] at h
  exact h

end Boolean.Tableau

end Cslib.Circuits
