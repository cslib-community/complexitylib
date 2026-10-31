/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122; `try` steps
-- that the unused-tactic linter flags are dropped

public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Composition within small space

If `f` and `g` are computable within space `sf` and `sg`, then `g ∘ f` is computable within space
`O(sf a + sg (f a) + log |a| + log |f a|)`, without ever writing down `f a`: a multi-pass fold over
the input simulates the machine of `g` on descriptions, and whenever it needs the symbol of `f a`
under the input head of `g`, it simulates the machine of `f` from the start, reading `a` in place
and counting down its emitted symbols to the one needed.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`: composition within small space.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_logSpace`: logarithmic space is closed under
  composition.
* `Turing.MultiTapeTM.Universal.computableTidily_compose`: the composition, on descriptions, as a
  multi-pass fold.
-/

namespace Turing.MultiTapeTM

/-! ### Halting and space -/

section Halting

variable {k : ℕ} {State Symbol : Type*} {tm : MultiTapeTM k Symbol State}

/-- The output at the first halt is the computed output. -/
public lemma output_haltsAt {input output : List Symbol} {h : ℕ}
    (hc : tm.Computes input output) (hh : tm.HaltsAt (tm.initCfg input) h) :
    (tm.runFrom (tm.initCfg input) h).output = output := by
  obtain ⟨u, hu, rfl⟩ := hc
  rw [hh.runFrom_eq (hh.le_of_halted hu)]

/-- The first halt is no later than the time bound. -/
public lemma exists_haltsAt_of_runsInTime {input : List Symbol} {t : ℕ}
    (ht : tm.RunsInTime input t) : ∃ h ≤ t, tm.HaltsAt (tm.initCfg input) h :=
  exists_haltsAt (runsInTime_iff_halted.mp ht)

/-- The machine starts in a state, so it halts at a positive time. -/
public lemma haltsAt_pos {input : List Symbol} {h : ℕ} (hh : tm.HaltsAt (tm.initCfg input) h) :
    0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | h
  · exact absurd hh.halted (by simp [runFrom, MultiTapeNTM.initCfg, Cfg.Halted])
  · exact h

/-- A space bound bounds the space of every run. -/
public lemma RunsInSpace.space_le {input : List Symbol} {s : ℕ}
    (h : tm.RunsInSpace input s) (t : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s := by
  let p : tm.ComputationPath input :=
    { toRunPath :=
        { length := t
          toFun := fun i => tm.runFrom (tm.initCfg input) i
          step := fun i => by simp [step_iff, runFrom_succ] }
      head_eq := rfl }
  have := h p
  rwa [computationPath_space_eq_space] at this

end Halting

namespace Universal

/-! ### Reading bits in place -/

/-- The translator whose events are the bits. -/
@[expose] public def bitTr : Translator Unit Bool := ⟨(), fun _ b => ((), some b)⟩

lemma bitTr_run (q : Unit) (w : List Bool) : bitTr.run q w = ((), w) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    simp only [Translator.run]
    rw [ih]
    rfl

public lemma bitTr_events (w : List Bool) : bitTr.events w = w := by
  simp [Translator.events, bitTr_run]

/-- Bits as symbols. -/
@[expose] public def eBit : Bool ↪ ℕ :=
  ⟨Bool.toNat, fun a b h => by cases a <;> cases b <;> simp_all⟩

/-- A round of the countdown over bits: the countdown goes down, and at `1` the bit is read. -/
@[expose] public def bitScan (p : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (p.1 - 1, if p.1 = 1 then eBit b else p.2)

lemma bitScan_zero (l : List Bool) (cur : ℕ) : l.foldl bitScan (0, cur) = (0, cur) := by
  induction l with
  | nil => rfl
  | cons c l ih => simpa [bitScan] using ih

lemma bitScan_all (l : List Bool) (k cur : ℕ) (hk : 1 ≤ k) :
    l.foldl bitScan (k, cur) =
      (k - l.length, if k ≤ l.length then eBit (l.getD (k - 1) false) else cur) := by
  induction l generalizing k cur with
  | nil => simp; omega
  | cons b l ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hk'
    · simp [bitScan, bitScan_zero]
    · rw [List.foldl_cons, bitScan]
      simp only [show k ≠ 1 by omega, ↓reduceIte]
      rw [ih _ _ (by omega)]
      refine Prod.ext (by simp only [List.length_cons]; omega) ?_
      simp only [List.length_cons]
      split_ifs <;> try omega
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      simp

/-- **The countdown over bits finds the symbol under the input head.** -/
public lemma inputSymbol_bitScan (w : List Bool) (p : ℕ) :
    inputSymbol (w.map eBit) p =
      if p = 0 ∨ (w.foldl bitScan (p, 0)).1 ≠ 0 then none else some (w.foldl bitScan (p, 0)).2 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [inputSymbol]
  rw [bitScan_all w p 0 hp]
  simp only [inputSymbol, hp.ne', false_or, ne_eq]
  rcases Nat.lt_or_ge (p - 1) w.length with h | h
  · simp [Nat.sub_eq_zero_iff_le.mpr (by omega : p ≤ w.length), List.head?_drop, h]
    omega
  · simp [show p - w.length ≠ 0 by omega]
    omega

/-- Along the bits, the countdown does not go up and the bit read is a bit. -/
public lemma bitScan_le (l : List Bool) (k cur : ℕ) (hcur : cur ≤ 1) :
    (l.foldl bitScan (k, cur)).1 ≤ k ∧ (l.foldl bitScan (k, cur)).2 ≤ 1 := by
  induction l generalizing k cur with
  | nil => exact ⟨le_rfl, hcur⟩
  | cons b l ih =>
    have := ih (k - 1) (if k = 1 then eBit b else cur) (by
      split_ifs
      · cases b <;> decide
      · exact hcur)
    exact ⟨this.1.trans (by omega), this.2⟩

/-! ### Counting down emitted symbols -/

/-- A round of the countdown over emitted symbols: nothing, or the events of a symbol. -/
@[expose] public def emitScan (p : ℕ × ℕ) (o : Option ℕ) : ℕ × ℕ :=
  o.elim p fun n => (tok n).foldl scan p

public lemma emitScan_some (p : ℕ × ℕ) (n : ℕ) :
    emitScan p (some n) = (p.1 - 1, if p.1 = 1 then p.2 + n else p.2) :=
  scan_tok p.1 p.2 n

/-- The countdown over emitted symbols is the countdown over their events. -/
public lemma foldl_emitScan (l : List (Option ℕ)) (p : ℕ × ℕ) :
    l.foldl emitScan p = (events (l.map Option.toList).flatten).foldl scan p := by
  induction l generalizing p with
  | nil => rfl
  | cons o l ih => cases o <;> simp [emitScan, ih, events]

/-- Along symbols that are bits, the countdown does not go up and the symbol read is a bit. -/
public lemma emitScan_le (l : List (Option ℕ)) (hl : ∀ o ∈ l, o.getD 0 ≤ 1) (k cur : ℕ)
    (hcur : cur ≤ 1) (hk : 1 ≤ k → cur = 0) :
    (l.foldl emitScan (k, cur)).1 ≤ k ∧ (l.foldl emitScan (k, cur)).2 ≤ 1 := by
  induction l generalizing k cur with
  | nil => exact ⟨le_rfl, hcur⟩
  | cons o l ih =>
    cases o with
    | none => exact ih (fun o ho => hl o (List.mem_cons_of_mem _ ho)) k cur hcur hk
    | some n =>
      have hn : n ≤ 1 := hl (some n) (by simp)
      rw [List.foldl_cons, emitScan_some]
      have := ih (fun o ho => hl o (List.mem_cons_of_mem _ ho)) (k - 1)
        (if k = 1 then cur + n else cur) (by split_ifs <;> omega) (by split_ifs <;> omega)
      exact ⟨this.1.trans (by omega), this.2⟩

/-! ### The control of the composition -/

/-- The control state: the description and configuration of the outer machine `g` and of the
inner machine `f`, and the countdown over the symbols emitted by `f` to the one under the input
head of `g`. -/
public abbrev Ctl := ((Desc × SCfg) × (Desc × SCfg)) × (ℕ × ℕ)

/-- The symbol under the input head of `g`, once `f` has halted. -/
@[expose] public def gSym (c : Ctl) : Option ℕ :=
  if c.1.1.2.inputPos = 0 ∨ c.2.1 ≠ 0 then none else some c.2.2

/-- A step of the composition, with `sym` under the input head of `f`: a step of `f`, counting
down its emitted symbol, or, once `f` has halted, a step of `g`, restarting `f`. -/
@[expose] public def cstep (c : Ctl) (sym : Option ℕ) : Ctl :=
  if c.1.2.2.state.isNone then
    (((c.1.1.1, (stepWith c.1.1.1 c.1.1.2 (gSym c)).1), (c.1.2.1, init c.1.2.1)),
      ((stepWith c.1.1.1 c.1.1.2 (gSym c)).1.inputPos, 0))
  else
    ((c.1.1, (c.1.2.1, (stepWith c.1.2.1 c.1.2.2 sym).1)),
      emitScan c.2 (stepWith c.1.2.1 c.1.2.2 sym).2)

/-- A bit as a symbol, decoded. -/
@[expose] public def decodeBit (o : Option ℕ) : List Bool := o.elim [] fun n => [decide (n ≠ 0)]

/-- What a step of the composition emits: the bit emitted by `g`, if any. -/
@[expose] public def gEmit (c : Ctl) : List Bool :=
  if c.1.2.2.state.isNone then decodeBit (stepWith c.1.1.1 c.1.1.2 (gSym c)).2 else []

/-- The initial control state. -/
@[expose] public def ctl₀ (dg df : Desc) : Ctl := (((dg, init dg), (df, init df)), (1, 0))

section Semantics

variable (dg df : Desc) (x y : List ℕ) (uf : ℕ)

/-- The countdown over the symbols that `f` emits in its first `r` steps. -/
@[expose] public def emitCount (p r : ℕ) : ℕ × ℕ :=
  ((List.range r).map fun j => (step df x (run df x j)).2).foldl emitScan (p, 0)

/-- Once `f` has halted, the countdown has found the symbol of its output under the input head
of `g`. -/
lemma gSym_halted
    (hy : ((List.range uf).map fun j => (step df x (run df x j)).2.toList).flatten = y)
    (cg cf : SCfg) :
    gSym (((dg, cg), (df, cf)), emitCount df x cg.inputPos uf) = inputSymbol y cg.inputPos := by
  rw [inputSymbol_scan, gSym, emitCount, foldl_emitScan, List.map_map]
  simp only [Function.comp_def, hy]
  rfl

/-- **The composition after `q` steps of `g` and `r ≤ uf` steps of `f`**, where `f` halts after
`uf` steps with the output `y`. -/
public theorem iterate_cstep (hhalt : ∀ r, (run df x r).state = none ↔ uf ≤ r)
    (hy : ((List.range uf).map fun j => (step df x (run df x j)).2.toList).flatten = y) (q r : ℕ)
    (hr : r ≤ uf) : (fun c => cstep c (inputSymbol x c.1.2.2.inputPos))^[q * (uf + 1) + r]
      (ctl₀ dg df) = (((dg, run dg y q), (df, run df x r)),
        emitCount df x ((run dg y q).inputPos) r) := by
  set G := fun c : Ctl => cstep c (inputSymbol x c.1.2.2.inputPos)
  have hinner (q : ℕ) (h₀ : G^[q * (uf + 1)] (ctl₀ dg df) =
      (((dg, run dg y q), (df, run df x 0)), emitCount df x ((run dg y q).inputPos) 0)) :
      ∀ r ≤ uf, G^[q * (uf + 1) + r] (ctl₀ dg df) =
        (((dg, run dg y q), (df, run df x r)), emitCount df x ((run dg y q).inputPos) r) := by
    intro r hr
    induction r with
    | zero => exact h₀
    | succ r ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega)]
      have hnh : (run df x r).state.isNone = false := by
        rw [Bool.eq_false_iff, ne_eq, Option.isNone_iff_eq_none, hhalt]
        omega
      simp only [G, cstep, hnh, Bool.false_eq_true, ↓reduceIte, ← step_eq_stepWith, run_succ']
      simp [emitCount, List.range_succ]
  induction q generalizing r with
  | zero => exact hinner 0 (by rw [Nat.zero_mul]; rfl) r hr
  | succ q ih =>
    refine hinner (q + 1) ?_ r hr
    have h := ih uf le_rfl
    rw [show (q + 1) * (uf + 1) = q * (uf + 1) + uf + 1 by ring, Function.iterate_succ_apply', h]
    have hh : (run df x uf).state.isNone = true := by
      simpa [Option.isNone_iff_eq_none] using (hhalt uf).mpr le_rfl
    simp only [G, cstep, hh, ↓reduceIte, gSym_halted dg df x y uf hy, ← step_eq_stepWith, run_succ']
    rfl

/-- What the composition emits after `q` steps of `g` and `r ≤ uf` steps of `f`: the bit `g`
emits, once `f` has halted. -/
public theorem gEmit_iterate (hhalt : ∀ r, (run df x r).state = none ↔ uf ≤ r)
    (hy : ((List.range uf).map fun j => (step df x (run df x j)).2.toList).flatten = y) (q r : ℕ)
    (hr : r ≤ uf) :
    gEmit ((fun c => cstep c (inputSymbol x c.1.2.2.inputPos))^[q * (uf + 1) + r] (ctl₀ dg df)) =
      if r = uf then decodeBit (step dg y (run dg y q)).2 else [] := by
  rw [iterate_cstep dg df x y uf hhalt hy q r hr, gEmit]
  have hh : (run df x r).state.isNone = true ↔ r = uf := by
    rw [Option.isNone_iff_eq_none, hhalt]
    omega
  by_cases h : r = uf
  · subst h
    simp only [hh, ↓reduceIte, gSym_halted dg df x y r hy, ← step_eq_stepWith]
  · simp only [hh, h, ↓reduceIte]

/-- **The output of the composition** after `ug` steps of `g`: the bits `g` emits. -/
public theorem flatten_gEmit (hhalt : ∀ r, (run df x r).state = none ↔ uf ≤ r)
    (hy : ((List.range uf).map fun j => (step df x (run df x j)).2.toList).flatten = y) (ug : ℕ) :
    ((List.range (ug * (uf + 1))).map fun i =>
      gEmit ((fun c => cstep c (inputSymbol x c.1.2.2.inputPos))^[i] (ctl₀ dg df))).flatten =
      (simulate dg y ug).1.map (fun n => decide (n ≠ 0)) := by
  rw [simulate_eq, List.map_flatten, List.map_map]
  induction ug with
  | zero => simp
  | succ ug ih =>
    rw [show (ug + 1) * (uf + 1) = ug * (uf + 1) + (uf + 1) by ring, List.range_add,
      List.map_append, List.flatten_append, ih, List.range_succ (n := ug), List.map_append,
      List.flatten_append, List.map_map]
    congr 1
    rw [List.range_succ, List.map_append, List.flatten_append]
    have hz : ((List.range uf).map ((fun i => gEmit ((fun c => cstep c
        (inputSymbol x c.1.2.2.inputPos))^[i] (ctl₀ dg df))) ∘ (ug * (uf + 1) + ·))).flatten = [] :=
      List.flatten_eq_nil_iff.mpr fun l hl => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        rw [Function.comp_apply, gEmit_iterate dg df x y uf hhalt hy ug r
          (List.mem_range.mp hr).le]
        simp [(List.mem_range.mp hr).ne]
    rw [hz, List.nil_append]
    simp only [List.map_cons, List.map_nil, Function.comp_apply, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [gEmit_iterate dg df x y uf hhalt hy ug uf le_rfl]
    simp only [↓reduceIte, decodeBit]
    cases (step dg y (run dg y ug)).2 <;> rfl

end Semantics

/-! ### The fold -/

/-- The state of the fold: the control state, and the countdown over the input of `f`. -/
public abbrev CSt := Ctl × (ℕ × ℕ)

/-- A round: one bit of the countdown. -/
@[expose] public def cNext (p : CSt × Bool) : CSt := (p.1.1, bitScan p.1.2 p.2)

/-- The symbol under the input head of `f`, at the end of a pass. -/
@[expose] public def xSym (s : CSt) : Option ℕ :=
  if s.1.1.2.2.inputPos = 0 ∨ s.2.1 ≠ 0 then none else some s.2.2

/-- The end of a pass: a step of the composition, and the countdown reset to the new input head
of `f`. -/
@[expose] public def cEnd (s : CSt) : CSt :=
  (cstep s.1 (xSym s), ((cstep s.1 (xSym s)).1.2.2.inputPos, 0))

/-- The initial state. -/
@[expose] public def cInit (dg df : Desc) : CSt := (ctl₀ dg df, (1, 0))

lemma streamState_cNext (s : CSt) (l : List Bool) (j : ℕ) :
    streamState s cNext l j = (s.1, (l.take j).foldl bitScan s.2) :=
  List.foldl_hom (fun a => (s.1, a)) (fun _ _ => rfl)

/-- **The passes** are the steps of the composition. -/
public theorem passState_cInit (dg df : Desc) (w : List Bool) (i : ℕ) :
    passState (cInit dg df) cNext cEnd w i =
      ((fun c => cstep c (inputSymbol (w.map eBit) c.1.2.2.inputPos))^[i] (ctl₀ dg df),
        (((fun c => cstep c (inputSymbol (w.map eBit) c.1.2.2.inputPos))^[i]
          (ctl₀ dg df)).1.2.2.inputPos, 0)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [passState, ih, streamState_cNext, List.take_length, cEnd, Function.iterate_succ_apply']
    have : xSym (((fun c => cstep c (inputSymbol (w.map eBit) c.1.2.2.inputPos))^[i]
        (ctl₀ dg df)), w.foldl bitScan ((((fun c => cstep c (inputSymbol (w.map eBit)
          c.1.2.2.inputPos))^[i] (ctl₀ dg df)).1.2.2.inputPos, 0))) =
        inputSymbol (w.map eBit) (((fun c => cstep c (inputSymbol (w.map eBit)
          c.1.2.2.inputPos))^[i] (ctl₀ dg df)).1.2.2.inputPos) := by
      rw [inputSymbol_bitScan]
      rfl
    rw [this]

/-! ### The parts of the fold, within bounds in the length of the state -/

/-- The encoding of control states. -/
public abbrev eCtl : Ctl ↪ List Bool :=
  encPair (encPair (encPair eDesc eCfg) (encPair eDesc eCfg)) (encPair encNat encUnary)

/-- The encoding of states of the fold. -/
public abbrev eCSt : CSt ↪ List Bool := encPair eCtl (encPair encNat encUnary)

open ComputableTidilyInO

/-- The input position of a configuration computed within bounds. -/
lemma inputPos_inO {α : Type} {enc : α ↪ List Bool} {c : α → SCfg} {T S : α → ℕ}
    (h : ComputableTidilyInO c enc eCfg T S) :
    ComputableTidilyInO (fun a => (c a).inputPos) enc encNat T S :=
  (h.of_enc_eq (encOut := eCfgFields)
    (g := fun a => ((c a).state, (c a).inputPos, (c a).workTapes)) fun _ => rfl).snd'.fst'

/-- Whether a configuration computed within bounds has halted. -/
lemma halted_inO {α : Type} {enc : α ↪ List Bool} {c : α → SCfg} {T S : α → ℕ}
    (h : ComputableTidilyInO c enc eCfg T S) :
    ComputableTidilyInO (fun a => (c a).state.isNone) enc encBool T S :=
  ((ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    fun b : Bool => !b).inO_one.comp_linear
      ((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear
        -- bridge for #862: tidy client of the plain `state_inO`
        (state_inO.tidy.comp_linear h))).of_enc_eq fun a => by
        simp only [Function.comp_apply]
        cases (c a).state <;> rfl

/-- The symbol under a countdown, from the input position and the countdown. -/
lemma countSym_inO {α : Type} {enc : α ↪ List Bool} {p k cur : α → ℕ} {T S : α → ℕ}
    (hp : ComputableTidilyInO p enc encNat T S) (hk : ComputableTidilyInO k enc encNat T S)
    (hcur : ComputableTidilyInO cur enc encUnary T S) :
    ComputableTidilyInO (fun a => if p a = 0 ∨ k a ≠ 0 then none else some (cur a)) enc eSym
      (fun a => T a + (enc a).length) fun a => S a + (enc a).length := by
  have hor := (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun b : Bool × Bool => b.1 || !b.2).inO_one.comp_linear
      ((ComputableInO.natIsZero.tidy.comp_linear hp).prod
        (ComputableInO.natIsZero.tidy.comp_linear hk))
  refine (((hor.ite (const none) ((ComputableTidilyInDegree.optionSome (enc₁ := encUnary)
    (enc := eSym)).inO_one.comp_linear hcur)).of_enc_eq fun a => ?_)).mono 4 (fun a => ?_)
    fun a => ?_
  · simp only [Function.comp_apply]
    split_ifs <;> simp_all
  all_goals
    simp only [Function.comp_apply]
    split_ifs <;> omega

/-- The time of a step, in the length of its context. -/
public lemma wTime_le' (c : WCtx) : wTime c ≤ 2 * ((eWCtx c).length + 1) ^ 3 := by
  have ht := length_le_length_encList eTape c.1.2.workTapes
  have hd := length_le_length_encList (encPair eKey eAct) c.1.1.table
  have hl : c.1.2.workTapes.length + c.1.1.table.length + 1 ≤ (eWCtx c).length + 1 := by
    simp only [length_encPair, eCfg_apply, eDesc_apply] at ht hd ⊢
    omega
  have hdesc : (eDesc c.1.1).length + 1 ≤ (eWCtx c).length + 1 := by
    simp only [length_encPair]
    omega
  have hpos : (encNat c.1.2.inputPos).length + 1 ≤ (eWCtx c).length + 1 := by
    simp only [length_encPair, eCfg_apply]
    omega
  have hproduct := Nat.mul_le_mul_right ((eWCtx c).length + 1) (Nat.mul_le_mul hl hdesc)
  have hdigits := Nat.pow_le_pow_left hpos 2
  have hsquare : ((eWCtx c).length + 1) ^ 2 ≤ ((eWCtx c).length + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  unfold wTime
  calc _ ≤ ((eWCtx c).length + 1) * ((eWCtx c).length + 1) * ((eWCtx c).length + 1) +
          ((eWCtx c).length + 1) ^ 2 := Nat.add_le_add hproduct hdigits
    _ = ((eWCtx c).length + 1) ^ 3 + ((eWCtx c).length + 1) ^ 2 := by ring
    _ ≤ 2 * ((eWCtx c).length + 1) ^ 3 := by omega

/-- A step of `g`, with the symbol found by the countdown. -/
public lemma stepG_inO :
    ComputableTidilyInO (fun s : CSt => stepWith s.1.1.1.1 s.1.1.1.2 (gSym s.1))
    eCSt (encPair eCfg eSym) (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hc := fst eCtl (encPair encNat encUnary)
  have hg := hc.fst'.fst'
  have hsym := countSym_inO (inputPos_inO hg.snd') hc.snd'.fst' hc.snd'.snd'
  -- bridge for #862: tidy client of the plain `stepWith_inO`
  refine (stepWith_inO.tidy.comp (hg.prod (hsym.of_enc_eq (g := fun s : CSt => gSym s.1)
    fun _ => rfl))).mono 100 (fun s => ?_) fun s => ?_
  all_goals
    have hw := wTime_le' (s.1.1.1, gSym s.1)
    have hctx : (eWCtx (s.1.1.1, gSym s.1)).length ≤ (eCSt s).length + 1 := by
      have : (eSym (gSym s.1)).length ≤ s.1.2.2 + 1 := by
        unfold gSym
        split_ifs <;> simp
      simp only [length_encPair, encUnary_apply, List.length_replicate] at this ⊢
      omega
    have hcube := Nat.pow_le_pow_left (Nat.add_le_add_right hctx 1) 3
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h8 : ((eCSt s).length + 1 + 1) ^ 3 ≤ 8 * ((eCSt s).length + 1) ^ 3 := by
      have := Nat.pow_le_pow_left
        (show (eCSt s).length + 1 + 1 ≤ 2 * ((eCSt s).length + 1) by omega) 3
      rw [Nat.mul_pow] at this
      omega
    dsimp only [eCSt] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    omega

/-- A step of `f`, with the symbol found by the countdown over the input. -/
public lemma stepF_inO : ComputableTidilyInO (fun s : CSt => stepWith s.1.1.2.1 s.1.1.2.2 (xSym s))
    eCSt (encPair eCfg eSym) (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hc := fst eCtl (encPair encNat encUnary)
  have hn := snd eCtl (encPair encNat encUnary)
  have hg := hc.fst'.snd'
  have hsym := countSym_inO (inputPos_inO hg.snd') hn.fst' hn.snd'
  -- bridge for #862: tidy client of the plain `stepWith_inO`
  refine (stepWith_inO.tidy.comp (hg.prod (hsym.of_enc_eq (g := xSym)
    fun _ => rfl))).mono 100 (fun s => ?_) fun s => ?_
  all_goals
    have hw := wTime_le' (s.1.1.2, xSym s)
    have hctx : (eWCtx (s.1.1.2, xSym s)).length ≤ (eCSt s).length + 1 := by
      have : (eSym (xSym s)).length ≤ s.2.2 + 1 := by
        unfold xSym
        split_ifs <;> simp
      simp only [length_encPair, encUnary_apply, List.length_replicate] at this ⊢
      omega
    have hcube := Nat.pow_le_pow_left (Nat.add_le_add_right hctx 1) 3
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h8 : ((eCSt s).length + 1 + 1) ^ 3 ≤ 8 * ((eCSt s).length + 1) ^ 3 := by
      have := Nat.pow_le_pow_left
        (show (eCSt s).length + 1 + 1 ≤ 2 * ((eCSt s).length + 1) by omega) 3
      rw [Nat.mul_pow] at this
      omega
    dsimp only [eCSt] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    omega

/-- The `g` branch of a step of the composition: a step of `g`, restarting `f`. -/
lemma gBranch_inO : ComputableTidilyInO (fun s : CSt =>
    (((s.1.1.1.1, (stepWith s.1.1.1.1 s.1.1.1.2 (gSym s.1)).1), (s.1.1.2.1, init s.1.1.2.1)),
      ((stepWith s.1.1.1.1 s.1.1.1.2 (gSym s.1)).1.inputPos, 0))) eCSt eCtl
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hc := fst eCtl (encPair encNat encUnary)
  have hdf := hc.fst'.snd'.fst'
  have hcg := stepG_inO.fst'
  refine (((hc.fst'.fst'.fst'.prod hcg).prod (hdf.prod (init_inO.comp hdf))).prod
    ((inputPos_inO hcg).prod (const (encMid := encUnary) 0))).mono 100 (fun s => ?_) fun s => ?_
  all_goals
    have hd : (eDesc s.1.1.2.1).length ≤ (eCSt s).length := by
      simp only [length_encPair]
      omega
    have h₁ := Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
    have h₂ : ((eCSt s).length + 1) ^ 2 ≤ ((eCSt s).length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eCSt] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    omega

lemma emitScan_eq (p : ℕ × ℕ) (o : Option ℕ) : emitScan p o =
    if o.isSome then (p.1 - 1, if p.1 = 1 then p.2 + o.getD 0 else p.2) else p := by
  cases o
  · rfl
  · simp [emitScan_some]

/-- The `f` branch of a step of the composition: a step of `f`, counting down its emitted
symbol. -/
lemma fBranch_inO : ComputableTidilyInO (fun s : CSt =>
    ((s.1.1.1, (s.1.1.2.1, (stepWith s.1.1.2.1 s.1.1.2.2 (xSym s)).1)),
      emitScan s.1.2 (stepWith s.1.1.2.1 s.1.1.2.2 (xSym s)).2)) eCSt eCtl
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hc := fst eCtl (encPair encNat encUnary)
  have ho := stepF_inO.snd'
  have hk := hc.snd'.fst'
  have hcur := hc.snd'.snd'
  have hsome := (ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear ho
  have hn := (ComputableTidilyInDegree.getD (enc₁ := encUnary) (enc := eSym) 0).inO_one.comp_linear
    ho
  have hk1 := (ComputableInO.eq encNat).tidy.comp (hk.prod (const (encMid := encNat) 1))
  have hsum := ComputableTidilyInO.append (g := fun s : CSt => s.1.2.2 +
    (stepWith s.1.1.2.1 s.1.1.2.2 (xSym s)).2.getD 0) (encOut := encUnary) hcur hn
    fun s => by simp
  have hnew := hsome.ite ((ComputableInO.natPred.tidy.comp hk).prod (hk1.ite hsum hcur))
    (hk.prod hcur)
  refine ((((hc.fst'.fst').prod (hc.fst'.snd'.fst'.prod stepF_inO.fst')).prod hnew).of_enc_eq
    fun s => ?_).mono 100 (fun s => ?_) fun s => ?_
  · simp only [Function.comp_apply, emitScan_eq]
    split_ifs <;> simp_all
  all_goals
    have hkL : (encNat s.1.2.1).length ≤ (eCSt s).length := by
      simp only [length_encPair]
      omega
    have h1 : (encNat 1).length = 1 := rfl
    have h₁ := Nat.pow_le_pow_left (Nat.add_le_add_right hkL 1) 2
    have h₂ : ((eCSt s).length + 1) ^ 2 ≤ ((eCSt s).length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have hm : ((encNat s.1.2.1).length + 1) * ((encNat s.1.2.1).length + 1 + 1) ≤
        2 * ((eCSt s).length + 1) ^ 3 := by
      have := Nat.mul_le_mul (Nat.add_le_add_right hkL 1)
        (show (encNat s.1.2.1).length + 1 + 1 ≤ 2 * ((eCSt s).length + 1) by omega)
      have h₃ : ((eCSt s).length + 1) * (2 * ((eCSt s).length + 1)) =
          2 * ((eCSt s).length + 1) ^ 2 := by ring
      omega
    have hp : (encPair encNat encNat (s.1.2.1, 1)).length = 2 * (encNat s.1.2.1).length + 2 := by
      simp only [length_encPair, h1]
    dsimp only [eCSt] at *
    rw [hp] at *
    try simp only [h1] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    generalize (L + 1) ^ 2 = B at *
    generalize ((encNat s.1.2.1).length + 1) ^ 2 = A at *
    generalize ((encNat s.1.2.1).length + 1) * ((encNat s.1.2.1).length + 1 + 1) = P at *
    split_ifs <;> omega

/-- A step of the composition at the end of a pass. -/
lemma cstep_inO : ComputableTidilyInO (fun s : CSt => cstep s.1 (xSym s)) eCSt eCtl
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hcf := (fst eCtl (encPair encNat encUnary)).fst'.snd'.snd'
  refine (((halted_inO hcf).ite gBranch_inO fBranch_inO).of_enc_eq (g := fun s : CSt =>
    cstep s.1 (xSym s)) fun s => ?_).mono 3 (fun s => ?_) fun s => ?_
  · simp only [cstep]
  all_goals
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eCSt] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    split_ifs <;> omega

/-- **The end of a pass.** -/
public lemma cEnd_inO : ComputableTidilyInO cEnd eCSt eCSt
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 :=
  (cstep_inO.prod ((inputPos_inO cstep_inO.fst'.snd'.snd').prod
    (const (encMid := encUnary) 0))).mono 3 (fun s => by
      have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      omega) fun s => by omega

/-- **What a pass emits.** -/
public lemma cEmit_inO : ComputableTidilyInO (fun s : CSt => gEmit s.1) eCSt encBits
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 := by
  have hcf := (fst eCtl (encPair encNat encUnary)).fst'.snd'.snd'
  have ho := stepG_inO.snd'
  have hsome := (ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear ho
  have hn := (ComputableTidilyInDegree.getD (enc₁ := encUnary) (enc := eSym) 0).inO_one.comp_linear
    ho
  have hz : ComputableTidilyInO (fun n => decide (n ≠ 0)) encUnary encBool
      (fun n => (encUnary n).length) fun n => (encUnary n).length :=
    ((ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
      fun b : Bool => !b).inO_one.comp_linear (of_linear (.of_isEmpty (f := fun n => decide (n = 0))
        fun n => by cases n <;> simp))).of_enc_eq fun n => by simp
  have hb := (hz.comp_linear hn).of_enc_eq (encOut := encBits) (g := fun s : CSt =>
      [decide ((stepWith s.1.1.1.1 s.1.1.1.2 (gSym s.1)).2.getD 0 ≠ 0)]) fun _ => rfl
  refine (((halted_inO hcf).ite (hsome.ite hb (const [])) (const [])).of_enc_eq
    fun s => ?_).mono 100 (fun s => ?_) fun s => ?_
  · simp only [gEmit, decodeBit, Function.comp_apply]
    split_ifs <;> simp_all
    cases h : (stepWith s.1.1.1.1 s.1.1.1.2 (gSym s.1)).2 <;> simp_all
  all_goals
    have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    dsimp only [eCSt] at *
    generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
    generalize (L + 1) ^ 3 = Y at *
    split_ifs <;> omega

/-- Whether another pass follows: `g` has not halted. -/
public lemma cCont_inO : ComputableTidilyInO (fun s : CSt => s.1.1.1.2.state.isSome) eCSt encBool
    (fun s => ((eCSt s).length + 1) ^ 3) fun s => (eCSt s).length + 1 :=
  (((ComputableTidilyInDegree.isSome encUnary).inO_one.comp_linear
    -- bridge for #862: tidy client of the plain `state_inO`
    (state_inO.tidy.comp_linear (fst eCtl (encPair encNat encUnary)).fst'.fst'.snd'))).mono 1
    (fun s => by
      have hL : (eCSt s).length + 1 ≤ ((eCSt s).length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      dsimp only [eCSt] at *
      generalize ((encPair eCtl (encPair encNat encUnary)) s).length = L at *
      generalize (L + 1) ^ 3 = Y at *
      omega) fun s => by dsimp only [eCSt]; omega

/-- **A round**: one bit of the countdown over the input. -/
public lemma cNext_inO : ComputableTidilyInO cNext (encPair eCSt encBool) eCSt
    (fun p => ((encPair eCSt encBool p).length + 1) ^ 2)
    fun p => (encPair eCSt encBool p).length + 1 := by
  have hs := fst eCSt encBool
  have hb := snd eCSt encBool
  have hk := hs.snd'.fst'
  have hcur := hs.snd'.snd'
  have hk1 := (ComputableInO.eq encNat).tidy.comp (hk.prod (const (encMid := encNat) 1))
  have hbit := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encUnary)
    eBit).inO_one.comp_linear hb
  refine ((hs.fst'.prod ((ComputableInO.natPred.tidy.comp hk).prod (hk1.ite hbit hcur))).of_enc_eq
    (g := cNext) fun p => ?_).mono 100 (fun p => ?_) fun p => ?_
  · simp only [cNext, bitScan, Function.comp_apply]
    split_ifs <;> simp_all
  all_goals
    have hk : (encNat p.1.2.1).length ≤ (encPair eCSt encBool p).length := by
      simp only [length_encPair]
      omega
    have h1 : (encNat 1).length = 1 := rfl
    have h2 : (encPair encNat encNat (p.1.2.1, 1)).length ≤
        2 * (encPair eCSt encBool p).length + 2 := by
      simp only [length_encPair, h1]
      omega
    dsimp only [Function.comp_apply]
    try simp only [h1]
    split_ifs <;> nlinarith

/-! ### The size of the states -/

/-- A bound on the states of the composition: the descriptions and configurations of both
machines, and the positions of their input heads in binary. -/
@[expose] public def composeSpace (dg df : Desc) (x y : List ℕ) (uf ug : ℕ) : ℕ :=
  2 * (2 * (2 * (2 * descLen dg + 1 + cfgSpace dg y ug) + 1 +
    (2 * descLen df + 1 + cfgSpace df x uf)) + 1 + (2 * (encNat (y.length + 1)).length + 1 + 1)) +
      1 + (2 * (encNat (x.length + 1)).length + 1 + 1)

lemma length_eCfg_le_cfgSpace (d : Desc) (x : List ℕ) {j t : ℕ} (h : j ≤ t) :
    (eCfg (run d x j)).length ≤ cfgSpace d x t :=
  (length_eCfg_le_space d x j).trans (by
    have := simSpace_mono d x h
    unfold cfgSpace
    gcongr)

/-- **The size of the states** of the composition. -/
public lemma length_eCSt_le (dg df : Desc) (w : List Bool) (y : List ℕ) (uf ug : ℕ)
    (hhalt : ∀ r, (run df (w.map eBit) r).state = none ↔ uf ≤ r)
    (hy : ((List.range uf).map fun j =>
      (step df (w.map eBit) (run df (w.map eBit) j)).2.toList).flatten = y)
    (hbits : ∀ n ∈ y, n ≤ 1) {i : ℕ} (hi : i ≤ ug * (uf + 1)) (j : ℕ) :
    (eCSt (streamState (passState (cInit dg df) cNext cEnd w i) cNext w j)).length ≤
      composeSpace dg df (w.map eBit) y uf ug := by
  set x := w.map eBit
  have hq : i / (uf + 1) ≤ ug := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hi)
  have hr : i % (uf + 1) ≤ uf := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
  rw [passState_cInit, streamState_cNext, ← Nat.div_add_mod' i (uf + 1),
    iterate_cstep dg df x y uf hhalt hy _ _ hr]
  have hcg := length_eCfg_le_cfgSpace dg y hq
  have hcf := length_eCfg_le_cfgSpace df x hr
  have hp := (inv_iterate dg y (i / (uf + 1))).1.inputPos
  have hpf := (inv_iterate df x (i % (uf + 1))).1.inputPos
  obtain ⟨hk, hfound⟩ := emitScan_le ((List.range (i % (uf + 1))).map fun j =>
    (step df x (run df x j)).2) (by
      intro o ho
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
      cases h : (step df x (run df x j)).2 with
      | none => simp
      | some n =>
        refine hbits n (hy ▸ List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, ?_, rfl⟩, by simp [h]⟩)
        simp only [List.mem_range] at hj ⊢
        omega) ((run dg y (i / (uf + 1))).inputPos) 0 (by omega) (fun _ => rfl)
  obtain ⟨hkx, hcur⟩ := bitScan_le (w.take j) ((run df x (i % (uf + 1))).inputPos) 0 (by omega)
  have h₁ := ComputableTidilyInO.length_encNat_mono (hk.trans hp)
  have h₂ := ComputableTidilyInO.length_encNat_mono (hkx.trans hpf)
  simp only [emitCount] at hk hfound h₁ ⊢
  simp only [length_encPair, encUnary_apply, List.length_replicate, composeSpace, descLen,
    List.length_map, x] at *
  omega

/-! ### The composition as a fold -/

/-- The time of the composition, simplified. -/
lemma compose_time (c N L E Q : ℕ) (hE : E ≤ L) (hQ : 1 ≤ Q) :
    c * (N + E + Q * (N + (N + 1) * (9 * (L + 1) ^ 3 + L + 1)))
      ≤ 20 * c * (Q * (N + 1) ^ 2 * (L + 1) ^ 3) := by
  have hA : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h₃ : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [Nat.mul_assoc 20, Nat.mul_left_comm 20 c]
  refine Nat.mul_le_mul_left c ?_
  set Y := (L + 1) ^ 3
  set Z := (N + 1) ^ 2 * Y
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hz₁ : (N + 1) * Y ≤ Z := Nat.mul_le_mul_right _ hN
  have hz₂ : N + 1 ≤ (N + 1) * Y := Nat.le_mul_of_pos_right _ hA
  have hz₃ : Y ≤ (N + 1) * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hz₄ : Z ≤ Q * Z := Nat.le_mul_of_pos_left _ hQ
  have h₅ : N + (N + 1) * (9 * Y + L + 1) ≤ 11 * Z := by
    have := Nat.mul_le_mul_left (N + 1) (show 9 * Y + L + 1 ≤ 10 * Y by omega)
    rw [show (N + 1) * (10 * Y) = 10 * ((N + 1) * Y) by ring] at this
    omega
  calc _ ≤ N + Y + Q * (11 * Z) := by gcongr; omega
    _ = N + Y + 11 * (Q * Z) := by ring
    _ ≤ 20 * (Q * Z) := by omega
    _ = 20 * (Q * (N + 1) ^ 2 * Y) := by ring

/-- **The composition, on given descriptions.** If the machine described by `df` halts on the
bits of every input after `uf` steps with the symbols `y`, which are bits, and the machine
described by `dg` halts on `y` after `ug` steps with the encoded value of `h`, then `h` is tidily
computable in space linear in `composeSpace`. -/
public theorem computableTidily_compose {α γ : Type} {encIn : α ↪ List Bool}
    {encOut : γ ↪ List Bool} (h : α → γ) (dg df : Desc) (y : α → List ℕ) (uf ug : α → ℕ)
    (hhaltf : ∀ a r, (run df ((encIn a).map eBit) r).state = none ↔ uf a ≤ r)
    (hy : ∀ a, ((List.range (uf a)).map fun j => (step df ((encIn a).map eBit)
      (run df ((encIn a).map eBit) j)).2.toList).flatten = y a)
    (hbits : ∀ a, ∀ n ∈ y a, n ≤ 1)
    (hhaltg : ∀ a q, (run dg (y a) q).state = none ↔ ug a ≤ q) (hug : ∀ a, 0 < ug a)
    (hout : ∀ a, encOut (h a) = (simulate dg (y a) (ug a)).1.map fun n => decide (n ≠ 0)) :
    ∃ c, ComputableTidilyInTimeAndSpace h encIn encOut
      (fun a => c * (ug a * (uf a + 1) * ((encIn a).length + 1) ^ 2 *
        (composeSpace dg df ((encIn a).map eBit) (y a) (uf a) (ug a) + 1) ^ 3))
      (fun a => c * (composeSpace dg df ((encIn a).map eBit) (y a) (uf a) (ug a) + 1)) := by
  set L := fun a => composeSpace dg df ((encIn a).map eBit) (y a) (uf a) (ug a) with hLdef
  have hpos (a : α) : 1 ≤ ug a * (uf a + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by have := hug a; positivity)
  have hL (a : α) {i : ℕ} (hi : i ≤ ug a * (uf a + 1)) (j : ℕ) :
      (eCSt (streamState (passState (cInit dg df) cNext cEnd (bitTr.events (encIn a)) i) cNext
        (bitTr.events (encIn a)) j)).length ≤ L a := by
    rw [bitTr_events]
    exact length_eCSt_le dg df (encIn a) (y a) (uf a) (ug a) (hhaltf a) (hy a) (hbits a) hi j
  have hinit : ComputableTidilyInO (fun _ : α => cInit dg df) encIn eCSt
      (fun a => (encIn a).length) fun _ => 0 := by
    obtain ⟨c₀, hc₀⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := eCSt)
      (cInit dg df)
    exact .of_bounds hc₀.computableTidilyInTimeAndSpace (2 * c₀ + 2 + (eCSt (cInit dg df)).length)
      (fun a => by nlinarith) (fun _ => Nat.zero_le _) (fun a => by simp)
  refine Exists.elim (ComputableTidilyInTimeAndSpace.multiPassFold_translate bitTr
    (encQ := encUnit) hinit cNext_inO cEmit_inO cEnd_inO cCont_inO
    (ComputableTidilyInO.const (encMid := encUnit) ())
    (passes := fun a => ug a * (uf a + 1) - 1) (g := h) (encOut := encOut) ?_ ?_
    (tMax := fun a => 9 * (L a + 1) ^ 3) (sMax := fun a => 9 * (L a + 1)) (lMax := L)
    ?_ ?_ ?_ ?_ ?_ ?_) fun c hc => ?_
  case refine_1 =>
    intro a i hi
    have hr : (i + 1) % (uf a + 1) ≤ uf a := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
    rw [bitTr_events, passState_cInit, ← Nat.div_add_mod' (i + 1) (uf a + 1),
      iterate_cstep dg df _ (y a) (uf a) (hhaltf a) (hy a) _ _ hr]
    rw [Bool.eq_iff_iff, Option.isSome_iff_ne_none, ne_eq, hhaltg, decide_eq_true_iff, not_le,
      Nat.div_lt_iff_lt_mul (by omega)]
    have := hug a
    have : 1 ≤ ug a * (uf a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  case refine_2 =>
    intro a
    have hP : ug a * (uf a + 1) - 1 + 1 = ug a * (uf a + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by have := hug a; positivity))
    rw [hout a, bitTr_events, hP]
    simp only [encBits_apply, streamState_cNext, passState_cInit]
    rw [flatten_gEmit dg df _ (y a) (uf a) (hhaltf a) (hy a)]
    exact (List.append_nil _).symm
  case refine_3 =>
    rintro a i hi j -
    have := hL a (show i ≤ ug a * (uf a + 1) by omega) j
    rw [length_encPair, encBool_apply, List.length_singleton]
    generalize (eCSt _).length = n at this ⊢
    have h₁ := Nat.pow_le_pow_left (show 2 * n + 1 + 1 + 1 ≤ 3 * (L a + 1) by omega) 2
    have h₂ : (L a + 1) ^ 2 ≤ (L a + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  case refine_4 =>
    rintro a i hi j -
    have := hL a (show i ≤ ug a * (uf a + 1) by omega) j
    rw [length_encPair, encBool_apply, List.length_singleton]
    dsimp only
    omega
  case refine_5 =>
    intro a i hi
    have h₁ := hL a (show i ≤ ug a * (uf a + 1) by omega) (bitTr.events (encIn a)).length
    have h₂ : (eCSt (passState (cInit dg df) cNext cEnd (bitTr.events (encIn a)) (i + 1))).length
        ≤ L a := hL a (show i + 1 ≤ ug a * (uf a + 1) by have := hpos a; omega) 0
    have h₃ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) 3
    have h₄ := Nat.pow_le_pow_left (Nat.add_le_add_right h₂ 1) 3
    refine (Nat.add_le_add (Nat.add_le_add h₃ h₃) h₄).trans ?_
    generalize (L a + 1) ^ 3 = Y
    omega
  case refine_6 =>
    intro a i hi
    have h₁ := hL a (show i ≤ ug a * (uf a + 1) by omega) (bitTr.events (encIn a)).length
    have h₂ : (eCSt (passState (cInit dg df) cNext cEnd (bitTr.events (encIn a)) (i + 1))).length
        ≤ L a := hL a (show i + 1 ≤ ug a * (uf a + 1) by have := hpos a; omega) 0
    omega
  case refine_7 =>
    rintro a i hi j -
    exact hL a (show i ≤ ug a * (uf a + 1) by omega) j
  case refine_8 =>
    intro a
    exact hL a (show ug a * (uf a + 1) - 1 + 1 ≤ ug a * (uf a + 1) by have := hpos a; omega) 0
  refine ⟨20 * c, hc.mono (fun a => ?_) fun a => ?_⟩
  all_goals
    have hE : (eCSt (passState (cInit dg df) cNext cEnd (bitTr.events (encIn a))
        (ug a * (uf a + 1) - 1 + 1))).length ≤ L a :=
      hL a (show ug a * (uf a + 1) - 1 + 1 ≤ ug a * (uf a + 1) by have := hpos a; omega) 0
    have hP : ug a * (uf a + 1) - 1 + 1 = ug a * (uf a + 1) := by have := hpos a; omega
    generalize (eCSt (passState (cInit dg df) cNext cEnd (bitTr.events (encIn a))
      (ug a * (uf a + 1) - 1 + 1))).length = E at hE ⊢
  · change _ ≤ 20 * c * (ug a * (uf a + 1) * ((encIn a).length + 1) ^ 2 * (L a + 1) ^ 3)
    rw [hP]
    exact compose_time c (encIn a).length (L a) E (ug a * (uf a + 1)) hE (hpos a)
  · change _ ≤ 20 * c * (L a + 1)
    rw [show 20 * c * (L a + 1) = c * (20 * (L a + 1)) by ring]
    exact Nat.mul_le_mul_left c (by omega)

/-! ### Machines -/

section Machines

variable {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)

/-- The simulation of a machine has halted exactly from the halting time of the machine on. -/
lemma run_desc_halted (x : List Bool) {u : ℕ} (hh : tm.HaltsAt (tm.initCfg x) u) (r : ℕ) :
    (run (desc eS eBit tm) (x.map eBit) r).state = none ↔ u ≤ r := by
  have h := congrArg Prod.snd (simulate_desc eS eBit tm x r)
  change (run (desc eS eBit tm) (x.map eBit) r).state.isNone = _ at h
  rw [← Option.isNone_iff_eq_none, h, Option.isNone_iff_eq_none]
  exact ⟨hh.le_of_halted, fun hr => (hh.runFrom_eq hr).symm ▸ hh.halted⟩

/-- The simulation of a machine emits its output by its halting time. -/
lemma simulate_desc_output (x : List Bool) {out : List Bool} (hc : tm.Computes x out) {u : ℕ}
    (hh : tm.HaltsAt (tm.initCfg x) u) :
    (simulate (desc eS eBit tm) (x.map eBit) u).1 = out.map eBit := by
  rw [simulate_desc, output_haltsAt hc hh]

/-- The space of the simulation of a machine within its space bound. -/
lemma cfgSpace_desc_le (x : List Bool) {s : ℕ} (hs : tm.RunsInSpace x s) (t : ℕ) :
    cfgSpace (desc eS eBit tm) (x.map eBit) t ≤ (12 * descLen (desc eS eBit tm) + 40) *
      (s + (encNat (x.length + 1)).length + 1) := by
  have hS : simSpace (desc eS eBit tm) (x.map eBit) t ≤ s :=
    (simSpace_desc eS eBit tm x t).trans_le (RunsInSpace.space_le hs t)
  have : (desc eS eBit tm).tapes ≤ descLen (desc eS eBit tm) := by
    simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
    omega
  simp only [cfgSpace, List.length_map]
  nlinarith

end Machines

/-- The space of the composition, simplified. -/
lemma composeSpace_le (Dg Df CG CF Ex Ey Kg Kf Sg Sf : ℕ) (hg : CG ≤ Kg * (Sg + Ey + 1))
    (hf : CF ≤ Kf * (Sf + Ex + 1)) :
    2 * (2 * (2 * (2 * Dg + 1 + CG) + 1 + (2 * Df + 1 + CF)) + 1 + (2 * Ey + 1 + 1)) + 1 +
        (2 * Ex + 1 + 1) + 1 ≤
      (8 * Kg + 4 * Kf + 16 * Dg + 8 * Df + 30) * (Sf + Sg + Ex + Ey + 1) := by
  nlinarith

/-- The time of the composition, in the given bounds. -/
lemma final_time_le (c K A A' N CS S : ℕ) (hA : A ≤ A') (hCS : CS + 1 ≤ K * (S + 1)) :
    c * (A * (N + 1) ^ 2 * (CS + 1) ^ 3) ≤ c * K ^ 3 * (A' * (N + 1) ^ 2 * (S + 1) ^ 3) := by
  have h₁ := Nat.pow_le_pow_left hCS 3
  calc _ ≤ c * (A' * (N + 1) ^ 2 * (K * (S + 1)) ^ 3) := by gcongr
    _ = _ := by ring

/-- The space of the composition, in the given bounds. -/
lemma final_space_le (c K CS S : ℕ) (hCS : CS + 1 ≤ K * (S + 1)) :
    c * (CS + 1) ≤ c * K ^ 3 * (S + 1) := by
  have : K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) _
  calc _ ≤ c * (K * (S + 1)) := Nat.mul_le_mul_left c hCS
    _ ≤ c * (K ^ 3 * (S + 1)) := by gcongr
    _ = _ := by ring

end Universal

open Universal in
/-- **Composition within small space.** If `f` and `g` are computable within the time bounds
`tf`, `tg` and the space bounds `sf`, `sg`, then `g ∘ f` is computable within space linear in
`sf a + sg (f a)` plus the logarithms of the lengths of the input and of the intermediate value,
without ever writing down the intermediate value. Its time is polynomial in the time bounds, the
length of the input and the space bound. -/
public theorem ComputableInTimeAndSpace.comp_space {α β γ : Type} {encIn : α ↪ List Bool}
    {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α → β} {g : β → γ}
    {tf sf : α → ℕ} {tg sg : β → ℕ} (hf : ComputableInTimeAndSpace f encIn encMid tf sf)
    (hg : ComputableInTimeAndSpace g encMid encOut tg sg) :
    ∃ c, ComputableInTimeAndSpace (g ∘ f) encIn encOut
      (fun a => c * ((tg (f a) + 1) * (tf a + 1) * ((encIn a).length + 1) ^ 2 *
        (sf a + sg (f a) + (encNat ((encIn a).length + 1)).length +
          (encNat ((encMid (f a)).length + 1)).length + 1) ^ 3))
      (fun a => c * (sf a + sg (f a) + (encNat ((encIn a).length + 1)).length +
          (encNat ((encMid (f a)).length + 1)).length + 1)) := by
  obtain ⟨kf, Sf, _, tmf, htmf⟩ := hf
  obtain ⟨kg, Sg, _, tmg, htmg⟩ := hg
  let := Fintype.ofFinite Sf
  let := Fintype.ofFinite Sg
  obtain ⟨ef, hef⟩ := Countable.exists_injective_nat Sf
  obtain ⟨eg, heg⟩ := Countable.exists_injective_nat Sg
  set df := desc ⟨ef, hef⟩ eBit tmf
  set dg := desc ⟨eg, heg⟩ eBit tmg
  choose uf huf_le huf using fun a => exists_haltsAt_of_runsInTime (htmf a).2.1
  choose ug hug_le hug using fun a => exists_haltsAt_of_runsInTime (htmg (f a)).2.1
  obtain ⟨c, hc⟩ := computableTidily_compose (encIn := encIn) (encOut := encOut) (g ∘ f) dg df
    (fun a => (encMid (f a)).map eBit) uf ug
    (fun a => run_desc_halted _ tmf (encIn a) (huf a))
    (fun a => (congrArg Prod.fst (simulate_eq df _ (uf a))).symm.trans
      (simulate_desc_output _ tmf (encIn a) (htmf a).1 (huf a)))
    (fun a n hn => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hn
      cases b <;> decide)
    (fun a => run_desc_halted _ tmg (encMid (f a)) (hug a))
    (fun a => haltsAt_pos (hug a))
    (fun a => by
      rw [simulate_desc_output _ tmg (encMid (f a)) (htmg (f a)).1 (hug a), List.map_map]
      conv_lhs => rw [← List.map_id (encOut ((g ∘ f) a))]
      congr 1
      funext b
      cases b <;> rfl)
  set K := 8 * (12 * descLen dg + 40) + 4 * (12 * descLen df + 40) + 16 * descLen dg +
    8 * descLen df + 30
  have hK (a : α) : composeSpace dg df ((encIn a).map eBit) ((encMid (f a)).map eBit) (uf a) (ug a)
      + 1 ≤ K * (sf a + sg (f a) + (encNat ((encIn a).length + 1)).length +
        (encNat ((encMid (f a)).length + 1)).length + 1) := by
    have hg := cfgSpace_desc_le ⟨eg, heg⟩ tmg (encMid (f a)) (htmg (f a)).2.2 (ug a)
    have hf := cfgSpace_desc_le ⟨ef, hef⟩ tmf (encIn a) (htmf a).2.2 (uf a)
    have := composeSpace_le (descLen dg) (descLen df) _ _ _ _ _ _ _ _ hg hf
    simp only [composeSpace, List.length_map] at this ⊢
    omega
  refine ⟨c * K ^ 3, hc.computableInTimeAndSpace.mono (fun a => ?_) fun a => ?_⟩
  · exact final_time_le c K _ _ _ _ _ (Nat.mul_le_mul (by have := hug_le a; omega)
      (by have := huf_le a; omega)) (hK a)
  · exact final_space_le c K _ _ (hK a)

/-- The binary length of a power. -/
lemma length_encNat_pow_le (n d : ℕ) : (encNat (n ^ d)).length ≤ d * (encNat n).length + 1 := by
  simp only [encNat_apply]
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  refine Nat.size_le.mpr ?_
  calc n ^ d < (2 ^ n.size) ^ d + 1 :=
        Nat.lt_succ_of_le (Nat.pow_le_pow_left (Nat.lt_size_self n).le d)
    _ ≤ 2 ^ (d * n.size + 1) := by
      rw [show d * n.size + 1 = n.size * d + 1 by ring, pow_succ, ← pow_mul]
      have := Nat.one_le_two_pow (n := n.size * d)
      omega

lemma log_time_le (c M A N S ℓ : ℕ) (h : S + 1 ≤ M * ℓ) :
    c * (A * (N + 1) ^ 2 * (S + 1) ^ 3) ≤ c * M ^ 3 * (A * (N + 1) ^ 2 * ℓ ^ 3) := by
  have h₁ := Nat.pow_le_pow_left h 3
  calc _ ≤ c * (A * (N + 1) ^ 2 * (M * ℓ) ^ 3) := by gcongr
    _ = _ := by ring

lemma log_space_le (c M S ℓ : ℕ) (h : S + 1 ≤ M * ℓ) : c * (S + 1) ≤ c * M ^ 3 * ℓ := by
  have : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) _
  calc _ ≤ c * (M * ℓ) := Nat.mul_le_mul_left c h
    _ ≤ c * (M ^ 3 * ℓ) := by gcongr
    _ = _ := by ring

/-- **Logarithmic space is closed under composition.** If `f` and `g` are computable in space
logarithmic in the lengths of their inputs, and `f` takes inputs of length `n` to values of length
less than `(n + 1) ^ d`, then `g ∘ f` is computable in space logarithmic in the length of its
input. -/
public theorem ComputableInTimeAndSpace.comp_logSpace {α β γ : Type} {encIn : α ↪ List Bool}
    {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α → β} {g : β → γ}
    {tf : α → ℕ} {tg : β → ℕ} {kf kg d : ℕ}
    (hf : ComputableInTimeAndSpace f encIn encMid tf
      fun a => kf * (encNat ((encIn a).length + 1)).length)
    (hg : ComputableInTimeAndSpace g encMid encOut tg
      fun b => kg * (encNat ((encMid b).length + 1)).length)
    (hlen : ∀ a, (encMid (f a)).length + 1 ≤ ((encIn a).length + 1) ^ d) :
    ∃ c, ComputableInTimeAndSpace (g ∘ f) encIn encOut
      (fun a => c * ((tg (f a) + 1) * (tf a + 1) * ((encIn a).length + 1) ^ 2 *
        (encNat ((encIn a).length + 1)).length ^ 3))
      (fun a => c * (encNat ((encIn a).length + 1)).length) := by
  obtain ⟨c, h⟩ := hf.comp_space hg
  set M := kf + (kg + 1) * (d + 1) + 3
  have hM (a : α) : kf * (encNat ((encIn a).length + 1)).length +
      kg * (encNat ((encMid (f a)).length + 1)).length + (encNat ((encIn a).length + 1)).length +
        (encNat ((encMid (f a)).length + 1)).length + 1 ≤
          M * (encNat ((encIn a).length + 1)).length := by
    have hℓ : 1 ≤ (encNat ((encIn a).length + 1)).length :=
      ComputableTidilyInO.length_encNat_mono (m := 1) (by omega)
    have hy : (encNat ((encMid (f a)).length + 1)).length ≤
        (d + 1) * (encNat ((encIn a).length + 1)).length :=
      (ComputableTidilyInO.length_encNat_mono (hlen a)).trans
        ((length_encNat_pow_le _ d).trans (by nlinarith))
    have := Nat.mul_le_mul_left kg hy
    have e : M * (encNat ((encIn a).length + 1)).length =
        kf * (encNat ((encIn a).length + 1)).length +
          kg * ((d + 1) * (encNat ((encIn a).length + 1)).length) +
          (d + 1) * (encNat ((encIn a).length + 1)).length +
          3 * (encNat ((encIn a).length + 1)).length := by
      simp only [M]
      ring
    omega
  exact ⟨c * M ^ 3, h.mono (fun a => log_time_le c M _ _ _ _ (hM a))
    fun a => log_space_le c M _ _ (hM a)⟩

end Turing.MultiTapeTM
