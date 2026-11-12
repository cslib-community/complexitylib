/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TruthTable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicPhase
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CarrySaveSelector

/-!
# A finite cyclic controller for streamed carry-save queries

The first six work tapes store binary height, binary index, persistent path, selector status, unary
layer frontier, and reusable selector flags, in that order. The unary frontier advances once
per compressor layer. Binary counters remain available to the amortized selector, while leaf
detection inspects one cell. Any additional tapes and their cursors are preserved for actual native
leaf continuations. The same time bound is independent of the number and contents of private tapes.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveStream

open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery

/-- The selector's finite state for a fixed port of one of the two compressor formulas. -/
abbrev SelectorState (carry : Bool) (port : Fin 7) :=
  MultiTapeTM.CarrySaveSelector.State (CarrySaveLocal.source carry port).shift ⊕ Option Bool

/-- Finite cyclic control. Runtime height and path never appear in this state type. -/
inductive State (S : Type) where
  | header (carry claim : Bool)
  | table (carry claim : Bool) (q : TruthTable.State Unit)
  | select (carry : Bool) (port : Fin 7) (claim : Bool) (q : SelectorState carry port)
  | returned (carry claim : Bool)
  | leaf (carry claim : Bool) (q : S)
  deriving Fintype

/-- First six tapes are reserved for the query; the remaining tapes belong to the leaf. -/
@[expose] def coreEmb (k : ℕ) : Fin 6 ↪ Fin (k + 6) where
  toFun i := ⟨i.val, by omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : Fin (k + 6) => j.val) h)

/-- Arbitrary private tape contents and head positions; the controller preserves them. Values
on the six reserved tapes are ignored when constructing a query configuration. -/
structure Scratch (k : ℕ) where
  /-- Backing tape contents outside the query layout. -/
  tapes : Fin (k + 6) → ℤ → Option Bool
  /-- Backing head positions outside the query layout. -/
  positions : Fin (k + 6) → ℤ

/-- Blank private storage with every head at the origin. -/
@[expose] def Scratch.blank (k : ℕ) : Scratch k := ⟨fun _ _ => none, fun _ => 0⟩

variable {k : ℕ}

private noncomputable def stop : MultiTapeATM (k + 6) Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ _ =>
    ⟨0, fun _ => (none, 0), none, none⟩)) (fun _ => false)

/-- The existing physical selector on the six reserved tapes. -/
private noncomputable def baseSelector (carry : Bool) (port : Fin 7) :
    MultiTapeTM 6 Bool (SelectorState carry port) :=
  MultiTapeTM.CarrySaveSelector.complete (0 : Fin 5) 1 2 3
    (childSide (CarrySaveLocal.source carry port).word) (CarrySaveLocal.source carry port).shift

/-- The physical selector acts only on the first six tapes. -/
noncomputable def selector (carry : Bool) (port : Fin 7) :
    MultiTapeTM (k + 6) Bool (SelectorState carry port) :=
  (baseSelector carry port).extendTapes (coreEmb k)

private noncomputable def table (carry claim : Bool) :
    MultiTapeATM (k + 6) Bool (TruthTable.State Unit) :=
  TruthTable.machine (fun v => (CarrySaveLocal.formula carry).eval interpretation v)
    claim (fun _ _ => stop)

private def jump {S : Type} (q : Option (State S)) (out : Option Bool := none) :
    Action (k + 6) Bool (State S) := ⟨0, fun _ => (none, 0), out, q⟩

private noncomputable def tr {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (move : Bool) : State S → Option Bool → (Fin (k + 6) → Option Bool) → Action (k + 6) Bool
        (State S)
  | .header carry claim, _, work =>
    if work (coreEmb k 4) = some true then
      ⟨0, fun i => (none, if i = coreEmb k 4 then 1 else 0), none,
        some (.table carry claim .guess₀)⟩
    else if work (coreEmb k 4) = none then jump (some (.leaf carry claim (leaf carry
        claim).toPTM.toNTM.q₀))
    else jump none
  | .table carry _ (.child p bit _), _, _ =>
    jump (some (.select carry p bit (selector (k := k) carry p).q₀))
  | .table carry claim q, input, work =>
    let a := (table carry claim).action q input work move
    { a with state := a.state.map (fun q => match q with
        | .child p bit _ => .select carry p bit (selector (k := k) carry p).q₀
        | q => .table carry claim q) }
  | .select carry p bit q, input, work =>
    let a := (selector (k := k) carry p).tr q input work
    { a with state := some (a.state.elim
      (.returned (childCarry (CarrySaveLocal.source carry p).word) bit) (.select carry p bit)) }
  | .returned carry claim, _, work =>
    if work (coreEmb k 3) = some false then jump (some (.header carry claim))
    else jump none (some (!claim))
  | .leaf carry claim q, input, work =>
    let a := (leaf carry claim).action q input work move
    { a with state := a.state.map (.leaf carry claim) }

private def universal {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) : State S → Bool
  | .table _ _ (.choose₀ _) | .table _ _ (.choose₁ _ _) | .table _ _ (.choose₂ _ _ _) => true
  | .leaf carry claim q => (leaf carry claim).universal q
  | _ => false

/-- One finite machine reuses its table and selector states for arbitrarily many runtime layers.
The unary tape must initially contain one true cell per remaining layer, followed by blanks. -/
noncomputable def machine {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) : MultiTapeATM (k + 6) Bool (State S) :=
  ofTMs (fun b => MultiTapeTM.ofTr (.header carry claim) (tr leaf b)) (universal leaf)

/-- Resume this same controller at a selector, retaining the selected input claim in control. -/
noncomputable def continuation {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry : Bool) (p : Fin 7) (bit : Bool) : MultiTapeATM (k + 6) Bool (State S) :=
  ofTMs (fun b => MultiTapeTM.ofTr (.select carry p bit (selector (k := k) carry p).q₀) (tr leaf b))
    (universal leaf)

private def fold {S : Type} (carry claim : Bool) : TruthTable.State (State S) → State S
  | .guess₀ => .table carry claim .guess₀
  | .guess₁ a => .table carry claim (.guess₁ a)
  | .guess₂ a b => .table carry claim (.guess₂ a b)
  | .guess₃ a b c => .table carry claim (.guess₃ a b c)
  | .guess₄ a b c d => .table carry claim (.guess₄ a b c d)
  | .guess₅ a b c d e => .table carry claim (.guess₅ a b c d e)
  | .guess₆ a b c d e f => .table carry claim (.guess₆ a b c d e f)
  | .choose₀ v => .table carry claim (.choose₀ v)
  | .choose₁ v a => .table carry claim (.choose₁ v a)
  | .choose₂ v a b => .table carry claim (.choose₂ v a b)
  | .child _ _ q => q

private noncomputable def folded {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) :=
  TruthTable.machine (fun v => (CarrySaveLocal.formula carry).eval interpretation v)
    claim (continuation leaf carry)


/-- Entering a compressor layer advances only the unary frontier. All existing words and the
persistent path remain in place. -/
theorem next_header_layer {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim move : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input)
    (h : cfg.workTapes (coreEmb k 4) (cfg.workTapePos (coreEmb k 4)) = some true) :
    (machine leaf carry claim).next move (cfg.withState (some (.header carry claim))) =
      { cfg.withState (some (.table carry claim .guess₀)) with
        workTapePos := Function.update cfg.workTapePos (coreEmb k 4) (cfg.workTapePos (coreEmb k
            4) + 1) } := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp only [tr, Cfg.workTapeSymbols, Cfg.withState, h, ↓reduceIte, Action.apply,
    moveInputPos_zero, Option.toList_none, List.append_nil]
  congr 1
  funext i
  by_cases hi : i = coreEmb k 4 <;> simp [hi]

/-- At the blank unary frontier, leaf handoff takes one transition and preserves all storage. -/
theorem next_header_leaf {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim move : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input)
    (h : cfg.workTapes (coreEmb k 4) (cfg.workTapePos (coreEmb k 4)) = none) :
    (machine leaf carry claim).next move (cfg.withState (some (.header carry claim))) =
      cfg.withState (some (.leaf carry claim (leaf carry claim).toPTM.toNTM.q₀)) := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [tr, Cfg.workTapeSymbols, Cfg.withState, h, jump, Action.apply]

/-- Successful selection returns to the same header; no query copy or normalization occurs. -/
theorem next_returned_valid {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim move : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input)
    (h : cfg.workTapes (coreEmb k 3) (cfg.workTapePos (coreEmb k 3)) = some false) :
    (machine leaf carry claim).next move (cfg.withState (some (.returned carry claim))) =
      cfg.withState (some (.header carry claim)) := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [tr, Cfg.workTapeSymbols, Cfg.withState, h, jump, Action.apply]

/-- An absent child has value false, so the boundary accepts precisely a false claim. -/
theorem next_returned_absent {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim move : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input)
    (h : cfg.workTapes (coreEmb k 3) (cfg.workTapePos (coreEmb k 3)) = some true) :
    (machine leaf carry claim).next move (cfg.withState (some (.returned carry claim))) =
      { cfg.withState none with output := cfg.output ++ [!claim] } := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [tr, Cfg.workTapeSymbols, Cfg.withState, h, jump, Action.apply]
private theorem action_fold {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) (q : TruthTable.State (State S))
    (input : Option Bool) (work : Fin (k + 6) → Option Bool) (move : Bool) :
    (machine leaf carry claim).action (fold carry claim q) input work move =
      let a := (folded leaf carry claim).action q input work move
      { a with state := a.state.map (fold carry claim) } := by
  cases q
  case child p bit q =>
    simp only [machine, folded, TruthTable.machine, action, ofTMs, MultiTapeTM.tr_ofTr,
      fold, TruthTable.tr, continuation, Equiv.apply_symm_apply]
    change tr leaf move q input work =
      { tr leaf move q input work with
        state := ((tr leaf move q input work).state.map (.child p bit)).map (fold carry claim) }
    cases ha : tr leaf move q input work
    simp [fold, Option.map_map, Function.comp_def]
  all_goals simp only [machine, folded, TruthTable.machine, action, ofTMs,
    MultiTapeTM.tr_ofTr, fold, tr, table, continuation,
    Equiv.apply_symm_apply, TruthTable.tr]
  all_goals first | rfl | (split <;> rfl)

private noncomputable def tableSimulation {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry claim : Bool) :
    StateSimulation (folded leaf carry claim) (machine leaf carry claim) where
  stateMap := fold carry claim
  universal_eq q := by
    cases q <;> simp [fold, machine, folded, TruthTable.machine, ofTMs, universal,
      TruthTable.universal, continuation]
  next_eq cfg move := by
    cases hs : cfg.state with
    | none => rw [next_of_halted _ (by simp [hs]), next_of_halted _ hs]
    | some q =>
      rw [next_of_state _ (q := fold carry claim q) (by simp [hs]), next_of_state _ hs]
      rw [action_fold]
      rfl

/-- The cyclic controller's table phase is the native seven-port alternating formula macro.
Its continuations are this same finite controller at the selected physical selector. -/
theorem acceptsWithin_table {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input)
    (hout : cfg.output = []) (n : ℕ) :
    (machine leaf carry claim).AcceptsWithin (n + 10)
      (cfg.withState (some (.table carry claim .guess₀))) ↔
      ∃ v : Fin 7 → Bool, (CarrySaveLocal.formula carry).eval interpretation v = claim ∧
        ∀ p, (continuation leaf carry p (v p)).AcceptsWithin n
          (cfg.withState (some (.select carry p (v p) (selector (k := k) carry p).q₀))) := by
  exact ((tableSimulation leaf carry claim).acceptsWithin_iff (n + 10)
    (cfg.withState (some .guess₀))).trans
      (TruthTable.acceptsWithin_iff
        (fun v => (CarrySaveLocal.formula carry).eval interpretation v) claim
        (continuation leaf carry) n (cfg.withState none) hout)

/-- All branches of the cyclic table phase obey the same ten-transition overhead. -/
theorem haltsWithin_table {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input) (n : ℕ)
    (h : ∀ p b, (continuation leaf carry p b).HaltsWithin n
      (cfg.withState (some (.select carry p b (selector (k := k) carry p).q₀)))) :
    (machine leaf carry claim).HaltsWithin (n + 10)
      (cfg.withState (some (.table carry claim .guess₀))) := by
  exact (tableSimulation leaf carry claim).haltsWithin_iff (n + 10)
    (cfg.withState (some .guess₀)) |>.mpr (TruthTable.haltsWithin
      (fun v => (CarrySaveLocal.formula carry).eval interpretation v) claim
      (continuation leaf carry) n (cfg.withState none) h)

private noncomputable def leafSimulation {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry claim : Bool) :
    StateSimulation (leaf carry claim) (machine leaf carry claim) where
  stateMap := .leaf carry claim
  universal_eq _ := rfl
  next_eq cfg move := by
    cases hs : cfg.state with
    | none => rw [next_of_halted _ (by simp [hs]), next_of_halted _ hs]
    | some q =>
      rw [next_of_state _ (q := .leaf carry claim q) (by simp [hs]), next_of_state _ hs]
      simp only [machine, action, ofTMs, MultiTapeTM.tr_ofTr, tr, Equiv.apply_symm_apply]
      rfl

/-- Leaf execution is the supplied native machine with exactly its original time budget. -/
theorem acceptsWithin_leaf {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input) (n : ℕ) :
    (machine leaf carry claim).AcceptsWithin n
      (cfg.withState (some (.leaf carry claim (leaf carry claim).toPTM.toNTM.q₀))) ↔
      (leaf carry claim).AcceptsWithin n
        (cfg.withState (some (leaf carry claim).toPTM.toNTM.q₀)) :=
  (leafSimulation leaf carry claim).acceptsWithin_iff n
    (cfg.withState (some (leaf carry claim).toPTM.toNTM.q₀))

/-- Unary zero detection and leaf execution together have one transition of overhead. -/
theorem acceptsWithin_header_leaf {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim : Bool) {T : Type} {input : List Bool} (cfg : Cfg (k + 6) Bool T input) (n : ℕ)
    (h : cfg.workTapes (coreEmb k 4) (cfg.workTapePos (coreEmb k 4)) = none) :
    (machine leaf carry claim).AcceptsWithin (n + 1)
      (cfg.withState (some (.header carry claim))) ↔
      (leaf carry claim).AcceptsWithin n
        (cfg.withState (some (leaf carry claim).toPTM.toNTM.q₀)) := by
  rw [acceptsWithin_succ_of_existential _ rfl rfl]
  simp only [next_header_leaf leaf carry claim _ cfg h, acceptsWithin_leaf, exists_const]

/-- Map the deterministic selector's terminal state to its cyclic controller return state. -/
def selectorStateMap {S : Type} (carry : Bool) (p : Fin 7) (bit : Bool) :
    Option (SelectorState carry p) → State S :=
  fun q => q.elim (.returned (childCarry (CarrySaveLocal.source carry p).word) bit)
    (.select carry p bit)

/-- Every running selector step is a physical step of the cyclic controller, for either choice. -/
theorem next_selector {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry : Bool) (p : Fin 7) (bit move : Bool) {input : List Bool}
    (cfg : Cfg (k + 6) Bool (SelectorState carry p) input) (hrun : cfg.state ≠ none) :
    (machine leaf carry bit).next move
      (cfg.mapState (fun q => some (selectorStateMap carry p bit q))) =
      ((selector (k := k) carry p).step cfg).mapState
        (fun q => some (selectorStateMap carry p bit q)) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hrun
  rw [next_of_state _ (q := .select carry p bit q) (by simp [hq, selectorStateMap]),
    MultiTapeTM.step_of_state hq]
  simp only [machine, action, ofTMs, MultiTapeTM.tr_ofTr, tr, Equiv.apply_symm_apply]
  rfl

private noncomputable def continuationSimulation {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry : Bool) (p : Fin 7)
    (bit carry' claim' : Bool) :
    StateSimulation (continuation leaf carry p bit) (machine leaf carry' claim') where
  stateMap := id
  universal_eq _ := rfl
  next_eq cfg move := by
    cases hs : cfg.state with
    | none => rw [next_of_halted _ (by simp [hs]), next_of_halted _ hs]
    | some q =>
      rw [next_of_state _ (q := q) (by simp [hs]), next_of_state _ hs]
      simp [machine, continuation, action, ofTMs, Cfg.mapState, Action.apply]

/-- A selector continuation is the same cyclic transition table with a different initial state. -/
theorem acceptsWithin_continuation {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry : Bool) (p : Fin 7)
    (bit carry' claim' : Bool) {input : List Bool} (cfg : Cfg (k + 6) Bool (State S) input) (n :
        ℕ) :
    (continuation leaf carry p bit).AcceptsWithin n cfg ↔
      (machine leaf carry' claim').AcceptsWithin n cfg := by
  simpa [continuationSimulation, Cfg.mapState] using
    ((continuationSimulation leaf carry p bit carry' claim').acceptsWithin_iff n cfg).symm

/-- Reinitializing at a selector does not change any branch's remaining running time. -/
theorem haltsWithin_continuation {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry : Bool) (p : Fin 7)
    (bit carry' claim' : Bool) {input : List Bool} (cfg : Cfg (k + 6) Bool (State S) input) (n :
        ℕ) :
    (continuation leaf carry p bit).HaltsWithin n cfg ↔
      (machine leaf carry' claim').HaltsWithin n cfg := by
  simpa [continuationSimulation, Cfg.mapState] using
    ((continuationSimulation leaf carry p bit carry' claim').haltsWithin_iff n cfg).symm

private def storage {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) : Cfg 5 Bool Unit input :=
  ⟨none, 0, ![tapeOfList height, tapeOfList bits, tapeOfList path,
    tapeOfList [status], tapeOfList unary], ![0, 0, (path.length : ℤ), 0, frontier], []⟩

/-- Physical representation of a streamed query, including cleared reusable flags. Binary
counters start at zero, the path head at its right blank, and the unary head at its frontier. -/
private def baseConfig {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) : Cfg 6 Bool Unit input :=
  MultiTapeTM.outCfg (storage height bits path unary frontier status)

/-- Certified selector clock for one chosen port; it charges scans, rewinds, append and cleanup. -/
def selectorClock (carry : Bool) (p : Fin 7) (height bits : List Bool) : ℕ :=
  2 * MultiTapeTM.BinaryDecrement.zeros height +
    MultiTapeTM.BinaryDecrement.totalClock (CarrySaveLocal.source carry p).shift.val bits +
    (CarrySaveLocal.source carry p).shift.val + 8

private theorem lastCases_small {α : Type*} (last : α) (f : Fin 5 → α)
    (j : Fin 6) (h : j.val < 5) : Fin.lastCases last f j = f ⟨j.val, h⟩ := by
  have hj : j = (⟨j.val, h⟩ : Fin 5).castSucc := by apply Fin.ext; rfl
  conv_lhs => rw [hj, Fin.lastCases_castSucc]

private theorem lastCases_top {α : Type*} (last : α) (f : Fin 5 → α) :
    Fin.lastCases last f (5 : Fin 6) = last := by
  change Fin.lastCases last f (Fin.last 5) = last
  exact Fin.lastCases_last

/-- The physical selector preserves the entire unary tape and its frontier, updates both
binary counters in place, appends one path bit, writes status and clears its scratch flags. -/
private theorem runFrom_baseSelector {input : List Bool} (carry : Bool) (p : Fin 7)
    (height bits path unary : List Bool) (frontier : ℤ) (status : Bool) :
    (baseSelector carry p).runFrom
      ((baseConfig (input := input) height bits path unary frontier status).withState
        (some (baseSelector carry p).q₀)) (selectorClock carry p height bits) =
      (baseConfig (Cslib.BitString.decrement height)
        (Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits)
        (path ++ [childSide (CarrySaveLocal.source carry p).word]) unary frontier
        ((MultiTapeTM.CarrySaveSelector.resultFlags height bits
          (CarrySaveLocal.source carry p).shift).contains true)).withState none := by
  have hr := MultiTapeTM.CarrySaveSelector.runFrom_complete
    (0 : Fin 5) 1 2 3 (by decide) (by decide) (by decide)
    (childSide (CarrySaveLocal.source carry p).word) (CarrySaveLocal.source carry p).shift
    (storage (input := input) height bits path unary frontier status) rfl
    height bits path rfl rfl rfl rfl rfl rfl
  dsimp only [baseSelector, selectorClock, baseConfig, Cfg.withState] at ⊢
  simp only [MultiTapeTM.outCfg, Cfg.withState] at hr ⊢
  rw [hr]
  clear hr
  apply Cfg.ext
  · rfl
  · rfl
  · funext i x
    cases x with
    | ofNat n =>
      cases n <;> fin_cases i <;>
        simp [storage, lastCases_small, lastCases_top, tapeOfList, Function.update_apply,
          ← Int.natCast_succ, -Nat.succ_eq_add_one, -Nat.cast_add, -Nat.cast_one]
    | negSucc n =>
      fin_cases i <;>
        simp [storage, lastCases_small, lastCases_top, tapeOfList, Function.update_apply]
  · funext i
    fin_cases i <;> simp [storage, lastCases_small, lastCases_top]
  · rfl

/-- Query tapes embedded beside arbitrary private leaf storage. -/
def config {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (scratch : Scratch k := .blank k) :
    Cfg (k + 6) Bool Unit input :=
  MultiTapeTM.embed (coreEmb k) (baseConfig height bits path unary frontier status)
    scratch.tapes scratch.positions

variable {scratch : Scratch k}

/-- The represented query has no acceptance output before its terminal branch. -/
@[simp] theorem config_output {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier status).output =
      [] := by
  simp [config, MultiTapeTM.embed, baseConfig, MultiTapeTM.outCfg]

private theorem not_mem_coreEmb (i : Fin (k + 6)) (hi : 6 ≤ i.val) :
    i ∉ Set.range (coreEmb k) := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have hb := j.isLt
  change j.val = i.val at hv
  omega

/-- A private tape keeps its supplied contents in every represented query configuration. -/
@[simp] theorem config_extra_tape {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (i : Fin (k + 6)) (hi : 6 ≤ i.val) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
        status).workTapes i =
      scratch.tapes i := by
  simp [config, MultiTapeTM.embed, MultiTapeTM.partialInv_eq_none _ (not_mem_coreEmb i hi)]

/-- The supplied private head positions are preserved alongside their tapes. -/
@[simp] theorem config_extra_head {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (i : Fin (k + 6)) (hi : 6 ≤ i.val) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
        status).workTapePos i =
      scratch.positions i := by
  simp [config, MultiTapeTM.embed, MultiTapeTM.partialInv_eq_none _ (not_mem_coreEmb i hi)]

/-- Embedding preserves the selector's certified run and all private tapes and cursors. -/
theorem runFrom_selector {input : List Bool} (carry : Bool) (p : Fin 7)
    (height bits path unary : List Bool) (frontier : ℤ) (status : Bool) :
    (selector (k := k) carry p).runFrom
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).withState
        (some (selector (k := k) carry p).q₀)) (selectorClock carry p height bits) =
      (config (scratch := scratch) (Cslib.BitString.decrement height)
        (Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits)
        (path ++ [childSide (CarrySaveLocal.source carry p).word]) unary frontier
        ((MultiTapeTM.CarrySaveSelector.resultFlags height bits
          (CarrySaveLocal.source carry p).shift).contains true)).withState none := by
  have h := runFrom_baseSelector (input := input) carry p height bits path unary frontier status
  have he := MultiTapeTM.runFrom_map
    (MultiTapeTM.embedHom (baseSelector carry p) (coreEmb k) scratch.tapes scratch.positions)
    ((baseConfig (input := input) height bits path unary frontier status).withState
      (some (baseSelector carry p).q₀)) (selectorClock carry p height bits)
  rw [h] at he
  simpa only [MultiTapeTM.embedHom_apply, selector, config, MultiTapeTM.embed, Cfg.withState,
    MultiTapeTM.extendTapes_q₀] using he

/-- A selector's clock is paid by a constant and the decrease in the zero-bit potential.
This local inequality telescopes along the actual cyclic execution, including wraparound. -/
theorem selectorClock_add_potential_le (carry : Bool) (p : Fin 7) (height bits : List Bool) :
    selectorClock carry p height bits + 2 * (Cslib.BitString.decrement height).count false +
      2 * (Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits).count false ≤
      28 + 2 * height.count false + 2 * bits.count false := by
  have hh := Cslib.BitString.decrementVisits_add_count_false_le height
  have hz := MultiTapeTM.BinaryDecrement.zeros_le_visits height
  have hb := Cslib.BitString.decrementCost_add_count_false_le
    (CarrySaveLocal.source carry p).shift.val bits
  have hc := MultiTapeTM.BinaryDecrement.totalClock_le_visits
    (CarrySaveLocal.source carry p).shift.val bits
  have hs := (CarrySaveLocal.source carry p).shift.isLt
  unfold selectorClock
  omega

/-- Selection really runs inside the cyclic controller. Its deterministic phase reaches the
returned state with exactly the certified native selector's output storage. -/
theorem exists_selector_phase {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry : Bool) (p : Fin 7) (bit : Bool) {input : List Bool}
    (cfg : Cfg (k + 6) Bool (SelectorState carry p) input) (t : ℕ)
    (ht : ((selector (k := k) carry p).runFrom cfg t).state = none) :
    let lift := fun c : Cfg (k + 6) Bool (SelectorState carry p) input =>
      c.mapState (fun q => some (selectorStateMap carry p bit q))
    ∃ τ ≤ t,
      (∀ j < τ, ∀ b, (machine leaf carry bit).next b
        (((machine leaf carry bit).next false)^[j] (lift cfg)) =
          ((machine leaf carry bit).next false)^[j + 1] (lift cfg)) ∧
      (∀ j ≤ τ, (((machine leaf carry bit).next false)^[j] (lift cfg)).state ≠ none) ∧
      ((machine leaf carry bit).next false)^[τ] (lift cfg) =
        lift ((selector (k := k) carry p).runFrom cfg t) := by
  exact exists_deterministic_phase (machine leaf carry bit) _
    (fun move c h => next_selector leaf carry p bit move c h) (by intros; simp) ht

private theorem haltsWithin_initial {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry claim carry' claim' : Bool)
    {input : List Bool} (cfg : Cfg (k + 6) Bool (State S) input) (n : ℕ) :
    (machine leaf carry claim).HaltsWithin n cfg ↔
      (machine leaf carry' claim').HaltsWithin n cfg :=
  (haltsWithin_continuation leaf false 0 false carry claim cfg n).symm.trans
    (haltsWithin_continuation leaf false 0 false carry' claim' cfg n)

/-- A physical selector followed by any bounded return continuation has their summed bound.
The actual handoff may occur earlier than the certified selector clock. -/
theorem haltsWithin_selector {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry : Bool) (p : Fin 7) (bit : Bool) {input : List Bool}
    (cfg post : Cfg (k + 6) Bool (SelectorState carry p) input) (t n : ℕ)
    (hrun : (selector (k := k) carry p).runFrom cfg t = post) (hpost : post.state = none)
    (hreturn : (machine leaf carry bit).HaltsWithin n
      (post.mapState (fun q => some (selectorStateMap carry p bit q)))) :
    (machine leaf carry bit).HaltsWithin (t + n)
      (cfg.mapState (fun q => some (selectorStateMap carry p bit q))) := by
  obtain ⟨τ, hτ, hdet, hlive, hend⟩ := exists_selector_phase leaf carry p bit cfg t
    (by rw [hrun]; exact hpost)
  rw [hrun] at hend
  exact (haltsWithin_iff_of_phase hdet hlive hend (t + n)).mpr
    ⟨by omega, hreturn.mono (by omega)⟩

/-- The uniform time budget uses the actual zero-bit potential, so it decreases through
native borrow scans rather than charging the full counter width on every layer. -/
@[expose] def budget (leafTime depth : ℕ) (height bits : List Bool) : ℕ :=
  40 * depth + 2 * height.count false + 2 * bits.count false + leafTime + 1

/-- Twelve control transitions surround one selector: unary test, table dispatch, and return. -/
theorem selectorClock_budget (leafTime depth : ℕ) (carry : Bool) (p : Fin 7)
    (height bits : List Bool) :
    12 + selectorClock carry p height bits +
      budget leafTime depth (Cslib.BitString.decrement height)
        (Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits) ≤
      budget leafTime (depth + 1) height bits := by
  have h := selectorClock_add_potential_le carry p height bits
  unfold budget
  omega

/-- At entry the entire potential is bounded by the two binary counter widths. -/
theorem budget_le (leafTime depth : ℕ) (height bits : List Bool) :
    budget leafTime depth height bits ≤
      40 * depth + 2 * height.length + 2 * bits.length + leafTime + 1 := by
  have hh := List.count_le_length (a := false) (l := height)
  have hb := List.count_le_length (a := false) (l := bits)
  unfold budget
  omega

/-- The unary frontier has exactly `depth` true cells left, followed by blanks. Its consumed
prefix is arbitrary and is never scanned by the controller. -/
@[expose] def Frontier (unary : List Bool) (frontier : ℤ) (depth : ℕ) : Prop :=
  ∀ j : ℕ, tapeOfList unary (frontier + j) = if j < depth then some true else none

private theorem Frontier.succ {unary : List Bool} {frontier : ℤ} {depth : ℕ}
    (h : Frontier unary frontier (depth + 1)) : Frontier unary (frontier + 1) depth := by
  intro j
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h (j + 1)

private theorem config_unary {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
        status).workTapes (coreEmb k 4)
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).workTapePos (coreEmb k 4)) =
      tapeOfList unary frontier := by
  simp [config, baseConfig, storage, MultiTapeTM.outCfg, lastCases_small]

private theorem config_status {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
        status).workTapes (coreEmb k 3)
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).workTapePos (coreEmb k 3)) =
      some status := by
  simp [config, baseConfig, storage, MultiTapeTM.outCfg, lastCases_small, tapeOfList]

private theorem next_header_config {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (carry claim move : Bool) {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) (h : tapeOfList unary frontier = some true) :
    (machine leaf carry claim).next move
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).withState
        (some (.header carry claim))) =
      (config (scratch := scratch) height bits path unary (frontier + 1) status).withState
        (some (.table carry claim .guess₀)) := by
  rw [next_header_layer leaf carry claim move _ (by rwa [config_unary])]
  apply Cfg.ext <;> try rfl
  funext j
  by_cases hj : j ∈ Set.range (coreEmb k)
  · obtain ⟨i, rfl⟩ := hj
    fin_cases i <;> simp [config, baseConfig, storage, MultiTapeTM.outCfg, Cfg.withState,
      lastCases_small, lastCases_top]
  · have hne : j ≠ coreEmb k 4 := fun h => hj ⟨4, h.symm⟩
    simp [config, MultiTapeTM.embed, MultiTapeTM.partialInv_eq_none _ hj, hne]

/-- A native leaf-family bound on the physical zero-layer representation. This is the only
external runtime contract: all compressor layers and their persistent updates run in `machine`.
The fixed private storage may, for example, contain a prepared query or blank scratch tapes. -/
@[expose] def LeafBound {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (leafTime sizeBudget : ℕ) (input : List Bool) (scratch : Scratch k := .blank k) : Prop :=
  ∀ (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool),
    Frontier unary frontier 0 → height.length + bits.length + path.length ≤ sizeBudget →
      (leaf carry claim).HaltsWithin leafTime
        ((config (scratch := scratch) (input := input) height bits path unary frontier
            status).withState
          (some (leaf carry claim).toPTM.toNTM.q₀))

private theorem length_decrements (n : ℕ) (w : List Bool) :
    (Cslib.BitString.decrement^[n] w).length = w.length := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply, ih]

/-- The finite cyclic controller halts on every branch in linear time in the number of layers
and the initial binary counter widths, plus the native leaf time. Incorrect guesses, missing
children, selector cleanup and unary leaf detection are included. -/
theorem haltsWithin_budget {S : Type} (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (leafTime sizeBudget : ℕ) {input : List Bool}
    (hleaf : LeafBound leaf leafTime sizeBudget input scratch)
    (depth : ℕ) (height bits path unary : List Bool) (frontier : ℤ)
    (status carry claim : Bool) (hfront : Frontier unary frontier depth)
    (hsize : height.length + bits.length + path.length + depth ≤ sizeBudget) :
    (machine leaf carry claim).HaltsWithin (budget leafTime depth height bits)
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).withState
        (some (.header carry claim))) := by
  induction depth generalizing height bits path unary frontier status carry claim with
  | zero =>
    have hleaf' := hleaf height bits path unary frontier status carry claim hfront
      (by simpa using hsize)
    have hs := (leafSimulation leaf carry claim).haltsWithin_iff leafTime
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).withState
        (some (leaf carry claim).toPTM.toNTM.q₀)) |>.mpr hleaf'
    have hh : (machine leaf carry claim).HaltsWithin (leafTime + 1)
        ((config (scratch := scratch) (input := input) height bits path unary frontier
            status).withState
          (some (.header carry claim))) := by
      apply haltsWithin_succ.mpr
      intro move
      rw [next_header_leaf leaf carry claim move _ (by
        rw [config_unary]; simpa using hfront 0)]
      exact hs
    exact hh.mono (by unfold budget; omega)
  | succ depth ih =>
    let N := budget leafTime (depth + 1) height bits - 11
    have hN : N + 10 + 1 = budget leafTime (depth + 1) height bits := by
      dsimp [N, budget]; omega
    rw [← hN]
    apply haltsWithin_succ.mpr
    intro move
    rw [next_header_config (scratch := scratch) leaf carry claim move height bits path unary
        frontier status
      (by simpa using hfront 0)]
    apply haltsWithin_table leaf carry claim _ N
    intro p bit
    let h' := Cslib.BitString.decrement height
    let b' := Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits
    let p' := path ++ [childSide (CarrySaveLocal.source carry p).word]
    let c' := childCarry (CarrySaveLocal.source carry p).word
    let flag := (MultiTapeTM.CarrySaveSelector.resultFlags height bits
      (CarrySaveLocal.source carry p).shift).contains true
    let post : Cfg (k + 6) Bool Unit input := config (scratch := scratch) h' b' p' unary
        (frontier + 1) flag
    have hb := ih h' b' p' unary (frontier + 1) flag c' bit hfront.succ
      (by simpa [h', b', p', length_decrements, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hsize)
    have hr : (machine leaf carry bit).HaltsWithin (budget leafTime depth h' b' + 1)
        (post.withState (some (.returned c' bit))) := by
      apply (haltsWithin_initial leaf c' bit carry bit _ _).mp
      apply haltsWithin_succ.mpr
      intro m
      cases hf : flag with
      | false =>
        rw [next_returned_valid leaf c' bit m post (by
          dsimp [post]; rw [config_status, hf])]
        exact hb
      | true =>
        rw [next_returned_absent leaf c' bit m post (by
          dsimp [post]; rw [config_status, hf])]
        apply haltsWithin_of_halted
        rfl
    have hs := haltsWithin_selector leaf carry p bit
      ((config (scratch := scratch) (input := input) height bits path unary (frontier + 1)
          status).withState
        (some (selector (k := k) carry p).q₀)) (post.withState none)
      (selectorClock carry p height bits) (budget leafTime depth h' b' + 1)
      (runFrom_selector carry p height bits path unary (frontier + 1) status) rfl hr
    have hcost := selectorClock_budget leafTime depth carry p height bits
    apply (haltsWithin_continuation leaf carry p bit carry bit _ N).mpr
    exact hs.mono (by dsimp [N, h', b']; omega)

private theorem acceptsWithin_initial {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (carry claim carry' claim' : Bool)
    {input : List Bool} (cfg : Cfg (k + 6) Bool (State S) input) (n : ℕ) :
    (machine leaf carry claim).AcceptsWithin n cfg ↔
      (machine leaf carry' claim').AcceptsWithin n cfg :=
  (acceptsWithin_continuation leaf false 0 false carry claim cfg n).symm.trans
    (acceptsWithin_continuation leaf false 0 false carry' claim' cfg n)

private theorem acceptsWithin_stable {S : Type} (atm : MultiTapeATM (k + 6) Bool S)
    {input : List Bool} {cfg : Cfg (k + 6) Bool S input} {n t : ℕ}
    (ht : atm.HaltsWithin t cfg) (hn : t ≤ n) :
    atm.AcceptsWithin n cfg ↔ atm.AcceptsWithin t cfg :=
  ⟨fun h => h.of_halted_stepCoins ht, fun h => h.mono hn⟩

/-- The native leaf machines correctly answer the selected component bit at unary depth zero. -/
@[expose] def LeafCorrect {S : Type} {w : ℕ} (leaves : List Bool → Cslib.BitString (w + w))
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S)
    (leafTime sizeBudget : ℕ) (input : List Bool) (scratch : Scratch k := .blank k) : Prop :=
  ∀ (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool),
    Frontier unary frontier 0 → height.length + bits.length + path.length ≤ sizeBudget →
    Cslib.BitString.lsbValue bits < w →
      ((leaf carry claim).AcceptsWithin leafTime
        ((config (scratch := scratch) (input := input) height bits path unary frontier
            status).withState
          (some (leaf carry claim).toPTM.toNTM.q₀)) ↔
        value leaves ⟨path, 0, carry, Cslib.BitString.lsbValue bits⟩ = claim)

/-- The cyclic physical evaluator answers a streamed compressor query. The only semantic
contract concerns native zero-layer leaf machines; all positive-height descent is implemented
by the finite controller, its in-place selector and its amortized clock. -/
theorem acceptsWithin_budget {S : Type} {w : ℕ}
    (leaves : List Bool → Cslib.BitString (w + w))
    (leaf : Bool → Bool → MultiTapeATM (k + 6) Bool S) (leafTime sizeBudget : ℕ) {input : List Bool}
    (hleafTime : LeafBound leaf leafTime sizeBudget input scratch)
    (hleaf : LeafCorrect leaves leaf leafTime sizeBudget input scratch)
    (depth : ℕ) (height bits path unary : List Bool) (frontier : ℤ)
    (status carry claim : Bool) (hfront : Frontier unary frontier depth)
    (hsize : height.length + bits.length + path.length + depth ≤ sizeBudget)
    (hheight : Cslib.BitString.lsbValue height = depth)
    (hbits : Cslib.BitString.lsbValue bits < w) :
    (machine leaf carry claim).AcceptsWithin (budget leafTime depth height bits)
      ((config (scratch := scratch) (input := input) height bits path unary frontier
          status).withState
        (some (.header carry claim))) ↔
      value leaves ⟨path, depth, carry, Cslib.BitString.lsbValue bits⟩ = claim := by
  induction depth generalizing height bits path unary frontier status carry claim with
  | zero =>
    have ht := hleafTime height bits path unary frontier status carry claim hfront
      (by simpa using hsize)
    have hh : (machine leaf carry claim).HaltsWithin (leafTime + 1)
        ((config (scratch := scratch) (input := input) height bits path unary frontier
            status).withState
          (some (.header carry claim))) := by
      apply haltsWithin_succ.mpr
      intro m
      rw [next_header_leaf leaf carry claim m _ (by rw [config_unary]; simpa using hfront 0)]
      exact (leafSimulation leaf carry claim).haltsWithin_iff leafTime
        ((config (scratch := scratch) (input := input) height bits path unary frontier
            status).withState
          (some (leaf carry claim).toPTM.toNTM.q₀)) |>.mpr ht
    rw [acceptsWithin_stable _ hh (by unfold budget; omega)]
    rw [acceptsWithin_header_leaf leaf carry claim _ leafTime
      (by rw [config_unary]; simpa using hfront 0)]
    exact hleaf height bits path unary frontier status carry claim hfront
      (by simpa using hsize) hbits
  | succ depth ih =>
    let N := budget leafTime (depth + 1) height bits - 11
    have hN : N + 10 + 1 = budget leafTime (depth + 1) height bits := by
      dsimp [N, budget]; omega
    rw [← hN, acceptsWithin_succ_of_next_eq
      (fun move => next_header_config (scratch := scratch) leaf carry claim move height bits
          path unary frontier status
        (by simpa using hfront 0))]
    rw [acceptsWithin_table leaf carry claim _ rfl N]
    have hchild (p : Fin 7) (bit : Bool) :
        (continuation leaf carry p bit).AcceptsWithin N
          ((config (scratch := scratch) (input := input) height bits path unary (frontier + 1)
              status).withState
            (some (.select carry p bit (selector (k := k) carry p).q₀))) ↔
          (descend ⟨path, depth + 1, carry, Cslib.BitString.lsbValue bits⟩ p).elim false
            (value leaves) = bit := by
      let h' := Cslib.BitString.decrement height
      let b' := Cslib.BitString.decrement^[(CarrySaveLocal.source carry p).shift.val] bits
      let p' := path ++ [childSide (CarrySaveLocal.source carry p).word]
      let c' := childCarry (CarrySaveLocal.source carry p).word
      let flag := (MultiTapeTM.CarrySaveSelector.resultFlags height bits
        (CarrySaveLocal.source carry p).shift).contains true
      let post : Cfg (k + 6) Bool Unit input := config (scratch := scratch) h' b' p' unary
          (frontier + 1) flag
      have hr := runFrom_selector (scratch := scratch) (input := input) carry p height bits path
          unary
        (frontier + 1) status
      obtain ⟨τ, hτ, hdet, hlive, hend⟩ := exists_selector_phase leaf carry p bit
        ((config (scratch := scratch) (input := input) height bits path unary (frontier + 1)
            status).withState
          (some (selector (k := k) carry p).q₀)) (selectorClock carry p height bits)
        (by rw [hr]; rfl)
      rw [hr] at hend
      have hcost := selectorClock_budget leafTime depth carry p height bits
      have hrem : budget leafTime depth h' b' + 1 ≤ N - τ := by
        dsimp [N, h', b']; omega
      rw [acceptsWithin_continuation leaf carry p bit carry bit _ N]
      have hphase := acceptsWithin_iff_of_phase hdet hlive hend N
      change (machine leaf carry bit).AcceptsWithin N
        ((config (scratch := scratch) (input := input) height bits path unary (frontier + 1)
            status).withState
          (some (.select carry p bit (selector (k := k) carry p).q₀))) ↔
        τ ≤ N ∧ (machine leaf carry bit).AcceptsWithin (N - τ)
          (post.withState (some (.returned c' bit))) at hphase
      rw [hphase]
      simp only [show τ ≤ N by omega, true_and]
      change (machine leaf carry bit).AcceptsWithin (N - τ)
        (post.withState (some (.returned c' bit))) ↔ _
      rw [acceptsWithin_initial leaf carry bit c' bit]
      rw [show N - τ = (N - τ - 1) + 1 by omega]
      cases hf : flag with
      | false =>
        rw [acceptsWithin_succ_of_next_eq (fun move =>
          next_returned_valid leaf c' bit move post (by dsimp [post]; rw [config_status, hf]))]
        have ht := haltsWithin_budget leaf leafTime sizeBudget hleafTime depth h' b' p' unary
          (frontier + 1) flag c' bit hfront.succ
          (by simpa [h', b', p', length_decrements, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hsize)
        rw [acceptsWithin_stable _ ht (by omega)]
        have hvalid :
            (CarrySaveLocal.source carry p).shift.val ≤ Cslib.BitString.lsbValue bits := by
          have hv := (MultiTapeTM.CarrySaveSelector.resultFlags_valid height bits
            (CarrySaveLocal.source carry p).shift).mp
            (by simpa [flag, List.contains_eq_mem] using hf)
          exact hv.2
        have hh' : Cslib.BitString.lsbValue h' = depth := by
          dsimp [h']; rw [Cslib.BitString.lsbValue_decrement height (by omega), hheight]; omega
        have hb' : Cslib.BitString.lsbValue b' = Cslib.BitString.lsbValue bits -
            (CarrySaveLocal.source carry p).shift.val :=
          Cslib.BitString.lsbValue_iterate_decrement _ bits hvalid
        rw [ih h' b' p' unary (frontier + 1) flag c' bit hfront.succ
          (by simpa [h', b', p', length_decrements, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hsize) hh' (by omega)]
        simp [descend, hvalid, p', c', hb']
      | true =>
        rw [acceptsWithin_succ_of_next_eq (fun move =>
          next_returned_absent leaf c' bit move post (by dsimp [post]; rw [config_status, hf]))]
        rw [acceptsWithin_of_halted _ rfl]
        have hinvalid : ¬(CarrySaveLocal.source carry p).shift.val ≤
            Cslib.BitString.lsbValue bits := by
          intro hv
          have hnot := (MultiTapeTM.CarrySaveSelector.resultFlags_valid height bits
            (CarrySaveLocal.source carry p).shift).mpr ⟨by omega, hv⟩
          simp [flag, List.contains_eq_mem, hnot] at hf
        simp [post, descend, hinvalid]
    simp only [hchild]
    rw [value_layer leaves path depth carry ⟨Cslib.BitString.lsbValue bits, hbits⟩]
    constructor
    · rintro ⟨v, hv, hvals⟩
      have he : (fun p => (descend ⟨path, depth + 1, carry,
          Cslib.BitString.lsbValue bits⟩ p).elim false (value leaves)) = v := funext hvals
      rwa [he]
    · intro h
      exact ⟨_, h, fun _ => rfl⟩

/-- The storage representation has no active machine state before a phase is installed. -/
@[simp] theorem config_state {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier status).state =
      none := by
  simp [config, MultiTapeTM.embed, baseConfig, MultiTapeTM.outCfg, storage]

/-- The host input is parked at its left blank during streamed descent. -/
@[simp] theorem config_inputPos {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier status).inputPos =
      0 := by
  simp [config, MultiTapeTM.embed, baseConfig, MultiTapeTM.outCfg, storage]

/-- Controller tape 2 holds the persistent root-to-leaf path. -/
@[simp] theorem config_path_tape {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier status).workTapes
      (coreEmb k 2) = tapeOfList path := by
  simp only [config, MultiTapeTM.embed, MultiTapeTM.partialInv_embed]
  rfl

/-- The persistent path head is parked at its right blank. -/
@[simp] theorem config_path_head {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
      status).workTapePos
      (coreEmb k 2) = path.length := by
  simp only [config, MultiTapeTM.embed, MultiTapeTM.partialInv_embed]
  rfl

/-- Controller tape 1 holds the current little-endian bit-index word. -/
@[simp] theorem config_bits_tape {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier status).workTapes
      (coreEmb k 1) = tapeOfList bits := by
  simp only [config, MultiTapeTM.embed, MultiTapeTM.partialInv_embed]
  rfl

/-- The current bit-index word is ready for reading at its first cell. -/
@[simp] theorem config_bits_head {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    (config (scratch := scratch) (input := input) height bits path unary frontier
      status).workTapePos (coreEmb k 1) = 0 := by
  simp only [config, MultiTapeTM.embed, MultiTapeTM.partialInv_embed]
  rfl

end Turing.MultiTapeATM.CarrySaveStream
