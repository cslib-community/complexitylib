/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import CslibFrontier.Foundations.Data.BiTape
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Equivalence between `SingleTapeTM` and Mathlib's `TM0` and `TM1`

This file bridges CSLib's single-tape Turing machine model (`Cslib.Turing.SingleTapeTM`) with
Mathlib's Post–Turing and Wang B-machine models (`_root_.Turing.TM0` and `_root_.Turing.TM1`) as
well as `StateTransition.eval` and `StateTransition.EvalsToInTime`.

## Main definitions

* `Cslib.Turing.SingleTapeTM.toTM1`: step-exact embedding of a `SingleTapeTM Symbol` into
  `_root_.Turing.TM1`.
* `Cslib.Turing.SingleTapeTM.toTM0`: compilation of a `SingleTapeTM Symbol` into
  `_root_.Turing.TM0` via `_root_.Turing.TM1to0.tr`.
* `Cslib.Turing.SingleTapeTM.ofTM0`: compilation of a finitely supported
  `_root_.Turing.TM0.Machine (Option Symbol) Λ` into a `SingleTapeTM Symbol`.
* `Cslib.Turing.SingleTapeTM.ofTM1`: compilation of a finitely supported
  `_root_.Turing.TM1` machine into a `SingleTapeTM Symbol`.

## Main results

* `Cslib.Turing.SingleTapeTM.outputs_iff_mem_eval`: `tm.Outputs l l'` holds if and only if
  `tm.haltCfg l' ∈ StateTransition.eval tm.step (tm.initCfg l)`.
* `Cslib.Turing.SingleTapeTM.outputsWithinTime_iff_evalsToInTime`: `tm.OutputsWithinTime l l' m`
  holds if and only if
  `StateTransition.EvalsToInTime tm.step (tm.initCfg l) (some (tm.haltCfg l')) m` is nonempty.
* `Cslib.Turing.SingleTapeTM.map_ofTM1Cfg_step`, `eval_toTM1`, `eval_toTM0_eq_eval_toTM1`: `toTM1`
  is a step-for-step simulation of `tm`, and `toTM0` preserves `eval`.
* `Cslib.Turing.SingleTapeTM.outputsWithinTime_ofTM0_iff`, `outputs_ofTM0_iff`, `eval_ofTM0`,
  `eval_ofTM1`: `ofTM0` preserves step counts, up to one final halting step, and terminal tape
  evaluations; `ofTM1` preserves terminal tape evaluations.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

open Relation StateTransition

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-! ## Connection with `StateTransition` -/

lemma flip_bind_iterate_eq_some_iff {σ : Type*} (f : σ → Option σ) (a b : σ) (n : ℕ) :
    (flip bind f)^[n] (some a) = some b ↔ RelatesInSteps (fun x y => y ∈ f x) a b n := by
  induction n generalizing b with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', RelatesInSteps.succ_iff]
    constructor
    · intro h
      rcases hx : (flip bind f)^[n] (some a) with _ | c
      · rw [hx] at h
        cases h
      · rw [hx] at h
        exact ⟨c, (ih c).mp hx, h⟩
    · rintro ⟨c, hrel, hstep⟩
      rw [(ih c).mpr hrel]
      exact hstep

lemma evalsTo_some_iff_relatesInSteps {σ : Type*} (f : σ → Option σ) (a b : σ) :
    Nonempty (EvalsTo f a (some b)) ↔ ∃ n, RelatesInSteps (fun x y => y ∈ f x) a b n := by
  constructor
  · rintro ⟨⟨n, hn⟩⟩
    exact ⟨n, (flip_bind_iterate_eq_some_iff f a b n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, (flip_bind_iterate_eq_some_iff f a b n).mpr hn⟩⟩

lemma evalsToInTime_some_iff_relatesWithinSteps {σ : Type*} (f : σ → Option σ) (a b : σ) (m : ℕ) :
    Nonempty (EvalsToInTime f a (some b) m) ↔
      RelatesWithinSteps (fun x y => y ∈ f x) a b m := by
  constructor
  · rintro ⟨⟨⟨n, hn⟩, hnm⟩⟩
    exact ⟨n, hnm, (flip_bind_iterate_eq_some_iff f a b n).mp hn⟩
  · rintro ⟨n, hnm, hn⟩
    exact ⟨⟨⟨n, (flip_bind_iterate_eq_some_iff f a b n).mpr hn⟩, hnm⟩⟩

@[simp] lemma step_haltCfg (tm : SingleTapeTM Symbol) (l : List Symbol) :
    tm.step (tm.haltCfg l) = none := rfl

lemma step_some (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.step ⟨some q, t⟩ =
      some ⟨(tm.tr q t.head).2,
        (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩ := by
  simp only [step]

/-- Convert an optional `Turing.Dir` to a `SignType` head movement. -/
def dirToSign : Option _root_.Turing.Dir → SignType
  | none => .zero
  | some .left => .neg
  | some .right => .pos

omit [Inhabited Symbol] [Fintype Symbol] in
lemma biTape_step_dirToSign (t : BiTape Symbol) (wr : Option Symbol)
    (dir : Option _root_.Turing.Dir) :
    t.step (some wr, dirToSign dir) = (t.write wr).optionMove dir := by
  cases dir with
  | none => rfl
  | some d => cases d <;> rfl

/-- `tm.Outputs l l'` holds if and only if `StateTransition.eval tm.step (tm.initCfg l)`
evaluates to `tm.haltCfg l'`. -/
theorem outputs_iff_mem_eval (tm : SingleTapeTM Symbol) (l l' : List Symbol) :
    tm.Outputs l l' ↔ tm.haltCfg l' ∈ StateTransition.eval tm.step (tm.initCfg l) := by
  rw [StateTransition.mem_eval]
  simp only [Outputs, StateTransition.Reaches, Option.mem_def, step_haltCfg, and_true]
  rfl

/-- `tm.OutputsWithinTime l l' m` holds if and only if `StateTransition.EvalsToInTime` reaches
`some (tm.haltCfg l')` in at most `m` steps. -/
theorem outputsWithinTime_iff_evalsToInTime (tm : SingleTapeTM Symbol) (l l' : List Symbol)
    (m : ℕ) :
    tm.OutputsWithinTime l l' m ↔
      Nonempty (EvalsToInTime tm.step (tm.initCfg l) (some (tm.haltCfg l')) m) :=
  (evalsToInTime_some_iff_relatesWithinSteps tm.step (tm.initCfg l) (tm.haltCfg l') m).symm

/-! ## Embedding `SingleTapeTM` into Mathlib's `TM1` and `TM0` -/

/-- Branching helper for optional head movement in `TM1` using the stored head symbol. -/
def moveStmt (tm : SingleTapeTM Symbol) (q : tm.State)
    (next : _root_.Turing.TM1.Stmt (Option Symbol) tm.State (Option Symbol)) :
    _root_.Turing.TM1.Stmt (Option Symbol) tm.State (Option Symbol) :=
  .branch (fun _ v => (tm.tr q v).1.movement == some .left)
    (.move .left next)
    (.branch (fun _ v => (tm.tr q v).1.movement == some .right)
      (.move .right next)
      next)

/-- Next-state helper in `TM1` using the stored head symbol. -/
def nextStmt (tm : SingleTapeTM Symbol) (q : tm.State) :
    _root_.Turing.TM1.Stmt (Option Symbol) tm.State (Option Symbol) :=
  .branch (fun _ v => (tm.tr q v).2.isSome)
    (.goto fun _ v => (tm.tr q v).2.getD tm.q₀)
    .halt

/-- Step-exact embedding of a `SingleTapeTM Symbol` into Mathlib's `_root_.Turing.TM1`.
Each step loads the current tape head into the local store `Option Symbol`, writes the new symbol,
performs the optional move, and transitions to the next state (or halts), all in a single `TM1`
step. -/
def toTM1 (tm : SingleTapeTM Symbol) (q : tm.State) :
    _root_.Turing.TM1.Stmt (Option Symbol) tm.State (Option Symbol) :=
  .load (fun a _ => a) <|
    .write (fun _ v => (tm.tr q v).1.symbol) <|
      moveStmt tm q (nextStmt tm q)

/-- Forgetful projection from `TM1` configurations to `SingleTapeTM` configurations. -/
def ofTM1Cfg (tm : SingleTapeTM Symbol)
    (c : _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol)) : tm.Cfg :=
  ⟨c.l, BiTape.equivTape.symm c.Tape⟩

/-- Lift a `SingleTapeTM` configuration to a `TM1` configuration with local variable `v`. -/
def toTM1Cfg (tm : SingleTapeTM Symbol) (c : tm.Cfg) (v : Option Symbol := none) :
    _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol) :=
  ⟨c.state, v, BiTape.equivTape c.BiTape⟩

@[simp] lemma ofTM1Cfg_toTM1Cfg (tm : SingleTapeTM Symbol) (c : tm.Cfg) (v : Option Symbol) :
    tm.ofTM1Cfg (tm.toTM1Cfg c v) = c := by
  cases c
  simp [ofTM1Cfg, toTM1Cfg]

@[simp] lemma toTM1Cfg_initCfg (tm : SingleTapeTM Symbol) (l : List Symbol) :
    tm.toTM1Cfg (tm.initCfg l) none = _root_.Turing.TM1.init (l.map some) := by
  simp [toTM1Cfg, initCfg, _root_.Turing.TM1.init, default]

@[simp] lemma ofTM1Cfg_init (tm : SingleTapeTM Symbol) (l : List Symbol) :
    tm.ofTM1Cfg (_root_.Turing.TM1.init (l.map some)) = tm.initCfg l := by
  rw [← toTM1Cfg_initCfg, ofTM1Cfg_toTM1Cfg]

lemma stepAux_nextStmt (tm : SingleTapeTM Symbol) (q : tm.State) (v : Option Symbol)
    (T : _root_.Turing.Tape (Option Symbol)) :
    _root_.Turing.TM1.stepAux (nextStmt tm q) v T = ⟨(tm.tr q v).2, v, T⟩ := by
  unfold nextStmt
  rcases h : (tm.tr q v).2 with _ | q' <;> simp [_root_.Turing.TM1.stepAux, h]

lemma stepAux_moveStmt (tm : SingleTapeTM Symbol) (q : tm.State) (v : Option Symbol)
    (T : _root_.Turing.Tape (Option Symbol)) :
    _root_.Turing.TM1.stepAux (moveStmt tm q (nextStmt tm q)) v T =
      ⟨(tm.tr q v).2, v, ( (tm.tr q v).1.movement ).elim T (fun d => T.move d)⟩ := by
  unfold moveStmt
  rcases h : (tm.tr q v).1.movement with _ | d
  · simp [_root_.Turing.TM1.stepAux, h, stepAux_nextStmt]
  · cases d <;> simp [_root_.Turing.TM1.stepAux, h, stepAux_nextStmt]

/-- One step of `tm.toTM1` on a lifted configuration `tm.toTM1Cfg c v` takes exactly one step of
`tm` and updates the local store to `c.BiTape.head`. -/
theorem step_toTM1 (tm : SingleTapeTM Symbol)
    (c : _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol)) :
    _root_.Turing.TM1.step tm.toTM1 c =
      (tm.step (tm.ofTM1Cfg c)).map fun c' => tm.toTM1Cfg c' c.Tape.1 := by
  rcases c with ⟨_ | q, v, T⟩
  · rfl
  · simp only [_root_.Turing.TM1.step, toTM1, _root_.Turing.TM1.stepAux, stepAux_moveStmt,
      ofTM1Cfg, step_some, BiTape.head_equivTape_symm, Option.map_some, toTM1Cfg,
      BiTape.equivTape_optionMove, BiTape.equivTape_write, Equiv.apply_symm_apply]

/-- `ofTM1Cfg` commutes with a single step of `TM1.step tm.toTM1` and `tm.step`. -/
@[simp] theorem map_ofTM1Cfg_step (tm : SingleTapeTM Symbol)
    (c : _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol)) :
    (_root_.Turing.TM1.step tm.toTM1 c).map tm.ofTM1Cfg = tm.step (tm.ofTM1Cfg c) := by
  rw [step_toTM1, Option.map_map]
  cases tm.step (tm.ofTM1Cfg c) <;> simp [Function.comp]

theorem respects_toTM1_ofTM1Cfg (tm : SingleTapeTM Symbol) :
    Respects (_root_.Turing.TM1.step tm.toTM1) tm.step
      (fun c₁ c₂ => tm.ofTM1Cfg c₁ = c₂) := by
  rw [fun_respects]
  intro c
  rcases h : _root_.Turing.TM1.step tm.toTM1 c with _ | c'
  · simp only [FRespects]
    have hstep := map_ofTM1Cfg_step tm c
    rw [h, Option.map_none] at hstep
    exact hstep.symm
  · simp only [FRespects]
    apply TransGen.single
    rw [← map_ofTM1Cfg_step, h, Option.map_some, Option.mem_def]

theorem eval_ofTM1Cfg (tm : SingleTapeTM Symbol)
    (c : _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol)) :
    StateTransition.eval tm.step (tm.ofTM1Cfg c) =
      tm.ofTM1Cfg <$> StateTransition.eval (_root_.Turing.TM1.step tm.toTM1) c :=
  tr_eval' (_root_.Turing.TM1.step tm.toTM1) tm.step tm.ofTM1Cfg
    (respects_toTM1_ofTM1Cfg tm) c

/-- Running `tm.toTM1` from `TM1.init (l.map some)` and projecting via `ofTM1Cfg` agrees with
`StateTransition.eval tm.step (tm.initCfg l)`. -/
theorem eval_toTM1 (tm : SingleTapeTM Symbol) (l : List Symbol) :
    tm.ofTM1Cfg <$>
      StateTransition.eval (_root_.Turing.TM1.step tm.toTM1) (_root_.Turing.TM1.init (l.map some)) =
      StateTransition.eval tm.step (tm.initCfg l) := by
  simpa using (eval_ofTM1Cfg tm (_root_.Turing.TM1.init (l.map some))).symm

/-- If `tm` outputs `l'` on input `l`, then `tm.toTM1` evaluates `(l.map some)` to
`ListBlank.mk (l'.map some)`. -/
theorem outputs_imp_mem_eval_toTM1 (tm : SingleTapeTM Symbol) {l l' : List Symbol}
    (h : tm.Outputs l l') :
    _root_.Turing.ListBlank.mk (l'.map some) ∈
      _root_.Turing.TM1.eval tm.toTM1 (l.map some) := by
  have heval : tm.haltCfg l' ∈ StateTransition.eval tm.step (tm.initCfg l) :=
    (outputs_iff_mem_eval tm l l').mp h
  rw [← eval_toTM1] at heval
  rcases (Part.mem_map_iff _).mp heval with ⟨c, hc, hcfg⟩
  rw [_root_.Turing.TM1.eval, Part.mem_map_iff]
  refine ⟨c, hc, ?_⟩
  have hTape : BiTape.equivTape.symm c.Tape = BiTape.mk₁ l' := congrArg Cfg.BiTape hcfg
  have hTape' : c.Tape = _root_.Turing.Tape.mk₁ (l'.map some) := by
    rw [← BiTape.equivTape_mk₁, ← hTape, Equiv.apply_symm_apply]
  rw [hTape', _root_.Turing.Tape.mk₁, _root_.Turing.Tape.mk₂, _root_.Turing.Tape.mk'_right₀]

theorem relatesInSteps_toTM1 (tm : SingleTapeTM Symbol) {c₁ c₂ : tm.Cfg} {n : ℕ}
    (h : RelatesInSteps tm.TransitionRelation c₁ c₂ n) (v : Option Symbol) :
    ∃ v', RelatesInSteps (fun a b => b ∈ _root_.Turing.TM1.step tm.toTM1 a)
      (tm.toTM1Cfg c₁ v) (tm.toTM1Cfg c₂ v') n := by
  induction h generalizing v with
  | refl => exact ⟨v, .refl _⟩
  | tail t' t'' m _ h₂ ih =>
    rcases ih v with ⟨v', ih'⟩
    refine ⟨t'.BiTape.head, .tail _ _ _ m ih' ?_⟩
    rw [Option.mem_def, step_toTM1, ofTM1Cfg_toTM1Cfg]
    change (tm.step t').map (fun c' => tm.toTM1Cfg c' t'.BiTape.head) = _
    rw [h₂, Option.map_some]

theorem relatesInSteps_of_toTM1 (tm : SingleTapeTM Symbol)
    {c₁ c₂ : _root_.Turing.TM1.Cfg (Option Symbol) tm.State (Option Symbol)} {n : ℕ}
    (h : RelatesInSteps (fun a b => b ∈ _root_.Turing.TM1.step tm.toTM1 a) c₁ c₂ n) :
    RelatesInSteps tm.TransitionRelation (tm.ofTM1Cfg c₁) (tm.ofTM1Cfg c₂) n := by
  refine h.map tm.ofTM1Cfg ?_
  intro a b hab
  rw [TransitionRelation, ← map_ofTM1Cfg_step, Option.mem_def.mp hab, Option.map_some]

/-- `tm.OutputsWithinTime l l' m` is equivalent to `tm.toTM1` reaching the halted configuration
`tm.toTM1Cfg (tm.haltCfg l') v` in at most `m` steps. -/
theorem outputsWithinTime_iff_evalsToInTime_toTM1 (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (m : ℕ) :
    tm.OutputsWithinTime l l' m ↔
      ∃ v, Nonempty (EvalsToInTime (_root_.Turing.TM1.step tm.toTM1)
        (_root_.Turing.TM1.init (l.map some)) (some (tm.toTM1Cfg (tm.haltCfg l') v)) m) := by
  constructor
  · rintro ⟨n, hnm, hrel⟩
    rcases relatesInSteps_toTM1 tm hrel none with ⟨v, hrel'⟩
    rw [toTM1Cfg_initCfg] at hrel'
    exact ⟨v, (evalsToInTime_some_iff_relatesWithinSteps _ _ _ m).mpr ⟨n, hnm, hrel'⟩⟩
  · rintro ⟨v, heval⟩
    rcases (evalsToInTime_some_iff_relatesWithinSteps _ _ _ m).mp heval with ⟨n, hnm, hrel⟩
    have hrel' := relatesInSteps_of_toTM1 tm hrel
    rw [ofTM1Cfg_init, ofTM1Cfg_toTM1Cfg] at hrel'
    exact ⟨n, hnm, hrel'⟩

theorem toTM1_supports (tm : SingleTapeTM Symbol) :
    _root_.Turing.TM1.Supports tm.toTM1 Finset.univ := by
  refine ⟨Finset.mem_univ _, fun q _ => ?_⟩
  simp only [toTM1, moveStmt, nextStmt, _root_.Turing.TM1.SupportsStmt, Finset.mem_univ,
    implies_true, and_self]

/-- Compilation of `tm : SingleTapeTM Symbol` into a Mathlib `_root_.Turing.TM0.Machine` via
`_root_.Turing.TM1to0.tr`. -/
def toTM0 (tm : SingleTapeTM Symbol) :
    _root_.Turing.TM0.Machine (Option Symbol) (_root_.Turing.TM1to0.Λ' tm.toTM1) :=
  _root_.Turing.TM1to0.tr tm.toTM1

/-- Finite state set supporting `tm.toTM0`. -/
noncomputable def toTM0Stmts (tm : SingleTapeTM Symbol) :
    Finset (_root_.Turing.TM1to0.Λ' tm.toTM1) :=
  _root_.Turing.TM1to0.trStmts tm.toTM1 Finset.univ

theorem toTM0_supports (tm : SingleTapeTM Symbol) :
    _root_.Turing.TM0.Supports tm.toTM0 ↑tm.toTM0Stmts :=
  _root_.Turing.TM1to0.tr_supports tm.toTM1 (toTM1_supports tm)

@[simp] theorem eval_toTM0_eq_eval_toTM1 (tm : SingleTapeTM Symbol)
    (l : List (Option Symbol)) :
    _root_.Turing.TM0.eval tm.toTM0 l = _root_.Turing.TM1.eval tm.toTM1 l :=
  _root_.Turing.TM1to0.tr_eval tm.toTM1 l

/-- If `tm` outputs `l'` on input `l`, then `tm.toTM0` evaluates `(l.map some)` to
`ListBlank.mk (l'.map some)`. -/
theorem outputs_imp_mem_eval_toTM0 (tm : SingleTapeTM Symbol) {l l' : List Symbol}
    (h : tm.Outputs l l') :
    _root_.Turing.ListBlank.mk (l'.map some) ∈
      _root_.Turing.TM0.eval tm.toTM0 (l.map some) := by
  rw [eval_toTM0_eq_eval_toTM1]
  exact outputs_imp_mem_eval_toTM1 tm h

/-! ## Compiling Mathlib's `TM0` and `TM1` to `SingleTapeTM` -/

section OfTM0

variable {Λ : Type} [Inhabited Λ]

/-- Compile a Mathlib `_root_.Turing.TM0.Machine (Option Symbol) Λ` supported on a finite state set
`S : Finset Λ` into a `SingleTapeTM Symbol`.
Each non-halting `TM0` transition (`move d` or `write a'`) executes in 1 `SingleTapeTM` step, and
halting (`M q a = none`) transitions to `none` in 1 step while leaving the tape unchanged. -/
def ofTM0 (M : _root_.Turing.TM0.Machine (Option Symbol) Λ) (S : Finset Λ)
    [DecidablePred (· ∈ S)] (hs : _root_.Turing.TM0.Supports M ↑S) : SingleTapeTM Symbol where
  State := { q : Λ // q ∈ S }
  stateFintype := Finset.fintypeCoeSort S
  q₀ := ⟨default, hs.1⟩
  tr q a :=
    match M q.1 a with
    | none => (⟨a, none⟩, none)
    | some (q', .move d) =>
      (⟨a, some d⟩, some (if hq' : q' ∈ S then ⟨q', hq'⟩ else ⟨default, hs.1⟩))
    | some (q', .write a') =>
      (⟨a', none⟩, some (if hq' : q' ∈ S then ⟨q', hq'⟩ else ⟨default, hs.1⟩))

variable (M : _root_.Turing.TM0.Machine (Option Symbol) Λ) (S : Finset Λ)
  [DecidablePred (· ∈ S)] (hs : _root_.Turing.TM0.Supports M ↑S)

/-- Translate a `TM0` configuration with state in `S` to an active `(ofTM0 M S hs).Cfg`. -/
def ofTM0Cfg (c : _root_.Turing.TM0.Cfg (Option Symbol) Λ) (hq : c.q ∈ S) :
    (ofTM0 M S hs).Cfg :=
  ⟨some ⟨c.q, hq⟩, BiTape.equivTape.symm c.Tape⟩

@[simp] lemma ofTM0Cfg_init (l : List Symbol) :
    ofTM0Cfg M S hs (_root_.Turing.TM0.init (l.map some)) hs.1 =
      (ofTM0 M S hs).initCfg l := by
  simp [ofTM0Cfg, _root_.Turing.TM0.init, initCfg, ofTM0]

lemma step_ofTM0Cfg (c : _root_.Turing.TM0.Cfg (Option Symbol) Λ) (hq : c.q ∈ S) :
    (ofTM0 M S hs).step (ofTM0Cfg M S hs c hq) =
      some ⟨((ofTM0 M S hs).tr ⟨c.q, hq⟩ c.Tape.head).2,
        ((BiTape.equivTape.symm c.Tape).write
          ((ofTM0 M S hs).tr ⟨c.q, hq⟩ c.Tape.head).1.symbol).optionMove
          ((ofTM0 M S hs).tr ⟨c.q, hq⟩ c.Tape.head).1.movement⟩ := rfl

lemma step_ofTM0Cfg_of_some {c c' : _root_.Turing.TM0.Cfg (Option Symbol) Λ} (hq : c.q ∈ S)
    (hstep : _root_.Turing.TM0.step M c = some c') :
    (ofTM0 M S hs).step (ofTM0Cfg M S hs c hq) =
      some (ofTM0Cfg M S hs c' (_root_.Turing.TM0.step_supports M hs hstep hq)) := by
  rcases c with ⟨q, T⟩
  simp only [_root_.Turing.TM0.step, Option.map_eq_some_iff] at hstep
  rcases hstep with ⟨⟨q', stmt⟩, hM, rfl⟩
  have hq' : q' ∈ S := hs.2 hM hq
  rw [step_ofTM0Cfg]
  cases stmt with
  | move d =>
    have htr : (ofTM0 M S hs).tr ⟨q, hq⟩ T.head =
        (⟨T.head, some d⟩, some ⟨q', hq'⟩) := by
      simp [ofTM0, hM, hq']
    rw [htr]
    simp [ofTM0Cfg, BiTape.optionMove, ← BiTape.head_equivTape_symm]
  | write a' =>
    have htr : (ofTM0 M S hs).tr ⟨q, hq⟩ T.head =
        (⟨a', none⟩, some ⟨q', hq'⟩) := by
      simp [ofTM0, hM, hq']
    rw [htr]
    simp [ofTM0Cfg, BiTape.optionMove]

lemma step_ofTM0Cfg_of_none {c : _root_.Turing.TM0.Cfg (Option Symbol) Λ} (hq : c.q ∈ S)
    (hstep : _root_.Turing.TM0.step M c = none) :
    (ofTM0 M S hs).step (ofTM0Cfg M S hs c hq) =
      some ⟨none, BiTape.equivTape.symm c.Tape⟩ := by
  rcases c with ⟨q, T⟩
  simp only [_root_.Turing.TM0.step, Option.map_eq_none_iff] at hstep
  rw [step_ofTM0Cfg]
  have htr : (ofTM0 M S hs).tr ⟨q, hq⟩ T.head =
      (⟨T.head, none⟩, none) := by
    simp [ofTM0, hstep]
  rw [htr]
  simp [BiTape.optionMove, ← BiTape.head_equivTape_symm]

theorem relatesInSteps_ofTM0Cfg {c₁ c₂ : _root_.Turing.TM0.Cfg (Option Symbol) Λ}
    (hq₁ : c₁.q ∈ S) (n : ℕ) :
    RelatesInSteps (fun a b => b ∈ _root_.Turing.TM0.step M a) c₁ c₂ n ↔
      ∃ hq₂ : c₂.q ∈ S, RelatesInSteps (ofTM0 M S hs).TransitionRelation
        (ofTM0Cfg M S hs c₁ hq₁) (ofTM0Cfg M S hs c₂ hq₂) n := by
  induction n generalizing c₂ with
  | zero =>
    constructor
    · intro h
      cases h
      exact ⟨hq₁, .refl _⟩
    · rintro ⟨hq₂, h⟩
      have heq := RelatesInSteps.zero h
      rcases c₁ with ⟨q₁, T₁⟩
      rcases c₂ with ⟨q₂, T₂⟩
      have hq_eq : q₁ = q₂ := by
        have h1 := congrArg Cfg.state heq
        exact Subtype.ext_iff.mp (Option.some.inj h1)
      have hT_eq : T₁ = T₂ := by
        have h2 := congrArg Cfg.BiTape heq
        exact BiTape.equivTape.symm.injective h2
      subst hq_eq hT_eq
      exact .refl _
  | succ n ih =>
    rw [RelatesInSteps.succ_iff]
    constructor
    · rintro ⟨c', hrel, hstep⟩
      rcases (ih (c₂ := c')).mp hrel with ⟨hq', hrel'⟩
      have hq₂ : c₂.q ∈ S := _root_.Turing.TM0.step_supports M hs hstep hq'
      exact ⟨hq₂, .tail _ _ _ n hrel' (step_ofTM0Cfg_of_some M S hs hq' hstep)⟩
    · rintro ⟨hq₂, hrel⟩
      rcases RelatesInSteps.succ hrel with ⟨cfg', hrel', hstep'⟩
      rcases cfg' with ⟨_ | ⟨q', hq'⟩, t'⟩
      · cases hstep'
      · let c' : _root_.Turing.TM0.Cfg (Option Symbol) Λ := ⟨q', BiTape.equivTape t'⟩
        have hcfg' : (⟨some ⟨q', hq'⟩, t'⟩ : (ofTM0 M S hs).Cfg) = ofTM0Cfg M S hs c' hq' := by
          simp [ofTM0Cfg, c']
        rw [hcfg'] at hrel' hstep'
        have hrel₁ : RelatesInSteps (fun a b => b ∈ _root_.Turing.TM0.step M a) c₁ c' n :=
          (ih (c₂ := c')).mpr ⟨hq', hrel'⟩
        rcases hM : _root_.Turing.TM0.step M c' with _ | c''
        · have hnone := step_ofTM0Cfg_of_none M S hs hq' hM
          rw [TransitionRelation, hnone] at hstep'
          cases hstep'
        · have hsome := step_ofTM0Cfg_of_some M S hs hq' hM
          rw [TransitionRelation, hsome, Option.some.injEq] at hstep'
          have hc'' : c'' = c₂ := by
            rcases c'' with ⟨q'', T''⟩
            rcases c₂ with ⟨q₂, T₂⟩
            have hq_eq : q'' = q₂ := by
              have h1 := congrArg Cfg.state hstep'
              exact Subtype.ext_iff.mp (Option.some.inj h1)
            have hT_eq : T'' = T₂ := by
              have h2 := congrArg Cfg.BiTape hstep'
              exact BiTape.equivTape.symm.injective h2
            subst hq_eq hT_eq
            rfl
          subst hc''
          exact ⟨c', hrel₁, hM⟩

theorem relatesInSteps_ofTM0Cfg_none {c₁ : _root_.Turing.TM0.Cfg (Option Symbol) Λ}
    (hq₁ : c₁.q ∈ S) (t_f : BiTape Symbol) (m : ℕ) :
    RelatesInSteps (ofTM0 M S hs).TransitionRelation (ofTM0Cfg M S hs c₁ hq₁) ⟨none, t_f⟩ m ↔
      ∃ n q_f, m = n + 1 ∧
        RelatesInSteps (fun a b => b ∈ _root_.Turing.TM0.step M a)
          c₁ ⟨q_f, BiTape.equivTape t_f⟩ n ∧
        _root_.Turing.TM0.step M ⟨q_f, BiTape.equivTape t_f⟩ = none := by
  cases m with
  | zero =>
    simp [ofTM0Cfg]
  | succ n =>
    rw [RelatesInSteps.succ_iff]
    constructor
    · rintro ⟨cfg', hrel', hstep'⟩
      rcases cfg' with ⟨_ | ⟨q_f, hq_f⟩, t'⟩
      · cases hstep'
      · let c_f : _root_.Turing.TM0.Cfg (Option Symbol) Λ := ⟨q_f, BiTape.equivTape t'⟩
        have hcfg' : (⟨some ⟨q_f, hq_f⟩, t'⟩ : (ofTM0 M S hs).Cfg) =
            ofTM0Cfg M S hs c_f hq_f := by
          simp [ofTM0Cfg, c_f]
        rw [hcfg'] at hrel' hstep'
        have hrel₁ : RelatesInSteps (fun a b => b ∈ _root_.Turing.TM0.step M a) c₁ c_f n :=
          (relatesInSteps_ofTM0Cfg M S hs hq₁ n).mpr ⟨hq_f, hrel'⟩
        rcases hM : _root_.Turing.TM0.step M c_f with _ | c''
        · have hnone := step_ofTM0Cfg_of_none M S hs hq_f hM
          rw [TransitionRelation, hnone, Option.some.injEq, Cfg.mk.injEq] at hstep'
          rcases hstep' with ⟨-, ht⟩
          have ht' : t' = t_f := by simpa [c_f] using ht
          subst ht'
          exact ⟨n, q_f, rfl, hrel₁, hM⟩
        · have hsome := step_ofTM0Cfg_of_some M S hs hq_f hM
          rw [TransitionRelation, hsome] at hstep'
          cases hstep'
    · rintro ⟨n', q_f, hm, hrel₁, hM⟩
      cases Nat.succ.inj hm
      rcases (relatesInSteps_ofTM0Cfg M S hs hq₁ n).mp hrel₁ with ⟨hq_f, hrel'⟩
      refine ⟨ofTM0Cfg M S hs ⟨q_f, BiTape.equivTape t_f⟩ hq_f, hrel', ?_⟩
      simpa [TransitionRelation] using
        step_ofTM0Cfg_of_none M S hs (c := ⟨q_f, BiTape.equivTape t_f⟩) hq_f hM

/-- `(ofTM0 M S hs).OutputsWithinTime l l' (t + 1)` holds if and only if `M` reaches a halting
configuration with tape `BiTape.equivTape (BiTape.mk₁ l')` in at most `t` steps. -/
theorem outputsWithinTime_ofTM0_iff (l l' : List Symbol) (t : ℕ) :
    (ofTM0 M S hs).OutputsWithinTime l l' (t + 1) ↔
      ∃ q_f, RelatesWithinSteps (fun a b => b ∈ _root_.Turing.TM0.step M a)
        (_root_.Turing.TM0.init (l.map some)) ⟨q_f, BiTape.equivTape (BiTape.mk₁ l')⟩ t ∧
        _root_.Turing.TM0.step M ⟨q_f, BiTape.equivTape (BiTape.mk₁ l')⟩ = none := by
  simp only [OutputsWithinTime, RelatesWithinSteps, ← ofTM0Cfg_init M S hs l, haltCfg]
  constructor
  · rintro ⟨m, hmt, hrel⟩
    rcases (relatesInSteps_ofTM0Cfg_none M S hs hs.1 (BiTape.mk₁ l') m).mp hrel with
      ⟨n, q_f, rfl, hrel', hnone⟩
    exact ⟨q_f, ⟨n, Nat.le_of_succ_le_succ hmt, hrel'⟩, hnone⟩
  · rintro ⟨q_f, ⟨n, hnt, hrel'⟩, hnone⟩
    refine ⟨n + 1, Nat.succ_le_succ hnt, ?_⟩
    exact (relatesInSteps_ofTM0Cfg_none M S hs hs.1 (BiTape.mk₁ l') (n + 1)).mpr
      ⟨n, q_f, rfl, hrel', hnone⟩

/-- `(ofTM0 M S hs).Outputs l l'` holds if and only if `StateTransition.eval (TM0.step M)` on
`TM0.init (l.map some)` halts with tape `BiTape.equivTape (BiTape.mk₁ l')`. -/
theorem outputs_ofTM0_iff (l l' : List Symbol) :
    (ofTM0 M S hs).Outputs l l' ↔
      ∃ q_f, (⟨q_f, BiTape.equivTape (BiTape.mk₁ l')⟩ : _root_.Turing.TM0.Cfg (Option Symbol) Λ) ∈
        StateTransition.eval (_root_.Turing.TM0.step M) (_root_.Turing.TM0.init (l.map some)) := by
  simp only [Outputs, ← ofTM0Cfg_init M S hs l, haltCfg, StateTransition.mem_eval,
    StateTransition.Reaches]
  constructor
  · intro h
    rcases h.relatesInSteps with ⟨m, hm⟩
    rcases (relatesInSteps_ofTM0Cfg_none M S hs hs.1 (BiTape.mk₁ l') m).mp hm with
      ⟨n, q_f, -, hrel, hnone⟩
    exact ⟨q_f, hrel.reflTransGen, hnone⟩
  · rintro ⟨q_f, hreach, hnone⟩
    rcases hreach.relatesInSteps with ⟨n, hn⟩
    have hm := (relatesInSteps_ofTM0Cfg_none M S hs hs.1 (BiTape.mk₁ l') (n + 1)).mpr
      ⟨n, q_f, rfl, hn, hnone⟩
    exact hm.reflTransGen

/-- Evaluating `ofTM0 M S hs` on `l` and reading `right₀` of the final tape produces the exact
same partial result as `_root_.Turing.TM0.eval M (l.map some)`. -/
theorem eval_ofTM0 (l : List Symbol) :
    (StateTransition.eval (ofTM0 M S hs).step ((ofTM0 M S hs).initCfg l)).map
      (fun c => (BiTape.equivTape c.BiTape).right₀) =
      _root_.Turing.TM0.eval M (l.map some) := by
  ext out
  simp only [_root_.Turing.TM0.eval, Part.mem_map_iff, StateTransition.mem_eval,
    StateTransition.Reaches, ← ofTM0Cfg_init M S hs l]
  constructor
  · rintro ⟨c, ⟨hreach, hstop⟩, rfl⟩
    rcases c with ⟨_ | q, t_f⟩
    · rcases hreach.relatesInSteps with ⟨m, hm⟩
      have hreach' :
          RelatesInSteps (ofTM0 M S hs).TransitionRelation
            (ofTM0Cfg M S hs (_root_.Turing.TM0.init (l.map some)) hs.1) ⟨none, t_f⟩ m := hm
      rcases (relatesInSteps_ofTM0Cfg_none M S hs hs.1 t_f m).mp hreach' with
        ⟨n, q_f, -, hrel, hnone⟩
      exact ⟨⟨q_f, BiTape.equivTape t_f⟩, ⟨hrel.reflTransGen, hnone⟩, rfl⟩
    · cases hstop
  · rintro ⟨⟨q_f, T_f⟩, ⟨hreach, hnone⟩, rfl⟩
    rcases hreach.relatesInSteps with ⟨n, hn⟩
    have hm := (relatesInSteps_ofTM0Cfg_none M S hs hs.1 (BiTape.equivTape.symm T_f) (n + 1)).mpr
      ⟨n, q_f, rfl, by simpa using hn, by simpa using hnone⟩
    have hm' : ReflTransGen (fun a b => b ∈ (ofTM0 M S hs).step a)
        (ofTM0Cfg M S hs (_root_.Turing.TM0.init (l.map some)) hs.1)
        ⟨none, BiTape.equivTape.symm T_f⟩ := hm.reflTransGen
    exact ⟨⟨none, BiTape.equivTape.symm T_f⟩, ⟨hm', rfl⟩, by simp⟩

/-- If `ofTM0 M S hs` outputs `l'` on input `l`, then `_root_.Turing.TM0.eval M (l.map some)`
evaluates to `ListBlank.mk (l'.map some)`. -/
theorem outputs_ofTM0_imp_mem_eval {l l' : List Symbol}
    (h : (ofTM0 M S hs).Outputs l l') :
    _root_.Turing.ListBlank.mk (l'.map some) ∈ _root_.Turing.TM0.eval M (l.map some) := by
  rw [← eval_ofTM0 M S hs l, Part.mem_map_iff]
  refine ⟨(ofTM0 M S hs).haltCfg l', (outputs_iff_mem_eval _ l l').mp h, ?_⟩
  simp [haltCfg, _root_.Turing.Tape.mk₁, _root_.Turing.Tape.mk₂]

end OfTM0

section OfTM1

variable {Λ σ : Type} [Inhabited Λ] [Inhabited σ] [Fintype σ]

open Classical in
/-- Compile a finitely supported Mathlib `_root_.Turing.TM1` machine into a `SingleTapeTM Symbol`
by composing `_root_.Turing.TM1to0.tr` with `SingleTapeTM.ofTM0`. -/
noncomputable def ofTM1 (M : Λ → _root_.Turing.TM1.Stmt (Option Symbol) Λ σ) (S : Finset Λ)
    (hs : _root_.Turing.TM1.Supports M S) : SingleTapeTM Symbol :=
  ofTM0 (_root_.Turing.TM1to0.tr M) (_root_.Turing.TM1to0.trStmts M S)
    (_root_.Turing.TM1to0.tr_supports M hs)

/-- Evaluating `ofTM1 M S hs` on `l` and reading `right₀` of the final tape produces the exact
same partial result as `_root_.Turing.TM1.eval M (l.map some)`. -/
theorem eval_ofTM1 (M : Λ → _root_.Turing.TM1.Stmt (Option Symbol) Λ σ) (S : Finset Λ)
    (hs : _root_.Turing.TM1.Supports M S) (l : List Symbol) :
    (StateTransition.eval (ofTM1 M S hs).step ((ofTM1 M S hs).initCfg l)).map
      (fun c => (BiTape.equivTape c.BiTape).right₀) =
      _root_.Turing.TM1.eval M (l.map some) := by
  classical
  unfold ofTM1
  rw [eval_ofTM0, _root_.Turing.TM1to0.tr_eval]

/-- If `ofTM1 M S hs` outputs `l'` on input `l`, then `_root_.Turing.TM1.eval M (l.map some)`
evaluates to `ListBlank.mk (l'.map some)`. -/
theorem outputs_ofTM1_imp_mem_eval (M : Λ → _root_.Turing.TM1.Stmt (Option Symbol) Λ σ)
    (S : Finset Λ) (hs : _root_.Turing.TM1.Supports M S) {l l' : List Symbol}
    (h : (ofTM1 M S hs).Outputs l l') :
    _root_.Turing.ListBlank.mk (l'.map some) ∈ _root_.Turing.TM1.eval M (l.map some) := by
  classical
  unfold ofTM1 at h
  rw [← _root_.Turing.TM1to0.tr_eval]
  exact outputs_ofTM0_imp_mem_eval (_root_.Turing.TM1to0.tr M)
    (_root_.Turing.TM1to0.trStmts M S) (_root_.Turing.TM1to0.tr_supports M hs) h

end OfTM1

end Cslib.Turing.SingleTapeTM
