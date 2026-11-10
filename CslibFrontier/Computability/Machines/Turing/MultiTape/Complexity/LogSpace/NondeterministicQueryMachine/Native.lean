/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank

/-!
# Native control for binary-choice query passes

An initializer runs once, followed by one or more passes. At each pass boundary one native
binary choice selects a deterministic pass routine. A blank continuation tape selects the
finalizer; a nonblank one starts another pass. All routing steps preserve every tape and head.

The finite native control contains only the control states of the initializer, the two pass
routines and the finalizer, together with two routing states. In particular, neither the
abstract query state nor the history of choices is put in native control.

## Main definitions

* `Turing.NondeterministicQueryMachine.Native.State`: native finite control.
* `Turing.NondeterministicQueryMachine.Native.table`: a binary-choice native transition table.
* `Turing.NondeterministicQueryMachine.Native.machine`: its ordinary nondeterministic machine.

## Main results

* `Turing.NondeterministicQueryMachine.Native.exists_runPath_iff`: all native run paths are
  exactly finite coin replays, including halted self-loops.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine.Native

/-- Native control for initialization, binary-choice passes, and finalization. -/
inductive State (SI : Type) (SP : Bool → Type) (SF : Type) where
  /-- The initializer is running. -/
  | init (q : SI)
  /-- Choose the next pass routine, without moving any head. -/
  | choose
  /-- The selected deterministic pass is running. -/
  | pass (choice : Bool) (q : SP choice)
  /-- Read the continuation tape after a pass. -/
  | check
  /-- The finalizer is running. -/
  | finish (q : SF)

instance {SI SF : Type} {SP : Bool → Type} [Finite SI] [∀ b, Finite (SP b)] [Finite SF] :
    Finite (State SI SP SF) :=
  Finite.of_injective
    (fun q : State SI SP SF => match q with
      | .init q => (Sum.inl q : SI ⊕ (Unit ⊕ ((Σ b, SP b) ⊕ (Unit ⊕ SF))))
      | .choose => .inr (.inl ())
      | .pass b q => .inr (.inr (.inl ⟨b, q⟩))
      | .check => .inr (.inr (.inr (.inl ())))
      | .finish q => .inr (.inr (.inr (.inr q))))
    (by intro q q' h; cases q <;> cases q' <;> simp_all)

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- Relabel an action's optional next state, preserving all tape actions. -/
def relabelAction {S S' : Type} (φ : Option S → Option S') (a : Turing.Action k Bool S) :
    Turing.Action k Bool S' :=
  ⟨a.inputTape, a.workTapes, a.output, φ a.state⟩

/-- A routing instruction changes control and leaves every head, tape and output unchanged. -/
def routeAction {S : Type} (q : Option S) : Turing.Action k Bool S :=
  ⟨0, fun _ => (none, 0), none, q⟩

/-- Embed initializer states, sending its halt to the first binary-choice boundary. -/
def initState : Option SI → Option (State SI SP SF) :=
  fun q => some (q.elim .choose .init)

/-- Embed pass states, sending the halt to the continuation check. -/
def passState (b : Bool) : Option (SP b) → Option (State SI SP SF) :=
  fun q => some (q.elim .check (.pass b))

/-- Embed finalizer states, preserving the final halt. -/
def finishState : Option SF → Option (State SI SP SF) := Option.map .finish

/-- Native instruction under one binary choice. Only `choose` depends on the choice. -/
noncomputable def instruction (q : State SI SP SF) (input : Option Bool)
    (work : Fin k → Option Bool) (choice : Bool) : Turing.Action k Bool (State SI SP SF) :=
  match q with
  | .init q => relabelAction initState (I.tr q input work)
  | .choose => routeAction (some (.pass choice (P choice).q₀))
  | .pass b q => relabelAction (passState b) ((P b).tr q input work)
  | .check => routeAction (some (if (work C).isSome then .choose else .finish F.q₀))
  | .finish q => relabelAction finishState (F.tr q input work)

/-- The native binary-choice transition table. Its oracle type is empty. -/
noncomputable def table : MultiTapePTM k Bool (State SI SP SF) where
  initial := .init I.q₀
  tr q input work _ choice :=
    .step (instruction I P F C q input work choice) (fun e => e.elim) (fun e => e.elim)

/-- The ordinary native nondeterministic machine. -/
noncomputable def machine : MultiTapeNTM k Bool (State SI SP SF) := (table I P F C).toNTM

/-- The finite native machine is never stuck, even away from its intended invariant. -/
theorem exists_step {input : List Bool} (c : Cfg k Bool (State SI SP SF) input) :
    ∃ c', (machine I P F C).Step c c' :=
  (table I P F C).exists_step_toNTM c

/-- A native step is selected by one binary choice. -/
theorem step_iff {input : List Bool} {c c' : Cfg k Bool (State SI SP SF) input} :
    (machine I P F C).Step c c' ↔
      ∃ choice, ((table I P F C).withCoin choice).toTM.step c = c' :=
  (table I P F C).step_toNTM_iff

/-- Finite native paths are exactly finite coin replays. Coins are proof-level witnesses. -/
theorem exists_runPath_iff {input : List Bool}
    {c c' : Cfg k Bool (State SI SP SF) input} {n : ℕ} :
    (∃ p : (machine I P F C).RunPath input,
      p.head = c ∧ p.length = n ∧ p.last = c') ↔
      ∃ choices : List Bool, choices.length = n ∧
        (table I P F C).stepCoins choices c = c' :=
  (table I P F C).exists_runPath_toNTM_iff

theorem tr_withCoin (choice : Bool) (q : State SI SP SF) (input : Option Bool)
    (work : Fin k → Option Bool) :
    ((table I P F C).withCoin choice).toTM.tr q input work =
      instruction I P F C q input work choice := by
  simp [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr, MultiTapePTM.withCoin, table,
    MultiTapeMachine.Action.emptyOracleEquiv]

/-- Applying a relabeled action agrees with relabeling the resulting configuration. The old
control state is never read by `Action.apply`. -/
theorem apply_relabelAction {S S' : Type} {input : List Bool}
    (φ ψ : Option S → Option S') (a : Turing.Action k Bool S) (c : Cfg k Bool S input) :
    (relabelAction φ a).apply (c.mapState ψ) = (a.apply c).mapState φ := rfl

theorem apply_routeAction {S : Type} {input : List Bool} (q : Option S)
    (c : Cfg k Bool S input) : (routeAction q).apply c = c.withState q := by
  apply Cfg.ext <;> simp [routeAction, Action.apply, SignType.cast, Cfg.withState]

/-- The initializer is simulated step for step until its first halt. -/
theorem step_init {input : List Bool} (choice : Bool) (c : Cfg k Bool SI input)
    (h : ¬c.Halted) :
    ((table I P F C).withCoin choice).toTM.step (c.mapState initState) =
      (I.step c).mapState initState := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hs : (c.mapState (initState (SP := SP) (SF := SF))).state = some (.init q) := by
    simp [initState, hq]
  rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hq, tr_withCoin]
  rfl

/-- A selected pass is deterministic until its first halt, regardless of subsequent coins. -/
theorem step_pass {input : List Bool} (coin b : Bool) (c : Cfg k Bool (SP b) input)
    (h : ¬c.Halted) :
    ((table I P F C).withCoin coin).toTM.step (c.mapState (passState b)) =
      ((P b).step c).mapState (passState b) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hs : (c.mapState (passState (SI := SI) (SF := SF) b)).state = some (.pass b q) := by
    simp [passState, hq]
  rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hq, tr_withCoin]
  rfl

/-- The finalizer is simulated step for step, with its halt preserved. -/
theorem step_finish {input : List Bool} (choice : Bool) (c : Cfg k Bool SF input)
    (h : ¬c.Halted) :
    ((table I P F C).withCoin choice).toTM.step (c.mapState finishState) =
      (F.step c).mapState finishState := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hs : (c.mapState (finishState (SI := SI) (SP := SP))).state = some (.finish q) := by
    simp [finishState, hq]
  rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hq, tr_withCoin]
  rfl

/-- The choice step selects a routine without storing any earlier choices or moving a head. -/
theorem step_choose {input : List Bool} (choice : Bool)
    (c : Cfg k Bool (State SI SP SF) input) (h : c.state = some .choose) :
    ((table I P F C).withCoin choice).toTM.step c =
      c.withState (some (.pass choice (P choice).q₀)) := by
  rw [MultiTapeTM.step_of_state h, tr_withCoin]
  exact apply_routeAction _ _

/-- The continuation check changes only native control. -/
theorem step_check {input : List Bool} (choice : Bool)
    (c : Cfg k Bool (State SI SP SF) input) (h : c.state = some .check) :
    ((table I P F C).withCoin choice).toTM.step c =
      c.withState (some (if (c.workTapeSymbols C).isSome then .choose else .finish F.q₀)) := by
  rw [MultiTapeTM.step_of_state h, tr_withCoin]
  exact apply_routeAction _ _

/-- Every native successor inside a live pass is the same deterministic successor. -/
theorem step_pass_iff {input : List Bool} (b : Bool) (c : Cfg k Bool (SP b) input)
    (h : ¬c.Halted) (c' : Cfg k Bool (State SI SP SF) input) :
    (machine I P F C).Step (c.mapState (passState b)) c' ↔
      c' = ((P b).step c).mapState (passState b) := by
  rw [step_iff]
  simp only [step_pass I P F C _ b c h]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨false, h.symm⟩⟩

/-- Every native successor inside the live initializer is its deterministic successor. -/
theorem step_init_iff {input : List Bool} (c : Cfg k Bool SI input) (h : ¬c.Halted)
    (c' : Cfg k Bool (State SI SP SF) input) :
    (machine I P F C).Step (c.mapState initState) c' ↔
      c' = (I.step c).mapState initState := by
  rw [step_iff]
  simp only [step_init I P F C _ c h]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨false, h.symm⟩⟩

/-- Every native successor inside the live finalizer is its deterministic successor. -/
theorem step_finish_iff {input : List Bool} (c : Cfg k Bool SF input) (h : ¬c.Halted)
    (c' : Cfg k Bool (State SI SP SF) input) :
    (machine I P F C).Step (c.mapState finishState) c' ↔
      c' = (F.step c).mapState finishState := by
  rw [step_iff]
  simp only [step_finish I P F C _ c h]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨false, h.symm⟩⟩

private theorem follows_routine {S NS : Type} {input : List Bool}
    {D : MultiTapeTM k Bool S} {N : MultiTapeNTM k Bool NS}
    (φ : Option S → Option NS)
    (hstep : ∀ c : Cfg k Bool S input, ¬c.Halted →
      ∀ c', N.Step (c.mapState φ) c' ↔ c' = (D.step c).mapState φ)
    (p : N.RunPath input) (q : RelSeries (D.runningStepRel input))
    (hhead : p.head = q.head.mapState φ)
    (n : ℕ) (hn : n < p.length + 1) (hq : n < q.length + 1) :
    p ⟨n, hn⟩ = (q ⟨n, hq⟩).mapState φ := by
  induction n with
  | zero => exact hhead
  | succ n ih =>
    have hnp : n < p.length := by omega
    have hnq : n < q.length := by omega
    have hsource := q.step ⟨n, hnq⟩
    have hp := p.step ⟨n, hnp⟩
    change N.Step (p ⟨n, by omega⟩) (p ⟨n + 1, hn⟩) at hp
    rw [ih (by omega) (by omega)] at hp
    have ht := (hstep _ hsource.1 _).mp hp
    rw [ht, MultiTapeTM.step_iff.mp hsource.2]
    rfl

/-- **Every native pass prefix is the deterministic pass prefix.** This is the reverse direction
needed for space bounds on all native computation paths, rather than only a selected replay.
The endpoint is included; it is the native continuation-check state. -/
theorem follows_pass {input : List Bool} (b : Bool) (p : (machine I P F C).RunPath input)
    (q : RelSeries ((P b).runningStepRel input))
    (hhead : p.head = q.head.mapState (passState b))
    (n : ℕ) (hn : n < p.length + 1) (hq : n < q.length + 1) :
    p ⟨n, hn⟩ = (q ⟨n, hq⟩).mapState (passState b) :=
  follows_routine (passState b) (step_pass_iff I P F C b) p q hhead n hn hq

/-- Every native initialization prefix is the deterministic initialization prefix. -/
theorem follows_init {input : List Bool} (p : (machine I P F C).RunPath input)
    (q : RelSeries (I.runningStepRel input)) (hhead : p.head = q.head.mapState initState)
    (n : ℕ) (hn : n < p.length + 1) (hq : n < q.length + 1) :
    p ⟨n, hn⟩ = (q ⟨n, hq⟩).mapState initState :=
  follows_routine initState (step_init_iff I P F C) p q hhead n hn hq

/-- Every native finalization prefix is the deterministic finalization prefix. -/
theorem follows_finish {input : List Bool} (p : (machine I P F C).RunPath input)
    (q : RelSeries (F.runningStepRel input)) (hhead : p.head = q.head.mapState finishState)
    (n : ℕ) (hn : n < p.length + 1) (hq : n < q.length + 1) :
    p ⟨n, hn⟩ = (q ⟨n, hq⟩).mapState finishState :=
  follows_routine finishState (step_finish_iff I P F C) p q hhead n hn hq

/-- Every prefix that is still in one pass stays within the pass's original common window.
No sum over time, repeated visits, or choices is taken. -/
theorem inWindow_pass_prefix {input : List Bool} (b : Bool)
    (p : (machine I P F C).RunPath input) (q : RelSeries ((P b).runningStepRel input))
    (hhead : p.head = q.head.mapState (passState b)) (hlen : p.length ≤ q.length) {s : ℕ}
    (hwin : ∀ c ∈ q, ∀ i, c.workTapePos i ∈ window s) : p.InWindow s := by
  rintro _ ⟨n, rfl⟩ i
  rw [follows_pass I P F C b p q hhead n n.isLt (by omega)]
  exact hwin _ ⟨_, rfl⟩ i

/-- Embed the running part of an initializer path into the native machine. -/
@[simps! apply]
def initHom {input : List Bool} :
    (I.runningStepRel input).Hom ((machine I P F C).stepRel input) where
  toFun := Cfg.mapState initState
  map_rel' {c _} hc := (step_iff I P F C).mpr
    ⟨false, (step_init I P F C false c hc.1).trans
      (congrArg (Cfg.mapState initState) (MultiTapeTM.step_iff.mp hc.2))⟩

/-- Embed the running part of a selected pass, retaining every head position. -/
@[simps! apply]
def passHom {input : List Bool} (b : Bool) :
    ((P b).runningStepRel input).Hom ((machine I P F C).stepRel input) where
  toFun := Cfg.mapState (passState b)
  map_rel' {c _} hc := (step_iff I P F C).mpr
    ⟨false, (step_pass I P F C false b c hc.1).trans
      (congrArg (Cfg.mapState (passState b)) (MultiTapeTM.step_iff.mp hc.2))⟩

/-- Embed the running part of a finalizer, preserving its final halt. -/
@[simps! apply]
def finishHom {input : List Bool} :
    (F.runningStepRel input).Hom ((machine I P F C).stepRel input) where
  toFun := Cfg.mapState finishState
  map_rel' {c _} hc := (step_iff I P F C).mpr
    ⟨false, (step_finish I P F C false c hc.1).trans
      (congrArg (Cfg.mapState finishState) (MultiTapeTM.step_iff.mp hc.2))⟩

/-- A deterministic pass specification gives a native round with one binary-choice step and one
continuation check. Its heads stay in the same origin-centered window, independently of the
number of preceding or following rounds. -/
theorem exists_round {input : List Bool} (b : Bool)
    {Pre : (input : List Bool) → (Fin k → List Bool) → Prop}
    {Post : (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) →
      List Bool → Prop} {t s : ℕ}
    (h : MultiTapeTM.TransformsTapes (P b) Pre Post t s)
    {ws : Fin k → List Bool} (out : List Bool) (hPre : Pre input ws) :
    ∃ ws' e, Post input ws ws' e ∧ ∃ p : (machine I P F C).RunPath input,
      p.head = wordsCfg input (some .choose) ws out ∧
      p.last = wordsCfg input
        (some (if ws' C = [] then .finish F.q₀ else .choose)) ws' (out ++ e) ∧
      p.length ≤ t + 2 ∧ p.InWindow s := by
  obtain ⟨ws', e, hPost, p, hhead, hlast, htime, hspace⟩ := h input ws out hPre
  obtain ⟨q, hqhead, hqlast, hqlen, hqmem⟩ := p.exists_running (by rw [hlast]; rfl)
  let f := passHom I P F C (input := input) b
  have hfirst : (machine I P F C).Step
      (wordsCfg input (some .choose) ws out) (q.map f).head := by
    apply (step_iff I P F C).mpr
    refine ⟨b, ?_⟩
    rw [step_choose I P F C b _ rfl]
    simp [f, hqhead, hhead, passState, wordsCfg, Cfg.mapState, Cfg.withState]
  have hcheck : (machine I P F C).Step (q.map f).last
      (wordsCfg input
        (some (if ws' C = [] then .finish F.q₀ else .choose)) ws' (out ++ e)) := by
    apply (step_iff I P F C).mpr
    refine ⟨false, ?_⟩
    have heq : (q.map f).last = wordsCfg input (some .check) ws' (out ++ e) := by
      simp [f, hqlast, hlast, passState, wordsCfg, Cfg.mapState]
    rw [heq, step_check I P F C false _ rfl]
    cases hc : ws' C <;>
      simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero,
        Cfg.withState, hc]
  let qp := (q.map f).cons (wordsCfg input (some .choose) ws out) hfirst
  have hcheck' : (machine I P F C).Step qp.last
      (wordsCfg input (some (if ws' C = [] then .finish F.q₀ else .choose)) ws' (out ++ e)) := by
    simpa [qp] using hcheck
  refine ⟨ws', e, hPost, qp.snoc _ hcheck', by simp [qp], by simp,
    by simp only [qp, RelSeries.snoc_length, RelSeries.cons_length, RelSeries.map_length,
      MultiTapeNTM.RunPath.time] at htime ⊢; omega, ?_⟩
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := p) (by simp [hhead]) hspace
  intro c hc
  rcases RelSeries.mem_snoc.mp hc with hc | rfl
  · change c ∈ (q.map f).cons _ hfirst at hc
    have hlist := RelSeries.mem_toList.mpr hc
    rw [RelSeries.toList_cons] at hlist
    rcases List.mem_cons.mp hlist with rfl | hc
    · simp [wordsCfg, mem_window]
    · obtain ⟨c₀, hc₀, rfl⟩ := RelSeries.exists_of_mem_map (RelSeries.mem_toList.mp hc)
      exact hwin c₀ (hqmem c₀ hc₀)
  · simp [wordsCfg, mem_window]

end Turing.NondeterministicQueryMachine.Native
