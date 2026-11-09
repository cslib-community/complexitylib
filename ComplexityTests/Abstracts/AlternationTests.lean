/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.AlternationAbstract
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-! # Concrete clients of the public alternation abstract

One-state machines without work tapes exercise the acceptance rules. The machine `choice u`
halts with output `[true]` on move `false` and stays forever on move `true`. Existentially
(`u = false`) it accepts. Universally (`u = true`) it does not: its infinite branch never
accepts, so acceptance is the least and not the greatest fixed point of the labelling. The machine
`constant b` writes `b` and halts on either move, so it accepts exactly when `b = true`. The
universal machine `split b₀ b₁` halts with output `[b₀]` or `[b₁]`, so it accepts when both moves
accept and rejects when one of them rejects. `constant b` halts within one step, which puts the
trivial problems in `AP` and `APSPACE` under every encoding; the headline theorems then place them
in `PSPACE` and `EXP`.
-/

namespace ComplexityTests.Abstracts.AlternationTests

open ComplexityAbstracts.AlternationAbstract

/-- Write `b` to the output and halt, without moving. -/
def haltWith (b : Bool) : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- Stay in the only state, without moving or writing. -/
def stay : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

/-- Move `false` writes `true` and halts; move `true` stays forever. The only state is universal
when `u = true`. -/
def choice (u : Bool) : ATM 0 Unit where
  start := ()
  move b _ _ _ := if b then stay else haltWith true
  universal _ := u

/-- Write `b` and halt on either move. -/
def constant (b : Bool) : ATM 0 Unit where
  start := ()
  move _ _ _ _ := haltWith b
  universal _ := false

/-- A universal state whose two moves halt: move `false` writes `b₀` and move `true` writes
`b₁`. -/
def split (b₀ b₁ : Bool) : ATM 0 Unit where
  start := ()
  move b _ _ _ := haltWith (if b then b₁ else b₀)
  universal _ := true

/-- The configurations accepting without moves: halted with output `[true]`. -/
def acceptingNow (input : List Bool) : Set (Turing.Cfg 0 Bool Unit input) :=
  {c | c.state = none ∧ c.output = [true]}

/-- A running configuration steps by either move. -/
theorem step_of_move {k : ℕ} {State : Type} (M : ATM k State) {input : List Bool}
    {c : Turing.Cfg k Bool State input} {q : State} (hc : c.state = some q) (b : Bool) :
    M.toNTM.Step c ((M.move b q c.inputSymbol c.workTapeSymbols).apply c) := by
  simp only [Turing.MultiTapeNTM.Step, hc]
  exact ⟨_, (⟨b, rfl⟩ : ∃ b', M.move b' q c.inputSymbol c.workTapeSymbols = _), rfl⟩

/-- Every step from a running configuration is one of the two moves. -/
theorem eq_of_step {k : ℕ} {State : Type} (M : ATM k State) {input : List Bool}
    {c d : Turing.Cfg k Bool State input} {q : State} (hc : c.state = some q)
    (h : M.toNTM.Step c d) : ∃ b, d = (M.move b q c.inputSymbol c.workTapeSymbols).apply c := by
  simp only [Turing.MultiTapeNTM.Step, hc] at h
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := h
  exact ⟨b, rfl⟩

/-- The existential machine accepts every input through its halting move. -/
theorem choice_false_accepts (input : List Bool) : (choice false).Accepts input :=
  fun _ hhalt hex _ => hex _ () rfl rfl ⟨_, step_of_move _ rfl false, hhalt _ rfl rfl⟩

/-- The universal machine accepts no input: the infinite branch never accepts. -/
theorem not_choice_true_accepts (input : List Bool) : ¬(choice true).Accepts input := by
  intro h
  have hinit := h (acceptingNow input) (fun _ hc hout => ⟨hc, hout⟩)
    (fun _ _ _ hq _ => Bool.noConfusion hq)
    (fun c _ hc _ hall => by
      have hnone := (hall _ (step_of_move _ hc true)).1
      simp [choice, stay, Turing.Action.apply] at hnone)
  simp [Turing.Cfg.init, acceptingNow] at hinit

/-- `constant true` accepts every input. -/
theorem constant_true_accepts (input : List Bool) : (constant true).Accepts input :=
  fun _ hhalt hex _ => hex _ () rfl rfl ⟨_, step_of_move _ rfl false, hhalt _ rfl rfl⟩

/-- `constant false` accepts no input: it halts with output ending in `false`. -/
theorem not_constant_false_accepts (input : List Bool) : ¬(constant false).Accepts input := by
  intro h
  have hinit := h (acceptingNow input) (fun _ hc hout => ⟨hc, hout⟩)
    (fun c _ hc _ ⟨_, hd, hdS⟩ => by
      obtain ⟨_, rfl⟩ := eq_of_step _ hc hd
      have hout := congrArg List.getLast? hdS.2
      simp [constant, haltWith, Turing.Action.apply] at hout)
    (fun _ _ _ hq _ => Bool.noConfusion hq)
  simp [Turing.Cfg.init, acceptingNow] at hinit

/-- A universal state whose two halting moves both accept is accepting. -/
theorem split_true_true_accepts (input : List Bool) : (split true true).Accepts input := by
  intro S hhalt _ hall
  refine hall _ () rfl rfl fun d hd => ?_
  obtain ⟨b, rfl⟩ := eq_of_step _ rfl hd
  cases b <;> exact hhalt _ rfl rfl

/-- A universal state with one rejecting halting move is not accepting, although its other move
accepts. -/
theorem not_split_true_false_accepts (input : List Bool) :
    ¬(split true false).Accepts input := by
  intro h
  have hinit := h (acceptingNow input) (fun _ hc hout => ⟨hc, hout⟩)
    (fun _ _ _ hq _ => Bool.noConfusion hq)
    (fun c _ hc _ hall => by
      have hout := congrArg List.getLast? (hall _ (step_of_move _ hc true)).2
      simp [split, haltWith, Turing.Action.apply] at hout)
  simp [Turing.Cfg.init, acceptingNow] at hinit

/-- `constant b` halts within one step. -/
theorem runsInTime_constant (b : Bool) (input : List Bool) :
    (constant b).toNTM.RunsInTime input 1 := by
  intro p hp
  have h0 : 0 < p.toRunPath.length := hp
  have hhead : p.toRunPath (Fin.castSucc ⟨0, h0⟩) = (constant b).toNTM.initCfg input :=
    p.head_eq
  have hstep : (constant b).toNTM.Step (p.toRunPath (Fin.castSucc ⟨0, h0⟩))
      (p.toRunPath (Fin.succ ⟨0, h0⟩)) := p.toRunPath.step ⟨0, h0⟩
  rw [hhead] at hstep
  obtain ⟨_, hd⟩ := eq_of_step (constant b) rfl hstep
  have hhalt : (p.toRunPath (Fin.succ ⟨0, h0⟩)).Halted := by
    rw [hd]
    rfl
  exact (Turing.MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt

/-- Every problem with all instances accepted is in `AP`, under every encoding. -/
theorem univ_mem_AP {α : Type} (enc : α ↪ List Bool) : (Set.univ : Set α) ∈ AP enc :=
  ⟨0, Unit, inferInstance, constant true, fun _ => 1,
    ⟨fun _ => 1, Cslib.PolynomiallyBounded.const 1, fun _ => le_rfl⟩,
    fun a => ⟨runsInTime_constant true (enc a), iff_of_true trivial (constant_true_accepts _)⟩⟩

/-- The empty problem is in `AP`, under every encoding. -/
theorem empty_mem_AP {α : Type} (enc : α ↪ List Bool) : (∅ : Set α) ∈ AP enc :=
  ⟨0, Unit, inferInstance, constant false, fun _ => 1,
    ⟨fun _ => 1, Cslib.PolynomiallyBounded.const 1, fun _ => le_rfl⟩,
    fun a => ⟨runsInTime_constant false (enc a),
      iff_of_false (Set.notMem_empty a) (not_constant_false_accepts _)⟩⟩

/-- Every problem with all instances accepted is in `APSPACE`, without work tapes. -/
theorem univ_mem_APSPACE {α : Type} (enc : α ↪ List Bool) : (Set.univ : Set α) ∈ APSPACE enc :=
  ⟨0, Unit, inferInstance, constant true, fun _ => 0,
    ⟨fun _ => 0, Cslib.PolynomiallyBounded.const 0, fun _ => le_rfl⟩,
    ⟨fun _ => ⟨Turing.MultiTapeNTM.runsInSpace_zero_tapes _ _ _,
      iff_of_true trivial (constant_true_accepts _)⟩,
      fun a => ⟨1, runsInTime_constant true (enc a)⟩⟩⟩

-- The headline theorems transfer these memberships to the deterministic classes.
example {α : Type} (enc : α ↪ List Bool) : (Set.univ : Set α) ∈ PSPACE enc :=
  ap_eq_pspace enc ▸ univ_mem_AP enc

example {α : Type} (enc : α ↪ List Bool) : (∅ : Set α) ∈ PSPACE enc :=
  ap_eq_pspace enc ▸ empty_mem_AP enc

example {α : Type} (enc : α ↪ List Bool) : (Set.univ : Set α) ∈ EXP enc :=
  apspace_eq_exp enc ▸ univ_mem_APSPACE enc

end ComplexityTests.Abstracts.AlternationTests
